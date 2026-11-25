"""Tidehunter v13: selective momentum with tranches.

Lessons from twelve losing variants on the dev window (and the kit's own
pilot momentum bot, which loses -9.38 SOL there):
- Chasing spikes fails: by the time a buy fills 2 slots later the spike
  has already run ~12% further and then dumps. The spike edge is a
  lookahead illusion.
- Buying everything fails too: the 2-slot latency + fees eat the edge.
- What loses least: enter only coins with real early momentum (up 5% off
  launch, buy-dominated flow, 10+ distinct buyers, creator not dumping,
  still near its young peak), risk little first (0.02 SOL), add 0.03 SOL
  only into a winner up 15%, exit fast (stop -8%, half at +18%, rest at
  +45%, trailing past +30%, fade on a 10% pullback off any +2% peak,
  time stop at ~2 minutes). Losers stay small; winners get size.

Everything is decided from the replay itself (slots, reserves, trade flow);
no clock, no environment, no randomness, so two runs agree byte for byte.
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "vendor"))

import makefun_bot  # noqa: E402  (after the sys.path line)

STAKE_LAMPORTS = 20_000_000          # first tranche 0.02 SOL: losers stay small
ADD_LAMPORTS = 30_000_000            # second tranche 0.03 SOL, only into a
                                     # winner that keeps rising
ADD_GAIN = 0.15                      # add when up 15% and flow still hot
MIN_BUY_LAMPORTS = 20_000_000        # 0.02 SOL per buy
MAX_SLIPPAGE_BPS = 500               # 5% on buys
SELL_SLIPPAGE_BPS = 800              # 8% on sells
ENTRY_MAX_AGE_SLOTS = 600            # only coins younger than ~2 minutes
ENTRY_MIN_TRADES = 8                 # need a little tape before judging
ENTRY_MIN_BUY_SHARE = 0.85           # buys must dominate recent SOL volume
ENTRY_MIN_BUYERS = 10                # distinct non-creator wallets buying
ENTRY_MIN_RISE = 1.05                # price already +5% off its first trade
ENTRY_MIN_RECENT_BUYERS = 5          # distinct buyers inside the flow window
ENTRY_MAX_CREATOR_SELL = 50_000_000  # creator dumping 0.05 SOL kills the coin
ENTRY_PEAK_KEEP = 0.95               # still within 5% of its young peak
TP1_GAIN = 0.18                      # sell half here
TP1_FRACTION = 0.5
TP2_GAIN = 0.45                      # sell the rest here
TRAIL_TRIGGER = 0.30                 # once the peak is past +30% ...
TRAIL_DROP = 0.08                    # ... sell all on an 8% pullback off peak
FADE_TRIGGER = 0.02                  # once a position is up 2% ...
FADE_DROP = 0.10                     # ... sell all on a 10% pullback off peak
STOP_LOSS = -0.05                    # hard stop
TIME_STOP_SLOTS = 600                # give a coin ~2 minutes, then judge it
TIME_STOP_GAIN = 0.05
STALE_SLOTS = 300                    # no trade for this long + under water: out
SELL_RETRY_SLOTS = 100               # after a rejected sell, wait this long
FLOW_WINDOW = 15


def _price(curve):
    """Lamports per token from a curve's virtual reserves (float ratio)."""
    if curve.virtual_token_reserves <= 0:
        return 0.0
    return curve.virtual_quote_reserves / curve.virtual_token_reserves


class Coin:
    """Per-coin tape, kept from the batch events as they arrive."""

    __slots__ = (
        "mint", "creator", "created_slot", "first_price", "peak_price",
        "trades", "buy_vol", "sell_vol", "buyers", "last_trade_slot", "flow",
        "creator_sell_vol",
        "entered", "added", "entry_slot", "entry_price", "peak_gain", "tp1_done",
    )

    def __init__(self, mint, creator, slot):
        self.mint = mint
        self.creator = creator
        self.created_slot = slot
        self.first_price = 0.0        # price right after its first trade
        self.peak_price = 0.0
        self.trades = 0
        self.buy_vol = 0
        self.sell_vol = 0
        self.buyers = set()
        self.last_trade_slot = slot
        self.flow = []               # (is_buy, sol_amount, user) of recent trades
        self.creator_sell_vol = 0
        self.entered = False
        self.added = False
        self.entry_slot = -1
        self.entry_price = 0.0
        self.peak_gain = 0.0
        self.tp1_done = False


coins = {}       # mint -> Coin, first-seen order (deterministic iteration)
held = {}        # mint -> Coin, currently held (subset of coins)
exit_plan = {}   # mint -> reason string for the pending/just-sent sell
trip_stats = {}  # reason -> [count, sum_gain, sum_slots]
prev_positions = {}  # mint -> (cost_lamports, token_amount) last batch
sell_blocked = {}  # mint -> slot until which no sell is re-sent (after a reject)


def _record_close(mint, gain, slots_held, reason):
    row = trip_stats.setdefault(reason, [0, 0.0, 0])
    row[0] += 1
    row[1] += gain
    row[2] += slots_held


def on_done(state, done):
    import sys as _sys
    total = 0
    for reason in sorted(trip_stats):
        count, gain_sum, slots_sum = trip_stats[reason]
        total += count
        print(f"TRIP {reason}: n={count} avg_gain={gain_sum / count:.3f} "
              f"avg_hold_slots={slots_sum / count:.0f}", file=_sys.stderr)
    print(f"TRIP total={total}", file=_sys.stderr)


def _event_price(event):
    vt = int(event["virtual_token_reserves"])
    if vt <= 0:
        return 0.0
    return int(event["virtual_sol_reserves"]) / vt


def _note_trade(coin, event, slot):
    coin.trades += 1
    coin.last_trade_slot = slot
    amount = int(event["sol_amount"])
    user = event.get("user")
    if coin.first_price <= 0:
        coin.first_price = _event_price(event)
        coin.peak_price = coin.first_price
    if event["is_buy"]:
        coin.buy_vol += amount
        if user and user != coin.creator:
            coin.buyers.add(user)
    else:
        coin.sell_vol += amount
        if user and user == coin.creator:
            coin.creator_sell_vol += amount
    coin.flow.append((event["is_buy"], amount, user))
    if len(coin.flow) > FLOW_WINDOW:
        del coin.flow[0]


def _buy_share(coin):
    buys = 0
    total = 0
    for is_buy, amount, _user in coin.flow:
        total += amount
        if is_buy:
            buys += amount
    if total <= 0:
        return 0.0
    return buys / total


def _recent_buyers(coin):
    buyers = set()
    for is_buy, _amount, user in coin.flow:
        if is_buy and user and user != coin.creator:
            buyers.add(user)
    return len(buyers)


def _try_enter(state, batch, orders):
    """Scan the batch's coins for a fresh momentum entry."""
    caps = state.hello["caps"]
    tx = state.tx_fee_lamports()
    free = state.free_cash_lamports()
    slots = caps["max_open_positions"] - state.committed_position_count()
    if slots <= 0:
        return
    seen = set()
    for event in batch["events"]:
        mint = event["mint"]
        if mint in seen:
            continue
        seen.add(mint)
        coin = coins.get(mint)
        if coin is None or coin.entered:
            continue
        curve = state.curves.get(mint)
        if curve is None or curve.complete:
            continue
        if state.slot - coin.created_slot > ENTRY_MAX_AGE_SLOTS:
            continue
        if coin.trades < ENTRY_MIN_TRADES:
            continue
        if len(coin.buyers) < ENTRY_MIN_BUYERS:
            continue
        if _recent_buyers(coin) < ENTRY_MIN_RECENT_BUYERS:
            continue
        if coin.creator_sell_vol > ENTRY_MAX_CREATOR_SELL:
            continue
        if _buy_share(coin) < ENTRY_MIN_BUY_SHARE:
            continue
        price = _price(curve)
        if coin.first_price <= 0 or price < coin.first_price * ENTRY_MIN_RISE:
            continue
        if coin.peak_price > 0 and price < coin.peak_price * ENTRY_PEAK_KEEP:
            continue
        cap = state.max_buy_lamports(mint)
        if cap < MIN_BUY_LAMPORTS:
            continue
        amount = min(cap, STAKE_LAMPORTS)
        if len(orders) >= caps["max_orders_per_batch"] or free < amount + tx:
            continue
        orders.append({
            "side": "buy", "mint": mint,
            "quote_lamports": amount,
            "max_slippage_bps": MAX_SLIPPAGE_BPS,
        })
        free -= amount + tx
        slots -= 1
        coin.entered = True
        if slots <= 0:
            return


def _try_add(state, batch, orders):
    """Pyramid: add a second tranche into a winner that keeps rising."""
    caps = state.hello["caps"]
    tx = state.tx_fee_lamports()
    free = state.free_cash_lamports()
    pending_buys = set()
    for pending in state.pending.values():
        if pending.order["side"] == "buy":
            pending_buys.add(pending.order["mint"])
    for mint, holding in list(state.positions.items()):
        if len(orders) >= caps["max_orders_per_batch"]:
            break
        if mint in pending_buys:
            continue
        coin = coins.get(mint)
        if coin is None or coin.added:
            continue
        curve = state.curves.get(mint)
        if curve is None or curve.complete:
            continue
        if state.slot - coin.created_slot > ENTRY_MAX_AGE_SLOTS:
            continue
        if coin.entry_price <= 0:
            continue
        price = _price(curve)
        if price < coin.entry_price * (1.0 + ADD_GAIN):
            continue
        if _buy_share(coin) < 0.80:
            continue
        cap = state.max_buy_lamports(mint)
        if cap < MIN_BUY_LAMPORTS:
            continue
        amount = min(cap, ADD_LAMPORTS)
        if free < amount + tx:
            continue
        orders.append({
            "side": "buy", "mint": mint,
            "quote_lamports": amount,
            "max_slippage_bps": MAX_SLIPPAGE_BPS,
        })
        free -= amount + tx
        coin.added = True


def _manage_exits(state, batch, orders):
    """Laddered exits for every held position."""
    caps = state.hello["caps"]
    pending_sells = set()
    for pending in state.pending.values():
        if pending.order["side"] == "sell":
            pending_sells.add(pending.order["mint"])
    for mint, holding in list(state.positions.items()):
        if len(orders) >= caps["max_orders_per_batch"]:
            break
        if mint in pending_sells:
            continue
        if state.slot < sell_blocked.get(mint, -1):
            continue
        curve = state.curves.get(mint)
        if curve is None or curve.complete:
            continue
        coin = coins.get(mint)
        if coin is None:
            continue
        if mint not in held:
            held[mint] = coin
            coin.entry_slot = state.slot
            coin.peak_gain = 0.0
            coin.tp1_done = False
        # Blended cost basis (moves when a second tranche fills).
        coin.entry_price = holding.cost_lamports / holding.token_amount
        price = _price(curve)
        if coin.entry_price <= 0 or price <= 0:
            continue
        gain = price / coin.entry_price - 1.0
        if gain > coin.peak_gain:
            coin.peak_gain = gain
        tokens = holding.token_amount
        sell = 0
        reason = None
        if gain >= TP2_GAIN:
            sell = tokens
            reason = "tp2"
        elif gain >= TP1_GAIN and not coin.tp1_done:
            sell = tokens // 2
            coin.tp1_done = True
            reason = "tp1"
        elif (coin.peak_gain >= TRAIL_TRIGGER
                and gain <= coin.peak_gain - TRAIL_DROP):
            sell = tokens
            reason = "trail"
        elif (coin.peak_gain >= FADE_TRIGGER
                and gain <= coin.peak_gain - FADE_DROP):
            sell = tokens
            reason = "fade"
        elif gain <= STOP_LOSS:
            sell = tokens
            reason = "stoploss"
        elif (state.slot - coin.entry_slot > TIME_STOP_SLOTS
                and gain < TIME_STOP_GAIN):
            sell = tokens
            reason = "timestop"
        elif (state.slot - coin.last_trade_slot > STALE_SLOTS
                and gain < 0.0):
            sell = tokens
            reason = "stale"
        if sell > 0:
            exit_plan[mint] = reason
            orders.append({
                "side": "sell", "mint": mint,
                "token_amount": sell,
                "max_slippage_bps": SELL_SLIPPAGE_BPS,
            })
            if sell >= tokens:
                held.pop(mint, None)


def on_batch(state, batch):
    # A rejected sell means the market moved past our slippage: do not
    # respam the same exit every batch, wait for the tape to settle.
    for fill in batch.get("fills", []):
        if (fill.get("status") == "rejected"
                and fill.get("side") == "sell"):
            sell_blocked[fill["mint"]] = state.slot + SELL_RETRY_SLOTS

    # Fold this batch's events into the per-coin tape first.
    for event in batch["events"]:
        kind = event["event"]
        mint = event["mint"]
        if kind == "CreateEvent":
            if mint not in coins:
                coins[mint] = Coin(mint, event.get("creator"), event["slot"])
        elif kind == "TradeEvent":
            coin = coins.get(mint)
            if coin is None:
                coin = Coin(mint, event.get("creator"), event["slot"])
                coins[mint] = coin
            _note_trade(coin, event, event["slot"])
    # Track each coin's young peak (for the never-buy-a-rollover filter).
    for event in batch["events"]:
        coin = coins.get(event["mint"])
        curve = state.curves.get(event["mint"])
        if coin is not None and curve is not None:
            price = _price(curve)
            if price > coin.peak_price:
                coin.peak_price = price

    # Drop bookkeeping for coins that completed (their positions auto-close).
    for mint in list(held):
        curve = state.curves.get(mint)
        if curve is not None and curve.complete:
            held.pop(mint, None)

    # Record round trips that closed since the last batch.
    for mint in list(prev_positions):
        if mint not in state.positions:
            coin = coins.get(mint)
            if coin is not None and coin.entry_price > 0:
                curve = state.curves.get(mint)
                price = _price(curve) if curve is not None else 0.0
                gain = price / coin.entry_price - 1.0 if price > 0 else -1.0
                reason = exit_plan.pop(mint, "flatten")
                _record_close(mint, gain, state.slot - coin.entry_slot, reason)
    prev_positions.clear()
    for mint, holding in state.positions.items():
        prev_positions[mint] = (holding.cost_lamports, holding.token_amount)

    orders = []
    _manage_exits(state, batch, orders)
    _try_add(state, batch, orders)
    _try_enter(state, batch, orders)
    return orders


if __name__ == "__main__":
    makefun_bot.run(on_batch, on_done=on_done)
