# SEND + MORE = MONEY: every letter a distinct digit.
import cpmpy as cp

s, e, n, d, m, o, r, y = letters = cp.intvar(0, 9, shape=8, name=list("sendmory"))
model = cp.Model(
    cp.AllDifferent(letters),
    s > 0,
    m > 0,
    1000 * s + 100 * e + 10 * n + d + 1000 * m + 100 * o + 10 * r + e
    == 10000 * m + 1000 * o + 100 * n + 10 * e + y,
)
