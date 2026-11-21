"""Stage DQ (addendum 1.2): the constant M4 of Lemma CZ-2 for larger y.  Python 3.11 grammar.  Interval arithmetic of dl_interval with the watch of stage DO
(decimal.Inexact trapped in the default context while the interval functions run).
  f(u, y) := e^{-u/2} [ ((1 + u)/2) (1 + u cosh sqrt(y u)) + cosh sqrt(y u) ],   M4(y) := sup_{u >= 0} f(u, y).
  Lemma DQ-M1 [proof, in DQ_証明まとめ.md]: |Xi_1(u, y)| <= y f(u, y) for y >= 0, and M4 is nondecreasing in y.
  Lemma DQ-M2 [computer-assisted]: M4(1e-4) <= 2.07.
     u in [0, 60]: pieces [u0, u1]; on a piece f <= e^{-u0/2} [((1 + u1)/2)(1 + u1 cosh sqrt(y u1)) + cosh sqrt(y u1)]   (e^{-u/2} decreases, the bracket increases).
     u >= 60: sqrt(y u) <= 0.01 sqrt(u) <= 0.0013 u, 1 + u e^c <= (1 + u) e^c and cosh c <= e^c, so f <= g(u) := e^{-0.4987 u} ((1 + u)^2/2 + 1);
              d/du ln g = -0.4987 + (1 + u)/((1 + u)^2/2 + 1) <= -0.4987 + 2/(1 + u) < 0 for u >= 60, so sup_{u >= 60} f <= g(60).
  Also: the inequality d_y := 1 - (1 - y) e^{-y/2} >= 1.5 y - (5/8) y^2 used in the line P3z + P4z (proof in the document; checked here on y in [0, 1e-4]).
  POWER: M4(1e-4) <= 2.04 must FAIL (a lower bound of f at one point exceeds 2.04); M4(1) <= 2.07 must FAIL; d_y >= 1.5 y must FAIL.
-> results/dq_m4.json"""
import json, time, functools, decimal, sys, os
from decimal import Decimal as Dc, localcontext
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dl_interval as V
from dl_interval import Iv, exp, sqrt


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


def cosh(x): return (exp(x) + exp(-x)) / 2


def bracket(u, y):
    c = cosh(sqrt(u * y)); return (1 + u) / 2 * (1 + u * c) + c


@trapped
def sup_f(y, umax=Dc(60), h_lo=Dc('0.005'), h_hi=Dc('0.05'), usplit=Dc(20)):
    """an upper bound of sup_{u in [0, umax]} f(u, y) (interval arithmetic; y a Decimal) and the u where the piece bound is largest."""
    Y = Iv(y); best = Dc(0); arg = None; u0 = Dc(0)
    while u0 < umax:
        h = h_lo if u0 < usplit else h_hi; u1 = u0 + h                     # exact decimal sums (few digits)
        val = (exp(-Iv(u0) / 2) * bracket(Iv(u1), Y)).hi
        if val > best: best, arg = val, u0
        u0 = u1
    return best, arg


@trapped
def tail(y, u=Dc(60)):
    """g(60) (an upper bound of f on u >= 60 for y <= 1e-4) and the two facts used: sqrt(y u) <= 0.0013 u at u >= 60, and the sign of d/du ln g at 60."""
    assert y <= Dc('1e-4')
    U = Iv(u); g = exp(-Iv(Dc('0.4987')) * U) * ((1 + U) ** 2 / 2 + 1)
    c_ok = (Dc('0.01') / sqrt(U)).hi <= Dc('0.0013')                     # 0.01 sqrt(u) <= 0.0013 u  <=>  0.01/sqrt(u) <= 0.0013, and 1/sqrt(u) decreases
    d_ok = (-Iv(Dc('0.4987')) + 2 / (1 + U)).hi < 0
    return g.hi, c_ok, d_ok


@trapped
def f_low(u, y):
    """a lower bound of f(u, y) at one point (for the power checks)."""
    U = Iv(u); return (exp(-U / 2) * bracket(U, Iv(y))).lo


@trapped
def dy_check(n=2000, ymax=Dc('1e-4')):
    """d_y - (1.5 y - (5/8) y^2) >= 0 on a grid of y in (0, ymax] (lower ends), and the wrong version d_y >= 1.5 y (must fail somewhere)."""
    worst = None; wrong_fails = False
    for i in range(1, n + 1):
        y = Iv(ymax * i / n)
        dy = 1 - (1 - y) * exp(-y / 2)
        s = (dy - (Iv(Dc('1.5')) * y - Iv(Dc('0.625')) * y * y)) / (y * y)
        worst = s.lo if worst is None else min(worst, s.lo)
        if (dy - Iv(Dc('1.5')) * y).hi < 0: wrong_fails = True
    return worst, wrong_fails


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    rows = {}
    for y in ('0', '1e-6', '6.5e-5', '1e-4'):
        b, arg = sup_f(Dc(y)); rows[y] = {'upper bound of sup over u in [0, 60]': float(b), 'at the piece starting at u =': float(arg)}
        print('y', y, rows[y], flush=True)
    gt, c_ok, d_ok = tail(Dc('1e-4'))
    out['M4(y): upper bounds (interval arithmetic, pieces of width 0.005 on [0, 20] and 0.05 on [20, 60])'] = rows
    out['tail u >= 60 (y <= 1e-4): g(60) upper bound, sqrt(y u) <= 0.0013 u, d/du ln g < 0'] = [float(gt), c_ok, d_ok]
    M = max(Dc(str(rows['1e-4']['upper bound of sup over u in [0, 60]'])), Dc(str(gt)))
    out['M4(1e-4) <= (both parts)'] = float(M)
    mono = [rows[y]['upper bound of sup over u in [0, 60]'] for y in ('0', '1e-6', '6.5e-5', '1e-4')]
    out['the upper bounds increase with y (as Lemma DQ-M1 (ii) says; information)'] = bool(all(a <= b for a, b in zip(mono, mono[1:])))
    ws, wf = dy_check()
    out["d_y >= 1.5 y - (5/8) y^2 on y in (0, 1e-4]: smallest (d_y - 1.5 y + 0.625 y^2)/y^2 (lower end; the series gives 7 y/48 > 0)"] = float(ws)
    lo = max(f_low(Dc(k) / 100, Dc('1e-4')) for k in range(150, 260))
    lo1 = max(f_low(Dc(k) / 10, Dc(1)) for k in range(1, 60))
    out['POWER'] = {'M4(1e-4) <= 2.04 fails (largest lower bound of f on a grid)': [float(lo), bool(lo > Dc('2.04'))],
                    'M4(1) <= 2.07 fails': [float(lo1), bool(lo1 > Dc('2.07'))], 'd_y >= 1.5 y fails somewhere in (0, 1e-4]': wf}
    out['ok'] = bool(M <= Dc('2.07') and c_ok and d_ok and ws >= 0 and lo > Dc('2.04') and lo1 > Dc('2.07') and wf)
    out['seconds'] = time.time() - t0; print(json.dumps(out, indent=1)[:1500])
    if save: json.dump(out, open('results/dq_m4.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    sys.exit(0 if run()['ok'] else 1)
