"""The map of Theorem 1 (paper I): every state lies in the range of at least one of the five statements.  Python 3.11 grammar.
A state at resolution sigma = e^{-ell} is a value of B = b/sigma^2 in (0, e^{2 ell}] (0 < b <= 1).  The ranges, as stated in the theorems:
  Theorem 2 (narrow):      ell >= 55.26, b <= 1/2, B >= max(2.5e10, 50 (8 ell + 100));
  Theorem 3 (resolution):  ell >= 55.26, b > 1/2  (B > e^{2 ell}/2);
  Theorem 4 (wide):        ell >= 960.8, 8 ell + 100 <= B < ell^4;
  Theorem 5 (very wide):   ell >= 960.8, 0 < B <= 8 ell + 100;
  Theorem H1 of paper H:   55.26 <= ell <= 960.8 and tau >= 20; tau = x/b >= 5e11 sigma^2/b = 5e11/B, so every state with B <= 2.5e10 has tau >= 20.
Test points: ell on a grid from 55.26 to 1e8 (geometric) with every break point (55.26, 960.8 and its neighbours, the crossing points of the boundaries);
for each ell, log B on a grid of (-60, 2 ell] together with every boundary of the five ranges and points just below and above it (relative 1e-12).
Arithmetic: 60-digit decimal in log B.  Also the inequalities of the proof of Theorem 1 (exact rationals):
  50 (8 ell + 100) <= 389320 < 2.5e10 for ell <= 960.8;  ell^4 >= 8.5e11 and ell^4 >= 50 (8 ell + 100) for ell >= 960.8;  5e11/2.5e10 = 20.
Power: without any one statement, or with Theorem 4 narrowed to B < ell^3, or Theorem 2 needing B >= 1e11, a gap is found."""
from decimal import Decimal as D, getcontext
from fractions import Fraction as Fr
import math

getcontext().prec = 60
LN2 = D(2).ln()


def ranges(ell, drop=None, wide_exp=4, narrow_min=D('2.5e10')):
    e2 = 2 * ell; out = []
    lo_n = max(narrow_min, 50 * (8 * ell + 100)).ln()
    if drop != 'narrow' and ell >= D('55.26'): out.append(('narrow', lo_n, e2 - LN2, True, True))         # (name, lo, hi, lo closed, hi closed)
    if drop != 'res' and ell >= D('55.26'): out.append(('res', e2 - LN2, e2, False, True))
    if drop != 'wide' and ell >= D('960.8'): out.append(('wide', (8 * ell + 100).ln(), wide_exp * ell.ln(), True, False))
    if drop != 'verywide' and ell >= D('960.8'): out.append(('verywide', D('-Infinity'), (8 * ell + 100).ln(), False, True))
    if drop != 'H1' and D('55.26') <= ell <= D('960.8'): out.append(('H1', D('-Infinity'), D('2.5e10').ln(), False, True))
    return out


def covered(lB, R):
    for n, lo, hi, lc, hc in R:
        if (lB > lo or (lc and lB == lo)) and (lB < hi or (hc and lB == hi)): return n
    return None


def ells():
    e = [D('55.26'), D('55.262'), D('960.8'), D('960.8') - D('1e-9'), D('960.8') + D('1e-9'), D(10) ** 8]
    k = 300
    for i in range(k + 1): e.append(D('55.26') * (D(10) ** 8 / D('55.26')) ** (D(i) / k))
    return sorted(set(e))


def points(ell, R):
    e2 = 2 * ell; pts = set()
    for i in range(401): pts.add(D(-60) + (e2 + 60) * D(i) / 400)
    for n, lo, hi, lc, hc in R:
        for v in (lo, hi):
            if v.is_finite():
                for f in (D(-1), D(0), D(1)): pts.add(v + f * D('1e-12'))
    for v in (D('2.5e10').ln(), (50 * (8 * ell + 100)).ln(), (8 * ell + 100).ln(), 4 * ell.ln(), e2 - LN2, e2):
        for f in (D(-1), D(0), D(1)): pts.add(v + f * D('1e-12'))
    return sorted(p for p in pts if p <= e2)


def gaps(**kw):
    g = []; n = 0
    for ell in ells():
        R = ranges(ell, **kw)
        for lB in points(ell, R):
            n += 1
            if covered(lB, R) is None: g.append((float(ell), float(lB)))
    return n, g


def proof_inequalities():
    l = Fr(9608, 10); ok = []
    ok.append(50 * (8 * l + 100) <= 389320 < Fr(25 * 10 ** 9))                  # increasing in ell, so the value at 960.8 bounds [55.26, 960.8]
    ok.append(l ** 4 >= Fr(85 * 10 ** 10))                                       # increasing
    ok.append(l ** 4 >= 50 * (8 * l + 100) and 4 * l ** 3 >= 400)                # and the derivative of ell^4 exceeds that of 50 (8 ell + 100) for ell >= 960.8
    ok.append(Fr(5 * 10 ** 11) / Fr(25 * 10 ** 9) == 20)
    return all(ok)


def run():
    n, g = gaps()
    power = {d: len(gaps(drop=d)[1]) > 0 for d in ('narrow', 'res', 'wide', 'verywide', 'H1')}
    power['Theorem 4 narrowed to B < ell^3'] = len(gaps(wide_exp=3)[1]) > 0
    power['Theorem 2 needing B >= 1e11'] = len(gaps(narrow_min=D('1e11'))[1]) > 0
    return {'points': n, 'gaps': g[:5], 'n_gaps': len(g), 'proof inequalities': proof_inequalities(), 'power (a gap must appear)': power,
            'ok': len(g) == 0 and proof_inequalities() and all(power.values())}


if __name__ == '__main__':
    import json; print(json.dumps(run(), indent=1))
