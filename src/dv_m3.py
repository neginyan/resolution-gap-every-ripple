"""Stage DV, section 2.1: the constants M1, M2, M4 for y <= 1e-40 by hand (Theorem 3 needs only y <= sigma^2/4 <= 3e-49).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  Plan: DU_探索計画.md (section DV, written before computing).
CLAIM (Lemma 27 of the paper I draft, proof by hand; this script only CHECKS it, with 60-digit decimals and grids, and runs the power checks):
  for 0 <= y <= 1e-40:  M1(y) <= (1 + 1e-38) 2/e,  M2(y) <= (1 + 1e-38)(4u* + 2) e^{-u*/2}, u* = (3 + sqrt17)/2,
                        M4(y) <= (1 + 1e-38)(4 + 2 sqrt2) e^{-(1 + sqrt2)/2};
  numerically 0.73576, 2.73761, 2.04208 (upper ends), so Qb(M2/2 + M1) <= 0.5263 <= 1 and M4 <= 2.07.
-> results/dv_m3.json"""
import json, math, sys, os, time
from decimal import Decimal as D, getcontext
import numpy as np
getcontext().prec = 60
HERE = os.path.dirname(os.path.abspath(__file__))


def dcosh(x): e = x.exp(); return (e + 1 / e) / 2


def f1(u, y): return u * (-u / 2).exp() * dcosh((y * u).sqrt())
def f2(u, y): return u * (-u / 2).exp() * (1 + u * dcosh((y * u).sqrt()))
def f4(u, y):
    c = dcosh((y * u).sqrt()); return (-u / 2).exp() * ((1 + u) / 2 * (1 + u * c) + c)


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    E = D(1).exp(); s17 = D(17).sqrt(); s2 = D(2).sqrt()
    us = (3 + s17) / 2; u4 = 1 + s2
    M1c = 2 / E; M2c = (4 * us + 2) * (-us / 2).exp(); M4c = (4 + 2 * s2) * (-u4 / 2).exp()
    out['closed forms (60 digits)'] = {'M1(0) = 2/e': str(M1c)[:20], 'u*': str(us)[:20], 'M2(0) = (4u*+2)e^{-u*/2}': str(M2c)[:20], 'u4 = 1+sqrt2': str(u4)[:20], 'M4(0) = (4+2sqrt2)e^{-(1+sqrt2)/2}': str(M4c)[:20]}
    out['identities'] = {'u*^2 - 3u* - 2': float(us * us - 3 * us - 2), 'u4^2 - 2u4 - 1': float(u4 * u4 - 2 * u4 - 1), 'u*(1+u*) - (4u*+2)': float(us * (1 + us) - (4 * us + 2)),
                         'f4(u4,0) - M4c': float(f4(u4, D(0)) - M4c), 'f2(u*,0) - M2c': float(f2(us, D(0)) - M2c), 'f1(2,0) - M1c': float(f1(D(2), D(0)) - M1c)}
    fac = 1 + D('1e-38')
    ub = {k: float(v * fac) for k, v in (('M1', M1c), ('M2', M2c), ('M4', M4c))}
    out['claimed upper bounds for y <= 1e-40'] = ub
    out['Qb(M2/2 + M1) <= (needs <= 1)'] = float(D('0.25') * (M2c * fac / 2 + M1c * fac)); out['c2 = 2Qb/e'] = float(D('0.5') / E)
    # the y = 0 functions: grid maximum vs closed form (the closed form must be the maximum)
    u = np.linspace(0, 600, 1_000_001); e = np.exp(-u / 2)
    g = {'M1': float(np.max(u * e)), 'M2': float(np.max(u * (1 + u) * e)), 'M4': float(np.max(e * ((u * u + 2 * u + 3) / 2)))}
    out['grid maxima at y = 0 (must be <= closed form, within 1e-12)'] = g
    ok_grid = all(g[k] <= float({'M1': M1c, 'M2': M2c, 'M4': M4c}[k]) + 1e-12 for k in g)
    # the factor 1 + 1e-38 on [0, 100] at y = 1e-40 (and 1e-49): f(u, y)/f(u, 0) - 1 is largest at u = 100 (it increases with u); also sample
    rat = {}
    for y in (D('1e-40'), D('1e-49')):
        worst = D(0)
        for uu in [D(k) / 4 for k in range(1, 401)]:
            for fn in (f1, f2, f4):
                worst = max(worst, fn(uu, y) / fn(uu, D(0)) - 1)
        rat[str(y)] = float(worst)
    out['largest f(u,y)/f(u,0) - 1 on u in (0, 100] (must be <= 1e-38)'] = rat
    ok_fac = all(v <= 1e-38 for v in rat.values())
    # tail u >= 100: sqrt(y u) <= 0.01 u for y <= 1e-4 u; bounds e^{-0.49u} x polynomial at u = 100, log-derivatives negative
    U = D(100); k = D('0.49')
    tails = {'M1 tail u e^{-0.49u} at 100': float(U * (-k * U).exp()), 'M2 tail u(1+u)e^{-0.49u}': float(U * (1 + U) * (-k * U).exp()),
             'M4 tail ((1+u)^2/2+1)e^{-0.49u}': float(((1 + U) ** 2 / 2 + 1) * (-k * U).exp())}
    out['tails at u = 100'] = tails
    ok_tail = all(v < 1e-15 for v in tails.values()) and float(1 / U + 1 / (1 + U) - k) < 0 and float(2 / U - k) < 0
    # direct check of the tail inequality f(u, y) <= tail bound for u in [100, 2000] at y = 1e-40 (60 digits)
    tail_ok = all(f2(D(uu), D('1e-40')) <= D(uu) * (1 + D(uu)) * (-k * D(uu)).exp() and f4(D(uu), D('1e-40')) <= ((1 + D(uu)) ** 2 / 2 + 1) * (-k * D(uu)).exp() for uu in range(100, 2001, 50))
    # POWER
    p = {}
    p['V1 delta = 0 at y = 1e-4: M2(1e-4) grid max > M2(0)'] = float(max(f2(D(x) / 1000, D('1e-4')) for x in range(3400, 3800))) - float(M2c)
    p['V1 delta = 0 at y = 1e-4: M4(1e-4) grid max > M4(0)'] = float(max(f4(D(x) / 1000, D('1e-4')) for x in range(2300, 2600))) - float(M4c)
    p['V2 factor 1+1e-38 at y = 1e-30: f2(100,y)/f2(100,0) - 1 (must exceed 1e-38)'] = float(f2(U, D('1e-30')) / f2(U, D(0)) - 1)
    wrong_us = (3 + D(13).sqrt()) / 2
    p['V3 u* -> (3+sqrt13)/2: grid max minus the wrong closed value (must be > 0)'] = g['M2'] - float(wrong_us * (1 + wrong_us) * (-wrong_us / 2).exp())
    p['V3 u = 3.5: grid max minus value (must be > 0)'] = g['M2'] - float(D('3.5') * D('4.5') * (D('-1.75')).exp())
    w4 = 1 + D(3).sqrt()
    p['V3 M4 at 1+sqrt3: grid max minus value (must be > 0)'] = g['M4'] - float(((w4 * w4 + 2 * w4 + 3) / 2) * (-w4 / 2).exp())
    # V4: tail with exponent 0.5 (c dropped) must fail somewhere at y = 1e-4 (large u)
    uu = D(10) ** 6; y4 = D('1e-4')
    dlt = f2(uu, y4) - uu * (1 + uu) * (-uu / 2).exp()
    p['V4 tail without c at y = 1e-4, u = 1e6: log10 of the ratio f2/(u(1+u)e^{-u/2}) (must be > 0)'] = float((f2(uu, y4) / (uu * (1 + uu) * (-uu / 2).exp())).log10()) if dlt > 0 else -1.0
    ok_pow = all(v > 0 for kk, v in p.items() if not kk.startswith('V2')) and p['V2 factor 1+1e-38 at y = 1e-30: f2(100,y)/f2(100,0) - 1 (must exceed 1e-38)'] > 1e-38
    out['power'] = p
    out['checks'] = {'grid': ok_grid, 'factor': ok_fac, 'tail bounds': ok_tail, 'tail inequality on [100, 2000]': tail_ok, 'power': ok_pow,
                     'Qb(M2/2+M1) <= 1': out['Qb(M2/2 + M1) <= (needs <= 1)'] <= 1, 'M4 <= 2.07': ub['M4'] <= 2.07}
    out['ok'] = all(out['checks'].values()); out['seconds'] = time.time() - t0
    print(json.dumps(out, indent=1))
    if save: json.dump(out, open(os.path.join(HERE, 'results', 'dv_m3.json'), 'w'), indent=1)
    return out


if __name__ == '__main__':
    sys.exit(0 if run()['ok'] else 1)
