"""Stage DY, item 2.4 (first step, before the interval runs): the corner family F1 at ell = 55.26 searched again with n = 1500 (DX report section 3.3 recommended it).
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).  [numerical search; not a proof]
Ends: chord A (lam = 1, remainders at eta = 0) and chord B (lam = 4/5, remainders at 1/4); the J lines of dx_search.coeffs_J; only the family 'F1 corner'
(plus the seeds of paper I's search).  POWER: the corner dip of paper I (depth 5, its widths) must be found by the same search (n = 1500, family F1 only).
-> results_DY/dy_corner.json"""
import json, math, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dj_lines as J, dj_search as S, dx_search as X


def one(name, ell, n=1500, seed=41, plant=None):
    lam, et, mode = X.CASES[name]; J.coeffs = X.coeffs_J(lam, et, mode)
    try:
        rng = np.random.default_rng(seed); seeds = S.seeds_all(ell)
        fy, y, nev, fam, nan = S.search(ell, rng, n=n, steps1=20, steps2=60, plant=plant, seeds=seeds, only=('F1 corner',))
    finally:
        J.coeffs = X._C0
    return {'(F^2 - 1) ell at the minimum': float(J.margin(np.array([fy]), ell)[0]), 'state': [float(v) for v in y], 'evaluations': int(nev), 'nan': int(nan),
            'family of the lowest walker': S.LAST.get('family of the lowest walker')}


def run(ell=55.26):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'ell': ell, 'family': 'F1 corner (+ seeds)', 'n': 1500}
    cc = np.array([math.log(ell / 4 - 9.0), -ell / 2 + 5.0, ell + 11.0, -17.0, -0.7]); ww = np.array([0.3, 3.0, 3.0, 3.0, 1.0])
    for name in ('chord A (lam 1, eta 0)', 'chord B (lam 0.8, eta 1/4)'):
        out[name] = one(name, ell); print(name, out[name]['(F^2 - 1) ell at the minimum'], round(time.time() - t0), flush=True)
        p = one(name, ell, seed=43, plant=(cc, ww, 5.0)); out['power: corner dip of paper I, ' + name] = {'margin': p['(F^2 - 1) ell at the minimum'], 'found (<= 5.5)': p['(F^2 - 1) ell at the minimum'] <= 5.5}
        print('power', name, p['(F^2 - 1) ell at the minimum'], round(time.time() - t0), flush=True)
    out['ok'] = all(out[k]['(F^2 - 1) ell at the minimum'] >= 10 for k in ('chord A (lam 1, eta 0)', 'chord B (lam 0.8, eta 1/4)')) and all(v['found (<= 5.5)'] for k, v in out.items() if k.startswith('power'))
    out['seconds'] = time.time() - t0
    return out


if __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DY'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dy_corner.json'), 'w'), indent=1); print(r['ok'])
