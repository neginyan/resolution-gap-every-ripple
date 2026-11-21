"""Stage DX, item 2.3: THE ATTEMPT TO BREAK THE CONCLUSION OF PAPER J (the lines of dx_table in float log form; the search tools of dj_search).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  [numerical search; not a proof]
CLAIM SEARCHED: for every state of the class and P <= Pbar, F_J := min_a max_k f_k(a) satisfies (F_J^2 - 1) ell >= 10, where f_k uses the J lines at the end
  A (lam = 1; uniform: remainders at 1/4; chord: remainders at 0) and the end B (lam = 4/5, remainders at 1/4, target (2 lam - 1) = 3/5 on d1, d3, lam on d2, d4),
  and for the uniform form also lam = 0.9 (between the ends).  The ceiling Pbar (H') is that of dj_search (it does not involve the ripple).
FAMILIES: dj_search.families (corner, global, E1-E5, N1-N5) and the minima of the search of paper I (dj_search.seeds_all) as seeds.
POWER: a planted dip (depth 5 in (F^2 - 1) ell) at the minimiser must be found; main lines dropped (P2z; hFz) must give (F^2 - 1) ell < 10 somewhere;
  the old FrB1 coefficient and the forgotten separation of eta are NOT visible to this search (they make the table larger, not smaller): they are the work of
  the audit dx_table (reported there).  DIAGNOSTIC (not a wrong version): the target with coefficient 1 at eta = 1/4 (gains 4/5).
-> results_DX/dx_search.json"""
import json, math, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dj_lines as J, dj_search as S

_C0 = J.coeffs
QB = 0.25


def coeffs_J(lam, etr, mode='uniform', x1new=True, target_one=False):
    def f(ell, lmu, lr, lB, lk, lP, gam=1.0, eta=None):
        T, aux = _C0(ell, lmu, lr, lB, lk, lP, gam=gam, eta=etr)
        e = etr; lfl = -math.log(1 + e)
        def sh(tag, d):
            t, s, L = T[tag]; T[tag] = (t, s, L + d)
        r = np.exp(np.asarray(lr, float)); kE = np.sqrt(r / (1 + r)); k1 = 1 + (e + 0.184) * kE
        if mode == 'chord':
            Kz2 = 8 * ell + 100; ringf = 1 - np.exp(math.log(Kz2 * (1 + e) / (8 * (1 - e))) - np.asarray(lB, float))
            with np.errstate(all='ignore'): sh('P2z', np.log(np.maximum(lam - (1 - ringf), 1e-300)) - np.log(ringf) - lfl)
        else:
            sh('P2z', math.log(lam) - lfl)
        sh('hFz', math.log(lam) - lfl)
        t_, s_, L_ = T['cKz']; T['cKz'] = (t_, s_, L_ + math.log(lam) - lfl)
        if not target_one:
            if mode == 'chord':
                sh('d1', np.log(((2 * lam - 1) * (1 + 0.184 * kE) + e * kE) / k1)); sh('d3', np.log(((2 * lam - 1) + 2 * e * kE) / (1 + 2 * e * kE)))
            else:
                sh('d1', math.log(2 * lam - 1)); sh('d3', math.log(2 * lam - 1))
            sh('d2', math.log(lam * (1 - e))); sh('d4', math.log(lam * (1 - e)))
        if x1new:
            U1 = QB * math.sqrt(2 * ell + 3.1) + 1e-6; X1 = U1 / (1 - QB); X1B = U1 / (1 - e) + math.sqrt(e * e / (math.e * (1 - e) ** 2))
            sh('B1m', math.log(X1B / X1))
        return T, aux
    return f


CASES = {'uniform A (lam 1)': (1.0, 0.25, 'uniform'), 'uniform mid (lam 0.9)': (0.9, 0.25, 'uniform'), 'uniform B (lam 0.8)': (0.8, 0.25, 'uniform'),
         'chord A (lam 1, eta 0)': (1.0, 1e-30, 'chord'), 'chord B (lam 0.8, eta 1/4)': (0.8, 0.25, 'chord')}


def run_case(name, ell, n=800, seed=0, drop=(), plant=None, x1new=True, target_one=False, steps=(20, 60)):
    lam, et, mode = CASES[name]; J.coeffs = coeffs_J(lam, et, mode, x1new, target_one)
    try:
        rng = np.random.default_rng(seed + int(ell) % 1000)
        try: seeds = S.seeds_all(ell)
        except Exception: seeds = None
        fy, y, nev, fam, nan = S.search(ell, rng, n=n, steps1=steps[0], steps2=steps[1], plant=plant, seeds=seeds, drop=drop)
    finally:
        J.coeffs = _C0
    mg = float(J.margin(np.array([fy]), ell)[0])
    return {'case': name, 'ell': ell, '(F^2 - 1) ell at the minimum': mg, 'log F': fy, 'state': [float(v) for v in y], 'evaluations': int(nev), 'nan': int(nan),
            'family of the lowest walker': S.LAST.get('family of the lowest walker'), 'per family after polishing (log F)': dict(S.LAST.get('per family after polishing', {}))}


def run(ells=(55.26, 960.8, 1e4, 1e6)):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'claim': '(F_J^2 - 1) ell >= 10', 'main': {}, 'power': {}, 'diagnostic': {}}
    part = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX', 'dx_search_partial.json')   # resume (each case is deterministic: its own seed)
    done = json.load(open(part)) if os.environ.get('DX_RESUME') == '1' and os.path.exists(part) else {}
    def keep(sec, key, fn):
        if key in done.get(sec, {}): out[sec][key] = done[sec][key]; return out[sec][key], True
        r = fn(); out[sec][key] = r; json.dump(out, open(part, 'w'), indent=1, default=str); return r, False
    for ell in ells:
        for name in CASES:
            r, old = keep('main', '%s ell=%g' % (name, ell), lambda: run_case(name, ell))
            if old: continue
            print(name, ell, round(r['(F^2 - 1) ell at the minimum'], 4), r['family of the lowest walker'], round(time.time() - t0), flush=True)
    # power at ell = 55.26 and 960.8, end B (uniform) and A (chord)
    for ell in (55.26, 960.8):
        for name in ('uniform B (lam 0.8)', 'chord A (lam 1, eta 0)'):
            m = out['main']['%s ell=%g' % (name, ell)]; c = list(m['state']); w = [0.5, 0.5, 0.5, 0.5, 0.25]
            # planted dips: the three of paper I (dj_search.run_power: corner, narrow, low mu; depth 5, its widths).  The first design of this stage (a dip of
            # widths 0.5 next to the minimiser) was too narrow to be felt by the walkers at ell = 55.26 (kept below, not counted).
            R = S.ranges(ell); line = 2 * math.log(ell) - ell
            dips = {'corner': (np.array([math.log(ell / 4 - 9.0), -ell / 2 + 5.0, ell + 11.0, -17.0, -0.7]), np.array([0.3, 3.0, 3.0, 3.0, 1.0])),
                    'narrow': (np.array([math.log(3.0), line - 0.5 * math.log(3.0) - 4.0, R[2, 0] + 13.0, -ell + 31.0, 0.0]), np.array([0.5, 3.0, 3.0, 3.0, 1.0])),
                    'low mu': (np.array([-0.4 * ell, -0.3 * ell, R[2, 0] + 0.3 * (R[2, 1] - R[2, 0]), -0.5 * ell, -2.0]), np.array([0.05 * ell] * 4 + [2.0]))}
            for dn, (cc, ww) in dips.items():
                keep('power', 'planted dip %s (paper I design, depth 5) %s ell=%g' % (dn, name, ell), lambda: (lambda r: {'found (margin <= 5.5)': r['(F^2 - 1) ell at the minimum'] <= 5.5,
                     'margin': r['(F^2 - 1) ell at the minimum']})(run_case(name, ell, plant=(cc, ww, 5.0), seed=31)))
            for d in (('P2z',), ('hFz',)):
                keep('power', 'drop %s %s ell=%g' % (d[0], name, ell), lambda: (lambda r: {'caught (margin < 10)': r['(F^2 - 1) ell at the minimum'] < 10,
                     'margin': r['(F^2 - 1) ell at the minimum']})(run_case(name, ell, drop=d, seed=7, n=400)))
            print('power', ell, name, round(time.time() - t0), flush=True)
        keep('diagnostic', 'coefficient 1 at eta = 1/4 (gains 4/5, target not scaled) ell=%g' % ell,
             lambda: run_case('uniform B (lam 0.8)', ell, target_one=True, seed=9, n=400)['(F^2 - 1) ell at the minimum'])
        keep('diagnostic', 'old FrB1 X1 (the table line B1m is smaller: the search sees a larger or equal margin) ell=%g' % ell,
             lambda: run_case('uniform B (lam 0.8)', ell, x1new=False, seed=9, n=400)['(F^2 - 1) ell at the minimum'])
    out['power, first design (a dip of widths 0.5 next to the minimiser; too narrow, not counted)'] = {k: v for k, v in done.get('power', {}).items() if k.startswith('planted dip (depth 5)')}
    out['main ok (every minimum >= 10)'] = all(v['(F^2 - 1) ell at the minimum'] >= 10 for v in out['main'].values())
    out['power ok'] = all(list(v.values())[0] for v in out['power'].values())
    out['seconds'] = time.time() - t0
    return out


def retry():
    """the planted dips that the first search missed, searched again: a larger population (n = 1500), another seed, and the widths x 3 (as in paper I)."""
    d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); r0 = json.load(open(os.path.join(d, 'dx_search.json')))
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'retried': {}}
    for k, v in r0['power'].items():
        if not k.startswith('planted dip') or v['found (margin <= 5.5)']: continue
        dn = k.split('planted dip ')[1].split(' (paper I')[0]; name = k.split('depth 5) ')[1].split(' ell=')[0]; ell = float(k.split('ell=')[1])
        R = S.ranges(ell); line = 2 * math.log(ell) - ell
        dips = {'corner': (np.array([math.log(ell / 4 - 9.0), -ell / 2 + 5.0, ell + 11.0, -17.0, -0.7]), np.array([0.3, 3.0, 3.0, 3.0, 1.0])),
                'narrow': (np.array([math.log(3.0), line - 0.5 * math.log(3.0) - 4.0, R[2, 0] + 13.0, -ell + 31.0, 0.0]), np.array([0.5, 3.0, 3.0, 3.0, 1.0])),
                'low mu': (np.array([-0.4 * ell, -0.3 * ell, R[2, 0] + 0.3 * (R[2, 1] - R[2, 0]), -0.5 * ell, -2.0]), np.array([0.05 * ell] * 4 + [2.0]))}
        cc, ww = dips[dn]; res = {}
        for lab, n, sd, wf in (('n = 1500, seed 32', 1500, 32, 1.0), ('n = 800, seed 31, widths x 3', 800, 31, 3.0)):
            m = run_case(name, ell, plant=(cc, ww * wf, 5.0), seed=sd, n=n)['(F^2 - 1) ell at the minimum']; res[lab] = {'margin': m, 'found (margin <= 5.5)': m <= 5.5}
            print(k, lab, m, flush=True)
        out['retried'][k] = res
    out['ok'] = all(any(x['found (margin <= 5.5)'] for x in v.values()) for v in out['retried'].values())
    json.dump(out, open(os.path.join(d, 'dx_search_retry.json'), 'w'), indent=1, default=str); print(out['ok'])


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'retry':
    retry()
elif __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dx_search.json'), 'w'), indent=1, default=str); print(r['main ok (every minimum >= 10)'], r['power ok'], r['seconds'])
