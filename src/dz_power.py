"""Stage DZ, item 2.2: THE POWER OF THE SEARCH FOR THE TRUE g sqrt(ell), and the swap of eta at the minimisers (DZ_探索計画.md section 6).  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
Input: results_DZ/dz_search_55.26.json (the main search).  At ell = 55.26, on the combination (room, family, eta) where the main search found its smallest value
('all' states) and on the one where it found its smallest ripple-dominated value ('bright'), with the same search budget and the same seeds as the main search:
  (p1) 'drop III': the term <E^2 X1^2/h phi> left out of N_phi; must be lower than the true value by more than 1e-3 (relative) at the true minimiser, and the
       search with the wrong version must find a value below the true minimum;
  (p2) 'sign': the scores computed with 1 - E R in place of h; must differ from the true value by more than 1e-3 at one of the minimisers of the narrow room
       (the largest difference over them is reported; at a single state the factors 1/h may act weakly, see dz_sandwich.py);
  (p3) a planted bowl: the objective replaced by min(v, m (0.3 + 0.7 |z - z*|^2/w^2)), m the true minimum, w = 0.35, at a point z* of the unit cube drawn
       uniformly (seed 20261120 + k; z* is not stored); its bottom 0.3 m is a new global minimum; the search (same budget) must find a value below 0.5 m;
  (p4) 'sandwich' (an artificial worst case of the sandwich at eta = 1/4: den's brightness part times 1/(1 - eta)^2, the ripple part of N_phi times
       1/(1 + eta)^2): the search must find a value at least 5% below the true minimum of the same family and room at eta = 1/4.
SWAP (fine grid): at the minimiser of every combination with eta = 1/4 and 0.1, the same window shape and the same state with eta = 1/ell; the ratio Q(eta)/Q(1/ell).
-> results_DZ/dz_power.json"""
import json, math, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_search as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main(ell=55.26):
    t0 = time.time(); M = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_search_%s.json' % ell)))
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'ell': ell}
    rows = M['rows']; k = 0
    for mode in ('all', 'bright'):
        w = min((r for r in rows if r['mode'] == mode and r['eta'] in ('1/4', '0.1')), key=lambda r: r['min Q sqrt(ell)'])
        room, fam, en, ev = w['room'], w['family'], w['eta'], w['eta value']
        zb = w['z of the 5 best starts'][0]; vt = S.evaluate(zb, ell, room, fam, ev, mode=mode)
        res = {'combination': [room, fam, en], 'true minimum (main search)': w['min Q sqrt(ell)'], 'true value at the minimiser (re-evaluated)': vt}
        for var in ('drop III', 'sign'):
            vw = S.evaluate(zb, ell, room, fam, ev, variant=var, mode=mode)
            res[var + ': value at the true minimiser'] = vw; res[var + ': relative difference'] = abs(vw / vt - 1)
        k += 1; bw, _ = S.search(ell, room, fam, ev, seed=5000 + k, variant='drop III', mode=mode)
        res['drop III: search minimum'] = bw[0][0]
        res['(p1) caught'] = bool(res['drop III: relative difference'] > 1e-3 and bw[0][0] < w['min Q sqrt(ell)'])
        P2 = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_post.json')))[str(ell)]['rows']; ds = []
        for r in rows:
            if r['room'] != 'narrow': continue
            z = r['z of the 5 best starts'][0]; a = S.evaluate(z, ell, 'narrow', r['family'], r['eta value'], M_rule='fine')
            if a >= 1e3: continue
            ds.append(abs(S.evaluate(z, ell, 'narrow', r['family'], r['eta value'], variant='sign', M_rule='fine') / a - 1))
        res['sign: largest relative difference over the minimisers of the narrow room'] = max(ds)
        res['(p2) caught'] = bool(max(ds) > 1e-3)
        rng = np.random.default_rng(20261120 + k); zs = rng.random(len(zb)); m = w['min Q sqrt(ell)']
        k += 1; bd, _ = S.search(ell, room, fam, ev, seed=6000 + k, dip=(zs, m), mode=mode)
        res['(p3) planted bowl: bottom (0.3 x true minimum)'] = 0.3 * m; res['(p3) planted bowl: search minimum'] = bd[0][0]
        res['(p3) planted bowl: distance of the found point to z* (unit cube)'] = float(np.linalg.norm(np.array(bd[0][1]) - zs))
        res['(p3) caught'] = bool(bd[0][0] < 0.5 * m)
        r4 = [r for r in rows if r['mode'] == mode and r['room'] == room and r['family'] == fam and r['eta'] == '1/4'][0]
        k += 1; bs, _ = S.search(ell, room, fam, 0.25, seed=7000 + k, variant='sandwich', mode=mode)
        res['(p4) sandwich variant at eta = 1/4: search minimum'] = bs[0][0]; res['(p4) true minimum at eta = 1/4'] = r4['min Q sqrt(ell)']
        res['(p4) caught'] = bool(bs[0][0] < 0.95 * r4['min Q sqrt(ell)'])
        out['power, ' + mode] = res
        print(mode, json.dumps(res)[:600], flush=True)
    sw = []
    for r in rows:
        if r['eta'] == '1/ell': continue
        z = r['z of the 5 best starts'][0]
        v1 = S.evaluate(z, ell, r['room'], r['family'], r['eta value'], mode=r['mode'], M_rule='fine'); v2 = S.evaluate(z, ell, r['room'], r['family'], 1 / ell, mode=r['mode'], M_rule='fine')
        sw.append({'mode': r['mode'], 'room': r['room'], 'family': r['family'], 'eta': r['eta'], 'Q(eta)': v1, 'Q(1/ell) same shape and state': v2, 'ratio': v1 / v2})
    out['swap of eta at the minimisers'] = sw
    for mode in ('all', 'bright'):
        s2 = [s for s in sw if s['mode'] == mode and s['Q(eta)'] < 1e3 and s['Q(1/ell) same shape and state'] < 1e3]
        if s2:
            m = min(s2, key=lambda s: s['ratio'])
            out['smallest ratio Q(eta)/Q(1/ell) at the minimisers, ' + mode] = m
    out['ok'] = all(out['power, ' + m]['(p%d) caught' % i] for m in ('all', 'bright') for i in (1, 2, 3, 4))
    out['seconds'] = time.time() - t0
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_power.json'), 'w'), indent=1)
    return out


if __name__ == '__main__':
    main()
