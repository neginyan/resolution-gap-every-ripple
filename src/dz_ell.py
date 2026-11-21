"""Stage DZ, item 2.2: the search for small true g sqrt(ell) at other ell, among them ell = 960.8 (longdouble), on the combinations where ell = 55.26 found
its smallest values (DZ_探索計画.md section 4).  [numerical]  Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
For each mode ('all', 'bright') and each eta in {1/4, 0.1, 1/ell}: the two (room, family) with the smallest fine-grid value at ell = 55.26 (results_DZ/dz_post.json)
are searched again at ell in {200, 960.8}, and the wide room (Theorem 4's band) at ell = 960.8 with the families S and Pt, with the budget nsample = 160, starts = 3, maxfev = 120 (ell = 960.8 is in longdouble, about 5 times slower),
and every minimiser is re-evaluated on the fine grid.  For eta = 1/ell the value of eta is that of the new ell.
-> results_DZ/dz_ell.json"""
import json, math, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_search as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def job(args):
    ell, mode, room, fam, en, seed = args
    ev = {'1/4': 0.25, '0.1': 0.1, '1/ell': 1 / ell}[en]; t1 = time.time()
    # the objective is log(Q sqrt(ell)) (Q exceeds the double range at most states of ell = 960.8), the penalty for an inadmissible window 1e6 in it
    # the wide band: the class box for L (L^2 <= 1/sigma, r >= sigma^3) with the split form of dz_truth; the other rooms: the box of the main search
    Lc = None if room == 'wide band' else 3.0
    best, nev = S.search(ell, room, fam, ev, starts=3, maxfev=120, seed=seed, mode=mode, nsample=160, pen=1e6, logobj=True, Lcap=Lc)
    vt, o = S.evaluate(best[0][1], ell, room, fam, ev, full=True, mode=mode, M_rule='fine', pen=1e6, logobj=True, Lcap=Lc)
    va = S.evaluate(best[0][1], ell, room, fam, ev, mode='all', M_rule='fine', pen=1e6, logobj=True, Lcap=Lc)
    return {'ell': ell, 'mode': mode, 'room': room, 'family': fam, 'eta': en, 'search value (coarse grid, log)': best[0][0], 'z': best[0][1],
            'log Q sqrt(ell) (fine grid)': va, 'Q sqrt(ell) (fine grid)': math.exp(va) if va < 700 else 'above 1e304 (see the log)',
            'at': S.summarize(vt, o), 'evaluations': nev, 'seconds': time.time() - t1}


def main(ells=(200.0, 960.8), procs=2):
    from multiprocessing import Pool
    t0 = time.time(); P = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_post.json')))['55.26']['rows']
    jobs = []; k = 0
    for mode in ('all', 'bright'):
        for en in ('1/4', '0.1', '1/ell'):
            rr = [r for r in P if r['mode'] == mode and r['eta'] == en and (mode == 'all' or (r['at'].get('W/b (ripple part of den over b)') or 0) >= 1)]
            rr.sort(key=lambda r: r['Q sqrt(ell) (fine grid)'])
            for r in rr[:2]:
                for ell in ells:
                    k += 1; jobs.append((ell, mode, r['room'], r['family'], en, 9000 + k))
            for fam in ('S', 'Pt'):             # the wide room of Theorem 4 at ell = 960.8
                k += 1; jobs.append((960.8, mode, 'wide band', fam, en, 9000 + k))
    rows = []
    with Pool(procs) as Pl:
        for r in Pl.imap_unordered(job, jobs):
            rows.append(r); print(r['ell'], r['mode'], r['room'], r['family'], r['eta'], '%.5g' % r['log Q sqrt(ell) (fine grid)'], round(r['seconds']), flush=True)
    rows.sort(key=lambda r: (r['ell'], r['mode'], r['eta'], r['room'], r['family']))
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'rows': rows}
    for ell in ells:
        for mode in ('all', 'bright'):
            for en in ('1/4', '0.1', '1/ell'):
                rr = [r for r in rows if r['ell'] == ell and r['mode'] == mode and r['eta'] == en and (mode == 'all' or (r['at'].get('W/b (ripple part of den over b)') or 0) >= 1)]
                if rr:
                    w = min(rr, key=lambda r: r['log Q sqrt(ell) (fine grid)'])
                    out['smallest Q sqrt(ell), ell = %s [%s], eta = %s' % (ell, mode, en)] = {'value': w['Q sqrt(ell) (fine grid)'], 'log': w['log Q sqrt(ell) (fine grid)'], 'room': w['room'], 'family': w['family']}
    out['ok'] = all(math.isfinite(r['log Q sqrt(ell) (fine grid)']) for r in rows) and len(rows) == len(jobs)
    out['wide room at ell = 960.8: smallest log Q sqrt(ell) found (any family, eta, mode)'] = min((r['log Q sqrt(ell) (fine grid)'] for r in rows if r['room'] == 'wide band'), default=None)
    out['seconds'] = time.time() - t0
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_ell.json'), 'w'), indent=1)
    return out


if __name__ == '__main__':
    main()
