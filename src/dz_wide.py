"""Stage DZ, item 2.2: THE BAND OF THEOREM 4 (8 ell + 100 <= B < ell^4) at ell = 55.26 with the class box for the envelope.  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
The main search (dz_search.py) capped the envelope at L <= 3 (with r >= sigma^2); in this band its minimisers sat at the cap, so the band is searched again
here with the box of the class (L^2 <= 1/sigma by (P0), r >= sigma^3), using the split form of dz_truth for L > 3 (the state with R = 0 in closed form,
Lemma 11 of paper I, plus the ripple part on |w| <~ 14 s).  Objective log(Q sqrt(ell)); every family, eta in {1/4, 0.1, 1/ell}, all states and ripple-dominated
states; budget nsample = 160, starts = 3, maxfev = 120.
WHY THE VALUES ARE LARGE [derivation]: in this band y = (1 - b)^2/(2B) >= 1/(2 ell^4) is not small, and the ripple's part of N_phi, <F (1 - cos(u + ...))>
with u = sqrt(y) s^, is about W y/2: a ripple that carries the denominator pays (a) + (a') >~ y/(4 sigma) = 1/(8 sigma B) (the chirp term cKz of the lines);
a dark ripple pays the background, (a) + (a') >= C0/sqrt(b) (Lemma 11 of paper I).  Both are of order 1/(sigma ell^2) or more.  This supersedes the rows 'wide band' of results_DZ/dz_search_55.26.json.
-> results_DZ/dz_wide.json"""
import json, math, os, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_search as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ELL = 55.26


def job(args):
    mode, fam, en, seed = args; ev = {'1/4': 0.25, '0.1': 0.1, '1/ell': 1 / ELL}[en]; t1 = time.time()
    best, nev = S.search(ELL, 'wide band', fam, ev, seed=seed, mode=mode, starts=3, maxfev=120, nsample=160, pen=1e6, logobj=True, Lcap=None)
    z = best[0][1]
    lv = S.evaluate(z, ELL, 'wide band', fam, ev, M_rule='fine', pen=1e6, logobj=True, Lcap=None)
    v, o = S.evaluate(z, ELL, 'wide band', fam, ev, full=True, mode=mode, M_rule='fine', pen=1e6, logobj=True, Lcap=None)
    return {'mode': mode, 'family': fam, 'eta': en, 'z': z, 'log Q sqrt(ell) (fine grid)': lv, 'Q sqrt(ell) (fine grid)': math.exp(lv) if lv < 700 else None,
            'at': S.summarize(v, o), 'evaluations': nev, 'seconds': time.time() - t1}


def main():
    t0 = time.time(); jobs = []; k = 0
    for mode in ('all', 'bright'):
        for fam in S.FAMS:
            for en in ('1/4', '0.1', '1/ell'):
                k += 1; jobs.append((mode, fam, en, 12000 + k))
    rows = []
    with Pool(2) as P:
        for r in P.imap_unordered(job, jobs):
            rows.append(r); print(r['mode'], r['family'], r['eta'], '%.5g' % r['log Q sqrt(ell) (fine grid)'], round(r['seconds']), flush=True)
    rows.sort(key=lambda r: (r['mode'], list(S.FAMS).index(r['family']), r['eta']))
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'ell': ELL, 'rows': rows}
    for en in ('1/4', '0.1', '1/ell'):
        w = min((r for r in rows if r['eta'] == en), key=lambda r: r['log Q sqrt(ell) (fine grid)'])
        out['smallest Q sqrt(ell), eta = ' + en] = {'value': w['Q sqrt(ell) (fine grid)'], 'log': w['log Q sqrt(ell) (fine grid)'], 'family': w['family'], 'mode': w['mode'],
                                                   'L': w['at'].get('L'), 'W/b': w['at'].get('W/b (ripple part of den over b)'), 'mu': w['at'].get('mu')}
    out['ok'] = len(rows) == len(jobs) and all(math.isfinite(r['log Q sqrt(ell) (fine grid)']) for r in rows)
    out['seconds'] = time.time() - t0
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_wide.json'), 'w'), indent=1)
    return out


if __name__ == '__main__':
    main()
