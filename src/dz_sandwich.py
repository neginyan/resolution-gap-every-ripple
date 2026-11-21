"""Stage DZ, item 2.2: HOW MUCH THE RIPPLE SANDWICH ACTS INSIDE THE TRUE QUANTITY, at every minimiser of the search at ell = 55.26.  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
At each minimiser (results_DZ/dz_post.json), on the fine grid: Q (true) and Q_h1 (dz_truth variant 'h1': the same window and state, the factors 1/h of the
scores replaced by 1, the density keeping h).  The ripple sandwich of the proof bounds the effect of these factors by (1 - eta)/(1 + eta) = 0.6 at eta = 1/4;
the ratio Q/Q_h1 is what they actually do at the state.  Also: the same window shape and state with eta = 1/ell (the swap; the brightness falls with eta^2).
SEARCH (breaking direction): Q/Q_h1 itself minimised over the window shape and the ripple-dominated states of the narrow room (W >= b), for every family at
eta = 1/4 and 0.1, with the budget of the main search; if the ripple could take the fraction (1 - eta)/(1 + eta) of the information, this ratio would show it.
-> results_DZ/dz_sandwich.json"""
import json, os, sys, time
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_search as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def ratio_job(args):
    fam, en = args; ev = {'1/4': 0.25, '0.1': 0.1}[en]; seed = 3000 + 10 * list(S.FAMS).index(fam) + (en == '0.1')
    best, nev = S.search(55.26, 'narrow', fam, ev, seed=seed, mode='bright', obj='ratio', maxfev=150)
    z = best[0][1]; q = S.evaluate(z, 55.26, 'narrow', fam, ev, M_rule='fine'); q1 = S.evaluate(z, 55.26, 'narrow', fam, ev, variant='h1', M_rule='fine')
    v, o = S.evaluate(z, 55.26, 'narrow', fam, ev, full=True, M_rule='fine')
    return {'family': fam, 'eta': en, 'smallest Q/Q_h1': q / q1, 'search value (coarse grid)': best[0][0], '(1 - eta)/(1 + eta)': (1 - ev) / (1 + ev),
            'Q sqrt(ell) there': q, 'W/b there': o.get('W/b (ripple part of den over b)'), 'at': S.summarize(v, o), 'evaluations': nev}


def main():
    t0 = time.time(); P = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_post.json')))['55.26']['rows']
    M = {(r['mode'], r['room'], r['family'], r['eta']): r for r in json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_search_55.26.json')))['rows']}
    rows = []
    for r in P:
        if r['room'] == 'wide band' or r['Q sqrt(ell) (fine grid)'] >= 1e3: continue
        m = M[(r['mode'], r['room'], r['family'], r['eta'])]; z = m['z of the 5 best starts'][0]; ev = m['eta value']
        q = S.evaluate(z, 55.26, r['room'], r['family'], ev, M_rule='fine'); q1 = S.evaluate(z, 55.26, r['room'], r['family'], ev, variant='h1', M_rule='fine')
        qs = S.evaluate(z, 55.26, r['room'], r['family'], 1 / 55.26, M_rule='fine') if r['eta'] != '1/ell' else q
        rows.append({'mode': r['mode'], 'room': r['room'], 'family': r['family'], 'eta': r['eta'], 'eta value': ev, 'Q sqrt(ell)': q, 'Q_h1 sqrt(ell)': q1, 'Q/Q_h1': q / q1,
                     '(1 - eta)/(1 + eta)': (1 - ev) / (1 + ev), 'Q with eta = 1/ell (same shape and state)': qs, 'Q/Q(1/ell)': q / qs,
                     'W/b': r['at'].get('W/b (ripple part of den over b)')})
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'rows': rows}
    for en in ('1/4', '0.1', '1/ell'):
        rr = [x for x in rows if x['eta'] == en and (x['W/b'] or 0) >= 1]
        if rr:
            out['ripple-dominated minimisers, eta = %s: smallest and largest Q/Q_h1' % en] = [min(x['Q/Q_h1'] for x in rr), max(x['Q/Q_h1'] for x in rr)]
        rr2 = [x for x in rows if x['eta'] == en and x['eta'] != '1/ell' and (x['W/b'] or 0) >= 1]
        if rr2:
            out['ripple-dominated minimisers, eta = %s: smallest and largest Q/Q(1/ell) (swap)' % en] = [min(x['Q/Q(1/ell)'] for x in rr2), max(x['Q/Q(1/ell)'] for x in rr2)]
    jobs = [(fam, en) for fam in ('W1', 'W2-21', 'W2-61', 'S', 'Pt', 'Pc') for en in ('1/4', '0.1')]
    with Pool(2) as Pl:
        rs = Pl.map(ratio_job, jobs)
    out['search of Q/Q_h1 (narrow room, ripple-dominated)'] = rs
    for en in ('1/4', '0.1'):
        w = min((x for x in rs if x['eta'] == en), key=lambda x: x['smallest Q/Q_h1'])
        out['search: smallest Q/Q_h1, eta = %s' % en] = {'value': w['smallest Q/Q_h1'], 'family': w['family'], '(1 - eta)/(1 + eta)': w['(1 - eta)/(1 + eta)'], 'Q sqrt(ell) there': w['Q sqrt(ell) there']}
    out['ok'] = len(rows) > 0 and len(rs) == len(jobs)
    out['seconds'] = time.time() - t0
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_sandwich.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}, indent=1))
    for x in rows:
        if (x['W/b'] or 0) >= 1: print(x['mode'], x['family'], x['eta'], '%.4f %.4f %.4f %.4f' % (x['Q sqrt(ell)'], x['Q/Q_h1'], x['(1 - eta)/(1 + eta)'], x['Q/Q(1/ell)']))


if __name__ == '__main__':
    main()
