"""Stage DZ, item 2.2: every minimiser of the search re-evaluated on the fine t-grid of dz_truth, with its local quantities; the summary tables of the
report.  [numerical]  Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
    python3 src/dz_post.py [ell ...]   (default 55.26; reads results_DZ/dz_search_<ell>.json) -> results_DZ/dz_post.json"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_search as S

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main(ells):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    for ell in ells:
        M = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_search_%s.json' % ell))); rows = []
        for r in M['rows']:
            z = r['z of the 5 best starts'][0]
            v, o = S.evaluate(z, r['ell'], r['room'], r['family'], r['eta value'], full=True, mode=r['mode'], M_rule='fine')
            vt = S.evaluate(z, r['ell'], r['room'], r['family'], r['eta value'], mode='all', M_rule='fine')
            rows.append({'mode': r['mode'], 'room': r['room'], 'family': r['family'], 'eta': r['eta'], 'search value (coarse grid)': r['min Q sqrt(ell)'],
                         'Q sqrt(ell) (fine grid)': vt, 'relative change': abs(vt / r['min Q sqrt(ell)'] - 1) if r['min Q sqrt(ell)'] < 1e3 else None,
                         'at': S.summarize(v, o)})
        res = {'rows': rows}
        for mode in ('all', 'bright'):
            for en in ('1/4', '0.1', '1/ell'):
                rr = [x for x in rows if x['mode'] == mode and x['eta'] == en and (mode == 'all' or (x['at'].get('W/b (ripple part of den over b)') or 0) >= 1)]
                if not rr: continue
                w = min(rr, key=lambda x: x['Q sqrt(ell) (fine grid)'])
                res['smallest Q sqrt(ell) [%s], eta = %s' % (mode, en)] = {'value': w['Q sqrt(ell) (fine grid)'], 'room': w['room'], 'family': w['family'], 'at': w['at']}
                for room in S.ROOMS:
                    r2 = [x for x in rr if x['room'] == room]
                    if r2:
                        w2 = min(r2, key=lambda x: x['Q sqrt(ell) (fine grid)'])
                        res['smallest [%s], eta = %s, %s' % (mode, en, room)] = {'value': w2['Q sqrt(ell) (fine grid)'], 'family': w2['family']}
        res['largest change coarse -> fine'] = max(x['relative change'] for x in rows if x['relative change'] is not None)
        out[str(ell)] = res
    out['seconds'] = time.time() - t0
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_post.json'), 'w'), indent=1)
    print(json.dumps({e: {k: v for k, v in out[e].items() if k != 'rows'} for e in out if e not in ('model', 'seconds')}, indent=1)[:5000])


if __name__ == '__main__':
    main([float(a) for a in sys.argv[1:]] or [55.26])
