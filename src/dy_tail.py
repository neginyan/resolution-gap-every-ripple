"""Stage DY, item 2.2: the tail [1e6, inf) with eta and 1/ell separated -- the general formulas with a1 = 7 reproduce the published tail of paper I exactly, and the
derivation A >= 1 - a1 t is checked in exact rational arithmetic (J: a1 = 5; wrong versions a1 = 4 and, for paper I, 6.9).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  -> results_DY/dy_tail.json"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dy_jsrc as Y

if __name__ == '__main__':
    t0 = time.time(); r = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}; r.update(Y.reduce_check()); r['seconds'] = time.time() - t0
    d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DY'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dy_tail.json'), 'w'), indent=1, default=str); print(r['ok'])
