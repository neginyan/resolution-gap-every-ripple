"""Stage DQ (addendum 1.2, step 4): the interval proof of Theorem DP-1a with the LOWERED lower end B_1(ell) = 8 ell + 100 (c_B = 1), on the same 6,952 pieces
of [960.8, 1e6] and the tail [1e6, inf), with the watch of stage DO (decimal.Inexact trapped).  Python 3.11 grammar.
Run only after the break attempts of DQ_探索計画.md section C.3 (dq_low.py) passed.  Everything is dp_room1's, except the lower bound of B on a piece:
  B_m := 8 ell_a + 100 (the left end of the piece) instead of max(5e5, 8 ell_a + 100).  The conditions of the lemmas that this needs (y <= 1/(2 (8 ell + 100)) <= 1e-4
  for M4 = 2.07: Lemma DQ-M2, results/dq_m4.json) are checked by dq_m4.py; the other uses of y are in DQ_証明まとめ.md section 12.3.
POWER: the same four wrong versions as dp_room1.power (each must fail).
-> results/dq_room1_low.json"""
import json, sys, os, time
from decimal import Decimal as Dc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dp_room1 as RM
import dl_interval as V
from dl_interval import Iv, sqrt

_ORIG = RM.params


def params_low(La, cB, Bm=None, e0_is_es=False, bI=None):
    """dp_room1.params without the floor 5e5."""
    cB = Dc(cB)
    B1 = Iv(cB) * (8 * Iv(La) + 100) if Bm is None else Iv(Dc(Bm))
    Bm_ = Iv(B1.lo)
    es = Iv((Iv(Dc('0.25')) / Bm_).hi)
    e0 = es if e0_is_es else Iv((2 / sqrt(Bm_) + es).hi)
    return Bm_, 8 * cB, (1 / (2 * Iv(cB))).hi, es, e0


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'claim': 'Theorem DP-1a with B_1(ell) = 8 ell + 100 (ell >= 960.8, 8 ell + 100 <= B < ell^4, c_B = 1)'}
    RM.params = params_low
    try:
        r = RM.run_cb('1'); out['c_B = 1, B_m = 8 ell_a + 100'] = r; print('c_B 1 low', r['ok'], r['number of failing pieces'], round(time.time() - t0), flush=True)
        out['power'] = RM.power()
    finally: RM.params = _ORIG
    f = r['parameters of the first piece']
    out['first piece: B_m, es, e0'] = [f['B_m'], f['es'], f['e0']]
    try: m4 = json.load(open('results/dq_m4.json')); out['Lemma DQ-M2 (M4(1e-4) <= 2.07) holds (results/dq_m4.json)'] = bool(m4['ok']); out['largest y here: 1/(2 (8 x 960.8 + 100))'] = 1 / (2 * (8 * 960.8 + 100))
    except Exception: out['Lemma DQ-M2 (M4(1e-4) <= 2.07) holds (results/dq_m4.json)'] = False
    try: lw = json.load(open('results/dq_low.json')); out['the break attempts passed first (results/dq_low.json)'] = bool(lw['ok'])
    except Exception: out['the break attempts passed first (results/dq_low.json)'] = False
    out['ok'] = bool(r['ok'] and out['power']['ok'] and out['Lemma DQ-M2 (M4(1e-4) <= 2.07) holds (results/dq_m4.json)'] and out['the break attempts passed first (results/dq_low.json)']
                     and out['largest y here: 1/(2 (8 x 960.8 + 100))'] <= 1e-4)
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dq_room1_low.json', 'w'), indent=1, default=str)
    return out


if __name__ == '__main__':
    r = run(); print(r['ok'], r['first piece: B_m, es, e0']); sys.exit(0 if r['ok'] else 1)
