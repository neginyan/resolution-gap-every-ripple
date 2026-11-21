"""Stage DY, items 2.3-2.4: THE INTERVAL PROOFS OF PAPER J at the two ends (chord form), with the DO watch (decimal.Inexact trapped).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  [computer-assisted]
    python3 src/dy_run.py t2 A|B [measure|final]   Theorem 2 (DJ-T in the form of paper J): the adaptive partition of dl_consts.run (9,809 pieces of [55.26, 1e6] at ratio
                                                   1.001, split on failure up to depth 12) and the tail [1e6, inf); every condition, and the quoted bounds:
                                                   'measure' = no quoted bound checked, the worst value of every quoted key recorded (pass 1);
                                                   'final'   = the quoted bounds QUOTED_J_FINAL (pass 2: the record that proves them);
    python3 src/dy_run.py t4 A|B                   Theorem 4 (DP-1a, B_1 = 8 ell + 100): dq_room1_low.run (6,952 pieces of [960.8, 1e6] + the tail, and its power);
    python3 src/dy_run.py r1 A|B                   (R1), (R3) and the tiny bounds of dp_r1.bounds_iv on [55.26, inf) as one piece, at the end's eta_r, with the sandwich
                                                   ratio 1/lam on (d4 + N4G)/P2z and on B1c/(Gam2 G) (the target Gamma_2 is lam Gamma/2);
    python3 src/dy_run.py power B                  wrong versions on the first 30 pieces, the last 5 below 1e6 and the tail (each must fail).
Run from the root of the work tree (results/ is read there).  -> results_DY/dy_<what>_<end>.json"""
import json, os, sys, time, math
from decimal import Decimal as Dc
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import dy_jsrc as Y

OUT = os.path.join(HERE, '..', 'results_DY')

# pass 2: the quoted bounds of paper J.  The 30 bounds of paper I that hold at both ends are kept; the others are the worst value of pass 1 (both ends, every piece
# and the tail) rounded outward to 4 significant digits.  Filled from results_DY/dy_t2_A_measure.json and dy_t2_B_measure.json by quoted_final().
def quoted_final():
    pub = None; worst = {}
    for end in 'AB':
        r = json.load(open(os.path.join(OUT, 'dy_t2_%s_measure.json' % end)))
        pub = r['paper I quoted bounds']
        for k, v in r['worst value of every quoted key (value, left end)'].items():
            s = [x[1] for x in pub if x[0] == k][0]
            if k not in worst or (v[0] > worst[k][0] if s == '<=' else v[0] < worst[k][0]): worst[k] = (v[0], end, v[1])
    out = []; table = {}
    for k, s, b in pub:
        if k not in worst: out.append((k, s, b)); table[k] = {'paper I': b, 'J': b, 'note': 'not computed on these pieces'}; continue
        w = worst[k][0]; holds = (w <= float(b)) if s == '<=' else (w >= float(b))
        if holds: nb = b
        else:
            e10 = math.floor(math.log10(abs(w))); sc = 10.0 ** (e10 - 3)
            x = (math.ceil(w / sc) if s == '<=' else math.floor(w / sc)) * sc
            nb = ('%.4g' % x)
            if (s == '<=' and float(nb) < w) or (s == '>=' and float(nb) > w):         # rounding of the print: one more step outward
                x = x + sc if s == '<=' else x - sc; nb = '%.4g' % x
        out.append((k, s, nb)); table[k] = {'sense': s, 'paper I': b, 'J worst (end, left end of the piece)': worst[k], 'J bound': nb, 'paper I bound kept': holds}
    return out, table


def run_t2(LC, mode, quoted, ratio=Dc('1.001')):
    t0 = time.time(); Y.set_quoted(LC, None, quoted) if False else None
    LC.QUOTED_J = list(quoted)
    ci = Y.trapped(LC.consts_iv); ch = Y.trapped(LC.checks)
    pieces = 0; La = LC.ELL1; worst = {}; wq = {}; nsplit = 0; fails = []; stack = []
    qkeys = [k for k, s, b in LC.QUOTED]; sense = {k: s for k, s, b in LC.QUOTED}
    cut = Dc(Y.ELL_CCH)                                                               # c_ch changes at 960.8: an edge of the partition
    while La < LC.ELL_TAIL:
        Lb = min(La * ratio, LC.ELL_TAIL)
        if La < cut < Lb: Lb = cut
        stack.append((La, Lb, 0)); La = Lb
    stack.reverse()
    def record(o, r, a):
        for k, (ok, v) in r.items():
            sm = LC.SENSE[k] == 'max'
            if k not in worst or (v > worst[k][1] if sm else v < worst[k][1]): worst[k] = (ok, v, float(a))
        for k in qkeys:
            if k not in o: continue
            v = float(o[k].hi) if sense[k] == '<=' else float(o[k].lo)
            if k not in wq or (v > wq[k][0] if sense[k] == '<=' else v < wq[k][0]): wq[k] = (v, float(a))
    while stack:
        a, b, d = stack.pop()
        try:
            o = ci(a, b); r = ch(o); bad = [k for k, (ok, v) in r.items() if not ok]
        except Exception as e:
            o, r = {}, {}; bad = ['exception: ' + repr(e)[:120]]
        if bad and d < 12:
            m = (a * b).sqrt(); stack.append((m, b, d + 1)); stack.append((a, m, d + 1)); nsplit += 1; continue
        if bad: fails.append({'piece': [str(a), str(b)], 'failed': bad[:8]})
        pieces += 1; record(o, r, a)
    try:
        ot = ci(LC.ELL_TAIL, Dc('Infinity')); rt = ch(ot); tailbad = [k for k, (ok, v) in rt.items() if not ok]; record(ot, rt, LC.ELL_TAIL)
    except Exception as e:
        rt = {}; tailbad = ['exception: ' + repr(e)[:160]]
    out = {'pieces of [55.26, 1e6]': pieces, 'splits': nsplit, 'pieces that fail (must be empty)': fails, 'tail [1e6, inf): failing (must be empty)': tailbad,
           'tail [1e6, inf): values': {k: v for k, (ok, v) in rt.items()},
           'worst over [55.26, 1e6] and the tail (ok, value, left end of the piece)': worst,
           'worst value of every quoted key (value, left end)': wq, 'seconds': time.time() - t0}
    out['ok'] = bool(not fails and not tailbad and rt)
    return out


def r1(end):
    import dp_r1 as R1
    from dl_interval import Iv
    e = Y.ENDS[end]; lam = Dc(e['LAM']); es = Dc('1e-11')
    o = Y.trapped(R1.bounds_iv)(eta_ripple=e['ETR'])
    f = lambda x: float(x.hi)
    inv = 1 / lam
    vals = {'R1: sum/P1 (units of es)': f(o['R1: sum/P1'] / es), 'R3 (a <= 1): S/P4z (es)': f(o['R3 (a <= 1): S/P4z'] / es), 'R3 (a >= 1): S/P1 (es)': f(o['R3 (a >= 1): S/P1'] / es),
            'X1^2/ell': f(o['X1^2/ell']),
            '(d4 + N4G)/P2z / es_sigma x (1/lam)/(1 + eta_r)': f(o['(d4 + N4G)/P2z / es_sigma'] * Iv(inv) / (1 + Iv(Dc(e['ETR'])))),
            'B1l/P2z / es_sigma x (1/lam)/(1 + eta_r)': f(o['B1l/P2z / es_sigma (mu <= 2 ell)'] * Iv(inv) / (1 + Iv(Dc(e['ETR'])))),
            'B1c/(Gam2 G) / es_sigma x (1/lam)': f(o['B1c/(Gam2 G) / es_sigma'] * Iv(inv)), 'c_S': f(o['c_S'])}
    # (d4 + N4G)/P2z and B1l/P2z carry (1 + eta) = 1/fl of the gain P2z in paper I; in J the gain is lam: the factor is 1/lam.  Both are multiplied by
    # (1/lam)/(1 + eta_r) >= 1 here (end A: 1, end B: 1).  B1c/(Gam2 G): the target Gamma_2 of J is lam Gamma/2 (paper I's bound used Gamma/2): x 1/lam.
    # THE ALLOCATION OF es IN PAPER J: (R1) <= 0.9 es P1 and (R3) <= 0.1 es (P4z for a <= 1, P1 for a >= 1).  Paper I used 0.52 / 0.48 (dp_r1); at the end B
    # (eta_r = 1/4) N2/P1 = Q2/(8 B) alone is 0.6006 es (Q2 = 1 + eta k_E 1.8), while (R3) needs only 0.04 es.  The total charged to P1 stays <= es, so (R4),
    # e0, m1, m4 and everything after are unchanged.
    A1, A3 = 0.9, 0.1
    ok = {'R1 <= 0.9 es': vals['R1: sum/P1 (units of es)'] <= A1, 'R3 (a <= 1) <= 0.1 es': vals['R3 (a <= 1): S/P4z (es)'] <= A3,
          'R3 (a >= 1) <= 0.1 es': vals['R3 (a >= 1): S/P1 (es)'] <= A3, 'X1^2 <= ell': vals['X1^2/ell'] <= 1,
          '(d4 + N4G)/P2z <= es_sigma': vals['(d4 + N4G)/P2z / es_sigma x (1/lam)/(1 + eta_r)'] <= 1, 'B1l/P2z <= es_sigma': vals['B1l/P2z / es_sigma x (1/lam)/(1 + eta_r)'] <= 1,
          'B1c <= es_sigma Gam2 G': vals['B1c/(Gam2 G) / es_sigma x (1/lam)'] <= 1}
    pw = {'B >= 1.3e10: R1 <= 0.9 es (must be False)': float((Y.trapped(R1.bounds_iv)(Bm='1.3e10', eta_ripple=e['ETR'])['R1: sum/P1'] / es).hi) <= A1,
          "paper I's allocation: R1 <= 0.52 es at the end B (must be False at B)": (vals['R1: sum/P1 (units of es)'] <= 0.52) if end == 'B' else False,
          'R1 <= 0.49 es at the end A (must be False at A)': (vals['R1: sum/P1 (units of es)'] <= 0.49) if end == 'A' else False}
    if end == 'B': pw['r >= sigma^5: R1 <= 0.9 es (must be False; at the end A eta_r = 0 removes the r-terms)'] = float((Y.trapped(R1.bounds_iv)(rpow=5, eta_ripple=e['ETR'])['R1: sum/P1'] / es).hi) <= A1
    return {'end': e, 'one piece [55.26, inf)': True, 'values': vals, 'conditions': ok, 'power (each must be False)': pw,
            'ok': bool(all(ok.values()) and not any(pw.values()))}


def power(LC, quoted, worst, end):
    """wrong versions (each must fail on some of the 36 pieces): quoted bounds tightened past the worst value, the rule constant c1 raised, e0 lowered."""
    r = Dc('1.001'); edges = [LC.ELL1]
    while edges[-1] < LC.ELL_TAIL: edges.append(min(edges[-1] * r, LC.ELL_TAIL))
    pcs = list(zip(edges[:-1], edges[1:])); pcs = pcs[:30] + pcs[-5:] + [(LC.ELL_TAIL, Dc('Infinity'))]
    def tight(k):
        s = [x for x in quoted if x[0] == k][0][1]; w = worst[k][0]
        return [(kk, ss, (('%.6g' % (w * (1 - 1e-4))) if s == '<=' else ('%.6g' % (w * (1 + 1e-4)))) if kk == k else bb) for kk, ss, bb in quoted]
    V = {'c1F quoted 1e-4 above its worst': {'quoted': tight('c1F')}, 'eps1 ell^2 quoted 1e-4 below its worst': {'quoted': tight('eps1 ell^2')},
         'R4 e0 needed quoted 1e-4 below its worst': {'quoted': tight('R4: e0 needed')}}
    # the rule constant raised just past what this end allows (Case I (Fz): c1F - K_F - lam c1 >= 0; end A allows about 0.80, end B about 0.774)
    if end == 'A': V['the rule constant c1 = 0.805'] = {'C1': Dc('0.805')}
    else:
        V['the rule constant c1 = 0.776'] = {'C1': Dc('0.776')}
        V['e0 = 1.26e-5 (the number of paper I; at the end A the e0 needed is below it, so this version is for the end B)'] = {'E0': Dc('1.26e-5')}
    out = {}; keep = (LC.C1, LC.E0)
    for name, w in V.items():
        LC.WRONG.clear()
        if 'quoted' in w: LC.WRONG['quoted'] = w['quoted']
        LC.C1 = w.get('C1', keep[0]); LC.E0 = w.get('E0', keep[1]); nbad = 0; where = []
        try:
            for a, b in pcs:
                bad = [k for k, (ok, v) in Y.trapped(LC.checks)(Y.trapped(LC.consts_iv)(a, b)).items() if not ok]
                if bad: nbad += 1; where.append([str(a), bad[0]]) if len(where) < 3 else None
        finally:
            LC.WRONG.clear(); LC.C1, LC.E0 = keep
        out[name] = {'pieces checked': len(pcs), 'failing pieces': nbad, 'caught': nbad > 0, 'first failures': where}
        print(name, nbad, flush=True)
    out['ok'] = all(v['caught'] for v in out.values())
    return out


if __name__ == '__main__':
    what, end = sys.argv[1], sys.argv[2]; os.makedirs(OUT, exist_ok=True); t0 = time.time()
    rec = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'end': end, 'end parameters': Y.ENDS[end], 'rule': Y.RULE, 'e0': Y.E0J}
    if what == 'r1':
        rec.update(r1(end)); fn = 'dy_r1_%s.json' % end
    else:
        LC, RM, DQL = Y.load(); Y.set_end(LC, RM, end)
        rec['paper I quoted bounds'] = [list(x) for x in LC.QUOTED]
        if what == 't2':
            mode = sys.argv[3]
            if mode == 'measure': q = []
            else: q, table = quoted_final(); rec['quoted bounds of paper J (pass 2)'] = [list(x) for x in q]; rec['quoted table'] = table
            Y.set_quoted(LC, RM, q); rec.update(run_t2(LC, mode, q)); fn = 'dy_t2_%s_%s.json' % (end, mode)
        elif what == 't4':
            q, table = quoted_final(); Y.set_quoted(LC, RM, q)
            r = DQL.run(save=False); rec['Theorem 4 (dq_room1_low.run on the J modules)'] = r; rec['ok'] = bool(r['ok']); fn = 'dy_t4_%s.json' % end
        elif what == 'power':
            q, table = quoted_final(); Y.set_quoted(LC, RM, q)
            w = json.load(open(os.path.join(OUT, 'dy_t2_%s_measure.json' % end)))['worst value of every quoted key (value, left end)']
            rec.update(power(LC, q, w, end)); fn = 'dy_power_%s.json' % end
    rec['seconds'] = time.time() - t0
    json.dump(rec, open(os.path.join(OUT, fn), 'w'), indent=1, default=str); print(fn, rec.get('ok'), round(rec['seconds']))
