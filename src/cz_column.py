"""Stage CZ 2.3: THE TEST COLUMN ell in [55.26, 65.26] WITHOUT EXCLUDING ANY BAND, on the CZ table (cz_cells.py: the old options T, B, F with the two
repairs, and the direct options Tz, Bz, Fz).  Python 3.11 grammar.
LEVEL BY LEVEL (so that a stop tells WHERE the column is open, not only the first stuck box): generation 0 = the initial boxes of cy_cells.initial_boxes
(all of them: no mask); every box that is not accepted is bisected by the rule of cv_cells.certify (the coordinate with the largest weighted width);
the children form the next generation.  A box whose largest weighted width is below MINW = 1e-6 is recorded as STUCK and not bisected further.
The column is CLOSED when a generation leaves no box and nothing is stuck.  Staged evaluation (the same acceptance: a box is accepted when one option
passes the endpoint rule): first the z-options, then, for the boxes they do not prove, the old options, then, in the true kappa tail, the two-piece
rule and the frozen-split rule.
RESUMABLE: the generation still to do is saved to results/cz_column_state_w{w}.npz every SAVE seconds.
  python3 cz_column.py W NW [max_seconds]   worker W of NW (the initial boxes are dealt out round-robin after a fixed shuffle)
  python3 cz_column.py finalize W           write worker W's result from its state (after a stop from outside)
  python3 cz_column.py merge NW             -> results/cz_column.json"""
import json, math, os, sys, time
import numpy as np
import cz_cells as X

HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
ELL_A, ELL_B = 55.26, 65.26
MINW = 1e-6; CW = [(0, 1.0), (2, 1.0), (4, 0.7), (6, 0.5), (8, 2.0)]
KSPLIT = {'on': os.environ.get('CZ_KSPLIT', '1') != '0', 'depth': 12.0}
# DE 2.2: a rejected box of the low kappa tail (kappa_a = 0, i.e. log kappa_a = -inf: width infinite, weight 0 in CW, never split before DE) is cut in
# kappa at c = (log kappa_b + kappa_f)/2, kappa_f = log b_hi - depth (below b e^-8 the enveloped brightness bound is flat, so deeper cuts gain nothing):
# the pieces [c, kappa_b] (finite: then bisected by CW as any box) and (0, e^c].  A tail with log kappa_b <= kappa_f + 1 is split by CW in the other variables.
# CZ_KSPLIT=0: the bisection of DD and before.


def split_boxes(bad):
    """the bisection of the table: (children, boxes too small to split).  CW (the widest weighted finite coordinate), plus the kappa cut of DE."""
    bad = np.asarray(bad, dtype=float)
    kcut = np.zeros(len(bad), dtype=bool)
    if KSPLIT['on'] and len(bad):
        ls_hi = np.minimum(-bad[:, 8], 0.5 * (math.log(X.BMAX) - bad[:, 4])); lb_hi = np.minimum(bad[:, 5] + 2 * ls_hi, math.log(X.BMAX))
        kf = lb_hi - KSPLIT['depth']
        kcut = ~np.isfinite(bad[:, 6]) & np.isfinite(bad[:, 7]) & (bad[:, 7] > kf + 1.0)
    out = []
    if kcut.any():
        T = bad[kcut]; c = 0.5 * (T[:, 7] + kf[kcut]); A = T.copy(); B = T.copy()
        A[:, 6] = c; B[:, 7] = c; out += [A, B]
    rest = bad[~kcut]
    W = np.stack([np.where(np.isfinite(rest[:, j]) & np.isfinite(rest[:, j + 1]), rest[:, j + 1] - rest[:, j], 0.0) * wt for j, wt in CW], axis=1) if len(rest) else np.zeros((0, len(CW)))
    k = np.argmax(W, axis=1) if len(rest) else np.zeros(0, dtype=int); small = np.max(W, axis=1) < MINW if len(rest) else np.zeros(0, dtype=bool)
    keep = rest[~small]; k = k[~small]; L = keep.copy(); R = keep.copy()
    if len(keep):
        jj = np.array([j for j, _ in CW])[k]; rows = np.arange(len(keep)); mid = 0.5 * (keep[rows, jj] + keep[rows, jj + 1])
        L[rows, jj + 1] = mid; R[rows, jj] = mid; out += [L, R]
    return (np.vstack(out) if out else np.zeros((0, 10))), rest[small]
#   bisection weights (mu, r, beta, kappa, ell).  The stored worker runs (results/cz_column_w*.json) used the weight 0.25 for log r (the rule of
#   cv_cells.certify); with it the boxes wait a long time for r to be halved, although r is the coordinate that keeps them from passing (the
#   z-options are sensitive to r through g_s(r)).  With the weight 1.0 a random sample of the initial boxes closes completely (follow()).
CW_FIRST_RUN = [(0, 1.0), (2, 0.25), (4, 0.7), (6, 0.5), (8, 2.0)]


DG = {'on': os.environ.get('CZ_DG', '0') != '0', 'first': True, 'coords': (4,), 'fit': 'l1'}
# DG 2.1 (stage 8): the whole-sum form of dg_tm (Theorem DG-1) for the finite boxes of the z-options.  'first': evaluated before the table's stages on
# every box (it is cheaper); the accepted set is the union of the stages either way (each stage is a valid proof on its own), only the label differs.
# 'coords': the coordinates in which the common factor and the variable At are scaled (default: ell); 'fit': the choice of the scaling (weighted L1).


def margin(Xb):
    """the box value: stages 1-7 of the table (margin_table) and, if DG['on'], stage 8 (the whole-sum form, Theorem DG-1); returns (margin, how)."""
    if not DG['on']: return margin_table(Xb)
    import dg_tm
    Xb = np.asarray(Xb, dtype=float); lGc, _ = X.box_P(Xb)
    if DG['first']:
        md = dg_tm.tm_margin(Xb, lGc, coords=DG['coords'], fit=DG['fit']); acc = md > X.ACC
        mg = md.copy(); how = np.where(acc, 8, 0)
        if (~acc).any():
            mt, ht = margin_table(Xb[~acc]); idx = np.where(~acc)[0]; mg[idx] = np.maximum(mg[idx], mt); how[idx] = ht
        return mg, how
    mg, how = margin_table(Xb); rest = ~(mg > X.ACC)
    if rest.any():
        md = dg_tm.tm_margin(Xb[rest], lGc[rest], coords=DG['coords'], fit=DG['fit']); idx = np.where(rest)[0]; mg[idx] = np.maximum(mg[idx], md); how[idx[md > X.ACC]] = 8
    return mg, how


def margin_table(Xb):
    """the box value of cz_cells.cell_margin, staged; returns (margin, how) with how = 1 (z-options), 2 (old options), 3 (two-piece rule), 4 (frozen-split rule of the z-options, true kappa tail), 5 (DA: constant form of the F main gain), 6 (DD: the same at many levels, with the branch B1 on a whole piece), 7 (DF: the coherent form), 0 (not accepted)."""
    lGc, _ = X.box_P(Xb); n = len(Xb); mg = np.full(n, -np.inf); how = np.zeros(n, dtype=int)
    saved = X.OPTS
    try:
        X.OPTS = X.OPTS_Z; mz = X.margin_from(X.values(Xb, 0.0, lGc)); mg = np.maximum(mg, mz); how[mz > X.ACC] = 1
        rest = ~(mg > X.ACC)
        if rest.any():
            X.OPTS = X.OPTS_OLD; mo = X.margin_from(X.values(Xb[rest], 0.0, lGc[rest]))
            idx = np.where(rest)[0]; mg[idx] = np.maximum(mg[idx], mo); how[idx[mo > X.ACC]] = 2
    finally:
        X.OPTS = saved
    tt = ~np.isfinite(Xb[:, 7]) & ~(mg > X.ACC)
    if tt.any():
        mt = X.tail_split_values(Xb[tt], 0.0, lGc[tt]); idx = np.where(tt)[0]; mg[idx] = np.maximum(mg[idx], mt); how[idx[mt > X.ACC]] = 3
    tt = ~np.isfinite(Xb[:, 7]) & ~(mg > X.ACC)
    if tt.any():
        mt = X.tail_fixed_values(Xb[tt], 0.0, lGc[tt]); idx = np.where(tt)[0]; mg[idx] = np.maximum(mg[idx], mt); how[idx[mt > X.ACC]] = 4
    rest = ~(mg > X.ACC)
    if X.AR['on'] and rest.any():                                       # DA 2.3: the constant form of the F main gain
        ma = X.arange_values(Xb[rest], 0.0, lGc[rest]); idx = np.where(rest)[0]; mg[idx] = np.maximum(mg[idx], ma); how[idx[ma > X.ACC]] = 5
    rest = ~(mg > X.ACC)
    if X.AR['on'] and not X.AR.get('levels') and X.AR.get('levels_low'):
        # DF 2.3: stage 6 where the table needs it -- the low-mu / deep-kappa region (mu_b <= 1e-3 and kappa_b < 1e-12; every failing state found has both): there, with r << sigma and
        # kappa below ~ e^2.6 b/sigma, every option of stages 1-5 is negative even at a point (df_gap), and stage 6 proves them (df_gap, df_lowmu)
        low = (Xb[:, 1] <= math.log(1e-3) + 1e-9) & (Xb[:, 7] < math.log(1e-12)) if X.AR.get('levels_low_rule', 'and') == 'and' else (Xb[:, 1] <= math.log(1e-3) + 1e-9) | (Xb[:, 7] < math.log(1e-12))
        rest = rest & low
    if X.AR['on'] and (X.AR.get('levels') or X.AR.get('levels_low')) and rest.any():   # DD 2.1: the stage at many levels + the branch B1 on a whole piece
        ml = X.levels_values(Xb[rest], q=X.AR['q'], Dd=0.0, lGc=lGc[rest], b1only=True); idx = np.where(rest)[0]; mg[idx] = np.maximum(mg[idx], ml); how[idx[ml > X.ACC]] = 6
    rest = ~(mg > X.ACC)
    if X.COH['on'] and rest.any():                                       # DF 2.1: the coherent form (slabs in log r, the variable A; Theorem DF-1)
        mc = X.coh_values(Xb[rest], 0.0, lGc[rest]); idx = np.where(rest)[0]; mg[idx] = np.maximum(mg[idx], mc); how[idx[mc > X.ACC]] = 7
    return mg, how


def where(A):
    """a summary of where a set of boxes lies (for the report)."""
    if not len(A): return None
    ell = 0.5 * (A[:, 8] + A[:, 9]); fin = lambda v: v[np.isfinite(v)]
    d = {'boxes': int(len(A)), 'log10_b': [float((A[:, 4] - 2 * A[:, 9]).min() / math.log(10)), float((A[:, 5] - 2 * A[:, 8]).max() / math.log(10))],
         'log_beta': [float(A[:, 4].min()), float(A[:, 5].max())], 'log10_r': [float(A[:, 2].min() / math.log(10)), float(A[:, 3].max() / math.log(10))],
         'ell': [float(A[:, 8].min()), float(A[:, 9].max())],
         'log_mu': [float(fin(A[:, 0]).min()) if len(fin(A[:, 0])) else None, float(fin(A[:, 1]).max()) if len(fin(A[:, 1])) else None],
         'log_kappa': [float(fin(A[:, 6]).min()) if len(fin(A[:, 6])) else None, float(fin(A[:, 7]).max()) if len(fin(A[:, 7])) else None],
         'mu_tail_low': int(np.sum(~np.isfinite(A[:, 0]))), 'mu_tail_high': int(np.sum(~np.isfinite(A[:, 1]))),
         'kappa_tail_low': int(np.sum(~np.isfinite(A[:, 6]))), 'kappa_tail_high': int(np.sum(~np.isfinite(A[:, 7])))}
    return d


def run(w, nw, max_seconds=6600.0, chunk=50_000, save_every=600.0):
    ST = os.path.join(RES, 'cz_column_state_w%d.npz' % w); OUT = os.path.join(RES, 'cz_column_w%d.json' % w)
    if os.path.exists(ST):
        z = np.load(ST, allow_pickle=False); cur = z['cur']; nxt = [z['nxt']] if len(z['nxt']) else []; meta = json.loads(str(z['meta'])); stuck = list(z['stuck'])
    else:
        X0 = X.initial_boxes(ELL_A, ELL_B); n_all = len(X0)
        rng = np.random.default_rng(0); X0 = X0[rng.permutation(n_all)][w::nw]
        cur = X0; nxt = []; stuck = []
        meta = {'AR_stage': bool(X.AR['on']), 'fixes': dict(X.FIX), 'weights': [wt for j, wt in CW], 'worker': w, 'workers': nw, 'initial_boxes_all': int(n_all), 'initial_boxes_worker': int(len(X0)), 'generation': 0, 'cells': 0, 'skipped': 0,
                'seconds': 0.0, 'accepted_by': {'z-options': 0, 'old options': 0, 'two-piece rule': 0}, 'thin': None, 'generations': []}
    t0 = time.time(); last = t0
    def save():
        tmp = ST + '.tmp.npz'
        np.savez(tmp, cur=cur, nxt=np.vstack(nxt) if nxt else np.zeros((0, 10)), stuck=np.array(stuck) if stuck else np.zeros((0, 10)), meta=json.dumps({**meta, 'seconds': meta['seconds'] + time.time() - t0}))
        os.replace(tmp, ST)
    while True:
        while len(cur):
            if time.time() - t0 > max_seconds:
                save(); meta2 = {**meta, 'seconds': meta['seconds'] + time.time() - t0}
                left = np.vstack([cur] + nxt)
                res = {'closed': False, 'reason': 'time', **meta2, 'left_in_generation': int(len(cur)), 'next_generation_so_far': int(sum(len(a) for a in nxt)),
                       'stuck': len(stuck), 'where_left': where(left), 'where_stuck': where(np.array(stuck)) if stuck else None, 'first_stuck': [list(map(float, s)) for s in stuck[:5]]}
                json.dump(res, open(OUT, 'w'), indent=1); print(json.dumps({'paused': True, 'generation': meta['generation'], 'cells': meta['cells'], 'left': int(len(left))}), flush=True)
                return res
            Xb = cur[:chunk]; cur = cur[chunk:]
            s = X.skip(Xb); meta['skipped'] += int(s.sum()); Xb = Xb[~s]
            if not len(Xb): continue
            meta['cells'] += len(Xb)
            mg, how = margin(Xb); ok = mg > X.ACC
            for k, nm in ((1, 'z-options'), (2, 'old options'), (3, 'two-piece rule'), (4, 'frozen-split rule'), (5, 'constant F gain')): meta['accepted_by'][nm] = meta['accepted_by'].get(nm, 0) + int(np.sum(how == k))
            if ok.any():
                i0 = int(np.argmin(np.where(ok, mg, np.inf)))
                if meta['thin'] is None or mg[i0] < meta['thin'][0]: meta['thin'] = [float(mg[i0]), [float(v) for v in Xb[i0]]]
            bad = Xb[~ok]
            if len(bad):
                W = np.stack([np.where(np.isfinite(bad[:, j]) & np.isfinite(bad[:, j + 1]), bad[:, j + 1] - bad[:, j], 0.0) * wt for j, wt in CW], axis=1)
                k = np.argmax(W, axis=1); mw = np.max(W, axis=1); small = mw < MINW
                for row in bad[small][:max(0, 1000 - len(stuck))]: stuck.append(row)
                meta['stuck_total'] = meta.get('stuck_total', 0) + int(small.sum())
                bad = bad[~small]; k = k[~small]; new = []
                for ii, (j, wt) in enumerate(CW):
                    sel = bad[k == ii]
                    if not len(sel): continue
                    mid = 0.5 * (sel[:, j] + sel[:, j + 1]); Lc = sel.copy(); Rc = sel.copy(); Lc[:, j + 1] = mid; Rc[:, j] = mid; new += [Lc, Rc]
                if new: nxt.append(np.vstack(new))
            if time.time() - last > save_every: save(); last = time.time()
        n_next = int(sum(len(a) for a in nxt))
        meta['generations'].append({'generation': meta['generation'], 'cells_so_far': meta['cells'], 'not_accepted -> next generation': n_next, 'sec': round(meta['seconds'] + time.time() - t0)})
        print(json.dumps(meta['generations'][-1]), flush=True)
        if not n_next: break
        cur = np.vstack(nxt); nxt = []; meta['generation'] += 1
        if meta['generation'] <= 3 or meta['generation'] % 5 == 0: meta.setdefault('where_by_generation', {})[str(meta['generation'])] = where(cur)
    meta['seconds'] += time.time() - t0
    res = {'closed': not stuck, 'reason': None if not stuck else 'stuck boxes', **meta, 'stuck': len(stuck), 'where_stuck': where(np.array(stuck)) if stuck else None,
           'first_stuck': [list(map(float, s)) for s in stuck[:5]]}
    json.dump(res, open(OUT, 'w'), indent=1); cur = np.zeros((0, 10)); save(); print(json.dumps({'closed': res['closed'], 'cells': meta['cells'], 'stuck': len(stuck)}), flush=True)
    return res


def finalize(w):
    """write the worker's result from its saved state (a run stopped from outside leaves only the state file)."""
    ST = os.path.join(RES, 'cz_column_state_w%d.npz' % w); OUT = os.path.join(RES, 'cz_column_w%d.json' % w)
    z = np.load(ST, allow_pickle=False); cur = z['cur']; nxt = z['nxt']; stuck = z['stuck']; meta = json.loads(str(z['meta']))
    left = np.vstack([cur, nxt]) if len(nxt) else cur
    res = {'closed': False, 'reason': 'stopped (time): the bisection had not finished', **meta, 'left_in_generation': int(len(cur)), 'next_generation_so_far': int(len(nxt)),
           'stuck': int(len(stuck)), 'where_left': where(left), 'where_stuck': where(stuck) if len(stuck) else None, 'first_stuck': [list(map(float, s)) for s in stuck[:5]]}
    # how the boxes that are left look to the table: a random sample of them, re-evaluated (also with the frozen-split rule of the final table)
    rng = np.random.default_rng(w); smp = left[rng.choice(len(left), min(20000, len(left)), replace=False)]; mg, how = margin(smp)
    widths = {nm: float(np.median(np.where(np.isfinite(smp[:, j + 1] - smp[:, j]), smp[:, j + 1] - smp[:, j], np.nan)[np.isfinite(smp[:, j + 1] - smp[:, j])])) for nm, j in (('log mu', 0), ('log r', 2), ('log beta', 4), ('log kappa', 6), ('ell', 8))}
    res['sample_of_left'] = {'boxes': int(len(smp)), 'accepted now': int((mg > X.ACC).sum()), 'by': {str(k): int((how == k).sum()) for k in range(5)}, 'median widths': widths}
    json.dump(res, open(OUT, 'w'), indent=1); print(json.dumps({k: res[k] for k in ('closed', 'reason', 'generation', 'cells', 'left_in_generation', 'stuck', 'sample_of_left')}))
    return res


def follow(n=100000, gens=80, seed=3):
    """a random sample of initial boxes followed through the bisection (how many generations until the boxes pass) -> results/cz_column_follow.json"""
    import cz_checks as CK
    rng = np.random.default_rng(seed); B = CK.boxes(rng, n, ELL_A, ELL_B); out = {'initial_boxes_sampled': int(len(B)), 'generations': []}; total = 0
    for g in range(gens + 1):
        mg, how = margin(B); bad = B[~(mg > X.ACC)]; total += len(B)
        out['generations'].append({'generation': g, 'boxes': int(len(B)), 'not_accepted': int(len(bad))}); print(json.dumps(out['generations'][-1]), flush=True)
        if not len(bad) or g == gens: break
        W = np.stack([np.where(np.isfinite(bad[:, j]) & np.isfinite(bad[:, j + 1]), bad[:, j + 1] - bad[:, j], 0.0) * wt for j, wt in CW], axis=1); k = np.argmax(W, axis=1); new = []
        for ii, (j, wt) in enumerate(CW):
            sel = bad[k == ii]
            if not len(sel): continue
            mid = 0.5 * (sel[:, j] + sel[:, j + 1]); Lc = sel.copy(); Rc = sel.copy(); Lc[:, j + 1] = mid; Rc[:, j] = mid; new += [Lc, Rc]
        B = np.vstack(new)
    out['boxes_evaluated'] = int(total); out['where_not_accepted_at_the_end'] = where(bad) if len(bad) else None
    out['closed'] = not len(bad); out['weights (mu, r, beta, kappa, ell)'] = [wt for j, wt in CW]
    json.dump(out, open(os.path.join(RES, 'cz_column_follow.json'), 'w'), indent=1)
    return out


def merge(nw):
    R = [json.load(open(os.path.join(RES, 'cz_column_w%d.json' % w))) for w in range(nw)]
    out = {'ell': [ELL_A, ELL_B], 'band_excluded': False, 'closed': all(r['closed'] for r in R), 'cells': sum(r['cells'] for r in R), 'seconds': sum(r['seconds'] for r in R),
           'initial_boxes_all': R[0]['initial_boxes_all'], 'skipped (beta <= 2.5e10: Theorem H1)': sum(r['skipped'] for r in R),
           'accepted_by': {k: sum(r['accepted_by'].get(k, 0) for r in R) for k in ('z-options', 'old options', 'two-piece rule', 'frozen-split rule', 'constant F gain')}, 'stuck': sum(r['stuck'] for r in R), 'left': sum(r.get('left_in_generation', 0) + r.get('next_generation_so_far', 0) for r in R), 'workers': R}
    th = [r['thin'] for r in R if r.get('thin')]; out['thin'] = min(th, key=lambda t: t[0]) if th else None
    json.dump(out, open(os.path.join(RES, 'cz_column.json'), 'w'), indent=1); print(json.dumps({k: out[k] for k in ('closed', 'cells', 'seconds', 'accepted_by', 'stuck')}))
    return out


if __name__ == '__main__':
    if os.environ.get('CZ_AR') == '0': X.AR['on'] = False          # DA 2.2: the column is run without the stage of DA 2.3 (it is not needed there; saves time)
    if sys.argv[1] == 'merge': merge(int(sys.argv[2]))
    elif sys.argv[1] == 'finalize': finalize(int(sys.argv[2]))
    elif sys.argv[1] == 'follow': follow(int(sys.argv[2]) if len(sys.argv) > 2 else 100000)
    else: run(int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 6600.0)
