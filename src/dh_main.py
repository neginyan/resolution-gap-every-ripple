"""Stage DH: THE POINT LINES OF THE TABLE AT ANY ELL, with a chosen brightness ceiling; the row comparison (2.1); the candidate DH-L (2.2).  [numerical]
Python 3.11 grammar.
(a) lP_log: the brightness bound of a POINT in logarithms (no bisection floor: 2.4).  The same inequality P/2 <= U(P) as cs_psi/cy_psi (CM-1 and the
    corollary of CN-1 for the table's list (K, L); mode 'JEN' adds the pairs of Lemma DH-1), solved by bisection in log P on [-1e7, log(2 mu Qb^2) + 50]
    with U evaluated in logarithms.  For kappa < 1e-12 the envelope of DE (kappa' = max(kappa, b e^t)).  At ell <= 965 it reproduces cz_cells.box_P.
    mode 'true': the brightness of the real one-carrier window with that (mu, kappa): 4 mu e^{-mu} min(1, sqrt(kappa)) (dh_true; no safety factor).
(b) fstar: the room f of the z-options' point lines (dg_tm.z_lines, in logarithms -> valid at every ell) with the given ceiling: as dg_ell.fstar_lines,
    but on a per-state A grid refined around the minimiser until the spacing in log A is < 5e-4 (the uniform grid of DG is too coarse at ell >> 1000).
    f is relative to the table's target (1 + 2.5e-4)/sqrt(ell);  f1 = f (1 + 2.5e-4) is relative to gamma_1 = 1/sqrt(ell)  (coefficient exactly 1).
(c) search: the smallest (f1^2 - 1) ell over the class at ell: the corner family, the DG seeds, global random; starts = the lowest states and the
    champions of a partition into cells; local refinement in two phases; planted dips and a fresh search with another seed (power).
Run: python3 dh_main.py validate | margins <ell> ... | power <ell> ... | merge | rows
-> results/dh_m_<ell>.json, results/dh_p_<ell>.json, merged into results/dh_main.json; results/dh_rows.json (rows);
   results/dh_main_first.json = the first search (lowest 40 only; its planted dips were not found: kept as a record)"""
import json, math, os, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
import numpy as np
import cz_cells as X, cy_psi as PS, dg_tm as D, dg_ell as GE, dh_true as TR

LN2 = math.log(2.0); T0 = 1 + 2.5e-4


def _lU(lP, lmu, lb, ls, lc):
    lE0 = lP - LN2 - lmu; lEh = np.minimum(lE0 - ls, math.log(1 / 16)); lbp = lb - 2 * ls
    with np.errstate(all='ignore'):
        bp = np.exp(np.minimum(lbp, 700.0))
        lnB0 = 2 * np.log(1 + np.exp(lEh / 2) + np.exp((lEh - LN2) / (2 + bp)))
        t1 = np.logaddexp(0.0, lbp - LN2) + ls + lEh + np.log(LN2 + lnB0 - lEh); t2 = math.log(CM.C_CM) + lbp + ls
    return lc + np.logaddexp(t1, t2)


def _pstar_log(lmu, lb, ls, lc, iters=75):
    lo = np.full(lmu.shape, -1e7); hi = np.log(2 * 0.0625) + lmu + 50
    for _ in range(iters):
        m = 0.5 * (lo + hi); f = m - LN2 <= _lU(m, lmu, lb, ls, lc); lo = np.where(f, m, lo); hi = np.where(f, hi, m)
    return hi


def lP_log(lmu, lb, lk, mode='DG'):
    """log of the point's brightness bound (+ 1e-6 as in the table); mode 'DG' (the table of DG), 'JEN' (with Lemma DH-1), 'true' (the real window),
    'CN+' (the lemma of DG, CN-1, with its list (K, L) continued to (2 lam, lam), lam up to 2^22: the list of the table ends at K = 256, L = 64 and
    loses a factor e^{~0.012 mu} at large mu; not in the table, a point bound for the comparison only)."""
    lmu, lb, lk = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, lk))
    if mode == 'true': return math.log(4.0) + lmu - np.exp(lmu) + 0.5 * np.minimum(lk, 0.0)
    best = _pstar_log(lmu, lb, np.zeros(lmu.shape), np.zeros(lmu.shape))
    deep = lk < math.log(1e-12) - 1e-9
    lks = [lk] + [np.where(deep, np.maximum(lk, lb + t), lk) for t in PS.ENV['t']]
    pairs = [(math.log(L * K), math.log(math.exp(1 / (2 * L)) / (1 - 1 / K))) for K in PS.KS for L in PS.LS]
    if mode == 'JEN': pairs += [(math.log(lam), 1 / (2 * lam)) for lam in PS.JEN['lams']]
    if mode == 'CN+': pairs += [(math.log(2 * lam * lam), 1 / (2 * lam) - math.log1p(-1 / (2 * lam))) for lam in PS.JEN['lams'] if lam >= 1]   # CN-1 with (K, L) = (2 lam, lam)
    for j, lk_ in enumerate(lks):
        if j > 0 and not deep.any(): break
        for (lLK, lc) in pairs:
            ok = lLK + lk_ <= 0
            if not ok.any(): continue
            lp = _pstar_log(lmu, lb, 0.5 * (lLK + np.where(ok, lk_, 0.0)), np.full(lmu.shape, lc)); best = np.where(ok, np.minimum(best, lp), best)
    return np.minimum(best, np.log(2 * 0.0625) + lmu) + 1e-6


def lG_of(Y, ell, mode):
    """log G_cell of the points Y = (log mu, log r, log beta, log kappa) at ell."""
    lb = np.minimum(Y[:, 2] - 2 * ell, math.log(X.BMAX)); r = np.exp(Y[:, 1])
    return lP_log(Y[:, 0], lb, Y[:, 3], mode) + 0.5 * (Y[:, 1] - np.log(2 + r))


def _ratios(lines, calls, aux, y, ell, lA, sh, want=None):
    """per option: list (per branch) of T(ratio), ratio = (other lines)/(target lines) on the grid lA (n, g), T(r) = sign(r) log(1 + |r|) (increasing in
    r, so min and max commute with it; computed from logarithms, so no overflow at any ell); and, if want = (opt, branch), the per-line values."""
    n, g = lA.shape; pos = aux['brk'].ok(); neg = aux['negbrk'].ok(); out = {}; detail = None
    for opt, cl in calls.items():
        rs = []
        for bi, tags in enumerate(cl):
            terms = []; okall = np.ones(n, bool)
            for tag in tags:
                t, p, s, q = lines[tag]
                if s == 0 or q is None: continue
                use = pos if tag == 'cKz' else neg if tag == 'lossK' else np.ones(n, bool)
                k, dp, d = D.TYPEINFO[t]; pA = p + dp
                Lc = q.v[0] + k * (math.log(4) + y[:, 1]) + (pA - 1) * (-ell)
                lg = -np.logaddexp(lA, sh) if t == 'H' else d * lA
                okall &= np.isfinite(Lc) | ~use
                terms.append((tag, s, np.where((use & np.isfinite(Lc))[:, None], Lc[:, None] + lg, -np.inf)))
            tg = [(tag, s, x) for tag, s, x in terms if tag in ('d1', 'd2', 'd3', 'd4')]; ot = [(tag, s, x) for tag, s, x in terms if tag not in ('d1', 'd2', 'd3', 'd4')]
            Mn = np.max([x for _, _, x in ot], axis=0); Mn = np.where(np.isfinite(Mn), Mn, 0.0); Md = np.max([x for _, _, x in tg], axis=0); Mdf = np.where(np.isfinite(Md), Md, 0.0)
            num = np.zeros((n, g)); den = np.zeros((n, g))
            for tag, s, x in ot: num += s * np.exp(x - Mn)
            for tag, s, x in tg: den += np.exp(x - Mdf)
            with np.errstate(all='ignore'):
                lr_ = np.log(np.abs(num)) + Mn - np.log(den) - Mdf                      # log |ratio| (no overflow at any ell)
                rr = np.where(den > 0, np.sign(num) * np.logaddexp(0.0, lr_), np.where(num > 0, np.inf, -np.inf)); rr = np.where(num == 0, 0.0, rr)
            rs.append(np.where(okall[:, None], rr, -np.inf))
            if want == (opt, bi): detail = ({tag: (s, x) for tag, s, x in terms}, Mdf + np.log(den))
        valid = pos if opt == 'Tz' else (pos | neg) if opt == 'Bz' else np.ones(n, bool)
        out[opt] = (rs, valid)
    return out, detail


def _value(rs):
    """the table's rule for one option at one end: the best of branch-on-the-whole-range and the best split (the grid runs from large A to small A)."""
    vb = np.max([r.min(axis=1) for r in rs], axis=0)
    if len(rs) == 2:
        pre = np.minimum.accumulate(rs[1], axis=1); suf = np.minimum.accumulate(rs[0][:, ::-1], axis=1)[:, ::-1]
        vb = np.maximum(vb, np.max(np.minimum(pre[:, :-1], suf[:, 1:]), axis=1))
    return vb


def fstar(Y, ell, lG, grid=401, zgrid=201, tol=5e-4, detail=False):
    """f (relative to the table's target) of the points Y at ell with the ceiling lG.  detail: also the lines of the binding option at its minimiser."""
    Y = np.atleast_2d(np.asarray(Y, float)); n = len(Y); Z = GE.boxes_at(Y, ell); y = Z[:, 0::2]
    lo = math.log(4) - 3 * ell; sh = (-2 * ell - math.log(4) - y[:, 1])[:, None]
    L = {}
    for end in ('c', '0+'):
        T, ext, aux = D.z_lines(y, y, lG, end); lines, calls = D._psi(T, ext); L[end] = (lines, calls, aux)
    lA = np.broadcast_to(np.linspace(0, 1, grid)[None, :] * lo, (n, grid)).copy(); half = 2 * abs(lo) / (grid - 1)
    while True:
        R = {end: _ratios(*L[end], y, ell, lA, sh)[0] for end in ('c', '0+')}
        vals = {opt: np.where(R['c'][opt][1], np.minimum(_value(R['c'][opt][0]), _value(R['0+'][opt][0])), -np.inf) for opt in R['c']}
        opts = list(vals); V = np.stack([vals[o] for o in opts]); bo = np.argmax(V, axis=0); f = V.max(axis=0)
        with np.errstate(all='ignore'): f = np.sign(f) * np.expm1(np.abs(f))                 # back from T(ratio) to the ratio
        if half <= tol * zgrid / 4: break
        # refine around the minimiser of the binding option (end 'c', the pointwise better branch)
        rmax = np.stack([np.max(np.stack(R['c'][o][0]), axis=0) for o in opts])[bo, np.arange(n)]
        with np.errstate(all='ignore'): c = lA[np.arange(n), np.argmin(np.where(np.isfinite(rmax), rmax, np.inf), axis=1)]
        new = np.clip(c[:, None] + np.linspace(-1, 1, zgrid)[None, :] * half, lo, 0.0)
        lA = -np.sort(-np.concatenate([lA, new], axis=1), axis=1); half = 4 * half / (zgrid - 1)
    if not detail: return f
    # the lines of the binding option at end 'c' on its better branch, at the minimiser
    det = []
    for i in range(n):
        o = opts[bo[i]]; rs = R['c'][o][0]; rmx = np.max(np.stack([r[i] for r in rs]), axis=0)      # the pointwise better branch (the split rule's value is its minimum)
        j = int(np.argmin(np.where(np.isfinite(rmx), rmx, np.inf))); bi = int(np.argmax([r[i][j] for r in rs]))
        _, dt = _ratios(*L['c'], y[i:i + 1], ell, lA[i:i + 1, j:j + 1], sh[i:i + 1], want=(o, bi))
        terms, lden = dt
        det.append({'option': o, 'branch': 'B2' if bi == 0 else 'B1', 'log A': float(lA[i, j]),
                    'lines / target': {tag: float(s * np.exp(x[0, 0] - lden[0, 0])) for tag, (s, x) in terms.items()}})
    return f, det


def fstar_robust(Y, ell, lG, grid=401, zc=41, tol=None):
    """f as fstar, with the A grid refined around EVERY candidate: the minimiser of every (end, option, branch), the best split point of the two
    branches and the minimiser of each branch on its side of that split (fstar refines only around the minimiser of the binding option at end 'c': exact where f is low, but it can overestimate f by a few
    per cent to tens of per cent at states where f >> 1, because the composite rule max-of-min is not convex in log A).  Slower; used for the
    validation (V2-V4) and for the stored worst states.  tol (the spacing of log A at the end): default min(5e-4, 0.03/sqrt(ell)) -- the grid
    minimum is above the true minimum by ~ spacing^2/8 in f, i.e. ~ ell spacing^2/4 in (f1^2 - 1) ell: < 3e-4 with this default."""
    if tol is None: tol = min(5e-4, 0.03 / math.sqrt(ell))
    Y = np.atleast_2d(np.asarray(Y, float)); n = len(Y); Z = GE.boxes_at(Y, ell); y = Z[:, 0::2]; ar = np.arange(n)
    lo = math.log(4) - 3 * ell; sh = (-2 * ell - math.log(4) - y[:, 1])[:, None]
    L = {}
    for end in ('c', '0+'):
        T, ext, aux = D.z_lines(y, y, lG, end); lines, calls = D._psi(T, ext); L[end] = (lines, calls, aux)
    lA = np.broadcast_to(np.linspace(0, 1, grid)[None, :] * lo, (n, grid)).copy(); half = 2 * abs(lo) / (grid - 1)
    while True:
        R = {end: _ratios(*L[end], y, ell, lA, sh)[0] for end in ('c', '0+')}
        vals = {opt: np.where(R['c'][opt][1], np.minimum(_value(R['c'][opt][0]), _value(R['0+'][opt][0])), -np.inf) for opt in R['c']}
        f = np.stack([vals[o] for o in vals]).max(axis=0)
        if 2 * half / (zc - 1) <= tol / 10 or half < tol: break
        cs = []
        for end in ('c', '0+'):
            for o in vals:
                rs = R[end][o][0]
                for r in rs:
                    with np.errstate(all='ignore'): cs.append(lA[ar, np.argmin(np.where(np.isfinite(r), r, np.inf), axis=1)])
                if len(rs) == 2:
                    pre = np.minimum.accumulate(rs[1], axis=1); suf = np.minimum.accumulate(rs[0][:, ::-1], axis=1)[:, ::-1]
                    k = np.argmax(np.minimum(pre[:, :-1], suf[:, 1:]), axis=1); cs.append(lA[ar, k]); cs.append(lA[ar, k + 1])
                    ix = np.arange(lA.shape[1])[None, :]                               # the minimisers of each branch on its side of the best split
                    with np.errstate(all='ignore'):
                        cs.append(lA[ar, np.argmin(np.where((ix <= k[:, None]) & np.isfinite(rs[1]), rs[1], np.inf), axis=1)])
                        cs.append(lA[ar, np.argmin(np.where((ix > k[:, None]) & np.isfinite(rs[0]), rs[0], np.inf), axis=1)])
        new = np.concatenate([np.clip(c[:, None] + np.linspace(-1, 1, zc)[None, :] * half, lo, 0.0) for c in cs], axis=1)
        lA = -np.sort(-np.concatenate([lA, new], axis=1), axis=1); half = 4 * half / (zc - 1)
    with np.errstate(all='ignore'): return np.sign(f) * np.expm1(np.abs(f))


def m_of(f, ell):
    """(f1^2 - 1) ell with f1 = f (1 + 2.5e-4): the margin against the coefficient 1."""
    return ((f * T0) ** 2 - 1) * ell


def ranges(ell):
    return np.array([[math.log(1e-3), math.log(4 * ell + 40) + 3], [-3 * ell, math.log(0.25)], [X.LB_SKIP, math.log(X.BMAX) + 2 * ell], [math.log(1e-12) - 190, math.log(X.KMAX) + 3]])


CBOX = np.array([[-6.0, 45.0], [-15.0, 15.0], [-12.0, 30.0], [-40.0, 5.0]])       # the corner family in (ell/4 - mu, log r + ell/2, log b + ell, log kappa)


def corner_family(ell, rng, n):
    mu = np.maximum(ell / 4 - rng.uniform(CBOX[0, 0], CBOX[0, 1], n), 1.0)
    return np.stack([np.log(mu), -ell / 2 + rng.uniform(CBOX[1, 0], CBOX[1, 1], n), ell + rng.uniform(CBOX[2, 0], CBOX[2, 1], n), rng.uniform(CBOX[3, 0], CBOX[3, 1], n)], axis=1)


def corner_coords(Y, ell):
    return np.stack([ell / 4 - np.exp(Y[:, 0]), Y[:, 1] + ell / 2, Y[:, 2] - ell, Y[:, 3]], axis=1)


def planted(Yc, ell, plant):
    """a planted dip for the power check, in the units of the claim: (f1^2 - 1) ell = depth + 10 d^2, d = the distance from the centre in units of the
    widths w; kind 'corner': distance in the corner coordinates; kind 'global': in (log mu, log r, log beta, log kappa).  Returns f (table target)."""
    kind, y0, w, depth = plant
    U = corner_coords(Yc, ell) if kind == 'corner' else Yc
    d2 = np.sum(((U - y0) / w) ** 2, axis=1)
    return np.sqrt(1 + (depth + 10 * d2) / ell) / T0


def _champions(f, cell, k, taken):
    """the lowest point of each cell, the k lowest of these (not already taken)."""
    out = []; seen = set()
    for i in np.argsort(f):
        if not np.isfinite(f[i]) or len(out) >= k: break
        c = int(cell[i])
        if c in seen: continue
        seen.add(c)
        if int(i) not in taken: out.append(int(i))
    return out


def search(ell, mode, rng, n_corner=6000, n_rand=6000, n_low=40, n_cell=120, steps1=30, steps2=100, plant=None, seeds=True, bins=6):
    """the smallest f over the class at ell.  Starts: the n_low lowest of all sampled states, and the champions (lowest point) of the cells of a
    bins^4 partition of the corner family (corner coordinates) and of the global family (the ranges): the n_cell lowest champions of each family.
    Phase 1: all starts, steps1 shrinking random steps (corner starts: steps of the corner's size; global starts: 1/8 of the ranges).  Phase 2: the
    n_low lowest, steps2 more steps down to 2e-4 of the corner's size.  (The first version refined only the lowest 40 states and missed planted
    dips in other basins: results/dh_main_first.json.)"""
    R = ranges(ell); Wd = np.array([8.0 / max(ell / 4, 4.0), 4.0, 4.0, 4.0]); Wg = (R[:, 1] - R[:, 0]) / 8
    Yc0 = np.clip(corner_family(ell, rng, n_corner), R[:, 0], R[:, 1]); Yg0 = R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(size=(n_rand, 4))
    Ys = [Yc0, Yg0] + ([np.clip(GE.seeds(ell, rng), R[:, 0], R[:, 1])] if seeds else [])
    Y = np.vstack(Ys); Y[:, 0] = np.maximum(Y[:, 0], R[0, 0]); kind = np.concatenate([np.full(len(v), k) for k, v in enumerate(Ys)])
    keep = ~X.skip(GE.boxes_at(Y, ell)); Y = Y[keep]; kind = kind[keep]
    def F(Yc, fine=False):
        out = np.empty(len(Yc))
        for i in range(0, len(Yc), 1500):
            Yi = Yc[i:i + 1500]
            with np.errstate(all='ignore'): f = fstar(Yi, ell, lG_of(Yi, ell, mode), grid=401 if fine else 201, zgrid=201 if fine else 101, tol=5e-4 if fine else 2e-3)
            out[i:i + 1500] = np.where(X.skip(GE.boxes_at(Yi, ell)) | ~np.isfinite(f), np.inf, f)
        if plant is not None: out = np.minimum(out, planted(Yc, ell, plant))
        return out
    f = F(Y)
    uc = (corner_coords(Y, ell) - CBOX[:, 0]) / (CBOX[:, 1] - CBOX[:, 0]); ug = (Y - R[:, 0]) / (R[:, 1] - R[:, 0])
    cid = lambda u: np.sum(np.clip((u * bins).astype(int), 0, bins - 1) * bins ** np.arange(4), axis=1)
    low = [int(i) for i in np.argsort(f)[:n_low]]; taken = set(low)
    ic = np.where(kind == 0)[0]; ig = np.where(kind == 1)[0]
    cc = [int(ic[j]) for j in _champions(f[ic], cid(uc[ic]), n_cell, set())]; cc = [i for i in cc if i not in taken]; taken |= set(cc)
    cg = [int(ig[j]) for j in _champions(f[ig], cid(ug[ig]), n_cell, set())]; cg = [i for i in cg if i not in taken]
    idx = np.array(low + cc + cg); Yr = Y[idx]; fr = f[idx]; glob = np.concatenate([kind[low] == 1, np.zeros(len(cc), bool), np.ones(len(cg), bool)])
    nev = len(Y)
    for s in range(steps1):                                                           # phase 1: every start
        sc = 0.1 ** (s / max(steps1 - 1, 1)); W = np.where(glob[:, None], Wg[None, :], Wd[None, :]) * sc
        Zc = np.clip(Yr + rng.normal(size=Yr.shape) * W * (rng.uniform(size=Yr.shape) < 0.6), R[:, 0], R[:, 1])
        fz = F(Zc); b = fz < fr; Yr = np.where(b[:, None], Zc, Yr); fr = np.where(b, fz, fr); nev += len(Zc)
    o = np.argsort(fr)[:n_low]; Yr = Yr[o]; fr = fr[o]; glob = glob[o]
    for s in range(steps2):                                                           # phase 2: the lowest
        t = s / (steps2 - 1); Wc_ = Wd * 0.3 * (2e-4 / 0.3) ** t; Wg_ = np.exp((1 - t) * np.log(Wg / 80) + t * np.log(Wd * 2e-4))
        Zc = np.clip(Yr + rng.normal(size=Yr.shape) * np.where(glob[:, None], Wg_[None, :], Wc_[None, :]) * (rng.uniform(size=Yr.shape) < 0.6), R[:, 0], R[:, 1])
        fz = F(Zc); b = fz < fr; Yr = np.where(b[:, None], Zc, Yr); fr = np.where(b, fz, fr); nev += len(Zc)
    fr = F(Yr, fine=True); i = int(np.argmin(fr))
    return float(fr[i]), Yr[i], nev, np.sort(fr)[:10]


def describe(y, ell):
    mu = math.exp(y[0]); return {'state (log mu, log r, log beta, log kappa)': [float(v) for v in y], 'mu/ell': mu / ell, 'ell/4 - mu': ell / 4 - mu,
                                 'log r + ell/2': float(y[1] + ell / 2), 'log b + ell': float(y[2] - ell), 'log kappa': float(y[3])}


def validate_fast(rng, ells=(55.26, 955.8, 1e5), n_corner=1500, n_rand=500):
    """(V3) the fast refinement (fstar, used by the search) against the robust one (fstar_robust), ceiling of DH-1: the fast value is never below the
    robust one; where the margin is low ((f1^2 - 1) ell < 100) the two agree; no state has robust margin < 10 and fast margin >= 10."""
    out = {}
    for ell in ells:
        R = ranges(ell); Y = np.vstack([corner_family(ell, rng, n_corner), R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(size=(n_rand, 4))]); Y = np.clip(Y, R[:, 0], R[:, 1])
        Y = Y[~X.skip(GE.boxes_at(Y, ell))]; lG = lG_of(Y, ell, 'JEN')
        with np.errstate(all='ignore'):
            ff = np.concatenate([fstar(Y[i:i + 500], ell, lG[i:i + 500]) for i in range(0, len(Y), 500)])
            fr = np.concatenate([fstar_robust(Y[i:i + 100], ell, lG[i:i + 100]) for i in range(0, len(Y), 100)])
        fin = np.isfinite(ff) & np.isfinite(fr); mf = m_of(ff, ell); mr = m_of(fr, ell); lw = fin & (mr < 100)
        out[str(ell)] = {'states': int(fin.sum()), 'smallest (fast - robust)/robust (>= 0: fast never below)': float(np.min((ff[fin] - fr[fin]) / np.abs(fr[fin]))),
                         'largest (fast - robust)/robust (at states with f >> 1)': float(np.max((ff[fin] - fr[fin]) / np.abs(fr[fin]))),
                         'states with robust (f1^2 - 1) ell < 100': int(lw.sum()), 'largest |fast - robust| of (f1^2 - 1) ell among them': float(np.max(np.abs(mf[lw] - mr[lw]))) if lw.any() else 0.0,
                         'states with robust margin < 10 and fast margin >= 10': int(np.sum(fin & (mr < 10) & (mf >= 10))), 'smallest robust (f1^2 - 1) ell in the sample': float(np.min(mr[fin]))}
        print('V3', ell, out[str(ell)], flush=True)
    return out


def validate_near(rng, ells=(55.26, 955.8, 1e4, 1e6), n=400):
    """(V4) fast against robust refinement next to the stored worst states (ceiling of DH-1): states at distances ~1.5 in the corner coordinates."""
    out = {}
    for ell in ells:
        y0 = np.array(json.load(open('results/dh_m_%s.json' % ell))['JEN']['state (log mu, log r, log beta, log kappa)']); mu0 = math.exp(y0[0])
        Y = y0[None, :] + rng.normal(size=(n, 4)) * np.array([1.5 / mu0, 1.5, 1.5, 1.5]); Y = np.clip(Y, ranges(ell)[:, 0], ranges(ell)[:, 1]); lG = lG_of(Y, ell, 'JEN')
        with np.errstate(all='ignore'):
            ff = fstar(Y, ell, lG); fr = np.concatenate([fstar_robust(Y[i:i + 100], ell, lG[i:i + 100]) for i in range(0, n, 100)])
        mf = m_of(ff, ell); mr = m_of(fr, ell)
        out[str(ell)] = {'states': n, '(f1^2 - 1) ell in the sample (robust): smallest, median, largest': [float(np.min(mr)), float(np.median(mr)), float(np.max(mr))],
                         'largest |fast - robust| of (f1^2 - 1) ell': float(np.max(np.abs(mf - mr))), 'smallest fast - robust (>= 0)': float(np.min(mf - mr))}
        print('V4', ell, out[str(ell)], flush=True)
    return out


def validate(rng):
    """(V1) lP_log against the table's box_P; (V2) fstar (refined grid) and fstar_robust against dg_ell.fstar_lines (uniform grids 2001 and, for
    ell <= 331.56, 40001), ell <= 955.8.  A finer grid lowers the minimum over A; it can also raise f where it finds a better split point of the
    two branches (the table's rule takes the best split), so differences of both signs against the grid of DG are expected."""
    out = {}
    for ell in (55.26, 331.56, 955.8):
        Y = np.vstack([corner_family(ell, rng, 300), GE.ranges(ell)[:, 0] + (GE.ranges(ell)[:, 1] - GE.ranges(ell)[:, 0]) * rng.uniform(size=(300, 4))])
        Y[:, 0] = np.maximum(Y[:, 0], math.log(1e-3)); Y = Y[~X.skip(GE.boxes_at(Y, ell))]
        lGt, _ = X.box_P(GE.boxes_at(Y, ell)); lGm = lG_of(Y, ell, 'DG')
        with np.errstate(all='ignore'):
            f0 = GE.fstar_lines(Y, ell, grid=2001); f1 = fstar(Y, ell, lGt); f2 = np.concatenate([fstar_robust(Y[i:i + 100], ell, lGt[i:i + 100]) for i in range(0, len(Y), 100)])
        fin = np.isfinite(f0) & np.isfinite(f1) & np.isfinite(f2) & (f0 < 1e6)
        out[str(ell)] = {'points': int(len(Y)), 'largest |log G (log form) - log G (table)|': float(np.max(np.abs(lGm - lGt))),
                         'largest (f fast - f DG grid)/f': float(np.max((f1[fin] - f0[fin]) / f0[fin])), 'smallest (f refined - f DG grid)/f': float(np.min((f1[fin] - f0[fin]) / f0[fin])),
                         'largest (f robust - f DG grid)/f (<= ~0: the robust grid is never above the uniform grid of DG)': float(np.max((f2[fin] - f0[fin]) / f0[fin])),
                         'smallest (f robust - f DG grid)/f': float(np.min((f2[fin] - f0[fin]) / f0[fin])),
                         'same sign of f - 1': bool(np.all((f0 > 1) == (f1 > 1)) and np.all((f0 > 1) == (f2 > 1)))}
        if ell < 400:
            with np.errstate(all='ignore'): fu = np.concatenate([GE.fstar_lines(Y[i:i + 50], ell, grid=40001) for i in range(0, len(Y), 50)])
            fin = fin & np.isfinite(fu)
            out[str(ell)]['(f robust - f uniform 40001)/f: smallest, largest'] = [float(np.min((f2[fin] - fu[fin]) / fu[fin])), float(np.max((f2[fin] - fu[fin]) / fu[fin]))]
    return out


def rows(ells=(55.26, 100.0, 165.78, 331.56, 663.1, 955.8), save=True):
    """2.1: at the table's worst state (DG ceiling) -- the table's lines against the true pieces of the real window with that (mu, kappa)."""
    rng = np.random.default_rng(7); out = {}
    for ell in ells:
        f, y, nev, _ = search(ell, 'DG', rng)
        fd, det = fstar(y[None, :], ell, lG_of(y[None, :], ell, 'DG'), detail=True); d = det[0]
        lA = d['log A']; ls2 = -2 * ell - lA; lb = y[2] - 2 * ell; mu = math.exp(y[0]); lkap = min(y[3], 0.0)
        tr = TR.closed(ell, mu, lb, y[1], ls2, lkap)                                  # the real window (packet with kappa, or the comb)
        lGt = float(lG_of(y[None, :], ell, 'DG')[0]); lGtrue = float(tr['lW']) + LN2  # G = 2 W
        tgt_tab = {k: v for k, v in d['lines / target'].items()}
        # true pieces, in units of the TRUE target gamma_1 (b + W) sigma -> pieces are already divided by sigma; gamma_1 = 1/sqrt(ell)
        ltt = np.logaddexp(tr['d_b'], tr['d_W']) - 0.5 * math.log(ell)
        true_rel = {k: float(np.exp(tr[k] - ltt)) for k in ('P1', 'P2', 'P34', 'hF', 'chirp')}
        # the same lines of the table per unit G: (line/target)_table x target_table / (true piece), with the table's lines rescaled to the true G
        sc = math.exp(lGtrue - lGt)                                                   # the lines proportional to G scale with it
        # absolute sizes in logarithms (divided by sigma): table line = (line/target) x T_tab, T_tab from d1: |d1| = gamma b (1 + (eta + 0.184) k_E)
        coef = {}; gam = T0 / math.sqrt(ell); kE = math.sqrt(math.exp(y[1]) / (1 + math.exp(y[1]))); lsc = lGtrue - lGt
        lTtab = math.log(gam) + lb + math.log1p((1 / ell + 0.184) * kE) - math.log(-tgt_tab['d1'])
        def rat(val, ltrue, perG=False):
            return math.copysign(math.exp(math.log(abs(val)) + lTtab + (lsc if perG else 0.0) - float(ltrue)), val) if val != 0 else 0.0
        coef['P1 (w background)'] = rat(tgt_tab['P1'], tr['P1'])
        coef['P2z (w gain of the window), per unit G'] = rat(tgt_tab['P2z'], tr['P2'], True)
        coef['hFz (F main), per unit G'] = rat(tgt_tab['hFz'], tr['hF'], True)
        coef['P4z + P3z (v background)'] = rat(tgt_tab['P4z'] + tgt_tab['P3z'], tr['P34'])
        coef['chirp, per unit G'] = rat(tgt_tab.get('cKz', 0.0) - tgt_tab.get('lossK', 0.0), tr['chirp'], True)
        coef['d1 (target, b part)'] = rat(-tgt_tab['d1'], tr['d_b'] + math.log(gam))
        coef['d2 (target, W part), per unit G'] = rat(-tgt_tab['d2'], tr['d_W'] + math.log(gam), True)
        rest = sum(v for k, v in tgt_tab.items() if k not in ('P1', 'P2z', 'hFz', 'P4z', 'P3z', 'cKz', 'lossK', 'd1', 'd2', 'd3', 'd4'))
        gtrue = float(tr['g'])
        out[str(ell)] = {'the table\'s worst state': describe(y, ell), 'f (table, target (1 + 2.5e-4)/sqrt(ell))': f, '(f1^2 - 1) ell (table)': m_of(f, ell),
                         'binding option, branch, log A': [d['option'], d['branch'], lA],
                         'table lines / table target at the minimiser': {k: tgt_tab[k] for k in ('P1', 'P2z', 'hFz', 'P4z', 'P3z', 'cKz', 'lossK', 'd1', 'd2', 'd3', 'd4') if k in tgt_tab},
                         'all remainder lines together / target': rest,
                         'true pieces / true target (the real window with this mu, kappa, at the same state)': true_rel,
                         'true g sqrt(ell) of that window at this state': gtrue, '(g^2 - 1) ell of that window at this state': (gtrue ** 2 - 1) * ell,
                         'brightness: G_cell (table) / G (real window)': math.exp(lGt - lGtrue),
                         'coefficient ratios table/true (1 = the row is exact)': coef, 'states evaluated': nev}
        # (b) the TRUE worst state (the comb, kappa = 1; dh_true.json): the table's f there, its lines, and the table/true coefficient ratios
        tw = json.load(open('results/dh_true.json'))['worst comb state per ell'].get(str(ell))
        if tw is not None:
            yc = np.array([math.log(tw['mu']), tw['log r + ell/2'] - ell / 2, tw['log b + ell'] + ell, 0.0])
            fc, detc = fstar(yc[None, :], ell, lG_of(yc[None, :], ell, 'DG'), detail=True); dc = detc[0]
            trc = TR.closed(ell, tw['mu'], yc[2] - 2 * ell, yc[1], -2 * ell - dc['log A'])
            lGc = float(lG_of(yc[None, :], ell, 'DG')[0]); scc = math.exp(float(trc['lW']) + LN2 - lGc); tc_ = dc['lines / target']
            kEc = math.sqrt(math.exp(yc[1]) / (1 + math.exp(yc[1]))); lsc2 = float(trc['lW']) + LN2 - lGc; scc = math.exp(lsc2)
            lTc = math.log(gam) + (yc[2] - 2 * ell) + math.log1p((1 / ell + 0.184) * kEc) - math.log(-tc_['d1'])
            def ratc(val, ltrue, perG=True):
                return math.copysign(math.exp(math.log(abs(val)) + lTc + (lsc2 if perG else 0.0) - float(ltrue)), val) if val != 0 else 0.0
            out[str(ell)]['at the true worst state (comb, kappa = 1)'] = {
                'state': describe(yc, ell), 'f1 = f T0 of the table there (min over A)': float(fc[0]) * T0, '(f1^2 - 1) ell (table)': float(m_of(fc[0], ell)),
                'true g sqrt(ell) (min over s)': tw['g sqrt(ell) (T1)'], '(g^2 - 1) ell (true)': tw['(g^2 - 1) ell'],
                'brightness: G_cell (table) / G (comb)': 1 / scc, 'table lines / table target': {k: tc_[k] for k in ('P1', 'P2z', 'hFz', 'P4z', 'cKz', 'lossK', 'd1', 'd2') if k in tc_},
                'coefficient ratios table/true at the table\'s minimiser': {'P2z per unit G': ratc(tc_['P2z'], trc['P2']), 'hFz per unit G': ratc(tc_['hFz'], trc['hF']),
                    'chirp per unit G': ratc(tc_.get('cKz', 0.0) - tc_.get('lossK', 0.0), trc['chirp']), 'P4z + P3z': ratc(tc_['P4z'] + tc_['P3z'], trc['P34'], False),
                    'd2 per unit G': ratc(-tc_['d2'], trc['d_W'] + math.log(gam))},
                'remainder lines together / target': sum(v for k, v in tc_.items() if k not in ('P1', 'P2z', 'hFz', 'P4z', 'P3z', 'cKz', 'lossK', 'd1', 'd2', 'd3', 'd4'))}
        print(ell, json.dumps(out[str(ell)]), flush=True)
    if save: json.dump(out, open('results/dh_rows.json', 'w'), indent=1)
    return out


def sandwich_model(ell, rng, start=None):
    """the comb minimum with the table's sandwich factors put into the true closed form (P2, hF, chirp / (1 + eta); W part of den / (1 - eta);
    b part of den x (1 + (eta + 0.184) k_E)): what the factors eta = 1/ell cost at the true worst state.  start: the true worst state (dh_true)."""
    eta = 1 / ell
    def g_s(Y):
        with np.errstate(all='ignore'):
            P = TR.closed(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3]); kE = np.sqrt(np.exp(Y[:, 2]) / (1 + np.exp(Y[:, 2])))
            ln = np.logaddexp.reduce([P['P1'], P['P2'] - math.log1p(eta), P['P34'], P['hF'] - math.log1p(eta), P['chirp'] - math.log1p(eta)], axis=0)
            ld = np.logaddexp.reduce([P['d_b'] + np.log1p((eta + 0.184) * kE), P['d_W'] - math.log1p(-eta), P['d_a']], axis=0)
            g = math.sqrt(ell) * np.exp(ln - ld)
        return np.where(TR.in_class(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3]) & np.isfinite(g), g, np.inf)
    mu, lb, lr, ls2 = TR.corner_states(ell, rng, 30000); Y = np.stack([mu, lb, lr, ls2], axis=1)
    if start is not None: Y = np.vstack([Y, np.asarray(start, float)[None, :] + rng.normal(size=(2000, 4)) * np.array([3.0, 2.0, 2.0, 1.0]), np.asarray(start, float)[None, :]])
    g = g_s(Y); idx = np.argsort(g)[:60]; Yr = Y[idx]; gr = g[idx]; W = np.array([10.0, 4.0, 3.0, 2.0])
    for s in range(400):
        Zc = Yr + rng.normal(size=Yr.shape) * W * (1e-5) ** (s / 399) * (rng.uniform(size=Yr.shape) < 0.7); gz = g_s(Zc); b = gz < gr; Yr = np.where(b[:, None], Zc, Yr); gr = np.where(b, gz, gr)
    return float(gr.min())


def true_state(ell):
    """the true worst comb state at ell stored by dh_true (mu, log b, log r, log s^2), or None."""
    d = json.load(open('results/dh_true.json'))
    for key in ('worst comb state per ell', 'worst comb state at very large ell (T1)'):
        w = d[key].get(str(ell))
        if w is not None: return [ell * w['mu/ell'], w['log b + ell'] - ell, w['log r + ell/2'] - ell / 2, w['log s^2 + ell'] - ell], w['(g^2 - 1) ell']
    return None, None


ELLS = (55.26, 82.89, 165.78, 331.56, 663.1, 955.8, 3000.0, 1e4, 1e5, 1e6)
POWER_ELLS = (165.78, 1e5)


def margins_at(ell, save=True):
    """the searches at one ell (all ceilings) -> results/dh_m_<ell>.json"""
    rng = np.random.default_rng(20261113 + int(ell)); row = {}; t0 = time.time()
    for mode in ('DG', 'JEN', 'true') + (('CN+',) if ell >= 900 else ()):
        f, y, nev, low = search(ell, mode, rng)
        row[mode] = {'f (table target)': f, '(f1^2 - 1) ell': m_of(f, ell), 'ten lowest (f1^2 - 1) ell': [float(m_of(v, ell)) for v in low], **describe(y, ell), 'states evaluated': nev,
                     'below 10 (the constant of DH-L)': bool(m_of(f, ell) < 10), 'negative with the target 1 + 2.5e-4 (f < 1)': bool(f < 1)}
        print(ell, mode, json.dumps(row[mode]), flush=True)
    st, mtrue = true_state(ell)
    row['sandwich model: (g^2 - 1) ell of the comb with the factors eta = 1/ell'] = (sandwich_model(ell, rng, st) ** 2 - 1) * ell
    row['true (g^2 - 1) ell of the comb (dh_true)'] = mtrue; row['seconds'] = time.time() - t0
    if save: json.dump(row, open('results/dh_m_%s.json' % ell, 'w'), indent=1)
    return row


def power_at(ell, save=True):
    """planted dips of depth (f1^2 - 1) ell = 5 (the natural minimum is > 10): the same search (same settings) must find each.
    dip 0: in the corner family (widths 3 in every corner coordinate, the size of the natural basin); dips 1, 2: anywhere in the class
    (widths 5 % of every range, as in DG)."""
    rng = np.random.default_rng(777 + int(ell)); R = ranges(ell); hits = []; rows_ = []
    for k in range(3):
        if k == 0: plant = ('corner', CBOX[:, 0] + (CBOX[:, 1] - CBOX[:, 0]) * rng.uniform(0.15, 0.85, 4), np.full(4, 3.0), 5.0)
        else:
            y0 = R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(0.1, 0.9, 4); y0[0] = max(y0[0], math.log(2.0)); plant = ('global', y0, 0.05 * (R[:, 1] - R[:, 0]), 5.0)
        f, y, nev, _ = search(ell, 'JEN', rng, plant=plant)
        hits.append(bool(m_of(f, ell) < 5.5)); rows_.append({'kind': plant[0], 'centre': [float(v) for v in plant[1]], 'found (f1^2 - 1) ell': float(m_of(f, ell))})
        print('power', ell, rows_[-1], flush=True)
    f2, y2, nev2, _ = search(ell, 'JEN', np.random.default_rng(4242 + int(ell)))            # a fresh search with another seed (no dip): reproducibility
    out = {'planted dips of depth (f1^2 - 1) ell = 5 found (3 needed; the first in the corner family, two anywhere in the class)': hits, 'dips': rows_,
           'fresh search with another seed (JEN, no dip): (f1^2 - 1) ell': float(m_of(f2, ell)), 'its state': describe(y2, ell)}
    if save: json.dump(out, open('results/dh_p_%s.json' % ell, 'w'), indent=1)
    return out


def merge(save=True):
    try: out = json.load(open('results/dh_main.json'))
    except Exception: out = {}
    out = {'validation': out.get('validation'), 'validation of the fast refinement (V3)': out.get('validation of the fast refinement (V3)'),
           'validation of the fast refinement next to the worst states (V4)': out.get('validation of the fast refinement next to the worst states (V4)')}
    res = {}
    for ell in ELLS:
        try: res[str(ell)] = json.load(open('results/dh_m_%s.json' % ell))
        except Exception: continue
        res[str(ell)]['true (g^2 - 1) ell of the comb (dh_true)'] = true_state(ell)[1]
        for m in ('DG', 'JEN', 'true', 'CN+'):                                        # the stored worst state again with the robust refinement
            if m in res[str(ell)]:
                y = np.array(res[str(ell)][m]['state (log mu, log r, log beta, log kappa)'])[None, :]
                with np.errstate(all='ignore'): res[str(ell)][m]['(f1^2 - 1) ell at the stored state, robust refinement'] = float(m_of(fstar_robust(y, ell, lG_of(y, ell, m))[0], ell))
        for m in ('DG', 'JEN', 'true', 'CN+'):
            if m in res[str(ell)]: res[str(ell)][m]['(f^2 - 1) ell in the measure of DG (f relative to (1 + 2.5e-4)/sqrt(ell))'] = (res[str(ell)][m]['f (table target)'] ** 2 - 1) * ell
    first = json.load(open('results/dh_main_first.json'))
    for k, r in res.items():                                                          # the first search (lowest 40 only): its minima are certificates too
        for m in ('DG', 'JEN', 'true', 'CN+'):
            if m not in r: continue
            v = first['smallest (f1^2 - 1) ell per ell and ceiling'].get(k, {}).get(m); cand = [r[m]['(f1^2 - 1) ell at the stored state, robust refinement']]
            if v is not None and v['f (table target)'] < 2:                           # (ell = 1e6 overflowed in the first search)
                r[m]['first search: (f1^2 - 1) ell'] = v['(f1^2 - 1) ell']; y = np.array(v['state (log mu, log r, log beta, log kappa)'])[None, :]
                with np.errstate(all='ignore'): r[m]['first search: (f1^2 - 1) ell at its stored state, robust refinement'] = float(m_of(fstar_robust(y, float(k), lG_of(y, float(k), m))[0], float(k)))
                cand.append(r[m]['first search: (f1^2 - 1) ell at its stored state, robust refinement'])
            r[m]['lowest found (robust refinement at the stored states of both searches): (f1^2 - 1) ell'] = min(cand)
    out['smallest (f1^2 - 1) ell per ell and ceiling'] = res
    pw = {}
    for ell in POWER_ELLS:
        try: pw[str(ell)] = json.load(open('results/dh_p_%s.json' % ell))
        except Exception: pass
    out['power'] = pw
    out['first search (lowest 40 only; results/dh_main_first.json): planted dips found'] = {k: list(v.values())[0] for k, v in first['power'].items()}
    out['largest |fast - robust| of (f1^2 - 1) ell at the stored worst states'] = max(abs(r[m]['(f1^2 - 1) ell'] - r[m]['(f1^2 - 1) ell at the stored state, robust refinement']) for r in res.values() for m in ('DG', 'JEN', 'true', 'CN+') if m in r)
    out['largest |new search - first search| with the ceiling of DH-1 (ell <= 1e5)'] = max(abs(r['JEN']['(f1^2 - 1) ell'] - r['JEN']['first search: (f1^2 - 1) ell']) for r in res.values() if 'first search: (f1^2 - 1) ell' in r['JEN'])
    LOW = 'lowest found (robust refinement at the stored states of both searches): (f1^2 - 1) ell'
    out['DH-L with the ceiling of DG: first ell with (f1^2 - 1) ell < 10'] = next((float(k) for k in res if res[k]['DG'][LOW] < 10), None)
    out['DH-L with the ceiling of DH-1 (Psi_3): ells with (f1^2 - 1) ell < 10'] = [float(k) for k in res if res[k]['JEN'][LOW] < 10]
    out['wrong versions of DH-L (power)'] = {
        'constant 1.1 x the minimum (JEN): broken by a fresh search with another seed, per ell': {k: bool(v['fresh search with another seed (JEN, no dip): (f1^2 - 1) ell'] < 1.1 * res[k]['JEN']['(f1^2 - 1) ell']) for k, v in pw.items() if k in res},
        'fresh search - stored minimum, per ell': {k: v['fresh search with another seed (JEN, no dip): (f1^2 - 1) ell'] - res[k]['JEN']['(f1^2 - 1) ell'] for k, v in pw.items() if k in res},
        'target 1 + 2.5e-4 kept (JEN): ells where f < 1': [float(k) for k in res if res[k]['JEN']['negative with the target 1 + 2.5e-4 (f < 1)']]}
    if save: json.dump(out, open('results/dh_main.json', 'w'), indent=1)
    return out


def run_validate(save=True):
    try: out = json.load(open('results/dh_main.json'))
    except Exception: out = {}
    out['validation'] = validate(np.random.default_rng(20261113)); print(json.dumps(out['validation']), flush=True)
    out['validation of the fast refinement (V3)'] = validate_fast(np.random.default_rng(20261114))
    out['validation of the fast refinement next to the worst states (V4)'] = validate_near(np.random.default_rng(20261115))
    if save: json.dump(out, open('results/dh_main.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    a = sys.argv[1] if len(sys.argv) > 1 else 'merge'
    if a == 'rows': rows()
    elif a == 'validate': run_validate()
    elif a == 'validate_near':                                                        # only (V4), added to the stored record
        out = json.load(open('results/dh_main.json')); out['validation of the fast refinement next to the worst states (V4)'] = validate_near(np.random.default_rng(20261115))
        json.dump(out, open('results/dh_main.json', 'w'), indent=1)
    elif a == 'merge': print(json.dumps(merge())[:2000])
    elif a == 'power':
        for e in sys.argv[2:]:
            if not os.path.exists('results/dh_p_%s.json' % float(e)): power_at(float(e))
    elif a == 'margins':
        for e in sys.argv[2:]:
            if not os.path.exists('results/dh_m_%s.json' % float(e)): margins_at(float(e))       # finished ells are kept (the run can be resumed)
