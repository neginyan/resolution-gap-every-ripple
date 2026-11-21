"""Stage DG 2.2: HOW THE MARGIN GROWS WITH ELL -- the adversarial search of the plan DG_探索計画.md (written before this code ran).  Python 3.11.  [numerical]
For ell in ELLS: the point margin of the table (zero-width boxes, cz_column.margin_table: stages 1-6, the point's own G_cell) over the class at that
ell; families F1 (residual points of DC/DD), F2 (heavy roots), F3 (the low-mu tail), F4 (global random), moved to the ell by two maps; the lowest
points refined by a local random search.  At the minimisers: the decomposition of Bz at G_cell (main gains / target / remainders at the binding A).
The room: f*(y) = the largest factor on the target gamma that keeps the point positive (bisection).
Power: W1 (gamma x 1.1 f*_min must give negative points), W0 (gamma x 0.9 f*_min must not), W2 (at ell = 955: gamma x f*_min(100) searched afresh).
-> results/dg_ell.json"""
import json, math, sys, time
import numpy as np
import cz_cells as X, cz_column as C, dg_tm as D

ELLS = (55.26, 100.0, 200.0, 305.0, 500.0, 955.0)


def ranges(ell):
    """(lo, hi) of (log mu, log r, log beta, log kappa) for the search at ell (finite parts of the tails included)."""
    return np.array([[math.log(1e-3) - 15, math.log(4 * ell + 40) + 3], [-3 * ell, math.log(0.25)], [X.LB_SKIP, math.log(X.BMAX) + 2 * ell], [math.log(1e-12) - 190, math.log(X.KMAX) + 3]])


def boxes_at(Y, ell):
    Z = np.zeros((len(Y), 10)); Z[:, 0:8:2] = Y; Z[:, 1:8:2] = Y; Z[:, 8] = Z[:, 9] = ell; return Z


def pmargin(Y, ell, full_below=0.6):
    """the table's point margin: first the z-options at the point (dg_tm at zero width = the table's stage 1, ~1 ms per point); where that is below
    full_below, the whole table (cz_column.margin_table: stages 1-6) and the larger of the two."""
    Z = boxes_at(Y, ell); m = np.full(len(Y), np.inf); sk = X.skip(Z)
    if (~sk).any():
        Zs = Z[~sk]; lG, _ = X.box_P(Zs)
        with np.errstate(all='ignore'): mz = D.tm_margin(Zs, lG, coords=(), scale=False)
        low = ~(mz > full_below)
        if low.any():
            with np.errstate(all='ignore'): mt, _ = C.margin_table(Zs[low])
            mz[low] = np.maximum(mz[low], mt)
        m[~sk] = mz
    return m                                                            # skipped (beta <= 2.5e10: Theorem H1) = +inf


def seeds(ell, rng):
    """the families F1-F3 moved to ell (two maps)."""
    S = []
    dc = json.load(open('results/dc_mainratio.json'))
    for k, v in dc.items():
        for d in v['details (residual)']:
            S.append((d['log mu'], d['log r'], d['log beta'], math.log(1e-30), d['ell']))
    for p in ((3.409, -88.0, 39.4), (3.407, -82.7, 43.3), (3.360, -80.2, 36.0), (3.238, -81.9, 36.7)):
        for lk in (-12 * math.log(10), -27 * math.log(10), -40 * math.log(10)): S.append((p[0], p[1], p[2], lk, 105.0))
    hard = [json.load(open('results/de_hardroot_a.json'))['root']] + [r['box'] for r in json.load(open('results/df_oracle.json'))['rows']]
    for b in hard:
        b = np.array(b, float)
        for _ in range(6):
            lo, hi = b[0::2].copy(), b[1::2].copy(); lo = np.where(np.isfinite(lo), lo, hi - 3); hi = np.where(np.isfinite(hi), hi, lo + 3)
            x = lo + (hi - lo) * rng.uniform(size=5); S.append(tuple(x))
    for _ in range(60):                                                 # F3: the low-mu tail, deep kappa, r << sigma
        e0 = 100.0; S.append((rng.uniform(-15, math.log(1e-3)), -e0 - rng.uniform(2, 20), rng.uniform(25, 40), rng.uniform(-80, -28), e0))
    out = []
    for (lm, lr, lB, lk, e0) in S:
        R0 = ranges(e0); R1 = ranges(ell)
        # map (i): relative position of r and beta in their ranges
        fr = (lr - R0[1, 0]) / (R0[1, 1] - R0[1, 0]); fb = (lB - R0[2, 0]) / (R0[2, 1] - R0[2, 0])
        out.append((lm, R1[1, 0] + fr * (R1[1, 1] - R1[1, 0]), R1[2, 0] + fb * (R1[2, 1] - R1[2, 0]), lk))
        # map (ii): log b = log beta - 2 ell and log(r / sigma) kept
        out.append((lm, lr + e0 - ell, lB - 2 * e0 + 2 * ell, lk))
    Y = np.array(out); R = ranges(ell)
    return np.clip(Y, R[:, 0], R[:, 1])


def fstar_lines(Y, ell, plant=None, grid=2001):
    """the room f*(y) of the claim at the point, in units of the target: max over the z-options of min over the two ends of G of
    min over A of (sum of the other lines) / (sum of the target lines d1-d4); for Tz, Bz the best of: B2 on the whole range, B1 on the whole range,
    B2 below and B1 above a split point (the table's rule; the best split on the grid).  The lines are dg_tm.z_lines at the point (= the table's lines, checked to 4e-14).  The low-mu
    region (mu < 1e-3) is not measured here (stage 6 decides there).  plant = (y0, w, depth): a planted dip for the power check."""
    Y = np.atleast_2d(np.asarray(Y, float)); n = len(Y)
    Z = boxes_at(Y, ell); lG, _ = X.box_P(Z); y = Z[:, 0::2]
    lA = np.linspace(0, 1, grid)[None, :] * (math.log(4) - 3 * ell); sh = (-2 * ell - math.log(4) - y[:, 1])[:, None]
    best = np.full(n, -np.inf)
    per_end = {}
    for end in ('c', '0+'):
        T, ext, aux = D.z_lines(y, y, lG, end); lines, calls = D._psi(T, ext)
        pos = aux['brk'].ok(); neg = aux['negbrk'].ok()
        for opt, cl in calls.items():
            vb = np.full(n, -np.inf); ratios = []
            for tags in cl:
                num = np.zeros((n, grid)); den = np.zeros((n, grid)); okall = np.ones(n, bool)
                terms = []
                for tag in tags:
                    t, p, s, q = lines[tag]
                    if s == 0 or q is None: continue
                    if tag == 'cKz': use = pos
                    elif tag == 'lossK': use = neg
                    else: use = np.ones(n, bool)
                    k, dp, d = D.TYPEINFO[t]; pA = p + dp
                    L = q.v[0] + k * (math.log(4) + y[:, 1]) + (pA - 1) * (-ell)
                    lg = -np.logaddexp(lA, sh) if t == 'H' else d * lA
                    okall &= np.isfinite(L) | ~use
                    terms.append((tag, s, np.where(use[:, None] & np.isfinite(L)[:, None], L[:, None] + lg, -np.inf)))
                Mx = np.max([x for _, _, x in terms], axis=0); Mx = np.where(np.isfinite(Mx), Mx, 0.0)   # per state and A: the largest line (the ratio is exact)
                for tag, s, x in terms:
                    val = np.exp(x - Mx)
                    if tag in ('d1', 'd2', 'd3', 'd4'): den += val
                    else: num += s * val
                rr = np.where(den > 0, num / np.where(den > 0, den, 1), np.where(num > 0, np.inf, -np.inf))
                rr = np.where(okall[:, None], rr, -np.inf); ratios.append(rr)
                vb = np.maximum(vb, rr.min(axis=1))                                    # the branch on the whole range
            if len(ratios) == 2:                                                       # B2 on [A_lo, A_m], B1 on [A_m, A_hi]: the best split point
                # the grid runs from A = 1 (index 0) DOWN to 4 sigma^3: the prefix is the large-A side (branch B1), the suffix the small-A side (B2)
                pre = np.minimum.accumulate(ratios[1], axis=1); suf = np.minimum.accumulate(ratios[0][:, ::-1], axis=1)[:, ::-1]
                vb = np.maximum(vb, np.max(np.minimum(pre[:, :-1], suf[:, 1:]), axis=1))
            valid = pos if opt == 'Tz' else (pos | neg) if opt == 'Bz' else np.ones(n, bool)
            per_end.setdefault(opt, []).append(np.where(valid, vb, -np.inf))
    for opt, v in per_end.items(): best = np.maximum(best, np.minimum(v[0], v[1]))
    if plant is not None:
        y0, w, depth = plant; best = np.minimum(best, depth * np.exp(np.sum(((Y - y0) / w) ** 2, axis=1) / 2))
    return np.where(np.exp(Y[:, 0]) >= 1e-3, best, np.inf)


def search_f(ell, rng, n_rand=20000, n_ref=40, steps=300, plant=None, grid=801):
    R = ranges(ell); R[0, 0] = math.log(1e-3)
    Y = np.vstack([R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(size=(n_rand, 4)), np.clip(seeds(ell, rng), R[:, 0], R[:, 1])])
    Z = boxes_at(Y, ell); Y = Y[~X.skip(Z)]
    f = np.concatenate([fstar_lines(Y[i:i + 2000], ell, plant, grid=grid) for i in range(0, len(Y), 2000)])
    idx = np.argsort(f)[:n_ref]; Yr = Y[idx]; fr = f[idx]; W = R[:, 1] - R[:, 0]
    for s in range(steps):
        sc = (1 / 8) * (1e-4 * 8) ** (s / (steps - 1))
        Zc = np.clip(Yr + rng.normal(size=Yr.shape) * W * sc * (rng.uniform(size=Yr.shape) < 0.6), R[:, 0], R[:, 1])
        fz = fstar_lines(Zc, ell, plant, grid=grid); fz = np.where(X.skip(boxes_at(Zc, ell)), np.inf, fz)
        b = fz < fr; Yr = np.where(b[:, None], Zc, Yr); fr = np.where(b, fz, fr)
    fr = fstar_lines(Yr, ell, plant, grid=2001); return Yr, fr, len(Y)          # the final values on the fine grid


def refine(Y, ell, rng, steps=300):
    R = ranges(ell); W = R[:, 1] - R[:, 0]; m = pmargin(Y, ell)
    for s in range(steps):
        sc = (1 / 8) * (1e-4 * 8) ** (s / (steps - 1))
        Z = np.clip(Y + rng.normal(size=Y.shape) * W * sc * (rng.uniform(size=Y.shape) < 0.6), R[:, 0], R[:, 1])
        mz = pmargin(Z, ell); better = mz < m; Y = np.where(better[:, None], Z, Y); m = np.where(better, mz, m)
    return Y, m


def decompose(y, ell):
    """the z-option that gives the point margin (best over Tz, Bz, Fz of the worse end), at its binding end, branch B2 (one branch), the lines at the
    point in the variable A: shares of the target gamma sigma den at the binding A* (the minimiser of the sum over a grid of 4001 values of log A)."""
    Z = boxes_at(y[None, :], ell); lG, _ = X.box_P(Z)
    with np.errstate(all='ignore'): v, el = D.tm_values(Z, lG, scale=False, coords=())
    best = max(X.OPTS_Z, key=lambda k: min(v[k + '0+'][0], v[k + 'c'][0])); end = 'c' if v[best + 'c'][0] <= v[best + '0+'][0] else '0+'
    T, ext, aux = D.z_lines(Z[:, 0::2], Z[:, 0::2], lG, end); lines, calls = D._psi(T, ext)
    tags = calls[best][0]; sig_l = -ell; r_l = y[1]; lA = np.linspace(math.log(4) + 3 * sig_l, 0, 4001); sh = 2 * sig_l - math.log(4) - r_l
    vals = {}
    for tag in tags:
        t, p, s, q = lines[tag]
        if s == 0 or q is None or not bool(q.ok()[0]): continue
        if tag == 'cKz' and not bool(aux['brk'].ok()[0]): continue
        if tag == 'lossK' and not bool(aux['negbrk'].ok()[0]): continue
        k, dp, d = D.TYPEINFO[t]; pA = p + dp
        L = float(q.v[0][0]) + k * (math.log(4) + r_l) + (pA - 1) * sig_l
        lg = -np.logaddexp(lA, sh) if t == 'H' else d * lA
        vals[tag] = (s, L + lg)
    big = max(np.max(v[1]) for v in vals.values())
    F = sum(s * np.exp(v - big) for s, v in vals.values()); i = int(np.argmin(F))
    gains = ('P1', 'P2z', 'P3z', 'P4z', 'hFz', 'cKz'); target = ('d1', 'd2', 'd3', 'd4')
    g = sum(math.exp(v[1][i] - big) for k, v in vals.items() if k in gains); tg = sum(math.exp(v[1][i] - big) for k, v in vals.items() if k in target)
    rem = {k: math.exp(v[1][i] - big) / tg for k, v in vals.items() if k not in gains and k not in target and v[0] < 0}
    top = sorted(rem.items(), key=lambda kv: -kv[1])[:4]
    return {'option, end': [best, end], 'rho_main (gains / target)': g / tg, 'remainders / target': sum(rem.values()), 'largest remainders (share of target)': top,
            'gains (share of target)': {k: math.exp(v[1][i] - big) / tg for k, v in vals.items() if k in gains},
            'target lines (share)': {k: math.exp(v[1][i] - big) / tg for k, v in vals.items() if k in target}, 'log A*': float(lA[i])}


def run(save=True, n_rand=20000, n_ref=40, seed=1, ells=ELLS, w2=True):
    import os
    out = json.load(open('results/dg_ell.json')) if os.path.exists('results/dg_ell.json') else {'plan': 'DG_探索計画.md', 'ells': {}}; t0 = time.time()
    for ell in ells:
        if str(float(ell)) in out['ells']: continue                       # resumable: an ell already measured is kept
        rng = np.random.default_rng(seed); R = ranges(ell)
        Y4 = R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(size=(n_rand, 4)); S = seeds(ell, rng)
        Y = np.vstack([Y4, S]); m = pmargin(Y, ell)
        fam = {'F4 random': (0, n_rand), 'F1-F3 seeds': (n_rand, len(Y))}
        famres = {k: float(np.min(m[a:b])) for k, (a, b) in fam.items()}
        idx = np.argsort(m)[:n_ref]; Yr, mr = refine(Y[idx], ell, rng)
        # the room f* (units of the target), searched on its own (mu >= 1e-3)
        Yf, ff, nst = search_f(ell, np.random.default_rng(seed + 1))
        j = int(np.argmin(ff)); fmin = float(ff[j])
        rows = []
        for i in np.argsort(ff)[:5]:
            try: dec = decompose(Yf[i], ell)
            except Exception as ex: dec = {'error': repr(ex)}
            rows.append({'state (log mu, log r, log beta, log kappa)': [round(float(v), 4) for v in Yf[i]], 'f* (room, units of the target)': float(ff[i]),
                         'point margin of the table': float(pmargin(Yf[i:i + 1], ell)[0]), 'log(r/sigma)': float(Yf[i, 1] + ell), 'log b': float(Yf[i, 2] - 2 * ell), 'mu / ell': math.exp(Yf[i, 0]) / ell,
                         'decomposition (best z-option, binding end, B2)': dec})
        # power: three planted dips (width 5 % of every range, depth 0.5 f*_min): the same search must find each
        R4 = ranges(ell); R4[0, 0] = math.log(1e-3); prng = np.random.default_rng(seed + 100); found = []
        for k in range(3):
            y0 = R4[:, 0] + (R4[:, 1] - R4[:, 0]) * prng.uniform(0.1, 0.9, 4); w = 0.05 * (R4[:, 1] - R4[:, 0])
            Yp, fp, _ = search_f(ell, np.random.default_rng(seed + 200 + k), n_rand=8000, steps=150, plant=(y0, w, 0.5 * fmin))
            found.append(bool(fp.min() < fmin))
        res = {'states evaluated (point margin search)': int(len(Y)), 'min point margin by family (before refinement)': famres, 'min point margin of the table (refined; all stages)': float(mr.min()),
               'negative point margins': int(np.sum(mr <= X.ACC)), 'states evaluated (f* search, mu >= 1e-3)': nst, 'f*_min': fmin, 'lowest states (by f*)': rows,
               'power: planted dips found (3 of 3 needed)': found, 'seconds': round(time.time() - t0)}
        out['ells'][str(ell)] = res
        print(ell, {k: res[k] for k in ('min point margin of the table (refined; all stages)', 'negative point margins', 'f*_min', 'power: planted dips found (3 of 3 needed)', 'seconds')},
              rows[0]['state (log mu, log r, log beta, log kappa)'], rows[0]['decomposition (best z-option, binding end, B2)'].get('option, end'), flush=True)
        if save: json.dump(out, open('results/dg_ell.json', 'w'), indent=1, default=float)
    if not w2 or '100.0' not in out['ells'] or 'W2 at ell 955: f* below f*_min(100)?' in out: return out
    # W2: at ell = 955, is there any state with f* below f*_min(100)?  (a fresh search with another seed)
    r100 = out['ells']['100.0']['f*_min']; Yw, fw, nw_ = search_f(955.0, np.random.default_rng(seed + 7))
    out['W2 at ell 955: f* below f*_min(100)?'] = {'f*_min(100)': r100, 'f*_min found at 955 (fresh search)': float(fw.min()), 'states below': int(np.sum(fw < r100))}
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dg_ell.json', 'w'), indent=1, default=float)
    return out


if __name__ == '__main__':
    run(ells=tuple(float(a) for a in sys.argv[1:]) if len(sys.argv) > 1 else ELLS)
