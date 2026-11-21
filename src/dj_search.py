"""Stage DJ: THE ATTEMPT TO BREAK THE THEOREM DJ-T (plan DJ_探索計画.md secs. 3-4; the plan was written before this ran).  Python 3.11 grammar.

THE CLAIM.  For ell >= 55.26, every state (mu > 0, sigma^3 <= r <= 1/4, B >= max(2.5e10, 50 (8 ell + 100)), b <= 1/2, kappa > 0), every P in (0, Pbar] and every
a in [4 sigma^2, 4 r/sigma]:   F_full := min_a max_k f_k(a) satisfies (F_full^2 - 1) ell >= 10   (dj_lines: every line of the z-options, the best option-branch at
every a).   Pbar = the largest P allowed by (H'):  (A) P <= mu/8;  (K) kappa P <= 2 U1^2;  (CM) Lemma CM-1;  (J) the corollary of Lemma DH-1 for pairs
(lam, kappa_b) with kappa_b >= kappa and  b <= lam kappa_b <= 1  (b' = b/(lam kappa_b) <= 1: CM-1 is used at a focus inside its stated setting).
Pbar is computed from a FINITE set of pairs, so it is >= the true supremum allowed by (H'): the search is on the safe side.

THE COORDINATES OF THE SEARCH (five):  (log mu, log r, log B, log kappa, q),  q = log(P/Pbar) <= 0.   The value is log F_full (no conversion that could overflow;
a nan is counted, never turned into +inf silently).
FAMILIES: see families().  The search: the lowest states of all families and the champions of the cells of each family, shrinking random steps, a pattern search.
WRONG VERSIONS (must be broken where the plan says so): a main line dropped; (J) dropped; the pairs with lam ~ 1 dropped; one option-branch only; the lower end
of b removed; the ends of the a-range removed.  PLANTED DIPS (depth 5 in (F^2 - 1) ell).
    python3 dj_search.py main | power | tails      -> results/dj_main_<ell>.json, results/dj_power.json, results/dj_tails.json"""
import json, math, os, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
import numpy as np
import di_ceiling as CE, dj_lines as J

C_CLAIM = 10.0
LBMIN = math.log(2.5e10)
ELLS = (55.26, 82.89, 165.78, 331.56, 955.8, 3000.0, 1e4, 1e5, 1e6, 1e8)
NBS = (16.0, 256.0)                       # kappa_b = max(kappa, N b)                (lam ~ 1 pairs; b' <= 1/N)
NMS = (16.0, 256.0)                       # kappa_b = max(kappa, N b e^mu/mu)        (lam = mu pairs)


def lU1sq2(ell):
    return math.log(2 * (0.25 * math.sqrt(2 * ell + 3.1) + 1e-6) ** 2)


def pstar(lmu, lb, ls, lc, lo0, iters=72):
    """di_ceiling.pstar with the lower end of the bisection as an argument (di_ceiling's is fixed at log P = -1e7, which is above the true ceiling when
    kappa ~ sigma and ell ~ 1e8: the first run of this search at ell = 1e8 returned a false alarm from that floor -- results/dj_main_first_1e8.json)."""
    lmu, lb, ls, lc = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, ls, lc))
    lo = np.full(lmu.shape, float(lo0)); hi = np.log(2 * 0.0625) + lmu + 50; lbp = lb - 2 * ls
    with np.errstate(all='ignore'): bp = np.exp(np.minimum(lbp, 700.0)); l1b = np.log1p(bp / 2)
    for _ in range(iters):
        m = 0.5 * (lo + hi); lEh = m - CE.LN2 - lmu - ls
        with np.errstate(all='ignore'):
            free = lEh < math.log(1 / 16); lE = np.minimum(lEh, math.log(1 / 16))
            lh = np.log(CE.LN2 + CE.lB0(lE, bp) - lE)
            t21 = math.log(CM.C_CM) + lbp - l1b - lE - lh
            resid = lmu - lc - l1b - lh - np.logaddexp(0.0, t21)
            f = np.where(free, resid <= 0, m - CE.LN2 <= CE.M._lU(m, lmu, lb, ls, lc))
        lo = np.where(f, m, lo); hi = np.where(f, hi, m)
    return hi


def lPbar(ell, lmu, lb, lk, parts=('A', 'K', 'CM', 'J'), lam1=True, bprime=True):
    """log Pbar from the finite subset of (H').  parts: which facts are used; lam1 = False drops the pairs with lam ~ 1 (a wrong version of the search: the
    ceiling for small mu is lost); bprime = False also admits pairs with b' > 1 (the DI convention; recorded for comparison only)."""
    lmu, lb, lk = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, lk)); best = np.full(lmu.shape, np.inf); z = np.zeros(lmu.shape)
    if 'A' in parts: best = np.minimum(best, lmu - math.log(8))
    if 'K' in parts: best = np.minimum(best, lU1sq2(ell) - lk)
    lo0 = -max(1e7, 30 * ell + 1e4)
    if 'CM' in parts: best = np.minimum(best, pstar(lmu, lb, z, z, lo0))
    if 'J' in parts:
        with np.errstate(all='ignore'):
            kbs = [lk] + [np.maximum(lk, lb + math.log(N)) for N in NBS] + [np.maximum(lk, math.log(N) + lb + np.exp(lmu) - lmu) for N in NMS]
            for lkb in kbs:
                lams = [np.minimum(lmu, -lkb), np.minimum(lmu, -lkb) - math.log(2)]
                if lam1: lams += [np.minimum(0.0, -lkb), np.minimum(math.log(8), -lkb)]
                for llam in lams:
                    ls2 = llam + lkb; ok = np.isfinite(lkb) & np.isfinite(llam) & (ls2 <= 1e-12)
                    if bprime: ok &= ls2 >= lb - 1e-12
                    lp = pstar(lmu, lb, 0.5 * np.where(ok, ls2, 0.0), np.exp(-np.where(ok, llam, 0.0)) / 2, lo0)
                    best = np.where(ok, np.minimum(best, lp), best)
    return best


def ranges(ell, lBmin=LBMIN):
    """the ranges of the five coordinates: mu in [sigma^3, 8 ell + 80] (the theorem: every mu > 0); r in [sigma^3, 1/4]; B from max(2.5e10, 50 (8 ell + 100))
    (lBmin < log 2.5e10: a wrong version, taken as given) to 1/(2 sigma^2); kappa in [e^{-2.2 ell - 50}, e^{3 ell}]; q in [-4 ell, 0]."""
    lB0 = max(lBmin, math.log(50 * (8 * ell + 100))) if lBmin >= LBMIN else lBmin
    return np.array([[-3 * ell, math.log(8 * ell + 80)], [-3 * ell, math.log(0.25)], [lB0, math.log(0.5) + 2 * ell], [-2.2 * ell - 50, 3 * ell], [-4 * ell, 0.0]])


def value(Y5, ell, parts=('A', 'K', 'CM', 'J'), lam1=True, bprime=True, **kw):
    """log F_full at the five-coordinate states (and nan where the evaluation fails)."""
    Y5 = np.atleast_2d(np.asarray(Y5, float)); lb = Y5[:, 2] - 2 * ell
    lP = lPbar(ell, Y5[:, 0], lb, Y5[:, 3], parts, lam1, bprime) + Y5[:, 4]
    lF, la, kb = J.lF_point(ell, Y5[:, :4], lP, **kw)
    return lF


def narrow(Y, ell):
    return Y[:, 1] + 0.5 * Y[:, 0] < 2 * math.log(ell) - ell


def families(ell, rng, n, lBmin=LBMIN):
    """name -> states (n, 5), clipped to the ranges."""
    R = ranges(ell, lBmin); U = lambda a, b, k=n: rng.uniform(a, b, k); pick = lambda *xs: np.choose(rng.integers(0, len(xs), n), xs)
    lsg = -ell; line = 2 * math.log(ell) - ell                                     # narrow: log r + 0.5 log mu < line
    q = lambda: pick(np.zeros(n), np.zeros(n), -U(0, 5), -U(0, 60), -U(0, 4 * ell))
    lkw = lambda: pick(U(R[3, 0], R[3, 1]), U(-40, 5), -ell + U(0, 60), U(0, 20))
    F = {}
    mu_c = np.maximum(ell / 4 - U(-6, 45), 1.0)
    F['F1 corner'] = np.stack([np.log(mu_c), -ell / 2 + U(-15, 15), ell + U(-12, 30), U(-40, 5), pick(np.zeros(n), -U(0, 3))], axis=1)
    F['F2 global'] = np.stack([U(math.log(1e-3), R[0, 1]), U(R[1, 0], R[1, 1]), U(R[2, 0], R[2, 1]), U(R[3, 0], R[3, 1]), q()], axis=1)
    lmid = np.log(U(ell / 16, ell / 3))
    F['E1 small r, b at the lower end'] = np.stack([lmid, U(-3 * ell, -ell + 4 * math.log(ell)), R[2, 0] + U(0, 12), -ell + U(15, 35), q()], axis=1)
    F['E2 b at the lower end'] = np.stack([U(math.log(1e-3), R[0, 1]), U(R[1, 0], R[1, 1]), R[2, 0] + U(0, 9), lkw(), q()], axis=1)
    F['E3 large b'] = np.stack([U(math.log(1e-3), R[0, 1]), U(R[1, 0], R[1, 1]), 2 * ell + U(math.log(1e-4), math.log(0.5)), lkw(), q()], axis=1)
    F['E4 tails of mu'] = np.stack([pick(U(math.log(1e-3), math.log(5.0)), np.log(U(ell / 3, 8 * ell))), -ell / 2 + U(-15, 15), ell + U(-12, 30), U(-40, 5), q()], axis=1)
    F['E5 tails of kappa'] = np.stack([np.log(mu_c), -ell / 2 + U(-15, 15), ell + U(-12, 30), pick(U(R[3, 0], -40.0), U(0.0, 25.0)), q()], axis=1)
    # N1: the narrow states: just below the line, around xi = r sqrt(mu)/sigma ~ 1, around r ~ sqrt(ell) sigma, ell sigma, ell^1.5 sigma, down to sigma^3
    lm = pick(np.log(U(ell / 16, ell / 2)), U(math.log(1e-3), R[0, 1]), np.log(U(1.0, 12.0)))
    lr_n = pick(line - 0.5 * lm - U(0, 12), lsg - 0.5 * lm + U(-6, 8), lsg + math.log(ell) * U(0.0, 2.0) + U(-3, 3), U(-3 * ell, lsg))
    F['N1 narrow'] = np.stack([lm, lr_n, pick(R[2, 0] + U(0, 40), ell + U(-12, 30), U(R[2, 0], R[2, 1])), pick(-ell + U(0, 60), U(R[3, 0], R[3, 1]), U(-40, 5)), q()], axis=1)
    # N2: the low-mu tail: mu in [sigma^3, 1e-3]
    lm = pick(U(-3 * ell, math.log(1e-3)), U(-ell - 40, -ell + 60), U(-40, math.log(1e-3)))
    lr_t = pick(U(R[1, 0], R[1, 1]), line - 0.5 * lm - U(-6, 12), lsg + U(-12, 30))
    F['N2 low mu'] = np.stack([lm, lr_t, pick(R[2, 0] + U(0, 40), U(R[2, 0], R[2, 1])), pick(-ell + U(0, 60), U(R[3, 0], R[3, 1]), U(-40, 5)), q()], axis=1)
    # N3: the region of the DF diagnosis: kappa <~ e^{2.6} b/sigma, r << sigma, mu in [e^-15, 1e-3]; and the same with mu up to 12
    lB3 = R[2, 0] + U(0, 30)
    F['N3 DF region'] = np.stack([pick(U(-15, math.log(1e-3)), U(math.log(1e-3), math.log(12.0))), lsg - U(0, 60), lB3, lB3 - ell + U(-8, 8), pick(np.zeros(n), -U(0, 3))], axis=1)
    # N4: on the line r sqrt(mu) = ell^2 sigma and next to it; the pocket of DI (mu ~ 5, b near the lower end, kappa ~ b/sigma)
    lm = np.log(10 ** U(-1, 2.3)); lB4 = R[2, 0] + U(0, 40)
    F['N4 on the line'] = np.stack([lm, line - 0.5 * lm + pick(np.zeros(n), U(-0.01, 0.01), U(-3, 3)), lB4, pick(lB4 - ell + U(-6, 6), -ell + U(5, 60)), pick(np.zeros(n), -U(0, 3))], axis=1)
    # N5: large kappa (up to the end of (K)), and states next to the border of the cases I/II (G ~ 0.8 sqrt(b)/Gam2: q is set so in refine; here b ~ P^2 ell/2)
    lm = pick(U(math.log(1e-3), R[0, 1]), np.log(mu_c))
    F['N5 large kappa'] = np.stack([lm, U(R[1, 0], R[1, 1]), pick(U(R[2, 0], R[2, 1]), R[2, 0] + U(0, 30)), pick(U(0, 3 * ell), U(0, 30)), q()], axis=1)
    return {k: np.clip(v, R[:, 0], R[:, 1]) for k, v in F.items()}


def planted(Y5, ell, plant):
    """a planted dip: log F of a margin  depth + 100 sum ((y - centre)/width)^2  (in (F^2 - 1) ell)."""
    centre, widths, depth = plant
    m = depth + 100 * np.sum(((Y5 - np.asarray(centre)) / np.asarray(widths)) ** 2, axis=1)
    return 0.5 * np.log1p(m / ell)


def _champions(f, cell, k):
    out = []; seen = set()
    for i in np.argsort(f):
        if not np.isfinite(f[i]) or len(out) >= k: break
        c = int(cell[i])
        if c in seen: continue
        seen.add(c); out.append(int(i))
    return out


LAST = {}                                                                          # filled by search(): the minima per family after polishing


def search(ell, rng, n=2500, n_low=40, n_cell=40, n_fam=4, steps1=30, steps2=90, plant=None, seeds=None, bins=4, lBmin=LBMIN, only=None, vfun=None, **kw):
    """the smallest log F_full over the class at ell (vfun: another function of the five-coordinate states to minimise, e.g. the rule of the proof).  Returns (lF, state5, evaluations, per-family minima, nan count)."""
    R = ranges(ell, lBmin); Wd = np.array([8.0 / max(ell / 4, 4.0), 4.0, 4.0, 4.0, 2.0]); Wg = (R[:, 1] - R[:, 0]) / 8
    Fm = families(ell, rng, n, lBmin)
    if only is not None: Fm = {k: v for k, v in Fm.items() if k in only}
    if seeds is not None and len(seeds): Fm['F4 seeds'] = np.clip(np.asarray(seeds, float), R[:, 0], R[:, 1])
    nan = [0]
    def V(Yc):
        f = value(Yc, ell, **kw) if vfun is None else vfun(Yc); nan[0] += int(np.isnan(f).sum()); f = np.where(np.isnan(f), np.inf, f)
        if plant is not None: f = np.minimum(f, planted(Yc, ell, plant))
        return f
    Ys = []; fs = []; starts = []; glob = []; fids = []; off = 0; fam = {}; names = list(Fm); CORNER = ('F1 corner', 'E5 tails of kappa', 'E4 tails of mu', 'F4 seeds')
    for j, (name, Yf) in enumerate(Fm.items()):
        f = V(Yf); Ys.append(Yf); fs.append(f); fam[name] = float(np.min(f)); fids.append(np.full(len(Yf), j))
        lo = Yf.min(axis=0); w = np.maximum(Yf.max(axis=0) - lo, 1e-9); cell = np.sum(np.clip(((Yf[:, :4] - lo[:4]) / w[:4] * bins).astype(int), 0, bins - 1) * bins ** np.arange(4), axis=1)
        ch = _champions(f, cell, n_cell); starts += [off + i for i in ch]; off += len(Yf)
    Y = np.vstack(Ys); f = np.concatenate(fs); fid_all = np.concatenate(fids); nev = len(Y)
    low = [int(i) for i in np.argsort(f)[:n_low]]; idx = np.array(low + starts); fid = fid_all[idx]; gl = np.array([False] * len(low) + [names[j] not in CORNER for j in fid[len(low):]])
    Yr = Y[idx].copy(); fr = f[idx].copy()
    for s in range(steps1):
        sc = 0.1 ** (s / max(steps1 - 1, 1)); W = np.where(gl[:, None], Wg[None, :] / 4, Wd[None, :]) * sc
        Zc = np.clip(Yr + rng.normal(size=Yr.shape) * W * (rng.uniform(size=Yr.shape) < 0.6), R[:, 0], R[:, 1]); fz = V(Zc); b = fz < fr
        Yr = np.where(b[:, None], Zc, Yr); fr = np.where(b, fz, fr); nev += len(Zc)
    # second stage: the n_low lowest walkers AND the n_fam best walkers of every family (so that the walkers of the corner do not crowd out the other families:
    # the first version kept only the n_low lowest, and planted dips in the narrow and low-mu families were then not found -- results/dj_superseded/)
    o = [int(i) for i in np.argsort(fr)[:n_low]]
    for j in range(len(names)):
        w = np.where(fid == j)[0]
        if len(w): o += [int(i) for i in w[np.argsort(fr[w])[:n_fam]]]
    o = np.array(list(dict.fromkeys(o))); Yr = Yr[o]; fr = fr[o]; fid = fid[o]; gl = gl[o]; Wp = np.array([1.0, 4.0, 4.0, 4.0, 2.0])
    for s in range(steps2):
        t = s / (steps2 - 1); W = np.where(gl[:, None], Wp[None, :], Wd[None, :]) * 0.3 * (2e-4 / 0.3) ** t
        Zc = np.clip(Yr + rng.normal(size=Yr.shape) * W * (rng.uniform(size=Yr.shape) < 0.6), R[:, 0], R[:, 1]); fz = V(Zc); b = fz < fr
        Yr = np.where(b[:, None], Zc, Yr); fr = np.where(b, fz, fr); nev += len(Zc)
    # polishing (coordinate pattern search, steps halved until tiny): the lowest walker AND the best walker of every family, all to convergence
    pk = [int(np.argmin(fr))] + [int(w[np.argmin(fr[w])]) for w in (np.where(fid == j)[0] for j in range(len(names))) if len(w)]
    pk = np.array(list(dict.fromkeys(pk))); Yp = Yr[pk].copy(); fp = fr[pk].copy(); St = np.where(gl[pk][:, None], Wp[None, :], Wd[None, :]).copy(); act = np.isfinite(fp); it = 0
    E = np.zeros((10, 5)); Smax = (R[:, 1] - R[:, 0]) / 4
    for k in range(5): E[2 * k, k] = 1.0; E[2 * k + 1, k] = -1.0
    while act.any() and it < 1500:                    # all ten neighbours of every active walker in one call; the best improving one is taken
        it += 1; ia = np.where(act)[0]
        Z = np.clip(Yp[ia][:, None, :] + E[None, :, :] * St[ia][:, None, :], R[:, 0], R[:, 1]); fz = V(Z.reshape(-1, 5)).reshape(len(ia), 10); nev += 10 * len(ia)
        j = np.argmin(fz, axis=1); fb = fz[np.arange(len(ia)), j]; b = fb < fp[ia]
        Yp[ia[b]] = Z[b, j[b]]; fp[ia[b]] = fb[b]
        kk = j[b] // 2; St[ia[b], kk] = np.minimum(St[ia[b], kk] * 2, Smax[kk]); St[ia[~b]] /= 2          # long treks: the step of the coordinate that moved is doubled
        act[ia] = St[ia].max(axis=1) > 1e-7 * Wd.max()
    LAST.clear(); LAST['per family after polishing'] = {names[int(fid[pk[i]])]: float(fp[i]) for i in range(1, len(pk))}
    for i in range(len(pk)): LAST['per family after polishing'][names[int(fid[pk[i]])]] = min(LAST['per family after polishing'].get(names[int(fid[pk[i]])], np.inf), float(fp[i]))
    i = int(np.argmin(fp)); y = Yp[i].copy(); fy = float(fp[i]); LAST['family of the lowest walker'] = names[int(fid[pk[i]])]
    return fy, y, nev, fam, nan[0]


def describe(y, ell):
    mu = math.exp(y[0]) if y[0] > -700 else 0.0
    return {'state (log mu, log r, log B, log kappa, log(P/Pbar))': [float(v) for v in y], 'mu': mu, 'ell/4 - mu': ell / 4 - mu, 'log r + ell/2': float(y[1] + ell / 2),
            'log b + ell': float(y[2] - ell), 'log kappa': float(y[3]), 'log(r sqrt(mu)/(ell^2 sigma))': float(y[1] + 0.5 * y[0] - 2 * math.log(ell) + ell),
            'log(B/2.5e10)': float(y[2] - LBMIN), 'log(kappa sigma/b)': float(y[3] - y[2] + ell)}


def di_seeds(ell):
    """the worst states of the DI searches (five lines), with q = 0."""
    out = []
    for fn, key in (('results/di_m_%s.json' % ell, None), ('results/di_narrow.json', str(ell)), ('results/di_wide.json', str(ell))):
        if os.path.exists(fn):
            d = json.load(open(fn)); d = d.get(key) if key else d
            if d and 'state (log mu, log r, log B, log kappa)' in d: out.append(list(d['state (log mu, log r, log B, log kappa)']) + [0.0])
    return np.array(out) if out else None


def at_min(ell, y):
    """the lines at the minimiser: the option-branch, a, and the largest lines relative to the target (for the report)."""
    lb = y[2] - 2 * ell; lP = float(lPbar(ell, y[0], lb, y[3])) + y[4]
    lF, la, kb, det = J.lF_point(ell, y[None, :4], np.array([lP]), detail=True)
    T, aux = J.coeffs(ell, y[0:1], y[1:2], y[2:3], y[3:4], np.array([lP])); k = J.ALL[int(kb[0])]; g = J._gt(la[:, None], ell)[0, 0]
    tg = np.logaddexp.reduce([T[t][2][0] + g[J.TY[T[t][0]]] for t in J.TARGET]) - 0.5 * math.log(ell) - aux['lg']
    rel = {t: float(T[t][1] * np.exp(T[t][2][0] + g[J.TY[T[t][0]]] - tg)) for t in J.SHARED + J.OPT[k] if t not in J.TARGET and np.isfinite(T[t][2][0])}
    big = dict(sorted(rel.items(), key=lambda kv: -abs(kv[1]))[:10])
    return {'option-branch': k, 'log a': float(la[0]), 'log(a/sigma)': float(la[0] + ell), 'log P': lP, 'log f of each option-branch there': {kk: float(v[0]) for kk, v in det.items()},
            'the ten largest lines / target (gamma_1)': big}


def seeds_all(ell):
    """the seeds of the main search: the worst states of the DI searches (di_seeds) and the minimiser of the first version of this search (results/dj_superseded/search_v1),
    so that the final run cannot stop above an earlier one (at ell = 1e8 the rounding of log F is about 1 in (F^2 - 1) ell and the polishing stalls on it)."""
    sd = di_seeds(ell); fn = 'results/dj_superseded/search_v1/dj_main_%s.json' % ell; out = [] if sd is None else [np.atleast_2d(sd)]
    if os.path.exists(fn): out.append(np.array(json.load(open(fn))['state (log mu, log r, log B, log kappa, log(P/Pbar))'])[None, :])
    return np.vstack(out) if out else None


def run_main(save=True):
    for ell in ELLS:
        fn = 'results/dj_main_%s.json' % ell
        if os.path.exists(fn): continue
        t0 = time.time(); lF, y, nev, fam, nan = search(ell, np.random.default_rng(2026 + int(ell) % 100000), seeds=seeds_all(ell))
        lc = 0.5 * math.log1p(C_CLAIM / ell); m = float(J.margin(np.array([lF]), ell)[0])
        out = {'ell': ell, 'smallest log F_full': lF, 'smallest (F_full^2 - 1) ell': m if np.isfinite(m) else 'overflow', 'log F needed by the claim (c = 10)': lc, 'below the claim': bool(lF < lc),
               **describe(y, ell), 'at the minimiser': at_min(ell, y), 'smallest log F per family (before refinement)': fam,
               'smallest log F per family (the best walker of every family polished to convergence)': dict(LAST['per family after polishing']), 'states evaluated': int(nev), 'nan': int(nan), 'seconds': round(time.time() - t0, 1)}
        print(json.dumps(out), flush=True)
        if save: json.dump(out, open(fn, 'w'), indent=1)


def run_power(save=True, block=None):
    """the power checks of the plan, sec. 4 (resumable).  Wrong versions at ell = 55.26 and 955.8; planted dips at 165.78 and 1e5 (two sets of widths); a fresh search.
    block: None (everything, results/dj_power.json) or 'a' (ell = 55.26), 'b' (ell = 955.8), 'c' (dips and fresh searches) -> results/dj_power_<block>.json (to run side by side)."""
    fn = 'results/dj_power.json' if block is None else 'results/dj_power_%s.json' % block; out = json.load(open(fn)) if os.path.exists(fn) else {}
    def do(key, f):
        if key in out: return
        t0 = time.time(); r = f(); r['seconds'] = round(time.time() - t0, 1); out[key] = r; print(key, json.dumps(r)[:500], flush=True)
        if save: json.dump(out, open(fn, 'w'), indent=1)
    def res(ell, lF, y, nev, fam, nan):
        m = float(J.margin(np.array([lF]), ell)[0]); lc = 0.5 * math.log1p(C_CLAIM / ell)
        return {'smallest log F': lF, 'smallest (F^2 - 1) ell': m if np.isfinite(m) else ('overflow' if lF > 0 else '-inf (f <= 0: the remainder exceeds the positive lines)'),
                'below the claim': bool(lF < lc), **describe(y, ell), 'states evaluated': int(nev), 'nan': int(nan)}
    for ell in [e for e, bl in ((55.26, 'a'), (955.8, 'b')) if block in (None, bl)]:
        sd = di_seeds(ell); mk = lambda: np.random.default_rng(77 + int(ell))
        for tag in J.MAIN5:
            do('line dropped: %s, ell = %s' % (tag, ell), lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, drop=(tag,))))
        do('ceiling without (J) (the corollary of DH-1), ell = %s' % ell, lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, parts=('A', 'K', 'CM'))))
        do('ceiling without the pairs lam ~ 1, ell = %s' % ell, lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, lam1=False)))
        for o in J.ALL:
            do('one option-branch only: %s, ell = %s' % (o, ell), lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, opts=(o,))))
        do('lower end of b removed (B >= 1e4), ell = %s' % ell, lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, lBmin=math.log(1e4))))
        do('lower end of the a-range removed (a down to 4 sigma^6), ell = %s' % ell, lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, arange='low')))
        do('upper end of the a-range removed (a up to 4 r/sigma^4), ell = %s' % ell, lambda: res(ell, *search(ell, mk(), n=1500, seeds=sd, arange='high')))
    for ell in ((165.78, 1e5) if block in (None, 'c') else ()):
        R = ranges(ell); lsg = -ell; line = 2 * math.log(ell) - ell
        dips = {'corner': (np.array([math.log(ell / 4 - 9.0), -ell / 2 + 5.0, ell + 11.0, -17.0, -0.7]), np.array([0.3, 3.0, 3.0, 3.0, 1.0])),
                'narrow (below the line, b near the lower end)': (np.array([math.log(3.0), line - 0.5 * math.log(3.0) - 4.0, R[2, 0] + 13.0, -ell + 31.0, 0.0]), np.array([0.5, 3.0, 3.0, 3.0, 1.0])),
                'low mu': (np.array([-0.4 * ell, -0.3 * ell, R[2, 0] + 0.3 * (R[2, 1] - R[2, 0]), -0.5 * ell, -2.0]), np.array([0.05 * ell, 0.05 * ell, 0.05 * ell, 0.05 * ell, 2.0]))}
        for name, (c, w) in dips.items():
            for wf, wn in ((1.0, ''), (3.0, ', widths * 3')):
                def f(c=c, w=w, wf=wf):
                    lF, y, nev, fam, nan = search(ell, np.random.default_rng(31 + int(ell)), n=1500, plant=(c, w * wf, 5.0)); m = float(J.margin(np.array([lF]), ell)[0])
                    return {'planted depth': 5.0, 'widths (log mu, log r, log B, log kappa, q)': [float(v) for v in w * wf], 'found': m, 'dip found (< 5.5)': bool(m < 5.5),
                            'distance of the found state from the centre / widths': [float(v) for v in (y - c) / (w * wf)], 'family of the lowest walker': LAST['family of the lowest walker'], 'states evaluated': int(nev)}
                do('planted dip: %s%s, ell = %s' % (name, wn, ell), f)
        do('fresh search (no seeds, another seed), ell = %s' % ell, lambda: res(ell, *search(ell, np.random.default_rng(4242 + int(ell)), n=2500)))
    return out


def merge_power():
    """results/dj_power_a.json, _b.json, _c.json -> results/dj_power.json (the blocks are run side by side)."""
    out = {}
    for bl in 'abc':
        fn = 'results/dj_power_%s.json' % bl
        if os.path.exists(fn): out.update(json.load(open(fn)))
    json.dump(out, open('results/dj_power.json', 'w'), indent=1); return out


if __name__ == '__main__':
    a = sys.argv[1] if len(sys.argv) > 1 else 'main'
    if a == 'main': run_main()
    elif a == 'power': run_power(block=sys.argv[2] if len(sys.argv) > 2 else None)
    elif a == 'merge': print(len(merge_power()), 'entries')
