"""Stage DJ: EVERY LINE OF THE z-OPTIONS AT A POINT, IN LOG FORM (the pointwise function of the theorem DJ-T).  Python 3.11 grammar.

THE OBJECT.  At a state (mu, r, B = b/sigma^2, kappa), sigma = e^{-ell}, with the brightness P (G = g_s P, g_s = sqrt(r/(2 + r))) and a = a' = 4 s^2, the table's
z-options are lower bounds of  (Num - gamma sigma den)/sigma  of the form   sum_l  s_l c_l sigma^{p_l - 1} f_t(a),   f_L = a, f_S = sqrt(a), f_C = 1, f_M = 1/sqrt(a),
f_H = 1/(a + sigma)   (dg_tm.z_lines / dg_tm.TYPEINFO: in the variable A, a = 4 r A/sigma, a line is c (4r)^k sigma^{p + dp - 1} A^d).  This module writes every
line of dg_tm.z_lines again, directly in logarithms (no long double, no box), so that it can be evaluated at any ell (1e8 and beyond) and at any mu > 0.
The coefficients are compared with dg_tm.z_lines on zero-width boxes, line by line, in dj_checks.py (they must agree to rounding).
  The shared lines (24):  P1 P2z P3z | d1 d2 d3 d4 (the target, with gamma) | N1 N2 N3 N4 N4G ring2 M0Xi A1v A1w A2k A2a A2b B1w1 B1w2 B2a B2b pair.
  Option Fz:   P4z, hneg1, FzK.
  Option Tz:   P4z, hneg1, hFz, cKz (bracket brk > 0) and the branch B2 (B2c, B2s) or the branch B1 (B1m, B1c, B1l, uB2c, uB2s).
  Option Bz:   as Tz with the loss lossK (bracket <= 0) in place of the gain cKz.
THE TARGET.  gamma = Gam_c = sqrt((1 + c/ell)/ell) (c = 10: the theorem), or the table's (1 + 2.5e-4)/sqrt(ell) (gam='table': for the comparison with dg_tm).
THE POINT FUNCTION.  For an option-branch k:   f_k(a) = (positive lines - remainder lines)/(target lines with gamma_1 = 1/sqrt(ell)),   and
    F_full = min over a in [4 sigma^2, 4 r/sigma] of max_k f_k(a).        The claim of DJ-T:  (F_full^2 - 1) ell >= 10  (i.e. S* >= 0 with Gam_10).
Every option-branch is a lower bound of the same quantity at the true (a, P), so the maximum over k may be taken at every a (no endpoint rule is needed at a point).
Per option-branch the lines are added up per type (five coefficients for each of: positive, remainder, target), so f_k(a) costs 15 exponentials.
THE MINIMUM OVER a.  Candidates: the crossings of every pair of the type-monomials of every option-branch (the kinks of the tropical form), a uniform grid, the
point a = sigma; then two local refinements around the best candidate.  Compared with a dense grid in dj_checks.py.
log f is returned (never converted where it could overflow); a state where the remainder exceeds the positive lines has log f = -inf (f <= 0)."""
import math, os
import numpy as np
N4OLD = os.environ.get('CZ_N4OLD', '0') != '0'                     # DL: True = the line N4 as it was up to DK (without the eta k_E r/(1+r) part of J_up)

QB = 0.25; M4Z = 2.07; C2Z = 0.184
TY = {'L': 0, 'S': 1, 'C': 2, 'M': 3, 'H': 4}
SLOPE = np.array([1.0, 0.5, 0.0, -0.5, -1.0])
SHARED = ('P1', 'P2z', 'P3z', 'd1', 'd2', 'd3', 'd4', 'N1', 'N2', 'N3', 'N4', 'N4G', 'ring2', 'M0Xi', 'A1v', 'A1w', 'A2k', 'A2a', 'A2b', 'B1w1', 'B1w2', 'B2a', 'B2b', 'pair')
OPT = {'Fz': ('P4z', 'hneg1', 'FzK'),
       'TzB2': ('P4z', 'hneg1', 'hFz', 'cKz', 'B2c', 'B2s'),
       'TzB1': ('P4z', 'hneg1', 'hFz', 'cKz', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s'),
       'BzB2': ('P4z', 'hneg1', 'hFz', 'lossK', 'B2c', 'B2s'),
       'BzB1': ('P4z', 'hneg1', 'hFz', 'lossK', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')}
OPT['XB2'] = ('P4z', 'hneg1', 'hFz', 'cKz', 'lossK', 'B2c', 'B2s')                      # Tz where brk > 0 (cKz; lossK = 0 there), Bz where brk <= 0 (lossK; cKz absent):
OPT['XB1'] = ('P4z', 'hneg1', 'hFz', 'cKz', 'lossK', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')   # where brk > 0, Tz >= Bz (cKz >= 0), so X = the better allowed one of Tz, Bz
ALL = ('Fz', 'XB2', 'XB1')
FIVE = ('Fz', 'TzB2', 'TzB1', 'BzB2', 'BzB1')
TARGET = ('d1', 'd2', 'd3', 'd4')
MAIN5 = ('P1', 'P2z', 'hFz', 'P4z', 'cKz')


def lgam_c(ell, c=10.0):
    return 0.5 * (math.log1p(c / ell) - math.log(ell))


def coeffs(ell, lmu, lr, lB, lk, lP, gam=1.0, eta=None):
    """every line at the states: tag -> (type, sign, L) with L = log(c sigma^{p-1}) (arrays).  gam: the factor of the target lines is exp(lg) with
    lg = log(gam/sqrt(ell)) for a number gam, or the table's (1 + 2.5e-4)/sqrt(ell) for gam = 'table'.  (The role of a line -- positive, remainder, target -- is
    read from its sign and its tag.)  Also the brackets: aux['brk'] (Tz allowed where > 0)."""
    lmu, lr, lB, lk, lP = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lr, lB, lk, lP))
    with np.errstate(all='ignore'):
        eta = 1.0 / ell if eta is None else float(eta); opeta = 1 + eta;          # DX: eta (the ripple) separated; None: eta = 1/ell
        opeta = 1 + eta; ometa = 1 - eta; lfl = -math.log(opeta); lom = math.log(ometa); ls = -ell
        r = np.exp(lr); l1pr = np.log1p(r); l2pr = np.log(2 + r); lkE = 0.5 * (lr - l1pr); kE = np.exp(lkE); lgs = 0.5 * (lr - l2pr)
        two_l = 2 * ell + 3.1; U1 = QB * math.sqrt(two_l) + 1e-6; X1 = U1 / (1 - QB); CZ = eta ** 2 / (math.e * ometa ** 2); X1CZ = X1 ** 2 + CZ
        lg = math.log(1 + 2.5e-4) - 0.5 * math.log(ell) if isinstance(gam, str) else math.log(gam) - 0.5 * math.log(ell)
        lb = lB - 2 * ell; b = np.exp(lb); omb = 1 - b; yh = np.exp(-math.log(2) - lB); w0 = np.exp(math.log(0.75) - lB); opw0 = 1 + w0
        Kz2 = 8 * ell + 100; Kz = math.sqrt(Kz2); TKc = 0.8 * math.exp(-50.0) * (Kz + 1)
        ringf = 1 - np.exp(math.log(Kz2 * opeta / (8 * ometa)) - lB)
        lG = lP + lgs; lcap = math.log(2 * QB ** 2) + 1e-6 + lgs; lGmu = np.minimum(lG - lmu, lcap); Gmu = np.exp(lGmu)
        M4c = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2; lM4g = math.log(1.5) + lGmu - 2 * l2pr - lom; M4g = np.exp(lM4g)
        z2 = Kz2 * yh; brk = 1 - (4 * b / omb + z2 / 12); negbrk = -brk
        lfF = lG - math.log(4) - lom; lfFs = lfF + 0.5 * (lk - math.log(2) - lB)
        lcs = np.logaddexp(0.5 * math.log(CZ / 2), lr - 0.5 * math.log(math.pi) - 0.5 * l2pr)
        T = {}
        def add(tag, t, p, s, lc): T[tag] = (t, s, lc + (p - 1) * ls)
        add('P1', 'L', 1, +1, np.full(lmu.shape, math.log(0.5)))
        add('P2z', 'L', 1, +1, np.log(ringf) + lfl + lG - lmu - l2pr - math.log(4) - lr)
        add('P3z', 'C', 2, +1, math.log(3 / 8) + 2 * np.log(omb) - np.log(opw0))
        add('d1', 'C', 3, -1, lg + lB + np.log1p((eta + 0.184) * kE))
        add('d2', 'C', 1, -1, lg + lG - math.log(2) - lom)
        add('d3', 'L', 2, -1, lg + np.log((1 + 2 * eta * kE) / 4))
        add('d4', 'L', 2, -1, lg + lGmu - math.log(2) - lom - l2pr - math.log(4) - lr)
        add('N1', 'L', 1, -1, math.log(eta) + lkE + l2pr - math.log(2) - l1pr)
        add('N2', 'L', 1, -1, np.log(1 + eta * kE * r / (1 + r) + 2 * eta * kE / (1 + r)) - math.log(16) - lB)
        add('N3', 'C', 2, -1, np.log((M4c + M4g) / 2))
        add('N4', 'L', 3, -1, math.log(1.5 / 4) + np.log(X1CZ * (1 + (0.0 if N4OLD else eta * kE * r / (1 + r)) + 2 * eta * kE / (1 + r)) + r * M4c))
        add('N4G', 'L', 3, -1, math.log(1.5) + np.logaddexp(math.log(X1CZ) + lGmu - math.log(2) - lom - l2pr, 2 * lr + lM4g) - math.log(4) - lr)
        add('ring2', 'L', 5, -1, 2 * math.log(eta) + lgs + math.log(TKc) - math.log(4) - lB - l2pr - lom - math.log(4) - lr)
        add('M0Xi', 'C', 2, -1, math.log(0.25 * QB * M4Z) + lkE)
        add('A1v', 'C', 3, -1, 0.5 * (math.log(7.5) + lB) + lkE + 0.5 * lP - math.log(4))
        add('A1w', 'S', 3.5, -1, lB + math.log(opeta) - math.log(4 * math.sqrt(math.pi)))
        add('A2k', 'C', 4, -1, lB + lk + lG - math.log(8) - lom)
        add('A2a', 'L', 5, -1, lB + np.log(1 + eta * kE * r / (1 + r)) - math.log(8))
        add('A2b', 'L', 5, -1, lB + 2 * math.log(eta) + lgs - l2pr - lom - math.log(8) - lr)
        add('B1w1', 'S', 3.5, -1, lB + np.log(C2Z + yh) + lr - l1pr - math.log(2 * math.sqrt(math.pi)))
        add('B1w2', 'S', 3.5, -1, lB + 2 * math.log(eta) + np.log1p(yh / 2) - math.log(2 * math.sqrt(math.pi)) - l2pr - lom)
        add('B2a', 'C', 3, -1, 0.5 * lB + math.log(U1) + 0.5 * lk + lG - math.log(4) - 2 * lom)
        add('B2b', 'L', 4, -1, 0.5 * (math.log(2) + lB) + 0.5 * lP - math.log(8) + np.logaddexp(lkE + lr - l1pr, 2 * math.log(eta) - 0.5 * (lr + l2pr) - l2pr - 2 * lom))
        add('pair', 'C', 4, -1, 2 * math.log(U1) + lgs + math.log(Kz + 5) + math.log(0.4) - 50.0 - lom)
        add('P4z', 'H', 3, +1, lB - math.log(2) - 2 * np.log(opw0))
        add('hneg1', 'H', 3, -1, lB + lkE + math.log(eta + 0.184))
        add('hFz', 'H', 1, +1, lfl + lG - math.log(4) + lr - l2pr + np.log(1 - z2 / 2))
        add('cKz', 'C', 0, +1, np.where(brk > 0, lfl + lG - math.log(4) + 2 * np.log(omb) + lk - math.log(4) - lB + np.log(np.where(brk > 0, brk, 1.0)), -np.inf))
        add('lossK', 'C', 0, -1, np.where(negbrk > 0, lk + lG - math.log(16) - lB - lom + np.log(np.where(negbrk > 0, negbrk, 1.0)), -np.inf))
        add('B2c', 'C', 1, -1, lfF + math.log(X1) - 0.5 * math.log(2))
        add('B2s', 'S', 1.5, -1, lfF + lcs - 0.5 * (math.log(4) + lr))
        add('B1m', 'M', 1.5, -1, lfF + math.log(X1) - 0.5 * math.log(2) - 0.5 * math.log(math.pi) - 0.5 * l2pr + 0.5 * (math.log(4) + lr))
        add('B1c', 'C', 2, -1, lfF + np.log(np.sqrt(CZ / (2 * math.pi * (2 + r))) + r / (2 * (2 + r)) + X1CZ))
        add('B1l', 'L', 3, -1, lfF + lr - math.log(8) - l2pr)
        add('uB2c', 'C', 1, -1, lfFs + math.log(X1) - 0.5 * math.log(2))
        add('uB2s', 'S', 1.5, -1, lfFs + lcs - 0.5 * (math.log(4) + lr))
        add('FzK', 'C', 2, -1, lk + lG - math.log(4) - lom)
    aux = {'brk': brk, 'lG': lG, 'lgs': lgs, 'lb': lb, 'lg': lg}
    return T, aux


def aggregate(T, aux, opts=ALL, drop=(), only=None):
    """per option-branch: (pos, rem, tgt), each (n, 5): the log of the sum of the coefficients of each type (L, S, C, M, H).  drop: tags left out (wrong
    versions); only: if given, the remainder is restricted to these tags (the measurement of single lines).  An option that is not allowed at a state (Tz with
    brk <= 0) gets pos = -inf there."""
    n = len(aux['lG']); out = {}
    for k in opts:
        pos = np.full((n, 5), -np.inf); rem = np.full((n, 5), -np.inf); tgt = np.full((n, 5), -np.inf)
        for tag in SHARED + OPT[k]:
            if tag in drop: continue
            t, s, L = T[tag]; j = TY[t]
            if tag in TARGET: tgt[:, j] = np.logaddexp(tgt[:, j], L)
            elif s > 0: pos[:, j] = np.logaddexp(pos[:, j], L)
            elif only is None or tag in only: rem[:, j] = np.logaddexp(rem[:, j], L)
        if k.startswith('Tz'): pos[aux['brk'] <= 0] = -np.inf
        out[k] = (pos, rem, tgt)
    return out


def _gt(lA, ell):
    """the logs of the five type functions on lA (n, g) -> (n, g, 5)."""
    return np.stack([lA, 0.5 * lA, np.zeros_like(lA), -0.5 * lA, -np.logaddexp(lA, -ell)], axis=-1)


def _lse(c, g):
    """log sum_t exp(c[:, None, t] + g[:, :, t])."""
    x = c[:, None, :] + g; m = np.max(x, axis=-1); m0 = np.where(np.isfinite(m), m, 0.0)
    with np.errstate(all='ignore'): return m0 + np.log(np.sum(np.exp(x - m0[..., None]), axis=-1))


def lf_on(agg, lA, ell, lg1):
    """log f_k on the grid lA (n, g) for every option-branch: dict k -> (n, g).  f = (pos - rem)/(tgt with gamma_1 = 1/sqrt(ell)); the target lines were built
    with exp(aux['lg']), so log tgt is shifted by lg1 = -0.5 log(ell) - aux['lg']."""
    g = _gt(lA, ell); out = {}
    with np.errstate(all='ignore'):
        for k, (pos, rem, tgt) in agg.items():
            lp = _lse(pos, g); lr_ = _lse(rem, g); lt = _lse(tgt, g) + lg1; d = lr_ - lp
            out[k] = np.where(d < 0, lp - lt + np.log(-np.expm1(np.minimum(d, 0.0))), -np.inf)
    return out


def a_range(ell, lr, arange='class'):
    lo = np.full(lr.shape, math.log(4) - 2 * ell); hi = math.log(4) + lr + ell
    if arange == 'low': lo = lo - 4 * ell
    if arange == 'high': hi = hi + 3 * ell
    return lo, hi


def _candidates(agg, ell, lo, hi, ngrid=48):
    """the candidate points of a (n, m): crossings of the type-monomials of each option-branch, a uniform grid, a = sigma, the ends; with offsets."""
    n = len(lo); cs = [lo[:, None], hi[:, None], np.full((n, 1), -ell), lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, ngrid)[None, :]]
    sl = np.concatenate([SLOPE, [0.0]])                                              # H as slope -1 (a >> sigma) and as slope 0 with intercept + ell (a << sigma)
    with np.errstate(all='ignore'):
        for k, (pos, rem, tgt) in agg.items():
            neg = np.logaddexp(rem, tgt)
            allc = np.concatenate([pos, pos[:, 4:5] + ell, neg, neg[:, 4:5] + ell], axis=1); sl2 = np.concatenate([sl, sl])
            i, j = np.triu_indices(12, 1); ds = sl2[j] - sl2[i]; ok = ds != 0
            t = (allc[:, i[ok]] - allc[:, j[ok]]) / ds[ok][None, :]
            cs.append(np.where(np.isfinite(t), t, lo[:, None]))
    base = np.concatenate(cs, axis=1)
    pts = np.concatenate([base + o for o in (-1.0, 0.0, 1.0)], axis=1)
    return np.clip(pts, lo[:, None], hi[:, None])


def lF_point(ell, Y, lP, gam=1.0, opts=ALL, drop=(), arange='class', detail=False, chunk=1500, ab=None):
    """log F_full at the states Y (n, 4) = (log mu, log r, log B, log kappa) with the brightness lP (n,):  min over a of max over the option-branches of log f_k.
    ab = (lo, hi): arrays restricting a to [lo, hi] (inside the range of arange).
    Returns (lF, la, kbest) -- kbest the index (in opts) of the best option-branch at the minimising a; with detail also the dict of log f_k there."""
    Y = np.atleast_2d(np.asarray(Y, float)); lP = np.broadcast_to(np.asarray(lP, float), (len(Y),)).copy(); n = len(Y)
    lF = np.empty(n); la = np.empty(n); kb = np.empty(n, int); det = {k: np.empty(n) for k in opts}
    for s in range(0, n, chunk):
        sl = slice(s, min(s + chunk, n)); y = Y[sl]
        T, aux = coeffs(ell, y[:, 0], y[:, 1], y[:, 2], y[:, 3], lP[sl], gam=gam); agg = aggregate(T, aux, opts, drop)
        lg1 = -0.5 * math.log(ell) - aux['lg']; lo, hi = a_range(ell, y[:, 1], arange)
        if ab is not None: lo, hi = np.maximum(lo, ab[0][sl]), np.minimum(hi, ab[1][sl])        # a sub-range of a (the rule of the proof)
        pts = _candidates(agg, ell, lo, hi)
        def best(pts):
            f = lf_on(agg, pts, ell, lg1); m = np.max(np.stack([f[k] for k in opts], axis=0), axis=0); m = np.where(np.isnan(m), -np.inf, m)
            i = np.argmin(m, axis=1); return m[np.arange(len(m)), i], pts[np.arange(len(m)), i]
        v, a = best(pts)
        for w in (1.0, 0.05, 0.0025, 1.25e-4):
            loc = np.clip(a[:, None] + np.linspace(-w, w, 41)[None, :], lo[:, None], hi[:, None]); v2, a2 = best(loc); b = v2 < v; v = np.where(b, v2, v); a = np.where(b, a2, a)
        f = lf_on(agg, a[:, None], ell, lg1); st = np.stack([f[k][:, 0] for k in opts], axis=0); st = np.where(np.isnan(st), -np.inf, st)
        lF[sl] = v; la[sl] = a; kb[sl] = np.argmax(st, axis=0)
        for i, k in enumerate(opts): det[k][sl] = st[i]
    return (lF, la, kb, det) if detail else (lF, la, kb)


def margin(lF, ell):
    """(F^2 - 1) ell from log F (inf where it overflows -- use log F itself for anything large)."""
    with np.errstate(all='ignore'): return np.where(lF < 300, np.expm1(2 * np.minimum(lF, 300.0)) * ell, np.inf)
