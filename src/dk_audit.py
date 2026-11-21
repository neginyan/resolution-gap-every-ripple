"""Stage DK 2.1: THE AUDIT OF RING 2 OVER THE WHOLE RANGE OF THEOREM DJ-T.  Python 3.11 grammar.  [numerical; the comparisons are in decimal]
(L)  LINE BY LINE: at states of the class (ell in ELLS up to 1e12; mu in [e^{-3 ell}, 8 ell + 80]; kappa in [e^{-2.2 ell - 50}, e^{3 ell}]; r in [sigma^3, 1/4];
     B in [max(2.5e10, 50(8 ell + 100)), 0.49/sigma^2]; P = (mu/8) e^{-q}, q in [0, 4 ell], and P at the ceiling of (H') for the corner family) and on a grid
     of a in [4 sigma^2, 4 r/sigma] (built in decimal: the ends exactly), every group of table lines (dk_table) against the lemma's piece (dk_lemma):
     gains table/lemma <= 1 + 1e-30, losses and den table/lemma >= 1 - 1e-30.  A lemma piece or a table line that vanishes (underflow) or an exception is a failure.
(S)  TOTALS: for every option-branch k (Fz; Tz-B2, Tz-B1 where brk > 0; Bz-B2, Bz-B1): Lambda_k(a) <= Phi_k(a)/sigma + 1e-30 scale, gamma = Gamma.
(I)  IDENTITY: the pieces of the lemma assembled per option equal the cz_point form of Phi_k (assembled independently in dk_lemma.pieces): <= 1e-40 scale.
(R)  RANGE CONDITIONS of the lemmas at every state (dk_lemma.ranges_ok).
(P)  PRECISION SELF-CHECK: a subsample recomputed with 40 more digits; every piece and line agrees to 1e-45 (relative).
(T2) TRANSCRIPTION: dk_table (decimal) against dj_lines.coeffs and dg_tm.z_lines (floats), log(c sigma^{p-1}) relative to 1 + |L|: <= 1e-13; type and sign equal.
(X)  CROSS-CHECK where the earlier 50-digit codes can be evaluated (ell <= 960.8, mu >= 1e-3, ...): dk_lemma against cz_point.point, cz_point.lemma_lines and
     da_linecheck.lemma_pieces with the same decimal inputs: <= 1e-40 scale.
POWER: the wrong versions of dk_table.WRONG must each be caught by (L)/(S) (counted per ell); the wrong versions of dj_lines by (T2); the precision versions
dk_lemma.NAIVE['range'] (the default exponent range) must be caught as vanished pieces or exceptions at large ell.
-> results/dk_audit.json (run), results/dk_power.json (power)"""
import json, math, os, sys, time, types
from decimal import Decimal as Dc, localcontext
import numpy as np
import dk_lemma as K, dk_table as T
ELLS = (55.26, 60.0, 165.78, 955.8, 2000.0, 1e4, 5e4, 1e5, 1e6, 1e8, 1e10, 1e12)
TOL = Dc('1e-30')
GROUPS = [  # name, table tags, kind, lemma piece (function of the lemma's dict)
    ('P1', ('P1',), 'gain', lambda o: o['P1']), ('P2z', ('P2z',), 'gain', lambda o: o['P2'] - o['ring1']),
    ('P3z+P4z (M0: b Psi0)', ('P3z', 'P4z'), 'gain', lambda o: o['M0 b Psi0']), ('hFz', ('hFz',), 'gain', lambda o: o['hF']),
    ('cKz (chirp)', ('cKz',), 'gain', lambda o: o['chirp']),
    ('N1', ('N1',), 'loss', lambda o: o['N1']), ('N2', ('N2',), 'loss', lambda o: o['N2']), ('ring2', ('ring2',), 'loss', lambda o: o['ring2']),
    ('N3', ('N3',), 'loss', lambda o: o['N3']), ('N4+N4G', ('N4', 'N4G'), 'loss', lambda o: o['N4']),
    ('hneg1 (M0: R_theta, t_rho)', ('hneg1',), 'loss', lambda o: o['M0 R_theta, t_rho']), ('M0Xi', ('M0Xi',), 'loss', lambda o: o['M0 Xi']),
    ('A1v', ('A1v',), 'loss', lambda o: o['A1v']), ('A1w', ('A1w',), 'loss', lambda o: o['A1w']), ('A2k', ('A2k',), 'loss', lambda o: o['A2k']),
    ('A2a', ('A2a',), 'loss', lambda o: o['A2a']), ('A2b', ('A2b',), 'loss', lambda o: o['A2b']), ('B1w1', ('B1w1',), 'loss', lambda o: o['B1w1']),
    ('B1w2', ('B1w2',), 'loss', lambda o: o['B1w2']), ('B2a', ('B2a',), 'loss', lambda o: o['B2a']), ('B2b', ('B2b',), 'loss', lambda o: o['B2b']),
    ('pair (tails)', ('pair',), 'loss', lambda o: o['tails'] + o['chirp tail']), ('FzK', ('FzK',), 'loss', lambda o: o['FzK']),
    ('lossK', ('lossK',), 'loss', lambda o: o['lossK']),
    ('B2c+B2s (FrB2)', ('B2c', 'B2s'), 'loss', lambda o: o['FrB2']), ('B1m+B1c+B1l+uB2c+uB2s (FrB1)', ('B1m', 'B1c', 'B1l', 'uB2c', 'uB2s'), 'loss', lambda o: o['FrB1']),
    ('d1', ('d1',), 'den', lambda o: o['den d1']), ('d2', ('d2',), 'den', lambda o: o['den d2']), ('d3', ('d3',), 'den', lambda o: o['den d3']),
    ('d4', ('d4',), 'den', lambda o: o['den d4'])]
MUST_POS = ('P1', 'P2', 'ring1', 'ring2', 'N1', 'N2', 'N3', 'N4', 'M0 b Psi0', 'M0 R_theta, t_rho', 'M0 Xi', 'A1v', 'A1w', 'A2k', 'A2a', 'A2b', 'B1w1', 'B1w2',
            'B2a', 'B2b', 'FzK', 'hF', 'tails', 'FrB2', 'FrB1', 'den d1', 'den d2', 'den d3', 'den d4')


def ranges(ell):
    lBmin = math.log(max(2.5e10, 50 * (8 * ell + 100)))
    return np.array([[-3 * ell, math.log(8 * ell + 80)], [-3 * ell, math.log(0.25)], [lBmin, math.log(0.5) + 2 * ell], [-2.2 * ell - 50, 3 * ell], [0.0, 4 * ell]])


def sample(ell, rng, n):
    """states (lmu, lr, lB, lk, lP) and family names."""
    R = ranges(ell); out = []; fam = []
    def U(m): return R[:, 0] + (R[:, 1] - R[:, 0]) * rng.uniform(size=(m, 5))
    nu = (3 * n) // 5; Y = U(nu); fam += ['uniform'] * nu; out.append(Y)
    ne = n // 5; Y = U(ne); j = rng.integers(0, 5, ne); e = rng.integers(0, 2, ne); Y[np.arange(ne), j] = R[j, e]; out.append(Y); fam += ['ends'] * ne
    nc = n // 14; Y = np.zeros((nc, 5)); mu = np.maximum(ell / 4 - rng.uniform(0, 15, nc), 1.0)
    Y[:, 0] = np.log(mu); Y[:, 1] = np.clip(-ell / 2 + rng.uniform(-10, 10, nc), R[1, 0], R[1, 1]); Y[:, 2] = np.clip(ell + rng.uniform(-20, 20, nc), R[2, 0], R[2, 1])
    lb = Y[:, 2] - 2 * ell; Y[:, 3] = np.clip(math.log(16) + lb + mu - np.log(mu) + rng.uniform(-10, 10, nc), R[3, 0], R[3, 1]); Y[:, 4] = rng.uniform(0, 3, nc)
    out.append(Y); fam += ['corner'] * nc
    nk = n // 10; Y = U(nk); e2 = rng.integers(0, 3, (nk, 5)); Y = np.where(e2 == 0, R[:, 0][None, :], np.where(e2 == 1, R[:, 1][None, :], Y)); out.append(Y); fam += ['corners (several ends)'] * nk
    nb = n - nu - ne - nc - nk; Y = U(nb); Y[:, 2] = 2 * ell + np.log(rng.uniform(0.15, 0.5, nb)); out.append(Y); fam += ['large b (brk <= 0)'] * nb
    Y = np.vstack(out); lP = Y[:, 0] - math.log(8) - Y[:, 4]
    # the corner family at the ceiling of (H') (where it is below mu/8)
    ic = [i for i, f in enumerate(fam) if f == 'corner']
    if ic:
        try:
            import dj_search as S
            lPb = S.lPbar(ell, Y[ic, 0], Y[ic, 2] - 2 * ell, Y[ic, 3]); lP[ic] = np.minimum(lPb, Y[ic, 0] - math.log(8))
        except Exception:
            pass
    # P relative to mu in decimal (P = (mu/8) e^{-q} exactly: in floats, log P of size ell carries a rounding of 1e-16 ell, which at ell = 1e12 puts P above mu/8,
    # outside the class); the end r = 1/4 exactly (log 0.25 as a float gives r = 1/4 (1 + 5e-17)).
    out_ = []
    with localcontext(K.context(ell, 20)):
        l8 = Dc(8).ln(); lq = Dc(4).ln()
        for i in range(len(Y)):
            lmu = K.D(float(Y[i, 0])); top = lmu - l8
            lPi = top - K.D(float(Y[i, 4])) if fam[i] != 'corner' else min(K.D(float(lP[i])), top)
            lri = -lq if float(Y[i, 1]) == float(R[1, 1]) else float(Y[i, 1])
            # the ends of mu (8 ell + 80) and of B (max(2.5e10, 50 (8 ell + 100)) and b = 1/2) exactly, in decimal
            lmui = (8 * K.D(ell) + 80).ln() if float(Y[i, 0]) == float(R[0, 1]) else float(Y[i, 0])
            if float(Y[i, 0]) == float(R[0, 1]): lPi = (lmui - l8 - K.D(float(Y[i, 4]))) if fam[i] != 'corner' else min(K.D(float(lP[i])), lmui - l8)
            if float(Y[i, 2]) == float(R[2, 1]): lBi = Dc('0.5').ln() + 2 * K.D(ell)
            elif float(Y[i, 2]) == float(R[2, 0]): lBi = max(Dc('2.5e10'), 50 * (8 * K.D(ell) + 100)).ln()
            else: lBi = float(Y[i, 2])
            out_.append((lmui if isinstance(lmui, float) else +lmui, lri, lBi if isinstance(lBi, float) else +lBi, float(Y[i, 3]), +lPi))
    return out_, fam


def a_grid(ell, lr, lB, c, m=25, rng=None):
    """Decimal logs of a in [4 sigma^2, 4 r/sigma]: the two ends exactly, a = sigma, a = sqrt(b), a = 4 sigma, interior points."""
    with localcontext(c):
        lo = Dc(4).ln() - 2 * K.D(ell); hi = Dc(4).ln() + K.D(lr) + K.D(ell)
        pts = [lo, hi, -K.D(ell), (K.D(lB) - 2 * K.D(ell)) / 2, Dc(4).ln() - K.D(ell)]
        fr = np.linspace(0, 1, m - len(pts) + 2)[1:-1] if rng is None else np.sort(rng.uniform(size=m - len(pts)))
        pts += [lo + (hi - lo) * K.D(float(f)) for f in fr]
        return [p for p in pts if lo <= p <= hi]


def gamma(ell, c):
    with localcontext(c): return ((1 + 10 / K.D(ell)) / K.D(ell)).sqrt()


def prepare(ell, st, c, gam):
    q = K.state(ell, *st, c); q['gam'] = gam; TT, brk = T.lines(q, c, gam)
    return q, TT, brk


def eval_point(ell, st, la, c, gam, pre=None):
    """one (state, a): group ratios, totals, identity.  Returns a dict."""
    q, TT, brk = pre if pre is not None else prepare(ell, st, c, gam)
    o, tot, alt, scale = K.pieces(q, la, c)
    with localcontext(c):
        sig = q['sig']; V = {k: T.value(TT, k, la, sig, c) for k in TT}
        res = {'groups': {}, 'tot': {}, 'vanished': [], 'brk>0': brk > 0, 'cd>0': q['cd'] > 0}
        for k in MUST_POS:
            if not o[k] > 0: res['vanished'].append('lemma ' + k)
        for k in T.ALL_TAGS:
            if k in ('cKz', 'lossK'): continue
            if V[k] == 0: res['vanished'].append('table ' + k)
        for name, tags, kind, f in GROUPS:
            l = f(o) * (q['gam'] if kind == 'den' else 1); t = sum(V[k] for k in tags)
            if kind != 'gain': t = -t
            if l == 0:
                res['groups'][name] = (None, t == 0 or kind != 'gain')        # lemma piece 0 (chirp with cd <= 0, lossK with cd >= 0): a gain must be 0 too
                continue
            rt = t / l; ok = (rt <= 1 + TOL) if kind == 'gain' else (rt >= 1 - TOL)
            res['groups'][name] = (rt, ok)
        for k, tags in T.OPT.items():
            if k.startswith('Tz') and not brk > 0: continue
            if k not in tot: res['tot'][k] = (None, False); continue           # brk > 0 but the lemma's Tz does not exist: impossible (brk <= 2 c_delta)
            lam = sum(V[t] for t in T.SHARED + tags)
            d = (tot[k] - lam) / scale; res['tot'][k] = (d, d >= -TOL)
        res['identity'] = max(abs((tot[k] - alt[k]) / scale) for k in tot)
        rg = K.ranges_ok(q, la, c); res['ranges'] = rg
    return res, o, V


def audit_ell(ell, n=1500, m=25, seed=0, nprec=60):
    t0 = time.time(); rng = np.random.default_rng(seed + int(ell) % 100000)
    states, fam = sample(ell, rng, n); c = K.context(ell); gam = gamma(ell, c)
    G = {nm: {'min': None, 'max': None, 'count': 0, 'lemma zero': 0, 'violations': []} for nm, *_ in GROUPS}
    S = {k: {'min (Phi - Lambda)/scale': None, 'count': 0, 'violations': []} for k in T.OPT}
    ident = Dc(0); van = []; exc = []; rgfail = {}; npts = 0; prec_worst = Dc(0); nprec_done = 0; brk_pos = 0; brk_cd = 0
    for i, st in enumerate(states):
        try:
            las = a_grid(ell, st[1], st[2], c, m); pre = prepare(ell, st, c, gam)
            for j, la in enumerate(las):
                res, o, V = eval_point(ell, st, la, c, gam, pre); npts += 1
                brk_pos += res['brk>0']; brk_cd += (res['brk>0'] and not res['cd>0'])
                if res['vanished']: van.append({'state': [str(v)[:40] for v in st], 'family': fam[i], 'la': str(la)[:30], 'what': res['vanished'][:6]})
                for nm, (rt, ok) in res['groups'].items():
                    g = G[nm]
                    if rt is None: g['lemma zero'] += 1
                    else:
                        g['count'] += 1; g['min'] = rt if g['min'] is None or rt < g['min'] else g['min']; g['max'] = rt if g['max'] is None or rt > g['max'] else g['max']
                    if not ok: g['violations'].append({'state': [str(v)[:40] for v in st], 'family': fam[i], 'la': str(la)[:40], 'ratio': str(rt)[:40]})
                for k, (d, ok) in res['tot'].items():
                    s = S[k]; s['count'] += 1
                    if d is not None: s['min (Phi - Lambda)/scale'] = d if s['min (Phi - Lambda)/scale'] is None or d < s['min (Phi - Lambda)/scale'] else s['min (Phi - Lambda)/scale']
                    if not ok: s['violations'].append({'state': [str(v)[:40] for v in st], 'family': fam[i], 'la': str(la)[:40], 'diff': str(d)[:40]})
                ident = max(ident, res['identity'])
                for kk, v in res['ranges'].items():
                    if not v: rgfail[kk] = rgfail.get(kk, 0) + 1
                if i % max(1, n // nprec) == 0 and j in (0, 2, len(las) - 1):                        # precision self-check
                    c2 = K.context(ell, 40); g2 = gamma(ell, c2)
                    res2, o2, V2 = eval_point(ell, st, la, c2, g2)
                    with localcontext(c2):
                        for dd, ee in ((o, o2), (V, V2)):
                            for k in dd:
                                x, y = dd[k], ee[k]
                                if y != 0: prec_worst = max(prec_worst, abs((x - y) / y))
                                elif x != 0: prec_worst = max(prec_worst, Dc(1))
                    nprec_done += 1
        except Exception as e:
            exc.append({'state': [str(v)[:40] for v in st], 'family': fam[i], 'error': repr(e)[:200]})
    f = lambda x: None if x is None else (float(x) if math.isfinite(float(x)) and (float(x) != 0 or x == 0) else str(x)[:24])
    out = {'ell': ell, 'states': len(states), 'points (state, a)': npts, 'decimal digits': c.prec, 'families': {k: fam.count(k) for k in dict.fromkeys(fam)},
           'groups': {nm: {'min ratio': f(g['min']), 'max ratio': f(g['max']), 'comparisons': g['count'], 'lemma piece 0': g['lemma zero'], 'violations': g['violations'][:5],
                           'number of violations': len(g['violations'])} for nm, g in G.items()},
           'totals': {k: {'min (Phi - Lambda)/scale': f(s['min (Phi - Lambda)/scale']), 'comparisons': s['count'], 'violations': s['violations'][:5], 'number of violations': len(s['violations'])} for k, s in S.items()},
           'identity: largest |assembled - cz_point form|/scale': f(ident), 'vanished (underflow)': van[:5], 'number vanished': len(van), 'exceptions': exc[:5], 'number of exceptions': len(exc),
           'range conditions that fail (count of points)': rgfail, 'precision self-check: largest relative difference (40 more digits)': f(prec_worst), 'precision self-check points': nprec_done,
           'points with brk > 0': brk_pos, 'points with brk > 0 but c_delta <= 0 (must be 0)': brk_cd, 'seconds': time.time() - t0}
    out['ok'] = bool(all(v['number of violations'] == 0 for v in out['groups'].values()) and all(v['number of violations'] == 0 for v in out['totals'].values())
                     and out['number vanished'] == 0 and out['number of exceptions'] == 0 and not rgfail and prec_worst < Dc('1e-45') and ident < Dc('1e-40') and brk_cd == 0)
    return out


# ------------------------------------------------------------------ (T2) the float codes
def transcription(ell, n=400, seed=1, dj=None):
    """dk_table against dj_lines.coeffs (gamma = Gamma) and dg_tm.z_lines (gamma of the table)."""
    import dj_lines as J0
    J = dj if dj is not None else J0
    rng = np.random.default_rng(seed + int(ell) % 100000); states, fam = sample(ell, rng, n); c = K.context(ell)
    states = [tuple(float(v) for v in st) for st in states]; Y = np.array(states); out = {}
    with np.errstate(all='ignore'):
        Tm, aux = J.coeffs(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3], Y[:, 4], gam=math.sqrt(1 + 10 / ell))
    worst = 0.0; bad = {}; nmis = 0
    gtab = None
    try:
        import dg_tm as Dg, dg_ell as GE
        y = GE.boxes_at(Y[:, :4], ell)[:, 0::2]; lgs = 0.5 * (Y[:, 1] - np.log(2 + np.exp(Y[:, 1]))); lG = Y[:, 4] + lgs
        with np.errstate(all='ignore'):
            Tg, ext, auxg = Dg.z_lines(y, y, lG, 'c'); gl, calls = Dg._psi(Tg, ext)
        gtab = gl
    except Exception as e:
        out['dg_tm error'] = repr(e)[:200]
    wg = 0.0; badg = {}
    for i, st in enumerate(states):
        q = K.state(ell, *st, c)
        for which, gam in (('dj', gamma(ell, c)), ('dg', None)):
            if which == 'dg':
                if gtab is None: continue
                with localcontext(c): gam = (1 + Dc('2.5e-4')) / K.D(ell).sqrt()
            TT, brk = T.lines(q, c, gam)
            for tag in T.ALL_TAGS:
                Ld = T.log_coeff(TT, tag, ell, c)
                if which == 'dj':
                    t, s, Lf = Tm[tag]; Lf = float(Lf[i]); tf, sf = t, s
                else:
                    if tag not in gtab: badg[tag] = 'missing in dg_tm'; continue
                    tf, pf, sf, qq = gtab[tag]
                    if qq is None: Lf = -math.inf
                    else: Lf = float(np.asarray(qq.v[0], float)[i]) + (pf - 1) * (-ell)
                if Ld is None:
                    if math.isfinite(Lf): (bad if which == 'dj' else badg)[tag] = 'zero in decimal, finite in float'; nmis += 1
                    continue
                if not math.isfinite(Lf): (bad if which == 'dj' else badg)[tag] = 'finite in decimal, zero in float'; nmis += 1; continue
                # tolerance: the float codes form L = log(c sigma^{p-1}) as a sum of logs of size up to ~ 4 ell (log B - 2 ell, log kappa, log P, ...), so their absolute
                # rounding is ~ 1e-16 x (the sizes of the summands); relative 1e-13 (1 + |L|) alone is not attainable at ell = 1e12 (stage DL)
                tol = 1e-13 * (1 + abs(Lf)) + 2e-15 * (4 * ell + abs(st[0]) + abs(st[2]) + abs(st[3]) + abs(st[4]))
                d = abs(float(Ld) - Lf) / tol * 1e-13
                if tf != TT[tag][0] or sf != TT[tag][1]: (bad if which == 'dj' else badg)[tag] = 'type or sign'
                if which == 'dj':
                    worst = max(worst, d)
                    if d > 1e-13: bad[tag] = max(bad.get(tag, 0) if isinstance(bad.get(tag, 0), float) else 0, d)
                else:
                    wg = max(wg, d)
                    if d > 1e-13: badg[tag] = max(badg.get(tag, 0) if isinstance(badg.get(tag, 0), float) else 0, d)
    out.update({'ell': ell, 'states': n, 'dj_lines: largest |dL|/tol x 1e-13 (tol = 1e-13 (1 + |L|) + 2e-15 (4 ell + |log mu| + |log B| + |log kappa| + |log P|))': worst,
                'dj_lines: lines that differ': bad, 'dg_tm: largest |dL|/tol x 1e-13': wg,
                'dg_tm: lines that differ': badg, 'zero/finite mismatches': nmis})
    out['ok'] = bool(not bad and not badg and nmis == 0 and gtab is not None)
    return out


# ------------------------------------------------------------------ (X) the earlier 50-digit codes
def cross_check(n=120, seed=7):
    import cz_point as CP, da_linecheck as DA
    rng = np.random.default_rng(seed); worst = {'cz_point.point': Dc(0), 'cz_point.lemma_lines': Dc(0), 'da_linecheck.lemma_pieces': Dc(0)}; cnt = 0; skipped = 0
    names = dict(zip(CP.LINE_NAMES, ('ring2', 'M0 Xi', 'A1v', 'A1w', 'A2k', 'A2a', 'A2b', 'B1w1', 'B1w2', 'B2a', 'B2b', None)))
    for i in range(n):
        ell = float(rng.choice([55.26, 300.0, 960.8])); mu, lB, lr, kap, P = CP.sample(rng, ell); lA = float(rng.uniform(math.log(4.0) - 3 * ell, 0.0))
        c = K.context(ell)
        with localcontext(c):
            dec = lambda v: Dc(repr(float(v)))
            Le = dec(ell); st = (dec(mu).ln(), dec(lr), dec(lB), dec(kap).ln(), dec(P).ln())
            q = K.state(Le, *st, c); q['gam'] = (1 + Dc('2.5e-4')) / Le.sqrt()
            la = dec(lA) + Dc(4).ln() + dec(lr) + Le
            o, tot, alt, scale = K.pieces(q, la, c, sharp_c0=False)
            for opt in ('Fz', 'Tz', 'Bz'):
                with localcontext() as c0:
                    c0.prec = 50; pv = CP.point(ell, mu, lB, lr, kap, P, lA, opt)
                mine = tot['Fz'] if opt == 'Fz' else (max(tot['TzB2'], tot['TzB1']) if opt == 'Tz' and 'TzB2' in tot else (max(tot['BzB2'], tot['BzB1']) if opt == 'Bz' else None))
                if pv is None or mine is None:
                    skipped += 1; continue
                worst['cz_point.point'] = max(worst['cz_point.point'], abs(mine - pv) / scale); cnt += 1
            with localcontext() as c0:
                c0.prec = 50; ll = CP.lemma_lines(ell, mu, lB, lr, kap, P, lA)
            sig = q['sig']
            for nm, v in zip(CP.LINE_NAMES, ll):
                k = names[nm]
                if k is None: continue
                mine = o[k] * 2 * sig / 2 if k in ('ring2',) else o[k] * sig               # lemma_lines are in Num units (halves of the 2N bounds; ring2 is 2 A_w)
                if v != 0: worst['cz_point.lemma_lines'] = max(worst['cz_point.lemma_lines'], abs(mine / v - 1))
            with localcontext() as c0:
                c0.prec = 50; g, l, d, info = DA.lemma_pieces(ell, mu, lB, lr, kap, P, lA)
            mp = {'P1': ('g', 'P1', o['P1'] * sig), 'P2': ('g', 'P2', o['P2'] * sig), 'N1': ('l', 'N1', o['N1'] * sig), 'N3': ('l', 'N3', o['N3'] * sig), 'N4': ('l', 'N4', o['N4'] * sig),
                  'd1': ('d', 'd1', o['den d1']), 'd2': ('d', 'd2', o['den d2']), 'd3': ('d', 'd3', o['den d3']), 'd4': ('d', 'd4', o['den d4'])}
            for k, (w, kk, mine) in mp.items():
                v = {'g': g, 'l': l, 'd': d}[w][kk]
                if v != 0: worst['da_linecheck.lemma_pieces'] = max(worst['da_linecheck.lemma_pieces'], abs(mine / v - 1))
    out = {k: float(v) for k, v in worst.items()}; out.update({'states': n, 'option comparisons': cnt, 'skipped (Tz with c_delta <= 0)': skipped})
    out['ok'] = bool(all(v < 1e-40 for k, v in out.items() if k in worst))
    return out


# ------------------------------------------------------------------ power
WRONG_T = ['P1 x1.01', 'P2z x1.01', 'hFz x1.01', 'cKz x1.01', 'P4z x1.01', 'N1 x0.99', 'N2 x0.99', 'N4 x0.99', 'A1w x0.99', 'B2a x0.99', 'B2c x0.99', 'hneg1 x0.99',
           'd1 x0.99', 'ring2 x0.99', 'M0Xi x0.99', 'A2k x0.99', 'B1m x0.99', 'FzK x0.99', 'pair x0.99',
           'N1 sign', 'hneg1 sign', 'eta N1', 'U1', 'K2', 'e50', 'A1w power', 'ringf0', 'N4 old']


# DL: the lines with their own slack against the lemma (the smallest ratio of dk_audit run over all ell): scaled by 0.9/(smallest ratio) they must be caught
SCALED = {'B2c, B2s x 0.9/1.2936': {'B2c': '0.6957', 'B2s': '0.6957'}, 'hneg1 x 0.9/1.998': {'hneg1': '0.4504'},
          'B1m, B1c, B1l, uB2c, uB2s x 0.9/1.2936': {k: '0.6957' for k in ('B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')}, 'pair x 0.9/330.1': {'pair': '0.002726'},
          'ring2 x 0.9/1.0027': {'ring2': '0.8976'}}


def power_one(name, ells=ELLS, n=60, m=9):
    """one wrong version of dk_table: number of (state, a) points at which (L) or (S) fails, per ell."""
    T.WRONG.clear(); out = {}
    if name in SCALED: T.WRONG['scale'] = SCALED[name]
    else: T.WRONG[name] = True
    try:
        for ell in ells:
            rng = np.random.default_rng(99 + int(ell) % 100000); states, fam = sample(ell, rng, n); c = K.context(ell); gam = gamma(ell, c); caught = 0; pts = 0
            for st in states:
                pre = prepare(ell, st, c, gam)
                for la in a_grid(ell, st[1], st[2], c, m):
                    res, o, V = eval_point(ell, st, la, c, gam, pre); pts += 1
                    if not all(ok for rt, ok in res['groups'].values()) or not all(ok for d, ok in res['tot'].values()): caught += 1
            out[str(ell)] = {'points': pts, 'caught': caught}
    finally:
        T.WRONG.clear()
    return out


def power_dj():
    """wrong versions of the float code dj_lines (one edit each) must be caught by (T2)."""
    import dj_lines as J0
    src = open(J0.__file__).read(); out = {}
    edits = {'dj_lines: P2z without ringf': ("add('P2z', 'L', 1, +1, np.log(ringf) + lfl", "add('P2z', 'L', 1, +1, 0.0 + lfl"),
             'dj_lines: N1 with eta/2': ("add('N1', 'L', 1, -1, math.log(eta) + lkE", "add('N1', 'L', 1, -1, math.log(eta / 2) + lkE"),
             'dj_lines: U1 with ell instead of 2 ell': ("two_l = 2 * ell + 3.1", "two_l = ell + 3.1")}
    for nm, (a, b) in edits.items():
        assert src.count(a) == 1, nm
        mod = types.ModuleType('dj_lines_wrong'); exec(compile(src.replace(a, b), 'dj_lines_wrong', 'exec'), mod.__dict__)
        out[nm] = {str(ell): (not transcription(ell, n=40, dj=mod)['ok']) for ell in (55.26, 955.8, 1e6, 1e12)}
    return out


def power_precision():
    """the default exponent range of decimal (NAIVE['range']): pieces vanish or the evaluation raises at large ell -- the audit must report it."""
    out = {}
    K.NAIVE['range'] = True
    try:
        for ell in (955.8, 1e5, 1e6, 1e8):
            r = audit_ell(ell, n=12, m=5, nprec=1)
            out[str(ell)] = {'reported (vanished or exceptions)': bool(r['number vanished'] + r['number of exceptions'] > 0), 'vanished': r['number vanished'], 'exceptions': r['number of exceptions'],
                             'audit ok': r['ok']}
    finally:
        K.NAIVE['range'] = False
    return out


def _run_ell(args):
    ell, n, m = args
    return audit_ell(ell, n=n, m=m)


def run(n=1500, m=25, procs=2):
    import multiprocessing as mp
    t0 = time.time(); out = {}
    fn = 'results/dk_audit.json'
    if os.path.exists(fn): out = json.load(open(fn))
    todo = [e for e in ELLS if 'ell = %s' % e not in out]
    with mp.get_context('fork').Pool(procs) as pool:
        for r in pool.imap_unordered(_run_ell, [(e, n, m) for e in todo]):
            out['ell = %s' % r['ell']] = r; print(r['ell'], r['ok'], round(r['seconds']), flush=True)
            json.dump(out, open(fn, 'w'), indent=1)
    if 'transcription (T2)' not in out:
        out['transcription (T2)'] = {str(e): transcription(e) for e in ELLS}; json.dump(out, open(fn, 'w'), indent=1)
    if 'cross-check (X)' not in out:
        out['cross-check (X)'] = cross_check(); json.dump(out, open(fn, 'w'), indent=1)
    out['ok'] = bool(all(out['ell = %s' % e]['ok'] for e in ELLS) and all(v['ok'] for v in out['transcription (T2)'].values()) and out['cross-check (X)']['ok'])
    out['seconds (this call)'] = time.time() - t0
    json.dump(out, open(fn, 'w'), indent=1)
    return out


def run_power(procs=2):
    import multiprocessing as mp
    fn = 'results/dk_power.json'; out = json.load(open(fn)) if os.path.exists(fn) else {}
    todo = [w for w in WRONG_T + list(SCALED) if 'table: ' + w not in out]
    with mp.get_context('fork').Pool(procs) as pool:
        for w, r in zip(todo, pool.imap(power_one, todo)):
            out['table: ' + w] = r; print(w, {e: v['caught'] for e, v in r.items()}, flush=True); json.dump(out, open(fn, 'w'), indent=1)
    if 'float code dj_lines' not in out: out['float code dj_lines'] = power_dj(); json.dump(out, open(fn, 'w'), indent=1)
    if 'precision: default exponent range' not in out: out['precision: default exponent range'] = power_precision(); json.dump(out, open(fn, 'w'), indent=1)
    json.dump(out, open(fn, 'w'), indent=1)
    return out


if __name__ == '__main__':
    a = sys.argv[1] if len(sys.argv) > 1 else 'run'
    if a == 'run': print(run()['ok'])
    elif a == 'power': run_power()
