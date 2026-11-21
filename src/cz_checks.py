"""Stage CZ 2.3: checks of the table cz_cells.py.  Python 3.11 grammar.
  (K1) with the repairs and the z-options off, cz_cells.py IS cy_cells.py: identical values of every option and identical margins on random boxes
       (so the only differences are the proved claims and the two repairs).
  (K2) the N9 repair: at a zero-width box the option-term N9 of the table against Lemma CN-2's value (co_remainders.catalogue, 'N9 F first'):
       ratio 1/sqrt2 without the repair (the old tables), 1 with it (up to e^{-se2/4} <= 1).
  (K3) what the two repairs change on random initial boxes of the column (accepted before/after), and what the z-options add.
  (K4) CONCAVITY IN G of the z-options (the premise of the endpoint rule), tested numerically: for one fixed relaxation (frac = 0, the one-branch form)
       the raw value v(G) on a box satisfies the chord inequality v((G1 + G2)/2) >= (v(G1) + v(G2))/2 on (0, G_cell], also in the true kappa tail
       (where sqrt(G) enters through its tangent).  POWER: the same test on a deliberately convex version (ZOPT['W'] = 'cvx': the F main gain made
       ~ G^2) must fail somewhere.  (The real nonlinear terms of the z-options -- sqrt(P), G/mu, sqrt(G) in the tail -- are all smaller than the
       total by a factor sigma, below any floating-point test; their concavity is by the written argument in cz_cells.py.)
  (K5) the z-options never use a line outside the lemma's range: K^2 y_hi <= 1 (z0 <= 1) and y_hi <= 1e-6 (M4) on every box that is not skipped.
-> results/cz_checks.json ; exit 1 if a check fails."""
import json, math, sys
import numpy as np
import cy_cells as Y, cz_cells as Z
res = {}; ok_all = True


def rec(name, ok, **kw):
    global ok_all
    ok_all &= bool(ok); res[name] = {'ok': bool(ok), **kw}
    print('[%s] %s %s' % ('OK ' if ok else 'FAIL', name, json.dumps(kw, default=float)[:300]), flush=True)


def boxes(rng, n, ell_a=55.26, ell_b=56.26, nl=10, wm=1.0, wr=4.0, wB=4.0, wk=2.0):
    """n random initial boxes of the column [ell_a, ell_b]: the grids of cy_cells.initial_boxes, one random cell per coordinate (the full product is
    not built: at ell = 960 it has 1e8 rows)."""
    lBlo = Y.LB_SKIP; lBhi = math.log(Y.BMAX) + 2 * ell_b
    lm = list(np.arange(math.log(1e-3), math.log(4 * ell_b + 40), wm)) + [math.log(4 * ell_b + 40)]
    lr = list(np.arange(-3 * ell_b, math.log(0.25), wr)) + [math.log(0.25)]
    lB = list(np.arange(lBlo, lBhi, wB)) + [lBhi]
    lk = list(np.arange(math.log(1e-12), math.log(3.0), wk)) + [math.log(3.0)] + [math.log(10.0 ** k) for k in range(1, 9)]
    le = np.linspace(ell_a, ell_b, nl + 1)
    mus = [(-np.inf, math.log(1e-3))] + list(zip(lm[:-1], lm[1:])) + [(math.log(4 * ell_b + 40), np.inf)]
    ks = [(-np.inf, math.log(1e-12))] + list(zip(lk[:-1], lk[1:])) + [(math.log(Y.KMAX), np.inf)]
    rs = list(zip(lr[:-1], lr[1:])); Bs = list(zip(lB[:-1], lB[1:])); es = list(zip(le[:-1], le[1:]))
    out = []
    for _ in range(n):
        m = mus[rng.integers(len(mus))]; r = rs[rng.integers(len(rs))]; B = Bs[rng.integers(len(Bs))]; k = ks[rng.integers(len(ks))]; e = es[rng.integers(len(es))]
        out.append((m[0], m[1], r[0], r[1], B[0], B[1], k[0], k[1], e[0], e[1]))
    X = np.array(out)
    return X[~Y.skip(X)]


def k1(rng):
    X = np.vstack([boxes(rng, 1500), boxes(rng, 800, 300.0, 301.0), boxes(rng, 800, 959.8, 960.8)])
    Z.FIX.update(N9=False, SAND=False, GGT=False, N6Y=False); Z.ZOPT['on'] = False; Z.set_opts(); Z.AR['on'] = False
    try:
        vy = Y.values(X); vz = Z.values(X); same = all(np.array_equal(vy[k], vz[k]) for k in vy)
        my = Y.cell_margin(X); mz = Z.cell_margin(X); same_m = bool(np.array_equal(my, mz))
    finally:
        Z.FIX.update(N9=True, SAND=True, GGT=True, N6Y=True); Z.ZOPT['on'] = True; Z.set_opts(); Z.AR['on'] = True
    rec('(K1) repairs off, z off: cz_cells = cy_cells (values of T, B, F at both ends and margins, incl. the two-piece rule)', same and same_m, boxes=int(len(X)),
        accepted=int((my > Y.ACC).sum()))


def k2():
    import co_remainders as CR
    ell = 60.0; mu = 5.0; r = 1e-3; kap = 2.0; lB = math.log(1e30)
    X = np.array([[math.log(mu), math.log(mu), math.log(r), math.log(r), lB, lB, math.log(kap), math.log(kap), ell, ell]])
    out = {}
    for fx in (False, True):
        Z.FIX['N9'] = fx; Z.ZOPT['on'] = False; Z.set_opts()
        try:
            lGc, _ = Z.box_P(X); cap = {}; Z.DIAG['CAPTURE'] = cap
            Z.terms_cell(X, 0.0, True, lGc=lGc, opts=('B',), lGref=lGc); Z.DIAG['CAPTURE'] = None
        finally:
            Z.DIAG['CAPTURE'] = None; Z.FIX['N9'] = True; Z.ZOPT['on'] = True; Z.set_opts()
        n9 = [float(-c[0]) for name, t, p, c in cap['opt']['B'] if name == 'N9'][0]
        sig = math.exp(-ell); G = math.exp(lGc[0]); gs = math.sqrt(r / (2 + r)); P = G / gs; b = math.exp(lB) * sig ** 2
        cat = CR.catalogue(ell, mu, b, r, kap, P, b * 20.0, 1.0, 1 / ell)
        out[fx] = n9 * sig / float(cat['N']['N9 F first'])
    rec('(K2) N9: table/lemma = 1/sqrt2 without the repair and 1 with it', abs(out[False] - 1 / math.sqrt(2)) < 1e-6 and abs(out[True] - 1) < 1e-6,
        ratio_without=out[False], ratio_with=out[True])


def k3(rng):
    X = np.vstack([boxes(rng, 3000), boxes(rng, 1000, 300.0, 301.0), boxes(rng, 1000, 959.8, 960.8)]); my = Y.cell_margin(X) > Y.ACC; d = {'boxes': int(len(X)), 'cy_cells accepted': int(my.sum())}
    try:
        for nm, fx in (('N9 repair only', dict(N9=True, SAND=False, GGT=False, N6Y=False)), ('sandwich repair only', dict(N9=False, SAND=True, GGT=False, N6Y=False)), ('both repairs', dict(N9=True, SAND=True, GGT=True, N6Y=True))):
            Z.FIX.update(**fx); Z.ZOPT['on'] = False; Z.set_opts(); m = Z.cell_margin(X) > Z.ACC
            d[nm] = {'accepted': int(m.sum()), 'lost': int((my & ~m).sum()), 'gained': int((~my & m).sum())}
        base = m
        Z.ZOPT['on'] = True; Z.set_opts(); mn = Z.cell_margin(X) > Z.ACC
        d['CZ table (both repairs, z-options)'] = {'accepted': int(mn.sum()), 'lost vs repaired old options': int((base & ~mn).sum()), 'gained': int((~base & mn).sum())}
    finally:
        Z.FIX.update(N9=True, SAND=True, GGT=True, N6Y=True); Z.ZOPT['on'] = True; Z.set_opts()
    rec('(K3) effect of the repairs and of the z-options on random initial boxes (ell near 55.26, 300, 960.8)', d['CZ table (both repairs, z-options)']['lost vs repaired old options'] == 0, **d)


def chord(X, opt, fr=(1e-6, 0.01, 0.1, 0.25, 0.5, 0.75, 1.0)):
    """number of chord violations of the raw one-relaxation value of the option along G = f G_cell."""
    lGc, _ = Z.box_P(X); Z.DIAG.update(RAW=True, FRAC=(0.0,), TSTAR=())
    try:
        with np.errstate(all='ignore'):
            V = [np.asarray(Z.terms_cell(X, 0.0, True, lGc=lGc + math.log(f), opts=(opt,), lGref=lGc), dtype=np.longdouble) for f in fr]
    finally:
        Z.DIAG.update(RAW=False, FRAC=None, TSTAR=None)
    bad = 0; n = 0
    for i in range(len(fr)):
        for j in range(i + 2, len(fr)):
            for k in range(i + 1, j):
                lam = (fr[k] - fr[i]) / (fr[j] - fr[i]); ch = (1 - lam) * V[i] + lam * V[j]
                fin = np.isfinite(V[i]) & np.isfinite(V[j]) & np.isfinite(V[k])
                tol = 1e-12 * (np.abs(V[i]) + np.abs(V[j]) + np.abs(V[k]))
                bad += int(np.sum(fin & (V[k] < ch - tol))); n += int(fin.sum())
    return bad, n


def k4(rng):
    X = np.vstack([boxes(rng, 1500), boxes(rng, 700, 300.0, 301.0), boxes(rng, 700, 959.8, 960.8)]); tail = ~np.isfinite(X[:, 7]); d = {}
    tot = 0
    for opt in ('Tz', 'Bz', 'Fz'):
        b1, n1 = chord(X[~tail], opt); b2, n2 = chord(X[tail], opt); d[opt] = {'finite kappa': [b1, n1], 'true kappa tail': [b2, n2]}; tot += b1 + b2
    Z.ZOPT['W'] = 'cvx'
    try:
        pw = sum(chord(X, opt)[0] for opt in ('Tz', 'Bz'))
    finally:
        Z.ZOPT['W'] = None
    rec('(K4) concavity in G of the z-options (chord test); power: a gain made convex in G is caught', tot == 0 and pw > 0, violations=tot, tested=d, power_violations_of_the_convex_version=pw)


def k5():
    lB = Y.LB_SKIP; worst = 0.0
    for ell in (55.26, 300.0, 960.8):
        worst = max(worst, (8 * ell + 100) / (2 * math.exp(lB)))
    rec('(K5) K^2 y_hi <= 1 and y_hi <= 1e-6 on every box that is not skipped (beta_a > 2.5e10)', worst <= 1 and 1 / (2 * math.exp(lB)) <= 1e-6, K2_yhi_max=worst, y_hi_max=1 / (2 * math.exp(lB)))


def run():
    rng = np.random.default_rng(20261110)
    k1(rng); k2(); k3(rng); k4(rng); k5()
    res['all_ok'] = bool(ok_all); json.dump(res, open('results/cz_checks.json', 'w'), indent=1, default=float); print('all ok:', ok_all)
    return ok_all


if __name__ == '__main__':
    sys.exit(0 if run() else 1)
