"""Stage DP: the attempts to BREAK the claims DP-1a (room 1a) and DP-2 (room 2) with the point function of Theorem DJ-T (dj_lines: the corrected 37 lines).
Python 3.11 grammar.  [numerical]   Plan: DP_探索計画.md sections B.3 (1) and C.2 (written before this ran).
The search is dj_search.search (families, champions of cells, shrinking random steps, pattern search to convergence) with the range of B replaced by a band:
  ROOM 1 (ell >= 960.8, B < 2.5e10):   (i)   [max(5e5, 50 (8 ell + 100)), 2.5e10]            the lines are lower bounds, the uniform constants of DJ-T (q, z2)
                                       (ii)  [max(5e5, (8 ell + 100)/2), 50 (8 ell + 100)]   the lines are lower bounds (z0 <= 1), where this band is not empty
                                       (iii) [max(1e4, 1.05 (ell + 13)), max(5e5, (8 ell + 100)/2)]   NOT lower bounds (z0 > 1 or y > 1e-6): the formulas only, recorded
     values: F_full (the best option-branch at every a) and F_rule (the option-branch chosen by the rule of DJ-T); (F^2 - 1) ell must be >= 10.
     extra families (as seeds): W1 kappa ~ 1 (what a wide focus gives), W2 kappa near the chirp threshold 16 Gam2 B sigma and near c_kap ell b/r,
     W3 the ends of the band with mu in [ell/16, ell + ln ell] and r at the borders xi = 8, xi = ell^2, r = c_ch sqrt(ell) sigma.
  ROOM 2 (b in (1/2, 1], every ell >= 55.26): option Fz only; P up to the ceiling of (A), (K), (CM) (the hypotheses of claim DP-2);
     log F = log(gamma* sqrt(ell)), gamma* the largest gamma with Lambda_Fz >= 0:  DP-2a needs (F^2 - 1) ell >= 10,  DP-2b needs gamma* >= 0.6.
PLANTED DIPS (depth 5 in (F^2 - 1) ell) and WRONG VERSIONS: see run_room1 / run_room2.
    python3 dp_search.py room1 | room2    -> results/dp_search_room1.json, results/dp_search_room2.json"""
import json, math, sys, time, contextlib
import numpy as np
import dj_search as S, dj_proof as PR, dj_lines as J

LB25 = math.log(2.5e10)
_ORIG_RANGES = S.ranges


@contextlib.contextmanager
def band(lBlo, lBhi):
    def rg(ell, lBmin=None):
        R = _ORIG_RANGES(ell, S.LBMIN); R[2, 0] = lBlo; R[2, 1] = lBhi; return R
    S.ranges = rg
    try: yield
    finally: S.ranges = _ORIG_RANGES


def bands(ell):
    b50 = math.log(max(5e5, 50 * (8 * ell + 100))); bv = math.log(max(5e5, (8 * ell + 100) / 2)); b0 = math.log(max(1e4, 1.05 * (ell + 13)))
    out = {'(i) [max(5e5, 50(8 ell + 100)), 2.5e10]': (b50, LB25)}
    if bv < b50 - 1e-9: out['(ii) [max(5e5, (8 ell + 100)/2), 50(8 ell + 100)]'] = (bv, b50)
    if b0 < bv - 1e-9: out['(iii) [max(1e4, 1.05(ell + 13)), max(5e5, (8 ell + 100)/2)] (NOT lower bounds: formulas only)'] = (b0, bv)
    return out


def room1_seeds(ell, rng, n, lBlo, lBhi):
    U = lambda a, b, k=n: rng.uniform(a, b, k); pick = lambda *xs: np.choose(rng.integers(0, len(xs), n), xs)
    lsg = -ell; l2 = math.log(1 / (2 * math.sqrt(ell)))                                # Gam2 ~ 1/(2 sqrt(ell))
    lB = pick(U(lBlo, lBhi), lBlo + U(0, 2), lBhi - U(0, 2))
    lmu = pick(np.log(U(ell / 16, ell + math.log(ell))), np.log(np.maximum(ell / 4 - U(-6, 45), 1.0)), U(math.log(1e-3), math.log(8 * ell)))
    line = 2 * math.log(ell) - ell
    lr = pick(U(-3 * ell, math.log(0.25)), -ell / 2 + U(-15, 15), line - 0.5 * lmu + U(-3, 3), lsg + math.log(8) - 0.5 * lmu + U(-3, 3), lsg + 0.5 * math.log(ell) + math.log(2.9) + U(-3, 3))
    q = pick(np.zeros(n), np.zeros(n), -U(0, 5))
    W1 = np.stack([lmu, lr, lB, U(-0.02, 0.02), q], axis=1)
    lk2 = pick(math.log(16) + l2 + lB + lsg + U(-6, 6), math.log(4.94 * ell) + lB - 2 * ell - lr + U(0, 4))
    W2 = np.stack([lmu, lr, lB, lk2, q], axis=1)
    W3 = np.stack([lmu, lr, pick(np.full(n, lBlo), np.full(n, lBhi)), pick(U(-0.02, 0.02), lk2, U(-40, 5)), q], axis=1)
    return np.vstack([W1, W2, W3])


def v_full(ell, **kw): return lambda Y: S.value(Y, ell, **kw)


def v_rule(ell):
    def f(Y):
        Y = np.atleast_2d(np.asarray(Y, float)); lP = S.lPbar(ell, Y[:, 0], Y[:, 2] - 2 * ell, Y[:, 3]) + Y[:, 4]
        return PR.rule_lF(ell, Y[:, :4], lP)[0]
    return f


def one(ell, lBlo, lBhi, vfun, seed, n=700, plant=None, seeds_fn=room1_seeds):
    rng = np.random.default_rng(seed)
    with band(lBlo, lBhi):
        sd = seeds_fn(ell, rng, n, lBlo, lBhi) if seeds_fn is not None else None
        lF, y, nev, fam, nan = S.search(ell, rng, n=n, n_low=30, n_cell=20, steps1=20, steps2=60, plant=plant, seeds=sd, vfun=vfun)
    m = float(J.margin(np.array([lF]), ell)[0])
    return {'log F': float(lF), '(F^2 - 1) ell': m, 'state (log mu, log r, log B, log kappa, q)': [float(v) for v in y], 'mu': float(math.exp(min(y[0], 700))),
            'B': float(math.exp(min(y[2], 700))), 'kappa': float(math.exp(min(y[3], 700))), 'log r + ell/2': float(y[1] + ell / 2), 'tau >= 5e11/B': 5e11 * math.exp(-min(y[2], 700)),
            'evaluations': int(nev), 'nan': int(nan), 'family minima before refinement (log F)': {k: float(v) for k, v in fam.items()}}


def run_room1(ells=(960.8, 3000.0, 1e4, 1e5, 1e6), save=True):
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)', 'needed': '(F^2 - 1) ell >= 10'}
    for ell in ells:
        row = {}
        for name, (lo, hi) in bands(ell).items():
            row[name] = {'F_full': one(ell, lo, hi, None, 101 + int(ell) % 977), 'F_rule': one(ell, lo, hi, v_rule(ell), 202 + int(ell) % 977)}
            print(ell, name[:6], 'full %.4g rule %.4g' % (row[name]['F_full']['(F^2 - 1) ell'], row[name]['F_rule']['(F^2 - 1) ell']), round(time.time() - t0), flush=True)
        out[str(ell)] = row
    # planted dips (band (i) at ell = 3000 and 1e5): depth 5
    pl = {}
    for ell in (3000.0, 1e5):
        lo, hi = bands(ell)['(i) [max(5e5, 50(8 ell + 100)), 2.5e10]']
        for nm, centre, widths in (('wide focus: kappa ~ 1, mu ~ ell/4, r ~ sigma^(1/2), B in the middle', [math.log(ell / 4), -ell / 2, 0.5 * (lo + hi), 0.0, 0.0], [0.3, 3, 3, 3, 1]),
                                   ('B at the lower end, low mu', [math.log(0.05), -ell / 3, lo + 0.5, -5.0, -1.0], [2, 20, 1, 5, 2])):
            r = one(ell, lo, hi, None, 303 + int(ell) % 977, plant=(centre, widths, 5.0)); pl['ell = %g: %s' % (ell, nm)] = {'found minimum of (F^2 - 1) ell': r['(F^2 - 1) ell'], 'found': abs(r['(F^2 - 1) ell'] - 5.0) < 0.05}
            print('plant', ell, nm[:20], r['(F^2 - 1) ell'], flush=True)
    out['planted dips (depth 5)'] = pl
    # wrong versions (band (i), ell = 3000)
    ell = 3000.0; lo, hi = bands(ell)['(i) [max(5e5, 50(8 ell + 100)), 2.5e10]']; wr = {}
    for nm, kw in (('line cKz (chirp) dropped', {'drop': ('cKz',)}), ('line P1 dropped', {'drop': ('P1',)}), ('line P2z dropped', {'drop': ('P2z',)}), ("(J) removed from (H')", {'parts': ('A', 'K', 'CM')}),
                   ('Tz-B2 only', {'opts': ('XB2',)}), ('Fz only', {'opts': ('Fz',)})):
        r = one(ell, lo, hi, v_full(ell, **kw), 404); wr[nm] = {'smallest (F^2 - 1) ell': r['(F^2 - 1) ell'], 'log F': r['log F'], 'broken (< 10)': bool(r['(F^2 - 1) ell'] < 10)}
        print('wrong', nm, r['(F^2 - 1) ell'], flush=True)
    out['wrong versions (ell = 3000, band (i))'] = wr
    vals = [out[str(e)][k][w]['(F^2 - 1) ell'] for e in ells for k in out[str(e)] if not k.startswith('(iii)') for w in ('F_full', 'F_rule')]
    out['smallest (F^2 - 1) ell in the bands (i), (ii)'] = float(min(vals)); out['claim holds on the searched states'] = bool(min(vals) >= 10)
    out['nan in the bands (i), (ii)'] = int(sum(out[str(e)][k][w]['nan'] for e in ells for k in out[str(e)] if not k.startswith('(iii)') for w in ('F_full', 'F_rule')))
    out['ok'] = bool(out['claim holds on the searched states'] and all(v['found'] for v in pl.values()) and any(v['broken (< 10)'] for v in wr.values()) and out['nan in the bands (i), (ii)'] == 0)
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_search_room1.json', 'w'), indent=1)
    return out


# ------------------------------------------------------------------------------------------------ room 2
def room2_seeds(ell, rng, n, lBlo, lBhi):
    U = lambda a, b, k=n: rng.uniform(a, b, k); pick = lambda *xs: np.choose(rng.integers(0, len(xs), n), xs)
    lB = pick(U(lBlo, lBhi), np.full(n, lBlo), np.full(n, lBhi), lBhi + np.log1p(-10 ** U(-12, -1)))
    lmu = pick(U(math.log(0.5), math.log(30.0)), U(math.log(1e-3), math.log(8 * ell + 80)), U(-3 * ell, math.log(1e-3)))       # Pbar is largest for mu of order 1-10
    lr = pick(np.full(n, math.log(0.25)), U(math.log(1e-4), math.log(0.25)), U(-3 * ell, math.log(0.25)), np.full(n, -3 * ell))
    lk = pick(U(-40, 5), U(0, math.log(2 * ell)), U(-2.2 * ell - 50, 3 * ell))
    q = pick(np.zeros(n), np.zeros(n), -U(0, 5), -U(0, 4 * ell))
    return np.stack([lmu, lr, lB, lk, q], axis=1)


def v_fz(ell, parts=('A', 'K', 'CM'), opts=('Fz',), **kw):
    return lambda Y: S.value(Y, ell, parts=parts, opts=opts, **kw)


def run_room2(ells=(55.26, 82.89, 331.56, 955.8, 1e4, 1e6), save=True):
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)', 'needed': 'DP-2a: (F^2 - 1) ell >= 10;  DP-2b: gamma* = F/sqrt(ell) >= 0.6'}
    for ell in ells:
        lo, hi = math.log(0.5) + 2 * ell, 2 * ell
        r = one(ell, lo, hi, v_fz(ell), 505 + int(ell) % 977, seeds_fn=room2_seeds)
        r['gamma* = F/sqrt(ell)'] = math.exp(r['log F']) / math.sqrt(ell); r['b'] = math.exp(r['state (log mu, log r, log B, log kappa, q)'][2] - 2 * ell)
        # are there states of Case II (the rule) in the room?  sample the seeds and the families at the ceiling
        rng = np.random.default_rng(9)
        with band(lo, hi): Y = np.vstack([room2_seeds(ell, rng, 3000, lo, hi)] + list(S.families(ell, rng, 400).values()))
        lP = S.lPbar(ell, Y[:, 0], Y[:, 2] - 2 * ell, Y[:, 3], parts=('A', 'K', 'CM')); Q = PR.state_quantities(ell, Y[:, :4], lP); reg = PR.rule(ell, Q)
        r['rule: states per regime at the ceiling (I/Fz, I/Tz-B2, II chirp, II rest)'] = [int((reg == k).sum()) for k in range(4)]
        r['largest G Gam2/(c1 sqrt(b)) at the ceiling (Case II needs > 1)'] = float(np.exp(np.max(Q['lG'] + Q['lG2'] - math.log(PR.C1) - 0.5 * Q['lb'])))
        out[str(ell)] = r; print(ell, 'gamma* %.4f  (F^2-1)ell %.4g  b %.4f' % (r['gamma* = F/sqrt(ell)'], r['(F^2 - 1) ell'], r['b']), r['rule: states per regime at the ceiling (I/Fz, I/Tz-B2, II chirp, II rest)'], round(time.time() - t0), flush=True)
    ell = 55.26; lo, hi = math.log(0.5) + 2 * ell, 2 * ell
    r = one(ell, lo, hi, v_fz(ell), 606, plant=([math.log(3.0), math.log(1e-3), math.log(0.75) + 2 * ell, 0.0, 0.0], [0.5, 2, 0.1, 3, 1], 5.0), seeds_fn=room2_seeds)
    out['planted dip (depth 5; b = 0.75, mu = 3, r = 1e-3; ell = 55.26)'] = {'found minimum of (F^2 - 1) ell': r['(F^2 - 1) ell'], 'found': abs(r['(F^2 - 1) ell'] - 5.0) < 0.05}
    wr = {}
    for nm, kw in (('line P4z dropped', {'drop': ('P4z',)}), ('line P1 dropped', {'drop': ('P1',)}), ('line hneg1 dropped (not a wrong version: it must RAISE gamma*)', {'drop': ('hneg1',)}),
                   ("(CM) removed from (H') (P up to mu/8)", {'parts': ('A', 'K')})):
        r = one(ell, lo, hi, v_fz(ell, **kw), 707, seeds_fn=room2_seeds); g = math.exp(r['log F']) / math.sqrt(ell)
        wr[nm] = {'smallest gamma*': g, '(F^2 - 1) ell': r['(F^2 - 1) ell'], 'DP-2a broken (< 10)': bool(r['(F^2 - 1) ell'] < 10), 'DP-2b broken (gamma* < 0.6)': bool(g < 0.6)}
        print('wrong', nm, g, r['(F^2 - 1) ell'], flush=True)
    out['wrong versions (ell = 55.26)'] = wr
    gmin = min(out[str(e)]['gamma* = F/sqrt(ell)'] for e in ells); out['smallest gamma* found'] = gmin
    out['wrong version: a claim gamma* >= 0.8 would be broken'] = bool(gmin < 0.8)
    out['DP-2a holds on the searched states'] = bool(all(out[str(e)]['(F^2 - 1) ell'] >= 10 for e in ells)); out['DP-2b holds on the searched states'] = bool(gmin >= 0.6)
    out['no state of Case II found'] = bool(all(sum(out[str(e)]['rule: states per regime at the ceiling (I/Fz, I/Tz-B2, II chirp, II rest)'][2:]) == 0 for e in ells))
    out['ok'] = bool(out['DP-2a holds on the searched states'] and out['DP-2b holds on the searched states'] and out['planted dip (depth 5; b = 0.75, mu = 3, r = 1e-3; ell = 55.26)']['found']
                     and wr['line P4z dropped']['DP-2b broken (gamma* < 0.6)'] and out['wrong version: a claim gamma* >= 0.8 would be broken'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_search_room2.json', 'w'), indent=1)
    return out


def run_gap(ells=(1e8, 1e9), save=True):
    """DP_探索計画.md section E (written before this ran): the band between Theorem DP-1a as first stated (B < 2.5e10) and Theorem DJ-T (B >= 50 (8 ell + 100)),
    which exists for ell > 6.25e7.  The whole band [8 ell + 100, 50 (8 ell + 100)] is searched (F_full and F_rule); needed: (F^2 - 1) ell >= 10."""
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)', 'needed': '(F^2 - 1) ell >= 10', 'band': 'B in [8 ell + 100, 50 (8 ell + 100)]'}
    for ell in ells:
        lo, hi = math.log(8 * ell + 100), math.log(50 * (8 * ell + 100))
        row = {'F_full': one(ell, lo, hi, None, 808 + int(ell) % 977), 'F_rule': one(ell, lo, hi, v_rule(ell), 909 + int(ell) % 977), 'the band contains B = 2.5e10': bool(lo < LB25 < hi)}
        out[str(ell)] = row; print(ell, 'full %.4g rule %.4g' % (row['F_full']['(F^2 - 1) ell'], row['F_rule']['(F^2 - 1) ell']), round(time.time() - t0), flush=True)
    ell = 1e8; lo, hi = math.log(8 * ell + 100), math.log(50 * (8 * ell + 100))
    r = one(ell, lo, hi, None, 1010, plant=([math.log(ell / 4), -ell / 2, math.log(3e10), 0.0, 0.0], [0.3, 3, 0.5, 3, 1], 5.0))
    out['planted dip (depth 5; ell = 1e8, B = 3e10, kappa ~ 1, mu ~ ell/4)'] = {'found minimum of (F^2 - 1) ell': r['(F^2 - 1) ell'], 'found': abs(r['(F^2 - 1) ell'] - 5.0) < 0.05}
    wr = {}
    for nm, kw in (('line cKz (chirp) dropped', {'drop': ('cKz',)}), ('line P1 dropped', {'drop': ('P1',)})):
        r = one(ell, lo, hi, v_full(ell, **kw), 1111); wr[nm] = {'smallest (F^2 - 1) ell': r['(F^2 - 1) ell'], 'broken (< 10)': bool(r['(F^2 - 1) ell'] < 10)}
        print('wrong', nm, r['(F^2 - 1) ell'], flush=True)
    out['wrong versions (ell = 1e8)'] = wr
    vals = [out[str(e)][w]['(F^2 - 1) ell'] for e in ells for w in ('F_full', 'F_rule')]
    out['smallest (F^2 - 1) ell'] = float(min(vals)); out['nan'] = int(sum(out[str(e)][w]['nan'] for e in ells for w in ('F_full', 'F_rule')))
    out['ok'] = bool(min(vals) >= 10 and out['planted dip (depth 5; ell = 1e8, B = 3e10, kappa ~ 1, mu ~ ell/4)']['found'] and any(v['broken (< 10)'] for v in wr.values()) and out['nan'] == 0)
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_search_gap.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = {'room1': run_room1, 'room2': run_room2, 'gap': run_gap}[sys.argv[1]](); print(r['ok'])
