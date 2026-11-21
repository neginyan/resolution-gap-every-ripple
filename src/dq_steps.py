"""Stage DQ (instruction 2.1): the steps of the proof of Theorem DP-1a, one by one, at random states of room 1a -- the tables of section 6.5/6.6 of DJ-T for DP-1a.
Python 3.11 grammar.  Plan: DQ_探索計画.md section A (written before this ran).
  States: dj_proof.sample (the families of the search, states lowered into Case II, the DI corner, the beta-case kappa) with the range of B replaced by
          [B_1(ell), ell^4]; one third of the states moved next to B_1 (B_1 e^{[0,1]}) and one third next to ell^4 (ell^4 e^{-[0,1]}).
  Constants: dj_proof.consts (floats) with the replacements of DP section 11.3 made in its SOURCE (as dp_room1 does for dl_consts.consts_iv):
          B_m := B_1(ell), q <= (1 + eta)/(8 (1 - eta)), z2 <= 1/2, es := 0.25/B_m, e0 := 2/sqrt(B_m) + es, the written-in numbers (w1) k_f >= K5, (w2) 1/sqrt(c0) >= IC0,
          (w3) A2k <= A2C b^2 cKz with the values of the piece; ES, E0 of the namespace replaced by es, e0.
  Items: every item of dj_proof.check_remainders (R1)-(R7) and the summaries, dj_proof.check_steps (F), (c), (II-ch), (II-s), (m1)-(m4), the forms of the text of
          (R1) <= 0.52 es, (R3) <= 0.48 es, (R4), and (b.5): on the wide Case II states with Th' < mT + T and ch < mT + Tbar: kappa_b mu <= 1 and u > max(6, U).
  POWER: bounds x 0.9; the wrong versions of check_steps; (R1) against 0.26 es; B below B_1 with the constants of B_1.
-> results/dq_steps.json"""
import json, math, time, inspect, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dj_proof as PR, dj_search as S, dj_lines as J, dp_search as SE

CSRC = inspect.getsource(PR.consts)
CREPL = [("def consts(ell):", "def consts(ell, BM=2.5e10, QDEN=400.0, Z2V=0.01, K5=0.999, IC0=0.999, A2C=2.1):"),
         ("Bm = 2.5e10; q = (1 + eta) / (400 * (1 - eta)); z2 = 0.01;", "Bm = BM; q = (1 + eta) / (QDEN * (1 - eta)); z2 = Z2V;"),
         ("o['c_k'] = 0.999 * 2 *", "o['c_k'] = K5 * 2 *"),
         ("* 398 ** 0.75 * ej2) * 0.999", "* 398 ** 0.75 * ej2) * IC0"),
         ("- 2.1 * bII ** 2; o['m3: m5 >=']", "- A2C * bII ** 2; o['m3: m5 >=']"),
         ("m5c = 1 - o['c_u'] * kEc - 2.1 * bII ** 2", "m5c = 1 - o['c_u'] * kEc - A2C * bII ** 2")]
for a_, b_ in CREPL:
    assert CSRC.count(a_) == 1, a_
    CSRC = CSRC.replace(a_, b_)
FUNCS = {f: inspect.getsource(getattr(PR, f)) for f in ('check_remainders', 'check_steps')}


TOL = 1e-9          # the identities (N1 = eps1 P1, hneg1 = eps_h P4z, B2c + B2s = c_B2 G at a = 4r/sigma, ...) give 1 + 2e-13 in floating point (as in DJ)
def tol(ell): return TOL + 1e-15 * ell      # ... and 1 + 8e-8 at ell = 1e8: the lines are logarithms of size ell (rounding 2.2e-16 ell per operation), as check_steps' 1e-13 ell


def B1(ell, floor):
    return max(floor, 8 * ell + 100)


def namespace(ell, floor=5e5, Bm=None, a2c=2.1):
    """a copy of dj_proof's namespace with the constants of DP-1a at ell (B_m = B_1(ell) unless given)."""
    Bm = B1(ell, floor) if Bm is None else Bm; eta = 1 / ell
    es = 0.25 / Bm; e0 = 2 / math.sqrt(Bm) + es; z2v = 0.5; qden = 8.0; qmax = (1 + eta) / (qden * (1 - eta))
    k5 = (1 - 1e-100) ** 2 * (1 - 4e-100 - z2v / 12); ic0 = ((1 - 3 * PR.ESS(ell)) * (1 - qmax)) ** 0.25
    ns = dict(vars(PR)); ns['ES'] = es; ns['E0'] = e0
    exec(compile(CSRC, 'dj_proof.consts (DP-1a)', 'exec'), ns)
    base = ns['consts']; ns['consts'] = lambda e: base(e, BM=Bm, QDEN=qden, Z2V=z2v, K5=k5, IC0=ic0, A2C=a2c)
    for f, src in FUNCS.items(): exec(compile(src, 'dj_proof.' + f, 'exec'), ns)
    return ns, {'B_m': Bm, 'es': es, 'e0': e0, 'q_max': qmax, 'z2_max': z2v, 'K5': k5, 'IC0': ic0}


def room_sampler(ell, lBlo, lBhi, near=True):
    """dj_proof.sample with B in [e^lBlo, e^lBhi]; a third of the states next to each end."""
    def sample(ell_, rng, n, full=False):
        with SE.band(lBlo, lBhi): Y4, lP, Y5 = PR.sample(ell_, rng, n, full=True)
        Y5 = Y5.copy()
        if near:
            k = len(Y5); idx = rng.permutation(k); a, b = idx[: k // 3], idx[k // 3: 2 * k // 3]
            Y5[a, 2] = lBlo + rng.uniform(0, 1, len(a)); Y5[b, 2] = lBhi - rng.uniform(0, 1, len(b))
        Y5[:, 2] = np.clip(Y5[:, 2], lBlo, lBhi)
        lP = S.lPbar(ell_, Y5[:, 0], Y5[:, 2] - 2 * ell_, Y5[:, 3]) + Y5[:, 4]
        return (Y5[:, :4], lP, Y5) if full else (Y5[:, :4], lP)
    return sample


def text_forms(ns, ell, rng, n):
    """(R1) <= 0.52 es, (R3) <= 0.48 es per side, (R4) in the form of the text, on the states and the a-grid of check_remainders (plus a near 1 and sqrt(b))."""
    Y, lP = ns['sample'](ell, rng, n); Q = PR.state_quantities(ell, Y, lP); o = ns['consts'](ell); es, e0 = ns['ES'], ns['E0']
    lo, hi = J.a_range(ell, Y[:, 1]); g = 40
    lA = lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, g)[None, :]
    lA = np.concatenate([lA, np.clip(np.array([-3.0, -1.0, -1e-9, 1e-9, 1.0, 3.0])[None, :] + 0 * lo[:, None], lo[:, None], hi[:, None]),
                         np.clip(0.5 * Q['lb'][:, None] + np.array([-1.0, 0.0, 1.0])[None, :], lo[:, None], hi[:, None])], axis=1)
    V, aux = PR._lines_on(ell, Y, lP, lA); S_ = PR._sum; les = math.log(es)
    def mx(d, mask=None):
        d = np.where(np.isnan(d), -np.inf, d)
        if mask is not None: d = np.where(mask, d, -np.inf)
        m = float(np.max(d)); return float(np.exp(min(m, 700.0))) if np.isfinite(m) else 0.0
    with np.errstate(all='ignore'):
        r1 = S_(V, ('N2', 'd3', 'N4', 'ring2', 'A2a', 'A2b', 'B2b')) - V['P1'][1]; s3 = S_(V, ('A1w', 'B1w1', 'B1w2'))
        return {'R1 (text): (N2 + d3 + N4 + ring2 + A2a + A2b + B2b)/P1 against 0.52 es': mx(r1 - les - math.log(0.52)),
                'R3 (text, a <= 1): (A1w + B1w1 + B1w2)/P4z against 0.48 es': mx(s3 - V['P4z'][1] - les - math.log(0.48), lA <= 0),
                'R3 (text, a >= 1): (A1w + B1w1 + B1w2)/P1 against 0.48 es': mx(s3 - V['P1'][1] - les - math.log(0.48), lA >= 0),
                'R4 (text): (N3 + M0Xi + A1v + pair)/((e0 - es)(P1 + P4z))': mx(S_(V, ('N3', 'M0Xi', 'A1v', 'pair')) - S_(V, ('P1', 'P4z')) - math.log(e0 - es)),
                'POWER: R1 against 0.26 es (must exceed 1)': mx(r1 - les - math.log(0.26))}


def _widen(ns, ell, Y, lP, rng, reps=40):
    Q = PR.state_quantities(ell, Y, lP); reg = PR.rule(ell, Q)
    with np.errstate(all='ignore'):
        lxi = Q['lr'] + 0.5 * Q['lmu'] + ell
    base = Y[(reg == 3) & (lxi >= 2 * math.log(ell) - 2)]
    if len(base) == 0: return Y, lP
    Z = np.repeat(base, reps, axis=0).copy(); Z[:, 3] = Z[:, 3] - rng.uniform(0, 2 * ell, len(Z)); R = S.ranges(ell); Z[:, 3] = np.maximum(Z[:, 3], R[3, 0])
    lPz = S.lPbar(ell, Z[:, 0], Z[:, 2] - 2 * ell, Z[:, 3]) - rng.uniform(0, 2, len(Z)) * (rng.random(len(Z)) < 0.5)
    return np.vstack([Y, Z]), np.concatenate([lP, lPz])


def b5(ns, ell, rng, n):
    """(b.5) on the wide Case II states with Th' < mT + T (check_steps' s4) and ch < mT + Tbar: kappa_b mu <= 1, u > max(6, U); and no state with u < U and v < U."""
    Y, lP = ns['sample'](ell, rng, n); o = ns['consts'](ell); E0 = ns['E0']; eta = 1 / ell
    Y, lP = _widen(ns, ell, Y, lP, rng)                       # more states where (b.5) is used: the wide Case II states found, with kappa lowered
    Q = PR.state_quantities(ell, Y, lP); reg = PR.rule(ell, Q)
    mu = np.exp(Q['lmu']); r = Q['r']; b = Q['b']; ESS = PR.ESS(ell); T = np.exp(Q['lb'] + np.log(Q['k1']) - Q['lG'] + math.log(2 * (1 - eta)))
    with np.errstate(all='ignore'):
        eps1 = eta * Q['kE'] * (2 + r) / (1 + r); epsh = 2 * Q['kE'] * (eta + 0.184) / Q['om']; m1 = 1 - eps1 - E0; m4 = 1 - epsh - E0; m2 = 1 - 3 * ESS; m3 = 1 - ell ** -3
        m5 = 1 - o['c_u'] * np.sqrt(r) - 2.1 * b ** 2; mT = 1 + ESS
        lu = np.log(m1 / (2 * m2)) - Q['lalpha'] - Q['lG']; lv = np.log(m4 * Q['om'] / (2 * m3)) + Q['lb'] - Q['lbeta'] - Q['lG']
        lTh = math.log(2) + 0.5 * (math.log(m2 * m3) + Q['lalpha'] + Q['lbeta']) - Q['lG2']; lch = np.log(np.maximum(m5, 1e-300)) + Q['lchi'] - Q['lG2']
        lxi = Q['lr'] + 0.5 * Q['lmu'] + ell + 0.5 * (math.log(m3 / m2) + np.log1p(-Q['z2'] / 2) - np.log1p(-Q['q']))
        rhob = np.sqrt(m1 / (m4 * Q['om']) * np.exp(-Q['lB']) + np.exp(-2 * lxi)); tgt = mT + T
        Thp = np.exp(np.minimum(lTh, 700.0)) * (1 - rhob / 2)
        s4 = (reg == 3) & (lxi >= 2 * math.log(ell)) & (Thp < tgt)
        Tb = o['tc'] * (4 / 3) * mu * np.exp(-mu) * PR.E_CM(mu, ell) / ell; U = ((mT + Tb) / Thp) ** 2 - 1
        w = s4 & (lch < np.log(mT + Tb))
        lkb = np.maximum(Q['lk'], math.log(16) + Q['lb'] + mu - Q['lmu'])
        out = {'wide Case II states with Th\' < mT + T (s4)': int(s4.sum()), 'of them with ch < mT + Tbar (where (b.5) is used)': int(w.sum()),
               'states with u < U and v < U where (b.5) is used (must be 0)': int((w & (lu < np.log(U)) & (lv < np.log(U))).sum()),
               'states with u < U and v < U on all of s4 (information: there ch >= mT + Tbar closes the claim)': int((s4 & (lu < np.log(U)) & (lv < np.log(U))).sum()),
               'smallest ch - (mT + Tbar) on the s4 states with u < U and v < U (must be >= 0)': float(np.min((np.exp(np.minimum(lch, 700.0)) - (mT + Tb))[s4 & (lu < np.log(U)) & (lv < np.log(U))])) if (s4 & (lu < np.log(U)) & (lv < np.log(U))).any() else None,
               'B < ell^4 on s4 (must be all)': bool(np.all(Q['lB'][s4] < 4 * math.log(ell))) if s4.any() else True,
               'largest log(kappa_b mu) where (b.5) is used (must be <= 0)': float(np.max(lkb[w] + Q['lmu'][w])) if w.any() else None,
               'smallest log u - log max(6, U) where (b.5) is used (must be > 0)': float(np.min(lu[w] - np.log(np.maximum(6.0, U[w])))) if w.any() else None,
               'smallest log u - log max(6, U) on all of s4 (information)': float(np.min(lu[s4] - np.log(np.maximum(6.0, U[s4])))) if s4.any() else None}
    sm = out['smallest ch - (mT + Tbar) on the s4 states with u < U and v < U (must be >= 0)']
    out['ok'] = bool(out['states with u < U and v < U where (b.5) is used (must be 0)'] == 0 and out['B < ell^4 on s4 (must be all)'] and (sm is None or sm >= 0)
                     and (out['largest log(kappa_b mu) where (b.5) is used (must be <= 0)'] is None or out['largest log(kappa_b mu) where (b.5) is used (must be <= 0)'] <= 0)
                     and (out['smallest log u - log max(6, U) where (b.5) is used (must be > 0)'] is None or out['smallest log u - log max(6, U) where (b.5) is used (must be > 0)'] > 0))
    return out


def one(ell, floor=5e5, n=500, seed=4401, lBlo=None, lBhi=None, Bm=None, power=False):
    lBlo = math.log(B1(ell, floor)) if lBlo is None else lBlo; lBhi = 4 * math.log(ell) - 1e-9 if lBhi is None else lBhi             # B < ell^4 (B = ell^4 belongs to DJ-T, (b.6))
    ns, par = namespace(ell, floor, Bm); ns['sample'] = room_sampler(ell, lBlo, lBhi)
    rng = lambda k: np.random.default_rng(seed + 31 * k + int(ell) % 9973)
    out = {'constants': par, 'B range': [math.exp(lBlo), math.exp(lBhi)]}
    rem = ns['check_remainders'](ell, rng(1), n); st = ns['check_steps'](ell, rng(2), n)
    out['remainders (largest ratio/bound, must be <= 1)'] = rem; out['steps'] = st; out['text forms (must be <= 1)'] = text_forms(ns, ell, rng(3), n); out['(b.5)'] = b5(ns, ell, rng(4), n)
    okr = all(v <= 1 + tol(ell) for k, v in rem.items() if isinstance(v, float)); okt = all(v <= 1 + tol(ell) for k, v in out['text forms (must be <= 1)'].items() if not k.startswith('POWER'))
    out['ok'] = bool(okr and st['ok'] and okt and out['(b.5)']['ok'])
    if power:
        p = {}
        rw = ns['check_remainders'](ell, rng(1), n, wrong=0.9); p['bounds x 0.9: items caught (ratio > 1)'] = sorted(k for k, v in rw.items() if isinstance(v, float) and v > 1 + tol(ell))
        p['bounds x 0.9: items not caught (their largest ratio is below 0.9)'] = sorted(k for k, v in rw.items() if isinstance(v, float) and v <= 1 + tol(ell))
        for wv in ('ckap2', 'cJ2', 'w16', 'EJ', 'ECM', 'phi'):
            sw = ns['check_steps'](ell, rng(2), n, wrong=wv); p['steps, wrong version ' + wv] = sorted(k for k, v in sw['smallest slack of every step (must be >= 0)'].items() if v is not None and v < -1e-9)
        p['R1 against 0.26 es caught'] = bool(out['text forms (must be <= 1)']['POWER: R1 against 0.26 es (must exceed 1)'] > 1)
        nsb, _ = namespace(ell, floor, Bm); nsb['sample'] = room_sampler(ell, lBlo - math.log(30), lBlo - math.log(3), near=False)
        rb = nsb['check_remainders'](ell, rng(5), n); sb = nsb['check_steps'](ell, rng(6), n)
        p['B in [B_1/30, B_1/3] with the constants of B_1: remainder items that fail'] = sorted(k for k, v in rb.items() if isinstance(v, float) and v > 1 + tol(ell))
        p['B in [B_1/30, B_1/3] with the constants of B_1: steps that fail'] = sorted(k for k, v in sb['smallest slack of every step (must be >= 0)'].items() if v is not None and v < -1e-9)
        tb = text_forms(nsb, ell, rng(7), n); p['B in [B_1/30, B_1/3]: text forms that fail'] = sorted(k for k, v in tb.items() if v > 1 and not k.startswith('POWER'))
        p['caught: below B_1'] = bool(p['B in [B_1/30, B_1/3] with the constants of B_1: remainder items that fail'] or p['B in [B_1/30, B_1/3] with the constants of B_1: steps that fail'] or p['B in [B_1/30, B_1/3]: text forms that fail'])
        out['power'] = p
    return out


def run(floors=(5e5,), ells=(960.8, 3000.0, 1e4, 1e6, 1e8), n=500, save=True, name='dq_steps'):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'plan': 'DQ_探索計画.md section A'}
    for fl in floors:
        for ell in ells:
            if fl == 0 and 8 * ell + 100 >= 5e5: continue
            r = one(ell, fl, n, power=(ell in (960.8, 1e4))); key = 'B_1 = %s, ell = %s' % ('max(5e5, 8 ell + 100)' if fl > 0 else '8 ell + 100', ell)
            out[key] = r; print(key, r['ok'], round(time.time() - t0), flush=True)
    out['ok'] = bool(all(v['ok'] for k, v in out.items() if k.startswith('B_1')))
    out['power ok'] = bool(all(v['power']['caught: below B_1'] and v['power']['R1 against 0.26 es caught'] for k, v in out.items() if k.startswith('B_1') and 'power' in v))
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/%s.json' % name, 'w'), indent=1)
    return out


if __name__ == '__main__':
    fl = tuple(float(x) for x in sys.argv[1:]) or (5e5,)
    r = run(floors=fl, name='dq_steps' if fl == (5e5,) else 'dq_steps_' + '_'.join('%g' % x for x in fl)); print(r['ok'], r['power ok'])
