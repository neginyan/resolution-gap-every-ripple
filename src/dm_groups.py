"""Stage DM 2.1: RING 2 CLOSED IN THE DOCUMENT -- the 30 groups of table lines against the lemma's pieces, written as formulas.  Python 3.11 grammar.
For every group the lemma's piece (dk_lemma.pieces, Num/sigma units; den pieces times gamma) is rewritten in the table's variables (CLOSED FORM: substitution
only) and then compared with the table's lines (dk_table.lines) by ELEMENTARY INEQUALITIES, as a CHAIN
    v0 = lemma piece  rel1  v1 = closed form  rel2  v2  ...  vn = table (magnitude)
with rel '=' (identity), '>=' (gains: lemma >= ... >= table) or '<=' (losses and den: lemma <= ... <= table).  DO_証明まとめ.md section 8.2 writes the same
chains in words, with the conditions each step uses.  Variables: a = 4 sigma/L^2, A = sigma a/(4 r) = sigma^2/s^2, u = sigma/a = L^2/4, B = b/sigma^2, G = g_s P.
(G1) the closed form equals the lemma's piece (relative 10^{-(digits-12)});  (G2) every step holds;  (G4) the groups add up to the table's Lambda_k and to the
lemma's Phi_k/sigma for every option-branch k (the map of 37 lines and the lemma's pieces).
POWER (WRONG): (W1) the reversed direction of every inequality group must fail somewhere; (W1') a factor dropped from the closed form of every identity group must
fail (G1); (W2) a condition dropped (points outside it) must make the group's direction fail.  -> results/dm_groups.json
The points are those of the ring-2 audit (dk_audit.sample, dk_audit.a_grid: the ends exactly)."""
import json, math, sys, time
from decimal import Decimal as Dc, localcontext
import numpy as np
import dk_lemma as K, dk_table as T, dk_audit as AU

GAIN = ('P1', 'P2z', 'P3z+P4z', 'hFz', 'cKz')
DEN = ('d1', 'd2', 'd3', 'd4')
TAGS = {'P1': ('P1',), 'P2z': ('P2z',), 'P3z+P4z': ('P3z', 'P4z'), 'hFz': ('hFz',), 'cKz': ('cKz',), 'N1': ('N1',), 'N2': ('N2',), 'ring2': ('ring2',),
        'N3': ('N3',), 'N4+N4G': ('N4', 'N4G'), 'hneg1': ('hneg1',), 'M0Xi': ('M0Xi',), 'A1v': ('A1v',), 'A1w': ('A1w',), 'A2k': ('A2k',), 'A2a': ('A2a',),
        'A2b': ('A2b',), 'B1w1': ('B1w1',), 'B1w2': ('B1w2',), 'B2a': ('B2a',), 'B2b': ('B2b',), 'pair': ('pair',), 'FzK': ('FzK',), 'lossK': ('lossK',),
        'FrB2': ('B2c', 'B2s'), 'FrB1': ('B1m', 'B1c', 'B1l', 'uB2c', 'uB2s'), 'd1': ('d1',), 'd2': ('d2',), 'd3': ('d3',), 'd4': ('d4',)}
IDENT = ('P1', 'N1', 'A1w', 'A2k', 'A2a', 'A2b', 'B2a', 'B2b', 'd1', 'd2', 'N3', 'd4')         # closed form = table (N3, d4: with (P3))
COND = {'N3': 'P3', 'N4+N4G': 'P3, P4', 'd4': 'P3', 'FrB1': 'P4, eta', 'FrB2': 'eta', 'hFz': 'z0', 'P3z+P4z': 'w0', 'ring2': 'T2'}
WRONG = {}      # 'drop <group>' (W1'), 'w0 = 0', 'T2 0.79 K' (W2 on the written inequality)


def chains(q, la, c, o, V, gam):
    """group -> [(rel, value, label), ...]; the first entry is the lemma's piece (rel None)."""
    W_ = WRONG.get
    with localcontext(c):
        pi = K.PI(); sqpi = pi.sqrt(); sq2 = Dc(2).sqrt(); e = Dc(1).exp(); e50 = Dc(-50).exp()
        sig, eta, r, b, B, kE, gs, G, P, mu, kap, y, dl, U1, K2, Kk, z02, cd = (q[k] for k in (
            'sig', 'eta', 'r', 'b', 'B', 'kE', 'gs', 'G', 'P', 'mu', 'kap', 'y', 'dl', 'U1', 'K2', 'K', 'z02', 'cd'))
        a = K.D(la).exp(); A = sig * a / (4 * r); u = sig / a; ome = 1 - eta; fl = 1 / (1 + eta)
        X1 = U1 / Dc('0.75'); CZ = eta ** 2 / (e * ome ** 2); Q2 = 1 + eta * kE * r / (1 + r) + 2 * eta * kE / (1 + r)
        w0 = Dc(0) if W_('w0 = 0') else Dc('0.75') / B; om_ = 1 / (1 + w0) ** 2; yh = 1 / (2 * B); z2 = K2 * yh; brk = 1 - (4 * b / (1 - b) + z2 / 12)
        Gmu = min(G / mu, 2 * Dc('0.0625') * Dc('1e-6').exp() * gs)
        M4c = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2; M4w = M4c + Dc('1.5') * G / (mu * (2 + r) ** 2 * ome)
        fF = G / (4 * ome); fFs = fF * (kap / (2 * B)).sqrt(); cs = (CZ / 2).sqrt() + r / (pi * (2 + r)).sqrt(); sA = A.sqrt(); sa = a.sqrt(); ss = sig.sqrt()
        t = lambda *tags: sum(abs(V[k]) for k in tags)
        dr = lambda g: (Dc('1.01') if W_('drop ' + g) else Dc(1))                                  # (W1'): a factor changed in the closed form
        C = {}
        C['P1'] = [(None, o['P1'], 'lemma'), ('=', a / 2 * dr('P1'), 'a/2'), ('=', t('P1'), 'table')]
        cf = fl * G * a / (4 * mu * r * (2 + r))
        C['P2z'] = [(None, o['P2'] - o['ring1'], 'lemma'), ('=', cf * (1 - (1 - b) ** 2 * K2 * (1 + eta) / (8 * B * ome)), 'closed'),
                    ('>=', cf * (1 - K2 * (1 + eta) / (8 * B * ome)), '(1-b)^2 <= 1'), ('=', t('P2z'), 'table')]
        # without cancellation: d_y := 1 - (1-y) e^{-y/2} = 1 - e^{-(y/2 - ln(1-y))},  d_w := 1 - omega = w0 (2 + w0)/(1 + w0)^2
        dy = K.om(y / 2 + K.lm1(y, c), c); dw = w0 * (2 + w0) / (1 + w0) ** 2; h = b / (2 * sig)
        C['P3z+P4z'] = [(None, o['M0 b Psi0'], 'lemma'), ('=', h * K.om(u + y / 2 + K.lm1(y, c), c), 'closed: h (1 - (1-y) e^{-y/2} e^{-u})'),
                        ('>=', h * (u + dy) / (1 + u), 'e^-u <= 1/(1+u)'),
                        ('>=', h * (om_ * u / (1 + u) + min(dy, dw)), 'numerator >= min(1-c_y, 1-omega)(1+u)'),
                        ('>=', h * (om_ * u / (1 + u) + Dc('1.5') * y / (1 + w0)), 'min >= 1.5 y/(1+w0)'),
                        ('=', (b / 2) * om_ / (a + sig) + Dc('0.375') * sig * (1 - b) ** 2 / (1 + w0) if W_('w0 = 0') else t('P3z', 'P4z'), 'table')]
        v = r * sig / (a * (2 + r)); pre = G * (1 - z02 / 2) / (4 * sig * (1 + eta))
        C['hFz'] = [(None, o['hF'], 'lemma'), ('=', pre * K.om(v, c), 'closed'), ('>=', pre * v / (1 + v), '1-e^-v >= v/(1+v)'),
                    ('>=', fl * (G / 4) * (r / (2 + r)) * (1 - z02 / 2) / (a + sig), 'r sigma <= (2+r) sigma'),
                    ('>=', fl * (G / 4) * (r / (2 + r)) * (1 - z2 / 2) / (a + sig), 'z0^2 <= z2'), ('=', t('hFz'), 'table')]
        kc = (1 - b) ** 2 * kap * G * fl / (8 * B * sig)
        C['cKz'] = [(None, o['chirp'], 'lemma'), ('=', (cd if cd > 0 else Dc(0)) * kc, 'closed'), ('>=', (brk / 2 if brk > 0 else Dc(0)) * kc, 'c_delta >= brk/2'),
                    ('=', t('cKz'), 'table')]
        C['N1'] = [(None, o['N1'], 'lemma'), ('=', eta * kE * (2 + r) * a / (2 * (1 + r)) * dr('N1'), 'closed'), ('=', t('N1'), 'table')]
        C['N2'] = [(None, o['N2'], 'lemma'), ('=', (1 - b) ** 2 * Q2 * a / (16 * B), 'closed'), ('<=', Q2 * a / (16 * B), '(1-b)^2 <= 1'), ('=', t('N2'), 'table')]
        rg = eta ** 2 * gs * a * sig ** 4 * e50 / (16 * B * r * (2 + r) * ome)
        C['ring2'] = [(None, o['ring2'], 'lemma'), ('=', (1 - b) ** 2 * rg * 2 * (Kk + 1 / Kk) / (2 * pi).sqrt(), 'closed (phi(K) = sigma^4 e^-50/sqrt(2 pi))'),
                      ('<=', rg * (Dc('0.79') * Kk if W_('T2 0.79 K') else Dc('0.8') * (Kk + 1)), '(1-b)^2 <= 1, 2(K+1/K)/sqrt(2pi) <= 0.8(K+1)'),
                      ('=', t('ring2') if not W_('T2 0.79 K') else rg * Dc('0.79') * Kk, 'table')]
        C['N3'] = [(None, o['N3'], 'lemma'), ('=', sig / 2 * M4w * dr('N3'), 'closed'), ('=', sig / 2 * (M4c + Dc('1.5') * Gmu / ((2 + r) ** 2 * ome)), '(P3): G/mu = G_mu'),
                   ('=', t('N3'), 'table')]
        jj = (a / (4 * sig)) * Q2 + G * a / (8 * mu * r * sig * (2 + r) * ome)
        C['N4+N4G'] = [(None, o['N4'], 'lemma'), ('=', Dc('1.5') * sig * (sig ** 2 * (X1 ** 2 + CZ * A) * jj + sig ** 2 * a ** 2 * M4w / 16), 'closed'),
                       ('<=', Dc('1.5') * sig * (sig ** 2 * (X1 ** 2 + CZ) * jj + sig ** 2 * a * (4 * r / sig) * M4w / 16), '(P4) A <= 1 twice'),
                       ('=', Dc('1.5') * sig * (sig ** 2 * (X1 ** 2 + CZ) * ((a / (4 * sig)) * Q2 + Gmu * a / (8 * r * sig * (2 + r) * ome))
                                                + sig ** 2 * a * (4 * r / sig) * (M4c + Dc('1.5') * Gmu / ((2 + r) ** 2 * ome)) / 16), '(P3): G/mu = G_mu'),
                       ('=', t('N4', 'N4G'), 'table')]
        vp = r * sig / (a * (1 + r)); pr = kE * b * (eta + Dc('0.184'))
        C['hneg1'] = [(None, o['M0 R_theta, t_rho'], 'lemma'), ('=', pr / (2 * sig) * K.om(vp, c), 'closed'), ('<=', pr / (2 * sig) * min(Dc(1), vp), '1-e^-v <= min(1, v)'),
                      ('<=', pr / (a + sig), 'a <= sigma or a >= sigma'), ('=', t('hneg1'), 'table')]
        C['M0Xi'] = [(None, o['M0 Xi'], 'lemma'), ('=', sig * (1 - b) ** 2 * Dc('0.25') * Dc('2.07') * kE / 4, 'closed'),
                     ('<=', sig * Dc('0.25') * Dc('2.07') * kE / 4, '(1-b)^2 <= 1'), ('=', t('M0Xi'), 'table')]
        C['A1v'] = [(None, o['A1v'], 'lemma'), ('=', sig ** 2 * (1 - b) * (Dc('7.5') * B).sqrt() * kE * P.sqrt() / 4, 'closed'),
                    ('<=', sig ** 2 * (Dc('7.5') * B).sqrt() * kE * P.sqrt() / 4, '1-b <= 1'), ('=', t('A1v'), 'table')]
        C['A1w'] = [(None, o['A1w'], 'lemma'), ('=', sig ** 2 * ss * B * (1 + eta) * sa / (4 * sqpi) * dr('A1w'), 'closed'), ('=', t('A1w'), 'table')]
        C['A2k'] = [(None, o['A2k'], 'lemma'), ('=', sig ** 3 * B * kap * G / (8 * ome) * dr('A2k'), 'closed'), ('=', t('A2k'), 'table')]
        C['A2a'] = [(None, o['A2a'], 'lemma'), ('=', sig ** 4 * B * (1 + eta * kE * r / (1 + r)) * a / 8 * dr('A2a'), 'closed'), ('=', t('A2a'), 'table')]
        C['A2b'] = [(None, o['A2b'], 'lemma'), ('=', sig ** 4 * B * eta ** 2 * gs * a / (8 * r * (2 + r) * ome) * dr('A2b'), 'closed'), ('=', t('A2b'), 'table')]
        C['B1w1'] = [(None, o['B1w1'], 'lemma'), ('=', B * sig ** 2 * ss * (Dc('0.184') + y) * (r / (1 + r)) * sa / (2 * sqpi), 'closed'),
                     ('<=', B * sig ** 2 * ss * (Dc('0.184') + yh) * (r / (1 + r)) * sa / (2 * sqpi), 'y <= 1/(2B)'), ('=', t('B1w1'), 'table')]
        C['B1w2'] = [(None, o['B1w2'], 'lemma'), ('=', B * sig ** 2 * ss * eta ** 2 * (1 + y / 2) * sa / (2 * sqpi * (2 + r) * ome), 'closed'),
                     ('<=', B * sig ** 2 * ss * eta ** 2 * (1 + yh / 2) * sa / (2 * sqpi * (2 + r) * ome), 'y <= 1/(2B)'), ('=', t('B1w2'), 'table')]
        C['B2a'] = [(None, o['B2a'], 'lemma'), ('=', sig ** 2 * B.sqrt() * U1 * kap.sqrt() * G / (4 * ome ** 2) * dr('B2a'), 'closed'), ('=', t('B2a'), 'table')]
        C['B2b'] = [(None, o['B2b'], 'lemma'), ('=', sig ** 3 * (2 * B).sqrt() * P.sqrt() * a / 8 * (kE * r / (1 + r) + eta ** 2 / ((r * (2 + r)).sqrt() * (2 + r) * ome ** 2)) * dr('B2b'),
                                                  'closed'), ('=', t('B2b'), 'table')]
        pf = sig ** 3 * U1 ** 2 * gs * e50; s2p = (2 * pi).sqrt()
        cl = pf * ((4 / Kk + 2 * dl * y.sqrt()) / (2 * s2p * ome) + ((cd * y * (Kk + 1 / Kk) / (s2p * (1 + eta))) if cd > 0 else Dc(0)))
        C['pair'] = [(None, o['tails'] + o['chirp tail'], 'lemma (Tz; Bz: tails only, Fz: none)'), ('=', cl, 'closed'),
                     ('<=', pf / ome * (Dc('1.6') + Dc('0.2') * (Kk + 1)), 'K >= 1, delta <= 2, y <= 1, c_delta <= 1/2'), ('<=', pf / ome * Dc('0.4') * (Kk + 5), '1.8 + 0.2K <= 0.4(K+5)'),
                     ('=', t('pair'), 'table')]
        C['FzK'] = [(None, o['FzK'], 'lemma'), ('=', sig * (1 - b) * kap * G / (4 * ome), 'closed'), ('<=', sig * kap * G / (4 * ome), '1-b <= 1'), ('=', t('FzK'), 'table')]
        C['lossK'] = [(None, o['lossK'], 'lemma'), ('=', (-cd if cd < 0 else Dc(0)) * (1 - b) ** 2 * kap * G / (8 * B * sig * ome), 'closed'),
                      ('<=', (-brk if brk < 0 else Dc(0)) * kap * G / (16 * B * sig * ome), '-2 c_delta <= -brk, (1-b)^2 <= 1'), ('=', t('lossK'), 'table')]
        C['FrB2'] = [(None, o['FrB2'], 'lemma'), ('=', fF * (U1 / (sq2 * ome) + cs * sA), 'closed'), ('<=', fF * (X1 / sq2 + cs * sA), '1/(1-eta) <= 4/3'),
                     ('=', t('B2c', 'B2s'), 'table')]
        c0h = U1 / (sq2 * ome) + (CZ / 2).sqrt() * sA; mm = 2 * r.sqrt() / ((pi * (2 + r)).sqrt() * sa)
        C['FrB1'] = [(None, o['FrB1'], 'lemma'),
                     ('=', fF * (ss * c0h * mm + sig * r / (2 * (2 + r)) + sig * c0h ** 2 + sig ** 2 * a * r / (8 * (2 + r))) + (1 - b) * fFs * (U1 / (sq2 * ome) + cs * sA), 'closed'),
                     ('<=', fF * (ss * (X1 / sq2) * mm + sig * r / (2 * (2 + r)) + sig * c0h ** 2 + sig ** 2 * a * r / (8 * (2 + r))) + (1 - b) * fFs * (U1 / (sq2 * ome) + cs * sA),
                      'c0hat <= X1/sqrt2 (U1 (4/3 - 1/(1-eta)) >= sqrt(CZ), A <= 1)'),
                     ('<=', fF * (ss * (X1 / sq2) * mm + sig * r / (2 * (2 + r)) + sig * (X1 ** 2 + CZ) + sig ** 2 * a * r / (8 * (2 + r))) + (1 - b) * fFs * (U1 / (sq2 * ome) + cs * sA),
                      'c0hat^2 <= X1^2 + CZ'),
                     ('<=', fF * (ss * (X1 / sq2) * mm + sig * ((CZ / (2 * pi * (2 + r))).sqrt() + r / (2 * (2 + r)) + X1 ** 2 + CZ) + sig ** 2 * a * r / (8 * (2 + r)))
                      + fFs * (X1 / sq2 + cs * sA), 'the extra sqrt(CZ/(2 pi (2+r))), 1-b <= 1, 1/(1-eta) <= 4/3'),
                     ('=', t('B1m', 'B1c', 'B1l', 'uB2c', 'uB2s'), 'table')]
        C['d1'] = [(None, gam * o['den d1'], 'lemma x gamma'), ('=', gam * b * (1 + (eta + Dc('0.184')) * kE) * dr('d1'), 'closed'), ('=', t('d1'), 'table')]
        C['d2'] = [(None, gam * o['den d2'], 'lemma x gamma'), ('=', gam * G / (2 * ome) * dr('d2'), 'closed'), ('=', t('d2'), 'table')]
        C['d3'] = [(None, gam * o['den d3'], 'lemma x gamma'), ('=', gam * sig * a * (1 + eta * kE * (2 + r) / (1 + r)) / 4, 'closed'),
                   ('<=', gam * sig * a * (1 + 2 * eta * kE) / 4, '(2+r)/(1+r) <= 2'), ('=', t('d3'), 'table')]
        C['d4'] = [(None, gam * o['den d4'], 'lemma x gamma'), ('=', gam * sig * G * a / (8 * mu * r * (2 + r) * ome) * dr('d4'), 'closed'),
                   ('=', gam * sig * Gmu * a / (8 * r * (2 + r) * ome), '(P3): G/mu = G_mu'), ('=', t('d4'), 'table')]
    return C


def check_chain(ch, c):
    """(ok, list of failing steps, strict gap of the whole chain relative to its size)."""
    with localcontext(c):
        tol = Dc(10) ** (12 - c.prec); bad = []
        for i in range(1, len(ch)):
            rel, x, lab = ch[i]; p = ch[i - 1][1]; sc = max(abs(x), abs(p))
            if sc == 0: continue
            if rel == '=': ok = abs(x - p) <= tol * sc
            elif rel == '>=': ok = p >= x - tol * sc
            else: ok = p <= x + tol * sc
            if not ok: bad.append((i, lab, str((x - p) / sc)[:24]))
        l0, ln = ch[0][1], ch[-1][1]; sc = max(abs(l0), abs(ln))
        gap = Dc(0) if sc == 0 else abs(l0 - ln) / sc
    return not bad, bad, gap


def coverage(q, o, V, tot, gam, brk, C, c):
    """the groups add up to Lambda_k (table) and Phi_k/sigma (lemma) for each option-branch k: largest relative difference."""
    with localcontext(c):
        base = [g for g in TAGS if g not in ('hFz', 'cKz', 'FzK', 'lossK', 'FrB2', 'FrB1')]
        extra = {'Fz': ['FzK'], 'TzB2': ['hFz', 'cKz', 'FrB2'], 'TzB1': ['hFz', 'cKz', 'FrB1'], 'BzB2': ['hFz', 'lossK', 'FrB2'], 'BzB1': ['hFz', 'lossK', 'FrB1']}
        worst = Dc(0)
        for k, ex in extra.items():
            if k.startswith('Tz') and not brk > 0: continue
            if k not in tot: return Dc(1)
            sgn = lambda g: (1 if g in GAIN else -1)
            lam_t = sum(V[x] for x in T.SHARED + T.OPT[k]); lam_g = sum(sgn(g) * C[g][-1][1] for g in base + ex)
            pairl = {'Fz': Dc(0), 'TzB2': o['tails'] + o['chirp tail'], 'TzB1': o['tails'] + o['chirp tail'], 'BzB2': o['tails'], 'BzB1': o['tails']}[k]
            phi_g = sum(sgn(g) * C[g][0][1] for g in base + ex if g != 'pair') - pairl
            sc = sum(abs(C[g][0][1]) + abs(C[g][-1][1]) for g in base + ex) + Dc(10) ** (-c.prec)
            worst = max(worst, abs(lam_t - lam_g) / sc, abs(tot[k] - phi_g) / sc)
    return worst


def run_ell(ell, n=400, m=25, seed=11, modify=None):
    """the chains at the audit's points; modify(q, la, c) -> (q, la) for the condition-dropped versions."""
    t0 = time.time(); rng = np.random.default_rng(seed + int(ell) % 100000); states, fam = AU.sample(ell, rng, n); c = K.context(ell); gam = AU.gamma(ell, c)
    R = {g: {'points': 0, 'fail': 0, 'first fail': None, 'max gap': Dc(0), 'lemma zero': 0} for g in TAGS}; cov = Dc(0); npts = 0; exc = []
    for i, st in enumerate(states):
        try:
            las = AU.a_grid(ell, st[1], st[2], c, m)
            for la in las:
                q = K.state(ell, *st, c); q['gam'] = gam
                if modify: q, la = modify(q, la, c)
                TT, brk = T.lines(q, c, gam); o, tot, alt, sc = K.pieces(q, la, c)
                with localcontext(c): V = {k: T.value(TT, k, la, q['sig'], c) for k in TT}
                C = chains(q, la, c, o, V, gam); npts += 1
                if not modify: cov = max(cov, coverage(q, o, V, tot, gam, brk, C, c))
                for g, ch in C.items():
                    rr = R[g]; rr['points'] += 1
                    if ch[0][1] == 0 and ch[-1][1] == 0: rr['lemma zero'] += 1; continue
                    ok, bad, gap = check_chain(ch, c)
                    if not ok:
                        rr['fail'] += 1
                        if rr['first fail'] is None: rr['first fail'] = {'family': fam[i], 'state': [str(x)[:16] for x in st], 'la': str(la)[:16], 'steps': bad[:3]}
                    rr['max gap'] = max(rr['max gap'], gap)
        except Exception as ex:
            exc.append({'family': fam[i], 'error': repr(ex)[:200]})
    out = {'ell': ell, 'points': npts, 'digits': c.prec, 'exceptions': exc[:5], 'number of exceptions': len(exc), 'seconds': time.time() - t0,
           'groups': {g: {'points': v['points'], 'failing points': v['fail'], 'first failure': v['first fail'], 'largest |lemma - table|/size': float(v['max gap']),
                          'lemma and table both 0': v['lemma zero']} for g, v in R.items()}}
    if not modify: out['coverage: largest relative difference (sums of the groups vs Lambda_k and Phi_k)'] = float(cov)
    return out


# ---- the condition-dropped versions (W2)
def _P_above(q, la, c):
    with localcontext(c):
        q['P'] = q['mu'] / 8 * Dc(3).exp(); q['G'] = q['gs'] * q['P']; q['W'] = q['G'] / 2
    return q, la


def _A_above(q, la, c):
    with localcontext(c): return q, Dc(4).ln() + q['r'].ln() + q['ell'] + 2


def _A_far(q, la, c):
    with localcontext(c): return q, Dc(4).ln() + q['r'].ln() + q['ell'] + 12


def _eta03(q, la, c):
    q['eta'] = Dc('0.3'); return q, la


def _z0_big(q, la, c):
    with localcontext(c):
        q['B'] = q['K2'] / 8; q['b'] = q['B'] * q['sig'] ** 2; b = q['b']
        q['y'] = (1 - b) ** 2 / (2 * q['B']); q['dl'] = 2 * b / (1 - b); q['z02'] = q['K2'] * q['y']; q['cd'] = Dc('0.5') - q['dl'] - q['z02'] / 24
    return q, la


W2 = {'P > mu/8 (P = e^3 mu/8): N3, N4+N4G, d4': (_P_above, ('N3', 'N4+N4G', 'd4')), 'A > 1 (a = e^2 4r/sigma): N4+N4G': (_A_above, ('N4+N4G',)),
      'A >> 1 (a = e^12 4r/sigma; FrB1 holds up to A ~ 5e3): FrB1': (_A_far, ('FrB1',)),
      'eta = 0.3 > 1/4: FrB2, FrB1': (_eta03, ('FrB2', 'FrB1')), 'z0^2 > 2 (B = K^2/8): hFz': (_z0_big, ('hFz',))}
W2b = {'w0 = 0 (no w0 >= 3y/2): P3z+P4z': ('w0 = 0', ('P3z+P4z',)), 'T2(K) bound 0.79 K: ring2': ('T2 0.79 K', ('ring2',))}


def power(ells=(55.26, 955.8), n=60, m=9):
    out = {'W1 reversed (inequality groups: the strict gap must be positive somewhere)': {}, "W1' a factor changed (identity groups)": {}, 'W2 condition dropped': {},
           'resolution of the gap (10^(12 - digits))': {}}
    for ell in ells:
        base = run_ell(ell, n, m, seed=23); out['resolution of the gap (10^(12 - digits))'][str(ell)] = 10.0 ** (12 - base['digits'])
        out['W1 reversed (inequality groups: the strict gap must be positive somewhere)'][str(ell)] = {g: v['largest |lemma - table|/size'] for g, v in base['groups'].items() if g not in IDENT}
        d = {}
        for g in IDENT:
            WRONG.clear(); WRONG['drop ' + g] = True
            r = run_ell(ell, n, m, seed=23); d[g] = r['groups'][g]['failing points']
        WRONG.clear(); out["W1' a factor changed (identity groups)"][str(ell)] = d
        w = {}
        for nm, (f, gs) in W2.items():
            r = run_ell(ell, n, m, seed=23, modify=f); w[nm] = {g: r['groups'][g]['failing points'] for g in gs}
        for nm, (flag, gs) in W2b.items():
            WRONG.clear(); WRONG[flag] = True; r = run_ell(ell, n, m, seed=23); w[nm] = {g: r['groups'][g]['failing points'] for g in gs}
        WRONG.clear(); out['W2 condition dropped'][str(ell)] = w
        print('power', ell, flush=True)
    rv = out['W1 reversed (inequality groups: the strict gap must be positive somewhere)']
    res = out['resolution of the gap (10^(12 - digits))']
    out['reversal caught (gap > 10 x resolution at some ell)'] = {g: any(rv[e][g] > 10 * res[e] for e in rv) for g in rv[str(ells[0])]}
    out['ok'] = bool(all(out['reversal caught (gap > 10 x resolution at some ell)'].values())
                     and all(v > 0 for e in out["W1' a factor changed (identity groups)"].values() for v in e.values())
                     and all(any(out['W2 condition dropped'][e][nm][g] > 0 for e in out['W2 condition dropped']) for nm in out['W2 condition dropped'][str(ells[0])]
                             for g in out['W2 condition dropped'][str(ells[0])][nm]))
    # W2: caught at SOME ell (the condition is used by the written proof; where the slack of the table is larger, e.g. FrB1 at large ell, the inequality
    # holds a little outside the condition, which is reported, not hidden)
    return out


def run(ells=(55.26, 955.8, 1e6, 1e12), n=400, m=25, save=True, fn='results/dm_groups.json'):
    t0 = time.time(); out = {}
    for ell in ells:
        r = run_ell(ell, n, m); out[str(ell)] = r
        print(ell, r['points'], {g: v['failing points'] for g, v in r['groups'].items() if v['failing points']}, r.get('coverage: largest relative difference (sums of the groups vs Lambda_k and Phi_k)'),
              round(r['seconds']), flush=True)
    out['ok'] = bool(all(all(v['failing points'] == 0 for v in r['groups'].values()) and r['number of exceptions'] == 0
                         and r['coverage: largest relative difference (sums of the groups vs Lambda_k and Phi_k)'] < 1e-40 for r in out.values()))
    out['power'] = power(); out['power ok'] = out['power']['ok']; out['seconds'] = time.time() - t0
    if save: json.dump(out, open(fn, 'w'), indent=1, default=str)
    return out


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'quick':
        r = run_ell(55.26, 20, 9); print({g: (v['failing points'], v['first failure']) for g, v in r['groups'].items() if v['failing points']}, r['coverage: largest relative difference (sums of the groups vs Lambda_k and Phi_k)'], r['number of exceptions'], r['exceptions'][:2])
    else:
        r = run(); print(r['ok'], r['power ok'])
