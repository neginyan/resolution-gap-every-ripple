"""AUDIT GUIDE (stage DN; the computation below is unchanged):
  WHAT: the lemma side of ring 2 -- the pieces of the lower bound Phi_k of (Num - gamma sigma den) at one state and one a, in decimal with the exponent range
  and the precision derived below.  WHERE: DO_証明まとめ.md section 8.1 (the lemmas and their conditions), section 8.2 (each piece rewritten in the table's
  variables: dm_groups.chains), appendix A.6 (the statements and proofs of CZ-1, CZ-2, CZ-4, CZ-5) and Lemma R_theta of paper H v1.1 sec. 8.
Stage DK 2.1: THE LEMMA SIDE OF RING 2, written once more in decimal arithmetic for the whole range of Theorem DJ-T.  Python 3.11 grammar.

WHAT IS WRITTEN.  At one state (ell, log mu, log r, log B, log kappa, log P) and one a (a = 4 sigma/L^2 = 4 r sigma/s^2, the table's a'), the pieces of the
lower bound Phi_k of (Num - gamma sigma den) given by
  - Lemma R_theta, w-branch and den (co_remainders.py: N1 ... N4, Dn1 ... Dn3), with the N2 ring average by Lemma CZ-4;
  - Lemmas CZ-1 ... CZ-5 (report CZ, section 3; cz_pair.py): the direct v-branch 2N = (I) + (II) + (III) >= M0 - |A1| - |A2| - |B1w| - |B2| + [(III) + B1v],
    [(III) + B1v] >= the bound of CZ-5 (c), (d) (options Tz, Bz; branch B2 with FrB2, branch B1 with FrB1) or >= -sigma^2 (1-b) kappa W/(1-eta) (option Fz).
The formulas are those of cz_point.point / cz_point.lemma_lines / da_linecheck.lemma_pieces (stages CZ, DA), with the inputs as LOGARITHMS (mu = e^{-3 ell},
kappa = e^{3 ell}, P underflow or overflow in floats).  One deliberate difference: c0 of CZ-5 (d) uses |chi_v| <= sigma U1/(sqrt2 (1 - eta)) as the lemma
states it (h >= 1 - eta); cz_point used the cruder 1 - Qb (also valid).  The pieces are returned in Num/sigma units (each 2 A_w piece / sigma, each 2N piece
/ (2 sigma), each den piece with gamma = 1, i.e. gamma sigma den / sigma = den).

PRECISION [derivation; DK_探索計画.md section 3].
  (1) exponent range 10^{+-10^17} (sigma^6 = e^{-6 ell} stays representable up to ell = 10^12; the default 10^{+-999999} underflows sigma^4 for ell > 5.7e5);
  (2) the inputs are exact (the binary value of the float), and decimal exp is correctly rounded: relative error 10^{-p} whatever the size of the argument;
  (3) 1 - e^{-x}, -ln(1 - y), ln(1 + e) by their series below 1e-8 (N = ceil(p/8) + 2 terms, remainder < x^{N+1} < 10^{-p}), directly with p + 10 digits
      above; e^{-x} = 0 for x > 1e6 (it only enters as 1 - (1-y) e^{-x});
  (4) p = 60 + 2 ceil(log10 ell) digits; the self-check (dk_audit) recomputes at p + 40.
The switches NAIVE (the default exponent range and the four-term series of cz_point) are the deliberately wrong precision versions of the power check."""
import math
from decimal import Decimal as Dc, localcontext, Context
QB = Dc('0.25'); C2 = Dc('0.184'); M4 = Dc('2.07')
NAIVE = {'range': False, 'om': False}


def prec_for(ell, extra=0):
    return 60 + 2 * max(1, math.ceil(math.log10(max(float(ell), 10.0)))) + extra


def context(ell, extra=0):
    c = Context(prec=prec_for(ell, extra), Emax=10 ** 17, Emin=-10 ** 17)
    if NAIVE['range']: c.Emax, c.Emin = 999999, -999999
    c.traps[__import__('decimal').Underflow] = False; c.traps[__import__('decimal').Overflow] = True
    return c


def D(v):
    """the exact decimal value of a float (or an int / Decimal)."""
    return v if isinstance(v, Dc) else Dc(float(v)) if not isinstance(v, int) else Dc(v)


def _nterms(c):
    return c.prec // 8 + 2


def om(x, c):
    """1 - e^{-x}, x >= 0."""
    if NAIVE['om']:
        return x * (1 - x / 2 + x * x / 6 - x ** 3 / 24) if abs(x) < Dc('1e-12') else 1 - (-x).exp()
    if x > Dc(10) ** 6: return Dc(1)
    if x < Dc('1e-8'):
        s = Dc(0); t = x
        for k in range(1, _nterms(c) + 1):
            s += t if k % 2 else -t
            t = t * x / (k + 1)
        return s
    with localcontext(c) as c2:
        c2.prec = c.prec + 10; v = 1 - (-x).exp()
    return +v


def lm1(y, c):
    """-ln(1 - y), 0 <= y < 1."""
    if NAIVE['om']:
        return y + y * y / 2 + y ** 3 / 3 if abs(y) < Dc('1e-12') else -(1 - y).ln()
    if y < Dc('1e-8'):
        s = Dc(0); t = y
        for k in range(1, _nterms(c) + 1):
            s += t / k; t = t * y
        return s
    with localcontext(c) as c2:
        c2.prec = c.prec + 10; v = -(1 - y).ln()
    return +v


def l1p(e, c):
    """ln(1 + e), e >= 0."""
    if e < Dc('1e-8'):
        s = Dc(0); t = e
        for k in range(1, _nterms(c) + 1):
            s += t / k if k % 2 else -t / k; t = t * e
        return s
    with localcontext(c) as c2:
        c2.prec = c.prec + 10; v = (1 + e).ln()
    return +v


def state(ell, lmu, lr, lB, lk, lP, c, eta=None):
    """the a-free quantities of a state (a dict of Decimals)."""
    q = {}
    with localcontext(c):
        L = D(ell); q['ell'] = L; q['sig'] = (-L).exp(); q['eta'] = 1 / L if eta is None else D(eta)                               # DX: eta separated (None: 1/ell)
        q['mu'] = D(lmu).exp(); q['r'] = D(lr).exp(); q['B'] = D(lB).exp(); q['kap'] = D(lk).exp(); q['P'] = D(lP).exp()
        q['b'] = q['B'] * q['sig'] ** 2; r = q['r']; b = q['b']
        q['kE'] = (r / (1 + r)).sqrt(); q['gs'] = (r / (2 + r)).sqrt(); q['W'] = q['gs'] * q['P'] / 2; q['G'] = q['gs'] * q['P']
        q['y'] = (1 - b) ** 2 / (2 * q['B']); q['dl'] = 2 * b / (1 - b)
        q['U1'] = QB * (2 * L + Dc('3.1')).sqrt() + Dc('1e-6')
        q['K2'] = 8 * L + 100; q['K'] = q['K2'].sqrt(); q['z02'] = q['K2'] * q['y']
        q['phiK'] = (-q['K2'] / 2).exp() / (2 * PI()).sqrt()
        q['QK'] = q['phiK'] / q['K']; q['T2K'] = 2 * q['phiK'] * (q['K'] + 1 / q['K'])
        q['cd'] = Dc('0.5') - q['dl'] - q['z02'] / 24
    return q


_PI = {}
def PI():
    p = __import__('decimal').getcontext().prec
    if p not in _PI:
        with localcontext() as c2:
            c2.prec = p + 10; s = Dc(0); k = 0
            # Machin: pi = 16 atan(1/5) - 4 atan(1/239)
            def atan_inv(n):
                x = Dc(1) / n; x2 = x * x; t = x; s_ = Dc(0); j = 0
                while True:
                    term = t / (2 * j + 1)
                    if term == 0 or abs(term) < Dc(10) ** (-(c2.prec + 2)): break
                    s_ += term if j % 2 == 0 else -term; t *= x2; j += 1
                return s_
            v = 16 * atan_inv(5) - 4 * atan_inv(239)
        _PI[p] = +v
    return _PI[p]


def pieces(q, la, c, sharp_c0=True):
    """the lemma's pieces at a = e^{la}, in Num/sigma units (dict name -> Decimal >= 0) and the totals Phi_k/sigma (gamma = q.get('gam', 1)).
    Gains: 'P1', 'P2-ring1', 'M0 b Psi0', 'hF', 'chirp'; losses: the rest; den: 'den d1' ... 'den d4'."""
    with localcontext(c):
        pi = PI(); sq2 = Dc(2).sqrt()
        sig, eta, r, b, B, kE, gs, W, P, mu, kap, y, dl = (q[k] for k in ('sig', 'eta', 'r', 'b', 'B', 'kE', 'gs', 'W', 'P', 'mu', 'kap', 'y', 'dl'))
        U1, K2, T2K, phiK, QK, z02, cd = (q[k] for k in ('U1', 'K2', 'T2K', 'phiK', 'QK', 'z02', 'cd'))
        a = D(la).exp()
        s2 = 4 * r * sig / a; L2 = 4 * sig / a; s = s2.sqrt(); Lq = L2.sqrt()
        seE = s2 / (1 + r); se2 = s2 / (2 + r)
        E0 = P / (2 * mu); D0 = E0 * gs * se2 / s2 ** 2
        xi = sig * U1 / (1 - QB); zeta = sig ** 2 * eta * Dc('-0.5').exp() / (s * (1 - eta))
        # ---- w-branch (2 A_w), Lemma R_theta + CZ-4
        Lam1 = eta * kE * (2 + r) / ((1 + r) * L2)
        J2a = (1 / L2) * (1 + eta * kE * r / (1 + r)) + 2 * eta * kE * seE / (L2 * s2)
        Jup = J2a + D0 / (1 - eta)
        M4w = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2 + 3 * se2 * D0 / (1 - eta)
        w = {'P1': 2 * sig ** 2 / L2, 'P2': 2 * sig ** 2 * D0 / (1 + eta),
             'ring1': sig ** 4 * (1 - b) ** 2 * K2 * D0 / (4 * b * (1 - eta)),
             'ring2': sig ** 4 * (1 - b) ** 2 * eta ** 2 * T2K * gs * se2 / (4 * b * s2 ** 2 * (1 - eta)),
             'N1': 2 * sig ** 2 * Lam1, 'N2': sig ** 4 * (1 - b) ** 2 * J2a / (4 * b), 'N3': sig ** 2 / 2 * M4w,
             'N4': Dc('1.5') * sig ** 2 * ((xi ** 2 + zeta ** 2) * Jup + sig ** 4 / L2 ** 2 * M4w)}
        # ---- v-branch (2N), Lemmas CZ-2, CZ-5
        Psi0 = om(y / 2 + L2 / 4 + lm1(y, c), c)
        cv = sig * U1 / (sq2 * ((1 - eta) if sharp_c0 else (1 - QB))); c0 = cv + zeta / sq2; c1 = sig ** 2 / (sq2 * L2)
        FrB2 = (W / (1 - eta)) * (c0 + sig ** 2 * (se2 / pi).sqrt() / L2)
        FrB1 = (W / (1 - eta)) * ((c0 * (2 * se2 / pi).sqrt() + c1 * se2) / sq2 + c0 ** 2 + c1 ** 2 * se2) + (y * kap).sqrt() * FrB2
        cL = C2 + y
        v = {'M0 b Psi0': b * Psi0, 'M0 R_theta, t_rho': kE * om(seE / 4, c) * b * (eta + C2), 'M0 Xi': kE * b * y * QB * M4,
             'A1v': b * sig * kE * (15 * y * P).sqrt() / 2, 'A1w': b * sig ** 2 * (1 / (pi.sqrt() * Lq) + eta * kE / (pi * seE).sqrt()),
             'A2k': b * sig ** 2 * kap * W / (2 * (1 - eta)), 'A2a': b * sig ** 4 * (1 + eta * kE * r / (1 + r)) / L2,
             'A2b': b * sig ** 4 * eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta)),
             'B1w1': 2 * sig ** 2 * b * cL * kE * (seE / pi).sqrt() / L2,
             'B1w2': sq2 * b * sig ** 2 * eta ** 2 * (1 + y / 2) * gs * (2 * se2 / pi).sqrt() / (s2 * (1 - eta)),
             'B2a': b.sqrt() * sig ** 2 * U1 * kap.sqrt() * W / (1 - eta) ** 2,
             'B2b': sig ** 4 * (2 * b * P).sqrt() * (kE * seE / L2 ** 2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta) ** 2)),
             'FzK': sig ** 2 * (1 - b) * kap * W / (1 - eta),
             'hF': (W / (1 + eta)) * (1 - z02 / 2) * om(se2 / 4, c),
             'chirp': (cd * y * kap * W / (1 + eta)) if cd > 0 else Dc(0),
             'chirp tail': (cd * y * gs * U1 ** 2 * T2K / (1 + eta)) if cd > 0 else Dc(0),
             'lossK': (-cd * y * kap * W / (1 - eta)) if cd < 0 else Dc(0),
             'tails': (U1 ** 2 * gs / (1 - eta)) * (4 * QK + 2 * dl * y.sqrt() * phiK),
             'FrB2': FrB2, 'FrB1': FrB1}
        den = {'d1': b * (1 + eta * kE) + C2 * b * kE, 'd2': W / (1 - eta), 'd3': sig ** 2 * (1 / L2 + Lam1), 'd4': sig ** 2 * D0 / (1 - eta)}
        gam = q.get('gam', Dc(1))
        out = {k: x / sig for k, x in w.items()}
        out.update({k: x / (2 * sig) for k, x in v.items()})
        out.update({'den ' + k: x for k, x in den.items()})
        # ---- totals Phi_k / sigma
        com = (out['P1'] + out['P2'] - out['ring1'] - out['ring2'] - out['N1'] - out['N2'] - out['N3'] - out['N4']
               + out['M0 b Psi0'] - out['M0 R_theta, t_rho'] - out['M0 Xi'] - out['A1v'] - out['A1w'] - out['A2k'] - out['A2a'] - out['A2b']
               - out['B1w1'] - out['B1w2'] - out['B2a'] - out['B2b'] - gam * sum(out['den ' + k] for k in den))
        tot = {'Fz': com - out['FzK']}
        zb = out['hF'] - out['tails']
        if cd > 0:
            tot['TzB2'] = com + zb + out['chirp'] - out['chirp tail'] - out['FrB2']
            tot['TzB1'] = com + zb + out['chirp'] - out['chirp tail'] - out['FrB1']
        tot['BzB2'] = com + zb - out['lossK'] - out['FrB2']
        tot['BzB1'] = com + zb - out['lossK'] - out['FrB1']
        # the cz_point form of the same total (independently assembled, for the identity check)
        twoAw = 2 * sig ** 2 * (1 / L2 + D0 / (1 + eta) - Lam1) - (sig ** 4 * (1 - b) ** 2 / (4 * b) * (J2a + (K2 * D0 + eta ** 2 * T2K * gs * se2 / s2 ** 2) / (1 - eta))
                                                                    + sig ** 2 / 2 * M4w + sig ** 2 * Dc('1.5') * ((xi ** 2 + zeta ** 2) * Jup + sig ** 4 / L2 ** 2 * M4w))
        M0 = b * Psi0 - kE * om(seE / 4, c) * b * (eta + C2) - kE * b * y * QB * M4
        A1 = b * sig * kE * (15 * y * P).sqrt() / 2 + b * sig ** 2 * (1 / (pi.sqrt() * Lq) + eta * kE / (pi * seE).sqrt())
        A2 = b * (sig ** 2 * kap * W / (2 * (1 - eta)) + sig ** 4 * ((1 + eta * kE * r / (1 + r)) / L2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta))))
        B1w = 2 * sig ** 2 * b * cL * kE * (seE / pi).sqrt() / L2 + sq2 * b * sig ** 2 * eta ** 2 * (1 + y / 2) * gs * (2 * se2 / pi).sqrt() / (s2 * (1 - eta))
        B2 = b.sqrt() * sig ** 2 * U1 * kap.sqrt() * W / (1 - eta) ** 2 + sig ** 4 * (2 * b * P).sqrt() * (kE * seE / L2 ** 2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta) ** 2))
        twoN = M0 - A1 - A2 - B1w - B2
        dsum = b * (1 + eta * kE) + W / (1 - eta) + C2 * b * kE + sig ** 2 * (1 / L2 + D0 / (1 - eta) + Lam1)
        alt = {'Fz': (twoAw + (twoN - sig ** 2 * (1 - b) * kap * W / (1 - eta)) / 2 - gam * sig * dsum) / sig}
        tails = (U1 ** 2 * gs / (1 - eta)) * (4 * QK + 2 * dl * y.sqrt() * phiK); main = (W / (1 + eta)) * (1 - z02 / 2) * om(se2 / 4, c)
        for br, Fr in (('B2', FrB2), ('B1', FrB1)):
            if cd > 0:
                alt['Tz' + br] = (twoAw + (twoN + main + cd * y * (kap * W - gs * U1 ** 2 * T2K) / (1 + eta) - tails - Fr) / 2 - gam * sig * dsum) / sig
            alt['Bz' + br] = (twoAw + (twoN + main + (cd * y * kap * W / (1 - eta) if cd < 0 else 0) - tails - Fr) / 2 - gam * sig * dsum) / sig
        scale = sum(abs(x) for x in out.values()) + Dc(10) ** (-c.prec)
    return out, tot, alt, scale


def ranges_ok(q, la, c):
    """the range conditions of the lemmas at the state (dict name -> bool)."""
    with localcontext(c):
        a = D(la).exp(); sig = q['sig']; s2 = 4 * q['r'] * sig / a; t = 1 + Dc('1e-40')          # t: the rounding of the exact ends (a = 4 r/sigma, r = 1/4, P = mu/8)
        return {'z0 <= 1 (CZ-5)': q['z02'] <= 1, 'y <= 1e-6 (M4 of CZ-2)': q['y'] <= Dc('1e-6'), 'K >= 20 (tails, cz_exact X4)': q['K'] >= 20,
                'b <= 1/2': q['b'] <= t * Dc('0.5'), 'A = sigma^2/s^2 <= 1 (P4)': sig ** 2 / s2 <= t, 'a >= 4 sigma^2 (P0: L^2 <= 1/sigma)': a * t >= 4 * sig ** 2,
                'P <= mu/8 (P3)': q['P'] <= t * q['mu'] / 8, 'r <= 1/4 (P4)': q['r'] <= t * Dc('0.25')}
