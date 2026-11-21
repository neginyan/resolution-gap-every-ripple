"""AUDIT GUIDE (stage DN; the computation below is unchanged):
  WHAT: the table side of ring 2 -- the 37 lines s c sigma^{p-1} f_t(a) of the z-options in decimal.  WHERE: DO_証明まとめ.md section 1.2a (all 37 formulas)
  and section 8.2 (each group of lines against the lemma's piece, with the elementary inequality and the condition it uses; checked by dm_groups.py).
Stage DK 2.1: THE TABLE SIDE OF RING 2 in decimal arithmetic: the lines of the z-options (dj_lines.coeffs = dg_tm.z_lines = DK_証明まとめ.md section 1.2)
written once more, as  value = s c sigma^{p-1} f_t(a)  with the sigma-free coefficient c and the exact power p (types L: a, S: sqrt a, C: 1, M: 1/sqrt a,
H: 1/(a + sigma)).  Python 3.11 grammar.
WRONG holds the deliberately wrong versions of the power check (dk_audit): {name: True}.  With WRONG empty this is the table.
THE LINE N4 (stage DL): the default is the CORRECTED line (J_up of Lemma R_theta with (1/L^2)(1 + eta k_E r/(1+r))); the table up to stage DK (since co_cells.py,
stage CO) had dropped the eta k_E r/(1+r) part (up to 0.15 % below the lemma's piece at s = sigma, r = 1/4, ell = 55.26).  WRONG['N4 old'] is that old line
(a wrong version of the power check); the environment CZ_N4OLD=1 makes the old line the default again (to reproduce stage DK), WRONG['N4 fix'] then corrects it."""
import os
from decimal import Decimal as Dc, localcontext
import dk_lemma as K
QB = Dc('0.25'); M4Z = Dc('2.07'); C2Z = Dc('0.184')
WRONG = {}
SHARED = ('P1', 'P2z', 'P3z', 'd1', 'd2', 'd3', 'd4', 'N1', 'N2', 'N3', 'N4', 'N4G', 'ring2', 'M0Xi', 'A1v', 'A1w', 'A2k', 'A2a', 'A2b', 'B1w1', 'B1w2', 'B2a', 'B2b', 'pair')
OPT = {'Fz': ('P4z', 'hneg1', 'FzK'),
       'TzB2': ('P4z', 'hneg1', 'hFz', 'cKz', 'B2c', 'B2s'),
       'TzB1': ('P4z', 'hneg1', 'hFz', 'cKz', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s'),
       'BzB2': ('P4z', 'hneg1', 'hFz', 'lossK', 'B2c', 'B2s'),
       'BzB1': ('P4z', 'hneg1', 'hFz', 'lossK', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')}
ALL_TAGS = SHARED + ('P4z', 'hneg1', 'FzK', 'hFz', 'cKz', 'lossK', 'B2c', 'B2s', 'B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')


def lines(q, c, gam):
    """tag -> (type, sign, p, c) at the state q (dk_lemma.state), gamma = gam (the target lines carry it).  Also the bracket brk."""
    W_ = WRONG.get
    with localcontext(c):
        pi = K.PI(); sq2 = Dc(2).sqrt(); sqpi = pi.sqrt()
        ell, eta, r, B, kap, P, mu = (q[k] for k in ('ell', 'eta', 'r', 'B', 'kap', 'P', 'mu'))
        b = q['b']; kE, gs = q['kE'], q['gs']
        fl = 1 / (1 + eta); ome = 1 - eta
        U1 = QB * ((ell if W_('U1') else 2 * ell) + Dc('3.1')).sqrt() + Dc('1e-6')
        X1 = U1 / (1 - QB); CZ = eta ** 2 / (Dc(1).exp() * ome ** 2); X1CZ = X1 ** 2 + CZ
        omb = 1 - b; yh = 1 / (2 * B); w0 = Dc('0.75') / B; opw0 = 1 + w0
        Kz2 = (4 if W_('K2') else 8) * ell + 100; Kz = Kz2.sqrt(); e50 = Dc(-50).exp() * ((-ell / 100).exp() if W_('e50') else 1)
        TKc = Dc('0.8') * e50 * (Kz + 1)
        ringf = 1 - Kz2 * (1 + eta) / (8 * ome * B)
        G = gs * P; cap = 2 * QB ** 2 * Dc('1e-6').exp() * gs; Gmu = min(G / mu, cap)
        M4c = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2
        M4g = Dc('1.5') * Gmu / ((2 + r) ** 2 * ome)
        z2 = Kz2 * yh; brk = 1 - (4 * b / omb + z2 / 12)
        fF = G / (4 * ome); fFs = fF * (kap / (2 * B)).sqrt()
        cs = (CZ / 2).sqrt() + r / (sqpi * (2 + r).sqrt())
        etaN1 = eta / 2 if W_('eta N1') else eta
        n4old = bool(W_('N4 old')) or (os.environ.get('CZ_N4OLD', '0') != '0' and not W_('N4 fix'))   # DL: the corrected N4 is the default; 'N4 old' = the line up to DK
        T = {
            'P1': ('L', +1, 1, Dc('0.5')),
            'P2z': ('L', +1, 1, (1 if W_('ringf0') else ringf) * fl * G / (mu * (2 + r) * 4 * r)),
            'P3z': ('C', +1, 2, Dc(3) / 8 * omb ** 2 / opw0),
            'd1': ('C', -1, 3, gam * B * (1 + (eta + Dc('0.184')) * kE)),
            'd2': ('C', -1, 1, gam * G / (2 * ome)),
            'd3': ('L', -1, 2, gam * (1 + 2 * eta * kE) / 4),
            'd4': ('L', -1, 2, gam * Gmu / (2 * ome * (2 + r) * 4 * r)),
            'N1': ('L', -1, 1, etaN1 * kE * (2 + r) / (2 * (1 + r))),
            'N2': ('L', -1, 1, (1 + eta * kE * r / (1 + r) + 2 * eta * kE / (1 + r)) / (16 * B)),
            'N3': ('C', -1, 2, (M4c + M4g) / 2),
            'N4': ('L', -1, 3, Dc('1.5') / 4 * (X1CZ * (1 + (0 if n4old else eta * kE * r / (1 + r)) + 2 * eta * kE / (1 + r)) + r * M4c)),
            'N4G': ('L', -1, 3, Dc('1.5') * (X1CZ * Gmu / (2 * ome * (2 + r)) + r ** 2 * M4g) / (4 * r)),
            'ring2': ('L', -1, 5, eta ** 2 * gs * TKc / (4 * B * (2 + r) * ome * 4 * r)),
            'M0Xi': ('C', -1, 2, Dc('0.25') * QB * M4Z * kE),
            'A1v': ('C', -1, 3, (Dc('7.5') * B).sqrt() * kE * P.sqrt() / 4),
            'A1w': ('S', -1, Dc('3.75') if W_('A1w power') else Dc('3.5'), B * (1 + eta) / (4 * sqpi)),
            'A2k': ('C', -1, 4, B * kap * G / (8 * ome)),
            'A2a': ('L', -1, 5, B * (1 + eta * kE * r / (1 + r)) / 8),
            'A2b': ('L', -1, 5, B * eta ** 2 * gs / ((2 + r) * ome * 8 * r)),
            'B1w1': ('S', -1, Dc('3.5'), B * (C2Z + yh) * (r / (1 + r)) / (2 * sqpi)),
            'B1w2': ('S', -1, Dc('3.5'), B * eta ** 2 * (1 + yh / 2) / (2 * sqpi * (2 + r) * ome)),
            'B2a': ('C', -1, 3, B.sqrt() * U1 * kap.sqrt() * G / (4 * ome ** 2)),
            'B2b': ('L', -1, 4, (2 * B).sqrt() * P.sqrt() / 8 * (kE * r / (1 + r) + eta ** 2 / ((r * (2 + r)).sqrt() * (2 + r) * ome ** 2))),
            'pair': ('C', -1, 4, U1 ** 2 * gs * (Kz + 5) * Dc('0.4') * e50 / ome),
            'P4z': ('H', +1, 3, (B / 2) / opw0 ** 2),
            'hneg1': ('H', +1 if W_('hneg1 sign') else -1, 3, B * kE * (eta + Dc('0.184'))),
            'hFz': ('H', +1, 1, fl * (G / 4) * (r / (2 + r)) * (1 - z2 / 2)),
            'cKz': ('C', +1, 0, fl * (G / 4) * omb ** 2 * kap / (4 * B) * brk if brk > 0 else Dc(0)),
            'lossK': ('C', -1, 0, kap * G / (16 * B * ome) * (-brk) if brk < 0 else Dc(0)),
            'B2c': ('C', -1, 1, fF * X1 / sq2),
            'B2s': ('S', -1, Dc('1.5'), fF * cs / (4 * r).sqrt()),
            'B1m': ('M', -1, Dc('1.5'), fF * X1 / (sq2 * sqpi * (2 + r).sqrt()) * (4 * r).sqrt()),
            'B1c': ('C', -1, 2, fF * ((CZ / (2 * pi * (2 + r))).sqrt() + r / (2 * (2 + r)) + X1CZ)),
            'B1l': ('L', -1, 3, fF * r / (8 * (2 + r))),
            'uB2c': ('C', -1, 1, fFs * X1 / sq2),
            'uB2s': ('S', -1, Dc('1.5'), fFs * cs / (4 * r).sqrt()),
            'FzK': ('C', -1, 2, kap * G / (4 * ome)),
        }
        for k, f in (('P1', 'P1 x1.01'), ('P2z', 'P2z x1.01'), ('hFz', 'hFz x1.01'), ('cKz', 'cKz x1.01'), ('P4z', 'P4z x1.01')):
            if W_(f): t, s, p, cc = T[k]; T[k] = (t, s, p, cc * Dc('1.01'))
        for k in ('N1', 'N2', 'A1w', 'B2a', 'pair', 'B2c', 'hneg1', 'd1', 'ring2', 'M0Xi', 'A2k', 'B1m', 'FzK', 'N4'):
            if W_(k + ' x0.99'): t, s, p, cc = T[k]; T[k] = (t, s, p, cc * Dc('0.99'))
        if W_('N1 sign'): t, s, p, cc = T['N1']; T['N1'] = (t, +1, p, cc)
        for k, f in (W_('scale') or {}).items():                                     # DL: a group of lines scaled by f (wrong versions just below the line's own slack)
            t, s, p, cc = T[k]; T[k] = (t, s, p, cc * Dc(f))
    return T, brk


def value(T, tag, la, sig, c):
    """the line's value s c sigma^{p-1} f_t(a) at a = e^{la} (Decimal, signed)."""
    t, s, p, cc = T[tag]
    with localcontext(c):
        if cc == 0: return Dc(0)
        a = K.D(la).exp()
        f = {'L': a, 'S': a.sqrt(), 'C': Dc(1), 'M': 1 / a.sqrt(), 'H': 1 / (a + sig)}[t]
        return s * cc * sig ** (Dc(p) - 1) * f


def log_coeff(T, tag, ell, c):
    """log(c sigma^{p-1}) (for the comparison with the float codes), or None for a zero coefficient."""
    t, s, p, cc = T[tag]
    with localcontext(c):
        if cc == 0: return None
        return cc.ln() - (Dc(p) - 1) * K.D(ell)
