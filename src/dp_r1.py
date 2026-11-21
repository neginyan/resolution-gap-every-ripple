"""Stage DP, addendum 1.1 (DP_探索計画.md section A, written before this ran): the allocation of es := 1e-11 between (R1) and (R3) in the proof of Theorem DJ-T.
Python 3.11 grammar.
THE FINDING (ChatGPT, third review): the text said '(R1) <= half of es P1' and '(R3) <= the other half', but N2/P1 = Q2/(8B) reaches 0.5073 es at ell = 55.26,
r = 1/4, B = 2.5e10.  The table of section 6.6 (dj_proof.check_remainders) measured (R1) against es and (R3) against es (P1 + P4z), not against the halves.
THE NEW ALLOCATION:  (R1)  N2 + d3 + N4 + ring2 + A2a + A2b + B2b <= 0.52 es P1;   (R3)  A1w + B1w1 + B1w2 <= 0.48 es P4z for a <= 1, <= 0.48 es P1 for a >= 1.
So the total charged to P1 is <= es and to P4z <= 0.48 es <= es: the coefficients (1 - eps1 - es), (1 - eps_h - es) of (R4), e0, m1, m4 and everything after are unchanged.
(I)  [computer-assisted] INTERVAL PROOF for every ell >= 55.26 (ONE piece [55.26, inf): every bound below is increasing in 1/ell and in sigma = e^-ell), every
     r in [sigma^3, 1/4], B >= 2.5e10, b <= 1/2, P <= 0.7008, G/mu <= g_s/8, mu < 2 ell (Case II: mu < ell + ln ell), with decimal.Inexact trapped in the default context:
       R1:  N2/P1 = Q2/(8B), Q2 = 1 + eps1(r) <= 1 + eta sqrt(0.2) 1.8;   d3/P1 <= Gam sigma (1 + 2 eta sqrt(0.2))/2;   N4/P1 <= (3/4) sigma^2 [(X1^2 + CZ) Q2 + M4c/4];
            ring2/P1 <= sigma^{5/2} eta^2 T_K/(16 sqrt2 B (1 - eta));   A2a/P1 <= sigma^2 (1 + eta)/8;   A2b/P1 <= sigma^{1/2} eta^2/(16 sqrt2 (1 - eta));
            B2b/P1 <= (sqrt(0.7008)/4)(0.0895 sigma^2 + sigma^{1/2} eta^2/(2 sqrt2 (1 - eta)^2));                      sum <= 0.52 es
       R3:  a <= 1: S/P4z <= 2 c_S sqrt(sigma)(1 + sigma)/omega;   a >= 1: S/P1 <= c_S sqrt(sigma)   (c_S as in dj_proof.consts);       both <= 0.48 es
       the 'tiny' bounds of (R1), (R7) that were stated with a ratio in brackets only (divided by es_sigma = ell^2 sigma):
            (d4 + N4G)/P2z,  B1l/P2z (mu <= 2 ell),  B1c/(Gam2 G)   <= es_sigma        (X1^2 <= ell is checked and used)
     POWER: 'half' (0.5 es) fails;  B >= 2.4e10 fails;  r >= sigma^5 fails.
(II) [numerical] on the states of dj_proof.sample and its grid of a: the ratios in the form of the text, and the old 'half' version (must exceed 1 at ell = 55.26: 1.0146).
-> results/dp_r1.json"""
import json, math, sys, time, functools
import decimal
from decimal import Decimal as Dc
import numpy as np
import dl_interval as V
from dl_interval import Iv
V.PI = Iv(Dc('3.141592653589793238462643383279502884197'), Dc('3.141592653589793238462643383279502884198'))   # as in dl_consts
import dj_proof as PR, dj_lines as J

ES = Dc('1e-11')


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


def bounds_iv(ell_lo='55.26', Bm='2.5e10', rpow=3, qden=400, eta_ripple=None):
    """upper bounds, valid for every ell >= ell_lo (one piece) and B >= Bm.  rpow: r >= sigma^rpow (the class has 3).  qden: q <= (1 + eta)/(qden (1 - eta))
    (400 in Theorem DJ-T; 8 c_B in room 1a of stage DP, dp_room1.py)."""
    L = Iv(Dc(ell_lo), V.INF); il = 1 / L; sg = V.exp(-L); Bm = Iv(Dc(Bm))
    eta = il if eta_ripple is None else Iv(Dc(eta_ripple))                    # DX: the ripple eta separated from 1/ell (None: eta = 1/ell, the published case)
    kE = V.sqrt(Iv(Dc('0.2'))); e1 = eta * kE * Dc('1.8'); Q2 = 1 + e1                                   # r = 1/4: k_E = sqrt(1/5), (2 + r)/(1 + r) = 1.8
    Gam = V.sqrt((1 + 10 * il) * il)
    X1sq_over_ell = (Iv(Dc(16)) / 9) * (V.sqrt(2 + Dc('3.1') * il) / 4 + Dc('1e-6') * V.sqrt(il)) ** 2   # X1^2/ell, increasing in 1/ell
    CZ = eta ** 2 / (V.exp(Iv(Dc(1))) * (1 - eta) ** 2)
    M4c = 3 * (1 + eta * kE * Dc('0.0625') / Dc('1.5625')) + 6 * eta * kE * Dc('0.25') / Dc('1.5625')
    sgL = V.pe(1, L)                                                                                    # ell sigma, decreasing for ell >= 1
    # ring2/P1 <= sigma^{(8 - rpow)/2} eta^2 T_K/(16 sqrt2 B (1 - eta)), T_K = 0.8 e^-50 (K + 1), K + 1 = sqrt(8 ell + 100) + 1 <= 11 ell, sigma^{5/2} <= sigma
    ring = Dc('0.8') * V.exp(Iv(Dc(-50))) * 11 * sgL * eta ** 2 / (16 * V.sqrt(Iv(Dc(2))) * Bm * (1 - eta))
    shalf = V.exp(-L * (Dc(4 - rpow) / 2))                                                              # sigma^2/sqrt(sigma^rpow): sigma^{1/2} for the class (rpow = 3)
    P = Iv(Dc('0.7008'))
    o = {}
    o['N2/P1'] = Q2 / (8 * Bm)
    o['d3/P1'] = Gam * sg * (1 + 2 * eta * kE) / 2
    o['N4/P1'] = Dc('0.75') * sg * ((X1sq_over_ell * sgL + CZ * sg) * Q2 + M4c * sg / 4)
    o['ring2/P1'] = ring
    o['A2a/P1'] = sg * sg * (1 + eta) / 8
    o['A2b/P1'] = shalf * eta ** 2 / (16 * V.sqrt(Iv(Dc(2))) * (1 - eta))
    o['B2b/P1'] = V.sqrt(P) / 4 * (Dc('0.0895') * sg * sg + shalf * eta ** 2 / (2 * V.sqrt(Iv(Dc(2))) * (1 - eta) ** 2))
    tot = o['N2/P1']
    for k in ('d3/P1', 'N4/P1', 'ring2/P1', 'A2a/P1', 'A2b/P1', 'B2b/P1'): tot = tot + o[k]
    o['R1: sum/P1'] = tot
    om = 1 / (1 + Dc('0.75') / Bm) ** 2
    cS = (1 + eta) / (4 * V.sqrt(V.PI)) + (Dc('0.184') + Dc('0.5') / Bm) * Dc('0.2') / (2 * V.sqrt(V.PI)) + eta ** 2 * (1 + Dc('0.25') / Bm) / (2 * V.sqrt(V.PI) * 2 * (1 - eta))
    shs = V.exp(-L / 2)                                                                                 # sqrt(sigma)
    o['c_S'] = cS
    o['R3 (a <= 1): S/P4z'] = 2 * cS * shs * (1 + sg) / om
    o['R3 (a >= 1): S/P1'] = cS * shs
    q = (1 + eta) / (qden * (1 - eta))                                                                  # q <= (1 + eta)/(400 (1 - eta)) for B >= 50 (8 ell + 100)
    # divided by es_sigma = ell^2 sigma:
    o['X1^2/ell'] = X1sq_over_ell
    o['(d4 + N4G)/P2z / es_sigma'] = (1 + eta) / (1 - q) * (Gam / (2 * (1 - eta)) + Dc('1.5') * ((X1sq_over_ell * sgL + CZ * sg) / (2 * (1 - eta)) + Dc('1.5') * sg / (16 * 2 * (1 - eta)))) * il ** 2
    o['B1l/P2z / es_sigma (mu <= 2 ell)'] = sg * (1 + eta) / (64 * (1 - eta) * (1 - q)) * il           # sigma^2 (2 ell)(1/16)(1 + eta)/(8 (1 - eta)(1 - q)) / (ell^2 sigma)
    # B1c/(Gam2 G) = sigma (sqrt(CZ/(2 pi (2 + r))) + r/(2 (2 + r)) + X1^2 + CZ)/(2 Gam);  / (ell^2 sigma), with eta/Gam <= sqrt(eta):
    o['B1c/(Gam2 G) / es_sigma'] = ((V.sqrt(CZ / (4 * V.PI)) + Dc('0.0625') + CZ) * il + X1sq_over_ell) * V.sqrt(il) / 2
    return o


def interval_part():
    out = {}
    o = trapped(bounds_iv)()
    f = lambda x: float(x.hi)
    out['upper bounds for every ell >= 55.26 (in units of es = 1e-11 where it applies)'] = {
        'N2/P1': f(o['N2/P1'] / ES), 'd3/P1': f(o['d3/P1'] / ES), 'N4/P1': f(o['N4/P1'] / ES), 'ring2/P1': f(o['ring2/P1'] / ES), 'A2a/P1': f(o['A2a/P1'] / ES),
        'A2b/P1': f(o['A2b/P1'] / ES), 'B2b/P1': f(o['B2b/P1'] / ES), 'R1: sum/P1': f(o['R1: sum/P1'] / ES), 'R3 (a <= 1): S/P4z': f(o['R3 (a <= 1): S/P4z'] / ES),
        'R3 (a >= 1): S/P1': f(o['R3 (a >= 1): S/P1'] / ES), 'c_S': f(o['c_S']), 'X1^2/ell': f(o['X1^2/ell']),
        '(d4 + N4G)/P2z / es_sigma': f(o['(d4 + N4G)/P2z / es_sigma']), 'B1l/P2z / es_sigma (mu <= 2 ell)': f(o['B1l/P2z / es_sigma (mu <= 2 ell)']),
        'B1c/(Gam2 G) / es_sigma': f(o['B1c/(Gam2 G) / es_sigma'])}
    ok = {'R1: sum/P1 <= 0.52 es': o['R1: sum/P1'].le(Dc('0.52') * ES), 'R3 (a <= 1) <= 0.48 es': o['R3 (a <= 1): S/P4z'].le(Dc('0.48') * ES),
          'R3 (a >= 1) <= 0.48 es': o['R3 (a >= 1): S/P1'].le(Dc('0.48') * ES), 'X1^2 <= ell': o['X1^2/ell'].le(1),
          '(d4 + N4G)/P2z <= es_sigma': o['(d4 + N4G)/P2z / es_sigma'].le(1), 'B1l/P2z <= es_sigma': o['B1l/P2z / es_sigma (mu <= 2 ell)'].le(1),
          'B1c <= es_sigma Gam2 G': o['B1c/(Gam2 G) / es_sigma'].le(1), 'c_S <= 0.155': o['c_S'].le(Dc('0.155'))}
    out['conditions (all must hold)'] = {k: bool(v) for k, v in ok.items()}
    pw = {}
    pw["the old 'half': R1 sum/P1 <= 0.5 es"] = bool(o['R1: sum/P1'].le(Dc('0.5') * ES))
    o2 = trapped(bounds_iv)(Bm='2.4e10'); pw['B >= 2.4e10 instead of 2.5e10: R1 sum/P1 <= 0.52 es'] = bool(o2['R1: sum/P1'].le(Dc('0.52') * ES))
    o3 = trapped(bounds_iv)(rpow=5); pw['r >= sigma^5 instead of sigma^3: R1 sum/P1 <= 0.52 es'] = bool(o3['R1: sum/P1'].le(Dc('0.52') * ES))
    out['power (each must be False: the wrong version fails)'] = pw
    out['ok'] = bool(all(ok.values()) and not any(pw.values()))
    return out


def point_part(ells=(55.26, 82.89, 165.78, 955.8, 1e4, 1e6, 1e8), n=1500, seed=2031):
    """the ratios in the form of the text, on the states and the grid of a of dj_proof.check_remainders."""
    out = {}
    for ell in ells:
        rng = np.random.default_rng(seed + int(ell) % 9973); Y, lP = PR.sample(ell, rng, n); Q = PR.state_quantities(ell, Y, lP); o = PR.consts(ell)
        lo, hi = J.a_range(ell, Y[:, 1]); g = 40
        lA = lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, g)[None, :]
        lA = np.concatenate([lA, np.clip(np.array([-3.0, -1.0, -1e-9, 1e-9, 1.0, 3.0])[None, :] + 0 * lo[:, None], lo[:, None], hi[:, None]), np.full((len(Y), 1), -ell).clip(lo[:, None], hi[:, None]),
                             np.clip(0.5 * Q['lb'][:, None] + np.array([-1.0, 0.0, 1.0])[None, :], lo[:, None], hi[:, None])], axis=1)      # a near sqrt(b): where P1 + P4z is smallest
        Vv, aux = PR._lines_on(ell, Y, lP, lA); S_ = PR._sum; les = math.log(1e-11)
        def mx(d, mask=None):
            d = np.where(np.isnan(d), -np.inf, d)
            if mask is not None: d = np.where(mask, d, -np.inf)
            m = float(np.max(d)); return float(np.exp(min(m, 700.0))) if np.isfinite(m) else 0.0
        with np.errstate(all='ignore'):
            r1 = S_(Vv, ('N2', 'd3', 'N4', 'ring2', 'A2a', 'A2b', 'B2b')) - Vv['P1'][1]; s3 = S_(Vv, ('A1w', 'B1w1', 'B1w2'))
            row = {'states': int(len(Y)),
                   'R1: (N2 + d3 + N4 + ring2 + A2a + A2b + B2b)/P1 against 0.52 es': mx(r1 - les - math.log(0.52)),
                   "POWER, the old 'half': the same against 0.5 es (must exceed 1 at ell = 55.26)": mx(r1 - les - math.log(0.5)),
                   'R3 (a <= 1): (A1w + B1w1 + B1w2)/P4z against 0.48 es': mx(s3 - Vv['P4z'][1] - les - math.log(0.48), lA <= 0),
                   'R3 (a >= 1): (A1w + B1w1 + B1w2)/P1 against 0.48 es': mx(s3 - Vv['P1'][1] - les - math.log(0.48), lA >= 0),
                   'R1 + R3 charged to P1 (a >= 1) against es': mx(np.logaddexp(r1, s3 - Vv['P1'][1]) - les, lA >= 0),
                   'R4 in the form of the text: (N3 + M0Xi + A1v + pair)/((e0 - es)(P1 + P4z))': mx(S_(Vv, ('N3', 'M0Xi', 'A1v', 'pair')) - S_(Vv, ('P1', 'P4z')) - math.log(PR.E0 - PR.ES)),
                   'R4 as coded in dj_proof (with the factor 1 - eps1_max - epsh_max)': mx(S_(Vv, ('N3', 'M0Xi', 'A1v', 'pair')) - S_(Vv, ('P1', 'P4z')) - math.log((PR.E0 - PR.ES) * (1 - o['eps1_max'] - o['epsh_max'])))}
        out[str(ell)] = row; print(ell, {k[:22]: round(v, 5) for k, v in row.items() if k != 'states'}, flush=True)
    half = "POWER, the old 'half': the same against 0.5 es (must exceed 1 at ell = 55.26)"
    out['ok'] = bool(all(v <= 1 for e, row in out.items() for k, v in row.items() if k not in ('states', half)) and out['55.26'][half] > 1.014)
    return out


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)'}
    out['(I) interval proof, ell in [55.26, inf) as one piece, Inexact trapped'] = interval_part()
    out['(II) on the states of dj_proof.sample (ratio/bound, must be <= 1)'] = point_part()
    out['ok'] = bool(out['(I) interval proof, ell in [55.26, inf) as one piece, Inexact trapped']['ok'] and out['(II) on the states of dj_proof.sample (ratio/bound, must be <= 1)']['ok'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_r1.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(); print(json.dumps(r['(I) interval proof, ell in [55.26, inf) as one piece, Inexact trapped'], indent=1)); print(r['ok'])
