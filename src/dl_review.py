"""Stage DL: checks for the answers to the reviews (ChatGPT C, D; Gemini 2, 3).  Python 3.11 grammar.
(C1) the 'equality' rows of the remainder table, in decimal (dk_table lines, 60+ digits) at the states of dj_proof.sample:
     N1 = eps1(r) P1, hneg1 = eps_h(r) P4z (identities of the formulas), B2c + B2s <= c_B2(r) G with equality at a = 4 r/sigma.
(C2) the summary row 'regime II rest, a >= a_s' in decimal: (positive lines) - (negative lines) - [reduced expression - d1 - Gam2 G (1 + es_sigma)] >= 0,
     with c_u taken at the upper end of its interval (dl_consts) -- the only row of DJ section 6.6 whose float ratio exceeded 1 other than (C1).
(D)  the far side of (m4): d/dx log(left/right) = 4 - 24/(ell + 4x) on x >= m_F, in interval arithmetic for every ell >= 55.26 (the lower bound 4 - 24/55.26).
(G3) E_J(mu) >= E_CM(mu, ell) for every mu >= 0 and ell >= 55.26: interval arithmetic on a partition of mu in [0, 80] and the tail mu >= 80.
(G2) (b.5): kappa_b mu <= max(1.002 ell^{7/2} (ell + ln ell) sigma/c_k, 16 ell^5 sigma) < 1 for ell >= 397.6 (interval arithmetic, ell^k e^{-ell} decreasing).
     Also the case kappa_b = 16 b e^mu/mu of (b.5) (written in stage DL): u > 6 (log u >= 220 at the worst point ell = 397.6, mu = 0.1531 ell).
-> results/dl_review.json"""
import json, math, sys, time
from decimal import Decimal as Dc, localcontext
import numpy as np
import dk_lemma as K, dk_table as T, dj_proof as P, dj_lines as J, dl_consts as LC, dl_interval as V
from dl_interval import Iv, exp, log, sqrt, pe


def c1_c2(ells=(55.26, 165.78, 955.8, 1e4, 1e6, 1e8), n=300, seed=31):
    out = {}
    for ell in ells:
        rng = np.random.default_rng(seed + int(ell) % 9973); Y, lP, Y5 = P.sample(ell, rng, n, full=True)
        Q = P.state_quantities(ell, Y, lP); reg = P.rule(ell, Q)
        c = K.context(ell); oc = LC.consts_iv(Dc(repr(ell)), Dc(repr(ell))); cu_hi = oc['c_u'].hi
        with localcontext(c): gam = ((1 + 10 / K.D(ell)) / K.D(ell)).sqrt()
        w = {'R1 |N1/P1 - eps1| (max)': Dc(0), 'R2 |hneg1/P4z - eps_h| (max)': Dc(0), 'R6 (B2c + B2s)/(c_B2 G) at a = 4r/sigma: |. - 1| (max)': Dc(0),
             'R6 (B2c + B2s)/(c_B2 G) below the end (max, must be <= 1)': Dc(0), 'C2 summary: min of the slack / scale (must be >= 0)': None}
        n3 = 0; npts = 0
        idx = np.arange(len(Y)); rng.shuffle(idx)
        for i in idx[:n]:
            st = (float(Y[i, 0]), float(Y[i, 1]), float(Y[i, 2]), float(Y[i, 3]), float(lP[i]))
            if not np.isfinite(st[4]): continue
            q = K.state(ell, *st, c); TT, brk = T.lines(q, c, gam)
            with localcontext(c):
                r = q['r']; kE = q['kE']; eta = q['eta']; B = q['B']; sig = q['sig']
                eps1 = eta * kE * (2 + r) / (1 + r); om = 1 / (1 + Dc('0.75') / B) ** 2; epsh = 2 * kE * (eta + Dc('0.184')) / om
                X1 = (Dc('0.25') * (2 * K.D(ell) + Dc('3.1')).sqrt() + Dc('1e-6')) / Dc('0.75'); CZ = eta ** 2 / (Dc(1).exp() * (1 - eta) ** 2)
                cs = (CZ / 2).sqrt() + r / (K.PI() * (2 + r)).sqrt(); cB2 = X1 / (4 * Dc(2).sqrt() * (1 - eta)) + cs / (4 * (1 - eta)); G = q['G']
                hi = Dc(4).ln() + K.D(st[1]) + K.D(ell)
                v = lambda tag, la: T.value(TT, tag, la, sig, c)
                w['R1 |N1/P1 - eps1| (max)'] = max(w['R1 |N1/P1 - eps1| (max)'], abs(-v('N1', hi) / v('P1', hi) - eps1))
                w['R2 |hneg1/P4z - eps_h| (max)'] = max(w['R2 |hneg1/P4z - eps_h| (max)'], abs(-v('hneg1', hi) / v('P4z', hi) - epsh))
                w['R6 (B2c + B2s)/(c_B2 G) at a = 4r/sigma: |. - 1| (max)'] = max(w['R6 (B2c + B2s)/(c_B2 G) at a = 4r/sigma: |. - 1| (max)'], abs(-(v('B2c', hi) + v('B2s', hi)) / (cB2 * G) - 1))
                lo = Dc(4).ln() - 2 * K.D(ell)
                for fr in ('0.1', '0.5', '0.9', '0.999'):
                    la = lo + (hi - lo) * Dc(fr)
                    w['R6 (B2c + B2s)/(c_B2 G) below the end (max, must be <= 1)'] = max(w['R6 (B2c + B2s)/(c_B2 G) below the end (max, must be <= 1)'], -(v('B2c', la) + v('B2s', la)) / (cB2 * G))
                if reg[i] == 3:
                    n3 += 1; las = K.D(float(Q['las'][i]))
                    m1 = 1 - eps1 - LC.E0; m4 = 1 - epsh - LC.E0; ESS = K.D(ell) ** 2 * (-K.D(ell)).exp(); m2 = 1 - 3 * ESS; m3 = 1 - K.D(ell) ** -3
                    m5 = 1 - (cu_hi * r.sqrt() + Dc('2.1') * q['b'] ** 2)
                    G2 = gam / (2 * (1 - eta))
                    for fr in ('0', '0.01', '0.3', '0.7', '1'):
                        la = max(las, lo) + (hi - max(las, lo)) * Dc(fr)
                        tags = J.SHARED + J.OPT['XB1']
                        vals = {t: v(t, la) for t in tags}
                        pos = sum(x for x in vals.values() if x > 0); neg = -sum(x for x in vals.values() if x < 0)
                        red = m1 * vals['P1'] + m4 * vals['P4z'] + m2 * vals['P2z'] + m3 * vals['hFz'] + m5 * vals['cKz']
                        slack = pos - neg - (red + vals['d1'] - G2 * G * (1 + ESS))          # vals['d1'] < 0: the target line d1 (with sign)
                        sc = pos + neg; d = slack / sc
                        w['C2 summary: min of the slack / scale (must be >= 0)'] = d if w['C2 summary: min of the slack / scale (must be >= 0)'] is None or d < w['C2 summary: min of the slack / scale (must be >= 0)'] else w['C2 summary: min of the slack / scale (must be >= 0)']
                        npts += 1
        out[str(ell)] = {k: (None if x is None else ('0' if x == 0 else format(+x, '.12e'))) for k, x in w.items()}
        out[str(ell)].update({'states': n, 'states in regime 3 (II rest)': n3, 'summary points': npts})
        out[str(ell)]['ok'] = bool(w['R1 |N1/P1 - eps1| (max)'] < Dc('1e-50') and w['R2 |hneg1/P4z - eps_h| (max)'] < Dc('1e-50')
                                   and w['R6 (B2c + B2s)/(c_B2 G) at a = 4r/sigma: |. - 1| (max)'] < Dc('1e-50') and w['R6 (B2c + B2s)/(c_B2 G) below the end (max, must be <= 1)'] <= 1
                                   and (w['C2 summary: min of the slack / scale (must be >= 0)'] is None or w['C2 summary: min of the slack / scale (must be >= 0)'] >= 0))
        print(ell, out[str(ell)], flush=True)
    return out


def far_side():
    """d/dx [4x - 6 ln(1 + 4x/ell)] = 4 - 24/(ell + 4x) >= 4 - 24/ell for x >= 0: >= 3.565 at ell = 55.26 (and larger for larger ell)."""
    L = Iv(Dc('55.26'), Dc('Infinity')); v = 4 - 24 / L
    return {'lower bound of d/dx log(left/right) over ell >= 55.26, x >= m_F': float(v.lo), 'ok': bool(v.lo > 0)}


def ej_ge_ecm():
    """E_J(mu) - E_CM(mu, ell) >= 0 for mu in [0, inf), ell >= 55.26 (E_CM is largest at ell = 55.26: (1 + 2e-3/ell) decreasing)."""
    worst = None; npc = 0
    t = Iv(Dc(0), (1 / Iv(Dc('55.26'))).hi)     # DO: inside the interval arithmetic (was 1/Dc('55.26') in the default context; verification/pre_DO)
    edges = [Dc(0)] + [Dc(k) / 100 for k in range(1, 8001)]
    for a, b in zip(edges[:-1], edges[1:]):
        mu = Iv(a, b); d = LC.E_J(mu) - LC.E_CM(mu, t); npc += 1
        worst = d.lo if worst is None or d.lo < worst else worst
    mu = Iv(Dc(80), Dc('Infinity')); dt = LC.E_J(mu) - LC.E_CM(mu, t)
    # the analytic line: with x = e^{-mu/2}:  E_J - E_CM >= (1 + 4.43x)^2 + 6.2e-4 - (1 + 3.445x)^2 (1 + 3.62e-5)
    #   = 0.985x (2 + 7.875x) + 6.2e-4 - 3.62e-5 (1 + 6.89x + 11.868x^2) >= 6.2e-4 - 3.62e-5 > 0  (0.985 x 2 > 3.62e-5 x 6.89, 0.985 x 7.875 > 3.62e-5 x 11.868)
    return {'pieces of mu in [0, 80]': npc, 'smallest lower bound of E_J - E_CM on [0, 80]': float(worst), 'lower bound on [80, inf)': float(dt.lo), 'ok': bool(worst > 0 and dt.lo > 0)}


def b5_kappa():
    """(b.5): kappa_b mu < 1.  kappa < (mT + Tbar) ell^{7/2} sigma/c_k with mT + Tbar <= 1.002, c_k >= 0.1107; 16 b e^mu/mu <= 16 ell^4 sigma^2 e^{ell + ln ell}/mu
    (B < ell^4, mu < ell + ln ell) = 16 ell^5 sigma/mu.  So kappa_b mu <= max(1.002 ell^{7/2} (ell + ln ell) sigma/0.1107, 16 ell^5 sigma)."""
    L = Iv(Dc('397.6'), Dc('Infinity'))
    v1 = Dc('1.002') / Iv(Dc('0.1107')) * 2 * pe(Dc('4.5'), L); v2 = 16 * pe(5, L)                      # ell + ln ell <= 2 ell
    # the case kappa_b = 16 b e^mu/mu (written in stage DL): u >= (m1/m2)(sqrt2/4) sqrt r e^{mu/2}/(sqrt(e b) E_J), sqrt b < ell^2 sigma,
    # sqrt r >= ell sigma^{1/2} mu^{-1/4}/sqrt(c0), c0 <= 1.01, m1/m2 >= 0.985, E_J(mu) <= E_J(6) for mu >= 6:
    #   log u >= log(0.985 (sqrt2/4)/sqrt(1.01 e)) - log E_J(6) + (ell + mu)/2 - (1/4) ln mu - ln ell,
    # increasing in mu (mu >= 1/2) and, at mu = x0 ell (x0 >= 0.1531), in ell (derivative 0.57655 - 1.25/ell > 0): the worst point is ell = 397.6, mu = 0.1531 ell.
    import dl_consts as LC2
    ej6 = LC2.E_J(Iv(6, Dc('Infinity'))).hi
    l0 = Iv(Dc('397.6')); m0 = Iv(Dc('0.1531')) * l0
    lu = log(Iv(Dc('0.985')) * sqrt(Iv(2)) / 4 / sqrt(Iv(Dc('1.01')) * exp(Iv(1)))) - log(Iv(ej6)) + (l0 + m0) / 2 - log(m0) / 4 - log(l0)
    return {'upper bound of kappa_b mu (first)': float(v1.hi), 'upper bound of kappa_b mu (second)': float(v2.hi),
            'E_J(mu) for mu >= 6: upper bound': float(ej6), 'log of the lower bound of u where kappa_b = 16 b e^mu/mu (ell >= 397.6, mu >= 0.1531 ell)': float(lu.lo),
            'ok': bool(v1.hi < 1 and v2.hi < 1 and ej6 <= Dc('1.5') and lu.lo > log(Iv(6)).hi)}


def run(save=True):
    t0 = time.time(); out = {'(C1), (C2)': c1_c2(), '(D) far side': far_side(), '(G3) E_J >= E_CM': ej_ge_ecm(), '(G2) (b.5) kappa_b mu < 1': b5_kappa()}
    out['ok'] = bool(all(v['ok'] for v in out['(C1), (C2)'].values()) and out['(D) far side']['ok'] and out['(G3) E_J >= E_CM']['ok'] and out['(G2) (b.5) kappa_b mu < 1']['ok'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dl_review.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    print(run()['ok'])
