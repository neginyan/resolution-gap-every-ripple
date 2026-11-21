"""Stage CZ: the DIRECT LOCAL FORM of the v-branch and its pieces, by quadrature -- the evaluator used to try to break Lemmas CZ-1 .. CZ-4
(plan: CZ_探索計画.md) and to check their proofs.  Python 3.11 grammar.

NOTATION (co_remainders.py; the line variable is t = sqrt(tau) sh, sh ~ N(0, 1); w ~ Gamma = N(0, L^2); <.> = int Gamma dw E_rho[.]):
  E = e^{-w^2/2s^2}, h = 1 + E R,  X1 := sqrt(x) R'(t),  X2 := x R''(t),  Ft := E^2 X1^2/h = sigma^2 F  (>= 0),
  S := sqrt(b) sh - E X1/h  (= sigma s_v up to sign),   a := sqrt(y) sh + w/sqrt2,   y = (1-b)^2 sigma^2/(2b),
  chi = chi_v + chi_w,  chi_v = sigma E X1/(sqrt2 h),  chi_w = -(sigma^2 w/sqrt2)(1/L^2 + E R/(s^2 h)),  rho := cos a - chi sin a - cos(a + chi).
LEMMA CZ-1 (identity):  Z sigma^2 E_p[s_v^2 phi] = <h S^2 (1 - cos(a + chi))> = (I) + (II) + (III),
  (I) = b <sh^2 h (1 - cos(a+chi))>,  (II) = -2 sqrt(b) <sh E X1 (1 - cos(a+chi))>,  (III) = <Ft (1 - cos(a+chi))>.
PIECES (exact):  (I) + (II) = M0 + A1 + A2 + B1 + B2,
  M0 = <(b sh^2 h - 2 sqrt(b) sh E X1)(1 - cos a)>,  A1 = b <sh^2 h chi sin a>,  A2 = b <sh^2 h rho>,
  B1 = -2 sqrt(b) <sh E X1 chi sin a>,  B2 = -2 sqrt(b) <sh E X1 rho>.
A 'sample set' is (sh, wt, R, X1, X2): points with weights summing to 1 -- an ordinary window on a grid of sh, or a carrier-averaged packet
(R = A(sh) cos th, X1 = -u_N A sin th, X2 = -u_N^2 A cos th with th uniform: the limit of a packet of harmonic number N -> infinity at fixed
u_N = N sqrt(x); used for the states whose harmonics cannot be resolved, e.g. the box where the CY column stopped)."""
import math
import numpy as np
from scipy.special import erfc

SQ2 = math.sqrt(2.0); SQPI = math.sqrt(math.pi)


def T2(a):
    """E[Z^2 1{|Z| > a}] for a standard normal Z: 2 (a phi(a) + Q(a))."""
    a = float(a)
    return 2 * (a * math.exp(-a * a / 2) / math.sqrt(2 * math.pi) + 0.5 * float(erfc(a / SQ2)))


def window_samples(q, ph, tau, x, ns=None, span=9.0):
    """ordinary window R = sum q_n cos(n t - phi_n) on a grid of sh (trapezoid with the normal weight)."""
    q = np.asarray(q, float); ph = np.asarray(ph, float); n = np.arange(1, len(q) + 1, dtype=float)
    nmax = max((i + 1 for i, v in enumerate(q) if v != 0), default=1)
    if ns is None: ns = int(min(600001, max(4001, 2 * span * nmax * math.sqrt(tau) / 0.12)))
    sh = np.linspace(-span, span, ns); wt = np.exp(-sh ** 2 / 2); wt[[0, -1]] *= 0.5; wt /= wt.sum()
    t = math.sqrt(tau) * sh; R = np.zeros(ns); X1 = np.zeros(ns); X2 = np.zeros(ns)
    for nn, qq, pp in zip(n, q, ph):
        if qq == 0: continue
        c = np.cos(nn * t - pp); s = np.sin(nn * t - pp)
        R += qq * c; X1 += -math.sqrt(x) * nn * qq * s; X2 += -x * nn * nn * qq * c
    return {'sh': sh, 'wt': wt, 'R': R, 'X1': X1, 'X2': X2, 'kind': 'window', 'q': q, 'ph': ph, 'tau': tau, 'x': x}


def carrier_samples(Afun, uN, ns=1201, nth=96, span=9.0):
    """carrier-averaged packet: R = A(sh) cos th, X1 = -uN A sin th, X2 = -uN^2 A cos th, th uniform on the circle."""
    sh = np.linspace(-span, span, ns); ws = np.exp(-sh ** 2 / 2); ws[[0, -1]] *= 0.5; ws /= ws.sum()
    th = (np.arange(nth) + 0.5) * 2 * math.pi / nth
    A = Afun(sh)
    R = (A[:, None] * np.cos(th)[None, :]).ravel(); X1 = (-uN * A[:, None] * np.sin(th)[None, :]).ravel(); X2 = (-uN ** 2 * A[:, None] * np.cos(th)[None, :]).ravel()
    return {'sh': np.repeat(sh, nth), 'wt': np.repeat(ws, nth) / nth, 'R': R, 'X1': X1, 'X2': X2, 'kind': 'carrier'}


def local_numbers(S):
    sh, wt, R, X1, X2 = S['sh'], S['wt'], S['R'], S['X1'], S['X2']
    xE1 = float(np.sum(wt * X1 ** 2)); E0 = float(np.sum(wt * R ** 2))
    return {'xE1': xE1, 'P': 2 * xE1, 'E0': E0, 'kappa': float(np.sum(wt * sh ** 2 * X1 ** 2)) / xE1 if xE1 > 0 else 0.0,
            'eta': float(np.max(np.abs(R))), 'U': float(np.max(np.abs(X1))), 'Rth': float(np.sum(wt * R)), 't_rho': -float(np.sum(wt * X2)),
            'ring0': float(np.sum(wt * sh ** 2 * R ** 2)), 'mu': xE1 / E0 if E0 > 0 else math.inf}


def w_grid(L, r, nw=700, span=9.0):
    a_ = max(min(2 * math.sqrt(r), 1.0), 1e-140)
    xi = np.linspace(-math.asinh(span / a_), math.asinh(span / a_), nw); om = a_ * np.sinh(xi)
    wo = a_ * np.cosh(xi) * (xi[1] - xi[0]); wo[[0, -1]] *= 0.5
    g = np.exp(-om ** 2 / 2) * wo; g /= g.sum()
    return L * om, g, np.exp(-om ** 2 / (2 * r))


def rho_stable(a, chi):
    """rho = cos a - chi sin a - cos(a + chi) = cos a (1 - cos chi) + sin a (sin chi - chi), without cancellation for small chi."""
    one_m_cos = 2 * np.sin(chi / 2) ** 2
    small = np.abs(chi) < 1e-2
    sc = np.where(small, -chi ** 3 / 6 * (1 - chi ** 2 / 20 * (1 - chi ** 2 / 42)), np.sin(chi) - chi)
    return np.cos(a) * one_m_cos + np.sin(a) * sc


def pieces(S, sig, b, L2, s2, nw=700, chunk=24):
    """all exact pieces by quadrature.  Returns a dict (floats)."""
    sh, wt, R, X1 = S['sh'], S['wt'], S['R'], S['X1']
    L = math.sqrt(L2); r = s2 / L2; y = (1 - b) ** 2 * sig ** 2 / (2 * b); sy = math.sqrt(y); sb = math.sqrt(b)
    w, g, E = w_grid(L, r, nw)
    acc = {k: 0.0 for k in ('total', 'direct', 'M0', 'M0r', 'A1v', 'A1w', 'A2', 'B1v', 'B1w', 'B2', 'III', 'Z', 'A1v_odd', 'B1v_odd', 'A1w_odd', 'B1w_odd',
                            'III0', 'IIIchirp', 'sh2Ft', 'Ft', 'J_ring_exact')}
    th = sy * sh
    for i0 in range(0, len(w), chunk):
        ww = w[i0:i0 + chunk][:, None]; gg = g[i0:i0 + chunk][:, None]; EE = E[i0:i0 + chunk][:, None]
        h = 1 + EE * R[None, :]
        cv = sig * EE * X1[None, :] / (SQ2 * h); cw = -(sig ** 2 * ww / SQ2) * (1 / L2 + EE * R[None, :] / (s2 * h)); chi = cv + cw
        a = th[None, :] + ww / SQ2
        P = gg * wt[None, :]
        one_m = 2 * np.sin((a + chi) / 2) ** 2; one_m0 = 2 * np.sin(a / 2) ** 2; sa = np.sin(a); rho = rho_stable(a, chi)
        W1 = b * sh[None, :] ** 2 * h; W2 = -2 * sb * sh[None, :] * EE * X1[None, :]; Ft = EE ** 2 * X1[None, :] ** 2 / h
        acc['Z'] += float(np.sum(P * h))
        acc['total'] += float(np.sum(P * (W1 + W2 + Ft) * one_m))
        # independent assembly in the physical variables: v = sigma sh/sqrt(b), sigma s_v = -sqrt(b) sh + E X1/h, s_w = -w/L^2 - (w/s^2) E R/h
        sv = -sb * sh[None, :] + EE * X1[None, :] / h; swv = -ww / L2 - (ww / s2) * EE * R[None, :] / h
        mz = (sig * sh[None, :] / sb + sig * sv + ww + sig ** 2 * swv) / SQ2
        acc['direct'] += float(np.sum(P * h * sv ** 2 * 2 * np.sin(mz / 2) ** 2))
        acc['M0'] += float(np.sum(P * (W1 + W2) * one_m0))
        acc['M0r'] += float(np.sum(P * (b * sh[None, :] ** 2 * EE * R[None, :] + W2) * one_m0))
        acc['A1v'] += float(np.sum(P * W1 * cv * sa)); acc['A1w'] += float(np.sum(P * W1 * cw * sa))
        acc['A2'] += float(np.sum(P * W1 * rho))
        acc['B1v'] += float(np.sum(P * W2 * cv * sa)); acc['B1w'] += float(np.sum(P * W2 * cw * sa))
        acc['B2'] += float(np.sum(P * W2 * rho))
        acc['III'] += float(np.sum(P * Ft * one_m)); acc['III0'] += float(np.sum(P * Ft * one_m0))
        acc['sh2Ft'] += float(np.sum(P * sh[None, :] ** 2 * Ft)); acc['Ft'] += float(np.sum(P * Ft))
        # the parts that must vanish by the parity in w (computed, to see that they do)
        sw_ = np.sin(ww / SQ2); cw_ = np.cos(ww / SQ2); st = np.sin(th)[None, :]; ct = np.cos(th)[None, :]
        acc['A1v_odd'] += float(np.sum(P * W1 * cv * ct * sw_)); acc['B1v_odd'] += float(np.sum(P * W2 * cv * ct * sw_))
        acc['A1w_odd'] += float(np.sum(P * W1 * cw * st * cw_)); acc['B1w_odd'] += float(np.sum(P * W2 * cw * st * cw_))
        acc['J_ring_exact'] += float(np.sum(P * sh[None, :] ** 2 * (ww ** 2 / s2 ** 2) * EE ** 2 * R[None, :] ** 2 / h))
    acc['A1'] = acc['A1v'] + acc['A1w']; acc['B1'] = acc['B1v'] + acc['B1w']
    return acc


def consts(y):
    """M1 = sup u e^{-u/2} cosh sqrt(yu), M2 = sup u e^{-u/2}(1 + u cosh sqrt(yu)), M4 = sup e^{-u/2}[(1+u)(1 + u cosh)/2 + cosh] (numerical sups)."""
    u = np.linspace(0, 600, 600001); c = np.cosh(np.sqrt(y * u)); e = np.exp(-u / 2)
    return {'M1': float(np.max(u * e * c)) * (1 + 1e-9), 'M2': float(np.max(u * e * (1 + u * c))) * (1 + 1e-9),
            'M4': float(np.max(e * ((1 + u) * (1 + u * c) / 2 + c))) * (1 + 1e-9)}


def Xi_fourier(q, ph, tau, y):
    """Xi = sum q_n cos(phi_n) e^{-u/2} [(1 + u)(1 - e cosh sqrt(yu)) + y e cosh sqrt(yu)], u = n^2 tau (stable for tiny y)."""
    q = np.asarray(q, float); n = np.arange(1, len(q) + 1, dtype=float); u = n * n * tau; z = np.sqrt(y * u)
    lc = np.log1p(2 * np.sinh(z / 2) ** 2)                       # log cosh z
    one_m = -np.expm1(-y / 2 + lc); ec = np.exp(-y / 2 + lc)
    return float(np.sum(q * np.cos(ph) * np.exp(-u / 2) * ((1 + u) * one_m + y * ec)))


def bounds(S, sig, b, L2, s2, Qb=None, flags=()):
    """the right-hand sides of Lemma CZ-2 with the window's own numbers (eta = sup|R|, U = sup|X1|, Qb = sum q for a window, P, kappa, ...).
    flags: deliberately wrong versions ('WA', 'WB', 'WC', 'WH')."""
    N = local_numbers(S); eta, U, P, kap = N['eta'], N['U'], N['P'], N['kappa']
    if Qb is None: Qb = float(np.sum(np.abs(S['q']))) if S['kind'] == 'window' else eta
    L = math.sqrt(L2); r = s2 / L2; y = (1 - b) ** 2 * sig ** 2 / (2 * b)
    kE = math.sqrt(r / (1 + r)); seE = s2 / (1 + r); se2 = s2 / (2 + r); gs = math.sqrt(r / (2 + r)); eE = math.exp(-seE / 4)
    W = gs * N['xE1']; C = consts(y); c2 = 2 * Qb / math.e * (0.5 if 'WC' in flags else 1.0)
    cL = c2 + y * Qb * (C['M2'] / 2 + C['M1'])
    J2p = (1 + eta * kE * r / (1 + r)) / L2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta))
    half = 0.2 if 'WH' in flags else 1.0          # WH: A2, B2 divided by 5 (a division by 2 is NOT broken: the bound of A2 has a spare factor 2, see the report)
    B = {}
    omE = -math.expm1(-seE / 4); B['omE'] = omE          # 1 - e_E without cancellation (se_E can be 1e-30)
    B['M0_eta'] = kE * omE * b * (eta + c2); B['M0_Xi'] = kE * eE * b * y * Qb * C['M4']
    B['A1v'] = b * sig * kE * math.sqrt((1.0 if 'WA' in flags else 15.0) * y * P) / 2
    B['A1w'] = b * sig ** 2 * (1 / (SQPI * L) + eta * kE / math.sqrt(math.pi * seE))
    B['A2'] = half * b * (sig ** 2 * kap * W / (2 * (1 - eta)) + sig ** 4 * J2p)
    B['B1v'] = sig ** 2 * (1 - b) * (1.0 if 'WB' in flags else kap) * W / (1 - eta)
    # B1w, second part: R R'/h = d/dt G_E(R), G_E(R) = (E R - ln(1 + E R))/E^2, |G_E| <= R^2/(2(1-eta)); Gaussian integration by parts in sh
    #   gives |E_rho[sh R' R cos(th)/h]| <= eta^2 (2 + y)/(2 (1-eta) sqrt(tau)), so the part is <= sqrt2 b sigma^2 eta^2 (1 + y/2) g_s sqrt(2 se2/pi)/(s^2 (1-eta))
    B['B1w'] = 2 * sig ** 2 * b * cL * kE * math.sqrt(seE / math.pi) / L2 + SQ2 * b * sig ** 2 * eta ** 2 * (1 + y / 2) * gs * math.sqrt(2 * se2 / math.pi) / (s2 * (1 - eta))
    B['B2'] = half * (math.sqrt(b) * sig ** 2 * U * math.sqrt(kap) * W / (1 - eta) ** 2
                      + sig ** 4 * math.sqrt(2 * b * P) * (kE * seE / L2 ** 2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta) ** 2)))
    Psi0 = -math.expm1(math.log1p(-y) - y / 2 - L2 / 4) if y < 1 else 1 - (1 - y) * math.exp(-y / 2 - L2 / 4)
    B['Psi0'] = Psi0; B['W'] = W; B['kE'] = kE; B['eE'] = eE; B['y'] = y; B['c2'] = c2; B['consts'] = C; B['numbers'] = N; B['Qb'] = Qb
    B['gs'] = gs; B['se2'] = se2; B['seE'] = seE
    return B


def cn2_lower(S, sig, b, L2, s2, Bd, z0=None, flags=()):
    """(III) >= this (Lemma CN-2 with step (iv) replaced by Lemma CZ-3; the chi-remainders N8, N9 of co_remainders with the window's own numbers).
    z0: the cut of CZ-3 (default min(1, 6 sqrt(y)) so that the tail starts at 6 standard deviations at least)."""
    N = Bd['numbers']; eta, U, kap = N['eta'], N['U'], N['kappa']; y = Bd['y']; W = Bd['W']; gs = Bd['gs']; se2 = Bd['se2']
    L = math.sqrt(L2); s = math.sqrt(s2); e2 = math.exp(-se2 / 4); om2 = -math.expm1(-se2 / 4)      # 1 - e^{-se2/4} without cancellation
    if z0 is None: z0 = max(min(1.0, 40 * math.sqrt(y)), min(3.0, 6 * math.sqrt(y))) if y > 0 else 1.0
    epsc = z0 * z0 / 12; a0 = z0 / math.sqrt(y) if y > 0 else math.inf
    xi = sig * U / (1 - eta); zeta = sig ** 2 * eta * math.exp(-0.5) / (s * (1 - eta)); xie = xi / SQ2
    c0 = (xi + zeta) / SQ2; c1 = sig ** 2 / (SQ2 * L2)
    N8 = W / (2 * (1 - eta)) * ((c0 * math.sqrt(2 * se2 / math.pi) + c1 * se2) / SQ2 + c0 ** 2 + c1 ** 2 * se2)
    N9 = W / 2 * e2 * xie * math.sqrt(y * kap)
    tail = 0.0 if ('WE' in flags or y <= 0) else gs * U ** 2 * T2(a0)
    fac = 1.0 if 'WF' in flags else (1 - epsc)
    main = (W / (1 + eta)) * (om2 + e2 * fac * (y / 2) * kap) - e2 * fac * (y / 2) * (0.0 if 'WF' in flags else tail) / (1 + eta)
    return main - 2 * N8 - 2 * N9, {'N8': N8, 'N9': N9, 'tail': tail, 'epsc': epsc, 'a0': a0}


def cz3_check(S, y, z0, flags=()):
    """Lemma CZ-3 on the sample set: E[X1^2 (1 - cos(sqrt(y) sh))] >= (1 - z0^2/12)(y/2)[E[sh^2 X1^2] - sup X1^2 T2(z0/sqrt y)].  Returns lhs, rhs."""
    sh, wt, X1 = S['sh'], S['wt'], S['X1']
    if y <= 0: return 0.0, 0.0
    lhs = float(np.sum(wt * X1 ** 2 * 2 * np.sin(math.sqrt(y) * sh / 2) ** 2))
    k1 = float(np.sum(wt * sh ** 2 * X1 ** 2)); U2 = float(np.max(X1 ** 2))
    tail = 0.0 if ('WE' in flags or 'WF' in flags) else U2 * T2(z0 / math.sqrt(y))
    fac = 1.0 if 'WF' in flags else (1 - z0 * z0 / 12)
    return lhs, fac * (y / 2) * (k1 - tail)


def cz4_check(S, K, flags=()):
    """Lemma CZ-4: E[sh^2 R^2] <= K^2 E[R^2] + sup R^2 T2(K)."""
    sh, wt, R = S['sh'], S['wt'], S['R']
    lhs = float(np.sum(wt * sh ** 2 * R ** 2)); E0 = float(np.sum(wt * R ** 2)); M = float(np.max(R ** 2))
    return lhs, K * K * E0 + (0.0 if 'WG' in flags else M * T2(K)), E0
