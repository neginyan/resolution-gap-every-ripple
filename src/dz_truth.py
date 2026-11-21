"""Stage DZ, item 2.2: THE TRUE QUANTITY (a) + (a') OF A PERIODIC WINDOW STATE, AT ANY ell (the method of DZ_探索計画.md section 1).  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
The state p = N_V(v) Gamma(w) h(t, w)/Z, h = 1 + E R(t + t0), E = exp(-w^2/(2 s^2)), t = k' v, in the variables of Lemma 18 of paper I:
    v = sqrt(V) s^,  t = sqrt(tau) s^ (the focus t0 is put into R),  sigma s_v = -S,  S = sqrt(b) s^ - E X1/h,  X1 = sqrt(x) R'(t),
    sigma s_w = -sigma w (1/L^2 + E R/(s^2 h)),   m_z = u + v_w + chi,  u = sqrt(y) s^,  v_w = w/sqrt2,  chi = sigma E X1/(sqrt2 h) - (sigma^2 w/sqrt2)(1/L^2 + E R/(s^2 h)).
Then  Z = <h>,  sigma^2 Z J_vv = <h S^2>,  sigma^2 Z J_ww = <h (sigma s_w)^2>,  sigma^2 Z E[s_w^2 phi] = <h (sigma s_w)^2 phi>,  sigma^2 Z E[s_v^2 phi] = <h S^2 phi>,
phi = 1 - cos m_z,  <.> = int Gamma(w) dw E_{s^}[.],  and  (a) + (a') = (2 A_w + N_phi)/(sigma den),  den = sigma^2 (J_vv + J_ww),  A_w = sigma^2 (J_ww - E[s_w^2 phi]/4),
N_phi = sigma^2 E[s_v^2 phi]/2  (as in dp_truth.direct of paper I).  Nothing is expanded or dropped:
  * the s^ average is exact: s^ enters only as s^^k (k <= 2), 1 - cos(u) and sin(u); the t-dependence is a 2 pi-periodic function, written by its Fourier
    coefficients c_n on M points, and E[s^^k U(s^) e^{i n sqrt(tau) s^}] is i^k He_k(theta) e^{-theta^2/2} (theta = n sqrt(tau)) with a series in delta = sqrt(y);
  * the w average is Gauss-Legendre on panels cut at the two scales s and L;
  * 1 - cos(u + c) = (1 - cos c) + (1 - cos u) cos c + sin u sin c,  1 - cos c = 2 sin^2(v_w/2) cos chi + 2 sin^2(chi/2) + sin v_w sin chi  (no cancellation);
  * everything in np.longdouble (exponent range 1e+-4932: sigma = e^{-960.8} and sigma^3 are representable); the FFT is done in double on rows scaled to 1.
VARIANTS (deliberately wrong, for the power of the search): 'drop III' (the term <E^2 X1^2/h phi> of N_phi left out), 'sign' (the scores computed with
1 - E R in place of h, the density keeping h), 'sandwich' (den's brightness part times 1/(1 - eta)^2 and the ripple part of the numerator times 1/(1 + eta)^2:
an artificial worst case of the sandwich, used only to check that the families can reach a low value if one existed).
DIAGNOSTIC (not a wrong version): 'h1' computes the scores with 1 in place of h (the density keeps h): the same window and state with the factors 1/h of the
scores removed; Q/Q_h1 measures how much the ripple sandwich acts inside the true quantity."""
import math
import numpy as np

LD = np.longdouble
SQ2 = np.sqrt(LD(2))
_GL = {}


def gl(n, F):
    if (n, F) not in _GL:
        x, w = np.polynomial.legendre.leggauss(n); _GL[(n, F)] = (x.astype(F), w.astype(F))
    return _GL[(n, F)]


def hermite_moments(kmax, theta, LD=LD):
    """array H[k, i] = E[s^^k e^{i theta_i s^}] = i^k He_k(theta_i) e^{-theta_i^2/2}, k = 0..kmax (complex longdouble)."""
    th = np.asarray(theta, dtype=LD); g = np.exp(-th * th / 2)
    He = np.zeros((kmax + 1, th.size), dtype=LD); He[0] = 1
    if kmax >= 1: He[1] = th
    for k in range(1, kmax): He[k + 1] = th * He[k] - k * He[k - 1]
    ik = np.array([1, 1j, -1, -1j])
    out = np.zeros((kmax + 1, th.size), dtype=np.clongdouble)
    for k in range(kmax + 1): out[k] = ik[k % 4] * He[k] * g
    return out


def moments(k, j, theta, delta, LD=LD):
    """E[s^^k U_j(s^) e^{i theta s^}], U_1 = 1, U_c = 1 - cos(delta s^), U_s = sin(delta s^); exact (series in delta for delta < 0.5)."""
    th = np.asarray(theta, dtype=LD); d = LD(delta)
    if j == '1': return hermite_moments(k, th)[k]
    if d >= LD('0.5'):
        Hm, H0, Hp = (hermite_moments(k, th + sh, LD)[k] for sh in (-d, LD(0), d))
        return H0 - (Hp + Hm) / 2 if j == 'c' else (Hp - Hm) / (2j)
    mmax = 12 if d < LD('0.05') else 40; H = hermite_moments(k + 2 * mmax + 1, th, LD); out = np.zeros(th.size, dtype=np.clongdouble); fact = LD(1); dp = LD(1)
    for p in range(1, 2 * mmax + 2):
        fact *= p; dp *= d
        if j == 'c' and p % 2 == 0: out += (-1) ** (p // 2 + 1) * dp / fact * H[k + p]
        if j == 's' and p % 2 == 1: out += (-1) ** ((p - 1) // 2) * dp / fact * H[k + p]
    return out


def w_nodes(L, s, F=LD, order=10):
    """Gauss-Legendre nodes and weights for int Gamma(w) F(w) dw, Gamma = N(0, L^2): panels in omega = w/L cut at the scale s/L and, when L > 1, at width
    <= 1/L in omega (the oscillation of cos(w/sqrt2))."""
    rs = float(s / L); br = {0.0, 10.0}
    for c in (0.0625, 0.125, 0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4, 5, 6, 8):
        br.add(c * rs) if c * rs < 10 else None; br.add(float(c))
    Lf = float(L)
    if Lf > 1:
        n = int(min(4000, math.ceil(5 * Lf))); [br.add(10.0 * i / n) for i in range(1, n)]
    br = np.array(sorted(b for b in br if 0 <= b <= 10), dtype=F)
    GX, GW = gl(order, F)
    a, c = br[:-1], br[1:]; mid = (a + c) / 2; hw = (c - a) / 2
    om = (mid[:, None] + hw[:, None] * GX[None, :]).ravel(); wt = (hw[:, None] * GW[None, :]).ravel()
    om = np.concatenate([-om[::-1], om]); wt = np.concatenate([wt[::-1], wt])
    dens = np.exp(-om * om / 2) / np.sqrt(2 * F(np.pi))
    return om * L, wt * dens


def w_nodes_split(L, s, F=LD, order=10):
    """nodes and weights (with the density of Gamma = N(0, L^2)) on |w| <= 14 s: the support of the ripple part when the envelope is wide (L > 3)."""
    sf = float(s); br = {0.0, 14.0 * sf}
    for c in (0.0625, 0.125, 0.25, 0.5, 0.75, 1, 1.5, 2, 3, 4, 5, 6, 8, 10, 12): br.add(c * sf)
    if sf > 0.5:
        n = int(math.ceil(14 * sf / 0.5))
        if n > 6000: raise ValueError('s too large for the split form')
        [br.add(14.0 * sf * i / n) for i in range(1, n)]
    br = np.array(sorted(br), dtype=F); GX, GW = gl(order, F)
    a, c = br[:-1], br[1:]; mid = (a + c) / 2; hw = (c - a) / 2
    w = (mid[:, None] + hw[:, None] * GX[None, :]).ravel(); wt = (hw[:, None] * GW[None, :]).ravel()
    w = np.concatenate([-w[::-1], w]); wt = np.concatenate([wt[::-1], wt])
    return w, wt * np.exp(-w * w / (2 * L * L)) / (np.sqrt(2 * F(np.pi)) * L)


def window_vals(q, ph, t):
    """R and R' on the array t, R = sum q_n cos(n t - ph_n)."""
    F = t.dtype.type; R = np.zeros_like(t); Rp = np.zeros_like(t)
    for n, (qq, pp) in enumerate(zip(q, ph), start=1):
        if qq == 0: continue
        arg = n * t - F(pp); R += F(qq) * np.cos(arg); Rp -= n * F(qq) * np.sin(arg)
    return R, Rp


def _fourier_expect(vec, k, j, sqtau, delta, ncut):
    LD = vec.dtype.type
    """sum_n c_n E[s^^k U_j e^{i n sqrt(tau) s^}] for the periodic function with samples vec on t_m = 2 pi m/M (vec real, longdouble)."""
    M = vec.size; sc = np.max(np.abs(vec))
    if sc == 0: return LD(0)
    c = np.fft.fft((vec / sc).astype(np.float64)) / M
    ns = np.arange(-ncut, ncut + 1)
    if ncut == 0 and j == '1' and k == 0: return LD(c[0].real) * sc
    cn = c[ns % M].astype(np.clongdouble) * LD(sc)
    mom = moments(k, j, ns.astype(LD) * sqtau, delta, LD)
    return (cn * mom).sum().real


def truth(ell, B=None, b=None, x=None, a=None, r=None, q=(0.25,), ph=(0.0,), t0=0.0, variant=None, M=None, local=True, prec='ld', order=10, path=None, M_rule='fine', force_split=None):
    """the true (a) + (a') and the local quantities. Give B (b = B sigma^2) or b.  prec 'ld' (np.longdouble, any ell) or 'd' (float64, ell <= 200)."""
    LD = np.longdouble if prec == 'ld' else np.float64
    ell = LD(ell); sig = np.exp(-ell); SQ2 = np.sqrt(LD(2))
    b = LD(B) * sig * sig if b is None else LD(b)
    x = LD(x); a = LD(a); r = LD(r)
    L2 = 4 * sig / a; s2 = r * L2; L = np.sqrt(L2); s = np.sqrt(s2)
    tau = x / b; sqtau = np.sqrt(tau); y = (1 - b) ** 2 * sig * sig / (2 * b); delta = np.sqrt(y)
    nmax = max(i + 1 for i, v in enumerate(q) if v != 0) if any(v != 0 for v in q) else 1
    nc0 = int(min(LD(10 ** 9), np.floor(40 / sqtau))) if sqtau > 0 else 10 ** 9
    # the t-grid: products such as X1^2/h carry frequencies up to about 4 nmax with weights of second order in eta, which alias into the mean on a
    # grid of 2.5 nmax points ('fast', the grid of the search objective; up to 0.5% off); 'fine' (default; every reported value) takes 4.5 nmax + 64
    if M is None and M_rule == 'fast': M = int(2 ** math.ceil(math.log2(max(64, 2.5 * nmax + 2 * min(nc0, 4 * nmax) + 8))))
    if M is None: M = int(2 ** math.ceil(math.log2(max(64, 4.5 * nmax + 2 * min(nc0, 4 * nmax) + 64))))
    ncut = int(min(M // 2 - 1, nc0))
    gh = (float(sqtau) * nmax <= 25 and ncut > 64) if path is None else (path == 'gh')
    if gh:
        # narrow focus: Gauss-Hermite in s^ (t = t0 + sqrt(tau) s^ stays on a short arc), the same integrand
        xs, ws = np.polynomial.hermite_e.hermegauss(128); xs = xs.astype(LD); ws = (ws / ws.sum()).astype(LD)
        t = LD(t0) + sqtau * xs; M = xs.size; ncut = -1
    else:
        t = 2 * LD(np.pi) * np.arange(M, dtype=LD) / M + LD(t0)
    R, Rp = window_vals(q, ph, t)
    # SPLIT FORM (only when L > 3, never in the main search, whose box has L <= 3): the state with R = 0 in closed form (Lemma 11 of paper I), plus the
    # ripple part, which is supported on |w| <~ 14 s (E = e^{-98} beyond), integrated on the s scale; see g0_closed for the closed form
    split = float(L) > 3 if force_split is None else force_split
    w, wt = w_nodes_split(L, s, LD, order) if split else w_nodes(L, s, LD, order)
    eta = float(np.max(np.abs(R))) if variant == 'sandwich' else 0.0
    terms = [('Z', 0, '1'), ('H2', 2, '1'), ('H1', 1, '1'), ('H0', 0, '1'), ('Wt', 0, '1'), ('WtA0', 0, '1'), ('WtA1', 0, 'c'), ('WtA2', 0, 's')]
    for k in (2, 1, 0): terms += [('S%dA0' % k, k, '1'), ('S%dA1' % k, k, 'c'), ('S%dA2' % k, k, 's')]
    acc = {nm: np.zeros(M, dtype=LD) for nm, _, _ in terms}
    Rr = R[None, :]; Rpp = Rp[None, :]; X1 = np.sqrt(x) * Rpp
    ch = max(8, int(2 ** 21 // M))                      # rows of w per chunk (memory)
    for i in range(0, w.size, ch):
        ww = w[i:i + ch, None]; Wc = wt[i:i + ch, None]
        E = np.exp(-ww * ww / (2 * s2))
        h = 1 + E * Rr; hs = (1 - E * Rr) if variant == 'sign' else (np.ones_like(h) if variant == 'h1' else h)
        chiv = sig * E * X1 / (SQ2 * hs); fw = 1 / L2 + E * Rr / (s2 * hs); chiw = -(sig * sig * ww / SQ2) * fw
        chi = chiv + chiw; vw = ww / SQ2
        A0 = 2 * np.sin(vw / 2) ** 2 * np.cos(chi) + 2 * np.sin(chi / 2) ** 2 + np.sin(vw) * np.sin(chi)
        A1 = np.cos(vw + chi); A2 = np.sin(vw + chi)
        H = {2: b * h, 1: -2 * np.sqrt(b) * E * X1 * (h / hs), 0: h * E * E * X1 * X1 / (hs * hs)}
        if variant == 'sandwich': H[0] = H[0] / LD(1 - eta) ** 2
        Wt = sig * sig * ww * ww * h * fw * fw
        acc['Z'] += (Wc * h).sum(axis=0); acc['Wt'] += (Wc * Wt).sum(axis=0)
        for k in (2, 1, 0):
            acc['H%d' % k] += (Wc * H[k]).sum(axis=0)
            if variant == 'drop III' and k == 0: continue
            Hn = H[k] * (LD(1 + eta) ** -2 * LD(1 - eta) ** 2) if (variant == 'sandwich' and k == 0) else H[k]
            WH = Wc * Hn
            acc['S%dA0' % k] += (WH * A0).sum(axis=0); acc['S%dA1' % k] += (WH * A1).sum(axis=0); acc['S%dA2' % k] += (WH * A2).sum(axis=0)
        WW = Wc * Wt
        acc['WtA0'] += (WW * A0).sum(axis=0); acc['WtA1'] += (WW * A1).sum(axis=0); acc['WtA2'] += (WW * A2).sum(axis=0)
        if split:     # subtract the same integrand with R = 0 (h = 1, E X1 = 0, chi = chi_w(R = 0)); the closed form is added below
            one = np.ones_like(h); fw0 = one / L2; chi0 = -(sig * sig * ww / SQ2) * fw0
            B0 = 2 * np.sin(vw / 2) ** 2 * np.cos(chi0) + 2 * np.sin(chi0 / 2) ** 2 + np.sin(vw) * np.sin(chi0)
            B1 = np.cos(vw + chi0); B2 = np.sin(vw + chi0); Wt0 = sig * sig * ww * ww * fw0 * fw0
            acc['Z'] -= (Wc * one).sum(axis=0); acc['Wt'] -= (Wc * Wt0).sum(axis=0); acc['H2'] -= (Wc * b * one).sum(axis=0)
            WB = Wc * b * one
            acc['S2A0'] -= (WB * B0).sum(axis=0); acc['S2A1'] -= (WB * B1).sum(axis=0); acc['S2A2'] -= (WB * B2).sum(axis=0)
            WW0 = Wc * Wt0
            acc['WtA0'] -= (WW0 * B0).sum(axis=0); acc['WtA1'] -= (WW0 * B1).sum(axis=0); acc['WtA2'] -= (WW0 * B2).sum(axis=0)
    if gh:
        u = delta * xs; Uj = {'1': np.ones_like(xs), 'c': 2 * np.sin(u / 2) ** 2, 's': np.sin(u)}
        ex = {nm: (acc[nm] * ws * xs ** k * Uj[j]).sum() for nm, k, j in terms}
    else:
        ex = {nm: _fourier_expect(acc[nm], k, j, sqtau, delta, ncut) for nm, k, j in terms}
    Z = ex['Z']; Jv = ex['H2'] + ex['H1'] + ex['H0']; Jw = ex['Wt']
    Sw = ex['WtA0'] + ex['WtA1'] + ex['WtA2']
    Sv = sum(ex['S%dA0' % k] + ex['S%dA1' % k] + ex['S%dA2' % k] for k in (2, 1, 0))
    if split:         # the closed form of the state with R = 0 (Lemma 11 of paper I): Z = 1, sigma^2 J_vv = b, sigma^2 J_ww = sigma^2/L^2,
        #   sigma^2 E[s_w^2 phi] = sigma^2 (1 - (1 - c^2) e)/L^2,  sigma^2 E[s_v^2 phi] = b (1 - (1 - alpha^2) e)
        al2 = sig * sig * (1 - b) ** 2 / (2 * b); c2 = (L - sig * sig / L) ** 2 / 2; tt = (al2 + c2) / 2; e0 = np.exp(-tt); om = -np.expm1(-tt)
        Z = Z + 1; Jv = Jv + b; Jw = Jw + sig * sig / L2; Sw = Sw + sig * sig * (om + c2 * e0) / L2; Sv = Sv + b * (om + al2 * e0)
    den = (Jv + Jw) / Z; Aw = (Jw - Sw / 4) / Z; Nphi = Sv / (2 * Z)
    val = (2 * Aw + Nphi) / (sig * den)
    out = {'W/b (ripple part of den over b)': float(ex['H0'] / Z / b), '(a)+(a\')': float(val), 'Q sqrt(ell)': float(val * np.sqrt(ell)), 'log Q sqrt(ell)': float(np.log(val * np.sqrt(ell))) if val > 0 else float('nan'), 'den': den, 'Aw': Aw, 'Nphi': Nphi, 'Z': Z, 'M': M, 'nw': int(w.size), 'ncut': ncut, 'path': ('Gauss-Hermite' if gh else 'Fourier') + (', split' if split else '')}
    if local:
        if gh:
            E0 = (ws * R * R).sum(); E1 = (ws * Rp * Rp).sum(); kap = (ws * xs * xs * Rp * Rp).sum() / E1 if E1 > 0 else LD(1)
        else:
            E0 = _fourier_expect(R * R, 0, '1', sqtau, 0, ncut); E1 = _fourier_expect(Rp * Rp, 0, '1', sqtau, 0, ncut)
            kap = _fourier_expect(Rp * Rp, 2, '1', sqtau, 0, ncut) / E1 if E1 > 0 else LD(1)
        gs = np.sqrt(r / (2 + r)); P = 2 * x * E1
        out.update({'E0': float(E0), 'E1': float(E1), 'kappa': float(kap), 'mu': float(x * E1 / E0) if E0 > 0 else float('inf'), 'P': float(P), 'G': float(gs * P),
                    'tau': float(tau), 'y': float(y), 'eta': float(np.max(np.abs(R))), 'L': float(L), 's': float(s)})
    return out


def g0_closed(ell, b, L2=None, a=None):
    """(a) + (a') for R = 0 in closed form (proof of Lemma 11 of paper I), in Decimal with 1200 digits: Q = [A1/L^2 + A2/V]/[2 sigma (1/L^2 + 1/V)],
    A1 = 3 + (1 - c^2) e,  A2 = 1 - (1 - alpha^2) e,  e = exp(-(alpha^2 + c^2)/2),  alpha = sigma (1 - b)/sqrt(2b),  c = (L - sigma^2/L)/sqrt2."""
    from decimal import Decimal as Dc, localcontext
    with localcontext() as C:
        C.prec = 1200; C.Emin = -10 ** 6
        sig = (-Dc(repr(ell))).exp(); b = Dc(repr(b))
        L2 = 4 * sig / Dc(repr(a)) if a is not None else Dc(repr(L2))
        V = sig ** 2 / b; L = L2.sqrt()
        al = sig * (1 - b) / (2 * b).sqrt(); c = (L - sig ** 2 / L) / Dc(2).sqrt(); t = (al ** 2 + c ** 2) / 2
        e = (-t).exp(); A1 = 3 + (1 - c ** 2) * e; A2 = 1 - (1 - al ** 2) * e
        return float((A1 / L2 + A2 / V) / (2 * sig * (1 / L2 + 1 / V)))
