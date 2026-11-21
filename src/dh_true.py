"""Stage DH 2.1: THE TRUE QUANTITY AT THE CORNER for one-carrier windows (the comb of paper F and packets at the focus).  Python 3.11 grammar.
State (cw_direct's notation): p = N_V(v) Gamma(w) h/Z, h = 1 + e^{-omega^2/(2r)} R(T), T = sqrt(tau) nu, and the true quantity
    sigma (a + a') = [2 (sigma^2/L^2) E(S_w^2 (1 - phi/4)) + (b/2) E(S_v^2 phi)] / [b E S_v^2 + (sigma^2/L^2) E S_w^2]
(cw_direct's formula with u = 1/(1 + beta L^2), multiplied above and below by (beta + 1/L^2) sigma^2).
WINDOW.  R(T) = q env(nu) cos(n T - phi0): one carrier n with mu := n^2 x and amplitude q <= 2 e^{-mu/2} (the class: q0_n <= 2 e^{-n^2 x/2}; the comb
f = sum of deltas at spacing 2 pi/n has q = 2 e^{-mu/2} up to e^{-3 mu/2}), env = 1 (the comb) or env^2 = e^{-nu^2 (1/kap - 1)/2} (a Gaussian packet
at the focus: under N(nu) env^2 the variable nu is N(0, kap) with mass sqrt(kap); then kappa = kap, E0 = q^2 sqrt(kap)/2, x E1 = mu E0).
PHASE AVERAGE [derivation].  n sqrt(tau) = sqrt(mu/b) is huge at the corner, so theta = n T - phi0 (mod 2 pi) is uniform and independent of nu up
to e^{-mu/(2b)} (the Fourier coefficients of a Gaussian); the packet needs in addition mu kap/b >> 1 (the carrier is faster than the envelope).
With e = e^{-omega^2/(2r)}, K = sqrt(mu/b) q, D = K e env sin(theta)/h:  S_v = -nu - D,  S_w = -omega (1 + q e env cos(theta)/(r h)).
(T1) CLOSED FORM, second order in q, without the phase corrections chi (they are O(sigma)):  with v2 = r/(2 + r), g_s = sqrt(v2), m0 = sqrt(kap),
  W = mu q^2 g_s m0/2 (= G/2), alpha^2 = (1 - b)^2 sigma^2/(2b), lambda^2 = (L - sigma^2/L)^2/2:
    Num = 2 (sigma^2/L^2)(1 - Psi_om/4) + P2full [3/4 + (1/4) e^{-alpha^2 kap/2} (1 - lambda^2 v2) e^{-lambda^2 v2/2}] + (b/2) Psi_nu
          + (W/2)(1 - e^{-alpha^2 kap/2 - lambda^2 v2/2}),          P2full = (sigma^2/s^2) q^2 m0 g_s/(2 + r) = 2 W sigma^2/(mu s^2 (2 + r)),
    Den = b + W + (sigma^2/L^2)(1 + P2full L^2/(2 sigma^2)),
    Psi_nu = 1 - (1 - alpha^2) e^{-(alpha^2 + lambda^2)/2},  Psi_om = 1 - (1 - lambda^2) e^{-(alpha^2 + lambda^2)/2}   (the Gaussian background, cw_direct).
  Gaussian identities used (checked to 60 digits in check_identities): under N(omega) e^2 the variable omega is N(0, v2) with mass g_s;
  E[cos(c X)] = e^{-c^2 v/2}, E[X^2 cos(c X)] = (v - c^2 v^2) e^{-c^2 v/2} for X ~ N(0, v).
(T2) SEMI-EXACT (the comb, env = 1): nu integrated exactly, theta and omega by quadrature, every order of q and the corrections chi kept (long double):
  m_z = alpha nu + m0,  m0 = [-sigma sqrt(mu) q e sin(theta)/h + L omega + (sigma^2/L) S_w]/sqrt2,
  E_nu[(nu + D)^2 (1 - cos m_z)] = (1 + D^2)(1 - e^{-alpha^2/2} cos m0) + e^{-alpha^2/2} (alpha^2 cos m0 + 2 alpha D sin m0).
CHECKS (run): (C1) T2 against cw_direct.Grid (the direct 2-D integral, no phase average); (C2) T1 against T2 at the corner; (C3) the identities to 60
digits; power: two wrong versions of T1 must be caught by (C2).  -> results/dh_true.json"""
import json, math, sys, time
from decimal import Decimal as Dc, getcontext
import numpy as np

LD = np.longdouble
LSE = np.logaddexp
L2 = math.log(2.0)


def _lpsi(la2, ll2, nu):
    """log Psi_nu (nu=True) or log Psi_om, arrays; la2 = log alpha^2, ll2 = log lambda^2 (any size, no underflow)."""
    a2 = np.exp(np.minimum(la2, 700.0)); l2 = np.exp(np.minimum(ll2, 700.0)); tot = a2 + l2
    small = LSE(math.log(3.0) + la2, ll2) - L2 if nu else LSE(la2, math.log(3.0) + ll2) - L2
    with np.errstate(all='ignore'):
        e = np.exp(-tot / 2); big = np.log(np.maximum(-np.expm1(-tot / 2) + (a2 if nu else l2) * e, 1e-300))
    return np.where(tot < 1e-7, small, big)


def closed(ell, mu, lb, lr, ls2, lkap=0.0, lq=None, wrong=None):
    """(T1): the log of every piece of Num/sigma and of Den, arrays.  Returns dict; 'g' = sqrt(ell) (a + a') (so the claim with coefficient 1 is g >= 1).
    wrong: 'noP2' (the w-gain of the window dropped), 'halfF' (the exponent of the F term halved) -- power checks only."""
    ell, mu, lb, lr, ls2, lkap = (np.asarray(v, float) for v in np.broadcast_arrays(ell, mu, lb, lr, ls2, lkap))
    lq = (L2 - mu / 2) if lq is None else np.asarray(lq, float)
    b = np.exp(lb); r = np.exp(lr); lL2 = ls2 - lr
    la2 = 2 * np.log1p(-b) - L2 - (lb + 2 * ell)                             # alpha^2 = (1 - b)^2 sigma^2/(2b)
    ll2 = lL2 - L2 + 2 * np.log1p(-np.exp(np.minimum(-2 * ell - lL2, -1e-12)))     # lambda^2 = (L - sigma^2/L)^2/2   (L^2 >= 4 sigma^2)
    v2 = r / (2 + r); lv2 = lr - np.log(2 + r); lgs = 0.5 * lv2                # in logarithms: r may underflow at very large ell
    lW = np.log(mu) + 2 * lq + lgs + 0.5 * lkap - L2                         # W = mu q^2 g_s sqrt(kap)/2
    la = -2 * ell - lL2                                                      # sigma^2/L^2
    lam2 = np.exp(np.minimum(ll2, 700.0)); al2k = np.exp(np.minimum(la2 + lkap, 700.0))
    PsO = np.exp(_lpsi(la2, ll2, False))
    lP2f = -2 * ell - ls2 + 2 * lq + 0.5 * lkap + lgs - np.log(2 + r)        # P2full
    with np.errstate(all='ignore'):
        c2 = 0.75 + 0.25 * np.exp(-al2k / 2) * (1 - lam2 * v2) * np.exp(-lam2 * v2 / 2)
        zF = lam2 * v2 / 2; zK = al2k / 2
        if wrong == 'halfF': zF = zF / 2
        lFoc = np.where(zF < 1e-7, ll2 + lv2 - L2 - (L2 if wrong == 'halfF' else 0.0), np.log(np.maximum(-np.expm1(-zF), 1e-300)))      # 1 - e^{-lambda^2 v2/2}
        lChp = np.where(zK < 1e-7, la2 + lkap - L2, np.log(np.maximum(-np.expm1(-zK), 1e-300))) - zF          # e^{-lambda^2 v2/2} (1 - e^{-alpha^2 kap/2})
    P = {'P1': la + L2 + np.log(1 - PsO / 4) + ell, 'P2': (lP2f + np.log(c2) + ell) if wrong != 'noP2' else np.full(ell.shape, -np.inf),
         'P34': lb - L2 + _lpsi(la2, ll2, True) + ell, 'hF': lW - L2 + lFoc + ell, 'chirp': lW - L2 + lChp + ell,
         'd_b': lb, 'd_W': lW, 'd_a': la + np.logaddexp(0.0, lP2f + lL2 + 2 * ell - L2), 'lW': lW, 'la': la}
    ln = np.logaddexp.reduce([P['P1'], P['P2'], P['P34'], P['hF'], P['chirp']], axis=0); ld = np.logaddexp.reduce([P['d_b'], P['d_W'], P['d_a']], axis=0)
    P['g'] = np.sqrt(ell) * np.exp(ln - ld)
    return P


def quad(ell, mu, lb, lr, ls2, lq=None, nth=48, nw=6000, span=9.0, chi=True):
    """(T2): sqrt(ell) (a + a') of the comb state, scalars; long double.  chi=False drops the phase corrections (m0 = L omega/sqrt2 exactly as T1)."""
    ell, mu, lb, lr, ls2 = (LD(v) for v in (ell, mu, lb, lr, ls2)); lq = (LD(L2) - mu / 2) if lq is None else LD(lq)
    sig = np.exp(-ell); b = np.exp(lb); r = np.exp(lr); s2 = np.exp(ls2); Lw = np.sqrt(s2 / r); q = np.exp(lq)
    beta = b / sig ** 2; al = (1 - b) / np.sqrt(2 * beta); K = np.sqrt(mu / b) * q
    a_ = min(2 * np.sqrt(r), LD(1)); xm = np.arcsinh(LD(span) / a_); xi = np.linspace(-xm, xm, nw).astype(LD)
    om = a_ * np.sinh(xi); wo = a_ * np.cosh(xi) * (xi[1] - xi[0]); wo[[0, -1]] *= LD(0.5)
    wo = wo * np.exp(-om ** 2 / 2) / np.sqrt(2 * LD(np.pi))
    th = (np.arange(nth, dtype=LD) + LD(0.5)) * (2 * LD(np.pi) / nth); c = np.cos(th)[:, None]; s = np.sin(th)[:, None]
    e = np.exp(-om ** 2 / (2 * r))[None, :]; h = 1 + q * e * c
    D = K * e * s / h; Sw = -om[None, :] * (1 + q * e * c / (r * h))
    m0 = (Lw * om[None, :]) / np.sqrt(LD(2))
    if chi: m0 = m0 + (-(sig * np.sqrt(mu) * q) * e * s / h + (sig ** 2 / Lw) * Sw) / np.sqrt(LD(2))
    ea = np.exp(-al ** 2 / 2); s2h = 2 * np.sin(m0 / 2) ** 2                       # 1 - cos m0, without cancellation
    omc = -np.expm1(-al ** 2 / 2) + ea * s2h                                       # 1 - e^{-alpha^2/2} cos m0
    Wt = h * wo[None, :] / nth
    tv = (1 + D ** 2) * omc + ea * (al ** 2 * np.cos(m0) + 2 * al * D * np.sin(m0))
    tw = Sw ** 2 * (1 - omc / 4)
    a = sig ** 2 / Lw ** 2
    num = 2 * a * (Wt * tw).sum() + (b / 2) * (Wt * tv).sum(); den = b * (Wt * (1 + D ** 2)).sum() + a * (Wt * Sw ** 2).sum()
    return float(np.sqrt(ell) * num / den / sig), float(Wt.sum())


def grid_value(n, tau, b, r, Lw, ell, q):
    """the same state by cw_direct.Grid (direct quadrature in (nu, omega), no phase average): sqrt(ell) (a + a')."""
    import cw_direct as CW
    q0 = [0.0] * (n - 1) + [q]; g = CW.Grid(q0, [0.3] * n, tau, r, nw=1400)
    lbeta = math.log(b) + 2 * ell
    return math.sqrt(ell) * g.sigQ(lbeta, ell, math.log(Lw)) / math.exp(-ell)


def _dexp(x):
    getcontext().prec = 80; return x.exp()


def _dcos(x):
    getcontext().prec = 80; t = Dc(1); s = Dc(1); k = 0
    while abs(t) > Dc(10) ** -78:
        k += 2; t = -t * x * x / (k * (k - 1)); s += t
    return s


def check_identities():
    """(C3): the Gaussian identities of (T1) in 60-digit decimals (the trapezoid rule on Gaussian integrands; step 0.25 sd, range 20 sd)."""
    getcontext().prec = 80; pi = Dc('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899')
    worst = Dc(0); rows = []
    def integ(f, sd):
        hstep = sd / 4; tot = Dc(0)
        for i in range(-80, 81): tot += f(hstep * i)
        return tot * hstep
    for (r, lam, al) in ((Dc('0.2'), Dc('1.3'), Dc('0.7')), (Dc('1e-9'), Dc('30000'), Dc('0.01')), (Dc('0.03'), Dc('4'), Dc('2.5'))):
        v2 = r / (2 + r); gs = v2.sqrt(); sd = v2.sqrt()
        N = lambda w: _dexp(-w * w / 2) / (2 * pi).sqrt()
        I0 = integ(lambda w: N(w) * _dexp(-w * w / r), sd); I2 = integ(lambda w: N(w) * w * w * _dexp(-w * w / r), sd)
        Ic = integ(lambda w: N(w) * _dexp(-w * w / r) * _dcos(lam * w), sd); I2c = integ(lambda w: N(w) * w * w * _dexp(-w * w / r) * _dcos(lam * w), sd)
        ee = _dexp(-lam * lam * v2 / 2)
        errs = [abs(I0 / gs - 1), abs(I2 / (gs * v2) - 1), abs(Ic - gs * ee) / gs, abs(I2c - gs * (v2 - lam * lam * v2 * v2) * ee) / (gs * v2)]
        J2 = integ(lambda w: N(w) * w * w * _dcos(al * w), Dc(1)); J0 = integ(lambda w: N(w) * _dcos(al * w), Dc(1))
        ea = _dexp(-al * al / 2); errs += [abs(J0 - ea), abs(J2 - (1 - al * al) * ea)]
        worst = max(worst, max(errs)); rows.append([float(x) for x in errs])
    return float(worst), rows


def corner_states(ell, rng, n):
    """random states around the corner (mu/ell, log b + ell, log r + ell/2, log s^2 + ell), inside the class."""
    mu = np.maximum(ell * rng.uniform(0.12, 0.27, n), 2 * math.log(2 * ell) + 0.1)
    return mu, -ell + rng.uniform(-2, 12, n), -ell / 2 + rng.uniform(-4, 6, n), -ell + rng.uniform(-4, 4, n)


def in_class(ell, mu, lb, lr, ls2):
    """the conditions on the STATE of the claim, for a one-carrier state: b in [1e4 sigma^2, 0.5], beta > 2.5e10 (the local route), r <= 1/4, sigma^2 <= s^2, L^2 <= 1/sigma,
    eta = 2 e^{-mu/2}/(1 - e^{-3 mu/2}) <= 1/ell and sum q_n <= 1/4 (mu >= 2 ln(2 ell) + 0.1 suffices for ell >= 55.26), and the phase average
    (mu/(2b) >= 40: e^{-40}).
    CAVEAT (the window).  The pure comb has no fundamental: as a window of its own period it is paper F's S'_C with x' = mu (outside x <= 0.003), and as
    a window of a longer period it violates (P2) (fundamental largest).  Inside the class of paper H the same LOCAL state is reached, up to an O(1)
    factor in brightness, by a coherent packet of high harmonics next to a fundamental (paper H, section 8: the ceiling CM-1 is sharp;
    results/dh_ceiling.json: windows of the class reach 0.648 of the bound; a rough test during the exploration, not shipped, gave
    P >= 0.24 x 4 mu e^{-mu} at kappa ~ 1 and large mu).  A brightness factor c changes (g^2 - 1) ell by about -4 ln c (+5.7 for c = 0.24).
    For the TABLE the state is admissible in any case: the table allows every G up to its ceiling."""
    lL2 = ls2 - lr
    return (lb <= math.log(0.5)) & (lb + 2 * ell > math.log(2.5e10)) & (lr <= math.log(0.25)) & (ls2 >= -2 * ell) & (lL2 <= ell) & \
           (mu >= 2 * np.log(2 * ell) + 0.1) & (np.exp(lb) <= mu / 80)


def worst_comb(ell, rng, n_rand=40000, n_ref=60, steps=400, lkap=0.0):
    """the smallest g = sqrt(ell)(a + a') over comb states at ell (T1): random start, shrinking random steps.  Returns (g_min, state, n evaluated).
    Half of the starts are drawn next to the corner (ell/4 - mu in [0, 60], wider ranges of b, r, s^2) and the steps in mu are at most 8: with
    steps of 0.05 ell alone the minimum at ell >= 1e4 was not reached (the first run was 0.5-1.6 too high in (g^2 - 1) ell there)."""
    mu, lb, lr, ls2 = corner_states(ell, rng, n_rand); h = n_rand // 2
    mu[:h] = np.maximum(ell / 4 - rng.uniform(0, 60, h), 2 * math.log(2 * ell) + 0.1)
    lb[:h] = -ell + rng.uniform(-2, 32, h); lr[:h] = -ell / 2 + rng.uniform(-4, 12, h); ls2[:h] = -ell + rng.uniform(-10, 4, h)
    Y = np.stack([mu, lb, lr, ls2], axis=1)
    def f(Y):
        ok = in_class(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3])
        with np.errstate(all='ignore'): g = closed(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3], lkap)['g']
        return np.where(ok & np.isfinite(g), g, np.inf)
    g = f(Y); idx = np.argsort(g)[:n_ref]; Yr = Y[idx]; gr = g[idx]; W = np.array([min(0.05 * ell, 8.0), 4.0, 3.0, 2.0])
    for s in range(steps):
        sc = (1e-5) ** (s / (steps - 1))
        Z = Yr + rng.normal(size=Yr.shape) * W * sc * (rng.uniform(size=Yr.shape) < 0.7)
        gz = f(Z); bt = gz < gr; Yr = np.where(bt[:, None], Z, Yr); gr = np.where(bt, gz, gr)
    i = int(np.argmin(gr)); y = Yr[i].copy(); gy = float(gr[i]); st = np.array([1.0, 1.0, 1.0, 1.0]); nev = n_rand + n_ref * steps
    while st.max() > 1e-7:                                                            # a pattern search from the best state (the function is smooth)
        moved = False
        for k in range(4):
            for sg in (1.0, -1.0):
                z = y.copy(); z[k] += sg * st[k]; gz = float(f(z[None, :])[0]); nev += 1
                if gz < gy: y, gy, moved = z, gz, True
        if not moved: st = st / 2
    return gy, y, nev


def run(save=True):
    t0 = time.time(); out = {}; rng = np.random.default_rng(20261113)
    # (C3) identities
    w, rows = check_identities(); out['C3 identities (60 digits): largest relative error'] = w
    # (C1) T2 against the direct grid (moderate states where the grid resolves everything)
    c1 = []
    for (n, tau, b, r, Lw, ell, q) in ((6, 2.0, 0.2, 0.2, 1.0, 2.0, 0.1), (5, 3.0, 0.1, 0.05, 0.7, 3.0, 0.05), (7, 1.5, 0.3, 0.1, 1.5, 2.5, 0.2), (6, 2.5, 0.05, 0.02, 0.5, 4.0, 0.02),
                                       (8, 1.2, 0.15, 0.25, 0.4, 3.0, 0.15)):
        mu = n * n * tau * b; s2 = r * Lw * Lw
        gq, z = quad(ell, mu, math.log(b), math.log(r), math.log(s2), lq=math.log(q), nth=96, nw=3000)
        gg = grid_value(n, tau, b, r, Lw, ell, q)
        g1 = float(closed(ell, mu, math.log(b), math.log(r), math.log(s2), lq=math.log(q))['g'])
        c1.append({'n': n, 'tau': tau, 'b': b, 'r': r, 'L': Lw, 'ell': ell, 'q': q, 'T2': gq, 'grid': gg, 'T2/grid - 1': gq / gg - 1, 'T1/T2 - 1 (O(q^2), chi)': g1 / gq - 1, 'Z - 1': z - 1})
    out['C1 T2 against cw_direct.Grid'] = c1; out['C1 largest |T2/grid - 1|'] = max(abs(c['T2/grid - 1']) for c in c1)
    # (C2) T1 against T2 at corner states; the worst comb state per ell
    c2 = []; worst = {}
    for ell in (55.26, 82.89, 100.0, 165.78, 331.56, 663.1, 955.8):
        gmin, y, nev = worst_comb(ell, rng)
        gq, _ = quad(ell, *y); gq0, _ = quad(ell, *y, chi=False)
        worst[str(ell)] = {'g sqrt(ell) (T1)': gmin, 'T2': gq, 'T2 without chi': gq0, '(g^2 - 1) ell': (gmin ** 2 - 1) * ell, '(g - 1) ell': (gmin - 1) * ell,
                           'mu': float(y[0]), 'mu/ell': float(y[0] / ell), 'ell/4 - mu': float(ell / 4 - y[0]), 'log b + ell': float(y[1] + ell),
                           'log r + ell/2': float(y[2] + ell / 2), 'log s^2 + ell': float(y[3] + ell), 'states evaluated': nev}
        mu, lb, lr, ls2 = corner_states(ell, rng, 12); ok = in_class(ell, mu, lb, lr, ls2)
        for i in np.where(ok)[0][:8]:
            g1 = float(closed(ell, mu[i], lb[i], lr[i], ls2[i])['g']); g2, _ = quad(ell, mu[i], lb[i], lr[i], ls2[i])
            wr = [float(closed(ell, mu[i], lb[i], lr[i], ls2[i], wrong=w_)['g']) / g2 - 1 for w_ in ('noP2', 'halfF')]
            c2.append({'ell': ell, 'T1/T2 - 1': g1 / g2 - 1, 'q^2': 4 * math.exp(-mu[i]), 'wrong noP2': wr[0], 'wrong halfF': wr[1]})
        print(ell, worst[str(ell)], flush=True)
    out['C2 T1 against T2'] = c2; out['C2 largest |T1/T2 - 1|'] = max(abs(c['T1/T2 - 1']) for c in c2)
    out['C2 power: wrong versions caught (|diff| > 1e-3)'] = {w_: int(sum(abs(c['wrong ' + w_]) > 1e-3 for c in c2)) for w_ in ('noP2', 'halfF')}
    out['worst comb state per ell'] = worst
    # the very large ell (T1 only: the closed form in logarithms)
    big = {}
    for ell in (3000.0, 1e4, 3e4, 1e5, 1.5e5, 2e5, 3e5, 1e6):
        gmin, y, nev = worst_comb(ell, rng)
        big[str(ell)] = {'g sqrt(ell)': gmin, '(g - 1) ell': (gmin - 1) * ell, '(g^2 - 1) ell': (gmin ** 2 - 1) * ell, 'below 1 + 2.5e-4': bool(gmin < 1 + 2.5e-4),
                         'mu/ell': float(y[0] / ell), 'ell/4 - mu': float(ell / 4 - y[0]), 'log b + ell': float(y[1] + ell), 'log r + ell/2': float(y[2] + ell / 2),
                         'log s^2 + ell': float(y[3] + ell), 'paper F upper bound 1 + 6 ln(ell)/ell': 1 + 6 * math.log(ell) / ell,
                         'leading order [derivation] 4.5 ln(ell) + 3.09 for (g^2 - 1) ell': 4.5 * math.log(ell) + 3.09}
        print(ell, big[str(ell)], flush=True)
    out['worst comb state at very large ell (T1)'] = big
    out['first run at very large ell (steps of 0.05 ell in mu: not converged), (g^2 - 1) ell'] = {'3000.0': 39.59, '10000.0': 46.1295, '30000.0': 50.7539, '100000.0': 55.5699, '150000.0': 57.2918, '200000.0': 59.2258, '300000.0': 60.6027, '1000000.0': 66.5899}
    out['ok'] = bool(out['C3 identities (60 digits): largest relative error'] < 1e-60 and out['C1 largest |T2/grid - 1|'] < 1e-5 and out['C2 largest |T1/T2 - 1|'] < 2e-3
                     and all(v >= 1 for v in out['C2 power: wrong versions caught (|diff| > 1e-3)'].values()))
    out['seconds'] = time.time() - t0
    print(json.dumps({k: v for k, v in out.items() if not isinstance(v, (list, dict))}))
    if save: json.dump(out, open('results/dh_true.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    run()
