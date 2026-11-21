"""Stage CW 2.1: the TRUE quantity (a) + (a') = (2 A_w + N_phi)/(sigma den) of the local route at large ell, by quadrature in dimensionless variables.
Python 3.11 grammar.  (plan: CW_探索計画.md sec. 0)
State: p = N_V(v) Gamma(w) h(k'v, w)/Z, h = 1 + e^{-w^2/2s^2} R(t), V = sigma^2/b, k' = sqrt(x)/sigma (ca_reduction.direct).  With v = sqrt(V) nu, w = L omega:
  T = k' v = sqrt(tau) nu,  sqrt(V) = beta^{-1/2} (beta = b/sigma^2),  e^{-w^2/2s^2} = e^{-omega^2/(2r)} (r = s^2/L^2),
  S_v := sqrt(V) s_v = -nu + sqrt(tau) h_T/h,   S_w := L s_w = -omega - (omega/r) e^{-omega^2/(2r)} R/h,
  m_z = [beta^{-1/2}(nu + b S_v) + (L omega + (sigma^2/L) S_w)]/sqrt2,   phi = 1 - cos m_z = 2 sin^2(m_z/2),
  with u = 1/(1 + beta L^2) (the share of 1/L^2 in beta + 1/L^2):
  sigma (a + a') = [2 u E(S_w^2 (1 - phi/4)) + ((1 - u)/2) E(S_v^2 phi)] / [(1 - u) E S_v^2 + u E S_w^2]      (exact rewriting).
The claim of the local route: (a) + (a') >= gamma = T_0(ell)/sqrt(ell), T_0 = 1 + 2.1/ell + 2.5e-4.  Reported: log((a + a')/gamma).
G = 0 exactly (R = 0, Gaussian): E[nu^2 phi] = 1 - (1 - al^2) e^{-(al^2 + la^2)/2}, E[om^2 phi] = 1 - (1 - la^2) e^{-(al^2 + la^2)/2},
  al = beta^{-1/2}(1 - b)/sqrt2, la = (L - sigma^2/L)/sqrt2 (closed_form_G0)."""
import math
import numpy as np


class Grid:
    """the window part of the state (depends on the window, tau, r only); expectations under p."""
    def __init__(self, q0, ph, tau, r, nv=None, nw=900, span=9.0):
        n_max = max((i + 1 for i, q in enumerate(q0) if q != 0), default=1)
        if nv is None: nv = int(min(60000, max(3000, 2 * span * math.sqrt(tau) * n_max / (2 * math.pi) * 40)))
        nu = np.linspace(-span, span, nv)
        r = max(r, 1e-300)                                                         # r below e^-690: the envelope is a spike thinner than any grid step
        a_ = max(min(2 * math.sqrt(r), 1.0), 1e-140)                               # omega = a sinh(xi): fine near 0 (the envelope e^{-omega^2/(2r)}),
        xi = np.linspace(-math.asinh(span / a_), math.asinh(span / a_), nw)       # smooth map -> the trapezoid rule in xi converges fast
        om = a_ * np.sinh(xi)
        wn = np.full(nv, nu[1] - nu[0]); wn[[0, -1]] *= 0.5
        wo = a_ * np.cosh(xi) * (xi[1] - xi[0]); wo[[0, -1]] *= 0.5
        T = math.sqrt(tau) * nu
        R = np.zeros_like(T); Rp = np.zeros_like(T)
        for n, (q, p_) in enumerate(zip(q0, ph), start=1):
            if q: R += q * np.cos(n * T - p_); Rp += -n * q * np.sin(n * T - p_)
        env = np.exp(-om ** 2 / (2 * r))
        H = 1 + env[None, :] * R[:, None]
        self.Sv = -nu[:, None] + math.sqrt(tau) * env[None, :] * Rp[:, None] / H
        self.Sw = -om[None, :] - (om / r * env)[None, :] * R[:, None] / H
        W = (np.exp(-nu ** 2 / 2) * wn)[:, None] * (np.exp(-om ** 2 / 2) * wo)[None, :] * H
        self.P = W / W.sum(); self.nu = nu; self.om = om
        self.Ev = float((self.P * self.Sv ** 2).sum()); self.Ew = float((self.P * self.Sw ** 2).sum())
        self.eta = float(np.max(np.abs(R))) if len(R) else 0.0
        self.E1 = float(np.sum(np.exp(-nu ** 2 / 2) * wn * Rp ** 2) / np.sum(np.exp(-nu ** 2 / 2) * wn))     # local E1 = <theta_tau R'^2>

    def moments(self):
        """E[S^2 X Y] for S in (S_v, S_w) and X, Y in (n: nu, p: S_v, w: omega, s: S_w): the pieces of E[S^2 m_z^2] in the tiny-m regime."""
        if hasattr(self, '_M'): return self._M
        X = {'n': self.nu[:, None] + 0 * self.Sv, 'p': self.Sv, 'w': self.om[None, :] + 0 * self.Sw, 's': self.Sw}
        M = {}
        for key, S2 in (('Sv2', self.Sv ** 2), ('Sw2', self.Sw ** 2)):
            M[key] = {a + b: float((self.P * S2 * X[a] * X[b]).sum()) for a in 'npws' for b in 'npws'}
        self._M = M
        return M

    def sigQ(self, lbeta, ell, lL, nphi_factor=1.0):
        """sigma (a + a') at (beta, sigma = e^-ell, L); nphi_factor < 1 is the deliberately weakened version (power check)."""
        b = math.exp(lbeta - 2 * ell); u = 1.0 / (1.0 + math.exp(min(lbeta + 2 * lL, 700.0)))
        m1 = math.exp(-lbeta / 2) * (self.nu[:, None] + b * self.Sv)
        m2 = math.exp(lL) * self.om[None, :] + math.exp(min(-2 * ell - lL, 700.0)) * self.Sw
        mz = (m1 + m2) / math.sqrt(2); phi = 2 * np.sin(mz / 2) ** 2
        num = 2 * u * float((self.P * self.Sw ** 2 * (1 - phi / 4)).sum()) + nphi_factor * (1 - u) / 2 * float((self.P * self.Sv ** 2 * phi).sum())
        den = (1 - u) * self.Ev + u * self.Ew
        return num / den


def _lse(terms):
    """log of a sum of signed terms given as (sign, log|value|); returns (sign, log|sum|)."""
    terms = [(sg, lv) for sg, lv in terms if sg != 0 and np.isfinite(lv)]
    if not terms: return 0, -math.inf
    m = max(lv for _, lv in terms); tot = sum(sg * math.exp(lv - m) for sg, lv in terms)
    return (1 if tot > 0 else (-1 if tot < 0 else 0)), (m + math.log(abs(tot)) if tot != 0 else -math.inf)


def _log_u(c):
    """log u and log(1 - u) for u = 1/(1 + e^c)."""
    lu = -(c + math.log1p(math.exp(-c))) if c > 0 else -math.log1p(math.exp(c))
    l1u = -math.log1p(math.exp(-c)) if c > 0 else c - math.log1p(math.exp(c))
    return lu, l1u


def log_sigQ(g, lbeta, ell, lL, nphi_factor=1.0, closed=False):
    """log of sigma (a + a'), valid at every ell (no underflow): where every |m_z| on the grid is < 1e-6, phi = m_z^2/2 to relative 1e-12 and the
    phi-moments are expanded in grid moments times scale factors computed in logarithms; otherwise the float64 path (Grid.sigQ / closed_form_G0)."""
    lsv = -lbeta / 2                                   # log beta^{-1/2}
    lsl = -2 * ell - lL                                # log sigma^2/L
    lb = lbeta - 2 * ell
    big = max(lsv, lL, lsl) + math.log(12.0)
    if big > math.log(1e-6):
        v = closed_form_G0(lbeta, ell, lL, nphi_factor) if closed else g.sigQ(lbeta, ell, lL, nphi_factor)
        return math.log(v) if v > 0 else -math.inf
    c = lbeta + 2 * lL; lu, l1u = _log_u(c)
    if closed:   # Gaussian: S_v = -nu, S_w = -omega: E[nu^2 m^2]/2 etc. with m = (al' nu + la' omega), al' = beta^{-1/2}(1-b), la' = L - sigma^2/L
        la_ = lL + math.log1p(-math.exp(lsl - lL)) if lsl < lL else None
        lal = lsv + math.log1p(-math.exp(lb))
        # E[nu^2 phi] = E[nu^2 m^2]/4 (m_z = m/sqrt2, phi = m_z^2/2):  E[nu^2 (al nu + la om)^2] = 3 al^2 + la^2
        _, lB = _lse([(1, math.log(3) + 2 * lal), (1, 2 * la_ if la_ is not None else -math.inf)]); lB -= math.log(4)
        _, lW = _lse([(1, 2 * lal), (1, math.log(3) + 2 * la_ if la_ is not None else -math.inf)]); lW -= math.log(4)
        lEv = 0.0; lEw = 0.0
    else:
        M = g.moments()
        # m = beta^{-1/2} nu + beta^{-1/2} b S_v + L omega + (sigma^2/L) S_w (components n, p, w, s); E[S^2 m^2] from the moments, scales in logs
        sc = {'n': lsv, 'p': lsv + lb, 'w': lL, 's': lsl}
        def quad(key):
            T = []
            for ia, a_ in enumerate('npws'):
                for b_ in 'npws'[ia:]:
                    mom = M[key][a_ + b_]
                    if mom == 0: continue
                    mult = 1 if a_ == b_ else 2
                    T.append((1 if mom > 0 else -1, math.log(mult * abs(mom)) + sc[a_] + sc[b_]))
            return _lse(T)
        sB, lB = quad('Sv2'); sW, lW = quad('Sw2')
        lB -= math.log(4); lW -= math.log(4)
        if sB <= 0: lB = -math.inf
        lEv = math.log(g.Ev); lEw = math.log(g.Ew)
    # A' = E[S_w^2 (1 - phi/4)] = Ew - E[S_w^2 phi]/4 (the correction is < 1e-12 relative here)
    lA = (math.log(g.Ew) if not closed else 0.0) + math.log1p(-math.exp(lW - ((math.log(g.Ew) if not closed else 0.0) + math.log(4)))) if np.isfinite(lW) else ((math.log(g.Ew) if not closed else 0.0))
    _, lnum = _lse([(1, math.log(2) + lu + lA), (1, math.log(nphi_factor / 2) + l1u + lB)])
    _, lden = _lse([(1, l1u + lEv), (1, lu + lEw)])
    return lnum - lden


def gamma(ell): return (1 + 2.1 / ell + 2.5e-4) / math.sqrt(ell)


def closed_form_G0(lbeta, ell, lL, nphi_factor=1.0):
    b = math.exp(lbeta - 2 * ell); u = 1.0 / (1.0 + math.exp(min(lbeta + 2 * lL, 700.0)))
    al = math.exp(-lbeta / 2) * (1 - b) / math.sqrt(2); la = (math.exp(lL) - math.exp(min(-2 * ell - lL, 700.0))) / math.sqrt(2)
    sx = (al ** 2 + la ** 2) / 2; ex = math.exp(-sx)
    Enp = -math.expm1(-sx) + al ** 2 * ex; Eop = -math.expm1(-sx) + la ** 2 * ex      # no cancellation (1 - e^{-s} by expm1)
    return 2 * u * (1 - Eop / 4) + nphi_factor * (1 - u) / 2 * Enp


def scan_L(g, lbeta, ell, r, nL=40, nphi_factor=1.0, closed=False):
    """min over L in [sigma/sqrt(r), 10] (log grid) of sigma (a + a'); returns (min, log L at min)."""
    lo = -ell - 0.5 * math.log(r); hi = math.log(10.0)
    best = (math.inf, None)
    for lL in np.linspace(lo, hi, nL):
        v = closed_form_G0(lbeta, ell, lL, nphi_factor) if closed else g.sigQ(lbeta, ell, lL, nphi_factor)
        if v < best[0]: best = (v, float(lL))
    return best


def log_margin(sq, ell):
    """log((a + a')/gamma) = log(sigma (a + a')) + ell - log gamma."""
    return math.log(sq) + ell - math.log(gamma(ell)) if sq > 0 else -math.inf
