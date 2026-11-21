"""Stage DG 2.1: THE WHOLE-SUM FORM (a Taylor model of every line in log space, carried together through the table's reduction).  Python 3.11 grammar.

THE OBJECTS.  A box X of the table has the coordinates y = (log mu, log r, log beta, log kappa, ell) with centre c and half-widths h.  For the z-options
(Tz, Bz, Fz) and each end of G (0+ and G_cell), the table reduces Num - gamma sigma den to lines  c_l(y) sigma^{p_l - 1} f_t(a')  (type t in L, H, C, S,
M); terms_cell takes every c_l at the safe ends of the box, every net at its worst sigma end, and loses the cancellation between lines.  Here every
line is carried as a function of the state y itself.

THEOREM (DG-1) [proof].  For a finite box X (mu_a > 0, kappa finite at both ends, b_hi = beta_b sigma_hi^2 < BMAX on X) and an end G_e in {0+, G_cell(X)}
of the z-options, let psi_l(y) = c_l(y) phi_t(r) sigma^{p_A - 1} be the l-th line at the state y in the variable A (a' = 4 r A/sigma; DF-1), with c_l(y)
the table's coefficient at the zero-width box {y} with the G range (0, G_cell(X)] of X, and Psi_l = log |psi_l| (every line has a fixed sign s_l on X,
or is identically 0).  Let e, e_A in R^5 be any vectors (chosen per box; see choose_scaling) and d_t the degree of the type function in A
(L 1, C 0, S 1/2, M -1/2, H -1).  Put
    w_l = sum_j |dPsi_l/dy_j (c) + d_t e_A,j - e_j| h_j + (1/2) sum_jk M_l,jk h_j h_k + 1e-6,   M_l,jk >= sup_X |d^2 Psi_l/dy_j dy_k|,
    chat_l = s_l exp(Psi_l(c) - s_l w_l).
Then the table's reduction (collect, fmin, the options, the branches, the frac relaxations) with the coefficients chat_l, the factor of sigma 1 in every
net, the A-range [min_X 4 sigma^3 e^{-u}, max_X e^{-u}] and the H shift range [min_X, max_X] of sigma^2 e^{-u}/(4 r) (u = e_A . (y - c)) gives a value v_e;
if v_e(0+) > ACC and v_e(G_cell) > ACC for one option, Num - gamma sigma den >= 0 at every state of X and every G in (0, G_cell(X)].
  (1) The table is valid for every box, also for the zero-width box {y} with the G range (0, G_cell(X)] (it contains the state's G: G_cell(X) >=
      G_cell({y})).  So at the state y:  Num - gamma sigma den >= sigma sum_l c_l(y) sigma^{p_l - 1} f_t(a')  line by line (the table's viewpoint 2 at a
      point), and in the variable A (an identity per state, DF-1):  = sigma sum_l psi_l(y) g_t(A),  g_t(A) = A, 1, sqrt A, 1/sqrt A, 1/(A + sigma^2/(4r)).
  (2) Substitute A = e^{u} At (u = e_A . delta, delta = y - c; a bijection for each state) and multiply by e^{-e . delta} > 0: the sign of the sum is that
      of  sum_l psi_l(y) e^{(d_t e_A - e) . delta} gt_t(At),  with gt the same type functions of At (homogeneity of degree d_t; for H the shift becomes
      sigma^2 e^{-u}/(4r)).  At ranges over [4 sigma^3 e^{-u}, e^{-u}] for this state, inside the hull over X.
  (3) Taylor with the Lagrange remainder (Psi_l is C^2 on X: every operation is smooth there, the branch of every min/max fixed per box):
      Psi_l(y) + (d_t e_A - e).delta = Psi_l(c) + (grad Psi_l(c) + d_t e_A - e).delta + (1/2) delta^T Hess Psi_l(xi) delta, so it lies in
      [Psi_l(c) - w_l, Psi_l(c) + w_l] (|delta_j| <= h_j, |Hess_jk| <= M_jk; the 1e-6 covers rounding, see ROUNDING).  Hence the l-th scaled line is
      >= chat_l gt_t(At) for every state of X (s_l = +1: the smallest positive value; s_l = -1: the largest magnitude; gt_t >= 0).
  (4) So the scaled sum >= sum_l chat_l gt_t(At): the table's reduced form with constant coefficients.  The rest is the table's own argument (DF-1 (3)):
      the nets, the rounding, the worst H shift over the shift range (be >= 0: the largest shift; be < 0: the smallest), the minimisation over the hull of
      the At-range, the frac relaxations, the split point (any point; per state it is a point of A that does not depend on G).
  (5) The endpoint rule.  For each state y the point form psi(y; G) is affine in G on (0, G_cell(X)] (the table's viewpoint 1 at the point {y}), so its
      minimum over A is concave in G, and the branches coincide at G -> 0+ (the lines in which they differ are proportional to G: their chat at 0+ is
      exactly 0, and the shared lines have the same chat in both branches).  Steps (i)-(v) of the endpoint rule then hold per state with the scaled
      function; the positive factors e^{-e.delta} do not change any sign.  QED.
THE BOX-WIDE HESSIAN BOUND M_l [proof of the method].  Psi_l is built from the coordinates by the operations of the class LA below: sums and integer or
  half-integer multiples of logs (products, quotients, powers: exact, no curvature added), log y_5 (ell itself: Hessian -1/ell^2 e5 e5^T, monotone in
  ell, worst at ell_a), the sum of two positive quantities  log(e^a + e^b)  (gradient p ga + (1-p) gb, Hessian p Ha + (1-p) Hb + p(1-p)(ga-gb)(ga-gb)^T,
  p = 1/(1 + e^{b-a}) monotone in b - a, p(1-p) <= 1/4 and monotone on each side of 1/2) and the difference of two  log(e^a - e^b) = a + log(1 - e^{b-a})
  (phi(d) = log(1 - e^d), phi' = -1/(e^{-d} - 1), phi'' = -e^{-d}/(e^{-d} - 1)^2: all monotone in d < 0, worst at the largest d, the box's sup of b - a).
  Each rule bounds the value, the gradient and the Hessian of the result over the WHOLE box from those of its arguments over the whole box, with the
  scalar factors (p, p(1-p), phi', phi'') at their worst over the box's range of the argument (monotone, so at the ends of that range).  By induction
  every LA object carries intervals that contain the value, the gradient and the Hessian of its function at every point of X; M_l is the larger end
  of |Hess| of Psi_l.  The centre values Psi_l(c), grad Psi_l(c) are the same computation on the zero-width box {c}.
ROUNDING.  Every LA operation is a few float64 operations (relative error <= 2^-52 each); a line has fewer than 400; |Psi| <= 1.2e4, |grad| <= 1e3.
  The total error of Psi_l(c) + grad.delta is below 400 * 2.3e-16 * (1.2e4 + 1e3 * 8) < 2e-9, and the interval ends of M are moved outward by the
  factor 1 + 1e-9: the 1e-6 in w_l covers both with room (and is relative 1e-6 on a coefficient: far below every margin used).
WRONG VERSIONS (power checks): TM['wrong'] = 'centre_slope' (M := 0: the centre slope, no remainder), 'half' (w_l / 2), 'hess_centre' (M from the Hessian at
  the centre instead of the box), 'no_e' (the scaling vectors put to 0 -- NOT wrong, a valid weaker form, reported for the effect)."""
import math
import numpy as np
import cz_cells as X

LD = np.longdouble
TM = {'on': False, 'wrong': None, 'scale': True, 'tab': True}
NV = 5


# ---------------------------------------------------------------- interval helpers on (lo, hi) arrays
def iadd(a, b): return (a[0] + b[0], a[1] + b[1])
def isub(a, b): return (a[0] - b[1], a[1] - b[0])
def iscal(k, a):
    k = np.asarray(k, dtype=float)
    return (np.where(k >= 0, k * a[0], k * a[1]), np.where(k >= 0, k * a[1], k * a[0]))
def imul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    with np.errstate(invalid='ignore'):
        lo = np.minimum(np.minimum(p[0], p[1]), np.minimum(p[2], p[3])); hi = np.maximum(np.maximum(p[0], p[1]), np.maximum(p[2], p[3]))
    return (np.where(np.isnan(lo), 0.0, lo), np.where(np.isnan(hi), 0.0, hi))    # 0 * inf cannot occur in a finite box; guard only
def iouter(g, k=None):
    """the interval outer product g g^T (n, 5, 5), the diagonal as a square (>= 0)."""
    a = (g[0][:, :, None], g[1][:, :, None]); b = (g[0][:, None, :], g[1][:, None, :])
    lo, hi = imul(a, b)
    sq_lo = np.where((g[0] <= 0) & (g[1] >= 0), 0.0, np.minimum(g[0] ** 2, g[1] ** 2)); sq_hi = np.maximum(g[0] ** 2, g[1] ** 2)
    i = np.arange(NV); lo[:, i, i] = sq_lo; hi[:, i, i] = sq_hi
    return lo, hi
def bc(s, nd):
    """broadcast an (n,) interval to (n, 1) or (n, 1, 1)."""
    return (s[0].reshape(s[0].shape + (1,) * nd), s[1].reshape(s[1].shape + (1,) * nd))


class LA:
    """log of a POSITIVE quantity on a box: value, gradient, Hessian as intervals over the whole box (n boxes at once)."""
    __slots__ = ('v', 'g', 'H')

    def __init__(self, v, g, H): self.v, self.g, self.H = v, g, H

    @staticmethod
    def const(c, n):
        c = np.asarray(c, dtype=float) + np.zeros(n); lc = np.log(c)
        z1 = np.zeros((n, NV)); z2 = np.zeros((n, NV, NV))
        return LA((lc, lc.copy()), (z1, z1.copy()), (z2, z2.copy()))

    @staticmethod
    def expvar(j, k, ylo, yhi):
        """the quantity e^{k y_j}: log = k y_j (linear)."""
        n = len(ylo); g = np.zeros((n, NV)); g[:, j] = k; z2 = np.zeros((n, NV, NV))
        v = (k * ylo, k * yhi) if k >= 0 else (k * yhi, k * ylo)
        return LA(v, (g, g.copy()), (z2, z2.copy()))

    @staticmethod
    def logvar(j, ylo, yhi):
        """the quantity y_j itself (y_j > 0): log y_j, gradient 1/y_j e_j, Hessian -1/y_j^2 e_j e_j^T (monotone: ends of the range)."""
        n = len(ylo); glo = np.zeros((n, NV)); ghi = np.zeros((n, NV)); Hlo = np.zeros((n, NV, NV)); Hhi = np.zeros((n, NV, NV))
        glo[:, j] = 1 / yhi; ghi[:, j] = 1 / ylo; Hlo[:, j, j] = -1 / ylo ** 2; Hhi[:, j, j] = -1 / yhi ** 2
        return LA((np.log(ylo), np.log(yhi)), (glo, ghi), (Hlo, Hhi))

    def __mul__(a, b):
        if not isinstance(b, LA): b = LA.const(b, len(a.v[0]))
        return LA(iadd(a.v, b.v), iadd(a.g, b.g), iadd(a.H, b.H))
    __rmul__ = __mul__

    def __truediv__(a, b):
        if not isinstance(b, LA): b = LA.const(b, len(a.v[0]))
        return LA(isub(a.v, b.v), isub(a.g, b.g), isub(a.H, b.H))

    def __rtruediv__(a, b):
        return LA.const(b, len(a.v[0])) / a

    def __pow__(a, k):
        return LA(iscal(k, a.v), iscal(k, a.g), iscal(k, a.H))

    def __add__(a, b):
        """log(e^a + e^b) (sum of two positive quantities)."""
        if not isinstance(b, LA): b = LA.const(b, len(a.v[0]))
        d = isub(b.v, a.v)                                        # b - a over the box
        with np.errstate(over='ignore'):
            p_lo = 1 / (1 + np.exp(d[1])); p_hi = 1 / (1 + np.exp(d[0]))    # p = 1/(1 + e^{b-a}), decreasing in b - a (e^{+big} = inf gives p = 0 exactly)
        P = (p_lo, p_hi)
        q_ends = (p_lo * (1 - p_lo), p_hi * (1 - p_hi))
        q_lo = np.minimum(q_ends[0], q_ends[1]); q_hi = np.where((p_lo <= 0.5) & (p_hi >= 0.5), 0.25, np.maximum(q_ends[0], q_ends[1]))
        v = (np.logaddexp(a.v[0], b.v[0]), np.logaddexp(a.v[1], b.v[1]))
        dg = isub(a.g, b.g)
        g = iadd(b.g, imul(bc(P, 1), dg))
        Hm = iadd(b.H, imul(bc(P, 2), isub(a.H, b.H)))
        H = iadd(Hm, imul(bc((q_lo, q_hi), 2), iouter(dg)))
        return LA(v, g, H)
    __radd__ = __add__

    def __sub__(a, b):
        """log(e^a - e^b), a > b on the whole box (asserted by the caller through ok())."""
        if not isinstance(b, LA): b = LA.const(b, len(a.v[0]))
        D = LA(isub(b.v, a.v), isub(b.g, a.g), isub(b.H, a.H))                       # d = b - a < 0
        dlo, dhi = D.v
        with np.errstate(all='ignore'):
            phi = (np.log(-np.expm1(dhi)), np.log(-np.expm1(dlo)))                # decreasing in d
            f1 = lambda d: -1 / np.expm1(-d)                                       # phi' < 0, decreasing (more negative as d -> 0-)
            f2 = lambda d: -np.exp(-d) / np.expm1(-d) ** 2                         # phi'' < 0, decreasing
            F1 = (f1(dhi), f1(dlo)); F2 = (f2(dhi), f2(dlo))
        bad = ~(dhi < 0)
        g = imul(bc(F1, 1), D.g)
        H = iadd(imul(bc(F2, 2), iouter(D.g)), imul(bc(F1, 2), D.H))
        out = LA(iadd(a.v, phi), iadd(a.g, g), iadd(a.H, H))
        out.v = (np.where(bad, np.nan, out.v[0]), np.where(bad, np.nan, out.v[1]))
        return out

    def __rsub__(a, b):
        return LA.const(b, len(a.v[0])) - a

    def where(self, mask, other):
        m1 = mask; m2 = mask[:, None]; m3 = mask[:, None, None]
        return LA((np.where(m1, self.v[0], other.v[0]), np.where(m1, self.v[1], other.v[1])),
                  (np.where(m2, self.g[0], other.g[0]), np.where(m2, self.g[1], other.g[1])),
                  (np.where(m3, self.H[0], other.H[0]), np.where(m3, self.H[1], other.H[1])))

    def ok(self):
        return np.isfinite(self.v[0]) & np.isfinite(self.v[1])


# ---------------------------------------------------------------- the lines of the z-options at a state (point form)
def z_lines(y_lo, y_hi, lGref, end, gmu_branch=None):
    """the lines of the z-options in the record order of terms_cell (T list with grp s or z, then the option extras), as (type, power, sign, LA) at
    the state y over the box [y_lo, y_hi] (or a point: y_lo = y_hi), the G range (0, G_cell] with G_cell = e^{lGref} per box; end = 'c' (G = G_cell)
    or '0+' (G = 0: the lines proportional to G are exactly 0, sign 0).  Returns (T, extras): T a list of (t, p, s, LA, tag), extras a dict
    option -> list of collect calls, each a list of (t, p, s, LA, tag)."""
    n = len(y_lo); C = lambda c: LA.const(c, n)
    mu = LA.expvar(0, 1, y_lo[:, 0], y_hi[:, 0]); r = LA.expvar(1, 1, y_lo[:, 1], y_hi[:, 1]); B = LA.expvar(2, 1, y_lo[:, 2], y_hi[:, 2])
    kap = LA.expvar(3, 1, y_lo[:, 3], y_hi[:, 3]); ell = LA.logvar(4, y_lo[:, 4], y_hi[:, 4]); sig = LA.expvar(4, -1, y_lo[:, 4], y_hi[:, 4])
    QB = X.QB
    eta = ell ** -1; one = C(1.0)
    opeta = one + eta; ometa = one - eta; fl = opeta ** -1
    onepr = one + r; twopr = C(2.0) + r
    kE = (r / onepr) ** 0.5; gs = (r / twopr) ** 0.5
    two_l = C(2.0) * ell + 3.1
    U1 = C(QB) * two_l ** 0.5 + 1e-6; U2 = C(QB) * two_l + 1e-4
    X1 = U1 / (1 - QB); CZ = eta ** 2 / (C(math.e) * ometa ** 2)
    gam = C(1 + 2.5e-4) * ell ** -0.5
    b = B * sig ** 2; omb = one - b
    yh = (C(2.0) * B) ** -1; w0 = C(0.75) * B ** -1; opw0 = one + w0
    Kz2 = C(8.0) * ell + 100.0; Kz = Kz2 ** 0.5
    TKc = C(0.8 * math.exp(-50.0)) * (Kz + 1.0)
    ringf = one - Kz2 * opeta / (C(8.0) * B * ometa)
    Gref = LA((lGref.astype(float), lGref.astype(float).copy()), (np.zeros((n, NV)),) * 2, (np.zeros((n, NV, NV)),) * 2)
    cap = C(2 * QB ** 2 * math.exp(1e-6)) * gs
    gmu1 = Gref / mu
    gb = _centre_smaller(gmu1, cap) if gmu_branch is None else gmu_branch
    Gmu = gmu1.where(gb, cap)                                                   # min(G_cell/mu, cap) <= the branch smaller at the centre (an upper bound)
    sqP = (Gref / gs) ** 0.5
    G = Gref if end == 'c' else None                                            # end 0+: G = 0
    M4c = C(3.0) * (one + eta * kE * r ** 2 / onepr ** 2) + C(6.0) * eta * kE * r / onepr ** 2
    M4g = C(3.0) * Gmu / (C(2.0) * twopr ** 2 * ometa)
    X1CZ = X1 ** 2 + CZ
    T = []
    def add(t, p, s, q, tag): T.append((t, float(p), s, q, tag))
    add('L', 1, +1, C(0.5), 'P1')
    add('L', 1, +1 if end == 'c' else 0, (ringf * fl * G / (mu * twopr) / (C(4.0) * r)) if end == 'c' else None, 'P2z')
    add('C', 2, +1, C(3.0) * omb ** 2 / (C(8.0) * opw0), 'P3z')
    add('C', 3, -1, gam * B * (one + (eta + 0.184) * kE), 'd1')
    add('C', 1, -1 if end == 'c' else 0, (gam * G / (C(2.0) * ometa)) if end == 'c' else None, 'd2')
    add('L', 2, -1, gam * (one + C(2.0) * eta * kE) / 4.0, 'd3')
    add('L', 2, -1, gam * Gmu / (C(2.0) * twopr * ometa) / (C(4.0) * r), 'd4')
    add('L', 1, -1, eta * kE * twopr / (C(2.0) * onepr), 'N1')
    add('L', 1, -1, (one + eta * kE * r / onepr + C(2.0) * eta * kE / onepr) / (C(16.0) * B), 'N2')
    add('C', 2, -1, (M4c + M4g) / 2.0, 'N3')
    n4J = (eta * kE * r / onepr) if X.FIX.get('N4J', True) else (0.0 * eta)                                   # DL: corrected N4 (cz_cells.FIX['N4J'])
    add('L', 3, -1, C(1.5 / 4) * (X1CZ * (one + n4J + C(2.0) * eta * kE / onepr) + r * M4c), 'N4')
    add('L', 3, -1, C(1.5) * (X1CZ * Gmu / (C(2.0) * twopr * ometa) + r ** 2 * M4g) / (C(4.0) * r), 'N4G')
    add('L', 5, -1, eta ** 2 * gs * TKc / (C(4.0) * B * twopr * ometa) / (C(4.0) * r), 'ring2')
    add('C', 2, -1, C(0.25 * QB * X.M4Z) * kE, 'M0Xi')
    add('C', 3, -1, (C(15.0 / 2) * B) ** 0.5 * kE * sqP / 4.0, 'A1v')
    add('S', 3.5, -1, B * opeta / C(4 * math.sqrt(math.pi)), 'A1w')
    add('C', 4, -1 if end == 'c' else 0, (B * kap * G / (C(8.0) * ometa)) if end == 'c' else None, 'A2k')
    add('L', 5, -1, B * (one + eta * kE * r / onepr) / 8.0, 'A2a')
    add('L', 5, -1, B * eta ** 2 * gs / (twopr * ometa) / (C(8.0) * r), 'A2b')
    cL = C(X.C2Z) + yh
    add('S', 3.5, -1, B * cL * (r / onepr) / C(2 * math.sqrt(math.pi)), 'B1w1')
    add('S', 3.5, -1, B * eta ** 2 * (one + yh / 2.0) / (C(2 * math.sqrt(math.pi)) * twopr * ometa), 'B1w2')
    add('C', 3, -1 if end == 'c' else 0, (B ** 0.5 * U1 * kap ** 0.5 * G / (C(4.0) * ometa ** 2)) if end == 'c' else None, 'B2a')
    add('L', 4, -1, (C(2.0) * B) ** 0.5 * sqP / 8.0 * (kE * r / onepr + eta ** 2 / ((r * twopr) ** 0.5 * twopr * ometa ** 2)), 'B2b')
    add('C', 4, -1, U1 ** 2 * gs * (Kz + 5.0) * C(0.4 * math.exp(-50.0)) / ometa, 'pair')
    # ---- option extras
    Hz = [('H', 3, +1, (B / 2.0) / opw0 ** 2, 'P4z'), ('H', 3, -1, B * kE * (eta + 0.184), 'hneg1')]
    on = end == 'c'
    z = lambda s: s if on else 0
    fF = (G / (C(4.0) * ometa)) if on else None
    z2 = Kz2 * yh
    hFz = (fl * G / 4.0 * (r / twopr) * (one - z2 / 2.0)) if on else None
    brk = one - (C(4.0) * b / omb + z2 / 12.0)                                  # > 0 on the box: Tz allowed, Bz's loss is 0
    negbrk = (C(4.0) * b / omb + z2 / 12.0) - one                               # > 0 on the box: Tz excluded, Bz carries the loss
    cKz = (fl * G / 4.0 * omb ** 2 * kap / (C(4.0) * B) * brk) if on else None
    lossK = (kap * G / (C(16.0) * B * ometa) * negbrk) if on else None
    s2 = C(math.sqrt(2.0)); spi = C(math.sqrt(math.pi))
    B2c = (fF * X1 / s2) if on else None
    B2s = (fF * ((CZ / 2.0) ** 0.5 + r / (spi * twopr ** 0.5)) / (C(4.0) * r) ** 0.5) if on else None
    B1m = (fF * X1 / (s2 * spi * twopr ** 0.5) * (C(4.0) * r) ** 0.5) if on else None
    B1c = (fF * ((CZ / (C(2 * math.pi) * twopr)) ** 0.5 + r / (C(2.0) * twopr) + X1CZ)) if on else None
    B1l = (fF * r / (C(8.0) * twopr)) if on else None
    fFs = (fF * (kap / (C(2.0) * B)) ** 0.5) if on else None
    uB2c = (fFs * X1 / s2) if on else None
    uB2s = (fFs * ((CZ / 2.0) ** 0.5 + r / (spi * twopr ** 0.5)) / (C(4.0) * r) ** 0.5) if on else None
    FzK = (kap * G / (C(4.0) * ometa)) if on else None
    HzF = Hz + [('H', 1, z(+1), hFz, 'hFz')]
    ext = {'Fz': [Hz + [('C', 2, z(-1), FzK, 'FzK')]],
           'Tz': [HzF + [('C', 0, z(+1), cKz, 'cKz'), ('C', 1, z(-1), B2c, 'B2c'), ('S', 1.5, z(-1), B2s, 'B2s')],
                  HzF + [('C', 0, z(+1), cKz, 'cKz'), ('M', 1.5, z(-1), B1m, 'B1m'), ('C', 2, z(-1), B1c, 'B1c'), ('L', 3, z(-1), B1l, 'B1l'),
                         ('C', 1, z(-1), uB2c, 'uB2c'), ('S', 1.5, z(-1), uB2s, 'uB2s')]],
           'Bz': [HzF + [('C', 0, z(-1), lossK, 'lossK'), ('C', 1, z(-1), B2c, 'B2c'), ('S', 1.5, z(-1), B2s, 'B2s')],
                  HzF + [('C', 0, z(-1), lossK, 'lossK'), ('M', 1.5, z(-1), B1m, 'B1m'), ('C', 2, z(-1), B1c, 'B1c'), ('L', 3, z(-1), B1l, 'B1l'),
                         ('C', 1, z(-1), uB2c, 'uB2c'), ('S', 1.5, z(-1), uB2s, 'uB2s')]]}
    aux = {'brk': brk, 'negbrk': negbrk, 'omb': omb, 'ringf': ringf, 'ometa': ometa, 'onemz2': one - z2 / 2.0, 'r': r, 'sig': sig, 'gmu_branch': gb}
    return T, ext, aux


def _centre_smaller(a, b):
    """the branch of min(a, b) smaller at the centre of the box (the upper bound used for the whole box)."""
    return 0.5 * (a.v[0] + a.v[1]) <= 0.5 * (b.v[0] + b.v[1])


# ---------------------------------------------------------------- the box form
TYPEINFO = {'L': (1.0, -1.0, 1.0), 'H': (-1.0, 1.0, -1.0), 'S': (0.5, -0.5, 0.5), 'M': (-0.5, 0.5, -0.5), 'C': (0.0, 0.0, 0.0)}
#            type: (k: the factor (4r)^k of the variable A, the shift of the power p, the degree d of the type function in A)


def eligible(Xb, lGc):
    """the boxes the whole-sum form is for: finite (mu_a > 0, kappa finite at both ends, ell finite), b_hi = beta_b sigma_hi^2 < BMAX (no kink of the
    sigma end), G_cell > 0.  (Every other box keeps the table.)"""
    Xb = np.asarray(Xb, dtype=float)
    fin = np.all(np.isfinite(Xb), axis=1)
    ls_hi = np.minimum(-Xb[:, 8], 0.5 * (math.log(X.BMAX) - Xb[:, 4]))
    nokink = Xb[:, 5] - 2 * Xb[:, 8] < math.log(X.BMAX) - 1e-9          # beta_b e^{-2 ell_a} < BMAX: then sigma_hi = e^{-ell_a} on the box and b < BMAX at every state
    return fin & nokink & np.isfinite(lGc) & (ls_hi == -Xb[:, 8])


def _psi(T, ext):
    """every distinct line once: tag -> (t, p, s, LA); and the collect lists per option as lists of tags."""
    lines = {}; calls = {}
    for t, p, s, q, tag in T: lines[tag] = (t, p, s, q)
    for opt, cl in ext.items():
        calls[opt] = []
        for c in cl:
            for t, p, s, q, tag in c: lines[tag] = (t, p, s, q)
            calls[opt].append([tag for *_, tag in T] + [tag for *_, tag in c])
    return lines, calls


def _grid_min_weights(Psi_c, info, tags, lsig_c, lr_c, n):
    """heuristic weights for the choice of the scaling (no proof needed: any e, e_A is allowed): |psi_l(c)| g_t(A*) at the minimiser A* of the centre's
    sum over a grid of log A in [log 4 sigma^3, 0]."""
    lA = np.linspace(0, 1, 49)[None, :] * (np.log(4.0) + 3 * lsig_c)[:, None]               # (n, 49): 0 ... log 4 sigma^3
    sh = 2 * lsig_c - np.log(4.0) - lr_c
    F = np.zeros((n, lA.shape[1])); terms = []
    for tag in tags:
        t, s, lv = info[tag]
        if s == 0 or lv is None: terms.append(None); continue
        d = TYPEINFO[t][2]
        lg = -np.logaddexp(lA, sh[:, None]) if t == 'H' else d * lA
        x = lv[:, None] + lg; x = np.where(np.isfinite(x), x, -np.inf)          # a line not defined on a box (cKz / lossK of the other bracket sign): weight 0
        terms.append((s, x))
    big = np.max([np.max(x[1], axis=1) for x in terms if x is not None], axis=0)
    for x in terms:
        if x is None: continue
        F += x[0] * np.exp(x[1] - big[:, None])
    i = np.argmin(F, axis=1)
    return {tag: (None if x is None else x[1][np.arange(n), i] - big) for tag, x in zip(tags, terms)}


def choose_scaling(G, lw, D):
    """per box and coordinate j: (e_j, a_j) minimising sum_l w_l (G_lj + d_l a_j - e_j)^2 (weighted least squares; any choice is valid)."""
    W = sum(lw); Wd = sum(w * d for w, d in zip(lw, D)); Wdd = sum(w * d * d for w, d in zip(lw, D))
    SG = sum(w[:, None] * g for w, g in zip(lw, G)); SdG = sum((w * d)[:, None] * g for w, g, d in zip(lw, G, D))
    den = (Wdd - Wd ** 2 / W)
    a = np.where(den[:, None] > 1e-12 * W[:, None], (SG * (Wd / W)[:, None] - SdG) / np.where(den > 1e-12 * W, den, 1)[:, None], 0.0)
    e = (SG + a * Wd[:, None]) / W[:, None]
    return e, a


def choose_scaling_l1(G, lw, D, K=10, coords=(0, 1, 2, 3, 4)):
    """per box and coordinate j: (e_j, a_j) minimising sum_l w_l |G_lj + d_l a_j - e_j| (the first-order part of sum_l w_l w_l; weighted L1).
    The optimum of a two-parameter L1 fit is exact on two lines (or on one line with a_j = 0): the candidates are those, among the K heaviest lines."""
    cs = list(coords)
    Gm = np.stack(G, axis=1)[:, :, cs]; Wm = np.stack(lw, axis=1); Dm = np.asarray(D, dtype=float)       # (n, L, c), (n, L), (L,): only the coordinates used
    n, L, _ = Gm.shape; K = min(K, L)
    top = np.argsort(-Wm, axis=1)[:, :K]                                                      # (n, K)
    Gt = np.take_along_axis(Gm, top[:, :, None], axis=1); Dt = Dm[top]                        # (n, K, 5), (n, K)
    nc = len(cs)
    cands_e = [Gt[:, i, :] for i in range(K)]; cands_a = [np.zeros((n, nc)) for _ in range(K)]
    for i in range(K):
        for k in range(i + 1, K):
            dd = Dt[:, i] - Dt[:, k]; okp = np.abs(dd) > 1e-12
            a = np.where(okp[:, None], (Gt[:, k, :] - Gt[:, i, :]) / np.where(okp, dd, 1)[:, None], 0.0)
            cands_a.append(a); cands_e.append(Gt[:, i, :] + Dt[:, i][:, None] * a)
    E = np.stack(cands_e, axis=1); A = np.stack(cands_a, axis=1)                              # (n, P, 5)
    obj = np.einsum('nl,nplj->npj', Wm, np.abs(Gm[:, None, :, :] + Dm[None, None, :, None] * A[:, :, None, :] - E[:, :, None, :]))
    best = np.argmin(obj, axis=1)                                                             # (n, 5)
    e_ = np.take_along_axis(E, best[:, None, :], axis=1)[:, 0, :]; a_ = np.take_along_axis(A, best[:, None, :], axis=1)[:, 0, :]
    e = np.zeros((n, NV)); a = np.zeros((n, NV)); e[:, cs] = e_; a[:, cs] = a_
    return e, a


def tm_values(Xb, lGc, wrong=None, scale=True, coords=(0, 1, 2, 3, 4), fit='l1'):
    """the per-option values of the whole-sum form (keys k+'0+', k+'c' for the z-options, as values()), -inf where not eligible."""
    Xb = np.asarray(Xb, dtype=float); n = len(Xb)
    out = {k + e: np.full(n, -np.inf) for k in X.OPTS_Z for e in ('0+', 'c')}
    el = eligible(Xb, lGc)
    if not el.any(): return out, el
    idx = np.where(el)[0]; Y = Xb[idx]; lg = lGc[idx]; m = len(idx)
    ylo, yhi = Y[:, 0::2].copy(), Y[:, 1::2].copy(); yc = 0.5 * (ylo + yhi); h = 0.5 * (yhi - ylo)
    ok = np.ones(m, dtype=bool)
    res = {}
    for end in ('c', '0+'):
        Tb, eb, auxb = z_lines(ylo, yhi, lg, end)                 # over the box (for the Hessian bound and the checks of the branches)
        Tc, ec, auxc = z_lines(yc, yc, lg, end, gmu_branch=auxb['gmu_branch'])   # at the centre (the same branch of every min)
        for nm in ('omb', 'ringf', 'ometa', 'onemz2'):
            ok &= auxb[nm].ok()                                   # every difference positive on the whole box
        res[end] = (_psi(Tb, eb), _psi(Tc, ec))
    pos = auxb['brk'].ok(); neg = auxb['negbrk'].ok()           # the sign of the chirp bracket on the WHOLE box (else: only Fz)
    BRK = {'pos': pos, 'neg': neg}
    lsig_c = -yc[:, 4]; lr_c = yc[:, 1]
    # ---- the lines: Psi(c), grad Psi(c), M (box)
    info = {}
    for end in ('c', '0+'):
        (lb, calls), (lc, _) = res[end]
        for tag, (t, p, s, qb) in lb.items():
            if s == 0 or qb is None: info[(end, tag)] = (t, p, 0, None, None, None); continue
            qc = lc[tag][3]; k, dp, d = TYPEINFO[t]; pA = p + dp
            v = 0.5 * (qc.v[0] + qc.v[1]) + k * (math.log(4.0) + yc[:, 1]) - (pA - 1) * yc[:, 4]
            g = 0.5 * (qc.g[0] + qc.g[1]); g = g.copy(); g[:, 1] += k; g[:, 4] -= (pA - 1)
            Hsrc = qc.H if wrong == 'hess_centre' else qb.H
            M = np.maximum(np.abs(Hsrc[0]), np.abs(Hsrc[1])) * (1 + 1e-9)
            lok = qb.ok() & qc.ok() & np.all(np.isfinite(M), axis=(1, 2))
            if tag == 'cKz': lok |= ~pos                          # used only where brk > 0 on the box (Tz)
            elif tag == 'lossK': lok |= ~neg                      # used only where brk < 0 on the box (Bz)
            ok &= lok
            info[(end, tag)] = (t, pA, s, v, g, M)
    # ---- the scaling (from the centre, end c, the lines of Bz's branch B2)
    if scale and len(coords):
        tags = res['c'][0][1]['Bz'][0]
        winfo = {tag: (info[('c', tag)][0], info[('c', tag)][2], info[('c', tag)][3]) for tag in tags}
        lw = _grid_min_weights(winfo, winfo, tags, lsig_c, lr_c, m)
        use = [tag for tag in tags if lw[tag] is not None]
        mx = np.max([lw[t] for t in use], axis=0)
        W = [np.where(np.isfinite(lw[t]), np.exp(lw[t] - mx), 0.0) for t in use]
        Gs = [np.where(np.isfinite(info[('c', t)][4]), info[('c', t)][4], 0.0) for t in use]; Ds = [TYPEINFO[info[('c', t)][0]][2] for t in use]
        e, a = choose_scaling_l1(Gs, W, Ds, coords=coords) if fit == 'l1' else choose_scaling(Gs, W, Ds)
        e = np.where(np.isfinite(e), e, 0.0); a = np.where(np.isfinite(a), a, 0.0)
        msk = np.zeros(NV, dtype=bool); msk[list(coords)] = True; e = np.where(msk, e, 0.0); a = np.where(msk, a, 0.0)
    else:
        e = np.zeros((m, NV)); a = np.zeros((m, NV))
    # ---- the coefficients chat_l
    chat = {}
    for key, (t, pA, s, v, g, M) in info.items():
        if s == 0: chat[key] = (t, pA, np.zeros(m, dtype=LD)); continue
        d = TYPEINFO[t][2]
        lin = np.sum(np.abs(g + d * a - e) * h, axis=1)
        quad = 0.0 if wrong == 'centre_slope' else 0.5 * np.einsum('nij,ni,nj->n', M, h, h)
        w = lin + quad + 1e-6
        if wrong == 'half': w = 0.5 * w
        cv = s * np.exp(np.asarray(v - s * w, dtype=LD))
        if key[1] == 'cKz': cv = np.where(pos, cv, LD(0))       # Tz is excluded where brk is not > 0 on the box
        if key[1] == 'lossK': cv = np.where(neg, cv, LD(0))     # brk > 0 on the box: the loss is exactly 0
        chat[key] = (t, pA, np.where(np.isfinite(cv), cv, LD(0)))
    # ---- the ranges of At and of the shift over the box
    e4 = np.zeros(NV); e4[4] = 1.0; e1 = np.zeros(NV); e1[1] = 1.0
    lA_lo = math.log(4.0) - 3 * yc[:, 4] - np.sum(np.abs(-3 * e4 - a) * h, axis=1)
    lA_hi = np.sum(np.abs(a) * h, axis=1)
    lsh_c = -2 * yc[:, 4] - math.log(4.0) - yc[:, 1]; lsh_w = np.sum(np.abs(-2 * e4 - e1 - a) * h, axis=1)
    rng_ = (np.exp(np.asarray(lA_lo, dtype=LD)), np.exp(np.asarray(lA_hi, dtype=LD)))
    shf = (np.exp(np.asarray(lsh_c - lsh_w, dtype=LD)), np.exp(np.asarray(lsh_c + lsh_w, dtype=LD)))
    # ---- the replay
    saved = X.OPTS
    try:
        X.OPTS = X.OPTS_Z
        for opt in X.OPTS_Z:
            for end in ('0+', 'c'):
                calls = res[end][0][1][opt]
                store = [[chat[(end, tag)] for tag in cl] for cl in calls]
                if TMDIAG.get('keep'): TMDIAG.setdefault('stores', []).append((store, rng_, shf))
                X.COHREC.update(mode='tm', store=store, i=0, tm_range=rng_, tm_shift=shf)
                try:
                    with np.errstate(all='ignore'):
                        vv = X.terms_cell(Y, 0.0, True, lGc=(lg if end == 'c' else np.full(m, -np.inf)), opts=(opt,), lGref=lg)
                    assert X.COHREC['i'] == len(store), 'DG: not every collect replayed'
                finally:
                    X.COHREC.update(mode=None, store=[], i=0)
                valid = ok & (pos if opt == 'Tz' else (pos | neg) if opt == 'Bz' else True)
                vv = np.where(np.isnan(vv) | ~valid, -np.inf, vv)
                out[opt + end][idx] = vv
    finally:
        X.OPTS = saved
    TMDIAG['last'] = {'e': e, 'a': a, 'ok': ok, 'pos': pos, 'neg': neg}
    return out, el


TMDIAG = {'last': None, 'keep': False}


def tm_margin(Xb, lGc=None, wrong=None, scale=True, coords=(0, 1, 2, 3, 4), fit='l1'):
    """the margin of the whole-sum form (per-option endpoint rule over the z-options); -inf where not eligible."""
    Xb = np.asarray(Xb, dtype=float)
    if lGc is None: lGc, _ = X.box_P(Xb)
    v, el = tm_values(Xb, lGc, wrong=wrong, scale=scale, coords=coords, fit=fit)
    saved = X.OPTS
    try:
        X.OPTS = X.OPTS_Z; m = X.margin_from(v)
    finally:
        X.OPTS = saved
    return np.where(el, m, -np.inf)
