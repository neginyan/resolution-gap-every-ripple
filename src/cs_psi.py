"""Stage CS: the brightness bound of a box, P_cell, from Lemma CM-1 and the corollary of Lemma CN-1 with (K, L) FIXED per box.  Python 3.11.

For fixed (K, L) with K > 1, L > 0, write s = sqrt(L K kappa), c = e^{1/(2L)}/(1 - 1/K), b' = b/s^2, E0 = P/(2 mu), E^ = min(E0/s, 1/16) and
    U(P) = c [ (1 + b'/2) s E^ ln(2 B0(E^, b')/E^) + c_CM b' s ],   B0(E, b) = (1 + sqrt(E) + (E/2)^{1/(2+b)})^2 .
The corollary of Lemma CN-1 says P/2 <= U(P) (it is cn_lemmas.rhs2 multiplied by E0); Lemma CM-1 is the case s = 1, c = 1.
  (S1) h(E) = ln(2 B0/E) decreases on (0, 1/16]; E h(E) increases there; B0 increases in E and in b.
  (S2) U(P)/P is nonincreasing in P, so {P : P/2 <= U(P)} = (0, P*] and P* is found by bisection.
  (S3) for fixed P, U decreases in mu;  (S4) U increases in b;  (S5) the corollary with delta^2 = K kappa_b tau holds for every kappa <= kappa_b.
Hence over a box [mu_a, mu_b] x [b_lo, b_hi] x [kappa_a, kappa_b]:  P <= P_cell = min(2 mu_b Qb^2, P*_CM1(mu_a, b_hi), min_{(K,L) in the list, L K kappa_b <= 1} P*_KL(mu_a, b_hi, kappa_b)).
The list of (K, L) only decides how sharp P_cell is, never whether it is valid (every admissible (K, L) gives a valid bound).
ROUNDING.  The bisection returns the upper end of a bracket of width 2^-60 in log P; P_cell is then multiplied by e^{1e-6}.  The relative error of U in double
precision is below 1e-14, and dlog P*/dlog U = 1/(1 - dlog U/dlog P) <= 1/(1 - 0.5) on the bracket (checked at every box: the slope is returned), so the
float error of log P* is below 1e-13, far inside 1e-6.
"""
import math
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
import numpy as np

QB = 0.25
WRONG = {'W1': False, 'W2': False, 'W3': False, 'W4': False}       # deliberately wrong versions of the search plan
KS = np.array([1.5, 2.0, 4.0, 8.0, 32.0, 256.0])
LS = np.array([0.1, 0.35, 1.0, 2.0, 8.0, 64.0])


def B0(E, b):
    return (1 + np.sqrt(E) + (E / 2) ** (1.0 / (2 + b))) ** 2


def U(P, mu, b, s, c):
    """the right side of P/2 <= U(P); arrays broadcast.  s = sqrt(L K kappa) (s = 1, c = 1 for CM-1)."""
    E0 = P / (2 * mu); Eh = np.minimum(E0 / s, 1.0 / 16); bp = b / s ** 2
    return c * ((1 + bp / 2) * s * Eh * np.log(2 * B0(Eh, bp) / Eh) + CM.C_CM * bp * s)


def Pstar(mu, b, s, c, iters=60):
    """largest P with P/2 <= U(P) (vectorised bisection in log P on [-1500, log(2 mu Qb^2) + 50]).  Returns (log P*, slope of log U at the end)."""
    mu, b, s, c = np.broadcast_arrays(np.asarray(mu, float), np.asarray(b, float), np.asarray(s, float), np.asarray(c, float))
    lo = np.full(mu.shape, -1500.0); hi = np.log(2 * mu * QB * QB) + 50
    ok_hi = np.exp(hi) / 2 <= U(np.exp(hi), mu, b, s, c)
    for _ in range(iters):
        m = 0.5 * (lo + hi)
        with np.errstate(all='ignore'):
            f = np.exp(m) / 2 <= U(np.exp(m), mu, b, s, c)
        lo = np.where(f, m, lo); hi = np.where(f, hi, m)
    with np.errstate(all='ignore'):
        sl = (np.log(U(np.exp(hi + 1e-3), mu, b, s, c)) - np.log(U(np.exp(hi), mu, b, s, c))) / 1e-3
    return np.where(ok_hi, hi, hi), sl


def lP_cell(lmu_a, lmu_b, lb_hi, lk_a, lk_b, Ks=KS, Ls=LS):
    """log of the brightness bound over the boxes (arrays).  kappa_b may be +inf (the tail [3, inf): CM-1 only).  Returns (log P_cell, max slope)."""
    lw = np.log(2 * np.exp(lmu_b) * QB * QB)
    small = lmu_b < math.log(3.5)                      # below mu = 3.5 the bound 2 mu_b Qb^2 is used alone (it is valid; the others are not needed there)
    if small.all(): return lw + 1e-6, np.zeros_like(lw)
    mu_a, mu_b = np.exp(lmu_a), np.exp(lmu_b); b = np.exp(lb_hi)
    if WRONG['W1']: mu_a = mu_b
    if WRONG['W2']: b = np.exp(lb_hi - 3.0)
    kb = np.exp(lk_a) if WRONG['W3'] else np.exp(lk_b)
    kchk = np.exp(lk_a) if WRONG['W4'] else kb
    lcm, sl = Pstar(mu_a, b, 1.0, 1.0)
    best = lcm; slmax = sl
    for K in Ks:
        for L in Ls:
            okKL = (L * K * kchk <= 1.0) & np.isfinite(kb)
            if not okKL.any(): continue
            s = np.sqrt(L * K * np.where(okKL, kb, 1e-300)); c = math.exp(1 / (2 * L)) / (1 - 1 / K)
            lp, sl2 = Pstar(mu_a, b, s, c)
            best = np.where(okKL, np.minimum(best, lp), best); slmax = np.where(okKL & (lp <= best), np.maximum(slmax, sl2), slmax)
    return np.where(small, lw, np.minimum(best, lw)) + 1e-6, slmax


def Psi2_point(mu, b, kap, K, L):
    """the corollary at one state for one (K, L) (for the checks)."""
    if L * K * kap > 1: return math.inf
    lp, _ = Pstar(np.array([mu]), np.array([b]), np.array([math.sqrt(L * K * kap)]), np.array([math.exp(1 / (2 * L)) / (1 - 1 / K)]))
    return float(lp[0])
