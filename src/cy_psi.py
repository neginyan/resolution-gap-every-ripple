"""Stage CY 2.1: cs_psi.py with the bound TIGHTENED BELOW mu = 3.5 (everything else is cs_psi.py line for line).  Python 3.11.
CHANGE.  cs_psi.lP_cell used 2 mu_b Qb^2 alone when mu_b < 3.5.  Here every box with mu_a >= 1e-3 uses min(2 mu_b Qb^2, P*_CM1(mu_a, b_hi), P*_KL(...)) as
above 3.5; boxes with mu_a < 1e-3 (in the table only mu_a = 0, the bottom box (0, 1e-3] of the mu grid, never split) keep 2 mu_b Qb^2 (there E0 = P/(2 mu_a) is infinite and CM-1 gives nothing).
WHY IT IS VALID BELOW 3.5 [proof].  (1) Lemma CM-1 (cm_local_bound): "for every window of the class and every focus (t0, tau = x/b, b <= 1)" -- no
condition on mu; the corollary of Lemma CN-1 (cn_lemmas): conditions delta^2 > kappa tau and tau' > 0 only.  (2) Of the facts S1-S5 below only S3 involves
mu: U depends on mu through E0 = P/(2 mu) only, and E h(E) increases in E (S1), so U is nonincreasing in mu for every mu > 0; S1, S2, S4, S5 do not
involve mu.  (3) The rounding argument (CV sec. 2, cv_pstar_check): the first midpoint m0 = (-1500 + log(2 mu Qb^2) + 50)/2 lies in [-729.5, -725.4] for
mu in [1e-3, 3.5] (> -745: P > 0); there U >= c (1 + b'/2) P ln(2 B0/Eh)/(2 mu) with ln(2 B0/Eh) >= ln(4 mu s) - m0 >= 725.4 - 20.4 > 700 (mu >= 1e-3;
s = sqrt(L K kappa_b) >= sqrt(0.1 * 1.5 * 1e-12) = 3.8e-7 since kappa_b >= 1e-12 for every kappa box, c >= 1), so U/P >= 700/(2 * 3.5) > 1/2: the test is TRUE at m0 (mathematically, and in float, where Eh may underflow below 1e-308 and U overflow to inf -- also true), lo >= m0 afterwards, P = 0 is never visited; the rest of
the CV argument (the amplification 1/(1 - slope) <= 2 ln(2 B0/E) < 4000) does not involve mu.  Checked in 60 digits in cy_checks.G4.

--- docstring of cs_psi.py ---
Stage CS: the brightness bound of a box, P_cell, from Lemma CM-1 and the corollary of Lemma CN-1 with (K, L) FIXED per box.  Python 3.11.

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
import math, os
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


ENV = {'on': False, 'deep': os.environ.get('CZ_ENV', '1') != '0', 't': (-8.0, -4.0, -2.0, 0.0, 2.0, 4.0, 8.0)}
# ENV['on']: the envelope on every row (float path; off: the bound of CY-DD); ENV['deep'] (DE, default on; CZ_ENV=0 turns it off): the envelope on the
# long-double rows only (kappa_b < 1e-12: the boxes the kappa split makes), so no box of the table before DE changes
GUARD = {'on': True, 'lk_min': -700.0}   # DD: never reached by the table (its kappa_b >= 1e-12); it only matters for a kappa split below e^-745     # DD: the monotone envelope in kappa (off: the bound of CY-DC)


JEN = {'on': os.environ.get('CZ_JEN', '0') == '1', 'lams': tuple(2.0 ** (0.5 * j) for j in range(-4, 45)), 'wrong': None}
# DH (Lemma DH-1, the two-focus lemma in its Jensen form; proof in dh_ceiling.py): for every tau' <= tau, E1 <= sqrt(tau'/tau) e^{kappa (tau/tau' - 1)/2} E1^(tau').
# With tau' = lam kappa_b tau (lam kappa_b <= 1) and kappa <= kappa_b the factor is <= sqrt(lam kappa_b) e^{1/(2 lam)}: the corollary's form with
# s = sqrt(lam kappa_b), c = e^{1/(2 lam)} (no Chebyshev factor 1/(1 - 1/K)).  Default OFF (CZ_JEN=1 turns it on): the records of DA-DG do not change.
# 'wrong' (power checks only): 'c1' (c = 1), 'above' (lam kappa_b > 1 allowed: tau' > tau, where E0^(tau') <= sqrt(tau/tau') E0 fails).
LDP = {'on': os.environ.get('CZ_LDP', '1') != '0', 'lk_min': -11000.0}   # CZ_LDP=0: the table of DD (the float path everywhere)     # DE: rows with kappa_b < 1e-12 (only the kappa split makes them) go through the long-double path below


def U_ld(P, mu, b, s, c):
    """U in long double (the same formula)"""
    E0 = P / (2 * mu); Eh = np.minimum(E0 / s, np.longdouble(1) / 16); bp = b / s ** 2
    B = (1 + np.sqrt(Eh) + (Eh / 2) ** (np.longdouble(1) / (2 + bp))) ** 2
    return c * ((1 + bp / 2) * s * Eh * np.log(2 * B / Eh) + np.longdouble(CM.C_CM) * bp * s)


def Pstar_ld(mu, b, s, c, iters=80):
    """Pstar in long double on [-11000, log(2 mu Qb^2) + 50] (P = e^-11000 is a normal long double).  As P -> 0, U/P -> inf (the term c_CM b' s
    is a positive constant and ln(2 B0/E^) -> inf), so the test is TRUE at the lower end; (S2) makes the set an interval; 80 halvings of a bracket of
    width < 11100 leave < 1e-20."""
    LD_ = np.longdouble
    mu, b, s, c = (np.asarray(v, dtype=LD_) for v in np.broadcast_arrays(np.asarray(mu, dtype=LD_), np.asarray(b, dtype=LD_), np.asarray(s, dtype=LD_), np.asarray(c, dtype=LD_)))
    lo = np.full(mu.shape, LD_(-11000)); hi = np.log(2 * mu * LD_(QB) * LD_(QB)) + 50
    with np.errstate(all='ignore'):
        for _ in range(iters):
            m = (lo + hi) / 2
            f = np.exp(m) / 2 <= U_ld(np.exp(m), mu, b, s, c)
            lo = np.where(f, m, lo); hi = np.where(f, hi, m)
        sl = (np.log(U_ld(np.exp(hi + LD_(1e-3)), mu, b, s, c)) - np.log(U_ld(np.exp(hi), mu, b, s, c))) / LD_(1e-3)
    return hi, sl


def lP_cell_ld(lmu_a, lmu_b, lb_hi, lk_a, lk_b, Ks=KS, Ls=LS):
    """lP_cell in long double, for any kappa_b down to e^-11000 (no underflow of kappa_b, b, s); the same bound (CM-1, the corollary for every
    admissible (K, L), the envelope ENV when on).  Returns float arrays (log P_cell + 1e-6, slope)."""
    LD_ = np.longdouble
    lmu_a, lmu_b, lb_hi, lk_b = (np.asarray(v, dtype=LD_) for v in (lmu_a, lmu_b, lb_hi, lk_b))
    lk_b = np.maximum(lk_b, LD_(LDP['lk_min']))
    lw = np.log(2 * np.exp(lmu_b) * LD_(QB) * LD_(QB))
    small = ~(np.exp(lmu_a) >= LD_(1e-3))
    mu_a = np.where(small, LD_(1), np.exp(lmu_a)); b = np.exp(lb_hi); kb = np.exp(lk_b)
    lcm, sl = Pstar_ld(mu_a, b, LD_(1), LD_(1))
    best = lcm; slmax = sl
    kbs = [kb] + ([np.maximum(kb, b * np.exp(LD_(t))) for t in ENV['t']] if (ENV['on'] or ENV['deep']) else [])
    for kb_ in kbs:
        for K in Ks:
            for L in Ls:
                okKL = (LD_(L) * LD_(K) * kb_ <= 1)
                if not okKL.any(): continue
                s = np.sqrt(LD_(L) * LD_(K) * np.where(okKL, kb_, LD_(1))); c = LD_(math.exp(1 / (2 * L)) / (1 - 1 / K))
                lp, sl2 = Pstar_ld(mu_a, b, s, c)
                best = np.where(okKL, np.minimum(best, lp), best); slmax = np.where(okKL & (lp <= best), np.maximum(slmax, sl2), slmax)
    if JEN['on']:
        for kb_ in kbs:
            for lam in JEN['lams'] + ((1e-2, 1e-3, 1e-4) if JEN['wrong'] == 'c1' else ()):
                okJ = (LD_(lam) * kb_ <= 1) | (JEN['wrong'] == 'above')
                if not okJ.any(): continue
                s = np.sqrt(LD_(lam) * np.where(okJ, kb_, LD_(1))); c = LD_(1.0 if JEN['wrong'] == 'c1' else math.exp(1 / (2 * lam)))
                lp, sl2 = Pstar_ld(mu_a, b, s, c)
                best = np.where(okJ, np.minimum(best, lp), best); slmax = np.where(okJ & (lp <= best), np.maximum(slmax, sl2), slmax)
    out = np.where(small, lw, np.minimum(best, lw)) + LD_(1e-6)
    return out.astype(float), slmax.astype(float)


def lP_cell(lmu_a, lmu_b, lb_hi, lk_a, lk_b, Ks=KS, Ls=LS):
    lk_b_ = np.asarray(lk_b, dtype=float)
    deep = np.isfinite(lk_b_) & (lk_b_ < math.log(1e-12) - 1e-9)
    if LDP['on'] and deep.any():                     # DE: the long-double path for the rows the kappa split makes (kappa_b below the old floor 1e-12)
        A = [np.broadcast_to(np.asarray(v, dtype=float), lk_b_.shape) for v in (lmu_a, lmu_b, lb_hi, lk_a, lk_b_)]
        lp = np.empty(lk_b_.shape); sl = np.empty(lk_b_.shape)
        if (~deep).any():
            lp0, sl0 = _lP_cell_f([a[~deep] for a in A][0], A[1][~deep], A[2][~deep], A[3][~deep], A[4][~deep], Ks, Ls); lp[~deep] = lp0; sl[~deep] = sl0
        lp1, sl1 = lP_cell_ld(A[0][deep], A[1][deep], A[2][deep], A[3][deep], A[4][deep], Ks, Ls); lp[deep] = lp1; sl[deep] = sl1
        return lp, sl
    return _lP_cell_f(lmu_a, lmu_b, lb_hi, lk_a, lk_b, Ks, Ls)


def _lP_cell_f(lmu_a, lmu_b, lb_hi, lk_a, lk_b, Ks=KS, Ls=LS):
    """log of the brightness bound over the boxes (arrays).  kappa_b may be +inf (the tail [3, inf): CM-1 only).  Returns (log P_cell, max slope)."""
    lw = np.log(2 * np.exp(lmu_b) * QB * QB)
    small = ~(np.exp(lmu_a) >= 1e-3)                   # CY: only mu_a < 1e-3 (in the table: mu_a = 0) keeps 2 mu_b Qb^2 alone (cs_psi: mu_b < 3.5)
    if small.all(): return lw + 1e-6, np.zeros_like(lw)
    mu_a, mu_b = np.where(small, 1.0, np.exp(lmu_a)), np.exp(lmu_b); b = np.exp(lb_hi)
    if WRONG['W1']: mu_a = mu_b
    if WRONG['W2']: b = np.exp(lb_hi - 3.0)
    if GUARD['on']: lk_b = np.maximum(lk_b, GUARD['lk_min'])     # DD (hole found): kappa_b < e^-745 underflowed to 0 -> s = 0 -> log P = -1500 (a false bound).
                                                                  # The corollary may be used with any kappa' >= kappa_b, so kappa_b is raised to e^-700.
    kb = np.exp(lk_a) if WRONG['W3'] else np.exp(lk_b)
    kchk = np.exp(lk_a) if WRONG['W4'] else kb
    lcm, sl = Pstar(mu_a, b, 1.0, 1.0)
    best = lcm; slmax = sl
    kbs = [kb]
    if ENV['on']:
        # DD: the corollary holds with any upper bound kappa' >= kappa of the state (the table already uses kappa_b for every kappa <= kappa_b),
        # so also kappa' = max(kappa_b, b e^t): the bound's term c_CM b' s = c_CM b/s grows as kappa -> 0 (b' = b/s^2), its minimum is near s^2 ~ b
        kbs += [np.maximum(kb, b * math.exp(t)) for t in ENV['t']]
    for kb_ in kbs:
        for K in Ks:
            for L in Ls:
                okKL = (L * K * (kchk if kb_ is kb else kb_) <= 1.0) & np.isfinite(kb_)
                if not okKL.any(): continue
                s = np.sqrt(L * K * np.where(okKL, kb_, 1e-300)); c = math.exp(1 / (2 * L)) / (1 - 1 / K)
                lp, sl2 = Pstar(mu_a, b, s, c)
                best = np.where(okKL, np.minimum(best, lp), best); slmax = np.where(okKL & (lp <= best), np.maximum(slmax, sl2), slmax)
    if JEN['on']:
        for kb_ in kbs:
            for lam in JEN['lams'] + ((1e-2, 1e-3, 1e-4) if JEN['wrong'] == 'c1' else ()):      # wrong 'c1': without e^{1/(2 lam)} a tiny lam would be free
                okJ = ((lam * (kchk if kb_ is kb else kb_) <= 1.0) | (JEN['wrong'] == 'above')) & np.isfinite(kb_)
                if not okJ.any(): continue
                s = np.sqrt(lam * np.where(okJ, kb_, 1e-300)); c = 1.0 if JEN['wrong'] == 'c1' else math.exp(1 / (2 * lam))
                lp, sl2 = Pstar(mu_a, b, s, c)
                best = np.where(okJ, np.minimum(best, lp), best); slmax = np.where(okJ & (lp <= best), np.maximum(slmax, sl2), slmax)
    return np.where(small, lw, np.minimum(best, lw)) + 1e-6, slmax


def Psi2_point(mu, b, kap, K, L):
    """the corollary at one state for one (K, L) (for the checks)."""
    if L * K * kap > 1: return math.inf
    lp, _ = Pstar(np.array([mu]), np.array([b]), np.array([math.sqrt(L * K * kap)]), np.array([math.exp(1 / (2 * L)) / (1 - 1 / K)]))
    return float(lp[0])
