"""Stage CY 2.2-2.3: THE TABLE OF THE LOCAL ROUTE, STANDARD FORM = cx_cells.py (the kappa decades and the true-tail two-piece rule of CX, now standard)
with two changes.  Python 3.11 grammar, numpy long double.
  (1) the brightness bound is cy_psi.lP_cell (CM-1 and Psi_2 also below mu = 3.5; proof in cy_psi's docstring);
  (2) THEOREM G0 replaces the check F(G = 0) > ACC of the endpoint rule (G0['on']; with G0['on'] = False and set_psi('cs') this module is cx_cells.py):
      the endpoint rule needed the states with G = 0 separately (the G path covers (0, G_cell] only).  Theorem G0 (cx_g0.py, proof there): for G = 0,
      b in (0, 1], L^2 >= 4 sigma^2 and every tau, mu, kappa, x:  (a) + (a') >= min(0.316/sigma, C0/sqrt(b)) >= C0 = 0.1995 > gamma(ell) for ell >= 55.26
      and sigma <= e^-55.26.  Every state of the table has sigma = e^-ell <= e^-55.26, b <= BMAX = 0.5 and L^2 >= 4 s^2 >= 4 sigma^2, so the G = 0 states of
      every box hold, and a box is accepted when one option k has v_k(0+) > ACC and v_k(G_cell) > ACC (and, in the true kappa tail, the two-piece rule
      without its F(0) condition).  The value 'F0' is still computed and returned (for the report), but no longer decides anything.

--- docstring of cx_cells.py ---
Stage CX 2.1: the CV table (cv_cells.py, unchanged otherwise) with the KAPPA TAIL REDESIGNED.  Python 3.11 grammar, numpy long double.
THE CHANGE (everything else is cv_cells.py line for line; with KTAIL['on'] = False this module is cv_cells.py exactly, up to the initial boxes):
  (1) the initial kappa grid adds the decades [3, 10], [10, 1e2], ..., [1e7, KMAX = 1e8]: finite boxes, where T, B, F are used as everywhere else
      (kappa_a, kappa_b at the box ends, as before);
  (2) the TRUE tail [KMAX, inf): option B is allowed, with N9 replaced by the kappa-free bound N9_free below; T stays excluded (cK, hK ~ kappa);
      F is unchanged.
LEMMA (kappa-free N9) [proof].  For every state of the class, (G/4) sqrt(kappa) <= (U1/2) sqrt(g_s(r_b) G/2).
  Proof.  (K1) kappa = E_rho[(s^2/tau) R'^2]/E1 with E_rho the average over the line variable s ~ N(0, tau) (co_remainders notation), so
  E1 kappa = E_rho[(s^2/tau) R'^2] <= sup R'^2 E_rho[s^2]/tau = sup R'^2.  (K2) R = sum q0_n cos(n t - phi_n), so |R'| <= sum n q0_n = N_1, and
  sqrt(x) N_1 <= U1 (the window constant of cl_link: q0_n <= 2 e^{-n^2 x/2}, sum q0_n <= Qb, U^2 = ln(1/x) + 30 <= 2 ell + 3.1).  Hence
  x E1 kappa <= x N_1^2 <= U1^2.  (K3) W_theta = x g_s E1 = P g_s/2 = G/2 and g_s(r) <= g_s(r_b), so
  (G/4) sqrt(kappa) = (W_theta/2) sqrt(kappa) = (g_s/2) sqrt(x E1) sqrt(x E1 kappa) <= (g_s/2) sqrt(x E1) U1 = (U1/2) sqrt(g_s G/2) <= (U1/2) sqrt(g_s(r_b) G/2).
  QED.  So N9 = (G/4) (X1/2) sqrt(kappa/(2 beta_a)) [the table's form] <= N9_free := (U1/2) sqrt(g_s(r_b)/2) sqrt(G) (X1/2)/sqrt(2 beta_a).
CONCAVITY.  sqrt(G) is concave, so -sqrt(G) would be convex in G.  We use sqrt(G) <= (G/sqrt(G0) + sqrt(G0))/2 for every G0 > 0 (AM-GM), with
  G0 = G_cell of the box (the caller's lGref): an affine upper bound, so -N9_free is affine in G and step (i) of the endpoint rule holds unchanged.
  The choice (N9_free in the true tail, the kappa form elsewhere) is fixed per box, not per G, so each option is one concave function of G.
Both sides of (K1)-(K3) are broken-tested in cx_kappa_rel.py (with deliberately wrong versions).  KTAIL['W'] = factor on N9_free (1 in the table;
the wrong version 0.01 is the power check TW1).

--- docstring of cv_cells.py ---
Stage CV 2.1: the local-route cell table with the two repairs of stage CU, as an ordinary source.  Python 3.11 grammar, numpy long double.
= cu_cells.py (stage CU: the CS table + option B + the per-option endpoint rule) with
  REPAIR 1 (finding 1 of CU: (Q1), (Q2) are convex in G).  On (0, G_cell] of a box, sqrt(P) <= sqrt(P_cell) and min(G/mu_a, cap) <= min(G_cell/mu_a, cap)
    (both increase with G), so the terms N12, N14 ((Q1)) and d4, N3 (M4g), N4 ((Q2)) are bounded below by their value at G_cell -- G-free on the interval.
    The value at G = G_cell is unchanged; the end G -> 0+ is evaluated with these G-free values (the caller passes lGref = log G_cell).
    G = 0 itself (the option F at G = 0, 'F0') uses no G term at all and is unchanged.
  REPAIR 2 (finding 2 of CU: float64 underflow in the minimisation over a').  The minimisation is done in long double (interval_min_ld), with two guards
    that can only lower the value: (g1) be/al zero or subnormal -> the non-convex bound (valid on the whole interval); (g2) S^2 underflowing in the
    S^2/(4 theta) bound -> S (S/(4 theta)).  WHY LONG DOUBLE AND NOT THE LOG BALANCING OF v1.1: the table keeps its structure (every coefficient is
    already built in long double), long double reaches e^{+-11355}, which the audit (CV 2.2, viewpoint 3) checks the domain stays inside, and the
    guards make any remaining underflow conservative.  v1.1's balancing would mean rewriting fmin in logarithms (a new, unchecked code path).
No coefficient differs from cu_cells.py; with REPAIR = {'Q': False, 'LD': False} the table is cu_cells.py exactly.

THE ENDPOINT RULE [proof].  Rule (as in cu_cells.py): accept a box iff F(G = 0) > ACC and, for some option k in {T, B, F}, v_k(0+) > ACC and
  v_k(G_cell) > ACC, where v_k(G) is the table's value (max over frac, t*, the one-branch option).  Claim: then Num - gamma sigma den >= 0 at every
  state of the box with brightness G in [0, G_cell].
  Notation.  For the box, an option k and a split s (B2 on [a'_lo, a*], B1 on [a*, a'_hi]; the one-branch option is a* = a'_hi; F has no split), let
  Phi_{k,s}(a', G) be the reduced bound with the repaired coefficients, the nets of equal type and power taken at their worst sigma end, the H term at
  its worst shift, and the EXACT S and M terms -S sqrt(a'), -M/sqrt(a').  For every state of the box, Num - gamma sigma den >= sigma Phi_{k,s}(a', G)
  at its own a' (each net c sigma^q >= min(c s_lo^q, c s_hi^q) for sigma in [s_lo, s_eff]; the coefficients are taken at the safe ends of the box).
  Let m_{k,s}(G) = min over a' in [a'_lo, a'_hi] of Phi_{k,s}(a', G).
  (i)  Concavity per a'.  After repair 1 every coefficient is affine in G or G-free (the list of cu_cells.py with (Q1), (Q2) now G-free on (0, G_cell]).
       A net is a sum; its worst sigma end min(c s_lo^q, c s_hi^q) and the rounding min(c(1 - eps), c(1 + eps)) are minima of linear functions of c;
       the worst H shift is min over sh in {s_lo, s_hi} of be/(a' + sh), linear in be for each sh; the S and M coefficients enter as -S sqrt(a'),
       -M/sqrt(a') with sqrt(a') > 0.  Minima and sums of concave functions are concave, so Phi_{k,s}(a', .) is concave on (0, G_cell] for each a'.
  (ii) m_{k,s} is concave on (0, G_cell] (a minimum over a' of concave functions) and has a limit at 0+.
  (iii) The table's value is a lower bound of m_{k,s}:  every frac relaxation is a lower bound of the exact S term (-S sqrt(a') >= -S sqrt(q) on [p, q];
       -S sqrt(a') >= -theta a' - S^2/(4 theta)), -M/sqrt(a') >= -M/sqrt(p) on [p, q], and interval_min is exact in the convex case and a valid lower
       bound otherwise; guards (g1), (g2) only lower it.  So for each end G_e in {0+, G_cell}: the value the table computes with (frac, s) is
       <= m_{k,s}(G_e), hence v_k(G_e) = max over (frac, s) of these <= max over s of m_{k,s}(G_e).  (frac is a relaxation of one exact function -- type
       E1 -- so taking the best frac at each end separately is allowed.)
  (iv) The split does not matter at 0+:  the two branches differ only by B1m, B1c, B1l, B2c, B2s, all proportional to fF = G/(4(1 - eta)), so they vanish
       at G -> 0+ and m_{k,s}(0+) = m_{k,s'}(0+) for any two splits s, s'.  (The split is NOT a relaxation of one function: at fixed a' the better of B1
       and B2 is a max of affine functions, convex in G.  This is why the coincidence at 0+ is needed -- the same reason as keepF in v1.1.)
  (v)  Proof of the claim.  Let s_c be the split that attains v_k(G_cell).  By (iii), m_{k,s_c}(G_cell) >= v_k(G_cell) > 0.  By (iii) and (iv),
       m_{k,s_c}(0+) = max over s of m_{k,s}(0+) >= v_k(0+) > 0.  By (ii), m_{k,s_c}(G) >= min(m_{k,s_c}(0+), m_{k,s_c}(G_cell)) > 0 for every
       G in (0, G_cell], so Num - gamma sigma den >= sigma m_{k,s_c}(G) > 0 there.  At G = 0 the option F gives F(0) > 0 directly.  QED.
  The options T, B, F are different lower bounds (type E2); the rule uses ONE option at both ends, so they need no coincidence at 0+.
  What the proof uses from the table and must hold for it (audited in CV 2.2): every coefficient affine or G-free in G on (0, G_cell] (viewpoint 1);
  every coefficient at the safe end of the box in every variable (viewpoint 2); every computed minimum a lower bound of the exact one (viewpoint 3);
  every term an instance of a proved lemma inside its range (viewpoint 4).

THE TABLE (from cs_cells.py, stage CS):

CLAIM (class (i): eta <= 1/ell).  For every state with ell in the column, x in [5e11 sigma^2, 0.003], b in [1e4 sigma^2, 0.5], L^2 <= 1/sigma,
sigma^2 <= s^2 <= L^2/4, every mu > 0, every kappa > 0 and every P_theta <= min(2 mu Qb^2, Psi_2(mu, b, kappa)):
    Num_theta - gamma sigma den_theta >= 0,   gamma = T_0(ell)/sqrt(ell),  T_0 = 1 + 2.1/ell + 2.5e-4,
with Num_theta, den_theta the bounds of Lemma R_theta (term table of co_cells.terms_cell, stage CO).  Covered elsewhere: b < 1e4 sigma^2 (Lemma BE, any tau);
beta <= 2.5e10 (then tau = x/b >= 5e11 sigma^2/b >= 20 for every admissible x: Theorem H1, target T_10 >= T_0).  Not claimed: b in (0.5, 1].

THE TERM TABLE is that of co_cells.terms_cell (each term: type L/H/C/S/M, power p of sigma, coefficient), with b = beta sigma^2:
  a factor b^k becomes beta^k sigma^{2k} (the power p grows by 2k);  y = (1-b)^2/(2 beta) in [ (1-b_hi)^2/(2 beta_b), 1/(2 beta_a) ];
  tau_min = 5e11 sigma^2/b >= 5e11/beta_b;  b <= b_hi = min(beta_b sigma_eff^2, 0.5), sigma_eff = min(e^{-ell_a}, sqrt(0.5/beta_a)).
Terms of equal type and power are netted at equal sigma; each net is then bounded at the worse end of [sigma_lo, sigma_eff] (the ends swap for a negative power).
gamma = T_0(ell_a)/sqrt(ell_a) (decreasing in ell), eta = 1/ell_a (class (i): eta <= 1/ell <= 1/ell_a), window constants at ell_b (increasing in ell).
THE BRIGHTNESS BOUND of a box is cs_psi.lP_cell (CM-1 and the corollary of CN-1 with (K, L) fixed per box: proved monotone, see cs_psi).
KAPPA TAILS: (0, 1e-12] (kappa_a = 0) and [3, inf) (CM-1 only; there the branch keepF = True, which carries kappa, is not used).
ROUNDING: the CO rule (long double; every net coefficient moved by 1e-12 in the safe direction; accepted if min/magnitude > 1e-10).
-> results/cu_cells.jsonl
"""
import json, math, os, sys, time
import numpy as np
import cy_psi as PS
import cs_psi as _PS_CS, cy_psi as _PS_CY
G0 = {'on': True}


def set_psi(which):
    """'cy' (standard) or 'cs' (the CS/CV bound, for comparisons)."""
    global PS
    PS = _PS_CY if which == 'cy' else _PS_CS


from cl_link import interval_min
LD = np.longdouble
QB = 0.25; EPS = 1e-12; ACC = 1e-10; BMAX = 0.5; LB_SKIP = math.log(2.5e10)
FN = os.environ.get('CY_CELLS_FN', 'results/cy_cells.jsonl')
KMAX = 1e8
KTAIL = {'on': True, 'W': 1.0}
WRONG = {'W6': False, 'W7': False, 'W8': False, 'W9': False}
#   deliberately wrong versions (audit power, all off): W6 y bound from beta_b (CS); W7 skip judged at beta_a (CS); W8 P2 with mu_a; W9 N9 with kappa_a.
REPAIR = {'Q': True, 'LD': True}
#   the two repairs of stage CU (both on in the table; off = cu_cells.py exactly):  Q = (Q1) sqrt(P) and (Q2) G/mu at their worst value on (0, G_cell];
#   LD = the minimisation over a' in long double with the underflow guards (interval_min_ld).
DIAG = {'RAW': False, 'FRAC': None, 'TSTAR': None, 'NOB2ONLY': False, 'UCAP': False, 'UFIX': None, 'U': None, 'GUARDS': 0, 'CAPTURE': None}
#   diagnostics for the audit only (all off in the table): RAW = return the minimum itself; FRAC, TSTAR = only these relaxations; NOB2ONLY = drop
#   the one-branch option; UCAP/UFIX = record / freeze the split scale u (one fixed relaxation, for the chord test); GUARDS counts guard firings;
#   CAPTURE = a dict to fill (cv_audit.py): the terms ('terms': (line, type, power, coefficient)), the option terms ('opt'), the nets ('nets':
#   type, power, sum of |summands|, net, count) and the aggregates handed to fmin ('agg'), with the interval ends.


def window_consts_v(ell):
    U1 = QB * np.sqrt(2 * ell + 3.1) + 1e-6; U2 = QB * (2 * ell + 3.1) + 1e-4
    gP = (U2 * (1 + QB) + U1 ** 2 + U1 * (1 + 2 * QB) / math.sqrt(math.e)) / (1 - QB) ** 2
    cchi = (U1 / (1 - QB) + math.sqrt(2 / math.pi) + QB * math.exp(-0.5) / (1 - QB)) / math.sqrt(2)
    return U1, U2, gP, cchi


def lgs(lr): return 0.5 * (lr - np.log(2 + np.exp(lr)))


def box_P(X):
    """log G_cell = log P_cell + log g_s(r_b), and the tail flag (kappa_b = inf)."""
    lB_a, lB_b, ell_a, ell_b = X[:, 4], X[:, 5], X[:, 8], X[:, 9]
    ls_hi = np.minimum(-ell_a, 0.5 * (math.log(BMAX) - lB_a))
    lb_hi = np.minimum(lB_b + 2 * ls_hi, math.log(BMAX))
    lp, sl = PS.lP_cell(X[:, 0], X[:, 1], lb_hi, X[:, 6], X[:, 7])
    return lp + lgs(X[:, 3]), sl


def interval_min_ld(al, be, ka, p, q, s, mag0=None):
    """min over a in [p, q] of al a + be/(a + s) + ka, in long double (repair 2 of stage CU).  Same formulas as cl_link.interval_min, plus two guards
    that can only LOWER the value: (g1) in the convex case, if be/al is zero or subnormal (the minimiser sqrt(be/al) - s cannot be trusted), the
    non-convex bound al p + be/(q + s) + ka is used instead (valid for every a in [p, q]: al a >= al p, be/(a+s) >= be/(q+s)); (g2) see fmin."""
    al, be, ka, p, q, s = (np.asarray(v, dtype=LD) for v in (al, be, ka, p, q, s))
    conv = (be > 0) & (al > 0)
    with np.errstate(all='ignore'):
        ratio = np.maximum(be, 0) / np.where(al > 0, al, 1)
        bad = conv & (ratio < np.finfo(LD).tiny)
        DIAG['GUARDS'] += int(bad.sum())
        conv = conv & ~bad
        au = np.where(conv, np.sqrt(ratio) - s, LD(0))
        ac = np.clip(au, p, q)
        v_conv = al * ac + be / (ac + s) + ka
        v_nc = np.where(al >= 0, al * p, al * q) + np.where(be >= 0, be / (q + s), be / (p + s)) + ka
        v = np.where(conv, v_conv, v_nc)
        if mag0 is None: return v
        m = np.asarray(mag0, dtype=LD) + np.where(conv, np.abs(al * ac) + np.abs(be / (ac + s)), np.abs(np.where(al >= 0, al * p, al * q)) + np.abs(be) / (p + s))
        return np.where(np.isfinite(v) & (m > 0), v / m, -np.inf)


def terms_cell(X, Dd, withG, lGc=None, debug=None, opts=None, lGref=None, lG0=None):
    """X rows = (lmu_a, lmu_b, lr_a, lr_b, lB_a, lB_b, lk_a, lk_b, ell_a, ell_b); returns min/magnitude of Phi/sigma over a' (array)."""
    n = len(X)
    lmu_a, lmu_b, lr_a, lr_b, lB_a, lB_b, lk_a, lk_b, ell_a, ell_b = (X[:, j].astype(LD) for j in range(10))
    s_lo = np.exp(-ell_b)
    ls_hi = np.minimum(-ell_a, LD(0.5) * (LD(math.log(BMAX)) - lB_a))
    s_hi = np.exp(ls_hi); empty = s_hi < s_lo * (1 - LD(1e-15)); s_hi = np.maximum(s_hi, s_lo)
    eta = 1 / ell_a; U1, U2, gP, cchi = window_consts_v(ell_b)
    X1 = U1 / (1 - QB); CZ = eta ** 2 / (LD(math.e) * (1 - eta) ** 2)
    gam = (1 + (LD(2.1) + LD(Dd)) / ell_a + LD(2.5e-4)) / np.sqrt(ell_a)
    mu_a, mu_b, r_a, r_b, B_a, B_b = (np.exp(v) for v in (lmu_a, lmu_b, lr_a, lr_b, lB_a, lB_b))
    k_a = np.exp(lk_a); k_b = np.exp(np.minimum(lk_b, LD(700)))
    tail3 = ~np.isfinite(X[:, 7])
    b_hi = np.minimum(B_b * s_hi ** 2, LD(BMAX))
    G = np.exp(lGc.astype(LD)) if withG else np.zeros(n, dtype=LD)
    P_hi = G / np.sqrt(r_a / (2 + r_a)) if withG else np.zeros(n, dtype=LD)
    sqP = np.sqrt(P_hi)
    if withG and REPAIR['Q']:
        # repair 1 (Q1): sqrt(P) <= sqrt(P_cell) on (0, G_cell] -- G_ref = G_cell of the box (lGref; the caller passes it, also for the end G -> 0+)
        assert lGref is not None, 'repair Q needs lGref = log G_cell'
        Gref = np.exp(np.asarray(lGref, dtype=LD)); Pref = Gref / np.sqrt(r_a / (2 + r_a))
        sqP = np.sqrt(np.maximum(Pref, P_hi))
    # (S9) G/mu = P g_s(r)/mu <= 2 Qb^2 g_s(r_b) at every state (P <= 2 mu Qb^2, g_s increasing); with mu_a = 0 (the tail (0, 1e-3]) only this bound is finite.
    #      The factor e^{1e-6} is the same safety factor as P_cell's, so at zero width the min never changes CO's value.
    with np.errstate(all='ignore'):
        Gmu = np.minimum(np.where(G > 0, G / mu_a, LD(0)), LD(2) * LD(QB) ** 2 * np.sqrt(r_b / (2 + r_b)) * np.exp(LD(1e-6))) if withG else np.zeros(n, dtype=LD)
        if withG and REPAIR['Q']:
            # repair 1 (Q2): min(G/mu_a, cap) <= min(G_cell/mu_a, cap) on (0, G_cell]
            cap = LD(2) * LD(QB) ** 2 * np.sqrt(r_b / (2 + r_b)) * np.exp(LD(1e-6))
            Gmu = np.minimum(np.where(mu_a > 0, np.maximum(Gref, G) / np.where(mu_a > 0, mu_a, 1), np.inf), cap)
    kE_a, kE_b = np.sqrt(r_a / (1 + r_a)), np.sqrt(r_b / (1 + r_b)); gs_a, gs_b = np.sqrt(r_a / (2 + r_a)), np.sqrt(r_b / (2 + r_b))
    y_hi = 1 / (2 * (B_b if WRONG['W6'] else B_a))
    w0_hi = 1.5 * y_hi
    tau_min = LD(5e11) / B_b
    M2 = LD(3.0)
    T = []
    def add(t, p, c):
        T.append((t, LD(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD)))
        if DIAG['CAPTURE'] is not None: DIAG['CAPTURE'].setdefault('terms', []).append((sys._getframe(1).f_lineno, t, float(p), T[-1][2]))
    r4a, r4b = 4 * r_a, 4 * r_b
    # ===== Num, positive
    add('L', 1, 2 * r_a / r4b)                                                    # P1
    if withG: add('L', 1, G / ((mu_a if WRONG['W8'] else mu_b) * (2 + r_b)) / r4b)                           # P2
    fZ = 1 - eta * kE_b
    add('C', 2, fZ * 3 * (1 - b_hi) ** 2 / (8 * (1 + w0_hi)))                     # P3
    hpos_c, hpos_p = fZ * (B_a / 2) / (1 + w0_hi) ** 2, 3                          # P4: (b/2)/(1+w0)^2 -> beta_a/2, power 1 + 2
    hF = (G / 4) * (r_a / (2 + r_a)) if withG else 0 * G                          # F main, H power 1
    cK = (G / 4) * (1 - b_hi) ** 2 * k_a / (4 * B_b) if withG else 0 * G          # P5: kappa W-term, (1-b)^2/(4b) sigma^2 -> /(4 beta_b): power 2 - 2 = 0
    hK = (G / 4) * k_b / (4 * B_a) if withG else 0 * G                            # its H part: power 3 - 2 = 1, negative
    hneg1 = B_b * (eta * kE_b + 2 * LD(0.092) * kE_b)                             # N6 + N15: b -> beta_b, H power 1 + 2 = 3
    hneg13 = (1 + eta) / 2 * (U2 * kE_b * 2 + U1 ** 2 * gs_b / (1 - eta) ** 2 * 2)   # N13: H power 3
    # ===== den
    add('C', 3, -gam * (B_b * (1 + (eta + LD(0.184)) * kE_b)))                    # d1: b -> beta_b, power 1 + 2
    if withG: add('C', 1, -gam * (G / 2))                                         # d2
    add('L', 2, -gam * r_b * (1 + 2 * eta * kE_b) / r4a)                          # d3
    if withG: add('L', 2, -gam * Gmu / (2 * (2 + r_a) * (1 - eta)) / r4a)    # d4
    # ===== Num, negative remainders
    add('L', 1, -2 * r_b * eta * kE_b * (2 + r_b) / (1 + r_b) / r4a)              # N1
    add('L', 1, -(1 / (4 * B_a)) * (r_b * (1 + eta * kE_b * r_b / (1 + r_b)) + 2 * eta * kE_b * r_b / (1 + r_a)) / r4a)   # N2: 1/b -> power 3 - 2
    add('L', 1, -(eta ** 2 * gs_b / (4 * B_a * (2 + r_a) * (1 - eta))) / r4a)    # N2 eta^2 part
    M4c = 3 * (1 + eta * kE_b * r_b ** 2 / (1 + r_b) ** 2) + 6 * eta * kE_b * r_b / (1 + r_b) ** 2
    M4g = 3 * Gmu / (2 * (2 + r_a) ** 2 * (1 - eta)) if withG else 0 * G
    add('C', 2, -(M4c + M4g) / 2)                                                 # N3
    add('L', 3, -LD(1.5) * ((X1 ** 2 + CZ) * (r_b + 2 * eta * kE_b * r_b / (1 + r_a)) + r_b ** 2 * M4c) / r4a)    # N4
    if withG: add('L', 3, -LD(1.5) * ((X1 ** 2 + CZ) * Gmu / (2 * (2 + r_a) * (1 - eta)) + r_b ** 2 * M4g) / r4a)
    add('C', 3, -(B_b / 2) * (1 + eta) * X1 / math.sqrt(2))                       # N7 xi: b -> power 1 + 2
    add('S', 3.5, -(B_b / 2) * (1 + eta) * (np.sqrt(CZ / 2) + np.sqrt(r_b / LD(math.pi))) / np.sqrt(r4a))   # N7 zeta: power 1.5 + 2
    if withG:
        add('C', 2, -((G / 2) / (1 - eta)) / 2)                                   # N11, W part
        add('S', 2.5, -(sqP / np.sqrt(LD(2)) * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a))) / (1 - eta)) / 2 / np.sqrt(r4a))   # N12
    add('C', 4, -(LD(0.184) * B_b * kE_b) / 2)                                    # N11, b part: power 2 + 2
    f13 = (1 + eta) / 2
    add('C', 2, -f13 * (U2 * kE_b + U1 ** 2 * gs_b / (1 - eta) ** 2) / (4 * B_a))    # N13 GgtPhi y/2: power 4 - 2
    add('H', 3, -hneg13)
    fw = U1 * (1 + eta / (1 - eta)) / (1 - eta)
    add('S', 2.5, -f13 * fw * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a))) / (4 * B_a) / np.sqrt(r4a))   # power 4.5 - 2
    add('M', 3.5, -f13 * fw * kE_b * math.sqrt(2 / math.pi) / (2 * (1 + r_a) ** LD(1.5)) * np.sqrt(r4b))
    Ggt_C = U2 * kE_b + U1 ** 2 * gs_b / (1 - eta) ** 2
    Ggt_S = fw * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a)))
    add('C', 3, -f13 * Ggt_C * X1 / math.sqrt(2))
    add('S', 3.5, -f13 * (Ggt_C * np.sqrt(CZ / 2) + Ggt_S * X1 / math.sqrt(2) + gP * np.sqrt(r_b / LD(math.pi))) / np.sqrt(r4a))
    add('L', 4, -f13 * Ggt_S * np.sqrt(CZ / 2) / r4a)
    # N14: sqrt(b) -> sqrt(beta_b) sigma (power + 1)
    sy = np.sqrt(1 + y_hi); sPb = sqP * np.sqrt(B_b) if withG else 0 * G; sb = np.sqrt(B_b)
    add('C', 2, -LD(0.5) * sy * (sPb * kE_b * X1 / math.sqrt(2) + sb * (1 + eta) * Ggt_C))
    add('S', 2.5, -LD(0.5) * sy * (sPb * kE_b * (np.sqrt(CZ / 2) + r_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a)))) + sb * (1 + eta) * Ggt_S) / np.sqrt(r4a))
    add('C', 2, -LD(0.125) * QB * kE_b * M2)                                      # N16
    # ===== F-term remainders
    N9 = (G / 4) * (X1 / 2) * np.sqrt((k_a if WRONG['W9'] else k_b) / (2 * B_a)) if withG else 0 * G       # sqrt(kappa/(2b)) sigma -> /sqrt(beta_a): power 2 - 1
    if withG and KTAIL['on']:
        # CX: in the true tail [KMAX, inf) the kappa-free bound (lemma in the docstring); sqrt(G) <= (G/sqrt(G0) + sqrt(G0))/2 with G0 = G_cell (affine in G)
        G0 = np.exp(np.asarray(lGref if lG0 is None else lG0, dtype=LD)) + np.zeros(n, dtype=LD)      # the tangent point of sqrt(G) (G_cell unless given)
        with np.errstate(all='ignore'): sG = np.where(G0 > 0, (G / np.sqrt(np.where(G0 > 0, G0, 1)) + np.sqrt(G0)) / 2, LD(0))   # G0 = 0: G = 0 on the box
        N9f = LD(KTAIL['W']) * (U1 / 2) * np.sqrt(gs_b / 2) * sG * (X1 / 2) / np.sqrt(2 * B_a)
        N9 = np.where(tail3, N9f, N9)
    N10 = LD(0.255) * gs_b * U2 * (1 + np.sqrt(LD(math.pi) / tau_min)) / (4 * B_a ** 2)   # 1/b^2: power 4 - 4
    fF = G / (4 * (1 - eta)) if withG else 0 * G
    B2c = fF * X1 / math.sqrt(2)
    B2s = fF * (np.sqrt(CZ / 2) + r_b / np.sqrt(LD(math.pi) * (2 + r_a))) / np.sqrt(r4a)
    B1m = fF * X1 / (math.sqrt(2) * np.sqrt(LD(math.pi) * (2 + r_a))) * np.sqrt(r4b)
    B1c = fF * (np.sqrt(CZ / (2 * LD(math.pi) * (2 + r_a))) + r_b / (2 * (2 + r_a)) + (X1 ** 2 + CZ))
    B1l = fF * (r_b ** 2 / (2 * (2 + r_a))) / r4a
    def collect(extra):
        acc = {}
        for t, p, c in T + extra:
            acc.setdefault((t, float(p)), np.zeros(n, dtype=LD)); acc[(t, float(p))] = acc[(t, float(p))] + c
        out = {k: np.zeros(n, dtype=LD) for k in 'LHCSM'}
        if DIAG['CAPTURE'] is not None:
            ab = {}; cnt = {}
            for t, p, c in T + extra:
                ab[(t, float(p))] = ab.get((t, float(p)), 0) + np.abs(c); cnt[(t, float(p))] = cnt.get((t, float(p)), 0) + 1
            DIAG['CAPTURE'].setdefault('nets', []).append({k: (ab[k], acc[k], cnt[k]) for k in acc})
        for (t, p), c in acc.items():
            c = np.where(c >= 0, c * (1 - EPS), c * (1 + EPS))
            q = LD(p) - 1
            lo_q, hi_q = s_lo ** q, s_hi ** q
            out[t] = out[t] + np.where(c >= 0, c * np.minimum(lo_q, hi_q), c * np.maximum(lo_q, hi_q))
            if DIAG['CAPTURE'] is not None:
                ty = DIAG['CAPTURE'].setdefault('_types', {}); prev = ty.get(t, (0, 0))
                ty[t] = (prev[0] + np.abs(np.where(c >= 0, c * np.minimum(lo_q, hi_q), c * np.maximum(lo_q, hi_q))), prev[1] + 1)
        if DIAG['CAPTURE'] is not None:
            DIAG['CAPTURE'].setdefault('types', []).append({t: (DIAG['CAPTURE']['_types'].get(t, (0, 0))[0], out[t], DIAG['CAPTURE']['_types'].get(t, (0, 0))[1]) for t in out})
            DIAG['CAPTURE']['_types'] = {}
        return out
    ap_lo = 16 * r_a * s_lo ** 2; ap_hi = 4 * r_b / s_lo
    def fmin(o, p_, q_, withM):
        al, be, C_, S_, M_ = o['L'], o['H'], o['C'], -o['S'], -o['M']
        sh = np.where(be >= 0, s_hi, s_lo)
        Mterm = M_ / np.sqrt(p_) if withM else 0 * M_
        vb = np.full(n, -np.inf, dtype=LD)
        for frac in (DIAG['FRAC'] if DIAG['FRAC'] is not None else (0.0, 1e-2, 0.3)):
            with np.errstate(all='ignore'):
                if frac > 0:
                    th = frac * al; Sterm = np.where(al > 0, S_ ** 2 / (4 * np.where(al > 0, th, 1)), np.where(S_ > 0, np.inf, 0)); alx = al * (1 - frac)
                    if REPAIR['LD']:
                        # (g2) S^2 underflowing to 0 (or subnormal) would drop a negative term: then S (S/(4 theta)) instead (only where it fires)
                        g2 = (al > 0) & (S_ > 0) & (S_ ** 2 < np.finfo(LD).tiny)
                        if g2.any():
                            DIAG['GUARDS'] += int(g2.sum())
                            Sterm = np.where(g2, S_ * (S_ / (4 * np.where(al > 0, th, 1))), Sterm)
                else:
                    Sterm = S_ * np.sqrt(q_); alx = al
                Kk = C_ - Sterm - Mterm; mag0 = np.abs(C_) + Sterm + Mterm
                pp = np.full(n, 0.0) + np.asarray(p_, float); qq = np.full(n, 0.0) + np.asarray(q_, float)
                if REPAIR['LD']:
                    v = interval_min_ld(alx, be, Kk, p_, q_, sh, None if DIAG['RAW'] else mag0)
                else:
                    v = interval_min(alx.astype(float), be.astype(float), Kk.astype(float), pp, qq, sh.astype(float), None if DIAG['RAW'] else mag0.astype(float))
            vb = np.maximum(vb, v)
        return vb
    best = np.full(n, -np.inf, dtype=LD)
    for opt in (opts if opts is not None else (('T', 'B', 'F') if withG else ('F',))):
        keepF = opt != 'F'; chirp = opt == 'T'
        Hterm = [('H', 1, hF if keepF else 0 * G), ('H', hpos_p, hpos_c), ('H', 3, -hneg1), ('H', 1, -(hK if chirp else 0 * G))]
        Cterm = (([('C', 0, cK)] if chirp else []) + [('C', 1, -N9)] + ([('C', 0, -N10)] if chirp else [])) if keepF else []
        if DIAG['CAPTURE'] is not None:
            nm = {'H': ['hF', 'P4', 'N6+N15', 'hK'], 'C': (['cK'] if chirp else []) + ['N9'] + (['N10'] if chirp else []) if keepF else []}
            DIAG['CAPTURE'].setdefault('opt', {})[opt] = ([(a, t, float(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD)) for a, (t, p, c) in zip(nm['H'], Hterm)]
                + [(a, t, float(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD)) for a, (t, p, c) in zip(nm['C'], Cterm)]
                + ([(a, t, float(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD)) for a, (t, p, c) in zip(['B2c', 'B2s', 'B1m', 'B1c', 'B1l'],
                   [('C', 1, -B2c), ('S', 1.5, -B2s), ('M', 1.5, -B1m), ('C', 2, -B1c), ('L', 3, -B1l)])] if keepF else []))
        if debug == 'noF' and not keepF: return collect(Hterm)              # aggregates for the independent check (zero-width boxes)
        if keepF:
            o2 = collect(Hterm + Cterm + [('C', 1, -B2c), ('S', 1.5, -B2s)])
            if debug == 'F': return o2
            o1 = collect(Hterm + Cterm + [('M', 1.5, -B1m), ('C', 2, -B1c), ('L', 3, -B1l)])
            if debug == 'F1': return o1
            if DIAG['CAPTURE'] is not None: DIAG['CAPTURE'].setdefault('agg', {})[opt] = {'o1': o1, 'o2': o2, 'ap_lo': ap_lo, 'ap_hi': ap_hi, 's_lo': s_lo, 's_hi': s_hi, 'tail3': tail3}
            with np.errstate(all='ignore'):
                u = np.where((o1['L'] > 0) & (o1['H'] > 0), np.sqrt(np.abs(o1['H']) / np.maximum(o1['L'], LD(1e-4900))), LD(1.0))
            if DIAG['UCAP']: DIAG['U'] = u
            if DIAG['UFIX'] is not None: u = DIAG['UFIX']
            vk = np.full(n, -np.inf, dtype=LD)
            for tstar in (DIAG['TSTAR'] if DIAG['TSTAR'] is not None else (1e-8, 1e-5, 1e-3, 0.1, 1.0, 10.0, 1e3)):
                am = np.clip(tstar * u, ap_lo, ap_hi)
                vk = np.maximum(vk, np.minimum(fmin(o2, ap_lo, am, False), fmin(o1, am, ap_hi, True)))
            if not DIAG['NOB2ONLY']: vk = np.maximum(vk, fmin(o2, ap_lo, ap_hi, False))
            excl = tail3 & (chirp if KTAIL['on'] else True)                      # CX: in the true tail only T is excluded (B uses N9_free)
            best = np.maximum(best, np.where(excl, -np.inf, vk))
        else:
            oF = collect(Hterm)
            if DIAG['CAPTURE'] is not None: DIAG['CAPTURE'].setdefault('agg', {})[opt] = {'o': oF, 'ap_lo': ap_lo, 'ap_hi': ap_hi, 's_lo': s_lo, 's_hi': s_hi}
            best = np.maximum(best, fmin(oF, ap_lo, ap_hi, False))
    return np.where(empty, np.inf, best)


def skip(X):
    """(S7) beta_b <= 2.5e10: every admissible x gives tau = x/b >= 5e11/beta >= 20 (Theorem H1); the box is skipped."""
    return (X[:, 4] if WRONG['W7'] else X[:, 5]) <= LB_SKIP


OPTS = ('T', 'B', 'F')


def values(X, Dd=0.0, lGc=None):
    """per-option box values: 'F0' (G = 0: only the option F exists), and for k in T, B, F: k+'0+' (the limit G -> 0+, i.e. the G path with G = 0
    exactly) and k+'c' (G = G_cell)."""
    if lGc is None: lGc, _ = box_P(X)
    z = np.full(len(X), -np.inf)
    with np.errstate(all='ignore'):
        out = {'F0': terms_cell(X, Dd, False)}
        for k in OPTS:
            out[k + '0+'] = terms_cell(X, Dd, True, lGc=z, opts=(k,), lGref=lGc)
            out[k + 'c'] = terms_cell(X, Dd, True, lGc=lGc, opts=(k,), lGref=lGc)
    return {a: np.where(np.isnan(v), -np.inf, v) for a, v in out.items()}


TSPLIT = (0.02, 0.1, 0.3, 0.7, 1.5, 3.0, 6.0, 12.0, 25.0)


def tail_split_values(X, Dd=0.0, lGc=None):
    """CX: THE TWO-PIECE RULE for the true kappa tail [KMAX, inf) [proof].  For t > 0 put G1 = G_cell e^-t and G0 = sqrt(G1 G_cell).
    Accept when F(G = 0) > ACC and, for some t of TSPLIT, the option F is > ACC at G -> 0+ and at G1, and the ONE-BRANCH option B (no a'-split;
    N9_free with its tangent at G0) is > ACC at G1 and at G_cell.
    Proof.  On (0, G1]: the F option is one concave function of G (cv_cells steps (i)-(iii); it has no split), so it is >= min of its ends > 0.
    On [G1, G_cell]: the one-branch B option (B2 on the whole a'-range) with N9_free <= its tangent at G0 (sqrt(G) <= (G/sqrt(G0) + sqrt(G0))/2) is one
    concave function of G (affine and G-free coefficients; the frac relaxations are of one function, type E1), so it is >= min of its ends > 0.
    The repaired (Q1), (Q2) terms use G_ref = G_cell, valid on all of (0, G_cell].  G = 0: F(0) > 0.  QED.
    Returns the best margin over t (array; -inf where the row is not in the true tail)."""
    if lGc is None: lGc, _ = box_P(X)
    tail = ~np.isfinite(X[:, 7]); best = np.full(len(X), -np.inf)
    if not tail.any() or not KTAIL['on']: return best
    Y = X[tail]; lG = lGc[tail]; z = np.full(len(Y), -np.inf); saved = DIAG['TSTAR']
    with np.errstate(all='ignore'):
        f0 = terms_cell(Y, Dd, False); f0p = terms_cell(Y, Dd, True, lGc=z, opts=('F',), lGref=lG)
        bt = np.full(len(Y), -np.inf)
        try:
            DIAG['TSTAR'] = ()
            for t in TSPLIT:
                l1 = lG - t; l0 = lG - t / 2
                fF = terms_cell(Y, Dd, True, lGc=l1, opts=('F',), lGref=lG)
                b1 = terms_cell(Y, Dd, True, lGc=l1, opts=('B',), lGref=lG, lG0=l0)
                bc = terms_cell(Y, Dd, True, lGc=lG, opts=('B',), lGref=lG, lG0=l0)
                v = np.minimum.reduce([fF, b1, bc]); v = np.where(np.isnan(v), -np.inf, v)
                bt = np.maximum(bt, v)
        finally:
            DIAG['TSTAR'] = saved
        m = np.minimum.reduce(([] if G0['on'] else [np.where(np.isnan(f0), -np.inf, f0)]) + [np.where(np.isnan(f0p), -np.inf, f0p), bt])   # CY: G = 0 by Theorem G0
    best[tail] = m
    return best


def margin_from(v):
    """THE PER-OPTION ENDPOINT RULE: F(G = 0) and, for one option k, both ends v_k(0+), v_k(G_cell)."""
    per = np.maximum.reduce([np.minimum(v[k + '0+'], v[k + 'c']) for k in OPTS])
    return per if G0['on'] else np.minimum(v['F0'], per)          # CY: G = 0 by Theorem G0


def cell_margin(X, Dd=0.0):
    """the box value: the per-option rule, and in the true kappa tail also the two-piece rule (either proves the box; accepted when > ACC)."""
    lGc, _ = box_P(X)
    m = margin_from(values(X, Dd, lGc))
    tail = ~np.isfinite(X[:, 7]) & ~(m > ACC)
    if KTAIL['on'] and tail.any():
        m = m.copy(); m[tail] = np.maximum(m[tail], tail_split_values(X[tail], Dd, lGc[tail]))
    return m


def value_at(X, lt, Dd=0.0, opts=None):
    """max over the options at G = G_cell e^{lt} (lt <= 0); opts = (k,) for one option."""
    lGc, _ = box_P(X)
    with np.errstate(all='ignore'):
        v = terms_cell(X, Dd, True, lGc=lGc + lt, opts=opts, lGref=lGc)
    return np.where(np.isnan(v), -np.inf, v)


def cell_ok(X, Dd=0.0):
    return cell_margin(X, Dd) > ACC


def initial_boxes(ell_a, ell_b, nl=10, wm=1.0, wr=4.0, wB=4.0, wk=2.0):
    lBlo = LB_SKIP; lBhi = math.log(BMAX) + 2 * ell_b
    lm = list(np.arange(math.log(1e-3), math.log(4 * ell_b + 40), wm)) + [math.log(4 * ell_b + 40)]
    lr = list(np.arange(-3 * ell_b, math.log(0.25), wr)) + [math.log(0.25)]
    lB = list(np.arange(lBlo, lBhi, wB)) + [lBhi]
    lk = list(np.arange(math.log(1e-12), math.log(3.0), wk)) + [math.log(3.0)]
    top = math.log(3.0)
    if KTAIL['on']:
        lk += [math.log(10.0 ** k) for k in range(1, 9)]; top = math.log(KMAX)          # CX: the decades [3, 10], ..., [1e7, KMAX]
    le = np.linspace(ell_a, ell_b, nl + 1)
    mus = [(-np.inf, math.log(1e-3))] + list(zip(lm[:-1], lm[1:])) + [(math.log(4 * ell_b + 40), np.inf)]
    ks = [(-np.inf, math.log(1e-12))] + list(zip(lk[:-1], lk[1:])) + [(top, np.inf)]
    out = []
    for m0, m1 in mus:
        for c, d in zip(lr[:-1], lr[1:]):
            for e, f in zip(lB[:-1], lB[1:]):
                for g, h in ks:
                    for ea, eb in zip(le[:-1], le[1:]): out.append((m0, m1, c, d, e, f, g, h, ea, eb))
    return np.array(out)


def certify(ell_a, ell_b, Dd=0.0, max_cells=200_000_000, chunk=100_000, wl=2.0, minw=1e-6, X0=None, progress=False):
    X0 = initial_boxes(ell_a, ell_b) if X0 is None else X0
    stack = [X0]; total = 0; skipped = 0; t0 = time.time(); thin = None; nch = 0
    cw = [(0, 1.0), (2, 0.25), (4, 0.7), (6, 0.5), (8, wl)]
    while stack:
        X = stack.pop()
        if len(X) > chunk: stack.extend(np.array_split(X, int(math.ceil(len(X) / chunk)))); continue
        s = skip(X); skipped += int(s.sum()); X = X[~s]
        if not len(X): continue
        total += len(X)
        if total > max_cells: return {'ell_a': ell_a, 'ell_b': ell_b, 'D': Dd, 'closed': False, 'cells': total, 'reason': 'cell budget', 'seconds': round(time.time() - t0, 1)}
        mg = cell_margin(X, Dd); ok = mg > ACC; bad = X[~ok]
        if ok.any():
            i0 = int(np.argmin(np.where(ok, mg, np.inf)))
            if thin is None or mg[i0] < thin[0]: thin = (float(mg[i0]), [float(v) for v in X[i0]])
        nch += 1
        if progress and nch % 200 == 0:
            print(json.dumps({'progress': nch, 'cells': total, 'skipped': skipped, 'stack': int(sum(len(a) for a in stack)), 'sec': round(time.time() - t0)}), flush=True)
        if not len(bad): continue
        W = np.stack([np.where(np.isfinite(bad[:, j]) & np.isfinite(bad[:, j + 1]), bad[:, j + 1] - bad[:, j], 0.0) * wt for j, wt in cw], axis=1)
        k = np.argmax(W, axis=1); mw = np.max(W, axis=1)
        if float(mw.min()) < minw:
            jj = int(np.argmin(mw))
            return {'ell_a': ell_a, 'ell_b': ell_b, 'D': Dd, 'closed': False, 'cells': total, 'skipped': skipped, 'reason': 'cells too small',
                    'stuck_cell': [float(v) for v in bad[jj]], 'stuck_value': float(mg[~ok][jj]), 'thinnest_accepted': thin, 'seconds': round(time.time() - t0, 1)}
        new = []
        for ii, (j, wt) in enumerate(cw):
            sel = bad[k == ii]
            if not len(sel): continue
            mid = 0.5 * (sel[:, j] + sel[:, j + 1])
            Lc = sel.copy(); Rc = sel.copy(); Lc[:, j + 1] = mid; Rc[:, j] = mid; new += [Lc, Rc]
        stack.append(np.vstack(new))
    return {'ell_a': ell_a, 'ell_b': ell_b, 'D': Dd, 'closed': True, 'cells_evaluated': total, 'skipped': skipped, 'initial_boxes': len(X0), 'thinnest_accepted': thin, 'seconds': round(time.time() - t0, 1)}


if __name__ == '__main__':
    ea, eb = float(sys.argv[1]), float(sys.argv[2])
    d = certify(ea, eb, progress=True)
    print(json.dumps(d), flush=True); open(FN, 'a').write(json.dumps(d) + '\n')
