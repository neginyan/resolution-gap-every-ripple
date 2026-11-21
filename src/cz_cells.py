"""Stage CZ 2.3: THE TABLE OF THE LOCAL ROUTE WITH THE DIRECT LEMMA.  = cy_cells.py (unchanged options T, B, F) plus
  (1) THREE NEW OPTIONS Tz, Bz, Fz built from Lemmas CZ-1 ... CZ-5 (the direct local form of the v-branch; proofs in the report CZ, section 3,
      and in cz_pieces.py; searched in cz_search.py).  The old and the new options are different lower bounds of the same Num - gamma sigma den
      (type E2 of the endpoint rule), so the rule (one option at both ends) is unchanged and the accepted set can only grow.
  (2) TWO REPAIRS OF THE OLD TABLE found in stage CZ (FIX, both on; with FIX = {'N9': False, 'SAND': False} and ZOPT['on'] = False this module is
      cy_cells.py exactly -- checked in cz_checks.py):
      FIX['N9']:   N9 = (W/2) xi_e sqrt(y kappa) with xi_e = xi/sqrt2 = sigma X1/sqrt2 is (G/4)(X1/sqrt2) sqrt(kappa/(2 beta)); co_cells ... cy_cells
                   had (X1/2): too small by sqrt2 (also in the kappa-free form N9_free of CX).
      FIX['SAND']: the sandwich factors are written into the table instead of being restored afterwards: the gains that carry the lower sandwich
                   (P2: S0 channel; hF, cK: S2 channel) get 1/(1 + eta), the S2 part of den (d2) gets 1/(1 - eta), eta = 1/ell_a, and the target is
                   gamma = (1 + D/ell + 2.5e-4)/sqrt(ell) (without the 2.1/ell that paid for the factors).  Reason: the scaling step
                   "Num >= lambda (positive part) - (remainders) >= lambda (cell expression)" needs (background gains) >= (remainders), which a box
                   with a small background (b ~ 1e-40) does not give (report CZ, section 1).  With the factors inside, nothing is restored.

THE NEW OPTIONS (b = beta sigma^2, y = (1-b)^2/(2 beta) <= y_hi = 1/(2 beta_a) <= 2e-11, K^2 = 8 ell_b + 100, z0 = K sqrt(y) <= 1).
  Shared with the old options: the w-branch (P1, N1 ... N4), den (d1 ... d4).  In the z-options the N2 ring part uses Lemma CZ-4:
    sigma^4 (1-b)^2/(4b) E_rho[s^^2 R^2/h] g_s se2/s^4 <= (K^2 (1+eta)/(8 beta (1-eta))) (2 sigma^2 D0/(1+eta)) + (eta^2 T_2(K) part): the first part is a
    fixed fraction of the gain P2 = 2 sigma^2 D0/(1+eta) of the same state, so P2 is multiplied by ringf = 1 - K^2 (1+eta)/(8 beta_a (1-eta)) > 0
    (linear in G, also in the box mu_a = 0); the second part is the line L 5.
  Lemma CZ-1/2 (direct form): 2N := Z sigma^2 E_p[s_v^2 phi] = <h S^2 (1 - cos(a + chi))> = (I) + (II) + (III), (I) + (II) = M0 + A1 + A2 + B1 + B2.
  Lines of the z-options (each is 1/2 of the bound of the lemma, in the table's units term = c sigma^p (type)):
    M0:   b Psi_0/2                                   -> P3, P4 with f_Z = 1 (the coefficient of Psi_0 is exactly b)
          (1/2) k_E (1 - e_E) |b R_theta + t_rho|     -> H 3: beta_b (eta + 0.184) k_E      [1 - e^{-u} <= 2u/(1+u), u = se_E/4 <= sigma/a']
          (1/2) k_E e_E b |Xi| <= (1/4) Qb k_E M4 sigma^2   -> C 2 (M4 = 2.07, y <= 1e-6)
    A1v:  b sigma k_E sqrt(15 y P)/4                  -> C 3: sqrt(15 beta_b/2) k_E sqrt(P)/4
    A1w:  b sigma^2 (1 + eta)/(2 sqrt(pi) L)          -> S 3.5: (beta_b/2)(1 + eta) sqrt(r_b/pi)/sqrt(4 r_a)
    A2:   b sigma^2 kappa W/(4(1-eta))                -> C 4: beta_b (kappa G)/(8(1-eta))
          b sigma^4 J2'/2                             -> L 5 (two lines)
    B1w:  sigma^2 b c_L k_E sqrt(se_E/pi)/L^2         -> S 3.5: beta_b c_L k_E^2/(2 sqrt(pi)),  c_L = 0.184 + y_hi
          b sigma^2 eta^2 (1+y/2) g_s sqrt(se2/pi)/(s^2(1-eta))   -> S 3.5: beta_b eta^2 (1+y_hi/2)/(2 sqrt(pi)(2+r_a)(1-eta))
    B2:   sqrt(b) sigma^2 U1 sqrt(kappa) W/(2(1-eta)^2)   -> C 3: sqrt(beta_b) U1 (sqrt(kappa) G)/(4(1-eta)^2)
          sigma^4 sqrt(2bP) [..]/2                    -> L 4
    PAIR (Lemma CZ-5): (III) + B1v >= (W/(1+eta)) [(1 - z0^2/2)(1 - e^{-se2/4}) + (y/2) kappa (1 - 2 delta - z0^2/12)] - tails - Frem*,
          delta = 2b/(1-b):  hF (1 - K^2 y_hi/2) [H 1];  cK (1 - 4 b_hi/(1-b_hi) - K^2 y_hi/12) [C 0; Tz only, bracket > 0];
          Bz with a negative bracket: the loss (G/4) kappa_b |bracket|/(4 beta_a (1-eta)) [C 0];  tails [C 4];
          Frem*: branch B2 = (B2c, B2s) of the old table; branch B1 = (B1m, B1c, B1l) + sqrt(kappa_b/(2 beta_a)) (B2c, B2s) [the u-part of |sin a|].
    Fz:   (III) >= 0 dropped; B1v >= -sigma^2 kappa W/(1-eta)  -> C 2: (kappa G)/(4(1-eta)).
  kappa in the true tail [KMAX, inf): kappa G <= 2 U1^2 g_s, sqrt(kappa) G <= U1 sqrt(2 g_s) sqrt(G) (K1-K3 of CX); the gain cK uses kappa_a = KMAX.
CONCAVITY IN G (per option, on (0, G_cell]): hF, cK, kappa_b G, sqrt(kappa_b) G, d2, P2 are linear in G; sqrt(P) is replaced by sqrt(P_cell) (repair Q,
  G-free); G/mu by its worst value (G-free); the true-tail forms 2 U1^2 g_s (G-free) and U1 sqrt(2 g_s) (G/sqrt(G0) + sqrt(G0))/2 (affine, the AM-GM
  tangent of CX); the tails and all other new lines are G-free.  The choices (bracket sign, true tail or not) are fixed per box.  So each z-option
  is one concave function of G, and steps (i)-(v) of the endpoint rule hold for it word for word (the two branches differ only by lines
  proportional to G or sqrt(kappa) G, or, in the true tail, by the tangent line: see TAILZ below).
  TAILZ: in the true tail the B1 branch of the z-options would add a G-free multiple of the tangent's constant, so the branches would not coincide at
  0+; there the per-option rule uses the one-branch form (B2 on the whole a'-range) only, and the split is used through the FROZEN-SPLIT RULE
  (tail_fixed_values: one split point a* at both ends; proof in its docstring).

--- docstring of cy_cells.py ---
Stage CY 2.2-2.3: THE TABLE OF THE LOCAL ROUTE, STANDARD FORM = cx_cells.py (the kappa decades and the true-tail two-piece rule of CX, now standard)
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
FN = os.environ.get('CZ_CELLS_FN', 'results/cz_cells.jsonl')
KMAX = 1e8
KTAIL = {'on': True, 'W': 1.0}
WRONG = {'W6': False, 'W7': False, 'W8': False, 'W9': False}
ZOPT = {'on': True, 'only': False, 'W': None}
#   on = add the options Tz, Bz, Fz; only = use the z-options alone (diagnostics); W = a deliberately wrong version of one new line (power checks):
#   'ring0' (ring loss dropped), 'cK2' (chirp gain doubled), 'M40' (the Xi line dropped), 'hneg0' (the R_theta, t_rho line dropped),
#   'A1w0', 'A1v0', 'A20', 'B1w0', 'B20' (that group of lines dropped), 'Fz0' (the B1v loss of Fz dropped), 'cvx' (F main made ~ G^2: convex in G, for the chord test).
FIX = {'N9': True, 'SAND': True, 'GGT': True, 'N6Y': True, 'N4J': os.environ.get('CZ_N4OLD', '0') == '0'}
# FIX['N4J'] (stage DL; default True = corrected): the line N4 with J_up of Lemma R_theta, (1/L^2)(1 + eta k_E r/(1+r)) + ...; the table up to stage DK had dropped
#   the eta k_E r/(1+r) part (found in DK: the line was up to 0.15 % below the lemma's piece at s = sigma).  False (environment CZ_N4OLD=1) = the table as it was,
#   only to reproduce the stored records of the stages CO ... DK.
# FIX['N6Y'] (stage DA 2.4): N6 = (b/2) eta k_E [(1-y)(e^{-se_E/4} - e e^{-L^2/4}) + y/2] <= (b/2) eta k_E [y + 2 sigma/(a' + sigma)]; the table had only the
#   H part B_b eta k_E (in hneg1); the part (b/2) eta k_E y = eta k_E (1-b)^2 sigma^2/4 (type C, power 2) was missing (old options T, B, F only).
# FIX['GGT'] (stage DA 2.4): gamma-tilde's term x E N2 carries 1/(1-eta) (|h''/h| <= E k'^2 |R''|/(1-eta); co_rtheta.lemma_R_theta); the formula line of
#   co_remainders.catalogue, and so co_cells ... cz_cells, had U2 k_E without it (in N13 and N14).
M4Z = 2.07; C2Z = 0.184
GAMF = {'f': 1.0}                                                                   # DG 2.2: the target gamma multiplied by f (power checks only; 1.0 = the table)
#   deliberately wrong versions (audit power, all off): W6 y bound from beta_b (CS); W7 skip judged at beta_a (CS); W8 P2 with mu_a; W9 N9 with kappa_a.
REPAIR = {'Q': True, 'LD': True}
#   the two repairs of stage CU (both on in the table; off = cu_cells.py exactly):  Q = (Q1) sqrt(P) and (Q2) G/mu at their worst value on (0, G_cell];
#   LD = the minimisation over a' in long double with the underflow guards (interval_min_ld).
DIAG = {'RAW': False, 'FRAC': None, 'TSTAR': None, 'NOB2ONLY': False, 'UCAP': False, 'UFIX': None, 'U': None, 'GUARDS': 0, 'CAPTURE': None, 'ARANGE': None, 'B1ONLY': False}
# B1ONLY (DC 2.4, candidate; off): also the branch B1 on the whole a'-range (outside the true tail): the split rule's a* = a'_lo still asked branch B2 at the point a'_lo
# DIAG['ARANGE'] (stage DA 2.3): None, or (side, theta) with side 'lo' / 'hi': the a'-range of every option is cut at a_c = theta sigma_lo r_a/(2 + r_a);
#   on the side 'lo' the F main gain is the constant form (G/4)(1 - e^{-1/theta}) instead of the H form (see arange_values).
AR_THETA = (0.25, 1.0, 4.0)
AR = {'on': True, 'hi_fix': os.environ.get('CZ_HIFIX', '1') != '0', 'levels': os.environ.get('CZ_LEVELS', '0') != '0', 'levels_low': os.environ.get('CZ_LEVELS_LOW', '1') != '0', 'q': math.e}   # hi_fix (DB; default True from DC): see terms_cell; True = corrected;
#   False (environment CZ_HIFIX=0) = the stage exactly as in DA, with the hole of DB -- only to reproduce the stored records of DA and DB
#   levels (DD 2.1; default True in DD; default False from DE 2.4 -- the kappa split closes every stuck point without it, de_pilot / de_ksplit;
#   environment CZ_LEVELS=1 turns it on = the table of DD, CZ_LEVELS=0 off = the table of DC): stage 6 of cz_column.margin, levels_values with q = AR['q']
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
    gam = (1 + ((LD(0) if FIX['SAND'] else LD(2.1)) + LD(Dd)) / ell_a + LD(2.5e-4)) / np.sqrt(ell_a)
    if GAMF['f'] != 1.0: gam = gam * LD(GAMF['f'])                                 # DG 2.2: WRONG versions only (power checks of the search); 1.0 in the table
    fl = 1 / (1 + eta) if FIX['SAND'] else LD(1); fu = 1 / (1 - eta) if FIX['SAND'] else LD(1)      # sandwich factors written into the table (FIX['SAND'])
    n9c = LD(1) / np.sqrt(LD(2)) if FIX['N9'] else LD(0.5)                                          # N9: X1/sqrt2 (FIX['N9']); the old tables had X1/2
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
    def add(t, p, c, grp='s'):
        # grp: 's' shared (w-branch, den), 'o' the old v-branch (options T, B, F), 'z' the direct v-branch (options Tz, Bz, Fz)
        T.append((t, LD(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD), grp))
        if DIAG['CAPTURE'] is not None: DIAG['CAPTURE'].setdefault('terms', []).append((sys._getframe(1).f_lineno, t, float(p), T[-1][2], grp))
    r4a, r4b = 4 * r_a, 4 * r_b
    # ===== Num, positive
    add('L', 1, 2 * r_a / r4b)                                                    # P1
    if withG: add('L', 1, fl * G / ((mu_a if WRONG['W8'] else mu_b) * (2 + r_b)) / r4b, 'o')                           # P2
    ringf = 1 - (LD(0) if ZOPT['W'] == 'ring0' else LD(1)) * (8 * ell_b + 100) * (1 + eta) / (8 * B_a * (1 - eta))        # CZ-4: N2 ring = (K^2 (1+eta)/(8 beta (1-eta))) x P2, K^2 = 8 ell_b + 100
    if withG: add('L', 1, ringf * fl * G / (mu_b * (2 + r_b)) / r4b, 'z')                                                # P2 of the z-options, net of the ring loss
    fZ = 1 - eta * kE_b
    add('C', 2, fZ * 3 * (1 - b_hi) ** 2 / (8 * (1 + w0_hi)), 'o')                     # P3
    add('C', 2, 3 * (1 - b_hi) ** 2 / (8 * (1 + w0_hi)), 'z')                          # P3 of the z-options: f_Z = 1
    hpos_c, hpos_p = fZ * (B_a / 2) / (1 + w0_hi) ** 2, 3                          # P4: (b/2)/(1+w0)^2 -> beta_a/2, power 1 + 2
    hF = fl * (G / 4) * (r_a / (2 + r_a)) if withG else 0 * G                          # F main, H power 1
    cK = fl * (G / 4) * (1 - b_hi) ** 2 * k_a / (4 * B_b) if withG else 0 * G          # P5: kappa W-term, (1-b)^2/(4b) sigma^2 -> /(4 beta_b): power 2 - 2 = 0
    hK = (G / 4) * k_b / (4 * B_a) if withG else 0 * G                            # its H part: power 3 - 2 = 1, negative
    hneg1 = B_b * (eta * kE_b + 2 * LD(0.092) * kE_b)                             # N6 + N15: b -> beta_b, H power 1 + 2 = 3
    g2t = 1 / (1 - eta) if FIX['GGT'] else LD(1)                                  # FIX['GGT']
    hneg13 = (1 + eta) / 2 * (U2 * kE_b * g2t * 2 + U1 ** 2 * gs_b / (1 - eta) ** 2 * 2)   # N13: H power 3
    # ===== den
    add('C', 3, -gam * (B_b * (1 + (eta + LD(0.184)) * kE_b)))                    # d1: b -> beta_b, power 1 + 2
    if withG: add('C', 1, -gam * fu * (G / 2))                                         # d2
    add('L', 2, -gam * r_b * (1 + 2 * eta * kE_b) / r4a)                          # d3
    if withG: add('L', 2, -gam * Gmu / (2 * (2 + r_a) * (1 - eta)) / r4a)    # d4
    # ===== Num, negative remainders
    add('L', 1, -2 * r_b * eta * kE_b * (2 + r_b) / (1 + r_b) / r4a)              # N1
    add('L', 1, -(1 / (4 * B_a)) * (r_b * (1 + eta * kE_b * r_b / (1 + r_b)) + 2 * eta * kE_b * r_b / (1 + r_a)) / r4a)   # N2: 1/b -> power 3 - 2
    add('L', 1, -(eta ** 2 * gs_b / (4 * B_a * (2 + r_a) * (1 - eta))) / r4a, 'o')    # N2 eta^2 part (the ring average bounded by eta^2)
    M4c = 3 * (1 + eta * kE_b * r_b ** 2 / (1 + r_b) ** 2) + 6 * eta * kE_b * r_b / (1 + r_b) ** 2
    M4g = 3 * Gmu / (2 * (2 + r_a) ** 2 * (1 - eta)) if withG else 0 * G
    add('C', 2, -(M4c + M4g) / 2)                                                 # N3
    n4J = eta * kE_b * r_b / (1 + r_a) if FIX['N4J'] else 0 * r_b                                                    # DL: the eta k_E r/(1+r) part of J_up (safe ends: kE, r up at r_b, 1 + r down at r_a)
    add('L', 3, -LD(1.5) * ((X1 ** 2 + CZ) * (r_b * (1 + n4J) + 2 * eta * kE_b * r_b / (1 + r_a)) + r_b ** 2 * M4c) / r4a)    # N4
    if withG: add('L', 3, -LD(1.5) * ((X1 ** 2 + CZ) * Gmu / (2 * (2 + r_a) * (1 - eta)) + r_b ** 2 * M4g) / r4a)
    add('C', 3, -(B_b / 2) * (1 + eta) * X1 / math.sqrt(2), 'o')                       # N7 xi: b -> power 1 + 2
    if FIX['N6Y']: add('C', 2, -eta * kE_b / 4, 'o')                                  # N6 y-part: (b/2) eta k_E y <= eta k_E sigma^2/4
    add('S', 3.5, -(B_b / 2) * (1 + eta) * (np.sqrt(CZ / 2) + np.sqrt(r_b / LD(math.pi))) / np.sqrt(r4a), 'o')   # N7 zeta: power 1.5 + 2
    if withG:
        add('C', 2, -((G / 2) / (1 - eta)) / 2, 'o')                                   # N11, W part
        add('S', 2.5, -(sqP / np.sqrt(LD(2)) * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a))) / (1 - eta)) / 2 / np.sqrt(r4a), 'o')   # N12
    add('C', 4, -(LD(0.184) * B_b * kE_b) / 2, 'o')                                    # N11, b part: power 2 + 2
    f13 = (1 + eta) / 2
    add('C', 2, -f13 * (U2 * kE_b * g2t + U1 ** 2 * gs_b / (1 - eta) ** 2) / (4 * B_a), 'o')    # N13 GgtPhi y/2: power 4 - 2
    add('H', 3, -hneg13, 'o')
    fw = U1 * (1 + eta / (1 - eta)) / (1 - eta)
    add('S', 2.5, -f13 * fw * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a))) / (4 * B_a) / np.sqrt(r4a), 'o')   # power 4.5 - 2
    add('M', 3.5, -f13 * fw * kE_b * math.sqrt(2 / math.pi) / (2 * (1 + r_a) ** LD(1.5)) * np.sqrt(r4b), 'o')
    Ggt_C = U2 * kE_b * g2t + U1 ** 2 * gs_b / (1 - eta) ** 2
    Ggt_S = fw * kE_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a)))
    add('C', 3, -f13 * Ggt_C * X1 / math.sqrt(2), 'o')
    add('S', 3.5, -f13 * (Ggt_C * np.sqrt(CZ / 2) + Ggt_S * X1 / math.sqrt(2) + gP * np.sqrt(r_b / LD(math.pi))) / np.sqrt(r4a), 'o')
    add('L', 4, -f13 * Ggt_S * np.sqrt(CZ / 2) / r4a, 'o')
    # N14: sqrt(b) -> sqrt(beta_b) sigma (power + 1)
    sy = np.sqrt(1 + y_hi); sPb = sqP * np.sqrt(B_b) if withG else 0 * G; sb = np.sqrt(B_b)
    add('C', 2, -LD(0.5) * sy * (sPb * kE_b * X1 / math.sqrt(2) + sb * (1 + eta) * Ggt_C), 'o')
    add('S', 2.5, -LD(0.5) * sy * (sPb * kE_b * (np.sqrt(CZ / 2) + r_b * np.sqrt(2 / (LD(math.pi) * (1 + r_a)))) + sb * (1 + eta) * Ggt_S) / np.sqrt(r4a), 'o')
    add('C', 2, -LD(0.125) * QB * kE_b * M2, 'o')                                      # N16
    # ===== F-term remainders
    N9 = (G / 4) * (X1 * n9c) * np.sqrt((k_a if WRONG['W9'] else k_b) / (2 * B_a)) if withG else 0 * G       # sqrt(kappa/(2b)) sigma -> /sqrt(beta_a): power 2 - 1
    if withG and KTAIL['on']:
        # CX: in the true tail [KMAX, inf) the kappa-free bound (lemma in the docstring); sqrt(G) <= (G/sqrt(G0) + sqrt(G0))/2 with G0 = G_cell (affine in G)
        G0 = np.exp(np.asarray(lGref if lG0 is None else lG0, dtype=LD)) + np.zeros(n, dtype=LD)      # the tangent point of sqrt(G) (G_cell unless given)
        with np.errstate(all='ignore'): sG = np.where(G0 > 0, (G / np.sqrt(np.where(G0 > 0, G0, 1)) + np.sqrt(G0)) / 2, LD(0))   # G0 = 0: G = 0 on the box
        N9f = LD(KTAIL['W']) * (U1 / 2) * np.sqrt(gs_b / 2) * sG * (X1 * n9c) / np.sqrt(2 * B_a)
        N9 = np.where(tail3, N9f, N9)
    N10 = LD(0.255) * gs_b * U2 * (1 + np.sqrt(LD(math.pi) / tau_min)) / (4 * B_a ** 2)   # 1/b^2: power 4 - 4
    fF = G / (4 * (1 - eta)) if withG else 0 * G
    B2c = fF * X1 / math.sqrt(2)
    B2s = fF * (np.sqrt(CZ / 2) + r_b / np.sqrt(LD(math.pi) * (2 + r_a))) / np.sqrt(r4a)
    B1m = fF * X1 / (math.sqrt(2) * np.sqrt(LD(math.pi) * (2 + r_a))) * np.sqrt(r4b)
    B1c = fF * (np.sqrt(CZ / (2 * LD(math.pi) * (2 + r_a))) + r_b / (2 * (2 + r_a)) + (X1 ** 2 + CZ))
    B1l = fF * (r_b ** 2 / (2 * (2 + r_a))) / r4a
    # ===== stage CZ: the direct v-branch (options Tz, Bz, Fz); every line is derived in the module docstring
    wz = ZOPT['W']
    Kz2 = 8 * ell_b + 100; Kz = np.sqrt(Kz2); TKc = LD(0.8) * (Kz + 1) * LD(math.exp(-50.0))      # T_2(K) <= TKc sigma^4 for sigma >= sigma_lo
    z2 = Kz2 * y_hi                                                                             # z0^2 <= K^2 y_hi (<= 1.6e-7)
    cL = LD(C2Z) + y_hi
    if withG:
        with np.errstate(all='ignore'):
            G0z = np.exp(np.asarray(lGref if lG0 is None else lG0, dtype=LD)) + np.zeros(n, dtype=LD)
            sGz = np.where(G0z > 0, (G / np.sqrt(np.where(G0z > 0, G0z, 1)) + np.sqrt(G0z)) / 2, LD(0))     # sqrt(G) <= its tangent at G0 (affine in G)
            kfree = LD(1)
            KG = np.where(tail3, kfree * 2 * U1 ** 2 * gs_b, k_b * G)                                  # kappa G  (true tail: <= 2 U1^2 g_s, K1-K3)
            SKG = np.where(tail3, kfree * U1 * np.sqrt(2 * gs_b) * sGz, np.sqrt(k_b) * G)              # sqrt(kappa) G  (true tail: <= U1 sqrt(2 g_s G))
            KG = np.where(np.isnan(KG), LD(0), KG); SKG = np.where(np.isnan(SKG), LD(0), SKG)
    else:
        KG = np.zeros(n, dtype=LD); SKG = np.zeros(n, dtype=LD)
    add('L', 5, -(eta ** 2 * gs_b / (4 * B_a * (2 + r_a) * (1 - eta))) / r4a * TKc, 'z')          # N2 ring: eta^2 T_2(K) part
    if wz != 'M40': add('C', 2, -LD(0.25) * QB * kE_b * LD(M4Z), 'z')                             # M0: Xi
    if withG and wz != 'A1v0': add('C', 3, -np.sqrt(15 * B_b / 2) * kE_b * sqP / 4, 'z')          # A1v
    if wz != 'A1w0': add('S', 3.5, -(B_b / 2) * (1 + eta) * np.sqrt(r_b / LD(math.pi)) / np.sqrt(r4a), 'z')        # A1w
    zA2 = 0 if wz == 'A20' else 1; zB1 = 0 if wz == 'B1w0' else 1; zB2 = 0 if wz == 'B20' else 1
    if withG: add('C', 4, -zA2 * B_b * KG / (8 * (1 - eta)), 'z')                                 # A2, kappa W part
    add('L', 5, -zA2 * (B_b / 2) * r_b * (1 + eta * kE_b * r_b / (1 + r_b)) / r4a, 'z')                 # A2, sigma^4 J2' (1/L^2 part)
    add('L', 5, -zA2 * (B_b / 2) * eta ** 2 * gs_b / ((2 + r_a) * (1 - eta)) / r4a, 'z')                # A2, sigma^4 J2' (eta^2 part)
    add('S', 3.5, -zB1 * B_b * cL * kE_b ** 2 / (2 * np.sqrt(LD(math.pi))), 'z')                        # B1w, first part
    add('S', 3.5, -zB1 * B_b * eta ** 2 * (1 + y_hi / 2) / (2 * np.sqrt(LD(math.pi)) * (2 + r_a) * (1 - eta)), 'z')   # B1w, second part
    if withG:
        add('C', 3, -zB2 * np.sqrt(B_b) * U1 * SKG / (4 * (1 - eta) ** 2), 'z')                         # B2, first part
        add('L', 4, -zB2 * np.sqrt(2 * B_b) * sqP / 8 * (kE_b * r_b / (1 + r_b) + eta ** 2 / (np.sqrt(r_a * (2 + r_a)) * (2 + r_a) * (1 - eta) ** 2)), 'z')   # B2, sigma^4 part
    add('C', 4, -U1 ** 2 * gs_b * (Kz + 5) * LD(0.4) * LD(math.exp(-50.0)) / (1 - eta), 'z')      # pair: the three Gaussian tails beyond |s^| = K
    hFz = hF * (1 - z2 / 2)                                                                       # pair: F main
    if wz == 'cvx' and withG: hFz = hFz * G / np.exp(np.asarray(lGref, dtype=LD))                 # WRONG (power of the chord test): a gain ~ G^2, convex in G
    dl2 = 4 * b_hi / (1 - b_hi)                                                                   # 2 delta at b_hi
    brk = 1 - dl2 - z2 / 12                                                                       # 2 c_delta at its smallest value on the box
    cKz = cK * np.maximum(brk, 0) * (2 if wz == 'cK2' else 1)                                     # pair: chirp gain (bracket > 0)
    lossK = KG / (16 * B_a * (1 - eta)) * np.maximum(-brk, 0) if withG else 0 * G                 # pair: chirp loss (bracket < 0): (G/4) kappa |bracket|/(4 beta_a (1-eta))
    sK2 = np.sqrt(k_b / (2 * B_a))                                                                # sqrt(y kappa) <= sqrt(kappa_b/(2 beta_a))
    with np.errstate(all='ignore'):
        fFs = np.where(tail3, U1 * np.sqrt(2 * gs_b) * (sGz if withG else 0 * G) / (4 * (1 - eta)) / np.sqrt(2 * B_a), fF * np.where(tail3, 0, sK2)) if withG else 0 * G
    uB2c = fFs * X1 / math.sqrt(2)                                                                # the u-part of |chi||sin a| (branch B1): sqrt(y kappa) (B2c, B2s)
    uB2s = fFs * (np.sqrt(CZ / 2) + r_b / np.sqrt(LD(math.pi) * (2 + r_a))) / np.sqrt(r4a)
    FzK = KG / (4 * (1 - eta)) * (0 if wz == 'Fz0' else 1)                                        # Fz: B1v
    def collect(extra, grp='o'):
        acc = {}
        TT = [(t, p, c) for t, p, c, g in T if g in ('s', grp)]
        if COHREC['mode'] is not None: TT, extra = _coh_hook(TT + extra, n), []           # DF: the coherent (slab) coefficients, see terms_cell_coh
        for t, p, c in TT + extra:
            acc.setdefault((t, float(p)), np.zeros(n, dtype=LD)); acc[(t, float(p))] = acc[(t, float(p))] + c
        out = {k: np.zeros(n, dtype=LD) for k in 'LHCSM'}
        if DIAG['CAPTURE'] is not None:
            ab = {}; cnt = {}
            for t, p, c in TT + extra:
                ab[(t, float(p))] = ab.get((t, float(p)), 0) + np.abs(c); cnt[(t, float(p))] = cnt.get((t, float(p)), 0) + 1
            DIAG['CAPTURE'].setdefault('nets', []).append({k: (ab[k], acc[k], cnt[k]) for k in acc})
        for (t, p), c in acc.items():
            c = np.where(c >= 0, c * (1 - EPS), c * (1 + EPS))
            q = LD(p) - 1
            lo_q, hi_q = (LD(1), LD(1)) if COHREC['mode'] == 'tm' else (s_lo ** q, s_hi ** q)     # DG: sigma folded into the coefficients
            out[t] = out[t] + np.where(c >= 0, c * np.minimum(lo_q, hi_q), c * np.maximum(lo_q, hi_q))
            if DIAG['CAPTURE'] is not None:
                ty = DIAG['CAPTURE'].setdefault('_types', {}); prev = ty.get(t, (0, 0))
                ty[t] = (prev[0] + np.abs(np.where(c >= 0, c * np.minimum(lo_q, hi_q), c * np.maximum(lo_q, hi_q))), prev[1] + 1)
        if DIAG['CAPTURE'] is not None:
            DIAG['CAPTURE'].setdefault('types', []).append({t: (DIAG['CAPTURE']['_types'].get(t, (0, 0))[0], out[t], DIAG['CAPTURE']['_types'].get(t, (0, 0))[1]) for t in out})
            DIAG['CAPTURE']['_types'] = {}
        return out
    ap_lo = 16 * r_a * s_lo ** 2; ap_hi = 4 * r_b / s_lo
    AV = (COHREC['mode'] == 'replay' and COH.get('A', False)) or COHREC['mode'] == 'tm'
    if AV: ap_lo = 4 * s_lo ** 3 + 0 * r_a; ap_hi = LD(1) + 0 * r_a      # DF 2.1: the variable A = sigma^2/s^2 in [4 sigma^3, 1] (a' = 4 r A/sigma), r-free
    if COHREC['mode'] == 'tm': ap_lo, ap_hi = (np.asarray(v, dtype=LD) for v in COHREC['tm_range'])   # DG: the hull of the range of At over the box
    lowA = False
    if DIAG['ARANGE'] is not None:
        side_, th_ = DIAG['ARANGE'][0], DIAG['ARANGE'][1]
        if side_ in ('mid', 'hiA'):
            # DC 2.4 (candidate, off unless levels_values is called): a piece [a_1, a_2] of the a'-range given per box (log a_1, log a_2 arrays).
            # 'mid': the constant form at the RIGHT end: every state with a' <= a_2 has se2/4 >= 1/theta_2, theta_2 = a_2 (2 + r_a)/(sigma_lo r_a)
            #        (the inequality of the stage of DA 2.3 with theta = theta_2), so 1 - e^{-se2/4} >= 1 - e^{-1/theta_2};  'hiA': the H form on [a_1, a'_hi].
            la1 = np.asarray(DIAG['ARANGE'][1], dtype=LD); la2 = np.asarray(DIAG['ARANGE'][2], dtype=LD) if side_ == 'mid' else None
            ap_lo = np.maximum(ap_lo, np.exp(la1))
            if side_ == 'mid':
                ap_hi = np.minimum(ap_hi, np.exp(la2)); lowA = True
                wr_ = DIAG['ARANGE'][3] if len(DIAG['ARANGE']) > 3 else None            # WRONG versions (power checks only): a log-factor, or
                lcut = la1 if wr_ == 'left' else la2                                    # 'left': theta from the piece's LEFT end; 'sigma_hi'; 'r_b'
                lsg = np.log(s_hi) if wr_ == 'sigma_hi' else np.log(s_lo); rr = r_b if wr_ == 'r_b' else r_a
                inv_th2 = np.exp(lsg + np.log(rr) - np.log(2 + rr) - lcut)                 # 1/theta_2 = sigma_lo r_a/((2 + r_a) a_2)
                cF = -np.expm1(-inv_th2) * (2 if ZOPT['W'] == 'hfc2' else 1) * (np.exp(LD(wr_)) if isinstance(wr_, float) else 1)
            else:
                cF = None
            empty = empty | ~(ap_lo < ap_hi)
            if side_ == 'mid': hF = fl * (G / 4) * cF if withG else 0 * G; hFz = hF * (1 - z2 / 2)
            side_ = 'levels'
        else:
            ac_ = LD(th_) * s_lo * r_a / (2 + r_a)          # a' <= a_c gives se2/4 = sigma r/((2+r) a') >= 1/theta on the whole box
            if side_ == 'lo': ap_hi = np.minimum(ap_hi, ac_); lowA = True
            else: ap_lo = np.maximum(ap_lo, ac_)
            empty = empty | ~(ap_lo < ap_hi)
            cF = (1 - LD(math.exp(-1.0 / th_))) * (2 if ZOPT['W'] == 'hfc2' else 1)        # 1 - e^{-se2/4} >= 1 - e^{-1/theta}  ('hfc2': deliberately doubled)
        if side_ == 'levels': pass
        elif side_ == 'lo' or not AR['hi_fix']:
            # DB FOUND: as written in DA, this line also ran on the side 'hi' (a' >= a_c), where it replaced the H-form coefficient r_a/(2+r_a) by
            # cF = 1 - e^{-1/theta} > r_a/(2+r_a) -- NOT a valid lower bound there (for large a' the true gain ~ (r/(2+r)) sigma/a' < cF sigma/(a'+sigma)).
            # AR['hi_fix'] = True keeps the H form of the table on the side 'hi' (the stage as described in its docstring).
            hF = fl * (G / 4) * cF if withG else 0 * G; hFz = hF * (1 - z2 / 2)
        if ZOPT['W'] == 'cvx' and withG:                                              # WRONG (DB: power of the chord test of the stage): a gain ~ G^2
            hF = hF * G / np.exp(np.asarray(lGref, dtype=LD)); hFz = hFz * G / np.exp(np.asarray(lGref, dtype=LD))
    def fmin(o, p_, q_, withM):
        if COHREC['mode'] == 'record': return np.zeros(n, dtype=LD)                    # DF: the record pass only needs the coefficients
        al, be, C_, S_, M_ = o['L'], o['H'], o['C'], -o['S'], -o['M']
        sh = np.where(be >= 0, s_hi ** 2 / (4 * r_a), s_lo ** 2 / (4 * r_b)) if AV else np.where(be >= 0, s_hi, s_lo)   # A-form: the shift sigma^2/(4r)
        if COHREC['mode'] == 'tm': sh = np.where(be >= 0, np.asarray(COHREC['tm_shift'][1], dtype=LD), np.asarray(COHREC['tm_shift'][0], dtype=LD))   # DG: worst shift over the box
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
    for opt in (opts if opts is not None else (OPTS if withG else (('F', 'Fz') if ZOPT['on'] else ('F',)))):
        if opt.endswith('z'):
            # ---- stage CZ: the direct options
            Hz = [('H', hpos_p, (B_a / 2) / (1 + w0_hi) ** 2), ('H', 3, -hneg1 * (0 if ZOPT['W'] == 'hneg0' else 1))]
            if opt == 'Fz':
                oF = collect(Hz + [('C', 2, -FzK)], 'z')
                if debug == 'Fz': return oF
                best = np.maximum(best, fmin(oF, ap_lo, ap_hi, False)); continue
            Hz = Hz + [(('C', 0) if lowA else ('H', 1)) + (hFz,)]
            Cz = [('C', 0, cKz)] if opt == 'Tz' else [('C', 0, -lossK)]
            if DIAG['CAPTURE'] is not None:                                     # DC: the named option lines of the z-options (diagnostics only)
                _nm = ['P3/P4 (M0: b Psi0/2)', 'M0 ring k_E(1-e_E)|b R + t| (H 3)', 'F main (pair, hF (1 - z0^2/2))', 'chirp gain cK (pair)' if opt == 'Tz' else 'chirp loss (pair, bracket < 0)',
                       'B2c (Frem*, branch B2)', 'B2s (Frem*, branch B2)', 'B1m (branch B1)', 'B1c (branch B1)', 'B1l (branch B1)', 'u-part B2c (branch B1)', 'u-part B2s (branch B1)']
                _ls = Hz + Cz + [('C', 1, -B2c), ('S', 1.5, -B2s), ('M', 1.5, -B1m), ('C', 2, -B1c), ('L', 3, -B1l), ('C', 1, -uB2c), ('S', 1.5, -uB2s)]
                DIAG['CAPTURE'].setdefault('optz', {})[opt] = [(a, t, float(p), np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD)) for a, (t, p, c) in zip(_nm, _ls)]
            o2 = collect(Hz + Cz + [('C', 1, -B2c), ('S', 1.5, -B2s)], 'z')
            if debug == opt: return o2
            o1 = collect(Hz + Cz + [('M', 1.5, -B1m), ('C', 2, -B1c), ('L', 3, -B1l), ('C', 1, -uB2c), ('S', 1.5, -uB2s)], 'z')
            if debug == opt + '1': return o1
            with np.errstate(all='ignore'):
                u = np.where((o1['L'] > 0) & (o1['H'] > 0), np.sqrt(np.abs(o1['H']) / np.maximum(o1['L'], LD(1e-4900))), s_lo / (4 * r_a) if AV else LD(1.0))   # DF: A-image of a' = 1
            if DIAG['UCAP']: DIAG['U'] = u
            fixed = DIAG['UFIX'] is not None                                     # a split point a* frozen by the caller (the same at both ends of G)
            if fixed: u = DIAG['UFIX']
            vk = np.full(n, -np.inf, dtype=LD)
            for tstar in (DIAG['TSTAR'] if DIAG['TSTAR'] is not None else (1e-8, 1e-5, 1e-3, 0.1, 1.0, 10.0, 1e3)):
                am = np.clip(tstar * u, ap_lo, ap_hi)
                vs = np.minimum(fmin(o2, ap_lo, am, False), fmin(o1, am, ap_hi, True))
                vk = np.maximum(vk, vs if fixed else np.where(tail3, -np.inf, vs))    # TAILZ: in the true tail a split only with a frozen a* (tail_fixed_values)
            if not DIAG['NOB2ONLY']: vk = np.maximum(vk, fmin(o2, ap_lo, ap_hi, False))
            if DIAG['B1ONLY'] and not fixed: vk = np.maximum(vk, np.where(tail3, -np.inf, fmin(o1, ap_lo, ap_hi, True)))
            excl = (opt == 'Tz') & ~(brk > 0)                                    # Tz needs a positive bracket on the whole box
            best = np.maximum(best, np.where(excl, -np.inf, vk)); continue
        keepF = opt != 'F'; chirp = opt == 'T'
        Hterm = [(('C', 0) if lowA else ('H', 1)) + (hF if keepF else 0 * G,), ('H', hpos_p, hpos_c), ('H', 3, -hneg1), ('H', 1, -(hK if chirp else 0 * G))]
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
                u = np.where((o1['L'] > 0) & (o1['H'] > 0), np.sqrt(np.abs(o1['H']) / np.maximum(o1['L'], LD(1e-4900))), s_lo / (4 * r_a) if AV else LD(1.0))   # DF: A-image of a' = 1
            if DIAG['UCAP']: DIAG['U'] = u
            if DIAG['UFIX'] is not None: u = DIAG['UFIX']
            vk = np.full(n, -np.inf, dtype=LD)
            for tstar in (DIAG['TSTAR'] if DIAG['TSTAR'] is not None else (1e-8, 1e-5, 1e-3, 0.1, 1.0, 10.0, 1e3)):
                am = np.clip(tstar * u, ap_lo, ap_hi)
                vk = np.maximum(vk, np.minimum(fmin(o2, ap_lo, am, False), fmin(o1, am, ap_hi, True)))
            if not DIAG['NOB2ONLY']: vk = np.maximum(vk, fmin(o2, ap_lo, ap_hi, False))
            if DIAG['B1ONLY'] and DIAG['UFIX'] is None: vk = np.maximum(vk, np.where(tail3, -np.inf, fmin(o1, ap_lo, ap_hi, True)))
            excl = tail3 & (chirp if KTAIL['on'] else True)                      # CX: in the true tail only T is excluded (B uses N9_free)
            best = np.maximum(best, np.where(excl, -np.inf, vk))
        else:
            oF = collect(Hterm)
            if DIAG['CAPTURE'] is not None: DIAG['CAPTURE'].setdefault('agg', {})[opt] = {'o': oF, 'ap_lo': ap_lo, 'ap_hi': ap_hi, 's_lo': s_lo, 's_hi': s_hi}
            best = np.maximum(best, fmin(oF, ap_lo, ap_hi, False))
    return np.where(empty, np.inf, best)


# ===== DF 2.1: THE COHERENT FORM (slab envelope of every line's coefficient).  Proof in terms_cell_coh's docstring.
COH = {'on': os.environ.get('CZ_COH', '0') != '0', 'kr': 8, 'km': 1, 'A': True, 'w': 0.125, 'kmax': 128, 'wrong': None}
COHREC = {'mode': None, 'store': [], 'i': 0, 'K': 1, 'r_ends': None, 'capture': None}


def _coh_hook(lines, n):
    """record: keep every line's coefficient (rows = K slabs x n boxes);  replay: put in the per-line minimum over the K slabs."""
    if COHREC['mode'] == 'record':
        COHREC['store'].append([np.asarray(c, dtype=LD) + np.zeros(n, dtype=LD) for t, p, c in lines]); return lines
    if COHREC['mode'] == 'tm':                                                            # DG 2.1: the whole-sum form (dg_tm, Theorem DG-1)
        rec = COHREC['store'][COHREC['i']]; COHREC['i'] += 1
        assert len(rec) == len(lines) and all(a[0] == b[0] for a, b in zip(rec, lines)), ('DG: the replay does not match the table', len(rec), len(lines))
        return rec
    rec = COHREC['store'][COHREC['i']]; COHREC['i'] += 1
    assert len(rec) == len(lines), ('coherent form: the replay does not match the record', len(rec), len(lines))
    K = COHREC['K']; out = []
    ra, rb = COHREC['r_ends']                                                             # per slab (K, n): exp of the slab's log r ends
    for (t, p, c), cr in zip(lines, rec):
        S = cr.reshape(K, n)
        if COH.get('A', False):
            # the line in the variable A (a' = 4 r A/sigma; derivation in terms_cell_coh): factor phi(r) > 0 and the power shift per type;
            # on each slab c phi(r) >= min(c phi(r_a), c phi(r_b)) (phi monotone, the min form keeps concavity in G)
            phi = {'L': (4 * ra, 4 * rb), 'H': (1 / (4 * ra), 1 / (4 * rb)), 'S': (np.sqrt(4 * ra), np.sqrt(4 * rb)),
                   'M': (1 / np.sqrt(4 * ra), 1 / np.sqrt(4 * rb)), 'C': (LD(1), LD(1))}[t]
            if COH['wrong'] == 'phic': phi = (np.sqrt(phi[0] * phi[1]),) * 2               # WRONG: the conversion at the slab's centre
            S = np.maximum(S * phi[0], S * phi[1]) if COH['wrong'] == 'phiw' else np.minimum(S * phi[0], S * phi[1])   # 'phiw' WRONG: the better end
            p = LD(p) + {'L': -1, 'H': 1, 'S': -0.5, 'M': 0.5, 'C': 0}[t]
        if COH['wrong'] == 'max': v = S.max(axis=0)                                       # WRONG (power check): the best slab instead of the worst
        elif COH['wrong'] == 'half': v = S[:max(1, K // 2)].min(axis=0)                   # WRONG: only half of the r-range covered
        else: v = S.min(axis=0)
        out.append((t, p, v))
    if COHREC.get('capture') is not None: COHREC['capture'].append([(t, float(p), v) for t, p, v in out])
    return out


def coh_slabs(X, kr, km):
    """the slab boxes: log r cut into kr equal pieces (and log mu into km pieces where both ends are finite); returns (stacked slabs, K)."""
    X = np.asarray(X, dtype=float); n = len(X); S = []
    mfin = np.isfinite(X[:, 0]) & np.isfinite(X[:, 1])
    for i in range(kr):
        for j in range(km):
            Y = X.copy()
            Y[:, 2] = X[:, 2] if i == 0 else X[:, 2] + (X[:, 3] - X[:, 2]) * i / kr                  # the cut points are the same floats on
            Y[:, 3] = X[:, 3] if i == kr - 1 else X[:, 2] + (X[:, 3] - X[:, 2]) * (i + 1) / kr      # both sides, the ends are the box's own
            if km > 1:
                a = X[:, 0] if j == 0 else X[:, 0] + (X[:, 1] - X[:, 0]) * j / km
                b = X[:, 1] if j == km - 1 else X[:, 0] + (X[:, 1] - X[:, 0]) * (j + 1) / km
                Y[:, 0] = np.where(mfin, a, X[:, 0]); Y[:, 1] = np.where(mfin, b, X[:, 1])
            if COH['wrong'] == 'centre':                                                  # WRONG: each slab at its centre point (no safe ends)
                for k in (2, 0):
                    cc = 0.5 * (Y[:, k] + Y[:, k + 1]); ok = np.isfinite(cc); Y[ok, k] = cc[ok]; Y[ok, k + 1] = cc[ok]
            S.append(Y)
    return np.vstack(S), kr * km


def terms_cell_coh(X, Dd, withG, lGc=None, opts=None, lGref=None, kr=None, km=None):
    """THE COHERENT FORM of terms_cell (DF 2.1).  Same value structure, but every line's coefficient is the MINIMUM over slabs of the box.
    THEOREM (DF-1) [proof].  Let the box X be cut into slabs S_1, ..., S_K (log r, and log mu where finite, cut into equal pieces; the union is X).
    For every line l of the table (type t_l in L, H, C, S, M; power p_l), let c_l(S_j) be the coefficient terms_cell builds for the sub-box S_j with the
    G range (0, G_cell(X)] of the whole box, and c_l* = min_j c_l(S_j).  Then the value this function returns is a valid box value of X: every
    statement (i)-(v) of the endpoint rule (cv_cells) holds for it.
      (1) Each slab is a box of the table (its ends lie in X), and the table is valid for every box and every G range (0, G_ref] that contains the
          states' G (the G terms use G_ref only as an upper bound of G: sqrt(P) <= sqrt(G_ref/g_s(r_a)), G/mu <= min(G_ref/mu_a, cap)).  So for every
          state of S_j and every line l:  (true value of line l) >= c_l(S_j) sigma^{p_l} f_t(a', sigma), with f_t >= 0 the type function (a', 1/(a'+sigma),
          1, sqrt(a'), 1/sqrt(a')) -- this is viewpoint 2 of the table (every coefficient at the safe end of its box), line by line.
      (2) A state of X lies in some S_j; since f_t >= 0, c_l(S_j) f_t >= c_l* f_t.  So (true value of l) >= c_l* sigma^{p_l} f_t at every state of X,
          and Num - gamma sigma den >= sum_l c_l* sigma^{p_l} f_t: the reduction of the table with the coefficients c_l*.
      (3) The rest is the table's own argument with c_l* in place of c_l(X): the nets of equal type and power, their worst sigma end, the rounding, the
          worst H shift and the a'-minimisation (fmin, interval_min_ld) only use that each coefficient is a valid lower bound.
      (4) Concavity in G (step (i)): c_l(S_j) is affine in G (or G-free) for every j (the table's viewpoint 1), so c_l* is a minimum of affine functions:
          concave.  The net, the worst sigma end min(c s_lo^q, c s_hi^q), the rounding, the worst H shift min_sh be/(a'+sh) and the S, M terms are
          NONDECREASING concave functions of the coefficients, so Phi(a', .) stays concave in G; (ii) and (iii) follow as in the table.
      (5) Step (iv), the coincidence of the two branches at G -> 0+: the lines in which they differ are G times a G-free factor on every slab, and
          min_j G k_j = G min_j k_j (G >= 0), so they still vanish at 0+; the other lines are the same in both branches.  (v) as in the table.  QED.
    THE VARIABLE A (COH['A'] = True, the form used).  The table's reduced form comes from the variable A = sigma^2/s^2 in [4 sigma^3, 1] (co_cells:
    a' = 4 r A/sigma).  For ONE state (fixed r, sigma) the substitution is an identity, line by line (c = the line's coefficient, f its type function):
        L:  c sigma^{p-1} a'             = (4 r c)       sigma^{p-2}   A
        H:  c sigma^{p-1} /(a' + sigma)  = (c/(4 r))     sigma^{p}     /(A + sigma^2/(4 r))
        S:  c sigma^{p-1} sqrt(a')       = (sqrt(4 r) c) sigma^{p-1.5} sqrt(A)
        M:  c sigma^{p-1} /sqrt(a')      = (c/sqrt(4 r)) sigma^{p-0.5} /sqrt(A)
        C:  unchanged.
    So in A every line is (c phi(r)) times a type function of A, with phi(r) > 0 monotone in r and the power of sigma shifted by the same amount for
    every line of a type (the nets by type and power are the same groups).  On a slab [r_a, r_b]: c phi(r) >= min(c phi(r_a), c phi(r_b)) for every
    r of the slab (phi monotone and positive: if c >= 0 the smaller phi, if c < 0 the larger); this min is a nondecreasing concave function of c, so
    (4) and (5) hold for it as for c.  Then (2) with these per-slab values.  The range of A is [4 sigma^3, 1] for every r: the box takes
    [4 sigma_lo^3, 1] (contains every state's range).  The shift of H is sigma^2/(4r): be/(A + sh) at the worst shift over the box (be >= 0: the
    largest, sigma_hi^2/(4 r_a); be < 0: the smallest, sigma_lo^2/(4 r_b)) is <= the state's value, the same argument as the table's worst H shift.
    The split point of the branches B2/B1 is any point of the range (each branch is a valid bound for every a', the choice per state depends on A
    only, not on G); the default u when the L net is not positive is mapped to the A-image of the table's a' = 1, so that at zero width (one slab, a
    point) the A-form IS the table's form after the substitution: the same value up to rounding (checked in df_coh_checks, part A).
    WHY NOT THE FIRST-ORDER FORM.  The loss in the expensive region is not inside single coefficients but between lines whose r-dependence cancels only
    in the sum when the variable is A (in a' the minimiser moves with r: a'* ~ r); see the report DF.  The slabs need no bound of a slope: every
    slab coefficient is the table's own safe-end coefficient.
    The slab values are computed by terms_cell itself (record), and the minimum is put in line by line (replay; the order of the lines is the same,
    checked by an assertion).  The a'-range, the sigma ends, G_cell and every per-box choice (bracket sign, true tail, the split point) are those of X.
    Wrong versions for the power checks: COH['wrong'] = 'centre' (each slab at its centre point), 'max' (the best slab), 'half' (half the slabs)."""
    kr = COH['kr'] if kr is None else kr; km = COH['km'] if km is None else km
    n = len(X); Ys, K = coh_slabs(X, kr, km)
    rep = lambda v: None if v is None else np.tile(np.asarray(v), K)
    lGc_s, lGref_s = rep(lGc), rep(lGref)                                              # the G range (0, G_cell(X)] of the whole box on every slab
    COHREC.update(mode='record', store=[], i=0, K=K, r_ends=(np.exp(Ys[:, 2].astype(LD)).reshape(K, n), np.exp(Ys[:, 3].astype(LD)).reshape(K, n)))
    try:
        with np.errstate(all='ignore'): terms_cell(Ys, Dd, withG, lGc=lGc_s, opts=opts, lGref=lGref_s)
        COHREC.update(mode='replay', i=0)
        with np.errstate(all='ignore'): v = terms_cell(np.asarray(X, dtype=float), Dd, withG, lGc=lGc, opts=opts, lGref=lGref)
        assert COHREC['i'] == len(COHREC['store']), 'coherent form: not every recorded collect was replayed'
    finally:
        COHREC.update(mode=None, store=[], i=0, K=1, r_ends=None)
    return v


def values_coh(X, Dd=0.0, lGc=None, kr=None, km=None, rows=120_000):
    """values() with the coherent form (DF 2.1): per option k, both ends k+'0+' and k+'c' (in pieces of <= rows slab rows)."""
    X = np.asarray(X, dtype=float)
    if lGc is None: lGc, _ = box_P(X)
    K = (COH['kr'] if kr is None else kr) * (COH['km'] if km is None else km); step = max(1, rows // K)
    out = {k + e: np.full(len(X), -np.inf) for k in OPTS for e in ('0+', 'c')}
    with np.errstate(all='ignore'):
        for i in range(0, len(X), step):
            Y = X[i:i + step]; lg = lGc[i:i + step]; z = np.full(len(Y), -np.inf)
            for k in OPTS:
                out[k + '0+'][i:i + step] = terms_cell_coh(Y, Dd, True, lGc=z, opts=(k,), lGref=lg, kr=kr, km=km)
                out[k + 'c'][i:i + step] = terms_cell_coh(Y, Dd, True, lGc=lg, opts=(k,), lGref=lg, kr=kr, km=km)
    return {a: np.where(np.isnan(v), -np.inf, v) for a, v in out.items()}


def coh_kr(X):
    """the number of r-slabs per box: the smallest power of 2 with slab width <= COH['w'] in log r (between 1 and COH['kmax'])."""
    w = np.asarray(X, dtype=float)[:, 3] - np.asarray(X, dtype=float)[:, 2]
    return np.clip(2 ** np.ceil(np.log2(np.maximum(w, 1e-300) / COH['w'])), 1, COH['kmax']).astype(int)


def coh_values(X, Dd=0.0, lGc=None):
    """the margin of the coherent form (per-option endpoint rule), the slabs chosen per box by coh_kr (grouped by their number)."""
    X = np.asarray(X, dtype=float)
    if lGc is None: lGc, _ = box_P(X)
    kk = coh_kr(X); m = np.full(len(X), -np.inf)
    for K in np.unique(kk):
        idx = np.where(kk == K)[0]
        m[idx] = margin_from(values_coh(X[idx], Dd, lGc[idx], kr=int(K), km=COH['km']))
    return m


def skip(X):
    """(S7) beta_b <= 2.5e10: every admissible x gives tau = x/b >= 5e11/beta >= 20 (Theorem H1); the box is skipped."""
    return (X[:, 4] if WRONG['W7'] else X[:, 5]) <= LB_SKIP


OPTS_OLD = ('T', 'B', 'F'); OPTS_Z = ('Tz', 'Bz', 'Fz')
OPTS = OPTS_OLD + OPTS_Z


def set_opts():
    """the option list from the switches ZOPT['on'], ZOPT['only']."""
    global OPTS
    OPTS = OPTS_Z if ZOPT['only'] else (OPTS_OLD + OPTS_Z if ZOPT['on'] else OPTS_OLD)


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
                for oF_, oB_ in ((('F', 'B'),) if not ZOPT['on'] else ((('Fz', 'Bz'), ('Fz', 'Tz')) if ZOPT['only'] else (('F', 'B'), ('Fz', 'Bz'), ('Fz', 'Tz'), ('F', 'Bz'), ('F', 'Tz')))):
                    fF = terms_cell(Y, Dd, True, lGc=l1, opts=(oF_,), lGref=lG)
                    b1 = terms_cell(Y, Dd, True, lGc=l1, opts=(oB_,), lGref=lG, lG0=l0)
                    bc = terms_cell(Y, Dd, True, lGc=lG, opts=(oB_,), lGref=lG, lG0=l0)
                    f0q = terms_cell(Y, Dd, True, lGc=z, opts=(oF_,), lGref=lG)
                    v = np.minimum.reduce([fF, b1, bc, f0q]); v = np.where(np.isnan(v), -np.inf, v)
                    bt = np.maximum(bt, v)
        finally:
            DIAG['TSTAR'] = saved
        m = np.minimum.reduce(([] if G0['on'] else [np.where(np.isnan(f0), -np.inf, f0)]) + ([np.where(np.isnan(f0p), -np.inf, f0p)] if not ZOPT['on'] else []) + [bt])   # CY: G = 0 by Theorem G0; CZ: the 0+ end of the lower piece is taken per pair (f0q)
    best[tail] = m
    return best


TFIX = (1e-8, 1e-6, 1e-4, 1e-2, 0.1, 1.0, 10.0, 1e3)


def tail_fixed_values(X, Dd=0.0, lGc=None):
    """CZ: THE FROZEN-SPLIT RULE for the options Tz, Bz in the true kappa tail [proof].  There the branch B1 carries the u-part with the tangent of
    sqrt(G) (a G-free constant), so the two branches do not coincide at G -> 0+ and step (iv) of the endpoint rule is not available.  Instead:
    for a FIXED split point a* (the same at both ends) the function
        m(G) = min( min over a' in [a'_lo, a*] of Phi_B2(a', G),  min over a' in [a*, a'_hi] of Phi_B1(a', G) )
    is a minimum of functions that are concave in G (every coefficient affine or G-free; steps (i)-(iii) of the endpoint rule), hence concave on
    (0, G_cell]; every state of the box has Num - gamma sigma den >= sigma m(G) (at its own a' the bound of its branch applies).  So if for one
    option and one a* the table's values at G -> 0+ and at G_cell are both > ACC, the box is proved.  a* = t u_c with u_c the split scale computed at
    G_cell (frozen through DIAG['UFIX']) and t in TFIX.  The frac relaxations are of one function (type E1), so their maximum may be taken at each
    end separately, as before.  Returns the best margin (array; -inf where the row is not in the true tail)."""
    if lGc is None: lGc, _ = box_P(X)
    tail = ~np.isfinite(X[:, 7]); best = np.full(len(X), -np.inf)
    if not tail.any() or not ZOPT['on']: return best
    Y = X[tail]; lG = lGc[tail]; z = np.full(len(Y), -np.inf); bt = np.full(len(Y), -np.inf)
    saved = {k: DIAG[k] for k in ('TSTAR', 'UCAP', 'UFIX', 'U', 'NOB2ONLY')}
    try:
        with np.errstate(all='ignore'):
            for k in ('Tz', 'Bz'):
                DIAG.update(TSTAR=(1.0,), UCAP=True, UFIX=None, NOB2ONLY=True); terms_cell(Y, Dd, True, lGc=lG, opts=(k,), lGref=lG); uc = DIAG['U']
                DIAG.update(UCAP=False, UFIX=uc)
                for t in TFIX:
                    DIAG['TSTAR'] = (t,)
                    v0 = terms_cell(Y, Dd, True, lGc=z, opts=(k,), lGref=lG); vc = terms_cell(Y, Dd, True, lGc=lG, opts=(k,), lGref=lG)
                    v = np.minimum(v0, vc); bt = np.maximum(bt, np.where(np.isnan(v), -np.inf, v))
    finally:
        DIAG.update(saved)
    best[tail] = bt
    return best


def arange_values(X, Dd=0.0, lGc=None):
    """STAGE DA 2.3: THE CONSTANT FORM OF THE F MAIN GAIN ON THE WIDE-FOCUS SIDE [proof].
    The F main gain of every keepF option is (W/(2(1+eta))) (1 - e^{-se2/4}) with se2/4 = sigma r/((2+r) a').  The table bounds it by the H form
    (r/(2+r)) sigma/(a' + sigma), which for a' << r sigma is only ~ r/2 of the true value (~ 1).  For theta > 0 put a_c = theta sigma_lo r_a/(2+r_a)
    (a per-box constant).  Every state of the box with a' <= a_c has se2/4 >= (sigma/sigma_lo)(r/(2+r))(2+r_a)/(r_a theta) >= 1/theta, hence
    1 - e^{-se2/4} >= 1 - e^{-1/theta} (a C-type line, G-linear); the states with a' >= a_c keep the H form.  So for each option k and theta the
    function  m_k(G) = min( min over a' in [a'_lo, a_c] (constant form), min over a' in [a_c, a'_hi] (H form) )  is a lower bound of
    (Num - gamma sigma den)/sigma on every state of the box, and it is concave in G (a minimum of two minima of functions affine in G: cv_cells steps
    (i)-(iii); the split a_c does not depend on G).  Hence: if m_k > ACC at G -> 0+ and at G_cell, and F(0) > ACC, the box is proved (as margin_from).
    Returns the best margin over (k, theta)."""
    if lGc is None: lGc, _ = box_P(X)
    z = np.full(len(X), -np.inf); best = np.full(len(X), -np.inf)
    saved = DIAG['ARANGE']
    try:
        with np.errstate(all='ignore'):
            f0 = terms_cell(X, Dd, False)
            for th in AR_THETA:
                for k in tuple(o for o in OPTS if o not in ('F', 'Fz')):
                    ends = []
                    for lg in (z, lGc):
                        DIAG['ARANGE'] = ('lo', th); vl = terms_cell(X, Dd, True, lGc=lg, opts=(k,), lGref=lGc)
                        DIAG['ARANGE'] = ('hi', th); vh = terms_cell(X, Dd, True, lGc=lg, opts=(k,), lGref=lGc)
                        ends.append(np.minimum(vl, vh))
                    v = np.minimum(ends[0], ends[1]); best = np.maximum(best, np.where(np.isnan(v), -np.inf, v))
    finally:
        DIAG['ARANGE'] = saved
    f0 = np.where(np.isnan(f0), -np.inf, f0)
    return best if G0['on'] else np.minimum(f0, best)


def levels_values(X, q=math.e ** 2, Dd=0.0, lGc=None, opts=None, wrong=None, b1only=True):
    """STAGE DC 2.4 -- CANDIDATE (not used by the table's acceptance; diagnostics only): THE STAGE OF DA 2.3 AT MANY LEVELS.
    Pieces of the a'-range of the box: [a'_lo, a_0], [a_0, a_0 q], ..., [a_0 q^{K-1}, a_K] with the constant form of the F main gain at each piece's RIGHT
    end, and [a_K, a'_hi] with the table's H form; a_0 = 4 sigma_lo r_a/(2 + r_a) (theta = 4), a_K = the first a_0 q^k >= 4 sigma_lo (there the H form
    is within a factor 5/4 of x/(1+x)).  Each state of the box lies in one piece; on a piece ending at a_2 every state has a' <= a_2, so the inequality
    of the stage (se2/4 >= 1/theta_2, theta_2 = a_2 (2+r_a)/(sigma_lo r_a)) gives the constant form there -- the same inequality as DA 2.3, no new one.
    Per option and piece the function is concave in G (the stage's argument, the cut points do not depend on G), so the value is
    min over pieces and over the two ends G -> 0+, G_cell.  Returns the best margin over the options (G0: the G = 0 states are Theorem G0's).
    wrong: a log-factor on the constant (power check: e.g. log 2 = the constant doubled).
    b1only: also the branch B1 on a whole piece (DIAG['B1ONLY'], outside the true tail; one fixed branch per piece and box: concave in G)."""
    if lGc is None: lGc, _ = box_P(X)
    n = len(X); z = np.full(n, -np.inf); best = np.full(n, -np.inf)
    with np.errstate(all='ignore'): f0 = terms_cell(X, Dd, False)
    f0 = np.where(np.isnan(f0), -np.inf, f0)
    ell_b = X[:, 9]; lr_a = X[:, 2]; lq = math.log(q)
    la0 = math.log(4.0) - ell_b + lr_a - np.log(2 + np.exp(lr_a)); laK_target = math.log(4.0) - ell_b
    K = np.maximum(np.ceil((laK_target - la0) / lq), 0); laK = la0 + K * lq; Kmax = int(np.max(K))
    saved = (DIAG['ARANGE'], DIAG['B1ONLY']); DIAG['B1ONLY'] = b1only
    try:
        with np.errstate(all='ignore'):
            for k in (opts if opts is not None else tuple(o for o in OPTS if o not in ('F', 'Fz'))):
                v = np.full(n, np.inf)
                for lg in (z, lGc):
                    pieces = [('mid', np.full(n, -np.inf), la0)] + [('mid', np.minimum(la0 + j * lq, laK), np.minimum(la0 + (j + 1) * lq, laK)) for j in range(Kmax)] + [('hiA', laK)]
                    for pc in pieces:
                        DIAG['ARANGE'] = pc + ((wrong,) if (wrong is not None and pc[0] == 'mid') else ())
                        vv = terms_cell(X, Dd, True, lGc=lg, opts=(k,), lGref=lGc)
                        v = np.minimum(v, np.where(np.isnan(vv), -np.inf, vv))
                best = np.maximum(best, v)
    finally:
        DIAG['ARANGE'], DIAG['B1ONLY'] = saved
    return best if G0['on'] else np.minimum(f0, best)


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
    tail = ~np.isfinite(X[:, 7]) & ~(m > ACC)
    if ZOPT['on'] and tail.any():
        m = m.copy(); m[tail] = np.maximum(m[tail], tail_fixed_values(X[tail], Dd, lGc[tail]))      # CZ: the frozen-split rule of the z-options
    rest = ~(m > ACC)
    if AR['on'] and rest.any():
        m = m.copy(); m[rest] = np.maximum(m[rest], arange_values(X[rest], Dd, lGc[rest]))             # DA 2.3: the constant form of the F main gain
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
