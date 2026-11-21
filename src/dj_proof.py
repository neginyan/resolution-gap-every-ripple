"""AUDIT GUIDE (stage DN; the computation below is unchanged except the constant c_CM of Lemma CM-1, see cm_const.py):
  WHAT: the proof of Theorem DJ-T in English with its constants evaluated at a point ell (consts), and the numerical checks of its steps on random states
  (check_steps, check_remainders, check_rule).  WHERE: DO_証明まとめ.md section 3 (the proof, in the same order: (F), (R), (I), (c), (II-ch), (II-s), (m1)-(m4)),
  section 6 (the records of the checks: section 6.0 is the final one) and section 7 (the constants at ell = 55.26).  The validity for EVERY ell >= 55.26
  is not from here but from the interval proof dl_consts.py (section 3.9).
Stage DJ: THEOREM DJ-T (every line of the z-options, every state of the class, every ell >= 55.26), its proof, and the checks of every step.  Python 3.11 grammar.

NOTATION.  ell >= ell_1 := 55.26, sigma = e^{-ell}, eta = 1/ell, c := 10, Gam := sqrt((1 + c/ell)/ell), k2 := 1/(2 (1 - eta)), Gam2 := Gam k2, fl := 1/(1 + eta).
A state (mu, r, b, kappa), B = b/sigma^2; P the brightness, G = g_s P, g_s = sqrt(r/(2 + r)); a = a' in (0, 4 r/sigma].  k_E = sqrt(r/(1 + r)),
U1 = sqrt(2 ell + 3.1)/4 + 1e-6, X1 = (4/3) U1.  The lines are those of dg_tm.z_lines (dj_lines.coeffs: the same coefficients, compared line by line); the
option-branches are Fz, Tz-B2, Tz-B1 (Tz needs brk := 1 - 4b/(1 - b) - z2/12 > 0, z2 = (8 ell + 100)/(2B)).  The five main lines, divided by sigma:
    P1 = a/2,  P2z = alpha G a,  hFz = beta G/(a + sigma),  P4z = (b omega/2)/(a + sigma),  cKz = chi G,
    alpha = (1 - q) fl/(4 mu r (2 + r)), q = (8 ell + 100)(1 + eta)/(8 B (1 - eta)),  beta = fl (1 - z2/2) r/(4 (2 + r)),  omega = (1 + 3/(4B))^{-2},
    chi = fl kf kappa sigma/(16 b),  kf := (1 - b)^2 brk;      the target  Gam (b k1 + G k2)  (lines d1, d2; d3, d4 are counted with the remainders), k1 = 1 + (eta + 0.184) k_E.
THE CLASS.  ell >= 55.26;  mu > 0;  sigma^3 <= r <= 1/4;  B >= B_min := max(2.5e10, 50 (8 ell + 100)),  b <= 1/2;  kappa > 0.
THE HYPOTHESIS (H') ON P (class facts, proved in earlier stages):
    (A) P <= mu/8.   (K) kappa P <= 2 U1^2.   (CM) P/2 <= U(P; mu, b, 1, 1)  (Lemma CM-1).
    (J) P/2 <= U(P; mu, b, sqrt(lam kappa_b), e^{1/(2 lam)}) for every lam > 0 and kappa_b >= kappa with  b <= lam kappa_b <= 1  (the corollary of Lemma DH-1,
        used only where CM-1 is applied at a focus with b' = b/(lam kappa_b) <= 1).

THEOREM DJ-T [proof].  For every state of the class, every P > 0 satisfying (H') and every a in (0, 4 r/sigma], the option-branch chosen by the RULE below has
        (sum of its lines with gamma = Gam) >= 0,        i.e.   (F_full^2 - 1) ell >= 10.
THE RULE (c1 := 0.78, c_T := 3.5, c_ch := 2.9, a_s := 4 cm^2 ell^6 sigma^3/r with cm := 2 X1 sqrt(2 + r)/((1 - eta) fl (1 - z2/2) sqrt(2 pi))):
    Case I   (G <= c1 sqrt(b)/Gam2):   Tz-B2 if (b < 0.1 and kappa >= c_T sqrt(ell) b/sigma), otherwise Fz.
    Case II  (G >  c1 sqrt(b)/Gam2):   if r <= c_ch sqrt(ell) sigma: Tz-B2 for every a;   otherwise Tz-B2 for a < a_s and Tz-B1 for a >= a_s.

PROOF.  The numbers are values at ell = 55.26 of expressions monotone in ell in the stated direction (consts(); check_consts(); MONO).
(F) FACTS FROM (H').
  (F1) P <= 0.7008:  (CM) with E0 <= 1/16, E ln(2 B0/E) increasing, B0(1/16, 1/2) = 2.25:  P <= 2 [(1.25/16) ln 72 + c_CM/2]  (c_CM = sqrt2/(16e); 0.01625 up to stage DM).
  (F2) [lam = 1]  if max(kappa, 16 b) <= kappa_b <= 1:  P <= w16 sqrt(kappa_b), w16 := e^{1/2} [(1 + 1/32)(1/8) ln(32 B0(1/16, 1/16)) + 2 c_CM/16] <= 0.8972
       ((J) with s = sqrt(kappa_b), c = e^{1/2}, b' <= 1/16, E^ <= 1/16).
  (F3) [Lemma DI-1 (iv), (v): the closed forms of (CM)];  (F4) [Lemma DI-1 (K): lam = mu, kappa <= kappa_b <= 1/mu, kappa_b >= 16 b e^mu/mu:
       P <= 4 mu e^{-mu} sqrt(e mu kappa_b) E_J(mu), E_J(mu) := (1 + 4.43 e^{-mu/2})^2 exp(mu e^{-mu}/32) + 6.2e-4, for mu >= 6].
(R) THE REMAINDER LINES (each bound is elementary; check_remainders() evaluates every ratio on random states).  es := 1e-11 covers the terms named "tiny" below that are charged to the
    background lines P1, P4z;  es_sigma := ell^2 e^{-ell} (ESS(); 3.1e-21 at 55.26, and ell es_sigma -> 0) covers the terms with a positive power of sigma that are charged to the lines
    proportional to G (P2z, the target): a fixed 1e-11 there would enter a0 of (N) as ell * 1e-11.
  (R1) L-type.  N1 = eps1(r) P1, eps1 := eta k_E (2 + r)/(1 + r) <= 0.01457.   N2, d3, N4, ring2, A2a, A2b, B2b <= tiny * P1.   d4 + N4G <= es_sigma * P2z, B1l <= es_sigma * P2z
       (B1l: for mu < ell + ln ell, which holds in Case II by (b.2)).
  (R2) H-type.  hneg1 = eps_h(r) P4z, eps_h := 2 k_E (eta + 0.184)/omega <= 0.1808.
  (R3) S-type.  A1w + B1w1 + B1w2 = c_S b sqrt(sigma a), c_S <= 0.155:  <= 2 c_S sqrt(sigma) (1 + sigma) P4z/omega for a <= 1 and <= c_S sqrt(sigma) P1 for a >= 1 (b <= 1/2): tiny.
  (R4) constants.  N3 + M0Xi + A1v + pair <= 1.77 sigma.  With m1 := 1 - eps1 - e0, m4 := 1 - eps_h - e0 (e0 := 1.26e-5):
       (1 - eps1 - es) a/2 + (1 - eps_h - es)(b omega/2)/(a + sigma) - 1.77 sigma >= m1 a/2 + m4 (b omega/2)/(a + sigma)   for every a >= 0
       [the left side is >= th_bg sqrt(b omega) - sigma/2 >= 1.4e5 sigma, th_bg := sqrt((1 - eps1 - es)(1 - eps_h - es)) >= 0.8985, so 1.77 sigma is at most
       1.26e-5 of it].   STEP 1':  m1 a/2 + m4 (b omega/2)/(a + sigma) >= sqrt(m1 m4 b omega) - sigma/2 >= Gam b k1 + c1F sqrt(b), c1F >= 0.7857.
  (R5) Fz:  FzK + A2k + B2a =: K_F.  In Case I with (b >= 0.1 or kappa < c_T sqrt(ell) b/sigma):  K_F <= 1.01e-3 sqrt(b)
       [FzK + A2k <= c_F sigma kappa G, c_F := (1/4 + 1/16)/(1 - eta); with G <= c1 sqrt(b)/Gam2 and kappa < c_T sqrt(ell) b/sigma this is <= c_F c_T c1 ell b^{3/2}/(Gam2 sqrt ell);
       with (K): <= 2 c_F U1^2 g_s sigma.  For b <= b0 := 5e-4/(c_F c_T c1 ell) the first is <= 1e-3 sqrt(b); for b > b0 the second is tiny * sqrt(b).  B2a <= tiny sqrt(b) by (K)].
  (R6) Tz-B2:  B2c + B2s <= c_B2 G for a <= 4 r/sigma, c_B2 := X1/(4 sqrt2 (1 - eta)) + c_s/(4 (1 - eta)), c_s := sqrt(CZ/2) + r/sqrt(pi (2 + r)) <= 0.102;  c_B2 <= 0.0896 sqrt(ell).
       A2k <= (2 b^2/((1 - eta) fl kf)) cKz;   B2a <= (4 U1 b^{3/2}/(sqrt(kappa) (1 - eta)^2 fl kf)) cKz.
  (R7) Tz-B1 (Case II, r > c_ch sqrt(ell) sigma, a >= a_s):  B1m <= ell^{-3} hFz + tiny * P2z   [B1m/hFz = cm sqrt(sigma/r)(sqrt a + sigma/sqrt a): <= ell^{-3} for
       a_s <= a <= a_L := r/(4 cm^2 ell^6 sigma); for a >= a_L, B1m/P2z <= (its value at a_L) = tiny];   B1c <= tiny * Gam2 G;
       uB2c + uB2s <= (1 + sqrt2 c_s/X1) uB2c,  uB2c/cKz = 2 X1 sqrt(b/kappa)/((1 - eta) fl kf) <= c_u sqrt(r), c_u <= 0.48 (by (c) below).
(I) CASE I.  Fz:  sum >= [m1 a/2 + m4 (b omega/2)/(a + sigma) - Gam b k1] - K_F - Gam2 G + (P2z - d4 - N4G) + P3z >= (c1F - 1.01e-3) sqrt(b) - Gam2 G >= 0.
    Tz-B2 (b < 0.1, kappa >= c_T sqrt(ell) b/sigma):  the same background part, and  cKz - B2c - B2s - A2k - B2a >= 0:  kf >= 0.4493, cKz >= cK kappa sigma G/b with
    cK >= 0.02758; A2k <= 0.0463 cKz, B2a tiny; (1 - 0.047) cK c_T sqrt(ell) >= c_B2.
(c) CASE II FORCES THE CHIRP.  In Case II:  G^2 > c1^2 b/Gam2^2 >= 1.9863 ell b, and G^2 <= (r/2) P^2.
    (c1) b < cb P^2 with cb := (Gam2/(3 c1))^2 <= 0.05593/ell (G <= P/3); so b <= 0.0275/ell (F1), then P <= P_II := 0.5223 ((CM) with this b), b <= 0.01526/ell,
         brk >= 0.998, kf >= 0.9975 (Tz is allowed), and T := b k1/(G k2) < tc G/ell, tc := Gam2 Gam k1 ell/c1^2 <= 1.0779, T <= 0.1877/ell.
    (c2) kappa <= 1:  kappa > c_kap ell b/r, c_kap := 2 c1^2/(Gam2^2 ell w16^2) >= 4.935   [(F2) with kappa_b = max(kappa, 16 b): 1.9863 ell b < (r/2) w16^2 kappa_b, and
         c_kap ell/r > 16 excludes kappa_b = 16 b].   Hence chi > fl kf c_kap ell sigma/(16 r).
    (c3) kappa > 1:  b < (Gam2^2/c1^2)(r/2) P_II^2, so chi > fl kf c1^2 sigma/(8 Gam2^2 P_II^2 r)  (>= 0.89 ell sigma/r).
    (c4) hence in Case II  sqrt(b/kappa) <= sqrt(r/(c_kap ell)) (kappa <= 1) or <= Gam2 sqrt(r/2) P_II/c1 (kappa > 1): (R7)'s c_u; and mu < ell + ln ell (b.2).
(II-ch) CASE II, r <= c_ch sqrt(ell) sigma, Tz-B2:  sum >= [background part - Gam b k1 >= 0] + (1 - es_sigma) P2z + hFz + chi G (1 - 1e-3) - c_B2 G - Gam2 G (1 + es_sigma), and by (c2)/(c3)
    chi (1 - 1e-3) >= min(fl kf c_kap sqrt(ell)/(16 c_ch), fl kf c1^2 sqrt(ell)/(8 Gam2^2 ell P_II^2 c_ch)) (1 - 1e-3) >= c_B2 + Gam2 (1 + es_sigma)   [0.1041 sqrt(ell) against 0.0996 sqrt(ell)].
(II-s) CASE II, r > c_ch sqrt(ell) sigma, a < a_s (<= ell^7 sigma^2 <= 1e-9 sigma), Tz-B2:  hFz >= beta G/(sigma (1 + 1e-9)) >= 0.1085 r G/sigma >= 0.3149 sqrt(ell) G >= c_B2 G + Gam2 G (1 + es_sigma);
    the background part is >= Gam b k1; the rest is >= 0.
(II-m) CASE II, r > c_ch sqrt(ell) sigma, a >= a_s, Tz-B1.  By (R):  sum >= X a + Y/(a + sigma) + m5 chi G - Gam2 G (mT + T)   with
        X := m1/2 + m2 alpha G,  Y := m4 b omega/2 + m3 beta G,   m2 := 1 - 3 es_sigma (d4 + N4G, B1l and the tail of B1m), m3 := 1 - ell^{-3}, m5 := 1 - c_u sqrt(r) - 2.1 b^2, mT := 1 + es_sigma (B1c).
    Put u := m1/(2 m2 alpha G), v := m4 b omega/(2 m3 beta G), Th* := 2 sqrt(m2 m3 alpha beta)/Gam2, ch := m5 chi/Gam2, xi := (r sqrt(mu)/sigma) sqrt(m3 (1 - z2/2)/(m2 (1 - q)))
    (so sigma sqrt(m2 alpha/(m3 beta)) = 1/xi), rho := sigma sqrt(X/Y) <= rhobar := sqrt(m1/(m4 B omega) + 1/xi^2).   For every a >= 0:
        X a + Y/(a + sigma) >= sqrt(XY)(2 - rho) if rho <= 1;   >= min(Y/(2 sigma), sqrt(2 XY)) always.
    Th* >= vth0 sqrt(ell/(4 mu)) with vth0 := th0 (8/9) (1 + c/ell)^{-1/2} sqrt(m2 m3) >= 0.7858, th0 := ((1 - eta)/(1 + eta)) sqrt((1 - q)(1 - z2/2)).
  (m1) xi < 8.  Then mu < 64 sigma^2/(c0^2 r^2) <= 7.7/ell.  Y/(2 sigma) >= m3 beta G/(2 sigma) >= 0.157 sqrt(ell) G and sqrt(2 XY) >= Th* Gam2 G/sqrt2 >= 5.5 Gam2 G: both >= Gam2 G (mT + T).
  (m2) xi >= 8 and Th' := Th* (1 - rhobar/2) >= mT + T:  sqrt(XY)(2 - rho) >= Gam2 G Th' sqrt((1 + u)(1 + v)) >= Gam2 G (mT + T).
  (m3) NARROW:  8 <= xi < ell^2 and Th' < mT + T.  rhobar <= 0.12501, so mu > x_n ell, x_n >= 0.1347 (mu > 7.44 > 5.61): the bootstrap (b.1) gives P <= 4 mu e^{-mu} E_CM.
       kappa <= 1/mu:  (F4) with kappa_b = max(kappa, 16 b e^mu/mu):  1.9863 ell b < (r/2) 16 e mu^3 e^{-2 mu} E_J^2 kappa_b, so kappa_b > c_J ell b e^{2 mu}/(mu^3 E_J^2 r), c_J := c1^2/(8 e Gam2^2 ell) >= 0.0913;
       this excludes kappa_b = 16 b e^mu/mu, so kappa > c_J ell b e^{2 mu}/(mu^3 E_J^2 r).   kappa > 1/mu:  b < (Gam2^2/c1^2)(r/2) 16 mu^2 e^{-2 mu} E_CM^2.   In both cases
            chi >= fl kf c_J ell sigma e^{2 mu}/(16 mu^3 E_J^2 r),   and in a narrow state sigma/r > sqrt(mu) c0/ell^2:
            ch >= Ch(ell, mu) := m5 fl kf c_J c0 e^{2 mu}/(16 (Gam2 sqrt ell) sqrt(ell) mu^{5/2} E_J^2) >= mT + T
       (at ell = 55.26, mu = 7.44: Ch >= 17; Ch increases with mu and, at mu = x_n ell, with ell).
  (m4) WIDE:  xi >= ell^2 and Th' < mT + T.  This is the proof of Lemma DI-M (di_lemma.py, (b.0)-(b.6)) with the constants below; the changes are:
       c1 = 0.78 for 0.88 (so cb, tc as in (c1)); T <= tc min(mu/24, P_II/3)/ell; rhobar <= sqrt(1.23/B + 1/ell^4); x0 >= 0.1531 (mu > 8.46);
       E_CM := (1 + 3.445 e^{-mu/2})^2 (1 + 2e-3/ell);  u, v carry m1/m2, m4/m3 and ch carries m5: after (b.4) r <= 18.7 E_CM^2 e^{-2 mu}, so k_E <= sqrt(r) is e^{-mu}-small and
       m1, m4, m5 >= 1 - 6e-4 (their product in u^3 v ch: >= 0.997);  Th' >= th1 (1 - 4 dl/ell)^{-1/2} with eps1 <= 0.76/ell^2 (m3 = 1 - ell^{-3});  K is multiplied by 0.997.
       The conditions (N) and (F) hold with these constants (consts(): at 55.26 the slack of (N) is 0.592; on the grid up to 1e12 they hold).
       (N0): for dl := ell/4 - mu >= 3.75, Th' >= th1 (1 - 15/ell)^{-1/2} >= mT + Tbar(mu_II) >= mT + Tbar, so D <= 0 there; hence D > 0 forces dl < 3.75 (where Tbar <= Tbar_N),
       and then dl < a0/(2 th1) <= 3.75.
    Every state of Case II with r > c_ch sqrt(ell) sigma is in exactly one of (m1)-(m4); the line xi = ell^2 between (m3) and (m4) belongs to (m4).   QED.

THE LOW-mu TAIL is inside the theorem: no step uses a lower bound on mu ((m1) and (m2) take the small mu; Case I and (II-ch) do not involve mu).
WHERE THE LOWER END OF b IS USED:  (R4) (the constants 1.77 sigma against sqrt(b)) and (b.2), (b.5).   WHERE a <= 4 r/sigma IS USED: (R6), (R7) (B2s, uB2s).
-> results/dj_proof.json (constants, 60 digits, (AG), steps, remainders, wrong versions), results/dj_proof_rule.json (the rule end to end, the borders),
   results/dj_proof_tight.json (the smallest value of the rule per regime)"""
import json, math, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
from decimal import Decimal as Dc, getcontext
import numpy as np
import di_ceiling as CE, dj_lines as J, dj_search as S

C = 10.0; ELL1 = 55.26
C1 = 0.78; CT = 3.5; CCH = 2.9; XI1 = 8.0
ES = 1e-11; E0 = 1.26e-5


def ESS(ell):
    """es_sigma := ell^2 e^{-ell}: the bound of the terms that carry a positive power of sigma against the lines proportional to G (d4, N4G, B1l, the tail of B1m against P2z;
    B1c against the target).  3e-21 at ell = 55.26, decreasing, and ell * es_sigma -> 0 (a fixed 1e-11 would not do for ell -> infinity: ell * 1e-11 enters a0)."""
    return ell ** 2 * math.exp(-ell)


def E_CM(mu, ell): return (1 + 3.445 * np.exp(-mu / 2)) ** 2 * (1 + 2e-3 / ell)
def E_J(mu): return (1 + 4.43 * np.exp(-mu / 2)) ** 2 * np.exp(mu * np.exp(-mu) / 32) + 6.2e-4


def lB0(E, bp): return 2 * math.log(1 + math.sqrt(E) + (E / 2) ** (1 / (2 + bp)))


def consts(ell):
    """the constants of the proof at ell."""
    eta = 1 / ell; fl = 1 / (1 + eta); Gs = math.sqrt(1 + C / ell); G2s = Gs / (2 * (1 - eta)); o = {}
    o['Gam sqrt(ell)'] = Gs; o['Gam2 sqrt(ell)'] = G2s
    U1 = 0.25 * math.sqrt(2 * ell + 3.1) + 1e-6; X1 = U1 / 0.75; CZ = eta ** 2 / (math.e * (1 - eta) ** 2); o['X1/sqrt(ell)'] = X1 / math.sqrt(ell)
    Bm = 2.5e10; q = (1 + eta) / (400 * (1 - eta)); z2 = 0.01; om = (1 + 0.75 / Bm) ** -2        # B >= max(2.5e10, 50 (8 ell + 100)): the uniform bounds of 1/B, q, z2
    o['q_max'] = q; o['z2_max'] = z2
    kE = math.sqrt(0.2); o['k1_max'] = 1 + (eta + 0.184) * kE
    # ---- (F)
    o['F1: P <='] = 2 * ((1.25 / 16) * math.log(72) + CM.C_CM / 2)
    o['w16'] = math.exp(0.5) * ((1 + 1 / 32) * (1 / 8) * (math.log(32) + lB0(1 / 16, 1 / 16)) + 2 * CM.C_CM / 16)
    # ---- (R)
    o['eps1_max'] = eta * kE * 2.25 / 1.25; o['epsh_max'] = 2 * kE * (eta + 0.184) / om
    o['c_S'] = (1 + eta) / (4 * math.sqrt(math.pi)) + (0.184 + 0.5 / Bm) * 0.2 / (2 * math.sqrt(math.pi)) + eta ** 2 * (1 + 0.25 / Bm) / (2 * math.sqrt(math.pi) * 2 * (1 - eta))
    M4c = 3 * (1 + eta * kE * 0.0625 / 1.5625) + 6 * eta * kE * 0.25 / 1.5625; M4g = 3 * (1 / 24) / (2 * 4 * (1 - eta))        # G/mu <= g_s/8 <= 1/24; (2 + r)^2 >= 4
    o['R4: constants/sigma <='] = (M4c + M4g) / 2 + 0.25 * 0.25 * 2.07 * kE + math.sqrt(3.75) * kE * math.sqrt(o['F1: P <=']) / 4 + 1e-9
    thbg = math.sqrt((1 - o['eps1_max'] - ES) * (1 - o['epsh_max'] - ES)); o['th_bg'] = thbg
    o['R4: e0 needed'] = o['R4: constants/sigma <='] / (thbg * math.sqrt(Bm * om) - 0.5) + ES
    m1 = 1 - o['eps1_max'] - E0; m4 = 1 - o['epsh_max'] - E0
    o['c1F'] = math.sqrt(m1 * m4 * om) - 0.5 / math.sqrt(Bm) - Gs * o['k1_max'] * math.sqrt(0.5) / math.sqrt(ell)
    cF = (0.25 + 1 / 16) / (1 - eta); b0 = 5e-4 / (cF * CT * C1 * ell)
    o['R5: K_F/sqrt(b) <='] = max(cF * CT * C1 * ell * b0 / G2s, 2 * cF * U1 ** 2 / 3 * math.exp(-ell) / math.sqrt(min(b0, 0.1))) + math.exp(-ell) * U1 ** 2 * math.sqrt(2 / 3 * 0.7008 / 3) / (4 * (1 - eta) ** 2)
    o['Case I (Fz): c1F - K_F/sqrt(b) - c1 (must be >= 0)'] = o['c1F'] - o['R5: K_F/sqrt(b) <='] - C1
    cs = math.sqrt(CZ / 2) + 0.25 / math.sqrt(math.pi * 2.25); o['c_s'] = cs
    cB2 = X1 / (4 * math.sqrt(2) * (1 - eta)) + cs / (4 * (1 - eta)); o['c_B2/sqrt(ell)'] = cB2 / math.sqrt(ell)
    kf01 = 0.81 * (1 - 0.4 / 0.9 - z2 / 12); o['kf (b < 0.1)'] = kf01; cK = fl * kf01 / 16; o['cK'] = cK
    a2k = 0.01 / (8 * (1 - eta) * cK); o['Case I (Tz-B2): A2k/cKz <='] = a2k
    o['Case I (Tz-B2): (1 - a2k - 1e-6) cK c_T sqrt(ell) - c_B2 (must be >= 0)'] = (1 - a2k - 1e-6) * cK * CT * math.sqrt(ell) - cB2
    # ---- (c)
    cb = (G2s / (3 * C1)) ** 2; o['cb ell'] = cb; bI = cb * o['F1: P <='] ** 2 / ell
    PII = 2 * ((1 + bI / 2) / 16 * (math.log(32) + lB0(1 / 16, bI)) + CM.C_CM * bI); o['P_II'] = PII; bII = cb * PII ** 2 / ell; o['b_II ell'] = bII * ell
    brk = 1 - 4 * bII / (1 - bII) - z2 / 12; kf = (1 - bII) ** 2 * brk; o['brk (Case II)'] = brk; o['kf (Case II)'] = kf
    tc = G2s * Gs * o['k1_max'] / C1 ** 2; o['tc'] = tc; o['T_max ell'] = tc * PII / 3
    o['c_kap'] = 2 * C1 ** 2 / (G2s ** 2 * o['w16'] ** 2); o['c_kap ell 4 - 16 (must be > 0)'] = o['c_kap'] * ell * 4 - 16
    o['16 b_II (must be <= 1)'] = 16 * bII
    rhs = cB2 / math.sqrt(ell) + G2s * (1 + ESS(ell)) / ell                                    # (c_B2 + Gam2 (1 + es))/sqrt(ell)
    o['II-ch: chi/sqrt(ell) lower bound (kappa <= 1)'] = fl * kf * o['c_kap'] / (16 * CCH) * (1 - 1e-3)
    o['II-ch: chi/sqrt(ell) lower bound (kappa > 1)'] = fl * kf * C1 ** 2 / (8 * G2s ** 2 * PII ** 2 * CCH) * (1 - 1e-3)
    o['II-ch: needed (c_B2 + Gam2)/sqrt(ell)'] = rhs
    o['II-ch: slack (must be >= 0)'] = min(o['II-ch: chi/sqrt(ell) lower bound (kappa <= 1)'], o['II-ch: chi/sqrt(ell) lower bound (kappa > 1)']) - rhs
    o['II-ch: A2k + B2a relative to cKz <='] = 2 * bII ** 2 / ((1 - eta) * fl * kf) + 4 * U1 * bII * 0.5 / (math.sqrt(o['c_kap'] * ell) * (1 - eta) ** 2 * fl * kf) + 4 * U1 * bII ** 1.5 / ((1 - eta) ** 2 * fl * kf)
    o['II-s: hFz/(sqrt(ell) G) lower bound'] = fl * (1 - z2 / 2) / (4 * 2.25) * CCH / (1 + 1e-9); o['II-s: slack (must be >= 0)'] = o['II-s: hFz/(sqrt(ell) G) lower bound'] - rhs
    cm = 2 * X1 * 1.5 / ((1 - eta) * fl * (1 - z2 / 2) * math.sqrt(2 * math.pi)); o['cm/sqrt(ell)'] = cm / math.sqrt(ell)
    o['II-s: log(a_s/sigma) <='] = math.log(4 * cm ** 2 * ell ** 6 / (CCH * math.sqrt(ell))) - ell              # a_s/sigma = 4 cm^2 ell^6 sigma^2/r, r > c_ch sqrt(ell) sigma
    cu1 = 2 * X1 / (math.sqrt(o['c_kap'] * ell) * (1 - eta) * fl * kf); cu2 = 2 * X1 * G2s / math.sqrt(ell) * math.sqrt(0.5) * PII / (C1 * (1 - eta) * fl * kf)
    o['c_u'] = max(cu1, cu2) * (1 + math.sqrt(2) * cs / X1) + 4 * U1 * bII / (math.sqrt(o['c_kap'] * ell) * (1 - eta) ** 2 * fl * kf)
    # ---- (II-m)
    m2 = 1 - 3 * ESS(ell); m3 = 1 - ell ** -3; mT = 1 + ESS(ell); th0 = (1 - eta) / (1 + eta) * math.sqrt((1 - q) * (1 - z2 / 2)); o['th0'] = th0
    vth0 = th0 * (8 / 9) / Gs * math.sqrt(m2 * m3); o['vth0'] = vth0; Tm = o['T_max ell'] / ell
    c0lo = math.sqrt(m3 * (1 - z2 / 2)); o['c0 >='] = c0lo
    o['m1: mu ell <'] = XI1 ** 2 / (c0lo ** 2 * CCH ** 2)
    o['m1: Y/(2 sigma)/(sqrt(ell) G) >='] = m3 * fl * (1 - z2 / 2) * CCH / (8 * 2.25)
    o['m1: slack 1 (must be >= 0)'] = o['m1: Y/(2 sigma)/(sqrt(ell) G) >='] - G2s * (mT + Tm) / ell
    o['m1: Th*/sqrt2 >='] = vth0 * ell / (2 * math.sqrt(o['m1: mu ell <'])) / math.sqrt(2); o['m1: slack 2 (must be >= 0)'] = o['m1: Th*/sqrt2 >='] - (mT + Tm)
    rb8 = math.sqrt(m1 / (m4 * Bm * om) + 1 / XI1 ** 2); o['rhobar (xi >= 8)'] = rb8
    xn = (vth0 * (1 - rb8 / 2) / (2 * (mT + Tm))) ** 2; o['x_n'] = xn; mun = xn * ell; o['mu_n'] = mun
    cJ = C1 ** 2 / (8 * math.e * G2s ** 2); o['c_J'] = cJ
    o['m3: 16 b e^mu at mu_n (must be <= 1)'] = 16 * (cb / ell) * (4 * 2.25 * 1.02) ** 2 * mun ** 2 * math.exp(-mun)       # b < cb P^2, P <= 9.18 mu e^-mu (b.1, first pass)
    o['m3: c_J ell e^mu - 16 mu^2 E_J^2 r at mu_n, r = 1/4 (must be > 0)'] = cJ * ell * math.exp(min(mun, 700.0)) - 16 * mun ** 2 * float(E_J(mun)) ** 2 * 0.25
    # in a narrow state of (m3): r < ell^2 sigma/(c0 sqrt(mu)), so m5 >= 1 - c_u ell sigma^{1/2} ... (tiny)
    m5n = 1 - o['c_u'] * math.sqrt(ell ** 2 * math.exp(-ell) / (c0lo * math.sqrt(mun))) - 2.1 * bII ** 2; o['m3: m5 >='] = m5n
    o['m3: log Ch(ell, mu_n)'] = math.log(m5n * fl * kf * cJ * c0lo / (16 * G2s * math.sqrt(ell) * mun ** 2.5 * float(E_J(mun)) ** 2)) + 2 * mun
    o['m3: slack (must be >= 0)'] = o['m3: log Ch(ell, mu_n)'] - math.log(mT + Tm)
    # ---- (m4): the proof of DI-M with the new constants
    rho_max = math.sqrt(m1 / (m4 * Bm * om) + 1.0 / ell ** 4); o['rho_max (wide)'] = rho_max
    vthw = vth0 * (1 - rho_max / 2); o['vth0 (1 - rho/2) (wide)'] = vthw
    lo, hi = 1e-6, 1.0                                                              # x0: the largest x with vthw/(2 sqrt x) >= mT + tc min(x/24, P_II/(3 ell))
    for _ in range(200):
        m = 0.5 * (lo + hi)
        if vthw / (2 * math.sqrt(m)) >= mT + tc * min(m / 24, PII / (3 * ell)): lo = m
        else: hi = m
    o['x0'] = lo; mu2 = lo * ell; o['mu_II'] = mu2; cbl = cb / ell; mub = min(mu2, mun)
    o['b.1 first pass: 0.065 mu c_b P <='] = 2 * CM.C_CM * 14.29 * cbl; o['b.1 first pass: mu b/2 <='] = 9.545 * cbl
    p1 = 4 * 2.25 * math.exp(o['b.1 first pass: mu b/2 <=']) / (1 - o['b.1 first pass: 0.065 mu c_b P <=']); o['b.1 first pass: P/(mu e^-mu) <='] = p1
    o['b.1 second pass: mu b/2 <= (at mu_n)'] = cbl * p1 ** 2 * mub ** 3 * math.exp(-2 * mub) / 2; o['b.1 second pass: 0.065 mu c_b P <= (at mu_n)'] = 2 * CM.C_CM * cbl * p1 * mub ** 2 * math.exp(-mub)
    o['b.1 second pass: E_CM formula - derived bound at mu_n (must be >= 0)'] = float(E_CM(mub, ell)) - (1 + 3.445 * math.exp(-mub / 2)) ** 2 * math.exp(o['b.1 second pass: mu b/2 <= (at mu_n)']) / (1 - o['b.1 second pass: 0.065 mu c_b P <= (at mu_n)'])
    o['c_G'] = C1 * math.sqrt(Bm) / G2s                                               # G > c_G sqrt(ell) sigma in Case II
    o['b.2: G/sigma at mu = ell + ln ell <='] = (4 / 3) * (1 + math.log(ell) / ell) * float(E_CM(ell + math.log(ell), ell))
    o['Th_min'] = vthw / (2 * math.sqrt(1 + math.log(ell) / ell)); ecm2 = float(E_CM(mu2, ell)); o['Tbar(mu_II) ell'] = tc * (4 / 3) * mu2 * math.exp(-mu2) * ecm2
    o['U_max'] = ((mT + o['Tbar(mu_II) ell'] / ell) / o['Th_min']) ** 2 - 1
    m1c = 1 - 2 * eta * 1e-3 - E0                                                     # after (b.4): k_E <= sqrt(r) <= 1e-3 (checked below)
    o['r bound coefficient'] = o['U_max'] ** 2 / (2 * (m1 / m2) ** 2)                 # u >= (m1/m2) sqrt2 sqrt(r) e^mu/E_CM  with the uniform m1 (before r is known small)
    rmax = o['r bound coefficient'] * ecm2 ** 2 * math.exp(-2 * mu2); o['b.4: r <= (at mu_II)'] = rmax; kEc = math.sqrt(rmax)
    m1c = 1 - eta * kE * 0 - 2.25 * eta * kEc - E0; m4c = 1 - 2 * kEc * (eta + 0.184) / om - E0; m5c = 1 - o['c_u'] * kEc - 2.1 * bII ** 2
    o['m4: m1, m4, m5 after (b.4) >='] = [m1c, m4c, m5c]; mprod = (m1c / m2) ** 3 * (m4c / m3) * m5c; o['m4: factor of K'] = mprod
    o['c_k'] = 0.999 * 2 * (1 - eta) / (16 * (1 + eta) * Gs) * m5c
    ej2 = float(E_J(mu2))
    o['b.5: u lower bound (kappa_b = kappa) at ell = 398, mu = 0.15 ell'] = (m1c / m2) * math.sqrt(2 * o['c_k'] / (math.e * 1.002)) * math.exp(0.15 * 398) / ((0.15 * 398) ** 0.75 * 398 ** 0.75 * ej2) * 0.999
    q4 = (8 * ell + 100) * (1 + eta) / (8 * (1 - eta) * ell ** 4); z4 = (8 * ell + 100) / (2 * ell ** 4); rho4 = math.sqrt(m1c / (m4c * ell ** 4 * (1 + 0.75 / ell ** 4) ** -2) + 1 / ell ** 4)
    o['eps1 ell^2'] = (1 - math.sqrt((1 - q4) * (1 - z4 / 2) * m2 * m3) * (1 - rho4 / 2) * (1 - rmax / 2)) * ell ** 2
    o['th1'] = (1 - eta) / (1 + eta) / Gs * (1 - o['eps1 ell^2'] / ell ** 2)
    bmax = 16 * cbl * mu2 ** 2 * math.exp(-2 * mu2) * ecm2 ** 2; o['kf (corner)'] = 1 - 6 * bmax - z4 / 12 - 1e-10
    o['beta-case: u^3 v lower bound at mu_II (must exceed U_max^4)'] = (m1c / m2) ** 3 * (m4c / m3) * (1 - 1e-10) * math.exp(min(4 * mu2, 700.0)) / (4 * math.e ** 2 * 256 * cbl * mu2 ** 3 * ej2 ** 4 * ecm2 ** 2)
    o['U_max^4'] = o['U_max'] ** 4
    muN = ell / 4 - 3.75; mF = 0.375 * math.log(ell) + 1; o['m_F'] = mF
    ecmN = float(E_CM(muN, ell)); ejN = float(E_J(muN)); o['Tbar_N ell'] = tc * (4 / 3) * muN * math.exp(-muN) * ecmN; TN = o['Tbar_N ell'] / ell
    o['Th_N'] = o['th1'] / math.sqrt(1 + 4 * mF / ell); UN = ((mT + TN) / o['Th_N']) ** 2 - 1; o['U_N'] = UN; o['a_N'] = o['Th_N'] * math.log1p(UN) / (2 * UN)
    o['k_N'] = mprod * o['kf (corner)'] * (1 - eta) / (2 * math.e * ejN ** 2 * ecmN ** 2 * Gs)
    o['C_N'] = 5 * (o['a_N'] ** 4 * o['k_N'] / 27) ** 0.2 * 4 ** 0.4 * (1 + 4 * mF / ell) ** -0.4
    o['dl_0'] = math.log(0.4 * o['C_N'] * ell ** 0.7) / 0.8
    o['a0'] = ell * (mT + TN - o['th1']); o['a0/th1'] = o['a0'] / o['th1']
    o['N: 2.5 + 2 dl_0 - a0/th1 (must be >= 0)'] = 2.5 + 2 * o['dl_0'] - o['a0/th1']
    # D <= 0 for dl >= 3.75 (mu <= mu_N): Th' >= th1 (1 - 15/ell)^{-1/2} there, and Tbar <= Tbar(mu_II); so D > 0 forces dl < 3.75, where Tbar <= Tbar_N and dl < a0/(2 th1)
    o['N0: th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II)) (must be >= 0)'] = o['th1'] / math.sqrt(1 - 15 / ell) - (mT + o['Tbar(mu_II) ell'] / ell)
    o['N0: 3.75 - a0/(2 th1) (must be >= 0)'] = 3.75 - o['a0/th1'] / 2
    o['F left'] = 16 * math.e ** 4 * o['k_N'] * o['th1'] ** 8; o['F right'] = (mT + o['Tbar(mu_II) ell'] / ell) ** 9 * (1 + 4 * mF / ell) ** 6
    o['F: left - right (must be >= 0)'] = o['F left'] - o['F right']
    return o


MUST = [k for k in consts(ELL1) if 'must be' in k]
MONO = {'Gam sqrt(ell)': 'down', 'Gam2 sqrt(ell)': 'down', 'X1/sqrt(ell)': 'down', 'k1_max': 'down', 'eps1_max': 'down', 'epsh_max': 'down', 'c_S': 'down', 'R4: constants/sigma <=': 'down',
        'th_bg': 'up', 'c1F': 'up', 'c_B2/sqrt(ell)': 'down', 'cb ell': 'down', 'tc': 'down', 'c_kap': 'up', 'cm/sqrt(ell)': 'down', 'c_u': 'down', 'vth0': 'up', 'x_n': 'up', 'c_J': 'up',
        'm3: log Ch(ell, mu_n)': 'up', 'x0': 'up', 'Th_min': 'up', 'U_max': 'down', 'c_k': 'up', 'th1': 'up', 'C_N': 'up', 'dl_0': 'up', 'F left': 'up', 'F right': 'down',
        'II-ch: chi/sqrt(ell) lower bound (kappa <= 1)': 'up', 'II-ch: chi/sqrt(ell) lower bound (kappa > 1)': 'up', 'II-ch: needed (c_B2 + Gam2)/sqrt(ell)': 'down',
        'II-s: hFz/(sqrt(ell) G) lower bound': 'up', 'm1: Y/(2 sigma)/(sqrt(ell) G) >=': 'up'}


# ------------------------------------------------------------------------------------------------ the rule, and the end-to-end check of the rule
def state_quantities(ell, Y, lP):
    """logs of the quantities of the proof at the states Y (n, 4) with the brightness lP."""
    Y = np.atleast_2d(np.asarray(Y, float)); lmu, lr, lB, lk = Y.T; eta = 1 / ell; fl = 1 / (1 + eta)
    Gs = math.sqrt(1 + C / ell); lG2 = math.log(Gs / (2 * (1 - eta))) - 0.5 * math.log(ell); lGam = math.log(Gs) - 0.5 * math.log(ell)
    U1 = 0.25 * math.sqrt(2 * ell + 3.1) + 1e-6; X1 = U1 / 0.75
    with np.errstate(all='ignore'):
        r = np.exp(lr); lb = lB - 2 * ell; b = np.exp(lb); lgs = 0.5 * (lr - np.log(2 + r)); lG = lP + lgs; kE = np.sqrt(r / (1 + r))
        Bi = np.exp(-lB); q = (8 * ell + 100) * (1 + eta) / (8 * (1 - eta)) * Bi; z2 = (8 * ell + 100) / 2 * Bi; om = (1 + 0.75 * Bi) ** -2
        la = np.log1p(-q) + math.log(fl) - math.log(4) - lmu - lr - np.log(2 + r); lbe = math.log(fl) + np.log1p(-z2 / 2) + lr - math.log(4) - np.log(2 + r)
        brk = 1 - 4 * b / (1 - b) - z2 / 12; kf = (1 - b) ** 2 * brk; lchi = np.where(brk > 0, math.log(fl) + np.log(np.where(kf > 0, kf, 1.0)) + lk - ell - math.log(16) - lb, -np.inf)
        k1 = 1 + (eta + 0.184) * kE; cm = 2 * X1 * np.sqrt(2 + r) / ((1 - eta) * fl * (1 - z2 / 2) * math.sqrt(2 * math.pi)); las = np.log(4 * cm ** 2) + 6 * math.log(ell) - 3 * ell - lr
    return {'lmu': lmu, 'lr': lr, 'lB': lB, 'lk': lk, 'lb': lb, 'b': b, 'r': r, 'lG': lG, 'lgs': lgs, 'kE': kE, 'q': q, 'z2': z2, 'om': om, 'lalpha': la, 'lbeta': lbe, 'lchi': lchi,
            'brk': brk, 'kf': kf, 'k1': k1, 'lG2': lG2, 'lGam': lGam, 'las': las, 'X1': X1, 'U1': U1, 'lP': lP}


def rule(ell, Q):
    """the regime of the RULE: 0 Case I / Fz, 1 Case I / Tz-B2, 2 Case II chirp (Tz-B2 for every a), 3 Case II otherwise (Tz-B2 below a_s, Tz-B1 from a_s)."""
    caseI = Q['lG'] <= math.log(C1) + 0.5 * Q['lb'] - Q['lG2']
    tzI = (Q['b'] < 0.1) & (Q['lk'] >= math.log(CT) + 0.5 * math.log(ell) + Q['lb'] + ell)
    ch = Q['lr'] <= math.log(CCH) + 0.5 * math.log(ell) - ell
    return np.where(caseI, np.where(tzI, 1, 0), np.where(ch, 2, 3))


def rule_lF(ell, Y, lP, arange='class'):
    """log F of the option-branch chosen by the RULE (the minimum over a of f of that option-branch; in regime 3 over the two pieces), and the regime."""
    Y = np.atleast_2d(np.asarray(Y, float)); Q = state_quantities(ell, Y, lP); reg = rule(ell, Q); n = len(Y); lF = np.full(n, np.inf)
    lo, hi = J.a_range(ell, Y[:, 1], arange)
    for g, opt in ((0, 'Fz'), (1, 'XB2'), (2, 'XB2')):
        m = reg == g
        if m.any(): lF[m] = J.lF_point(ell, Y[m], lP[m], opts=(opt,), arange=arange)[0]
    m = reg == 3
    if m.any():
        las = Q['las'][m]; lom, him = lo[m], hi[m]
        f1 = J.lF_point(ell, Y[m], lP[m], opts=('XB1',), arange=arange, ab=(np.maximum(las, lom), him))[0]
        f2 = np.full(m.sum(), np.inf); low = las > lom
        if low.any():
            idx = np.where(m)[0][low]
            f2[low] = J.lF_point(ell, Y[idx], lP[idx], opts=('XB2',), arange=arange, ab=(lom[low], las[low]))[0]
        lF[m] = np.minimum(f1, f2)
    return lF, reg


def check_rule(ells=(55.26, 82.89, 331.56, 955.8, 1e4, 1e6, 1e8), n=2500, seed=11):
    """END TO END: at random states of every family of the search (and P = Pbar e^q), the option-branch chosen by the RULE alone gives (F^2 - 1) ell >= 10 at every a
    (class range, and with the lower end of the a-range removed: the theorem is stated for a in (0, 4 r/sigma])."""
    out = {}
    for ell in ells:
        rng = np.random.default_rng(seed + int(ell) % 9973); F = S.families(ell, rng, n); Y5 = np.vstack(list(F.values())); sd = S.di_seeds(ell)
        if sd is not None: Y5 = np.vstack([Y5, sd, sd[:1] + rng.normal(size=(300, 5)) * np.array([0.03, 1.0, 1.0, 0.5, 0.0])])
        R = S.ranges(ell); Y5 = np.clip(Y5, R[:, 0], R[:, 1]); lP = S.lPbar(ell, Y5[:, 0], Y5[:, 2] - 2 * ell, Y5[:, 3]) + Y5[:, 4]; lc = 0.5 * math.log1p(C / ell); row = {'states': int(len(Y5))}
        for ar in ('class', 'low'):
            lF, reg = rule_lF(ell, Y5[:, :4], lP, ar); nan = int(np.isnan(lF).sum()); lF = np.where(np.isnan(lF), -np.inf, lF)
            lFs = J.lF_point(ell, Y5[:, :4], lP, arange=ar)[0]
            row[ar] = {'smallest log F of the rule per regime (I/Fz, I/Tz-B2, II chirp, II rest)': [float(lF[reg == g].min()) if (reg == g).any() else None for g in range(4)],
                       'states per regime': [int((reg == g).sum()) for g in range(4)], 'log F needed': lc, 'states below the claim': int((lF < lc).sum()), 'nan': nan,
                       'smallest (F^2 - 1) ell of the rule': float(J.margin(np.array([lF.min()]), ell)[0]), 'the same with the best option-branch at every a (the search)': float(J.margin(np.array([np.nanmin(lFs)]), ell)[0]),
                       'largest log(F_best/F_rule)': float(np.nanmax(np.where(np.isfinite(lFs - lF), lFs - lF, 0.0)))}
        out[str(ell)] = row; print(ell, json.dumps(row), flush=True)
    return out


# ------------------------------------------------------------------------------------------------ states for the checks
def sample(ell, rng, n, full=False):
    """states for the checks of the steps: the families of the search, and states built to lie in Case II (b lowered until G > c1 sqrt(b)/Gam2 at P = Pbar e^q):
    with r wide, r near c_ch sqrt(ell) sigma, narrow (8 <= xi < ell^2) and wide; kappa near its lower bounds of (c2)/(m3) and anywhere."""
    R = S.ranges(ell); F = S.families(ell, rng, n); Y5 = [np.vstack(list(F.values()))]; U = lambda a, b, k=n: rng.uniform(a, b, k); pick = lambda *xs: np.choose(rng.integers(0, len(xs), n), xs)
    lsg = -ell; line = 2 * math.log(ell) - ell
    for rep in range(4):
        lm = pick(np.log(np.maximum(ell / 4 - U(-6, 45), 0.5)), np.log(U(0.1 * ell, 0.6 * ell)), U(math.log(1e-3), math.log(12.0)), U(-2 * ell, math.log(1e-3)))
        lr = pick(U(R[1, 0], R[1, 1]), lsg + 0.5 * math.log(ell) + math.log(CCH) + U(-4, 4), line - 0.5 * lm - U(0, 2 * math.log(ell)), -ell / 2 + U(-15, 15), line - 0.5 * lm + U(0, 3))
        lk = pick(U(R[3, 0], R[3, 1]), U(-40, 5), U(0, 12), np.full(n, np.nan))
        lB = np.full(n, R[2, 0] + 10.0); q = pick(np.zeros(n), np.zeros(n), -U(0, 2))
        for it in range(3):                                                           # lower b until the state is in Case II; kappa (where nan) next to c_kap ell b/r
            lb = lB - 2 * ell; lkk = np.where(np.isnan(lk), math.log(4.94 * ell) + lb - lr + U(0, 4), lk)
            lP = S.lPbar(ell, lm, lb, lkk) + q; lG = lP + 0.5 * (lr - np.log(2 + np.exp(lr)))
            lG2 = math.log(math.sqrt(1 + C / ell) / (2 * (1 - 1 / ell))) - 0.5 * math.log(ell)
            lB = np.clip(2 * (lG + lG2 - math.log(C1)) - U(0.01, 6) + 2 * ell, R[2, 0], R[2, 1])
        lb = lB - 2 * ell; lkk = np.where(np.isnan(lk), math.log(4.94 * ell) + lb - lr + U(0, 4), lk)
        Y5.append(np.stack([lm, lr, lB, lkk, q], axis=1))
    sd = S.di_seeds(ell)                                                              # next to the worst states of the DI searches (the corner: u, v small)
    if sd is not None:
        Y5.append(np.vstack([y[None, :] + rng.normal(size=(n // 4, 5)) * np.array([0.5 / max(ell / 4, 4.0), 1.0, 1.0, 1.0, 0.0]) for y in sd]))
        Z = sd[0][None, :] + rng.normal(size=(n, 5)) * np.array([0.5 / max(ell / 4, 4.0), 3.0, 3.0, 0.0, 0.0])                # kappa around 16 b e^mu/mu (the beta-case of (b.6))
        Z[:, 3] = math.log(16) + Z[:, 2] - 2 * ell + np.exp(Z[:, 0]) - Z[:, 0] + rng.uniform(-6, 6, n); Y5.append(Z)
    Y5 = np.clip(np.vstack(Y5), R[:, 0], R[:, 1]); lP = S.lPbar(ell, Y5[:, 0], Y5[:, 2] - 2 * ell, Y5[:, 3]) + Y5[:, 4]
    return (Y5[:, :4], lP, Y5) if full else (Y5[:, :4], lP)


def _lines_on(ell, Y, lP, lA):
    """the value of every line on the grid lA (n, g): tag -> (sign, log|value| (n, g))."""
    T, aux = J.coeffs(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3], lP, gam=math.sqrt(1 + C / ell)); g = J._gt(lA, ell)
    return {tag: (s, L[:, None] + g[:, :, J.TY[t]]) for tag, (t, s, L) in T.items()}, aux


def _sum(V, tags):
    xs = [V[t][1] for t in tags]; m = np.max(xs, axis=0); m0 = np.where(np.isfinite(m), m, 0.0)
    with np.errstate(all='ignore'): return m0 + np.log(np.sum([np.exp(x - m0) for x in xs], axis=0))


def check_remainders(ell, rng, n=1500, wrong=None):
    """(R): every bound of the remainder lines at random states and on a grid of a (class range, and down to a_s where the bound is stated from a_s); and the
    summary: the full sum of the chosen option-branch against the reduced expression of the proof.  Returns the largest (ratio/bound) per item (must be <= 1) --
    with wrong = a factor < 1 the bounds are multiplied by it (the power check: the sharp ones must then fail)."""
    Y, lP = sample(ell, rng, n); Q = state_quantities(ell, Y, lP); reg = rule(ell, Q); o = consts(ell); f = 1.0 if wrong is None else wrong
    lo, hi = J.a_range(ell, Y[:, 1]); g = 40
    lA = lo[:, None] + (hi - lo)[:, None] * np.linspace(0, 1, g)[None, :]
    lA = np.concatenate([lA, np.clip(Q['las'][:, None] + np.array([0.0, 0.5, 3.0])[None, :], lo[:, None], hi[:, None]), np.clip(0.5 * Q['lb'][:, None] + np.array([-1.0, 0.0, 1.0])[None, :], lo[:, None], hi[:, None]),
                         np.clip((Q['lr'] + 0.5 * Q['lmu'])[:, None] + np.array([-1.0, 0.0, 1.0])[None, :], lo[:, None], hi[:, None]), np.full((len(Y), 1), -ell).clip(lo[:, None], hi[:, None])], axis=1)
    V, aux = _lines_on(ell, Y, lP, lA); r = Q['r']; kE = Q['kE']; eta = 1 / ell; res = {}
    def rec(name, lratio, lbound, mask=None):
        """largest ratio/bound over the masked states and the grid."""
        with np.errstate(all='ignore'): d = lratio - (lbound + math.log(f))
        d = np.where(np.isnan(d), -np.inf, d)
        if mask is not None: d = np.where(mask if mask.ndim == 2 else mask[:, None], d, -np.inf)
        mx = float(np.max(d)); res[name] = float('inf') if mx == float('inf') else (float(np.exp(min(mx, 700.0))) if np.isfinite(mx) else 0.0)   # +inf (a bound that is 0 where the line is not) is reported as such
    one = np.zeros((len(Y), 1))
    lkE = 0.5 * (Q['lr'] - np.log1p(r)); leps1 = math.log(eta) + lkE + np.log((2 + r) / (1 + r)); lepsh = math.log(2 * (eta + 0.184)) + lkE - np.log(Q['om'])   # in log form: r = e^{lr} underflows for large ell
    eps1 = np.exp(leps1); epsh = np.exp(lepsh)
    with np.errstate(all='ignore'):
        rec('R1: N1/P1 against eps1(r)', V['N1'][1] - V['P1'][1], leps1[:, None])
        rec('R1: (N2 + d3 + N4 + ring2 + A2a + A2b + B2b)/P1 against es', _sum(V, ('N2', 'd3', 'N4', 'ring2', 'A2a', 'A2b', 'B2b')) - V['P1'][1], math.log(ES) + one)
        les = 2 * math.log(ell) - ell                                                             # log es_sigma (ESS itself underflows for large ell)
        rec('R1: (d4 + N4G)/P2z against es_sigma', _sum(V, ('d4', 'N4G')) - V['P2z'][1], les + one)
        rec('R1: B1l/P2z against es_sigma (Case II)', V['B1l'][1] - V['P2z'][1], les + one, reg >= 2)
        rec('R2: hneg1/P4z against eps_h(r)', V['hneg1'][1] - V['P4z'][1], lepsh[:, None])
        rec('R3: (A1w + B1w1 + B1w2)/(P1 + P4z) against es', _sum(V, ('A1w', 'B1w1', 'B1w2')) - _sum(V, ('P1', 'P4z')), math.log(ES) + one)
        rec('R4: (N3 + M0Xi + A1v + pair)/sigma against 1.77', _sum(V, ('N3', 'M0Xi', 'A1v', 'pair')) + ell, math.log(o['R4: constants/sigma <=']) + one)
        bg = _sum(V, ('P1', 'P4z')); rec('R4: (N3 + M0Xi + A1v + pair)/(e0 - es)(P1 + P4z) (the constants inside the background lines)', _sum(V, ('N3', 'M0Xi', 'A1v', 'pair')) - bg,
                                           math.log((E0 - ES) * (1 - o['eps1_max'] - o['epsh_max'])) + one)
        rec('R5: (FzK + A2k + B2a)/sqrt(b) against 1.01e-3 (regime I/Fz)', _sum(V, ('FzK', 'A2k', 'B2a')) - 0.5 * Q['lb'][:, None], math.log(1.01e-3) + one, reg == 0)
        rec('R6: (B2c + B2s)/G against c_B2', _sum(V, ('B2c', 'B2s')) - Q['lG'][:, None], math.log(o['c_B2/sqrt(ell)'] * math.sqrt(ell)) + one)
        rec('R6: (A2k + B2a)/cKz against 0.0461 + 1e-6 (regime I/Tz-B2)', _sum(V, ('A2k', 'B2a')) - V['cKz'][1], math.log(o['Case I (Tz-B2): A2k/cKz <='] + 1e-6) + one, reg == 1)
        rec('R6: (A2k + B2a)/cKz against 1e-3 (Case II)', _sum(V, ('A2k', 'B2a')) - V['cKz'][1], math.log(1e-3) + one, reg >= 2)
        ge = lA >= Q['las'][:, None] - 1e-12; m3 = (reg == 3)[:, None] & ge
        rec('R7: B1m/(ell^-3 hFz + es_sigma P2z) (regime 3, a >= a_s)', V['B1m'][1] - np.logaddexp(-3 * math.log(ell) + V['hFz'][1], les + V['P2z'][1]), one, m3)
        rec('R7: B1c/(es_sigma Gam2 G) (Case II)', V['B1c'][1] - (les + Q['lG2'] + Q['lG'])[:, None], one, reg >= 2)
        rec('R7: (uB2c + uB2s + A2k + B2a)/cKz against c_u sqrt(r) + 2.1 b^2 (regime 3)', _sum(V, ('uB2c', 'uB2s', 'A2k', 'B2a')) - V['cKz'][1], np.logaddexp(math.log(o['c_u']) + 0.5 * Q['lr'], math.log(2.1) + 2 * Q['lb'])[:, None], reg == 3)
        # the summary: full sum of the chosen option-branch >= the reduced expression (per regime), on the grid
        def full(opt):
            pos = _sum(V, [t for t in J.SHARED + J.OPT[opt] if V[t][0] > 0]); neg = _sum(V, [t for t in J.SHARED + J.OPT[opt] if V[t][0] < 0]); return pos, neg
        m1 = 1 - eps1 - E0; m4 = 1 - epsh - E0; lG2G = (Q['lG2'] + Q['lG'])[:, None]; d1 = V['d1'][1]
        bgm = np.logaddexp(np.log(m1)[:, None] + V['P1'][1], np.log(m4)[:, None] + V['P4z'][1])
        # regime 0: full(Fz) >= bgm - d1 - Gam2 G - 1.01e-3 sqrt(b):  i.e.  pos + [d1 + Gam2 G + 1.01e-3 sqrt b] >= neg + bgm
        p, ng = full('Fz'); lhs = np.logaddexp(p, np.logaddexp(np.logaddexp(d1, lG2G), math.log(1.01e-3 * f) + 0.5 * Q['lb'][:, None])); rhs = np.logaddexp(ng, bgm)
        rec('summary, regime I/Fz: (remainders + reduced)/(positive + allowed)', rhs - lhs, one, reg == 0)
        # regime 2 (and 1): full(TzB2) >= bgm - d1 + (1 - 1e-3) cKz - c_B2 G - Gam2 G (1 + es)
        p, ng = full('XB2'); allow = np.logaddexp(np.logaddexp(d1, lG2G + math.log1p(ESS(ell))), math.log(o['c_B2/sqrt(ell)'] * math.sqrt(ell)) + Q['lG'][:, None])
        red = np.logaddexp(bgm, math.log1p(-1e-3 * f) + V['cKz'][1])
        rec('summary, regime II chirp: (remainders + reduced)/(positive + allowed)', np.logaddexp(ng, red) - np.logaddexp(p, allow), one, reg == 2)
        red1 = np.logaddexp(bgm, math.log1p(-(o['Case I (Tz-B2): A2k/cKz <='] + 1e-6) * f) + V['cKz'][1])
        rec('summary, regime I/Tz-B2: (remainders + reduced)/(positive + allowed)', np.logaddexp(ng, red1) - np.logaddexp(p, allow), one, reg == 1)
        # regime 3, a >= a_s: full(TzB1) >= m1 P1 + m2 P2z + m4 P4z + m3 hFz + m5 cKz - d1 - mT Gam2 G
        p, ng = full('XB1'); m5 = 1 - (o['c_u'] * np.sqrt(r) + 2.1 * Q['b'] ** 2) * f
        red3 = np.logaddexp.reduce([bgm, math.log1p(-3 * ESS(ell) * f) + V['P2z'][1], math.log1p(-ell ** -3 * f) + V['hFz'][1], np.log(np.maximum(m5, 1e-300))[:, None] + V['cKz'][1]])
        rec('summary, regime II rest, a >= a_s: (remainders + reduced)/(positive + allowed)', np.logaddexp(ng, red3) - np.logaddexp(p, np.logaddexp(d1, lG2G + math.log1p(ESS(ell)))), one, m3)
    res['states per regime (I/Fz, I/Tz-B2, II chirp, II rest)'] = [int((reg == k).sum()) for k in range(4)]
    return res


def check_outside(ell, rng, n=800):
    """POWER of the remainder bounds: OUTSIDE the region where each is stated, the bound must fail (largest ratio/bound > 1).
    (R4) the constants inside the background lines, with the lower end of b removed (B in [1e4, 2.5e10 e^-3]);
    (R6) B2c + B2s <= c_B2 G above the upper end of the a-range (a = e^2 * 4 r/sigma);
    (R7) B1m <= ell^-3 hFz + es_sigma P2z below a_s (a = a_s e^-3)."""
    Y, lP, Y5 = sample(ell, rng, n, full=True); o = consts(ell); out = {}; les = 2 * math.log(ell) - ell
    def mx(d, mask=None):
        d = np.where(np.isnan(d), -np.inf, d)
        if mask is not None: d = np.where(mask[:, None], d, -np.inf)
        m = float(np.max(d)); return float('inf') if m == float('inf') else (float(np.exp(min(m, 700.0))) if np.isfinite(m) else 0.0)
    with np.errstate(all='ignore'):
        Yb = Y.copy(); Yb[:, 2] = rng.uniform(math.log(1e4), math.log(2.5e10) - 3, len(Y)); lb = Yb[:, 2] - 2 * ell; lPb = S.lPbar(ell, Yb[:, 0], lb, Yb[:, 3]) + Y5[:, 4]
        lA = (0.5 * lb)[:, None] + np.linspace(-3, 3, 13)[None, :]; V, aux = _lines_on(ell, Yb, lPb, lA)
        out['R4 with B in [1e4, 2.5e10 e^-3]: (N3 + M0Xi + A1v + pair)/(e0 - es)(P1 + P4z)'] = mx(_sum(V, ('N3', 'M0Xi', 'A1v', 'pair')) - _sum(V, ('P1', 'P4z')) - math.log((E0 - ES) * (1 - o['eps1_max'] - o['epsh_max'])))
        Q = state_quantities(ell, Y, lP); reg = rule(ell, Q); lo, hi = J.a_range(ell, Y[:, 1])
        V, aux = _lines_on(ell, Y, lP, (hi + 2.0)[:, None])
        out['R6 at a = e^2 * 4 r/sigma: (B2c + B2s)/(c_B2 G)'] = mx(_sum(V, ('B2c', 'B2s')) - Q['lG'][:, None] - math.log(o['c_B2/sqrt(ell)'] * math.sqrt(ell)))
        V, aux = _lines_on(ell, Y, lP, (Q['las'] - 3.0)[:, None])
        out['R7 at a = a_s e^-3: B1m/(ell^-3 hFz + es_sigma P2z) (regime 3)'] = mx(V['B1m'][1] - np.logaddexp(-3 * math.log(ell) + V['hFz'][1], les + V['P2z'][1]), reg == 3)
    out['every bound fails outside its region'] = bool(all(v > 1 + 1e-6 for v in out.values()))
    return out


def check_steps(ell, rng, n=1500, wrong=None):
    """the steps (F), (c), (II-ch), (II-s), (m1)-(m4) at random states (P = Pbar e^q <= Pbar, the finite subset of (H')).  Per item: the smallest slack (must be
    >= 0; reported as a difference of logarithms or of the two sides divided by the right side) and the number of states it was checked on.
    wrong: 'ckap2' (c_kap doubled), 'cJ2' (c_J doubled), 'w16' (w16 * 0.8), 'EJ' (E_J := 1), 'ECM' (E_CM := 1), 'phi' (rhobar := 0 in (m2)): wrong versions."""
    Y, lP = sample(ell, rng, n); Q = state_quantities(ell, Y, lP); reg = rule(ell, Q); o = consts(ell); eta = 1 / ell; fl = 1 / (1 + eta); res = {}; cnt = {}
    mu = np.exp(Q['lmu']); r = Q['r']; b = Q['b']; lk = Q['lk']; P = np.exp(lP); G2s = o['Gam2 sqrt(ell)']
    nbad = {}
    def rec(name, slack, mask):
        slack = np.where(np.isposinf(slack), 1e300, slack); bad = mask & ~np.isfinite(slack); mask = mask & np.isfinite(slack)      # +inf is a pass; nan or -inf is counted (must not occur)
        if bad.any(): nbad[name] = int(bad.sum())
        cnt[name] = int(mask.sum()); res[name] = float(np.min(slack[mask])) if mask.any() else None
    II = reg >= 2; w16 = o['w16'] * (0.8 if wrong == 'w16' else 1.0); ckap = o['c_kap'] * (2.0 if wrong == 'ckap2' else 1.0); cJ = o['c_J'] * (2.0 if wrong == 'cJ2' else 1.0)
    ej = E_J(mu) if wrong != 'EJ' else np.ones_like(mu); ecm = E_CM(mu, ell) if wrong != 'ECM' else np.ones_like(mu)
    with np.errstate(all='ignore'):
        rec('F1: log(0.7008/P)', math.log(o['F1: P <=']) - lP, np.ones(len(Y), bool))
        lkb = np.maximum(lk, math.log(16) + Q['lb']); rec('F2: log(w16 sqrt(kappa_b)/P), kappa_b = max(kappa, 16 b) <= 1', math.log(w16) + 0.5 * lkb - lP, lkb <= 0)
        lkb4 = np.maximum(lk, math.log(16) + Q['lb'] + mu - Q['lmu'])
        rec('F4: log(4 mu e^-mu sqrt(e mu kappa_b) E_J/P), kappa_b = max(kappa, 16 b e^mu/mu) <= 1/mu, mu >= 6', math.log(4) + Q['lmu'] - mu + 0.5 * (1 + Q['lmu'] + lkb4) + np.log(ej) - lP, (mu >= 6) & (lkb4 + Q['lmu'] <= 0))
        rec('b.1: log(4 mu e^-mu E_CM/P) in Case II, mu > mu_n', math.log(4) + Q['lmu'] - mu + np.log(ecm) - lP, II & (mu > o['mu_n']))
        rec('c1: log(cb P^2/b) in Case II', math.log(o['cb ell'] / ell) + 2 * lP - Q['lb'], II)
        rec('c1: log(P_II/P) in Case II', math.log(o['P_II']) - lP, II)
        T = np.exp(Q['lb'] + np.log(Q['k1']) - Q['lG'] + math.log(2 * (1 - eta))); rec('c1: T_max/ell - T in Case II', o['T_max ell'] / ell - T, II)
        rec('c2: log(kappa r/(c_kap ell b)) in Case II, kappa <= 1', lk + Q['lr'] - math.log(ckap * ell) - Q['lb'], II & (lk <= 0))
        rec('c3: log(chi r 8 Gam2^2 P_II^2/(fl kf c1^2 sigma)) in Case II, kappa > 1', Q['lchi'] + Q['lr'] + math.log(8 * G2s ** 2 / ell * o['P_II'] ** 2 / (fl * C1 ** 2)) - np.log(Q['kf']) + ell, II & (lk > 0))
        rec('b.2: log((ell + ln ell)/mu) in Case II', math.log(ell + math.log(ell)) - Q['lmu'], II)
        lrhs = math.log(o['c_B2/sqrt(ell)'] * math.sqrt(ell) + G2s / math.sqrt(ell) * (1 + ESS(ell)))
        rec('II-ch: log(chi (1 - 1e-3)/(c_B2 + Gam2)), regime II chirp', Q['lchi'] + math.log1p(-1e-3) - lrhs, reg == 2)
        rec('II-s: log(beta/(sigma (1 + 1e-9) (c_B2 + Gam2))), regime II rest', Q['lbeta'] + ell - math.log1p(1e-9) - lrhs, reg == 3)
        rec('II-s: log(1e-9 sigma/a_s), regime II rest', math.log(1e-9) - ell - Q['las'], reg == 3)
        # ---- (II-m): the reduced five lines
        m3r = reg == 3; eps1 = eta * Q['kE'] * (2 + r) / (1 + r); epsh = 2 * Q['kE'] * (eta + 0.184) / Q['om']; m1 = 1 - eps1 - E0; m4 = 1 - epsh - E0; m2 = 1 - 3 * ESS(ell); m3 = 1 - ell ** -3
        m5 = 1 - o['c_u'] * np.sqrt(r) - 2.1 * b ** 2; mT = 1 + ESS(ell)
        lu = np.log(m1 / (2 * m2)) - Q['lalpha'] - Q['lG']; lv = np.log(m4 * Q['om'] / (2 * m3)) + Q['lb'] - Q['lbeta'] - Q['lG']
        lTh = math.log(2) + 0.5 * (math.log(m2 * m3) + Q['lalpha'] + Q['lbeta']) - Q['lG2']; lch = np.log(np.maximum(m5, 1e-300)) + Q['lchi'] - Q['lG2']
        lxi = Q['lr'] + 0.5 * Q['lmu'] + ell + 0.5 * (math.log(m3 / m2) + np.log1p(-Q['z2'] / 2) - np.log1p(-Q['q']))
        rhob = np.sqrt(m1 / (m4 * Q['om']) * np.exp(-Q['lB']) + np.exp(-2 * lxi)); tgt = mT + T
        rec('m: log(Th*/(vth0 sqrt(ell/(4 mu)))), regime II rest', lTh - math.log(o['vth0']) - 0.5 * (math.log(ell / 4) - Q['lmu']), m3r)
        s1 = m3r & (lxi < math.log(XI1))
        rec('m1: log(m3 beta/(2 sigma Gam2 (mT + T)))', math.log(m3 / 2) + Q['lbeta'] + ell - Q['lG2'] - np.log(tgt), s1)
        rec('m1: log(Th*/(sqrt2 (mT + T)))', lTh - 0.5 * math.log(2) - np.log(tgt), s1)
        Thp = np.exp(np.minimum(lTh, 700.0)) * (1 - (0.0 if wrong == 'phi' else rhob) / 2); s2 = m3r & (lxi >= math.log(XI1)) & (Thp >= tgt)
        # (m2): the true minimum over a of X a + Y/(a + sigma) (closed form) against Gam2 G (mT + T):  log of the ratio
        lX = np.logaddexp(np.log(m1 / 2), math.log(m2) + Q['lalpha'] + Q['lG']); lY = np.logaddexp(np.log(m4 * Q['om'] / 2) + Q['lb'], math.log(m3) + Q['lbeta'] + Q['lG'])
        rho = np.exp(np.minimum(-ell + 0.5 * (lX - lY), 50.0)); lmin = np.where(rho <= 1, 0.5 * (lX + lY) + np.log(np.maximum(2 - rho, 1e-300)), lY + ell)
        rec('m2: log(min_a [X a + Y/(a + sigma)]/(Gam2 G (mT + T))) where Th\' >= mT + T', lmin - Q['lG2'] - Q['lG'] - np.log(tgt), s2)
        rec('m2: rhobar - rho (rho <= rhobar)', rhob - rho, m3r & (lxi >= math.log(XI1)))
        rb = 0.0 if wrong == 'phi' else rhob
        rec('m2: log(min_a [X a + Y/(a + sigma)]/(Gam2 G Th* (1 - rhobar/2) sqrt((1 + u)(1 + v)))) for xi >= 8', lmin - Q['lG2'] - Q['lG'] - lTh - np.log(1 - rb / 2) - 0.5 * (np.logaddexp(0, lu) + np.logaddexp(0, lv)), m3r & (lxi >= math.log(XI1)))
        s3 = m3r & (lxi >= math.log(XI1)) & (lxi < 2 * math.log(ell)) & (Thp < tgt)
        rec('m3: mu - mu_n (narrow, Th\' < mT + T)', mu - o['mu_n'], s3)
        lchilo = math.log(fl * cJ / 16) + np.log(Q['kf']) + math.log(ell) - ell + 2 * mu - 3 * Q['lmu'] - 2 * np.log(ej) - Q['lr']
        rec('m3: log(chi/(fl kf c_J ell sigma e^{2 mu}/(16 mu^3 E_J^2 r))) in Case II, mu > mu_n', Q['lchi'] - lchilo, II & (mu > o['mu_n']))
        rec('m3: log(ch/(mT + T)) (narrow, Th\' < mT + T)', lch - np.log(tgt), s3)
        s4 = m3r & (lxi >= 2 * math.log(ell)) & (Thp < tgt)
        rec('m4: mu - mu_II (wide, Th\' < mT + T)', mu - o['mu_II'], s4)
        u = np.exp(np.minimum(lu, 700.0)); v = np.exp(np.minimum(lv, 700.0)); ch = np.exp(np.minimum(lch, 700.0))
        rec('m4: Th\' sqrt((1 + u)(1 + v)) + ch - (mT + T) (wide, Th\' < mT + T): the claim (*)', Thp * np.sqrt((1 + u) * (1 + v)) + ch - tgt, s4)
        Tb = o['tc'] * (4 / 3) * mu * np.exp(-mu) * ecm / ell; U = ((mT + Tb) / Thp) ** 2 - 1; s5 = s4 & (u < U) & (v < U)
        rec('m4: 18.7 E_CM^2 e^{-2 mu} - r where u, v < U', o['r bound coefficient'] * ecm ** 2 * np.exp(-2 * mu) - r, s5)
        s6 = s5 & (Q['lB'] >= 4 * math.log(ell))
        lK = math.log(o['m4: factor of K']) + np.log(Q['kf'] * Q['om']) + math.log((1 - eta) / (2 * math.e * math.sqrt(1 + C / ell))) + 0.5 * math.log(ell) - 4 * (ell / 4 - mu) - 2 * Q['lmu'] - 2 * np.log(ej) - 2 * np.log(ecm)
        rec('m4: log(u^3 v ch/K) where u, v < U and B >= ell^4', 3 * lu + lv + lch - lK, s6)
        dl = ell / 4 - mu; rec('m4: Th\' - th1 (1 - 4 dl/ell)^{-1/2} where u, v < U and B >= ell^4', Thp - o['th1'] / np.sqrt(np.maximum(1 - 4 * dl / ell, 1e-9)), s6)
        # the product inequality and the bound of Th' on every wide Case II state with mu > mu_II, B >= ell^4 and r below the bound of (b.4) (not only where u, v < U)
        sw = m3r & (lxi >= 2 * math.log(ell)) & (mu > o['mu_II']) & (Q['lB'] >= 4 * math.log(ell)) & (r <= o['r bound coefficient'] * ecm ** 2 * np.exp(-2 * mu)); lk0 = math.log(16) + Q['lb'] + mu - Q['lmu']
        rec('m4 (alpha-case): log(u^3 v ch/K) on wide states with mu > mu_II, B >= ell^4, r <= 18.7 E_CM^2 e^{-2 mu}, kappa >= 16 b e^mu/mu', 3 * lu + lv + lch - lK, sw & (lk >= lk0))
        lbeta = math.log(o['m4: factor of K'] / (4 * math.e ** 2 * 256 * o['cb ell'] / ell)) + np.log(Q['om']) + 4 * mu - 3 * Q['lmu'] - 4 * np.log(ej) - 2 * np.log(ecm)
        rec('m4 (beta-case): log(u^3 v/(omega e^{4 mu}/(4 e^2 256 cb mu^3 E_J^4 E_CM^2))) on the same states with kappa < 16 b e^mu/mu', 3 * lu + lv - lbeta, sw & (lk < lk0))
        rec('m4: Th\' - th1 (1 - 4 dl/ell)^{-1/2} on the same states', Thp - o['th1'] / np.sqrt(np.maximum(1 - 4 * dl / ell, 1e-9)), sw)
    return {'smallest slack of every step (must be >= 0)': res, 'states checked per step': cnt, 'states per regime (I/Fz, I/Tz-B2, II chirp, II rest)': [int((reg == k).sum()) for k in range(4)],
            'states where a slack is nan or -inf, per step (must be empty)': nbad,
            'ok': bool(all(v is None or v >= -(1e-9 + 1e-13 * ell) for v in res.values()) and not nbad)}        # rounding of logarithms of size ell


def check_consts():
    """every condition of the proof ('must be') at 55.26 and on a grid of ell up to 1e12; the monotone directions (MONO) on the grid."""
    o = consts(ELL1); grid = [ELL1 * (1e12 / ELL1) ** (i / 400) for i in range(401)]; G = [consts(e) for e in grid]; mono = {}
    for k, d in MONO.items():
        v = np.array([g[k] for g in G]); dv = np.diff(v); mono[k] = bool(np.all(dv <= 1e-12 * np.abs(v[:-1])) if d == 'down' else np.all(dv >= -1e-12 * np.abs(v[:-1])))
    must = {k: {'at 55.26': o[k], 'smallest on the grid': float(min(g[k] for g in G)), 'largest on the grid': float(max(g[k] for g in G))} for k in MUST}
    def okm(k, v): return v['largest on the grid'] <= 1 if '<= 1' in k else v['smallest on the grid'] >= 0
    assert consts(ELL1)['b.1 first pass: P/(mu e^-mu) <='] <= 4 * 2.25 * 1.02
    quoted = []
    def q(name, val, bound, sense): quoted.append({'quantity': name, 'value at 55.26': val, 'quoted': sense + ' ' + repr(bound), 'ok': bool(val <= bound if sense == '<=' else val >= bound)})
    q('F1: P', o['F1: P <='], 0.7008, '<='); q('w16', o['w16'], 0.8972, '<='); q('eps1_max', o['eps1_max'], 0.01457, '<='); q('epsh_max', o['epsh_max'], 0.1808, '<='); q('c_S', o['c_S'], 0.155, '<=')
    q('R4: constants/sigma', o['R4: constants/sigma <='], 1.77, '<='); q('R4: e0 needed', o['R4: e0 needed'], E0, '<='); q('th_bg', o['th_bg'], 0.8985, '>='); q('c1F', o['c1F'], 0.7857, '>=')
    q('R5: K_F/sqrt(b)', o['R5: K_F/sqrt(b) <='], 1.01e-3, '<='); q('c_s', o['c_s'], 0.102, '<='); q('c_B2/sqrt(ell)', o['c_B2/sqrt(ell)'], 0.0896, '<='); q('kf (b < 0.1)', o['kf (b < 0.1)'], 0.4493, '>=')
    q('cK', o['cK'], 0.02758, '>='); q('Case I (Tz-B2): A2k/cKz', o['Case I (Tz-B2): A2k/cKz <='], 0.0463, '<='); q('cb ell', o['cb ell'], 0.05593, '<='); q('P_II', o['P_II'], 0.5223, '<=')
    q('b_II ell', o['b_II ell'], 0.01526, '<='); q('brk (Case II)', o['brk (Case II)'], 0.998, '>='); q('kf (Case II)', o['kf (Case II)'], 0.9975, '>='); q('tc', o['tc'], 1.0779, '<=')
    q('T_max ell', o['T_max ell'], 0.1877, '<='); q('c_kap', o['c_kap'], 4.935, '>='); q('c_u', o['c_u'], 0.48, '<='); q('vth0', o['vth0'], 0.7855, '>='); q('m1: mu ell', o['m1: mu ell <'], 7.7, '<=')
    q('rhobar (xi >= 8)', o['rhobar (xi >= 8)'], 0.12501, '<='); q('x_n', o['x_n'], 0.1346, '>='); q('mu_n', o['mu_n'], 7.43, '>='); q('c_J', o['c_J'], 0.0913, '>='); q('m3: Ch(ell, mu_n)', math.exp(o['m3: log Ch(ell, mu_n)']), 13.0, '>=')
    q('x0', o['x0'], 0.1531, '>='); q('mu_II', o['mu_II'], 8.46, '>='); q('b.4: r bound coefficient', o['r bound coefficient'], 18.7, '<='); q('m4: factor of K', o['m4: factor of K'], 0.997, '>=')
    q('eps1 ell^2', o['eps1 ell^2'], 0.76, '<='); q('U_max', o['U_max'], 5.96, '<='); q('b.2: G/sigma at mu = ell + ln ell', o['b.2: G/sigma at mu = ell + ln ell <='], 1.5, '<='); q('c_G', o['c_G'], 2.2e5, '>=')
    q('(N) slack', o['N: 2.5 + 2 dl_0 - a0/th1 (must be >= 0)'], 0.58, '>='); q('b.5: u lower bound', o['b.5: u lower bound (kappa_b = kappa) at ell = 398, mu = 0.15 ell'], 6.0, '>=')
    q('beta-case: u^3 v lower bound / U_max^4', o['beta-case: u^3 v lower bound at mu_II (must exceed U_max^4)'] / o['U_max^4'], 1.0, '>=')
    q('m4: sqrt(r) after (b.4)', math.sqrt(o['b.4: r <= (at mu_II)']), 1e-3, '<=')
    return {'conditions of the proof (must hold at every ell of the grid)': must, 'all conditions hold on the grid': bool(all(okm(k, v) for k, v in must.items())),
            'quoted numbers': quoted, 'all quoted numbers hold at 55.26': bool(all(r['ok'] for r in quoted)),
            'monotone in ell on the grid 55.26 ... 1e12 (401 points)': mono, 'all monotone': bool(all(mono.values())),
            'smallest (N) on the grid': float(min(g['N: 2.5 + 2 dl_0 - a0/th1 (must be >= 0)'] for g in G)), 'smallest (F) left - right on the grid': float(min(g['F: left - right (must be >= 0)'] for g in G)),
            'largest a0/(2 th1) on the grid (must be <= 3.75)': float(max(g['a0/th1'] for g in G) / 2),
            'smallest beta-case bound / U_max^4 on the grid': float(min(g['beta-case: u^3 v lower bound at mu_II (must exceed U_max^4)'] / g['U_max^4'] for g in G)), 'constants at 55.26': o}


def check_AG_direct(ells=(55.26, 60.0, 82.89, 165.78, 331.56, 955.8, 3000.0, 1e4, 1e5, 1e6, 1e8), n=4001):
    """(AG) of (m4) with the bounds of the proof on a grid of dl in (ell/4 - ell - ln ell, a0/(2 th1)), per ell: the smallest 5 (a^4 K/27)^{1/5} - D (must be >= 0
    wherever D > 0), with Th' = th1 (1 - 4 dl/ell)^{-1/2}, D = mT + Tbar - Th', U = ((mT + Tbar)/Th')^2 - 1, a = Th' ln(1 + U)/(2U), K with the factor of (m4)."""
    out = {}
    for ell in ells:
        o = consts(ell); eta = 1 / ell; top = o['a0/th1'] / 2 + 0.5; lo = ell / 4 - ell - math.log(ell); mid = max(lo, -(o['m_F'] + 10)); mT = 1 + ESS(ell)
        dl = np.concatenate([np.linspace(mid, top, n), mid - np.geomspace(1e-3, max(mid - lo, 2e-3), n // 2)]); mu = ell / 4 - dl; ok = mu >= o['mu_II']
        with np.errstate(all='ignore'):
            ecm = E_CM(mu, ell); ej = E_J(mu); Tb = o['tc'] * (4 / 3) * mu * np.exp(-mu) * ecm / ell; Th = o['th1'] / np.sqrt(1 - 4 * dl / ell); D = mT + Tb - Th
            U = ((mT + Tb) / Th) ** 2 - 1; a = Th * np.log1p(U) / (2 * U)
            lK = np.log(o['m4: factor of K'] * o['kf (corner)'] * (1 - eta) * math.sqrt(ell) / (2 * math.e * math.sqrt(1 + C / ell))) - 4 * dl - 2 * np.log(mu) - 2 * np.log(ej) - 2 * np.log(ecm)
            lhs = 5 * np.exp((4 * np.log(a) + lK - math.log(27)) / 5)
            alt = lK - 4 * np.log(np.maximum(U, 1e-300)) - np.log(mT + Tb)
            g = np.where(D > 0, np.maximum(lhs - D, np.where(alt >= 0, 0.0, -np.inf)), np.inf)
        g = np.where(ok, g, np.inf); i = int(np.argmin(g))
        out[str(ell)] = {'smallest [5 (a^4 K/27)^{1/5} - D] ell where D > 0 (or K >= (mT + Tbar) U^4)': float(g[i] * ell), 'at dl': float(dl[i]), 'points with D > 0': int(np.sum(ok & (D > 0)))}
    return out


def check_60():
    """60 digits: the algebra of the new steps.  (a) Th*/(2 xi) = sigma m2 alpha/Gam2;  (b) u^3 v ch = (m1/m2)^3 (m4/m3) m5 b omega chi/(16 alpha^3 beta G^4 Gam2);
    (c) at kappa = c_kap ell b/r:  (r/2) w^2 kappa = c1^2 b/Gam2^2;  (d) at kappa = c_J ell b e^{2 mu}/(mu^3 E^2 r):  (r/2) 16 e mu^3 e^{-2 mu} E^2 kappa = c1^2 b/Gam2^2;
    (e) min over a >= 0 of m1 a/2 + m4 (b omega/2)/(a + sigma) = sqrt(m1 m4 b omega) - m1 sigma/2;  (f) min over a >= sigma... of X a + Y/(2a) = sqrt(2 X Y);
    (g) B1m/hFz = cm sqrt(sigma/r)(sqrt a + sigma/sqrt a) and uB2c/cKz = 2 X1 sqrt(b/kappa)/((1 - eta) fl kf) from the coefficients of the lines;
    (h) hneg1/P4z = 2 k_E (eta + 0.184)/omega, N1/P1 = eta k_E (2 + r)/(1 + r);  (i) B1m/P2z at a_L."""
    getcontext().prec = 80; D = Dc; worst = D(0); pi = D('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899')
    for ell, mu, r, B, kap, P, a in ((D('55.26'), D('11.0'), D('1e-12'), D('1e28'), D('0.03'), D('7e-4'), D('1e-11')), (D('955.8'), D('233.5'), D('1e-207'), D('1e420'), D('0.0015'), D('1e-99'), D('1e-205')),
                                     (D('300'), D('6'), D('0.2'), D('3e10'), D('0.5'), D('1e-20'), D('1e-100'))):
        sg = (-ell).exp(); eta = 1 / ell; Gm = ((1 + D(10) / ell) / ell).sqrt(); k2 = 1 / (2 * (1 - eta)); G2 = Gm * k2; b = B * sg * sg; fl = 1 / (1 + eta)
        q = (8 * ell + 100) * (1 + eta) / (8 * B * (1 - eta)); z2 = (8 * ell + 100) / (2 * B); al = (1 - q) * fl / (4 * mu * r * (2 + r)); be = fl * (1 - z2 / 2) * r / (4 * (2 + r))
        om = 1 / (1 + D(3) / (4 * B)) ** 2; brk = 1 - 4 * b / (1 - b) - z2 / 12; kf = (1 - b) ** 2 * brk; chi = fl * kf * kap * sg / (16 * b); G = P * (r / (2 + r)).sqrt()
        m1, m2, m3, m4, m5 = D('0.97'), D('0.9999'), D('0.999'), D('0.83'), D('0.9')
        Ths = 2 * (m2 * m3 * al * be).sqrt() / G2; xi = r * mu.sqrt() / sg * (m3 * (1 - z2 / 2) / (m2 * (1 - q))).sqrt()
        worst = max(worst, abs(Ths / (2 * xi) / (sg * m2 * al / G2) - 1))
        u = m1 / (2 * m2 * al * G); v = m4 * b * om / (2 * m3 * be * G); ch = m5 * chi / G2
        worst = max(worst, abs(u ** 3 * v * ch / ((m1 / m2) ** 3 * (m4 / m3) * m5 * b * om * chi / (16 * al ** 3 * be * G ** 4 * G2)) - 1))
        c1 = D('0.78'); w = D('0.8972'); G2s2 = G2 * G2 * ell; ckap = 2 * c1 ** 2 / (G2s2 * w ** 2); k0 = ckap * ell * b / r; worst = max(worst, abs((r / 2) * w ** 2 * k0 / (c1 ** 2 * b / G2 ** 2) - 1))
        E = D('1.3'); cJ = c1 ** 2 / (8 * D(1).exp() * G2s2); k1 = cJ * ell * b * (2 * mu).exp() / (mu ** 3 * E ** 2 * r)
        worst = max(worst, abs((r / 2) * 16 * D(1).exp() * mu ** 3 * (-2 * mu).exp() * E ** 2 * k1 / (c1 ** 2 * b / G2 ** 2) - 1))
        t = (m4 * b * om / m1).sqrt(); worst = max(worst, abs((m1 * (t - sg) / 2 + m4 * (b * om / 2) / t) / ((m1 * m4 * b * om).sqrt() - m1 * sg / 2) - 1))
        X = m1 / 2 + m2 * al * G; Y = m4 * b * om / 2 + m3 * be * G; a0 = (Y / (2 * X)).sqrt(); worst = max(worst, abs((X * a0 + Y / (2 * a0)) / (2 * X * Y).sqrt() - 1))
        U1 = (2 * ell + D('3.1')).sqrt() / 4 + D('1e-6'); X1 = U1 / D('0.75'); fF = G / (4 * (1 - eta)); kE = (r / (1 + r)).sqrt()
        B1m = fF * X1 / (D(2).sqrt() * pi.sqrt() * (2 + r).sqrt()) * (4 * r).sqrt() * sg ** D('0.5') / a.sqrt(); hFz = fl * G / 4 * (r / (2 + r)) * (1 - z2 / 2) / (a + sg)
        cm = 2 * X1 * (2 + r).sqrt() / ((1 - eta) * fl * (1 - z2 / 2) * (2 * pi).sqrt()); worst = max(worst, abs(B1m / hFz / (cm * (sg / r).sqrt() * (a.sqrt() + sg / a.sqrt())) - 1))
        uB2c = fF * (kap / (2 * B)).sqrt() * X1 / D(2).sqrt(); cKz = fl * G / 4 * (1 - b) ** 2 * kap / (4 * B) * brk / sg
        worst = max(worst, abs(uB2c / cKz / (2 * X1 * (b / kap).sqrt() / ((1 - eta) * fl * kf)) - 1))
        hneg = B * kE * (eta + D('0.184')) * sg * sg / (a + sg); P4 = (B / 2) / (1 + D(3) / (4 * B)) ** 2 * sg * sg / (a + sg); worst = max(worst, abs(hneg / P4 / (2 * kE * (eta + D('0.184')) / om) - 1))
        N1 = eta * kE * (2 + r) / (2 * (1 + r)) * a; worst = max(worst, abs(N1 / (a / 2) / (eta * kE * (2 + r) / (1 + r)) - 1))
        aL = r / (4 * cm ** 2 * ell ** 6 * sg); B1mL = B1m * (a / aL).sqrt(); P2L = al * G * aL
        worst = max(worst, abs(B1mL / P2L / (X1 * 2 * (r * sg).sqrt() * 4 * mu * r * (2 + r) / (4 * (1 - eta) * (2 * pi * (2 + r)).sqrt() * (1 - q) * fl * aL ** D('1.5'))) - 1))
    aa = D('0.37'); w = D('0.0123'); u = 3 * w / aa; v = w / aa; worst = max(worst, abs((aa * u + aa * v + w) / (5 * (aa ** 4 * u ** 3 * v * w / 27) ** (D(1) / 5)) - 1))
    return float(worst)


def check_borders(ell, rng, n=1500):
    """states ON the borders of the regimes of the RULE (and e^{+-1e-9} next to them): xi = ell^2 (narrow/wide), r = c_ch sqrt(ell) sigma, G = c1 sqrt(b)/Gam2 (Cases I/II),
    kappa = c_T sqrt(ell) b/sigma.  The rule's log F on them (must be >= the claim): no gap between the pieces of the proof."""
    Y, lP, Y5 = sample(ell, rng, n, full=True); R = S.ranges(ell); lc = 0.5 * math.log1p(C / ell); out = {}; line = 2 * math.log(ell) - ell
    lG2 = math.log(math.sqrt(1 + C / ell) / (2 * (1 - 1 / ell))) - 0.5 * math.log(ell)
    def ev(name, Z5):
        Z5 = np.clip(Z5, R[:, 0], R[:, 1]); lp = S.lPbar(ell, Z5[:, 0], Z5[:, 2] - 2 * ell, Z5[:, 3]) + Z5[:, 4]; lF, reg = rule_lF(ell, Z5[:, :4], lp)
        lF = np.where(np.isnan(lF), -np.inf, lF)
        out[name] = {'states': int(len(Z5)), 'states per regime': [int((reg == k).sum()) for k in range(4)], 'smallest log F of the rule': float(lF.min()), 'log F needed': lc, 'below the claim': int((lF < lc).sum())}
    for d in (0.0, 1e-9, -1e-9):
        Z = Y5.copy(); Z[:, 1] = line - 0.5 * Z[:, 0] + d; ev('xi = ell^2 (r sqrt(mu) = ell^2 sigma) %+.0e' % d, Z)
        Z = Y5.copy(); Z[:, 1] = math.log(CCH) + 0.5 * math.log(ell) - ell + d; ev('r = c_ch sqrt(ell) sigma %+.0e' % d, Z)
        Z = Y5.copy(); lgs = 0.5 * (Z[:, 1] - np.log(2 + np.exp(Z[:, 1]))); lPb = S.lPbar(ell, Z[:, 0], Z[:, 2] - 2 * ell, Z[:, 3]); qn = math.log(C1) + 0.5 * (Z[:, 2] - 2 * ell) - lG2 - lgs - lPb + d
        ok = qn <= 0; Z = Z[ok]; Z[:, 4] = qn[ok]; ev('G = c1 sqrt(b)/Gam2 %+.0e' % d, Z)
        Z = Y5.copy(); Z = Z[Z[:, 2] - 2 * ell < math.log(0.1)]; Z[:, 3] = math.log(CT) + 0.5 * math.log(ell) + Z[:, 2] - ell + d; ev('kappa = c_T sqrt(ell) b/sigma (b < 0.1) %+.0e' % d, Z)
    return out


def rule_search(ell, seed=5, n=1500):
    """the smallest log F of the RULE per regime (how tight each piece of the proof is): the search of dj_search with the rule's value, restricted to one regime at
    a time; the starts are the families of the search and the states of sample() that lie in the regime."""
    out = {}; lc = 0.5 * math.log1p(C / ell); rng0 = np.random.default_rng(seed + int(ell) % 9973); Y, lP, Y5 = sample(ell, rng0, n, full=True); reg0 = rule(ell, state_quantities(ell, Y, lP))
    names = ('Case I, Fz', 'Case I, Tz-B2', 'Case II, chirp (Tz-B2)', 'Case II, the rest (Tz-B2 below a_s, Tz-B1 from a_s)')
    for g in range(4):
        def vf(Yc, g=g):
            lp = S.lPbar(ell, Yc[:, 0], Yc[:, 2] - 2 * ell, Yc[:, 3]) + Yc[:, 4]; lF, reg = rule_lF(ell, Yc[:, :4], lp); return np.where(reg == g, lF, np.inf)
        sd = Y5[reg0 == g]; sd = sd[rng0.permutation(len(sd))[:3000]] if len(sd) else None
        lF, y, nev, fam, nan = S.search(ell, np.random.default_rng(seed + g), n=n, seeds=sd, vfun=vf)
        m = float(J.margin(np.array([lF]), ell)[0])
        out[names[g]] = {'smallest log F of the rule in this regime': lF, 'the same as (F^2 - 1) ell': m if np.isfinite(m) else 'overflow', 'log F needed': lc, 'below the claim': bool(lF < lc), **S.describe(y, ell),
                         'states evaluated': int(nev), 'nan': int(nan)}
        print(ell, names[g], json.dumps(out[names[g]])[:400], flush=True)
    return out


def run(part='all', save=True):
    """python3 dj_proof.py [all|quick|rule|tight]  -> results/dj_proof.json, and results/dj_proof_rule.json for the part 'rule' (so that it can run beside the others) (quick: constants, 60 digits, (AG), steps and remainders; rule: the end-to-end check of the
    rule and the borders; tight: the smallest value of the rule per regime), each part resumable."""
    fn = __import__('os').environ.get('DJ_PROOF_OUT') or {'rule': 'results/dj_proof_rule.json', 'tight': 'results/dj_proof_tight.json'}.get(part, 'results/dj_proof.json'); out = json.load(open(fn)) if __import__('os').path.exists(fn) else {}
    def put(k, f):
        if k in out: return
        t0 = time.time(); out[k] = f(); print(k, json.dumps(out[k])[:600], round(time.time() - t0, 1), flush=True)
        if save: json.dump(out, open(fn, 'w'), indent=1)
    if part in ('all', 'quick'):
        put('60-digit check (the algebra of the new steps): largest error', check_60)
        put('constants', check_consts)
        put('(AG) on a grid of dl, per ell', check_AG_direct)
        for ell in (55.26, 82.89, 165.78, 955.8, 1e4, 1e6, 1e8):
            put('remainders, ell = %s' % ell, lambda: check_remainders(ell, np.random.default_rng(101 + int(ell) % 9973)))
            put('steps, ell = %s' % ell, lambda: check_steps(ell, np.random.default_rng(202 + int(ell) % 9973)))
        for ell in (55.26, 955.8):
            put('power: remainder bounds multiplied by 0.9, ell = %s' % ell, lambda: check_remainders(ell, np.random.default_rng(101 + int(ell)), wrong=0.9))
            for w in ('ckap2', 'cJ2', 'w16', 'EJ', 'ECM', 'phi'):
                put('power: wrong version %s of the steps, ell = %s' % (w, ell), lambda: check_steps(ell, np.random.default_rng(202 + int(ell)), wrong=w))
            put('power: the remainder bounds outside their regions, ell = %s' % ell, lambda: check_outside(ell, np.random.default_rng(404 + int(ell))))
    if part == 'rule':
        put('the rule, end to end', check_rule)
        for ell in (55.26, 955.8, 1e6):
            put('borders, ell = %s' % ell, lambda: check_borders(ell, np.random.default_rng(303 + int(ell))))
    if part in ('all', 'tight'):
        for ell in (55.26, 955.8):
            put('the smallest value of the rule per regime, ell = %s' % ell, lambda: rule_search(ell))
    return out


if __name__ == '__main__':
    run(sys.argv[1] if len(sys.argv) > 1 else 'all')
