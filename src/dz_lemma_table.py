"""Stage DZ, item 2.1 (revised in stage EA: section numbers of App. A of paper I, X1_B1 as a function of eta, the line B1m of paper J): THE TABLE OF HOW THE LEMMAS USE eta (the re-reading of the proofs of paper I and of the lemmas it borrows from papers H and F).
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
The table itself is a reading of the published text (paper I v1.0, App. A-C and Secs. III-VII; paper H v1.3, Secs. VII-IX and co_remainders.py; paper F v1.5,
App. A); it is written below as data, one row per lemma, and printed as the LaTeX table of App. A of paper J.  This file checks what can be checked by machine:
 (T1) THE INVENTORY.  Every one of the 37 lines of paper I has an origin (a row of the table); the basic functions of eta read from the CODE by dy_convex
      (results_DY/dy_convex.json) must be contained in the eta-forms that the table lists for the origin rows of the line, and every eta-form listed for a row
      that carries lines must occur in at least one of its lines (no form in the table that the code does not have, none in the code that the table misses).
      POWER: (t1) the form 1/(1-eta)^2 removed from the row of (B2); (t2) the line FzK given the origin of (A1v) (eta-free); (t3) sqrt(CZ) added to the row of
      the ring lemma: each must be caught.
 (T2) THE ELEMENTARY STEPS AT eta <= 1/4 (exact rationals where the step is rational; 2000 grid points and 60 digits otherwise):
      (e1) |z - ln(1 + z)| <= z^2/(2(1 - eta)) for |z| <= eta < 1 (the bound |G_E| <= R^2/(2(1 - eta)) of Lemma 19 (B1w));  wrong version z^2/2 must fail;
      (e2) 1/(1 - eta) <= 4/3 for eta <= 1/4 (exact), and fails at eta = 26/100;
      (e3) THE STEP OF FrB1: U1 (4/3 - 1/(1 - eta)) >= sqrt(CZ(eta)) holds at eta = 1/ell for ell in [55.26, 1e6] and FAILS at eta = 1/4 (the one step of the
           lemmas that needs eta <= 1/ell);
      (e4) the repair: c0^ = U1/(sqrt2 (1 - eta)) + sqrt(CZ(eta)/2) sqrt(A) <= X1_B1(eta)/sqrt2, X1_B1(eta) = U1/(1 - eta) + sqrt(CZ(eta)) (stage EA: a function of
           eta, pointwise), for eta in [0, 1/4], A in [0, 1]; wrong version without sqrt(CZ) must fail;
      (e5) c0^2 <= X1^2 + CZ (X1 = 4 U1/3) for eta <= 1/4, A <= 1; wrong version (X1^2 + CZ)/2 (the factor 2 of (p + q)^2 <= 2p^2 + 2q^2 dropped) must fail;
      (e6) the ring: q = K^2 (1 + eta)/(8 B (1 - eta)) <= (1 + eta)/(400 (1 - eta)) <= 1/240 (narrow, B >= 50 K^2) and <= 5/24 (wide, B >= K^2), so 1 - q > 0;
           the text's number 'ringf >= 1 - 0.0026' holds at eta = 1/ell and fails at 1/4 (a number, retaken; the code computes q with eta);
      (e7) the tail of paper I: (1 - eta)/(1 + eta) >= 1 - 2/ell holds at eta = 1/ell and fails at eta = 1/4 (the second place where eta <= 1/ell is used:
           in the proof, not in a lemma; replaced in DY by the tail with eta and 1/ell separated);
      (e8) Theorem H1: its certificates use eta_bar = 1/2 in the remainders and lambda_* = 2/3 (paper H, Sec. IV); 1/4 <= 1/2 and 2/3 <= 1/(1 + 1/4).
-> results_DZ/dz_lemma_table.json and paper J's App. A table (paperJ/sections/A_lemma_table.tex, written by this file)."""
import json, math, os, sys
from decimal import Decimal as Dc, getcontext
from fractions import Fraction as Fr

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MODEL = 'Claude Opus 5.5 (claude-opus-5-5)'

# ---------------------------------------------------------------------------------------------------------------------------------------------------
# THE TABLE.  fields: id, lemma, where (paper I numbering of v1.0 unless said), statement (eta or ell in the hypotheses), where eta enters the proof,
# bound used, valid for eta <= 1/4, fix, forms (eta-forms in the vocabulary of dy_convex: eta, eta^2, 1/(1-eta), 1/(1-eta)^2, sqrt(CZ), sandwich fl,
# sandwich ringf), lines (the lines of App. B of paper I whose origin is this row).
# ---------------------------------------------------------------------------------------------------------------------------------------------------
ROWS = [
    dict(id='L18', lemma='Lemma 18 (direct form)', where='I, App. A 2', stmt='none', enters='nowhere (an identity: the definition in the variables of the line)',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='L19M0', lemma='Lemma 19 (M0)', where='I, App. A 3', stmt='none ($|R_\\theta|\\le\\eta$ is a consequence)', enters='$|R_\\theta|\\le\\eta$ from $|R|\\le\\eta$; $|t_\\rho|\\le0.184b$ uses $\\Qb$',
         bound='$\\eta=\\sup|R|$ (definition)', ok='yes', fix='', forms=['eta'], lines=['P3z', 'P4z', 'hneg1', 'M0Xi']),
    dict(id='L19A1', lemma='Lemma 19 (A1v), (A1w)', where='I, App. A 3', stmt='none', enters='(A1w): $|R|\\le\\eta$ and $\\eta k_E/\\sqrt{\\mathrm{se}_E}=\\eta/L$ (identity)',
         bound='definition', ok='yes', fix='', forms=['eta'], lines=['A1v', 'A1w']),
    dict(id='L19A2', lemma='Lemma 19 (A2)', where='I, App. A 3', stmt='none', enters='$h\\ge1-\\eta$; $R^2/h\\le\\eta^2/(1-\\eta)$',
         bound='$\\eta<1$', ok='yes', fix='', forms=['eta', 'eta^2', '1/(1-eta)'], lines=['A2k', 'A2a', 'A2b']),
    dict(id='L19B1v', lemma='Lemma 19 (B1v)', where='I, App. A 3', stmt='none', enters='$\\langle\\hat s^2\\tilde F\\rangle\\le\\kappa W/(1-\\eta)$ ($h\\ge1-\\eta$)',
         bound='$\\eta<1$', ok='yes', fix='', forms=['1/(1-eta)'], lines=['FzK', 'lossK']),
    dict(id='L19B1w', lemma='Lemma 19 (B1w)', where='I, App. A 3', stmt='none', enters='$|G_E(R)|\\le R^2/(2(1-\\eta))$ for $|ER|\\le\\eta$; $R^2\\le\\eta^2$',
         bound='$\\eta<1$ (checked, e1)', ok='yes', fix='', forms=['eta^2', '1/(1-eta)'], lines=['B1w1', 'B1w2']),
    dict(id='L19B2', lemma='Lemma 19 (B2)', where='I, App. A 3', stmt='none', enters='$E|X_1|/h\\le U/(1-\\eta)$; $R^2/h^2\\le\\eta^2/(1-\\eta)^2$',
         bound='$\\eta<1$', ok='yes', fix='', forms=['eta^2', '1/(1-eta)^2'], lines=['B2a', 'B2b']),
    dict(id='L20', lemma='Lemmas 15, 20, 21 ($M_4$, $M_1$, $M_2$)', where='I, Sec. VI, App. A 3', stmt='none', enters='nowhere ($y$ only)',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='L22', lemma='Lemma 22 (ring)', where='I, App. A 4', stmt='none', enters='$M=\\eta^2/(1-\\eta)$ for $g=R^2/h$; $q=K^2(1+\\eta)/(8B(1-\\eta))<1$',
         bound='$\\eta<1$; $q\\le\\frac1{240}$ (narrow), $\\frac5{24}$ (wide) at $\\eta\\le\\frac14$ (e6)', ok='yes',
         fix='the number $1-0.0026$ in the sign paragraph of App. B of I is the value at $\\eta=1/\\ell$; at $\\eta\\le\\frac14$ it is $1-\\frac1{240}$ (the code computes $q$ with $\\eta$)',
         forms=['eta^2', '1/(1-eta)', 'sandwich ringf'], lines=['ring2', 'P2z']),
    dict(id='L23', lemma='Lemma 23 (pair) (a)--(c)', where='I, App. A 4', stmt='none', enters='$\\tilde F$ between $E^2X_1^2/(1\\pm\\eta)$; tails $U^2g_s/(1-\\eta)$',
         bound='$\\eta<1$', ok='yes', fix='', forms=['sandwich fl', '1/(1-eta)'], lines=['hFz', 'cKz', 'pair']),
    dict(id='L23d2', lemma='Lemma 23 (d), FrB2', where='I, App. A 4; App. B (group B2c$+$B2s)', stmt='none',
         enters='$c_0=\\sigma U/(\\sqrt2(1-\\eta))+\\zeta/\\sqrt2$, $\\zeta^2=\\sigma^2\\mathrm{CZ}A$; App. B: $U_1/(1-\\eta)\\le X_1$',
         bound='$1/(1-\\eta)\\le\\frac43$ (e2)', ok='yes (equality at $\\frac14$)', fix='', forms=['1/(1-eta)', 'sqrt(CZ)'], lines=['B2c', 'B2s']),
    dict(id='L23d1', lemma='Lemma 23 (d), FrB1', where='I, App. A 4; App. B (group B1m$+\\dots+$uB2s)', stmt='none',
         enters='App. B: $\\hat c_0\\le X_1/\\sqrt2$ from $U_1(\\frac43-1/(1-\\eta))\\ge\\sqrt{\\mathrm{CZ}}$; $\\hat c_0^2\\le X_1^2+\\mathrm{CZ}$',
         bound='$\\eta\\le1/\\ell$ in the first step (e3); $1/(1-\\eta)\\le\\frac43$ in the second (e5)',
         ok='\\textbf{no} for the first step (zero left side at $\\frac14$); yes for the second',
         fix='$X_{1,\\rm B1}(\\eta)=U_1/(1-\\eta)+\\sqrt{\\mathrm{CZ}(\\eta)}$ in the line B1m (e4), a function of $\\eta$ of the class of Lemma~\\ref{lem:chord}, Sec.~\\ref{sec:changes}',
         forms=['1/(1-eta)', '1/(1-eta)^2', 'eta^2', 'sqrt(CZ)'], lines=['B1m', 'B1c', 'B1l', 'uB2c', 'uB2s']),
    dict(id='Lsum', lemma='$v$-branch sum and its den (App. A 5 of I)', where='I, App. A 5', stmt='none', enters='den: $b(1+k_ER_\\theta)\\le b(1+\\eta k_E)$; $W/(1-\\eta)$',
         bound='$\\eta<1$', ok='yes', fix='', forms=['eta', '1/(1-eta)'], lines=['d1', 'd2']),
    dict(id='HRt', lemma='Lemma R$_\\theta$ of H, $w$-branch (N1--N4, P1, P2, den)', where='H, Sec. IX A; \\code{co\\_remainders.py}; I, App. A 6',
         stmt='none (``every periodic window state\'\')',
         enters='$\\Lambda_1$, $Q_2$: $|R_\\theta|\\le\\eta$; $J_{2,\\rm up}$, $M_{4w}$, $J_{\\rm up}$: $\\eta^2/(1-\\eta)$, $D_0/(1-\\eta)$; P2: $D_0/(1+\\eta)$; $\\xi=\\sigma U_1/(1-\\Qb)$ uses $\\Qb$, not $\\eta$',
         bound='$\\eta<1$, $\\Qb=\\frac14$, $A\\le1$', ok='yes', fix='',
         forms=['eta', 'eta^2', '1/(1-eta)', '1/(1-eta)^2', 'sandwich fl'], lines=['P1', 'P2z', 'N1', 'N2', 'N3', 'N4', 'N4G', 'd3', 'd4']),
    dict(id='L8', lemma='Lemma 8 (the 37 lines): the 12 identities and 18 inequalities', where='I, Sec. III B; App. B',
         stmt='$\\eta\\le1/\\ell$ (coefficients evaluated at $\\eta=1/\\ell$)',
         enters='coefficients only, except the FrB1 step (row above) and $1/(1-\\eta)\\le\\frac43$ in FrB2, FrB1; signs: positive factors for $\\eta<1$',
         bound='$\\eta<1$, $\\eta\\le\\frac14$', ok='yes, with the FrB1 constant', fix='the coefficients are evaluated with the end values of $\\eta$ (the chord, Sec.~\\ref{sec:sandwich})',
         forms=[], lines=[]),
    dict(id='L9', lemma='Lemma 9 (H$^\\prime$), Lemma 24, Corollary 25', where='I, Sec. III C; App. A 7', stmt='none', enters='nowhere: (A) and (CM) use $\\Qb$; (K) uses $U_1$; (J) is Jensen',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='L10', lemma='Lemmas 10, 26, 27 (closed forms, $E_J$)', where='I, Sec. III C; App. A 8', stmt='none', enters='nowhere', bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='L11', lemma='Lemma 11 ($G=0$)', where='I, Sec. III D; App. A 9', stmt='none', enters='nowhere ($R=0$)', bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='T5', lemma='Theorem 5 (Proposition 6, Lemmas 7, 16, 17)', where='I, Sec. VII; App. D', stmt='none', enters='only through $\\Qb$: $|h_t/h|\\le N_1/(1-\\Qb)$, $\\Xi$, $K_1$',
         bound='$\\Qb=\\frac14$', ok='yes', fix='', forms=[], lines=[]),
    dict(id='HCM', lemma='Lemma CM-1, Lemma CN-1 (line 2) of H', where='H, Sec. IX A; I, App. A 10', stmt='none (every focus)', enters='nowhere ($f\\ge0$; a pointwise Gaussian bound)',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='HA4', lemma='Lemma A4$^*$ of H', where='H, Sec. III, App. D; I, App. A 10', stmt='none', enters='$\\zeta=\\sigma^2\\eta e^{-1/2}/(s(1-\\eta))$; $\\xi$ with $\\Qb$',
         bound='$\\eta<1$', ok='yes', fix='', forms=[], lines=[]),
    dict(id='HH1', lemma='Theorem H1, Lemma BE of H', where='H, Secs. IV, VI--VIII', stmt='the theorem: every admissible window, coefficient $\\lambda/\\Upsilon$; item (i) only: $\\eta\\le1/\\ell$',
         enters='the certificates: $\\bar\\eta=\\frac12$ in the remainders, $\\lambda_*=\\frac23$', bound='$\\eta\\le\\frac12$', ok='yes (item (i) is not used)', fix='', forms=[], lines=[]),
    dict(id='Hwin', lemma='window constants $U_1$, $U_2$, $\\gamma_P$, $c_\\chi$ of H', where='H, Sec. VI; I, App. A 10', stmt='$x\\ge5\\times10^{11}\\sigma^2$', enters='nowhere ($\\Qb$, $\\ell$)',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='F', lemma='Lemmas 19, 21--23 of F (BL0--BL3), Eq.~(ga) and (P6)', where='F, App. A', stmt='none', enters='nowhere: $\\Qb$ and $\\nu_k$; (P6) is the class bound $\\bar\\varepsilon$',
         bound='none', ok='yes', fix='', forms=[], lines=[]),
    dict(id='P24', lemma='Propositions 12, 14 (Theorems 2, 4): the written steps', where='I, Secs. IV, VI; App. C', stmt='$\\eta\\le1/\\ell$',
         enters='(a) 18 of the 48 quoted numbers are values at $\\eta=1/\\ell$; (b) the rule: $c_m$, $\\Gamma_2=\\Gamma_\\ell k_2$; (c) the tail on $[10^6,\\infty)$: $\\theta_1\\ge(1-7/\\ell)(1-\\varepsilon_1^\\prime)$ uses $(1-\\eta)/(1+\\eta)\\ge1-2/\\ell$ (e7)',
         bound='$\\eta=1/\\ell$ as a value; (c) $\\eta\\le1/\\ell$', ok='no as written; every step holds with the numbers retaken',
         fix='(a) new bounds (Table~\\ref{tab:quoted}); (b) $\\lambda$-free rule (Sec.~\\ref{sec:sandwich}); (c) the tail with $\\eta$ and $1/\\ell$ separated (App.~\\ref{app:C}): constants, no new idea',
         forms=[], lines=[]),
    dict(id='P13', lemma='Proposition 13 (Theorem 3)', where='I, Sec. V', stmt='$\\eta\\le1/\\ell$', enters='the numbers of the proof at $\\eta=1/\\ell$',
         bound='$\\eta=1/\\ell$ as a value', ok='redone', fix='proved again by hand at $\\bar\\eta=\\frac14$ (Sec.~\\ref{sec:res})', forms=[], lines=[]),
]


def inventory_check(rows, inv):
    """inv: line -> list of basics read from the code.  Returns (problems, line -> origin rows)."""
    origin = {}
    for r in rows:
        for l in r['lines']: origin.setdefault(l, []).append(r['id'])
    probs = []
    for l, bas in inv.items():
        if l not in origin: probs.append('line %s has no origin row' % l); continue
        allowed = set().union(*(set(next(r for r in rows if r['id'] == o)['forms']) for o in origin[l]))
        extra = set(bas) - allowed
        extra = {e for e in extra if not (e.startswith('sandwich ringf') and 'sandwich ringf' in allowed)}
        if extra: probs.append('line %s: forms read from the code not in the table: %s' % (l, sorted(extra)))
    for r in rows:
        if not r['lines']: continue
        used = set()
        for l in r['lines']:
            used |= {('sandwich ringf' if b.startswith('sandwich ringf') else b) for b in inv.get(l, [])}
        missing = set(r['forms']) - used
        if missing: probs.append('row %s: forms in the table that none of its lines has: %s' % (r['id'], sorted(missing)))
    for l in origin:
        if l not in inv: probs.append('row line %s is not one of the 37 lines' % l)
    return probs, origin


def steps():
    getcontext().prec = 60; out = {}
    # (e1)
    worst = None; wrong_fail = False
    for i in range(1, 51):
        eta = Dc(i) / 200                                   # (0, 1/4]
        for j in range(-40, 41):
            z = eta * j / 40
            if z == 0: continue
            lhs = abs(z - (1 + z).ln()); rhs = z * z / (2 * (1 - eta))
            m = rhs - lhs; worst = m if worst is None or m < worst else worst
            if lhs > z * z / 2: wrong_fail = True
    out['e1 |z - ln(1+z)| <= z^2/(2(1-eta)), |z| <= eta <= 1/4: smallest margin'] = float(worst)
    out['e1 holds'] = bool(worst >= 0); out['e1 wrong version z^2/2 fails somewhere'] = wrong_fail
    # (e2)
    out['e2 1/(1-1/4) = 4/3 exactly'] = Fr(1) / (1 - Fr(1, 4)) == Fr(4, 3)
    out['e2 wrong: 1/(1-26/100) > 4/3'] = Fr(1) / (1 - Fr(26, 100)) > Fr(4, 3)
    # (e3)-(e5)
    U1 = lambda ell: Dc('0.25') * (2 * Dc(ell) + Dc('3.1')).sqrt() + Dc('1e-6')
    CZ = lambda eta: eta * eta / (Dc(1).exp() * (1 - eta) ** 2)
    e3 = []
    for ell in ('55.26', '100', '960.8', '1e4', '1e6'):
        eta = 1 / Dc(ell); e3.append(U1(ell) * (Dc(4) / 3 - 1 / (1 - eta)) - CZ(eta).sqrt())
    out['e3 FrB1 step at eta = 1/ell (ell = 55.26 ... 1e6): smallest margin'] = float(min(e3)); out['e3 holds at eta = 1/ell'] = bool(min(e3) > 0)
    eq = U1('55.26') * (Dc(4) / 3 - 1 / (1 - Dc('0.25'))) - CZ(Dc('0.25')).sqrt()
    out['e3 FrB1 step at eta = 1/4, ell = 55.26 (must be negative)'] = float(eq); out['e3 fails at eta = 1/4'] = bool(eq < 0)
    sq2 = Dc(2).sqrt(); e4 = []; e4w = []; e5 = []; e5w = []
    for ell in ('55.26', '960.8', '1e6'):
        for i in range(0, 51):
            eta = Dc(i) / 200
            for A in (Dc(0), Dc('0.5'), Dc(1)):
                c0 = U1(ell) / (sq2 * (1 - eta)) + (CZ(eta) / 2).sqrt() * A.sqrt()
                X1B1 = U1(ell) / (1 - eta) + CZ(eta).sqrt(); X1w = U1(ell) / (1 - eta)        # stage EA: X1_B1(eta), pointwise; wrong: without sqrt(CZ)
                e4.append(X1B1 / sq2 - c0); e4w.append(X1w / sq2 - c0)
                X1 = 4 * U1(ell) / 3; e5.append(X1 * X1 + CZ(eta) - c0 * c0); e5w.append((X1 * X1 + CZ(eta)) / 2 - c0 * c0)
    out['e4 repaired step c0^ <= X1_B1(eta)/sqrt2 (eta in [0, 1/4], A in [0, 1]): smallest margin'] = float(min(e4)); out['e4 holds'] = bool(min(e4) >= Dc('-1e-50'))   # equality at A = 1 (60-digit rounding)
    out['e4 wrong version (X1_B1 without sqrt(CZ)) fails'] = bool(min(e4w) < 0)
    out['e5 c0^2 <= X1^2 + CZ: smallest margin'] = float(min(e5)); out['e5 holds'] = bool(min(e5) >= 0); out['e5 wrong version (X1^2 + CZ)/2 fails'] = bool(min(e5w) < 0)
    # (e6)
    q_n = (1 + Fr(1, 4)) / (400 * (1 - Fr(1, 4))); q_w = (1 + Fr(1, 4)) / (8 * (1 - Fr(1, 4)))
    out['e6 q at eta = 1/4: narrow (B >= 50 K^2), wide (B >= K^2)'] = [str(q_n), str(q_w)]
    out['e6 1 - q > 0 at both'] = bool(q_n < 1 and q_w < 1)
    out['e6 text number 0.0026: holds at eta = 1/55.26'] = bool((1 + 1 / Dc('55.26')) / (400 * (1 - 1 / Dc('55.26'))) <= Dc('0.0026'))
    out['e6 text number 0.0026: fails at eta = 1/4'] = bool(Dc(q_n.numerator) / Dc(q_n.denominator) > Dc('0.0026'))
    # (e7)
    ok7 = all((1 - 1 / Dc(l)) / (1 + 1 / Dc(l)) >= 1 - 2 / Dc(l) for l in ('55.26', '1e6', '1e12'))
    out['e7 (1-eta)/(1+eta) >= 1 - 2/ell at eta = 1/ell'] = ok7
    out['e7 fails at eta = 1/4, ell = 1e6'] = bool(Fr(3, 5) < 1 - Fr(2, 10 ** 6))
    # (e8)
    out['e8 1/4 <= 1/2 and 2/3 <= 1/(1 + 1/4)'] = bool(Fr(1, 4) <= Fr(1, 2) and Fr(2, 3) <= 1 / (1 + Fr(1, 4)))
    keys_true = [k for k in out if isinstance(out[k], bool)]
    out['all elementary checks as expected'] = all(out[k] for k in keys_true)
    return out


def latex(rows):
    L = ['% written by src/dz_lemma_table.py (stage DZ); do not edit by hand', '\\begin{table*}',
         '\\caption{How the lemmas behind Theorem~\\ref{thm:J} use $\\eta$: the re-reading of every lemma of~\\cite{I} that Theorem~\\ref{thm:J} uses, and of the lemmas it borrows from~\\cite{F,H}. '
         '``Statement\'\': $\\eta$ or $\\ell$ in the hypotheses. ``Where $\\eta$ enters\'\': the step of the proof. ``Bound used\'\': the bound on $\\eta$ that step needs. '
         'Numbers of lemmas and sections are those of~\\cite{I} v1.0 unless marked H~\\cite{H} or F~\\cite{F}. The labels (e1)--(e8) are the elementary checks of \\code{dz\\_lemma\\_table.py}.}',
         '\\label{tab:lemmas}', '\\begin{ruledtabular}', '\\scriptsize',
         '\\begin{tabular}{p{0.15\\textwidth}p{0.09\\textwidth}p{0.1\\textwidth}p{0.25\\textwidth}p{0.12\\textwidth}p{0.08\\textwidth}p{0.13\\textwidth}}',
         'lemma & where & statement & where $\\eta$ enters & bound used & $\\eta\\le\\frac14$ & repair\\\\ \\hline']
    head = L[-2:]                                       # the tabular head, repeated in the continuation
    # the table is split into two floats (rows 1-13 and 14-26), because as one float it is taller than a page of REVTeX and is cut there
    half = (len(rows) + 1) // 2
    for i, r in enumerate(rows):
        if i == half:
            L += ['\\end{tabular}', '\\end{ruledtabular}', '\\end{table*}', '\\begin{table*}', '\\addtocounter{table}{-1}',
                  '\\caption{(Continued.)}', '\\begin{ruledtabular}', '\\scriptsize'] + head
        L.append(' & '.join([r['lemma'], r['where'], r['stmt'], r['enters'], r['bound'], r['ok'], r['fix'] or '---']) + '\\\\')
    L += ['\\end{tabular}', '\\end{ruledtabular}', '\\end{table*}']
    return '\n'.join(L) + '\n'


def main():
    inv = json.load(open(os.path.join(ROOT, 'results_DY', 'dy_convex.json')))['inventory read from the code (line -> sign, type, sandwich, basics)']
    inv = {l: (v['basics'] if isinstance(v, dict) else v[-1]) for l, v in inv.items()}
    # stage EA: the line B1m of paper J, with X1_B1(eta) in it, read by the parser from the transformed code (ea_convex.py)
    ea = os.path.join(ROOT, 'results_EA', 'ea_convex.json')
    if os.path.exists(ea): inv['B1m'] = json.load(open(ea))['B1m of paper J read from the transformed code']['basics']
    out_b1m = inv['B1m']
    probs, origin = inventory_check(ROWS, inv)
    power = {}
    import copy
    R1 = copy.deepcopy(ROWS); next(r for r in R1 if r['id'] == 'L19B2')['forms'].remove('1/(1-eta)^2')
    power['t1 1/(1-eta)^2 removed from (B2)'] = bool(inventory_check(R1, inv)[0])
    R2 = copy.deepcopy(ROWS); next(r for r in R2 if r['id'] == 'L19B1v')['lines'].remove('FzK'); next(r for r in R2 if r['id'] == 'L19A1')['lines'].append('FzK')
    power['t2 FzK given the origin of (A1v)'] = bool(inventory_check(R2, inv)[0])
    R3 = copy.deepcopy(ROWS); next(r for r in R3 if r['id'] == 'L22')['forms'].append('sqrt(CZ)')
    power['t3 sqrt(CZ) added to the ring row'] = bool(inventory_check(R3, inv)[0])
    st = steps()
    out = {'model': MODEL, 'B1m read with X1_B1(eta) (results_EA/ea_convex.json)': out_b1m, 'rows': len(ROWS), 'lines covered': len(origin), 'the 37 lines read from the code': len(inv),
           'inventory problems (must be empty)': probs, 'line -> origin rows': origin, 'power (each must be caught)': power, 'elementary steps': st,
           'rows that need eta <= 1/ell as an inequality': [r['id'] for r in ROWS if 'no' in r['ok'] and 'yes' not in r['ok'].split(';')[0]],
           'table': ROWS}
    out['ok'] = bool(not probs and len(origin) == 37 and all(power.values()) and st['all elementary checks as expected'])
    os.makedirs(os.path.join(ROOT, 'results_DZ'), exist_ok=True)
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_lemma_table.json'), 'w'), indent=1, ensure_ascii=False)
    tex = os.environ.get('DZ_TEX_OUT')
    if tex: open(tex, 'w').write(latex(ROWS))
    print(json.dumps({k: v for k, v in out.items() if k not in ('table', 'line -> origin rows')}, indent=1)[:3000])
    return out


if __name__ == '__main__':
    main()
