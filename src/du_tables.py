"""Stage DU: the three tables of App. C of the paper I draft, written from the records (results/du_fix.json: the interval proofs with the corrected
number 9.549).  Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
  table_cond18()  -> the 18 conditions of Proposition 6 (narrow): smallest value on [55.26, 1e6] (where) and on the tail;
  table_quoted48() -> the 48 quoted numbers with their worst value;
  table_cond35()  -> the 35 conditions of Proposition 14 (wide), smallest/largest value over the 6,953 pieces.
python3 du_tables.py  -> writes paperI/sections/C_tables.tex (input by C_constants.tex)."""
import json, os, sys, math
HERE = os.path.dirname(os.path.abspath(__file__))
REC = os.path.join(HERE, 'results', 'du_fix.json')

C18 = [('Case I (Fz): c1F - K_F/sqrt(b) - c1 (must be >= 0)', r'Case~I (Fz): $c_{1F}-K_F/\sqrt b-c_1\ge0$'),
       ('Case I (Tz-B2): [(1 - a2k - 1e-6) cK c_T sqrt(ell) - c_B2]/sqrt(ell) (must be >= 0)', r'Case~I (Tz-B2): $[(1-0.04616-10^{-6})c_Kc_T\sqrt\ell-c_{B2}]/\sqrt\ell\ge0$'),
       ('[c_kap ell 4 - 16]/(4 ell) (must be > 0)', r'(c2): $(4c_\kappa\ell-16)/(4\ell)>0$'),
       ('16 b_II (must be <= 1)', r'(c1): $16b_{\rm II}\le1$'),
       ('II-ch: slack (must be >= 0)', r'(II-ch): margin $\ge0$'),
       ('II-s: slack (must be >= 0)', r'(II-s): margin $\ge0$'),
       ('m1: slack 1 (must be >= 0)', r'(m1): margin $\ge0$'),
       ('m1: [Th*/sqrt2 - (mT + Tm)]/ell (must be >= 0)', r'(m1): $[\Theta^*/\sqrt2-(m_T+T)]/\ell\ge0$'),
       ('m3: 16 b e^mu at mu_n (must be <= 1)', r'(m3): $16be^\mu\le1$ at $\mu_n$'),
       ('m3: [c_J ell e^mu - 16 mu^2 E_J^2 r]/(ell e^mu) at mu_n, r = 1/4 (must be > 0)', r'(m3): $[c_J\ell e^\mu-16\mu^2E_J^2r]/(\ell e^\mu)>0$'),
       ('m3: slack (must be >= 0)', r'(m3): margin $\ge0$'),
       ('b.1 second pass: [E_CM formula - derived bound]/((1 + 3.445 e^{-mu/2})^2 t) at mu_n (must be >= 0)', r'(b.1) second pass ($\ell$ times) $\ge0$'),
       ('b.5: mT + Tbar (must be <= 1.002)', r'(b.5): $m_T+\bar T\le1.002$'),
       ('beta-case: log(u^3 v lower bound/U_max^4) (must be >= 0)', r'($\beta$): $\ln(u^3v/U^4)\ge0$'),
       ('N: 2.5 + 2 dl_0 - a0/th1 (must be >= 0)', r'(N): $2.5+2\delta_0-a_0/\theta_1\ge0$'),
       ('N0: th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II)) (must be >= 0)', r'(N0): $\theta_1(1-15/\ell)^{-1/2}-(m_T+\bar T)\ge0$'),
       ('N0: 3.75 - a0/(2 th1) (must be >= 0)', r'(N0): $3.75-a_0/(2\theta_1)\ge0$'),
       ('F: left - right (must be >= 0)', r'(F): left $-$ right $\ge0$')]

Q48 = {'F1: P <=': r'(F1) $P$', 'w16': r'$w_{16}$', 'eps1_max': r'$\varepsilon_1$', 'epsh_max': r'$\varepsilon_h$', 'c_S': r'$c_S$',
       'R4: constants/sigma <=': r'(R4) constant lines$/\sigma$', 'R4: e0 needed': r'(R4) $e_0$ needed', 'th_bg': r'$\sqrt{m_1m_4\omega}$', 'c1F': r'$c_{1F}$',
       'R5: K_F/sqrt(b) <=': r'(R5) $K_F/\sqrt b$', 'c_s': r'$c_s$', 'c_B2/sqrt(ell)': r'$c_{B2}/\sqrt\ell$', 'kf (b < 0.1)': r'$k_f$ ($b<0.1$)', 'cK': r'$c_K$',
       'Case I (Tz-B2): A2k/cKz <=': r'A2k$/$cKz (Case~I)', 'cb ell': r'$c_b\ell$', 'P_II': r'$P_{\rm II}$', 'b_II ell': r'$b_{\rm II}\ell$', 'brk (Case II)': r'brk (Case~II)',
       'kf (Case II)': r'$k_f$ (Case~II)', 'tc': r'$t_c$', 'T_max ell': r'$T\ell$', 'c_kap': r'$c_\kappa$', 'c_u': r'$c_u$', 'vth0': r'$\vartheta_0$',
       'm1: mu ell <': r'(m1) $\mu\ell$', 'rhobar (xi >= 8)': r'$\bar\varrho$ ($\xi\ge8$)', 'x_n': r'$x_n$', 'mu_n': r'$\mu_n$', 'c_J': r'$c_J$',
       'm3: log Ch(ell, mu_n)': r'(m3) $\ln\mathrm{Ch}$ ($\mathrm{Ch}\ge17$)', 'x0 (certified lower bound)': r'$x_0$', 'mu_II': r'$\mu$ in (m4)',
       'r bound coefficient': r'(b.4) coefficient of $r$', 'm4: factor of K': r'(b.4) factor', 'eps1 ell^2': r"$\varepsilon_1'\ell^2$", 'U_max': r'$U$',
       'b.2: G/sigma at mu = ell + ln ell <=': r'(b.2) $G/\sigma$', 'c_G': r'$c_G$', 'b.5: u lower bound (kappa_b = kappa), ell >= 397.6, mu >= x0 ell': r'(b.5) $u$',
       'b.4: r <= (at mu_II)': r'(b.4) $r$', 'II-s: log(a_s/sigma) <=': r'(II-s) $\ln(a_s/\sigma)$', 'II-ch: A2k + B2a relative to cKz <=': r'(II-ch) (A2k$+$B2a)$/$cKz',
       'm4: m1 after (b.4) >=': r'$m_1$ after (b.4)', 'm4: m4 after (b.4) >=': r'$m_4$ after (b.4)', 'm4: m5 after (b.4) >=': r'$m_5$ after (b.4)', 'c_k': r'$c_k$',
       'b.1 first pass: P/(mu e^-mu) <=': r'(b.1) first pass $P/(\mu e^{-\mu})$'}

C35 = {'written-in: (b.5) b < ell^4 sigma^2 <= 1e-100': r'(w1) $\ell^4\sigma^2\le10^{-100}$', 'written-in: A2k/cKz coefficient 2/((1 - eta) fl k_f) <= 2.1 (Case II)': r'(w3) $2/((1-\eta)\mathrm{fl}\,k_f)\le2.1$',
       'written-in: II-ch: (A2k + B2a)/cKz <= 1e-3': r'(w4) (A2k$+$B2a)$/$cKz$\le10^{-3}$', 'written-in: II-s: log(a_s/sigma) <= -20.73 (a_s <= 1e-9 sigma)': r'(w5) $\ln(a_s/\sigma)\le-20.73$',
       'written-in: Case I (Tz-B2): B2a/cKz <= 1e-6': r'(w6) B2a$/$cKz$\le10^{-6}$',
       'R1: sum/P1 <= 0.52 es': r'(R1) sum$/$P1$/\mathrm{es}\le0.52$', 'R3 (a <= 1): S/P4z <= 0.48 es': r'(R3) $a\le1$, $/\mathrm{es}\le0.48$', 'R3 (a >= 1): S/P1 <= 0.48 es': r'(R3) $a\ge1$, $/\mathrm{es}\le0.48$',
       'tiny: (d4 + N4G)/P2z / es_sigma <= 1': r'(d4$+$N4G)$/$P2z$/\mathrm{es}_\sigma\le1$', 'tiny: B1l/P2z / es_sigma (mu <= 2 ell) <= 1': r'B1l$/$P2z$/\mathrm{es}_\sigma\le1$',
       'tiny: B1c/(Gam2 G) / es_sigma <= 1': r'B1c$/(\Gamma_2G)/\mathrm{es}_\sigma\le1$', 'tiny: X1^2/ell <= 1': r'$X_1^2/\ell\le1$', 'tiny: B1m/P2z at a_L / es_sigma (mu <= 2 ell) <= 1': r'B1m$/$P2z at $a_L$, $/\mathrm{es}_\sigma\le1$',
       'R4: e0 needed <= e0': r'(R4) $e_0$ needed$/e_0\le1$', 'input: F1: P <= 0.7008': r'(F1) $P\le0.7008$', 'input: b.1 first pass P/(mu e^-mu) <= 9.18': r'(b.1) $P/(\mu e^{-\mu})\le9.18$',
       'b.2: c_G sqrt(ell) > G/sigma at mu = ell + ln ell': r'(b.2) $(G/\sigma)/(c_G\sqrt\ell)<1$', 'b.5: mu_II >= 6': r'(b.5) $\mu\ge6$', 'b.5: kappa_b mu < 1 (both bounds)': r'(b.5) $\kappa_b\mu<1$',
       'b.5: u > max(6, U_max) where kappa_b = kappa': r'(b.5) $u$, $\kappa_b=\kappa$', 'b.5: log u - log max(6, U_max) > 0 where kappa_b = 16 b e^mu/mu': r'(b.5) $\ln u-\ln\max(6,U)$, $\kappa_b=16be^\mu/\mu$',
       'b.5: ell >= 398, so 2.5e10 <= 398^4 <= ell^4 (B < ell^4 in the whole room)': r'(b.5) $\ell\ge398$'}


def fmt(v):
    if v == 0: return '$0$'
    if isinstance(v, bool): return str(v)
    a = abs(v)
    if 1e-3 <= a < 1e5: s = ('%.4g' % v)
    else:
        m, e = ('%.3e' % v).split('e'); return '$%s\\times10^{%d}$' % (m.rstrip('0').rstrip('.'), int(e))
    return '$%s$' % s


def where(x): return '$55.26$' if abs(x - 55.26) < 1e-9 else ('$960.8$' if abs(x - 960.8) < 1e-9 else fmt(x))


def build():
    n = json.load(open(REC)); A = n['(A) record']; wa = A['worst over [55.26, 1e6] (ok, value, at the left end of the piece)']; tl = A['tail [1e6, inf): values']
    B = n['(B) record']['c_B = 1, B_m = 8 ell_a + 100']['worst value of every condition (ok, value, left end of the piece)']
    rows18 = ['%s & %s (%s) & %s\\\\' % (lab, fmt(wa[k][1]), where(wa[k][2]), fmt(tl[k]) if k in tl and tl[k] is not None else fmt(tl[k.replace('N0: th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II)) (must be >= 0)', 'N0: [th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II))]/t (must be >= 0)')]) + ' ($\\ell$ times)') for k, lab in C18]
    q = [k for k in wa if k.startswith('quoted: ')]
    rows48 = []
    for k in q:
        body = k[len('quoted: '):]; name, sense, bound = body.rsplit(' ', 2)
        lab = Q48.get(name)
        if lab is None: raise KeyError(name)
        rows48.append('%s & $%s %s$ & %s\\\\' % (lab, '\\le' if sense == '<=' else '\\ge', bound, fmt(wa[k][1])))
    rows35 = ['%s & %s\\\\' % (C35.get(k) or k, fmt(v[1])) for k, v in B.items()]
    for k, lab in C18[:13]:
        pass
    t18 = ('\\begin{table*}\n\\caption{The 18 conditions of Proposition~\\ref{prop:narrow}: the smallest value (the largest for upper bounds) over the $9{,}809$ pieces of $[55.26,10^6]$, at the left end of the piece shown, and on the tail $[10^6,\\infty)$ (the conditions (N0) and (b.1) on the tail in the forms multiplied by $\\ell$ described in the text). From \\code{results/du\\_fix.json}.}\n'
           '\\label{tab:cond18}\n\\begin{ruledtabular}\n\\small\n\\begin{tabular}{p{0.5\\textwidth}p{0.24\\textwidth}p{0.16\\textwidth}}\ncondition & $[55.26,10^6]$ (at $\\ell$) & tail\\\\ \\hline\n'
           + '\n'.join(rows18) + '\n\\end{tabular}\n\\end{ruledtabular}\n\\end{table*}\n')
    half = (len(rows48) + 1) // 2
    t48 = ('\\begin{table*}\n\\caption{The 48 numbers quoted in Sec.~\\ref{sec:narrow}: the bound used and the worst value over the pieces of $[55.26,10^6]$ (interval arithmetic; the tail $[10^6,\\infty)$ is checked as well). From \\code{results/du\\_fix.json}.}\n'
           '\\label{tab:quoted48}\n\\begin{ruledtabular}\n\\small\n\\begin{tabular}{p{0.19\\textwidth}p{0.08\\textwidth}p{0.13\\textwidth}p{0.19\\textwidth}p{0.08\\textwidth}p{0.13\\textwidth}}\nquantity & bound & worst & quantity & bound & worst\\\\ \\hline\n'
           + '\n'.join(a[:-2] + ' & ' + b for a, b in zip(rows48[:half], rows48[half:] + ['& & \\\\'] * (half - len(rows48[half:]))))
           + '\n\\end{tabular}\n\\end{ruledtabular}\n\\end{table*}\n')
    t35 = ('\\begin{table*}\n\\caption{The 35 conditions of Proposition~\\ref{prop:wide} with $B_m=8\\ell_a+100$: the worst value over the $6{,}953$ pieces (the smallest for lower bounds, the largest for upper bounds). The $13$ conditions of Table~\\ref{tab:cond18} that do not belong to (b.6) appear with the same names. From \\code{results/du\\_fix.json}.}\n'
           '\\label{tab:cond35}\n\\begin{ruledtabular}\n\\small\n\\begin{tabular}{p{0.27\\textwidth}p{0.12\\textwidth}p{0.27\\textwidth}p{0.12\\textwidth}}\ncondition & worst & condition & worst\\\\ \\hline\n')
    lab35 = []
    names18 = dict(C18)
    for k, v in B.items():
        lab35.append('%s & %s' % (C35.get(k) or names18.get(k, k), fmt(v[1])))
    h = (len(lab35) + 1) // 2
    t35 += '\n'.join(a + ' & ' + b + '\\\\' for a, b in zip(lab35[:h], lab35[h:] + [' & '] * (h - len(lab35[h:]))))
    t35 += '\n\\end{tabular}\n\\end{ruledtabular}\n\\end{table*}\n'
    return t18, t48, t35, len(rows48), len(lab35), len(rows18)


if __name__ == '__main__':
    t18, t48, t35, n48, n35, n18 = build()
    assert (n18, n48, n35) == (18, 48, 35), (n18, n48, n35)
    open(os.path.join(HERE, 'paperI', 'sections', 'C_tables.tex'), 'w', encoding='utf-8').write('% generated by du_tables.py from results/du_fix.json\n' + t18 + t48 + t35)
    print('written', n18, n48, n35)
