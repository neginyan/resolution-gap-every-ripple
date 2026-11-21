"""Stage DA 2.4: LINE-BY-LINE AUDIT OF THE OLD OPTIONS T, B, F of the local-route table (cz_cells.py = cy_cells.py + the two CZ repairs) against
Lemma R_theta written out once more, in its CLASS form, in 50-digit decimals.  Python 3.11 grammar.
THE LEMMA (co_remainders.py docstring = Lemma R_theta of stage CO, co_rtheta.lemma_R_theta) with the class bounds of the table:
  sqrt(x) N1 -> U1, x N2 -> U2 (cl_link.window_consts), |R_theta| -> eta = 1/ell, Qbar = 1/4, E1 = P/(2x), E0 = P/(2 mu), x E1^{(2tau)} -> U2 theta_{2tau}(0)
  with tau = 5e11/beta (the smallest tau of the box, as the table's N10), M2 = M2_const(beta, tau).
  gamma-tilde (the pointwise bound of |sigma^2 G|, G = h''/h - (h'/h)^2 written with the envelope factors):
      gamma-tilde <= x (E N2 + E^2 N1^2/(1-eta))/(1-eta) + sigma sqrt(x) (|w|/s^2) E N1 (1 + eta E/(1-eta))/(1-eta)
  [ |h''/h| <= E k'^2 |R''|/(1-eta), (h'/h)^2 <= E^2 k'^2 R'^2/(1-eta)^2 ]: the term x E N2 carries 1/(1-eta) (co_rtheta.lemma_R_theta and the comment
  of co_remainders.py; the formula line of co_remainders.catalogue and the table have U2 k_E without it -- see FLAG_GGT).
THE PIECES (Num units, i.e. Z Num = 2 A_w + (1/2)[(B)+(F)+(X)+(L)]; den units for den):
  gains   P1 = 2 sigma^2/L^2,  P2 = 2 sigma^2 D0/(1+eta),  P34 = (b/2)(1 - eta k_E) Psi_0,  hF = (W/(2(1+eta)))(1 - e^{-se2/4}),
          chirp = (W/(2(1+eta))) e^{-se2/4} (y/2) kappa
  losses  N1 ... N16 of co_remainders (N5 is inside P34; N8 = the B1 form of F_rem; B2 = the B2 form (W/(2(1-eta)))(c0 + sigma^2 sqrt(se2/pi)/L^2)),
          'N6+N15' = N6 + N15
  den     d1 = b(1 + eta k_E) + 0.184 b k_E,  d2 = W/(1-eta),  d3 = sigma^2 (1/L^2 + Lambda_1 (with eta)),  d4 = sigma^2 D0/(1-eta)
THE TABLE'S LINES at a zero-width box of the same state, each evaluated at a' = 4 r A/sigma as c sigma^p (type), type L a', C 1, S sqrt(a'), M 1/sqrt(a'),
  H 1/(a' + sigma), grouped by the comment of the source line (the groups above).  CHECK: every loss group of the table >= the lemma's piece, every gain
  group <= the lemma's piece, every den group/(gamma sigma) >= the den piece (relative tolerance 1e-12).
POWER: copies of cz_cells.py with ONE coefficient changed (a loss made 1 % smaller, a gain 1 % larger, or more where the line has its own slack:
see WRONG_EDITS) must each be caught.
-> results/da_linecheck.json"""
import importlib.util, json, math, os, re, sys
from decimal import Decimal as Dc, getcontext
import numpy as np
getcontext().prec = 50
HERE = os.path.dirname(os.path.abspath(__file__))
import cz_cells as Z0
from co_remainders import M2_const

PI = Dc('3.14159265358979323846264338327950288419716939937510'); QB = Dc('0.25'); C184 = Dc('0.184'); E1H = Dc(-1) / 2
SQ2 = Dc(2).sqrt()
FLAG_GGT = {'with': True}       # True: the lemma's gamma-tilde (x N2 E/(1-eta)); False: the catalogue's line (without 1/(1-eta))


def dexp(x): return Dc(x).exp()


def om(x):
    x = Dc(x)
    return x * (1 - x / 2 + x * x / 6 - x ** 3 / 24) if abs(x) < Dc('1e-12') else 1 - (-x).exp()


def lemma_pieces(ell, mu, lB, lr, kap, P, lA):
    ell, mu, lB, lr, kap, P, lA = (Dc(repr(float(t))) for t in (ell, mu, lB, lr, kap, P, lA))
    sig = dexp(-ell); b = dexp(lB) * sig ** 2; r = dexp(lr); A = dexp(lA); eta = 1 / ell
    s2 = sig ** 2 / A; L2 = s2 / r; s = s2.sqrt(); L = L2.sqrt()
    se2 = s2 / (2 + r); gs = (r / (2 + r)).sqrt(); kE = (r / (1 + r)).sqrt(); seE = s2 / (1 + r)
    U1 = QB * (2 * ell + Dc('3.1')).sqrt() + Dc('1e-6'); U2 = QB * (2 * ell + Dc('3.1')) + Dc('1e-4')
    gP = (U2 * (1 + QB) + U1 ** 2 + U1 * (1 + 2 * QB) / Dc(1).exp().sqrt()) / (1 - QB) ** 2
    beta_ = dexp(lB); tau = Dc('5e11') / beta_; x = b * tau
    y = (1 - b) ** 2 * sig ** 2 / (2 * b); e = dexp(-y / 2); bt = (tau * y).sqrt()
    W = gs * P / 2; E0 = P / (2 * mu); D0 = E0 * gs * se2 / s2 ** 2
    xi = sig * U1 / (1 - QB); zeta = sig ** 2 * eta * dexp(E1H) / (s * (1 - eta)); xie = xi / SQ2
    c0 = (xi + zeta) / SQ2; c1 = sig ** 2 / (SQ2 * L2)
    rC = (xi + zeta + sig ** 2 * (2 / PI).sqrt() / L) / SQ2; rCE = kE * (xi + zeta + sig ** 2 * (2 * seE / PI).sqrt() / L2) / SQ2
    eL = dexp(-L2 / 4); eSE = dexp(-seE / 4); ese2 = dexp(-se2 / 4)
    lm1y = (y + y * y / 2 + y ** 3 / 3 + y ** 4 / 4) if y < Dc('1e-10') else -(1 - y).ln()     # -ln(1 - y) without cancellation (y can be 1e-134)
    Psi0 = om(y / 2 + L2 / 4 + lm1y)
    one_m_eeSE = om(y / 2 + seE / 4); one_m_eese2 = om(y / 2 + se2 / 4); one_m_e = om(y / 2)
    J2 = (1 / L2) * (1 + eta * kE * r / (1 + r)) + 2 * eta * kE * seE / (L2 * s2) + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta))
    Jup = (1 / L2) * (1 + eta * kE * r / (1 + r)) + 2 * eta * kE * seE / (L2 * s2) + D0 / (1 - eta)
    M4 = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2 + 3 * se2 * D0 / (1 - eta)
    M2 = Dc(repr(M2_const(bt, tau)))
    g2 = (1 / (1 - eta)) if FLAG_GGT['with'] else Dc(1)
    Ggt = U2 * kE * g2 + U1 ** 2 * gs / (1 - eta) ** 2 + sig * U1 * kE * (2 * seE / PI).sqrt() * (1 + eta / (1 - eta)) / (s2 * (1 - eta))
    GgtPhi = (U2 * kE * one_m_eeSE * g2 + U1 ** 2 * gs * one_m_eese2 / (1 - eta) ** 2
              + sig * U1 * (1 + eta / (1 - eta)) / (s2 * (1 - eta)) * (one_m_e * kE * (2 * seE / PI).sqrt() + e * kE * (2 / PI).sqrt() * seE * seE.sqrt() / 2))
    GgtChi = Ggt * (xi + zeta) / SQ2 + sig ** 2 * gP * (2 / PI).sqrt() / (SQ2 * L)
    Lam1 = eta * kE * (2 + r) / ((1 + r) * L2)
    g = {'P1': 2 * sig ** 2 / L2, 'P2': 2 * sig ** 2 * D0 / (1 + eta), 'P34': b / 2 * (1 - eta * kE) * Psi0,
         'hF': W / (2 * (1 + eta)) * om(se2 / 4), 'chirp': W / (2 * (1 + eta)) * ese2 * (y / 2) * kap}
    l = {'N1': 2 * sig ** 2 * Lam1, 'N2': sig ** 4 / (4 * b) * (1 - b) ** 2 * J2, 'N3': sig ** 2 / 2 * M4,
         'N4': sig ** 2 * Dc('1.5') * ((xi ** 2 + zeta ** 2) * Jup + sig ** 4 / L2 ** 2 * M4),
         'N6+N15': b / 2 * eta * kE * ((1 - y) * eSE * om(y / 2 + L2 / 4 - seE / 4) + y / 2) + Dc('0.5') * C184 * b * kE * om(seE / 4),   # eSE - e eL = eSE (1 - e^{-(y/2 + L^2/4 - seE/4)})
         'N7': b / 2 * (1 + eta) * (1 - y) * rC,
         'B1': W / (2 * (1 - eta)) * ((c0 * (2 * se2 / PI).sqrt() + c1 * se2) / SQ2 + c0 ** 2 + c1 ** 2 * se2),
         'B2': W / (2 * (1 - eta)) * (c0 + sig ** 2 * (se2 / PI).sqrt() / L2),
         'N9': W / 2 * ese2 * xie * (y * kap).sqrt(),
         'N10': Dc('0.5') * Dc('0.51') * y ** 2 * gs * U2 * (1 + (PI / tau).sqrt()),
         'N11': sig ** 2 / 2 * (1 - b) * (W / (1 - eta) + C184 * b * kE),
         'N12': sig ** 3 / 2 * (1 - b) * (P / 2).sqrt() * kE * (2 * seE / PI).sqrt() / (s2 * (1 - eta)),
         'N13': sig ** 2 / 2 * (1 - b) * (1 + eta) * (GgtPhi + GgtChi),
         'N14': Dc('0.5') * (1 + y).sqrt() * ((P * b).sqrt() * rCE + sig * b.sqrt() * (1 + eta) * Ggt),
         'N16': Dc('0.5') * (y / 2) * b * QB * kE * M2}
    d = {'d1': b * (1 + eta * kE) + C184 * b * kE, 'd2': W / (1 - eta), 'd3': sig ** 2 * (1 / L2 + Lam1), 'd4': sig ** 2 * D0 / (1 - eta)}
    return g, l, d, {'sig': sig, 'gam': (1 + Dc('2.5e-4')) / ell.sqrt(), 'r': r, 'A': A}


# ------------------------------------------------------------------ the table's lines
RULES = [('N6+N15', r"# N6 y-part"), ('P1', r"# P1\b"), ('P2', r"# P2\b"), ('P3', r"# P3\b"), ('d1', r"# d1"), ('d2', r"# d2"), ('d3', r"# d3"), ('d4', r"# d4"),
         ('N1', r"# N1\b"), ('N2', r"# N2"), ('N3', r"# N3\b"), ('N4', r"# N4\b|-LD\(1\.5\) \* \(\(X1 \*\* 2 \+ CZ\) \* Gmu"), ('N7', r"# N7"),
         ('N11', r"# N11"), ('N12', r"# N12"), ('N13', r"f13|hneg13"), ('N14', r"sy \*"), ('N16', r"# N16")]


def classify(mod):
    src = open(mod.__file__).read().splitlines(); out = {}
    for i, t in enumerate(src, 1):
        if 'add(' not in t: continue
        for nm, pat in RULES:
            if re.search(pat, t): out[i] = nm; break
    return out


def ld2dec(v): return Dc(np.format_float_scientific(np.longdouble(v), precision=25, unique=False))


def table_groups(mod, cls, ell, mu, lB, lr, kap, P, lA, opt):
    X = np.array([[math.log(mu), math.log(mu), lr, lr, lB, lB, math.log(kap), math.log(kap), ell, ell]])
    lG = np.array([math.log(P) + 0.5 * (lr - math.log(2 + math.exp(lr)))])
    cap = {}; mod.DIAG['CAPTURE'] = cap
    try:
        with np.errstate(all='ignore'): mod.terms_cell(X, 0.0, True, lGc=lG, opts=(opt,), lGref=lG)
    finally:
        mod.DIAG['CAPTURE'] = None
    sig = dexp(-Dc(repr(ell))); ap = 4 * dexp(Dc(repr(lr)) + Dc(repr(float(lA)))) / sig
    ty = {'L': ap, 'C': Dc(1), 'S': ap.sqrt(), 'M': 1 / ap.sqrt(), 'H': 1 / (ap + sig)}
    grp = {}
    def put(nm, t, p, c): grp[nm] = grp.get(nm, Dc(0)) + ld2dec(c) * sig ** Dc(repr(float(p))) * ty[t]
    for line, t, p, c, g in cap['terms']:
        if g == 'z': continue
        nm = cls.get(line)
        if nm is None: raise RuntimeError('unclassified table line %d' % line)
        put(nm, t, p, c[0])
    for nm, t, p, c in cap['opt'][opt]:
        nm = {'N6+N15': 'N6+N15'}.get(nm, nm)
        nm = {'P4': 'P3', 'B2c': 'B2', 'B2s': 'B2', 'B1m': 'B1', 'B1c': 'B1', 'B1l': 'B1', 'hK': 'chirp', 'cK': 'chirp'}.get(nm, nm)
        put(nm, t, p, c[0])
    return grp


def compare(grp, g, l, d, info, opt):
    """ratios table/lemma: gains must be <= 1, losses >= 1, den/gamma >= 1.  Returns list of (name, ratio, ok)."""
    out = []
    m = {'P1': 'P1', 'P2': 'P2', 'P3': 'P34', 'hF': 'hF', 'chirp': 'chirp'}
    for nm, ln in m.items():
        if nm in grp and g[ln] > 0:
            rt = grp[nm] / g[ln]; out.append(('gain ' + nm, float(rt), rt <= 1 + Dc('1e-12')))
    for nm in ('N1', 'N2', 'N3', 'N4', 'N6+N15', 'N7', 'N9', 'N10', 'N11', 'N12', 'N13', 'N14', 'N16', 'B1', 'B2'):
        if nm in grp and l[nm] > 0:
            rt = -grp[nm] / l[nm]; out.append(('loss ' + nm, float(rt), rt >= 1 - Dc('1e-12')))
    for nm in ('d1', 'd2', 'd3', 'd4'):
        if nm in grp and d[nm] > 0:
            rt = -grp[nm] / (info['gam'] * info['sig'] * d[nm]); out.append(('den ' + nm, float(rt), rt >= 1 - Dc('1e-12')))      # the den lines are -gamma sigma den (Num units)
    return out


def sample(rng, ell):
    if ell < 20:
        lB = rng.uniform(math.log(300.0), math.log(0.49) + 2 * ell); lr = rng.uniform(math.log(1e-4), math.log(0.25))
        mu = math.exp(rng.uniform(math.log(1e-2), math.log(30.0))); kap = math.exp(rng.uniform(math.log(1e-3), math.log(1e3)))
        return mu, lB, lr, kap, 2 * mu * 0.0625 * math.exp(rng.uniform(-6, 0))
    lB = rng.uniform(math.log(2.6e10), math.log(0.49) + 2 * ell); lr = rng.uniform(-3 * ell, math.log(0.25))
    mu = math.exp(rng.uniform(math.log(1e-3), math.log(4 * ell))); kap = math.exp(rng.uniform(math.log(1e-6), math.log(1e6)))
    return mu, lB, lr, kap, 2 * mu * 0.0625 * math.exp(rng.uniform(-40, 0))


def audit(mod, n=60, seed=11, ells=(4.0, 6.0, 55.26, 300.0, 960.8)):
    cls = classify(mod); rng = np.random.default_rng(seed)
    saved = (dict(mod.FIX), dict(mod.ZOPT)); mod.FIX.update(N9=True, SAND=True)
    stats = {}; bad = []
    try:
        for i in range(n):
            ell = float(rng.choice(ells)); st = sample(rng, ell); lA = float(rng.uniform(math.log(4.0) - 3 * ell, 0.0))
            g, l, d, info = lemma_pieces(ell, *st, lA)
            for opt in ('T', 'B', 'F'):
                grp = table_groups(mod, cls, ell, *st, lA, opt)
                for nm, rt, ok in compare(grp, g, l, d, info, opt):
                    s = stats.setdefault(nm, [math.inf, -math.inf, 0]); s[0] = min(s[0], rt); s[1] = max(s[1], rt); s[2] += 1
                    if not ok: bad.append({'line': nm, 'ratio': rt, 'option': opt, 'ell': ell, 'state': list(st), 'logA': lA})
    finally:
        mod.FIX.clear(); mod.FIX.update(saved[0]); mod.ZOPT.clear(); mod.ZOPT.update(saved[1])
    return bad, {k: {'min ratio': v[0], 'max ratio': v[1], 'comparisons': v[2]} for k, v in stats.items()}


def audit_low(mod, n=40, seed=13, ells=(4.0, 6.0, 55.26, 300.0, 960.8)):
    """DA 2.3: the low side of the a'-split (DIAG['ARANGE'] = ('lo', theta)): at states with a' <= a_c the table's F main line (now type C) must be
    <= the lemma's (W/(2(1+eta)))(1 - e^{-se2/4}); every other line as in audit()."""
    cls = classify(mod); rng = np.random.default_rng(seed); bad = []; rts = []
    saved = (dict(mod.FIX), dict(mod.ZOPT), mod.DIAG['ARANGE']); mod.FIX.update(N9=True, SAND=True)
    try:
        for i in range(n):
            ell = float(rng.choice(ells)); st = sample(rng, ell); th = float(rng.choice([0.25, 1.0, 4.0]))
            mu, lB, lr, kap, P = st; r = math.exp(lr)
            lac = math.log(th) - ell + lr - math.log(2 + r)                                  # log a_c (zero-width box)
            lap = lac - float(rng.uniform(0, 30)); lA = lap - ell - math.log(4) - lr        # a' = 4 r A/sigma, so A = sigma a'/(4 r)
            if lA > 0 or lA < math.log(4.0) - 3 * ell: continue
            g, l, d, info = lemma_pieces(ell, *st, lA)
            mod.DIAG['ARANGE'] = ('lo', th)
            for opt in ('T', 'B'):
                grp = table_groups(mod, cls, ell, *st, lA, opt)
                for nm, rt, ok in compare(grp, g, l, d, info, opt):
                    if nm == 'gain hF': rts.append(rt)
                    if not ok: bad.append({'line': nm, 'ratio': rt, 'option': opt, 'ell': ell, 'theta': th})
            mod.DIAG['ARANGE'] = None
    finally:
        mod.FIX.clear(); mod.FIX.update(saved[0]); mod.ZOPT.clear(); mod.ZOPT.update(saved[1]); mod.DIAG['ARANGE'] = saved[2]
    return bad, {'gain hF (low side) ratio min': min(rts) if rts else None, 'max': max(rts) if rts else None, 'comparisons': len(rts)}


# one coefficient changed per copy (the old string must occur once in cz_cells.py)
WRONG_EDITS = {
    'N1 x 0.99': ("add('L', 1, -2 * r_b * eta * kE_b * (2 + r_b)", "add('L', 1, -1.98 * r_b * eta * kE_b * (2 + r_b)"),
    'N3 x 0.99': ("add('C', 2, -(M4c + M4g) / 2)", "add('C', 2, -0.99 * (M4c + M4g) / 2)"),
    'N7 xi x 0.99': ("add('C', 3, -(B_b / 2) * (1 + eta) * X1 / math.sqrt(2), 'o')", "add('C', 3, -0.99 * (B_b / 2) * (1 + eta) * X1 / math.sqrt(2), 'o')"),
    'N11 W x 0.99': ("add('C', 2, -((G / 2) / (1 - eta)) / 2, 'o')", "add('C', 2, -0.99 * ((G / 2) / (1 - eta)) / 2, 'o')"),
    'N16 x 0.85 (its slack is 9.6 %)': ("add('C', 2, -LD(0.125) * QB * kE_b * M2, 'o')", "add('C', 2, -LD(0.10625) * QB * kE_b * M2, 'o')"),
    'N9 x 0.99': ("N9 = (G / 4) * (X1 * n9c)", "N9 = 0.99 * (G / 4) * (X1 * n9c)"),
    'P1 x 1.01': ("add('L', 1, 2 * r_a / r4b)", "add('L', 1, 2.02 * r_a / r4b)"),
    'hF x 1.01': ("hF = fl * (G / 4) * (r_a / (2 + r_a))", "hF = 1.01 * fl * (G / 4) * (r_a / (2 + r_a))"),
    'd1 x 0.99': ("add('C', 3, -gam * (B_b * (1 + (eta + LD(0.184)) * kE_b)))", "add('C', 3, -0.99 * gam * (B_b * (1 + (eta + LD(0.184)) * kE_b)))"),
    'B1c x 0.5': ("B1c = fF * (", "B1c = 0.5 * fF * ("),
    'N6 y-part x 0.99': ("if FIX['N6Y']: add('C', 2, -eta * kE_b / 4, 'o')", "if FIX['N6Y']: add('C', 2, -0.99 * eta * kE_b / 4, 'o')"),
    'N14 g2t dropped': ("    Ggt_C = U2 * kE_b * g2t + U1 ** 2", "    Ggt_C = U2 * kE_b + U1 ** 2"),
}


def wrong_module(name):
    src = open(Z0.__file__).read(); a, b = WRONG_EDITS[name]
    assert src.count(a) == 1, (name, src.count(a))
    d = os.path.join(os.environ.get('DA_SCRATCH', os.path.join(HERE, 'results', 'da_wrong_tables')), re.sub(r'\W', '_', name)); os.makedirs(d, exist_ok=True)
    fn = os.path.join(d, 'cz_cells_wrong.py'); open(fn, 'w').write(src.replace(a, b))
    spec = importlib.util.spec_from_file_location('cz_cells_wrong_' + re.sub(r'\W', '_', name), fn); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


def run(n=60):
    out = {}
    FLAG_GGT['with'] = True
    bad, st = audit(Z0, n); out['audit (lemma gamma-tilde with 1/(1-eta) on x N2 E)'] = {'bad': len(bad), 'first_bad': bad[:6], 'ratios': st}
    print('lemma form: bad', len(bad), {k: (round(v['min ratio'], 6), round(v['max ratio'], 4)) for k, v in st.items()}, flush=True)
    FLAG_GGT['with'] = False
    bad2, st2 = audit(Z0, n); out['audit (catalogue line of gamma-tilde, without it)'] = {'bad': len(bad2), 'first_bad': bad2[:6], 'ratios': st2}
    print('catalogue form: bad', len(bad2), flush=True)
    FLAG_GGT['with'] = True
    pw = {}
    for nm in WRONG_EDITS:
        m = wrong_module(nm); b_, _ = audit(m, max(12, n // 2), seed=21); pw[nm] = len(b_); print('  wrong', nm, len(b_), flush=True)
    out['power (wrong copies: violations found)'] = pw
    bl, sl = audit_low(Z0, max(20, n // 2)); out['audit of the low side of the a-split (DA 2.3)'] = {'bad': len(bl), 'first_bad': bl[:5], **sl}
    Z0.ZOPT['W'] = 'hfc2'
    try:
        bw, _ = audit_low(Z0, max(20, n // 2), seed=14)
    finally:
        Z0.ZOPT['W'] = None
    out['power (wrong copies: violations found)']['hfc2 (low-side constant doubled)'] = len(bw)
    print('low side: bad', len(bl), sl, 'wrong hfc2 caught', len(bw), flush=True)
    out['lines_classified'] = len(classify(Z0))
    json.dump(out, open(os.path.join(HERE, 'results', 'da_linecheck.json'), 'w'), indent=1, default=float)
    return out


if __name__ == '__main__':
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 60)


# ------------------------------------------------------------------ stage DC 2.1: BOTH SIDES of the a'-split of the stage (and the z-options' F main line)
def audit_high(mod, n=40, seed=17, ells=(4.0, 6.0, 55.26, 300.0, 960.8)):
    """DC 2.1: the HIGH side of the a'-split (DIAG['ARANGE'] = ('hi', theta)): at states with a' >= a_c every line of the options T, B must pass the
    same comparison with the lemma as in audit() (the F main line there must be the table's H form, <= (W/(2(1+eta)))(1 - e^{-se2/4})).
    The stage as written in DA (AR['hi_fix'] = False) must be caught here (its hF line exceeds the lemma's piece)."""
    cls = classify(mod); rng = np.random.default_rng(seed); bad = []; rts = []; tested = 0
    saved = (dict(mod.FIX), dict(mod.ZOPT), mod.DIAG['ARANGE']); mod.FIX.update(N9=True, SAND=True)
    try:
        for i in range(n * 4):
            if tested >= n: break
            ell = float(rng.choice(ells)); st = sample(rng, ell); th = float(rng.choice([0.25, 1.0, 4.0]))
            mu, lB, lr, kap, P = st; r = math.exp(lr)
            lac = math.log(th) - ell + lr - math.log(2 + r)                                  # log a_c (zero-width box)
            lap = lac + (float(rng.exponential(1.0)) if rng.random() < 0.5 else float(rng.uniform(0, 3 * ell)))    # a' >= a_c, near it and far above
            lA = lap - ell - math.log(4) - lr
            if lA > 0 or lA < math.log(4.0) - 3 * ell: continue
            tested += 1
            g, l, d, info = lemma_pieces(ell, *st, lA)
            mod.DIAG['ARANGE'] = ('hi', th)
            for opt in ('T', 'B'):
                grp = table_groups(mod, cls, ell, *st, lA, opt)
                for nm, rt, ok in compare(grp, g, l, d, info, opt):
                    if nm == 'gain hF': rts.append(rt)
                    if not ok: bad.append({'line': nm, 'ratio': rt, 'option': opt, 'ell': ell, 'theta': th, 'log a\' - log a_c': lap - lac})
            mod.DIAG['ARANGE'] = None
    finally:
        mod.FIX.clear(); mod.FIX.update(saved[0]); mod.ZOPT.clear(); mod.ZOPT.update(saved[1]); mod.DIAG['ARANGE'] = saved[2]
    return bad, {'gain hF (high side) ratio min': min(rts) if rts else None, 'max': max(rts) if rts else None, 'comparisons': len(rts), 'states': tested}


def zline_check(mod, n=40, seed=19, ells=(55.26, 300.0, 960.8)):
    """DC 2.1: the z-options' F main line on every branch of the stage (no stage / side lo / side hi, theta in {1/4, 1, 4}): it must have the same
    (type, power) as the F main line hF of option T on that branch and a coefficient <= it (the factor 1 - z0^2/2 <= 1); with audit()/audit_low()/
    audit_high() (hF <= the lemma's (W/(2(1+eta)))(1 - e^{-se2/4})) this bounds it by the pair lemma CZ-5's (1 - z0^2/2)(...)."""
    rng = np.random.default_rng(seed); bad = []; tested = 0
    saved = mod.DIAG['ARANGE']
    try:
        for i in range(n):
            ell = float(rng.choice(ells)); mu, lB, lr, kap, P = sample(rng, ell)
            X = np.array([[math.log(mu), math.log(mu), lr, lr, lB, lB, math.log(kap), math.log(kap), ell, ell]])
            lG = np.array([math.log(P) + 0.5 * (lr - math.log(2 + math.exp(lr)))])
            for side in (None, ('lo', 0.25), ('lo', 1.0), ('lo', 4.0), ('hi', 0.25), ('hi', 1.0), ('hi', 4.0)):
                mod.DIAG['ARANGE'] = side; cap = {}; mod.DIAG['CAPTURE'] = cap
                try:
                    with np.errstate(all='ignore'):
                        mod.terms_cell(X, 0.0, True, lGc=lG, opts=('T', 'Tz', 'Bz'), lGref=lG)
                finally:
                    mod.DIAG['CAPTURE'] = None
                hT = [z for z in cap['opt']['T'] if z[0] == 'hF'][0]
                for o in ('Tz', 'Bz'):
                    hz = [z for z in cap['optz'][o] if z[0].startswith('F main')][0]; tested += 1
                    if not (hz[1] == hT[1] and hz[2] == hT[2] and float(hz[3][0]) <= float(hT[3][0]) * (1 + 1e-15)):
                        bad.append({'option': o, 'side': side, 'z line': [hz[1], hz[2], float(hz[3][0])], 'T line': [hT[1], hT[2], float(hT[3][0])]})
    finally:
        mod.DIAG['ARANGE'] = saved
    return bad, tested


# ------------------------------------------------------------------ stage DD 2.1: THE PIECES OF THE STAGE AT MANY LEVELS ('mid', 'hiA') and B1 near a'_lo
def audit_levels(mod, n=40, seed=21, ells=(55.26, 300.0, 960.8), wrong=None, lq_choices=(0.5, 1.0, 2.0)):
    """DD 2.1: at states (zero-width boxes) the lines of the options T, B on a piece [a_1, a_2] containing a' (side 'mid': the constant form at the
    piece's RIGHT end) and on the top piece [a_1, a'_hi] (side 'hiA': the H form), against Lemma R_theta in 50 digits (compare()).
    wrong: a version of the piece's constant that must be caught ('left': theta from the LEFT end; 'top-left': the constant of the left end used on
    the top piece -- the constant form on a piece where it does not hold; a float: a log-factor)."""
    cls = classify(mod); rng = np.random.default_rng(seed); bad = []; rts = []; tested = 0
    saved = (dict(mod.FIX), dict(mod.ZOPT), mod.DIAG['ARANGE']); mod.FIX.update(N9=True, SAND=True)
    try:
        for i in range(n * 4):
            if tested >= n: break
            ell = float(rng.choice(ells)); st = sample(rng, ell); mu, lB, lr, kap, P = st
            lA = float(rng.uniform(math.log(4.0) - 3 * ell, 0.0)) if rng.random() < 0.5 else float(rng.uniform(-3 * ell, 0.0))
            if lA < math.log(4.0) - 3 * ell: continue
            lap = lA + ell + math.log(4) + lr                                           # log a' = log(4 r A/sigma)
            lq = float(rng.choice(lq_choices)); top = rng.random() < 0.25
            la2 = lap + float(rng.uniform(0, lq)); la1 = la2 - lq
            if wrong == 'top-left': top = True
            side = ('hiA', np.array([la1])) if top else ('mid', np.array([la1]), np.array([la2]))
            if wrong is not None:
                side = ('mid', np.array([la1]), np.array([lap + 50.0]), 'left') if wrong == 'top-left' else ('mid', np.array([la1]), np.array([la2]), wrong)
            tested += 1
            g, l, d, info = lemma_pieces(ell, *st, lA)
            mod.DIAG['ARANGE'] = side
            for opt in ('T', 'B'):
                grp = table_groups(mod, cls, ell, *st, lA, opt)
                for nm, rt, ok in compare(grp, g, l, d, info, opt):
                    if nm == 'gain hF': rts.append(rt)
                    if not ok: bad.append({'line': nm, 'ratio': rt, 'option': opt, 'ell': ell, 'side': side[0], 'wrong': wrong})
            mod.DIAG['ARANGE'] = None
    finally:
        mod.FIX.clear(); mod.FIX.update(saved[0]); mod.ZOPT.clear(); mod.ZOPT.update(saved[1]); mod.DIAG['ARANGE'] = saved[2]
    return bad, {'gain hF (pieces) ratio min': min(rts) if rts else None, 'max': max(rts) if rts else None, 'comparisons': len(rts), 'states': tested}


def levels_box_check(mod, n=300, seed=23, wrong=None):
    """DD 2.1: the constant of a 'mid' piece on BOXES WITH WIDTH (ell, r, beta, mu of positive width): the captured F main coefficient of option T
    must equal fl (G/4) (1 - e^{-1/theta_2}), theta_2 = a_2 (2 + r_a)/(sigma_lo r_a), recomputed here in 50 digits (fl: the captured coefficient of
    the same box without the stage, divided by (G/4) r_a/(2+r_a)); and 1 - e^{-1/theta_2} must be <= 1 - e^{-se2/4} at the box's worst state
    (sigma_lo, r_a, a' = a_2).  Wrong versions ('left', 'sigma_hi', 'r_b', a float) must fail one of the two."""
    rng = np.random.default_rng(seed); bad = 0; tested = 0; worst = math.inf
    saved = mod.DIAG['ARANGE']
    try:
        for i in range(n):
            ell_a = float(rng.uniform(55.0, 960.0)); ell_b = ell_a + float(rng.uniform(0.05, 1.0))
            lra = float(rng.uniform(-3 * ell_b, math.log(0.2))); lrb = min(math.log(0.25), lra + float(rng.uniform(0.1, 2.0)))
            lBa = float(rng.uniform(math.log(2.6e10), 2 * ell_a - 2)); lBb = lBa + float(rng.uniform(0.1, 2.0))
            lmu = float(rng.uniform(-3, 3)); lk = float(rng.uniform(-10, 5))
            Xb = np.array([[lmu, lmu + 0.5, lra, lrb, lBa, lBb, lk, lk + 1.0, ell_a, ell_b]]); lG, _ = mod.box_P(Xb)
            la0 = math.log(4.0) - ell_b + lra - math.log(2 + math.exp(lra)); la2 = la0 + float(rng.uniform(0, 3 * ell_b)); la1 = la2 - 1.0
            caps = []
            for side in (None, ('mid', np.array([la1]), np.array([la2])) + ((wrong,) if wrong is not None else ())):
                cap = {}; mod.DIAG['CAPTURE'] = cap; mod.DIAG['ARANGE'] = side
                try:
                    with np.errstate(all='ignore'): mod.terms_cell(Xb, 0.0, True, lGc=lG, opts=('T',), lGref=lG)
                finally:
                    mod.DIAG['CAPTURE'] = None; mod.DIAG['ARANGE'] = saved
                caps.append([z for z in cap['opt']['T'] if z[0] == 'hF'][0])
            h0, h1 = caps
            if not (h1[1] == 'C' and float(h1[2]) == 0.0): bad += 1; continue
            tested += 1
            sig_lo = dexp(-Dc(repr(ell_b))); ra = dexp(Dc(repr(lra))); a2 = dexp(Dc(repr(la2)))
            inv_th2 = sig_lo * ra / ((2 + ra) * a2)
            cF = om(inv_th2)
            base = ld2dec(h0[3][0]) / (ra / (2 + ra))                                # fl (G/4)
            got = ld2dec(h1[3][0]) / base
            rel = abs(got - cF) / cF
            worst = min(worst, float(cF and (1 - rel)))
            if rel > Dc('1e-12'): bad += 1                                          # long double: exp of arguments ~ -3000 carries ~1e-16 relative
    finally:
        mod.DIAG['ARANGE'] = saved
    return {'boxes': tested, 'mismatches (the constant is not 1 - e^{-sigma_lo r_a/((2+r_a) a_2)})': bad, 'wrong': wrong}
