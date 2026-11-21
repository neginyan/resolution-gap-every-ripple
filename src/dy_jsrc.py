"""Stage DY, items 2.1-2.4: THE SOURCE OF THE CONSTANTS OF PAPER J (Theorems 2 and 4), built from the published source of paper I by asserted text replacements.
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
load(end) writes, into a temporary folder, a copy of dl_consts.py (as 'dl_consts') and of dp_room1.py (as 'dp_room1') with the replacements below, and imports them
(and dq_room1_low, unchanged, which then imports the patched dp_room1).  Nothing in the work tree is changed.
dl_consts (the source of consts_iv; the def line is kept, so dp_room1's own replacements still apply):
  (u)  (b.1) 9.545 -> 9.549 (the correction of stage DU, du_fix.py);
  (r)  the rule constants c1 = 0.77, c_T = 6.5, c_ch = 1.5;  e0 = 2e-5 (E0; the (R4) condition 'e0 needed <= e0' is a quoted bound, checked on every piece);
  (e)  the end: LAM (the gain factor lam = 1/(1 + eta)), ETR (the remainders' eta: 0 at end A, 1/4 at end B; the chord form), A2CJ (the 2.1 of (R7)/(m3)/(m4) per end);
  (s)  the sandwich: fl -> LAM;  the target's Gamma_2 -> LAM Gamma/2 ((II-ch) right side, (m1) slack 1, (m3) log Ch);  the rule's Gamma_2 -> Gamma/2;
       Case I (Fz): c1F - K_F - LAM c1;  c1F's d1 target: (2 lam - 1)(1 + 0.184 k_E) + eta_r k_E;  th0 = sqrt((1 - q/lam)(1 - z2/2));
       the gain/target ratios (1 - eta)/(1 + eta) of c_k and A -> 1, the (1 - eta) of k_N -> 1;
  (f)  FrB1: X1_B1 = U1/(1 - eta_r) + sqrt(CZ(eta_r));  the RULE's c_m (a_s) fixed at its largest value over the range: X1_B1(1/4), 1 - eta = 3/4, fl = 4/5;
  (t)  the tail [1e6, inf) with eta and 1/ell separated:  A >= 1 - a1 t,  a1 := 5 + ell (1 - theta_A)  (theta_A = the gain/target ratio in A; 1/sqrt(1 + 10t) >= 1 - 5t):
           a0 <= ell es_sigma + Tbar_N ell + a1 + eps1' t;   (N0)/t >= (7.5 - a1) - 7.5 a1 t - eps1' t (1 + (7.5 - a1) t) - ell es_sigma - Tbar(mu_II);
       paper I: theta_A = (1 - eta)/(1 + eta), eta = 1/ell: ell (1 - theta_A) = 2/(1 + t) <= 2, a1 = 7 (its formulas);  paper J: theta_A = 1, a1 = 5;
  (q)  QUOTED -> the quoted bounds of paper J (QUOTED_J);
dp_room1 (Theorem 4): its replacements of c_k, m5n, m5c follow the J text; in piece(): eta -> ETR, fl -> LAM, the default A2C -> A2CJ, and the (R7) tiny bound uses X1_B1.
reduce_check(): the tail formulas written with a1 (and the published A) reproduce the published tail of paper I exactly (a1 = 7) on [1e6, inf).
The interval arithmetic is dl_interval under the DO watch (decimal.Inexact trapped) in every run that uses these modules."""
import importlib, importlib.util, inspect, os, sys, tempfile, shutil, decimal, functools
from decimal import Decimal as Dc

HERE = os.path.dirname(os.path.abspath(__file__))
ENDS = {'A': {'LAM': '1', 'ETR': '0', 'A2CJ': '2.1'}, 'B': {'LAM': '0.8', 'ETR': '0.25', 'A2CJ': '3.5'}}
RULE = {'C1': '0.77', 'CT': '6.5', 'CCH': '1.5', 'CCH for ell >= 960.8': '2.0'}
CCH_HI = '2.0'; ELL_CCH = '960.8'; E0C_ROOM = '2.7'
E0J = '2e-5'

# the quoted bounds of paper J (key, sense, bound): the 30 bounds of paper I that still hold, and 18 new numbers (DX report section 4.4; replaced by the
# interval values of this stage after the first run: see QUOTED_J_FINAL in dy_run.py)
QUOTED_J = None     # set by dy_run (the list used in the run is written into the record)


def jsource_dl(src, a1='5'):
    R = [
        ("Dc('9.545') * cbl", "Dc('9.549') * cbl"),
        ("C = Dc(10); C1 = Dc('0.78'); CT = Dc('3.5'); CCH = Dc('2.9'); XI1 = Dc(8); ES = Dc('1e-11'); E0 = Dc('1.26e-5')",
         "C = Dc(10); C1 = Dc('%s'); CT = Dc('%s'); CCH = Dc('%s'); XI1 = Dc(8); ES = Dc('1e-11'); E0 = Dc('%s')\nLAM = '1'; ETR = '0'; A2CJ = '2.1'; A1T = Dc('%s')   # paper J: the end (set by dy_jsrc.set_end)"
         % (RULE['C1'], RULE['CT'], RULE['CCH'], E0J, a1)),
        ("    et = t if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta)))\n",
         "    et = Iv(V.D(ETR)) if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta))); lam = Iv(V.D(LAM))   # paper J: the end\n"),
        ("    if eta is not None and tail: raise NotImplementedError('the tail forms of a0 and (N0) use eta = 1/ell')\n", ""),
        ("eta = et; fl = 1 / (1 + et); Gs = sqrt(1 + C * t); G2s = Gs / (2 * (1 - et))",
         "eta = et; fl = lam; Gs = sqrt(1 + C * t); G2s = Gs / 2; G2t = lam * Gs / 2; o['Gam2 target sqrt(ell)'] = G2t"),
        ("o['X1/sqrt(ell)'] = X1n",
         "o['X1/sqrt(ell)'] = X1n; X1Bn = u1n / (1 - et) + sqrt(CZ) * sqrt(t); o['X1_B1/sqrt(ell)'] = X1Bn\n"
         "    EBR = Iv(Dc('0.25')); CZB = EBR * EBR / (E * (1 - EBR) ** 2); X1Bw = u1n / (1 - EBR) + sqrt(CZB) * sqrt(t)   # the rule's c_m: largest value"),
        ("- Gs * k1 * sqrt(Iv(Dc('0.5'))) * sqrt(t); o['c1F'] = c1F",
         "- ((2 * lam - 1) * (1 + Dc('0.184') * kE) + et * kE) * Gs * sqrt(Iv(Dc('0.5'))) * sqrt(t); o['c1F'] = c1F"),
        ("o['R5: K_F/sqrt(b) <='] - C1", "o['R5: K_F/sqrt(b) <='] - lam * C1"),
        ("    rhs = cB2n + G2s * (1 + ESS) * t", "    rhs = cB2n + G2t * (1 + ESS) * t"),
        ("cmn = 2 * X1n * Dc('1.5') / ((1 - et) * fl * (1 - z2 / 2) * sqrt(2 * PI))",
         "cmn = 2 * X1Bw * Dc('1.5') / ((1 - EBR) * Dc('0.8') * (1 - z2 / 2) * sqrt(2 * PI))"),
        ("th0 = (1 - et) / (1 + et) * sqrt((1 - q) * (1 - z2 / 2))", "th0 = sqrt((1 - q / lam) * (1 - z2 / 2))"),
        ("o['m1: slack 1 (must be >= 0)'] = m1Y - G2s * (mT + Tm) * t", "o['m1: slack 1 (must be >= 0)'] = m1Y - G2t * (mT + Tm) * t"),
        ("cJ * c0lo / (16 * G2s))", "cJ * c0lo / (16 * G2t))"),
        ("m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc('2.1') * bII ** 2", "m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc(A2CJ) * bII ** 2"),
        ("m5c = 1 - cu * kEc - Dc('2.1') * bII ** 2", "m5c = 1 - cu * kEc - Dc(A2CJ) * bII ** 2"),
        ("ck = Dc('0.999') * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c", "ck = Dc('0.999') * 2 / (16 * Gs) * m5c"),
        ("A = (1 - et) / ((1 + et) * Gs)", "A = 1 / Gs"),
        ("o['kf (corner)'] * (1 - et) / (2 * E", "o['kf (corner)'] / (2 * E"),
        ("        a0 = pe(3, L) + TNl + 7 + e1 * t ", "        a0 = pe(3, L) + TNl + A1T + e1 * t "),
        ("= Dc('0.5') - Dc('52.5') * t - e1 * t * (1 + Dc('0.5') * t) - pe(3, L) - Tbar2",
         "= (Dc('7.5') - A1T) - Dc('7.5') * A1T * t - e1 * t * (1 + (Dc('7.5') - A1T) * t) - pe(3, L) - Tbar2"),
        ("    for k, s, b in (WRONG.get('quoted') or QUOTED):", "    for k, s, b in (WRONG.get('quoted') or QUOTED_J):"),
    ]
    for a, b in R:
        assert src.count(a) == 1, a
        src = src.replace(a, b)
    # (p) the rule constant c_ch is piecewise in ell: 1.5 on [55.26, 960.8], 2.0 on [960.8, inf) (DY 2.5, first remedy: the wide room at the end B needs it).
    #     A piece must not contain 960.8 inside (the partition of dy_run puts 960.8 at an edge).
    i0 = src.index('def consts_iv('); i1 = src.index('\n    return o\n', i0); body = src[i0:i1]
    n = body.count('CCH'); assert n == 6, n
    body = body.replace('CCH', 'CCHL')
    a = "    L = Iv(La, Lb); t = 1 / L; o = {} if _o is None else _o\n"
    assert body.count(a) == 1
    body = body.replace(a, a + "    assert not (La < Dc('%s') < Lb), 'a piece contains 960.8'; CCHL = Dc('%s') if La >= Dc('%s') else CCH   # paper J: c_ch piecewise in ell\n" % (ELL_CCH, CCH_HI, ELL_CCH))
    e = "    o['R4: e0 needed'] = R4c / (thbg * sqrt(Bm * om) - Dc('0.5')) + ES\n"
    assert body.count(e) == 1
    body = body.replace(e, e + "    o['R4: e0 - e0 needed (must be >= 0)'] = E0 - o['R4: e0 needed']   # paper J: e0 is a number of the proof; checked on every piece\n")
    src = src[:i0] + body + src[i1:]
    return src + "\n\nQUOTED_J = list(QUOTED)   # replaced by dy_jsrc.set_quoted\n"


def jsource_room1(src):
    R = [
        ("""("    ck = Dc('0.999') * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c; o['c_k'] = ck", "    ck = K5 * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c; o['c_k'] = ck"),""",
         """("    ck = Dc('0.999') * 2 / (16 * Gs) * m5c; o['c_k'] = ck", "    ck = K5 * 2 / (16 * Gs) * m5c; o['c_k'] = ck"),"""),
        ("""("m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc('2.1') * bII ** 2", "m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - A2C * bII ** 2"),""",
         """("m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc(A2CJ) * bII ** 2", "m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - A2C * bII ** 2"),"""),
        ("""("m5c = 1 - cu * kEc - Dc('2.1') * bII ** 2", "m5c = 1 - cu * kEc - A2C * bII ** 2"),""",
         """("m5c = 1 - cu * kEc - Dc(A2CJ) * bII ** 2", "m5c = 1 - cu * kEc - A2C * bII ** 2"),"""),
        ("""assert 'Bm = ' not in SRC and SRC.count('Bm') >= 8 and "Dc('0.999')" not in _body and "Dc('2.1')" not in _body""",
         """assert 'Bm = ' not in SRC and SRC.count('Bm') >= 8 and "Dc('0.999')" not in _body and "Dc(A2CJ)" not in _body"""),
        ("    et = t if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta))); fl = 1 / (1 + et)          # DX: eta separated (None: eta = 1/ell)",
         "    et = Iv(V.D(NS['ETR'])) if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta))); fl = Iv(V.D(NS['LAM']))   # paper J: the end"),
        ("    a2c = Dc('2.1') if a2c is None else Dc(a2c)", "    a2c = Dc(NS['A2CJ']) if a2c is None else Dc(a2c)"),
        ("    b1m = 48 * o['X1/sqrt(ell)'] * o['cm/sqrt(ell)'] ** 3", "    b1m = 48 * o['X1_B1/sqrt(ell)'] * o['cm/sqrt(ell)'] ** 3"),
    ]
    for a, b in R:
        assert src.count(a) == 1, a
        src = src.replace(a, b)
    return src


TMP = None


def load(a1='5'):
    """write and import the patched modules; returns (LC, RM, DQL)."""
    global TMP
    TMP = tempfile.mkdtemp(prefix='dy_jsrc_')
    s = open(os.path.join(HERE, 'dl_consts.py'), encoding='utf-8').read()
    open(os.path.join(TMP, 'dl_consts.py'), 'w', encoding='utf-8').write(jsource_dl(s, a1))
    s = open(os.path.join(HERE, 'dp_room1.py'), encoding='utf-8').read()
    open(os.path.join(TMP, 'dp_room1.py'), 'w', encoding='utf-8').write(jsource_room1(s))
    s = open(os.path.join(HERE, 'dq_room1_low.py'), encoding='utf-8').read()
    a = "    e0 = es if e0_is_es else Iv((2 / sqrt(Bm_) + es).hi)"; assert s.count(a) == 1
    s = s.replace(a, "    e0 = es if e0_is_es else Iv((Dc('%s') / sqrt(Bm_) + es).hi)   # paper J: e0 = 2.7/sqrt(B_m) + es (paper I: 2/sqrt(B_m) + es)" % E0C_ROOM)
    open(os.path.join(TMP, 'dq_room1_low.py'), 'w', encoding='utf-8').write(s)
    for m in ('dl_consts', 'dp_room1', 'dq_room1_low'): sys.modules.pop(m, None)
    sys.path.insert(0, TMP)
    try:
        LC = importlib.import_module('dl_consts'); RM = importlib.import_module('dp_room1'); DQL = importlib.import_module('dq_room1_low')
    finally:
        sys.path.remove(TMP)
    assert LC.__file__.startswith(TMP) and RM.__file__.startswith(TMP) and DQL.__file__.startswith(TMP)
    return LC, RM, DQL


def set_end(LC, RM, end):
    for k, v in ENDS[end].items():
        setattr(LC, k, v); RM.NS[k] = v
    return ENDS[end]


def set_quoted(LC, RM, q):
    LC.QUOTED_J = list(q); RM.NS['QUOTED_J'] = list(q)


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


def reduce_check():
    """the tail written with a1 reproduces the published tail of paper I (with its A, du_fix's 9.549) when a1 = 7: every key on [1e6, inf), end points equal."""
    s = open(os.path.join(HERE, 'dl_consts.py'), encoding='utf-8').read().replace("Dc('9.545') * cbl", "Dc('9.549') * cbl")
    g = s.replace("        a0 = pe(3, L) + TNl + 7 + e1 * t ", "        a0 = pe(3, L) + TNl + A1T + e1 * t ") \
         .replace("= Dc('0.5') - Dc('52.5') * t - e1 * t * (1 + Dc('0.5') * t) - pe(3, L) - Tbar2",
                  "= (Dc('7.5') - A1T) - Dc('7.5') * A1T * t - e1 * t * (1 + (Dc('7.5') - A1T) * t) - pe(3, L) - Tbar2") + "\nA1T = Dc(7)\n"
    assert g.count('A1T') == 5, g.count('A1T')
    out = {}
    for name, src in (('published', s), ('general a1 = 7', g)):
        ns = {'__name__': 'dy_red_' + name.replace(' ', '_'), '__file__': os.path.join(HERE, 'dl_consts.py')}
        sys.path.insert(0, HERE)
        try: exec(compile(src, 'dl_consts (%s)' % name, 'exec'), ns)
        finally: sys.path.remove(HERE)
        out[name] = trapped(ns['consts_iv'])(Dc(10) ** 6, Dc('Infinity'))
    a, b = out['published'], out['general a1 = 7']
    diff = [k for k in a if not (a[k].lo == b[k].lo and a[k].hi == b[k].hi)]
    # the derivation, in exact rational arithmetic (polynomials in t; fractions):
    #   J:  A = 1/sqrt(1 + 10 t) >= 1 - a1 t  <=>  (1 - a1 t)^2 (1 + 10 t) <= 1  (for 0 < t, a1 t < 1);  the left side is
    #       1 + (10 - 2 a1) t + (a1^2 - 20 a1) t^2 + 10 a1^2 t^3.  a1 = 5: 1 - 75 t^2 + 250 t^3 <= 1 for t <= 0.3 (so for t <= 1e-6).  a1 = 4: + 2 t > 0 (fails).
    #   paper I: (1 - t)/(1 + t) >= 1 - 2t  ((1 - 2t)(1 + t) = 1 - t - 2t^2 <= 1 - t), so A >= (1 - 2t)(1 - 5t) = 1 - 7t + 10 t^2 >= 1 - 7t: a1 = 7.
    from fractions import Fraction as Fr
    def poly(a1):
        a1 = Fr(a1); return [Fr(1), 10 - 2 * a1, a1 * a1 - 20 * a1, 10 * a1 * a1]
    def holds(a1, tmax=Fr(1, 10 ** 6)):
        c = poly(a1)
        if c[1] > 0: return False                                    # fails for small t
        if c[1] == 0: return c[2] + c[3] * tmax <= 0                 # t^2 (c2 + c3 t) <= 0 on (0, tmax]
        return all(c[1] + c[2] * x + c[3] * x * x < 0 for x in (tmax,)) and c[2] <= 0
    der = {'J: (1 - a1 t)^2 (1 + 10 t) coefficients, a1 = 5': [str(x) for x in poly(5)], 'J: a1 = 5 holds for 0 < t <= 1e-6': holds(5),
           'J power: a1 = 4 holds (must be False)': holds(4),
           'paper I: (1 - 2t)(1 + t) = 1 - t - 2 t^2 and (1 - 2t)(1 - 5t) = 1 - 7t + 10 t^2 (a1 = 7)': True,
           'paper I power: a1 = 6.9 from (1 - 2t)(1 - 5t) >= 1 - 6.9 t (must be False for small t)': (Fr(-7) + Fr(69, 10)) >= 0}
    trapped_der = der
    return {'keys on the tail': len(a), 'keys that differ (must be empty)': diff, 'derivation checks': trapped_der,
            'ok': bool(not diff and der['J: a1 = 5 holds for 0 < t <= 1e-6'] and not der['J power: a1 = 4 holds (must be False)']
                       and not der['paper I power: a1 = 6.9 from (1 - 2t)(1 - 5t) >= 1 - 6.9 t (must be False for small t)'])}
