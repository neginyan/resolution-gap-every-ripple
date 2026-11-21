"""Stage DP, room 1a (DP_探索計画.md section C, written before this ran): the interval proof of Theorem DJ-T with the lower end of B replaced by
        B_1(ell) := max(5e5, c_B (8 ell + 100)),      ell >= 960.8,   B_1(ell) <= B < ell^4          (CLAIM DP-1a(c_B)).
(The plan, section C, stated the upper end as 2.5e10; section E, written before the computations of the band, restates it as ell^4: the proof uses the upper end of B
only in (b.5), as B < ell^4, and the interval arithmetic below uses only the LOWER bound B_m.  With ell^4 the claim joins DJ-T, whose lower end is
max(2.5e10, 50 (8 ell + 100)) <= ell^4, also for ell > 6.25e7 where 50 (8 ell + 100) > 2.5e10.)
Python 3.11 grammar.  [computer-assisted]
WHY THIS IS THE SAME PROOF: the 37 lines are lower bounds of the lemmas whenever z0^2 = K^2 y <= 1, 1 - q > 0 and y <= 1e-6, i.e. B >= max(5e5, (8 ell + 100)/2);
the proof of DJ-T uses B >= 2.5e10 only through CONSTANTS: es (R1), e0 (R4), omega, c_S, c1F, rhobar, rho_max, c_G (b.2); and B >= 50 (8 ell + 100) only through
q <= (1 + eta)/(400 (1 - eta)), z2 <= 0.01.  Here these five are parameters of the piece [La, Lb]:
        B_m := (lower end of) B_1(La),   q <= (1 + eta)/(8 c_B (1 - eta)),   z2 <= 1/(2 c_B),   es := 0.25/B_m,   e0 := 2/sqrt(B_m) + es   (both rounded up).
consts_gen is the SOURCE of dl_consts.consts_iv with exactly these replacements (asserted; and with the original values it reproduces consts_iv: check E).
Here B < ell^4, so step (m4) closes by (b.5) alone (it uses b < ell^4 sigma^2 and sqrt(b) < ell^2 sigma only): the conditions of (b.6) (beta-case, (N), (N0), (F)) are NOT used and not required.
CONDITIONS REQUIRED ON EVERY PIECE (all with decimal.Inexact trapped in the default context):
  (a) the 'must be' conditions of consts_iv except those of (b.6);
  (b) (R1) sum/P1 <= 0.52 es, (R3) <= 0.48 es, the tiny bounds (dp_r1.bounds_iv with B_m, q);   (R4) e0 needed <= e0;
  (c) inputs quoted inside the formulas: F1: P <= 0.7008;  (b.1) first pass P/(mu e^-mu) <= 9.18;
  (d) (b.2): c_G sqrt(ell) > G/sigma at mu = ell + ln ell   [Case II: G > c1 sqrt(b)/Gam2 = c_G sqrt(ell) sigma];
  (e) (b.5): mu_II >= 6;  kappa_b mu < 1: (mT + Tbar)/c_k 2 ell^{9/2} sigma < 1 and 16 ell^5 sigma < 1;  u > max(6, U_max) in both sub-cases:
        kappa_b = kappa: the key of consts_iv;   kappa_b = 16 b e^mu/mu:  log u >= log((m1/m2)(sqrt2/4)/sqrt(c0^2 e)) - log E_J(6) + (ell + mu)/2 - (1/4) ln mu - ln ell
        at mu = x0 ell, ell = La (increasing in mu and, at mu = x0 ell, in ell), with m1 = 1 - eps1_max - e0, m2 = 1 - 3 es_sigma, c0^2 <= 1/(m2 (1 - q)).
NUMBERS WRITTEN INTO THE FORMULAS of DJ-T that depend on z2, q or k_f (re-audit of the source of consts_iv in DP; the first run of this file had left the first two
at their DJ-T values, which hold only for z2 <= 0.01, q <= 0.0026 -- found before the report, corrected, everything re-run; the margins of the two conditions they
enter are of the order 1e48, so no result changed):
  (w1) (b.5) c_k uses k_f >= 0.999          -> parameter K5 := lower end of (1 - b)^2 (1 - 4b/(1 - b) - z2/12) at b = 1e-100 (and ell^4 sigma^2 <= 1e-100 is a condition);
  (w2) (b.5) u uses 1/sqrt(c0) >= 0.999      -> parameter IC0 := lower end of (m2 (1 - q))^(1/4);
  (w3) A2k/cKz <= 2.1 b^2 (Case II; in m5)   -> condition 2/((1 - eta) fl k_f) <= 2.1 (parameter A2C);
  (w4) (II-ch) (A2k + B2a)/cKz <= 1e-3;  (w5) (II-s) a_s <= 1e-9 sigma;  (w6) Case I (Tz-B2) B2a/cKz <= 1e-6   -> conditions.
The other numbers written in (0.7008, 9.18, 1.002, 14.29, 9.545, the pair line 1e-9) do not depend on B, z2 or q, or are conditions already.
ONE PLACE of the proof uses 'b < 0.1' (Case I, Tz-B2: kf >= 0.4493, A2k/cKz <= 0.04616).  With c_B = 1/2 (z2 <= 1) that uniform constant is too weak and the condition
of Case I (Tz-B2) FAILS, and so does (w3) (2.186 > 2.1); here b < ell^4 sigma^2 < 1e-100, and with this bound in that one place (parameter bI) and 2.2 in (w3) all
conditions hold: recorded as a separate run.
POWER (wrong versions must fail): e0 := es (no absorption of the constant lines);  c_B = 0.3 (z2 > 1);  the rule constant c1 = 0.95;  B_m = 100.
    python3 dp_room1.py [c_B ...]     -> results/dp_room1.json"""
import inspect, json, math, sys, time, functools
import decimal
from decimal import Decimal as Dc
import dl_interval as V
from dl_interval import Iv, exp, log, sqrt, pe
import dl_consts as LC
import dp_r1 as R1

ELL0 = Dc('960.8'); ELL_TAIL = Dc(10) ** 6; BTOP = Dc('2.5e10')
SRC = inspect.getsource(LC.consts_iv)
REPL = [("def consts_iv(La, Lb, eta=None, _o=None):", "def consts_gen(La, Lb, Bm, qden, z2v, ES, E0, bI=Dc('0.1'), K5=Dc('0.999'), IC0=Dc('0.999'), A2C=Dc('2.1'), eta=None, _o=None):"),
        # (b.5): two numbers written into the formulas of DJ-T that hold only for z2 <= 0.01 and q <= 0.0026 (found in the re-audit of the source, DP):
        #   c_k = k_f 2 (1 - eta)/(16 (1 + eta) Gs) m5 with k_f >= 0.999 (k_f = (1 - b)^2 (1 - 4b/(1 - b) - z2/12), b < ell^4 sigma^2)  -> parameter K5;
        #   u >= ... /sqrt(c0) with 1/sqrt(c0) >= 0.999 (c0^2 <= 1/(m2 (1 - q)))                                                       -> parameter IC0.
        ("    ck = Dc('0.999') * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c; o['c_k'] = ck", "    ck = K5 * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c; o['c_k'] = ck"),
        ("sqrt(2 * ck / (E * Dc('1.002'))) * Dc('0.999') * exp(H(x0, L5, 1, Dc('1.5'), Dc('0.75')))", "sqrt(2 * ck / (E * Dc('1.002'))) * IC0 * exp(H(x0, L5, 1, Dc('1.5'), Dc('0.75')))"),
        # A2k/cKz <= 2 b^2/((1 - eta) fl k_f) <= 2.1 b^2 (Case II): the 2.1 as a parameter A2C (it is CHECKED below against the k_f of the piece)
        ("m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc('2.1') * bII ** 2", "m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - A2C * bII ** 2"),
        ("m5c = 1 - cu * kEc - Dc('2.1') * bII ** 2", "m5c = 1 - cu * kEc - A2C * bII ** 2"),
        # Case I, Tz-B2: 'b < 0.1' as a parameter bI (kf >= (1 - bI)^2 (1 - 4 bI/(1 - bI) - z2/12), A2k/cKz <= bI^2/(8 (1 - eta) cK)); bI = 0.1 gives the two lines of DJ-T
        ("    kf01 = Dc('0.81') * (1 - Iv(Dc('0.4')) / Dc('0.9') - z2 / 12); o['kf (b < 0.1)'] = kf01; cK = fl * kf01 / 16; o['cK'] = cK",
         "    bIv = Iv(bI); kf01 = (1 - bIv) ** 2 * (1 - 4 * bIv / (1 - bIv) - z2 / 12); o['kf (b < 0.1)'] = kf01; cK = fl * kf01 / 16; o['cK'] = cK"),
        ("    a2k = Dc('0.01') / (8 * (1 - et) * cK); o['Case I (Tz-B2): A2k/cKz <='] = a2k",
         "    a2k = bIv ** 2 / (8 * (1 - et) * cK); o['Case I (Tz-B2): A2k/cKz <='] = a2k"),
        ("    Bm = Dc('2.5e10'); q = (1 + et) / (400 * (1 - et)); z2 = Iv(Dc('0.01')); om = 1 / (1 + Iv(Dc('0.75')) / Bm) ** 2",
         "    q = (1 + et) / (qden * (1 - et)); z2 = Iv(z2v); om = 1 / (1 + Iv(Dc('0.75')) / Bm) ** 2"),
        ("Dc('0.5') / sqrt(Iv(Bm))", "Dc('0.5') / sqrt(Bm)")]
for a_, b_ in REPL:
    assert SRC.count(a_) == 1, a_
    SRC = SRC.replace(a_, b_)
_body = SRC[SRC.index('\n'):]                                                        # everything after the def line (which holds the default values)
assert 'Bm = ' not in SRC and SRC.count('Bm') >= 8 and "Dc('0.999')" not in _body and "Dc('2.1')" not in _body
B5 = Dc('1e-100')                                                                    # (b.5): b < ell^4 sigma^2 <= 1e-100 (checked on every piece)
NS = dict(LC.__dict__); exec(compile(SRC, 'dl_consts.consts_iv (generalised in dp_room1)', 'exec'), NS); consts_gen = NS['consts_gen']
B6 = ('beta-case', 'N: 2.5', 'N0:', 'F: left')


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


def params(La, cB, Bm=None, e0_is_es=False, bI=None):
    """the parameters of the piece starting at La (Decimal): all as point intervals / decimals, rounded in the safe direction."""
    cB = Dc(cB)
    B1 = V.imax(Iv(Dc('5e5')), Iv(cB) * (8 * Iv(La) + 100)) if Bm is None else Iv(Dc(Bm))
    Bm_ = Iv(B1.lo)                                                                 # a lower bound of B_1(ell) for every ell >= La
    es = Iv((Iv(Dc('0.25')) / Bm_).hi)
    e0 = es if e0_is_es else Iv((2 / sqrt(Bm_) + es).hi)
    return Bm_, 8 * cB, (1 / (2 * Iv(cB))).hi, es, e0                              # z2 <= 1/(2 c_B) rounded up inside the interval arithmetic (8 c_B is exact)


def piece(La, Lb, cB, c1=None, bI=None, a2c=None, eta=None, **kw):
    """every required condition on [La, Lb]: name -> (ok, value)."""
    Bm, qden, z2v, es, e0 = params(La, cB, **kw)
    L = Iv(V.D(La), V.D(Lb)); t = 1 / L
    et = t if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta))); fl = 1 / (1 + et)          # DX: eta separated (None: eta = 1/ell)
    b5 = Iv(B5); k5 = ((1 - b5) ** 2 * (1 - 4 * b5 / (1 - b5) - Iv(z2v) / 12)).lo                   # k_f in (b.5), for b <= 1e-100 and z2 <= z2v
    qmax = (1 + et) / (qden * (1 - et)); ic0 = sqrt(sqrt((1 - 3 * pe(2, L)) * (1 - qmax))).lo        # 1/sqrt(c0) >= (m2 (1 - q))^(1/4)
    a2c = Dc('2.1') if a2c is None else Dc(a2c)
    keep = NS['C1']
    if c1 is not None: NS['C1'] = Dc(c1)
    try: o = consts_gen(La, Lb, Bm, qden, z2v, es, e0, K5=Iv(k5), IC0=Iv(ic0), A2C=a2c, **({} if bI is None else {'bI': Dc(bI)}), eta=eta)    # K5, IC0 as intervals: no arithmetic outside the context
    finally: NS['C1'] = keep
    out = {}
    # the numbers written into the formulas of DJ-T that depend on z2, q or k_f: each is a condition here
    out['written-in: (b.5) b < ell^4 sigma^2 <= 1e-100'] = (pe(4, L, 2).hi <= B5, float(pe(4, L, 2).hi))
    out['written-in: A2k/cKz coefficient 2/((1 - eta) fl k_f) <= %s (Case II)' % a2c] = ((2 / ((1 - et) * fl * o['kf (Case II)'])).hi <= a2c, float((2 / ((1 - et) * fl * o['kf (Case II)'])).hi))
    out['written-in: II-ch: (A2k + B2a)/cKz <= 1e-3'] = (o['II-ch: A2k + B2a relative to cKz <='].hi <= Dc('1e-3'), float(o['II-ch: A2k + B2a relative to cKz <='].hi))
    out['written-in: II-s: log(a_s/sigma) <= -20.73 (a_s <= 1e-9 sigma)'] = (o['II-s: log(a_s/sigma) <='].hi <= Dc('-20.73'), float(o['II-s: log(a_s/sigma) <='].hi))
    b2a = 4 * (Dc('0.75') * o['X1/sqrt(ell)']) * Dc('0.1') * sqrt(pe(Dc('0.5'), L)) / ((1 - et) ** 2 * fl * o['kf (b < 0.1)'] * sqrt(Iv(NS['CT'])))
    out['written-in: Case I (Tz-B2): B2a/cKz <= 1e-6'] = (o['kf (b < 0.1)'].lo > 0 and b2a.hi <= Dc('1e-6'), float(b2a.hi))
    for k, v in o.items():                                                           # (a)
        if 'must be' not in k or any(s in k for s in B6): continue
        if '<= 1.002' in k: out[k] = (v.hi <= Dc('1.002'), float(v.hi))
        elif '<= 1)' in k: out[k] = (v.hi <= 1, float(v.hi))
        elif '> 0' in k: out[k] = (v.lo > 0, float(v.lo))
        else: out[k] = (v.lo >= 0, float(v.lo))
    r = R1.bounds_iv(ell_lo=La, Bm=Bm.lo, qden=qden)                                 # (b)
    out['R1: sum/P1 <= 0.52 es'] = (r['R1: sum/P1'].hi <= (Dc('0.52') * es).lo, float((r['R1: sum/P1'] / es).hi))
    out['R3 (a <= 1): S/P4z <= 0.48 es'] = (r['R3 (a <= 1): S/P4z'].hi <= (Dc('0.48') * es).lo, float((r['R3 (a <= 1): S/P4z'] / es).hi))
    out['R3 (a >= 1): S/P1 <= 0.48 es'] = (r['R3 (a >= 1): S/P1'].hi <= (Dc('0.48') * es).lo, float((r['R3 (a >= 1): S/P1'] / es).hi))
    for k in ('(d4 + N4G)/P2z / es_sigma', 'B1l/P2z / es_sigma (mu <= 2 ell)', 'B1c/(Gam2 G) / es_sigma', 'X1^2/ell'):
        out['tiny: %s <= 1' % k] = (r[k].hi <= 1, float(r[k].hi))
    # (R7) a >= a_L: B1m/P2z <= 16 X1 mu sqrt(2 + r) c_m^3 ell^9 sigma^2/((1 - eta) sqrt(2 pi) (1 - q) fl) <= es_sigma  (mu <= 2 ell, sqrt(2 + r) <= 1.5; c_m with z2, 1 - q of the piece)
    b1m = 48 * o['X1/sqrt(ell)'] * o['cm/sqrt(ell)'] ** 3 * pe(10, L) / ((1 - et) * sqrt(2 * LC.PI) * (1 - qmax) * fl)
    out['tiny: B1m/P2z at a_L / es_sigma (mu <= 2 ell) <= 1'] = (b1m.hi <= 1, float(b1m.hi))
    out['R4: e0 needed <= e0'] = (o['R4: e0 needed'].hi <= e0.lo, float((o['R4: e0 needed'] / e0).hi))
    out['input: F1: P <= 0.7008'] = (o['F1: P <='].hi <= Dc('0.7008'), float(o['F1: P <='].hi))            # (c)
    out['input: b.1 first pass P/(mu e^-mu) <= 9.18'] = (o['b.1 first pass: P/(mu e^-mu) <='].hi <= Dc('9.18'), float(o['b.1 first pass: P/(mu e^-mu) <='].hi))
    cG = o['c_G'] * sqrt(Iv(V.D(La))); g2 = o['b.2: G/sigma at mu = ell + ln ell <=']                       # (d)
    out['b.2: c_G sqrt(ell) > G/sigma at mu = ell + ln ell'] = (cG.lo > g2.hi, float((g2 / cG).hi))
    mu2 = o['mu_II']; ck = o['c_k']; mTT = o['b.5: mT + Tbar (must be <= 1.002)']; Um = o['U_max']           # (e)
    out['b.5: mu_II >= 6'] = (mu2.lo >= 6, float(mu2.lo))
    v1 = mTT / ck * 2 * pe(Dc('4.5'), L); v2 = 16 * pe(5, L)
    out['b.5: kappa_b mu < 1 (both bounds)'] = (v1.hi < 1 and v2.hi < 1, float(max(v1.hi, v2.hi)))
    six = V.imax(Iv(6), Um)
    ua = o['b.5: u lower bound (kappa_b = kappa), ell >= 397.6, mu >= x0 ell']
    out['b.5: u > max(6, U_max) where kappa_b = kappa'] = (ua.lo > six.hi, float(min(ua.lo, Dc('1e300'))))
    ESS = pe(2, L); m1 = 1 - o['eps1_max'] - e0; m2 = 1 - 3 * ESS; c0sq = 1 / (m2 * (1 - o['q_max']))
    la = Iv(V.D(La)); m0 = o['x0 (certified lower bound)'] * la
    ej6 = LC.E_J(Iv(6, V.INF)).hi
    lu = log((m1 / m2) * sqrt(Iv(2)) / 4 / sqrt(c0sq * exp(Iv(1)))) - log(Iv(ej6)) + (la + m0) / 2 - log(m0) / 4 - log(la)
    out['b.5: log u - log max(6, U_max) > 0 where kappa_b = 16 b e^mu/mu'] = ((lu - log(six)).lo > 0, float((lu - log(six)).lo))
    out['b.5: ell >= 398, so 2.5e10 <= 398^4 <= ell^4 (B < ell^4 in the whole room)'] = (V.D(La) >= 398 and Dc(398) ** 4 >= BTOP, float(V.D(La)))
    info = {'B_m': float(Bm.lo), 'es': float(es.hi), 'e0': float(e0.hi), 'x0': float(o['x0 (certified lower bound)'].lo), 'U_max': float(Um.hi), 'c_k': float(ck.lo),
            'c1F': float(o['c1F'].lo), 'rho_max': float(o['rho_max (wide)'].hi)}
    return out, info


def run_cb(cB, ratio=Dc('1.001'), pcs=None, **kw):
    t0 = time.time(); worst = {}; fails = []; n = 0; first_info = None
    if pcs is None:
        pcs = []; La = ELL0
        while La < ELL_TAIL:
            Lb = min(La * ratio, ELL_TAIL); pcs.append((La, Lb)); La = Lb
        pcs.append((ELL_TAIL, Dc('Infinity')))
    for a, b in pcs:
        try:
            r, info = trapped(piece)(a, b, cB, **kw); bad = [k for k, (ok, v) in r.items() if not ok]
        except decimal.Inexact:
            raise
        except Exception as e:
            r, info = {}, {}; bad = ['exception: ' + repr(e)[:140]]
        n += 1
        if first_info is None: first_info = info
        if bad: fails.append({'piece': [str(a), str(b)], 'failed': bad[:6]})
        for k, (ok, v) in r.items():
            sense_max = ('<=' in k or '< 1' in k) and 'log u' not in k and 'ell >= 398' not in k
            if k not in worst or (v > worst[k][1] if sense_max else v < worst[k][1]): worst[k] = (bool(ok), v, float(a))
    return {'c_B': str(cB), 'pieces (with the tail)': n, 'failing pieces (must be empty)': fails[:12], 'number of failing pieces': len(fails),
            'worst value of every condition (ok, value, left end of the piece)': worst, 'parameters of the first piece': first_info, 'last piece': info,
            'ok': not fails, 'seconds': time.time() - t0}


def equivalence():
    """(E) consts_gen with the original parameters reproduces dl_consts.consts_iv (relative 1e-30) on four pieces."""
    worst = 0.0
    for a, b in ((Dc('55.26'), Dc('55.26') * Dc('1.001')), (Dc('960.8'), Dc('961.7608')), (Dc('999000'), Dc('1000000')), (Dc('1000000'), Dc('Infinity'))):
        o1 = trapped(LC.consts_iv)(a, b); o2 = trapped(consts_gen)(a, b, Iv(Dc('2.5e10')), 400, Dc('0.01'), LC.ES, LC.E0)   # bI = 0.1 (default)
        assert set(o1) == set(o2)
        with decimal.localcontext(decimal.Context(prec=60)):                         # the comparison itself (not interval arithmetic)
            for k in o1:
                for x, y in ((o1[k].lo, o2[k].lo), (o1[k].hi, o2[k].hi)):
                    if x == y: continue
                    d = abs(x - y) / max(abs(x), abs(y)); worst = max(worst, float(d))
    return {'largest relative difference of an end point': worst, 'ok': worst < 1e-30}


def power():
    pcs = [(ELL0, ELL0 * Dc('1.001')), (Dc('3000'), Dc('3003')), (Dc('100000'), Dc('100100')), (ELL_TAIL, Dc('Infinity'))]
    out = {}
    for name, cB, kw in (('e0 := es (the constant lines are not absorbed)', '50', {'e0_is_es': True}), ('c_B = 0.3 (z2 > 1)', '0.3', {}),
                         ('the rule constant c1 = 0.95', '50', {'c1': '0.95'}), ('B_m = 100 (the constants with B far below the room; they still hold at B_m = 1e3)', '50', {'Bm': '100'})):
        r = run_cb(cB, pcs=pcs, **kw); out[name] = {'failing pieces of 4': r['number of failing pieces'], 'caught': r['number of failing pieces'] > 0,
                                                    'first': (r['failing pieces (must be empty)'] or [{}])[0].get('failed', [])[:3]}
    out['ok'] = all(v['caught'] for v in out.values())
    return out


BROOM = '1e-100'      # in room 1a: b = B sigma^2 < 2.5e10 e^{-2 ell} <= 2.5e10 e^{-1921.6} < 1e-100


def run(cbs=('50', '1', '0.5'), save=True):
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)', '(E) the generalised source reproduces dl_consts.consts_iv': equivalence()}
    print('E', out['(E) the generalised source reproduces dl_consts.consts_iv'], flush=True)
    for cB in cbs:
        r = run_cb(cB); out['c_B = %s' % cB] = r; print('c_B', cB, r['ok'], r['number of failing pieces'], round(r['seconds']), r['failing pieces (must be empty)'][:2], flush=True)
    # the room's own bound of b in the one place where DJ-T uses 'b < 0.1' (Case I, Tz-B2): b < 1e-100 in room 1a
    for cB in ('1', '0.5'):
        r = run_cb(cB, bI=BROOM, a2c=('2.2' if cB == '0.5' else None)); out['c_B = %s with b < 1e-100 in Case I (Tz-B2)' % cB] = r      # c_B = 1/2: also the coefficient 2.1 -> 2.2
        print('c_B', cB, 'bI', BROOM, r['ok'], r['number of failing pieces'], round(r['seconds']), r['failing pieces (must be empty)'][:2], flush=True)
    out['power'] = power(); print('power', out['power'], flush=True)
    out['ok'] = bool(out['(E) the generalised source reproduces dl_consts.consts_iv']['ok'] and out['c_B = 50']['ok'] and out['c_B = 1']['ok']
                     and out['c_B = 0.5 with b < 1e-100 in Case I (Tz-B2)']['ok'] and not out['c_B = 0.5']['ok'] and out['power']['ok'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_room1.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(tuple(sys.argv[1:]) or ('50', '1', '0.5')); print(r['ok'])
