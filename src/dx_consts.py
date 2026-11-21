"""Stage DX, items 2.2 and 2.4: THE CONSTANTS OF THE PROOF OF THEOREM DJ-T IN THE FORM OF PAPER J  [numerical estimate; not a proof].  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).
consts_J(La, Lb, lam, etab, C1, CT, CCH, x1new) is dl_consts.consts_iv rewritten by text substitution (every substitution asserted once), with
  - every remainder (eps1, eps_h, k1, q, M4c, M4g, CZ, c_S, c_F, the loss-side 1/(1 - eta), (R7)) at the uniform bound eta_bar (et = etab);
  - the sandwich: the gains carry lam (fl = lam, in place of 1/(1 + eta)); the target is (lam/Upsilon) Gamma x den, so the d2 part of the target is
    lam Gamma/2 (G2t) and the gain/target ratios (1 - eta)/(1 + eta) of th0, c_k, A and k_N become 1 (k_N: background gain over lam x target, >= 1, taken as 1);
    the d1 part of the target in c1F carries lam/Upsilon = lam (1 - eta) = 2 lam - 1 (eta = 1/lam - 1: affine in lam);
  - the variable lam is the GAIN factor 1/(1 + eta): eta in [0, 1/4] is lam in [4/5, 1], and the coefficient of the law lam/Upsilon = 2 lam - 1 runs over [3/5, 1].
    The two ends are lam = 1 (coefficient 1) and lam = 4/5 (coefficient 3/5).  lam = 3/5 (the gains at 3/5) is also run as a stress row (a literal reading of
    'lambda = 3/5'); it is not needed for the claim;
  - mode='uniform' (as asked in DX 2.2): every remainder at eta_bar at BOTH ends.  mode='chord' (found in this stage; reported as a proposal): a remainder
    R(eta) that is a product of nonnegative increasing convex functions of eta is convex in lam (eta = 1/lam - 1 is convex), so on [4/5, 1] it lies under its
    chord R(0) + (R(1/4) - R(0)) 5 (1 - lam); the lines stay affine in lam, and the ends are eta = 0 at lam = 1 and eta = 1/4 at lam = 4/5 (call with etab = 0
    and etab = 1/4).  Where a remainder multiplies the sandwich, it is split first: lam (1 - q) >= lam - q, (2 lam - 1) k1(eta) <= (2 lam - 1)(1 + 0.184 k_E) + eta k_E;
  - the rule does not depend on lam: its Gamma_2 is Gamma/2 (G2s), the value of lam Gamma/2 at lam = 1 (the target is <= it for every lam <= 1);
  - FrB1 (x1new): X1 -> X1_B1 = U1/(1 - eta_bar) + sqrt(CZ(eta_bar)) where X1 stands for the B1m line (the constant c_m of (II-s)).
The arithmetic is dl_interval (decimal, outward rounding) under the DO watch (decimal.Inexact trapped); it is read here on point pieces [ell, ell] as an estimate.
The tail form [1e6, inf) is not rewritten (the a0 and (N0) tail forms use eta = 1/ell): DY."""
import inspect, decimal, functools, json, os, sys, time
from decimal import Decimal as Dc
import dl_consts as LC
from dl_interval import Iv

SRC = inspect.getsource(LC.consts_iv)
REPL = [
    ("def consts_iv(La, Lb, eta=None, _o=None):",
     "def consts_J(La, Lb, lam, etab=Dc('0.25'), C1=Dc('0.62'), CT=Dc('6.5'), CCH=Dc('1.7'), x1new=True, A2C=Dc('2.1'), mode='uniform', _o=None):"),
    ("    et = t if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta)))\n", "    et = Iv(V.D(etab)); lam = Iv(V.D(lam))\n"),
    ("    if eta is not None and tail: raise NotImplementedError('the tail forms of a0 and (N0) use eta = 1/ell')\n",
     "    if tail: raise NotImplementedError('the tail [1e6, inf) of paper J: stage DY')\n"),
    ("eta = et; fl = 1 / (1 + et); Gs = sqrt(1 + C * t); G2s = Gs / (2 * (1 - et))",
     "eta = et; fl = lam; Gs = sqrt(1 + C * t); G2s = Gs / 2; G2t = lam * Gs / 2; o['Gam2 target sqrt(ell)'] = G2t"),
    # FrB1: the B1m line needs X1_B1 = U1/(1 - eta_bar) + sqrt(CZ)
    ("o['X1/sqrt(ell)'] = X1n", "o['X1/sqrt(ell)'] = X1n; X1Bn = (u1n / (1 - et) + sqrt(CZ) * sqrt(t)) if x1new else X1n; o['X1_B1/sqrt(ell)'] = X1Bn"),
    ("- Gs * k1 * sqrt(Iv(Dc('0.5'))) * sqrt(t); o['c1F'] = c1F",
     "- (((2 * lam - 1) * k1) if mode == 'uniform' else ((2 * lam - 1) * (1 + Dc('0.184') * kE) + et * kE)) * Gs * sqrt(Iv(Dc('0.5'))) * sqrt(t); o['c1F'] = c1F"),
    # Case I (Fz): the target Gamma_2 G <= (lam Gamma/2) c1 sqrt(b)/(Gamma/2) = lam c1 sqrt(b) (rule Gamma_2 = Gamma/2)
    ("o['R5: K_F/sqrt(b) <='] - C1", "o['R5: K_F/sqrt(b) <='] - lam * C1"),
    ("    rhs = cB2n + G2s * (1 + ESS) * t", "    rhs = cB2n + G2t * (1 + ESS) * t"),
    ("cmn = 2 * X1n * Dc('1.5') /", "cmn = 2 * X1Bn * Dc('1.5') /"),
    ("th0 = (1 - et) / (1 + et) * sqrt((1 - q) * (1 - z2 / 2))", "th0 = sqrt(((1 - q) if mode == 'uniform' else (1 - q / lam)) * (1 - z2 / 2))"),
    ("o['m1: slack 1 (must be >= 0)'] = m1Y - G2s * (mT + Tm) * t", "o['m1: slack 1 (must be >= 0)'] = m1Y - G2t * (mT + Tm) * t"),
    ("cJ * c0lo / (16 * G2s))", "cJ * c0lo / (16 * G2t))"),
    ("m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc('2.1') * bII ** 2", "m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - A2C * bII ** 2"),
    ("m5c = 1 - cu * kEc - Dc('2.1') * bII ** 2", "m5c = 1 - cu * kEc - A2C * bII ** 2"),
    ("ck = Dc('0.999') * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c", "ck = Dc('0.999') * 2 / (16 * Gs) * m5c"),
    ("A = (1 - et) / ((1 + et) * Gs)", "A = 1 / Gs"),
    ("o['kf (corner)'] * (1 - et) / (2 * E", "o['kf (corner)'] / (2 * E"),
]
for a_, b_ in REPL:
    assert SRC.count(a_) == 1, a_
    SRC = SRC.replace(a_, b_)
NS = dict(LC.__dict__); exec(compile(SRC, 'dl_consts.consts_iv (paper J form, dx_consts)', 'exec'), NS); _consts_J = NS['consts_J']

# the check of the (II-ch) A2k + B2a / cKz ratio against the 2.1 b^2 (A2C) used in m5: A2k/cKz <= 2 b^2/((1 - eta) fl k_f): in J, fl = lam
def a2c_needed(o, lam, etab=Dc('0.25')):
    return 2 / ((1 - float(etab)) * float(lam) * float(o['kf (Case II)'].lo))


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


@trapped
def consts_J(*a, **k):
    return _consts_J(*a, **k)


def checks(o):
    """the conditions ('must be' keys) as (ok, float of the relevant end)"""
    out = {}
    for k, v in o.items():
        if 'must be' not in k: continue
        if '<= 1.002' in k: out[k] = (v.hi <= Dc('1.002'), float(v.hi))
        elif '<= 1)' in k: out[k] = (v.hi <= 1, float(v.hi))
        elif '> 0' in k: out[k] = (v.lo > 0, float(v.lo))
        else: out[k] = (v.lo >= 0, float(v.lo))
    return out


def point(ell, lam, **kw):
    o = {}; err = None
    try: consts_J(str(ell), str(ell), Dc(str(lam)), _o=o, **kw)
    except Exception as ex: err = '%s: %s' % (type(ex).__name__, str(ex)[:120])
    return o, err


if __name__ == '__main__':
    for ell in ('55.26', '960.8', '10000', '1000000'):
        for lam in ('1', '0.8', '0.6'):
            o, err = point(ell, lam); c = checks(o)
            print(ell, lam, err, [(k[:40], round(v, 5)) for k, (ok, v) in c.items() if not ok][:6])
