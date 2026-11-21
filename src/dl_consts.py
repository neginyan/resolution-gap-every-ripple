"""AUDIT GUIDE (stage DN; the computation below is unchanged except the constant c_CM of Lemma CM-1, see cm_const.py):
  WHAT: every constant of the proof of Theorem DJ-T as an interval valid for all ell in a piece [La, Lb] (Lb may be infinite), the 18 conditions and the 48
  quoted bounds checked on 9,809 pieces of [55.26, 1e6] and on the tail [1e6, inf).  WHERE: DO_証明まとめ.md section 3.9 (table of conditions) and the
  proof steps of section 3 that each condition closes (names of the keys = the names in the tables of sections 3.9 and 7).  RUN: python dl_consts.py
  (-> results/dl_consts.json), python dl_consts.py power (wrong versions).
Stage DL (review B of ChatGPT): THE CONSTANTS AND CONDITIONS OF THE PROOF OF THEOREM DJ-T FOR EVERY ell >= 55.26.  Python 3.11 grammar.
consts_iv(La, Lb): every constant of dj_proof.consts as an INTERVAL valid for all ell in [La, Lb] (Lb may be +inf), every condition and every quoted bound as an
interval; the interval arithmetic is dl_interval (decimal, outward rounding).  The formulas are those of dj_proof.consts, with three kinds of changes:
  (n) each condition with a growing positive factor is computed DIVIDED by that factor (the sign is the same):  4 ell (c_kap - 4/ell) for 'c_kap ell 4 - 16',
      sqrt(ell)[(1 - a2k - 1e-6) cK c_T - c_B2/sqrt(ell)] for Case I (Tz-B2), ell [Th*/sqrt2/ell - (mT + Tm)/ell] for (m1) slack 2,
      ell e^{mu_n} [c_J - 4 mu_n^2 e^{-mu_n} E_J^2/ell] for (m3);
  (s) the products of a growing and a decaying factor are written with the special functions of dl_interval (pe, pec, H, lol, lq), whose monotonicity is
      proved by one derivative each; the values are the same functions;
  (t) four places where dj_proof.consts used the exact value and an UPPER bound (or a lower bound) is enough and is tail-safe:
      eps1 ell^2 <= ell^2 [q4 + z4/2 + 3 es_sigma + ell^-3 + rho4/2 + rmax/2]   (1 - sqrt(X) y z <= (1 - X) + (1 - y) + (1 - z), 1 - prod(1 - a_i) <= sum a_i);
      (b.1) second pass:  E_CM - derived >= (1 + 3.445 e^{-mu/2})^2 t [2e-3 - (X_t e^X + Y_t)/(1 - Y)]   (e^X - 1 <= X e^X);
      x0: a certified LOWER bound (the inequality checked at x0 for every ell of the interval; every use of mu_II = x0 ell is conservative when x0 is smaller);
      for Lb = inf only (the tail): a0 <= ell es_sigma + Tbar_N ell + 7 + eps1' t  and  (N0) divided by t with th1 >= (1 - 7t)(1 - eps1' t^2), (1 - 15t)^{-1/2} >= 1 + 7.5t.
  (b.5) is written for every ell >= 397.6 (where B < ell^4 can happen) and mu >= x0 ell, with its worst case at mu = x0 ell (u increases in mu) instead of the
      value at ell = 398, mu = 0.15 ell of dj_proof.consts.
run(): the partition of [55.26, ELL_TAIL] (geometric, adaptive) and the tail [ELL_TAIL, inf): every condition and every quoted bound on every piece."""
import json, math, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
from decimal import Decimal as Dc, localcontext
import dl_interval as V
from dl_interval import Iv, exp, log, sqrt, log1p, imin, imax, pe, pec, H, lol, lq
ELL1 = Dc('55.26'); ELL_TAIL = Dc(10) ** 6
C = Dc(10); C1 = Dc('0.78'); CT = Dc('3.5'); CCH = Dc('2.9'); XI1 = Dc(8); ES = Dc('1e-11'); E0 = Dc('1.26e-5')
E = exp(Iv(1)); PI = Iv(Dc('3.141592653589793238462643383279502884197'), Dc('3.141592653589793238462643383279502884198'))


CI = CM.c_cm_iv()                                                                    # DN: sqrt2/(16e) as an interval (CM_C0325=1: 0.0325)


def E_CM(mu, t): return (1 + Dc('3.445') * exp(mu * Dc('-0.5'))) ** 2 * (1 + Dc('2e-3') * t)
def E_J(mu): return (1 + Dc('4.43') * exp(mu * Dc('-0.5'))) ** 2 * exp(pe(1, mu) / 32) + Dc('6.2e-4')
def lB0(Ev, bp): return 2 * log(1 + sqrt(Ev) + exp(log(Ev / 2) / (2 + bp)))


def x0_cert(vthw, mT, tc, PII, t):
    """the largest x (bisection, 60 steps) with  lower(vthw/(2 sqrt x)) >= upper(mT + tc min(x/24, PII t/3))  for every ell of the interval."""
    lo, hi = Dc('1e-6'), Dc(1)
    with localcontext(V.CTX):
        def ok(x):
            f = vthw / (2 * sqrt(Iv(x))) - (mT + tc * imin(Iv(x) / 24, PII * t / 3))
            return f.lo >= 0
        assert ok(lo)
        for _ in range(60):
            m = (lo + hi) / 2
            if ok(m): lo = m
            else: hi = m
    return Iv(lo)


def consts_iv(La, Lb, eta=None, _o=None):
    """DX: eta (the ripple, sup|R|) is a separate argument; eta=None is eta = 1/ell, the published case (then et IS t and the arithmetic is unchanged)."""
    La, Lb = V.D(La), V.D(Lb); tail = Lb.is_infinite()
    L = Iv(La, Lb); t = 1 / L; o = {} if _o is None else _o
    et = t if eta is None else (eta if isinstance(eta, Iv) else Iv(V.D(eta)))
    if eta is not None and tail: raise NotImplementedError('the tail forms of a0 and (N0) use eta = 1/ell')
    eta = et; fl = 1 / (1 + et); Gs = sqrt(1 + C * t); G2s = Gs / (2 * (1 - et))
    o['Gam sqrt(ell)'] = Gs; o['Gam2 sqrt(ell)'] = G2s
    u1n = Dc('0.25') * sqrt(2 + Dc('3.1') * t) + Dc('1e-6') * sqrt(t); X1n = u1n / Dc('0.75'); CZ = et * et / (E * (1 - et) ** 2); o['X1/sqrt(ell)'] = X1n
    Bm = Dc('2.5e10'); q = (1 + et) / (400 * (1 - et)); z2 = Iv(Dc('0.01')); om = 1 / (1 + Iv(Dc('0.75')) / Bm) ** 2
    o['q_max'] = q; o['z2_max'] = z2
    kE = sqrt(Iv(Dc('0.2'))); k1 = 1 + (et + Dc('0.184')) * kE; o['k1_max'] = k1
    # ---- (F)
    F1P = 2 * ((Dc('1.25') / 16) * log(Iv(72)) + CI / 2); o['F1: P <='] = F1P
    w16 = exp(Iv(Dc('0.5'))) * ((1 + Dc(1) / 32) * (Dc(1) / 8) * (log(Iv(32)) + lB0(Iv(Dc(1) / 16), Iv(Dc(1) / 16))) + 2 * CI / 16); o['w16'] = w16
    # ---- (R)
    eps1 = et * kE * Dc('2.25') / Dc('1.25'); epsh = 2 * kE * (et + Dc('0.184')) / om; o['eps1_max'] = eps1; o['epsh_max'] = epsh
    o['c_S'] = (1 + et) / (4 * sqrt(PI)) + (Dc('0.184') + Dc('0.5') / Bm) * Dc('0.2') / (2 * sqrt(PI)) + et * et * (1 + Dc('0.25') / Bm) / (2 * sqrt(PI) * 2 * (1 - et))
    M4c = 3 * (1 + et * kE * Dc('0.0625') / Dc('1.5625')) + 6 * et * kE * Dc('0.25') / Dc('1.5625'); M4g = 3 * (Iv(1) / 24) / (2 * 4 * (1 - et))
    R4c = (M4c + M4g) / 2 + Dc('0.25') * Dc('0.25') * Dc('2.07') * kE + sqrt(Iv(Dc('3.75'))) * kE * sqrt(F1P) / 4 + Dc('1e-9'); o['R4: constants/sigma <='] = R4c
    thbg = sqrt((1 - eps1 - ES) * (1 - epsh - ES)); o['th_bg'] = thbg
    o['R4: e0 needed'] = R4c / (thbg * sqrt(Bm * om) - Dc('0.5')) + ES
    m1 = 1 - eps1 - E0; m4 = 1 - epsh - E0
    c1F = sqrt(m1 * m4 * om) - Dc('0.5') / sqrt(Iv(Bm)) - Gs * k1 * sqrt(Iv(Dc('0.5'))) * sqrt(t); o['c1F'] = c1F
    cF = (Dc('0.25') + Dc(1) / 16) / (1 - et); b0 = Dc('5e-4') * t / (cF * CT * C1)
    assert b0.hi <= Dc('0.1')                                                        # so min(b0, 0.1) = b0
    o['R5: K_F/sqrt(b) <='] = imax(Dc('5e-4') / G2s, 2 * cF * u1n ** 2 / 3 * sqrt(cF * CT * C1 / Dc('5e-4')) * pe(Dc('1.5'), L)) \
        + u1n ** 2 * pe(1, L) * sqrt(Iv(2) / 3 * Dc('0.7008') / 3) / (4 * (1 - et) ** 2)
    o['Case I (Fz): c1F - K_F/sqrt(b) - c1 (must be >= 0)'] = c1F - o['R5: K_F/sqrt(b) <='] - C1
    cs = sqrt(CZ / 2) + Dc('0.25') / sqrt(PI * Dc('2.25')); o['c_s'] = cs
    cB2n = X1n / (4 * sqrt(Iv(2)) * (1 - et)) + cs * sqrt(t) / (4 * (1 - et)); o['c_B2/sqrt(ell)'] = cB2n
    kf01 = Dc('0.81') * (1 - Iv(Dc('0.4')) / Dc('0.9') - z2 / 12); o['kf (b < 0.1)'] = kf01; cK = fl * kf01 / 16; o['cK'] = cK
    a2k = Dc('0.01') / (8 * (1 - et) * cK); o['Case I (Tz-B2): A2k/cKz <='] = a2k
    o['Case I (Tz-B2): [(1 - a2k - 1e-6) cK c_T sqrt(ell) - c_B2]/sqrt(ell) (must be >= 0)'] = (1 - a2k - Dc('1e-6')) * cK * CT - cB2n
    # ---- (c)
    cb = (G2s / (3 * C1)) ** 2; o['cb ell'] = cb; bI = cb * F1P ** 2 * t
    PII = 2 * ((1 + bI / 2) / 16 * (log(Iv(32)) + lB0(Iv(Dc(1) / 16), bI)) + CI * bI); o['P_II'] = PII
    bIIl = cb * PII ** 2; bII = bIIl * t; o['b_II ell'] = bIIl
    brk = 1 - 4 * bII / (1 - bII) - z2 / 12; kf = (1 - bII) ** 2 * brk; o['brk (Case II)'] = brk; o['kf (Case II)'] = kf
    tc = G2s * Gs * k1 / C1 ** 2; o['tc'] = tc; o['T_max ell'] = tc * PII / 3
    ckap = 2 * C1 ** 2 / (G2s ** 2 * w16 ** 2); o['c_kap'] = ckap
    o['[c_kap ell 4 - 16]/(4 ell) (must be > 0)'] = ckap - 4 * t
    o['16 b_II (must be <= 1)'] = 16 * bII
    ESS = pe(2, L)
    rhs = cB2n + G2s * (1 + ESS) * t
    chi1 = fl * kf * ckap / (16 * CCH) * (1 - Dc('1e-3')); chi2 = fl * kf * C1 ** 2 / (8 * G2s ** 2 * PII ** 2 * CCH) * (1 - Dc('1e-3'))
    o['II-ch: chi/sqrt(ell) lower bound (kappa <= 1)'] = chi1; o['II-ch: chi/sqrt(ell) lower bound (kappa > 1)'] = chi2; o['II-ch: needed (c_B2 + Gam2)/sqrt(ell)'] = rhs
    o['II-ch: slack (must be >= 0)'] = imin(chi1, chi2) - rhs
    o['II-ch: A2k + B2a relative to cKz <='] = 2 * bII ** 2 / ((1 - et) * fl * kf) + 4 * u1n * bIIl * t * Dc('0.5') / (sqrt(ckap) * (1 - et) ** 2 * fl * kf) \
        + 4 * u1n * bIIl ** Dc('1.5') * t / ((1 - et) ** 2 * fl * kf)
    IIs = fl * (1 - z2 / 2) / (4 * Dc('2.25')) * CCH / (1 + Dc('1e-9')); o['II-s: hFz/(sqrt(ell) G) lower bound'] = IIs; o['II-s: slack (must be >= 0)'] = IIs - rhs
    cmn = 2 * X1n * Dc('1.5') / ((1 - et) * fl * (1 - z2 / 2) * sqrt(2 * PI)); o['cm/sqrt(ell)'] = cmn
    o['II-s: log(a_s/sigma) <='] = log(4 * cmn ** 2 / CCH) + log(pe(Dc('6.5'), L))
    cu1 = 2 * X1n / (sqrt(ckap) * (1 - et) * fl * kf); cu2 = 2 * X1n * G2s * sqrt(Iv(Dc('0.5'))) * PII / (C1 * (1 - et) * fl * kf)
    cu = imax(cu1, cu2) * (1 + sqrt(Iv(2)) * cs * sqrt(t) / X1n) + 4 * u1n * bIIl * t / (sqrt(ckap) * (1 - et) ** 2 * fl * kf); o['c_u'] = cu
    # ---- (II-m)
    m2 = 1 - 3 * ESS; m3 = 1 - t ** 3; mT = 1 + ESS; th0 = (1 - et) / (1 + et) * sqrt((1 - q) * (1 - z2 / 2)); o['th0'] = th0
    vth0 = th0 * (Iv(8) / 9) / Gs * sqrt(m2 * m3); o['vth0'] = vth0; Tm = o['T_max ell'] * t
    c0lo = sqrt(m3 * (1 - z2 / 2)); o['c0 >='] = c0lo
    m1mul = XI1 ** 2 / (c0lo ** 2 * CCH ** 2); o['m1: mu ell <'] = m1mul
    m1Y = m3 * fl * (1 - z2 / 2) * CCH / (8 * Dc('2.25')); o['m1: Y/(2 sigma)/(sqrt(ell) G) >='] = m1Y
    o['m1: slack 1 (must be >= 0)'] = m1Y - G2s * (mT + Tm) * t
    o['m1: [Th*/sqrt2 - (mT + Tm)]/ell (must be >= 0)'] = vth0 / (2 * sqrt(m1mul) * sqrt(Iv(2))) - (mT + Tm) * t
    rb8 = sqrt(m1 / (m4 * Bm * om) + 1 / XI1 ** 2); o['rhobar (xi >= 8)'] = rb8
    xn = (vth0 * (1 - rb8 / 2) / (2 * (mT + Tm))) ** 2; o['x_n'] = xn; mun = xn * L; o['mu_n'] = mun
    cJ = C1 ** 2 / (8 * E * G2s ** 2); o['c_J'] = cJ
    o['m3: 16 b e^mu at mu_n (must be <= 1)'] = 16 * cb * (4 * Dc('2.25') * Dc('1.02')) ** 2 * xn * pe(1, mun)
    EJn = E_J(mun)
    o['m3: [c_J ell e^mu - 16 mu^2 E_J^2 r]/(ell e^mu) at mu_n, r = 1/4 (must be > 0)'] = cJ - 4 * pe(2, mun) * EJn ** 2 * t
    m5n = 1 - cu * sqrt(ESS / (c0lo * sqrt(mun))) - Dc('2.1') * bII ** 2; o['m3: m5 >='] = m5n
    o['m3: log Ch(ell, mu_n)'] = log(m5n * fl * kf * cJ * c0lo / (16 * G2s)) + H(xn, L, 2, 3, Dc('2.5')) - 2 * log(EJn)
    o['m3: slack (must be >= 0)'] = o['m3: log Ch(ell, mu_n)'] - log(mT + Tm)
    # ---- (m4)
    rho_max = sqrt(m1 / (m4 * Bm * om) + t ** 4); o['rho_max (wide)'] = rho_max
    vthw = vth0 * (1 - rho_max / 2); o['vth0 (1 - rho/2) (wide)'] = vthw
    x0 = x0_cert(vthw, mT, tc, PII, t); o['x0 (certified lower bound)'] = x0; mu2 = x0 * L; o['mu_II'] = mu2; cbl = cb * t; mub = imin(mu2, mun)
    o['b.1 first pass: 0.065 mu c_b P <='] = 2 * CI * Dc('14.29') * cbl; o['b.1 first pass: mu b/2 <='] = Dc('9.545') * cbl
    p1 = 4 * Dc('2.25') * exp(o['b.1 first pass: mu b/2 <=']) / (1 - o['b.1 first pass: 0.065 mu c_b P <=']); o['b.1 first pass: P/(mu e^-mu) <='] = p1
    Xt = cb * p1 ** 2 * pe(3, 2 * mub) / 16; Yt = 2 * CI * cb * p1 * pe(2, mub); Xv = Xt * t; Yv = Yt * t
    o['b.1 second pass: [E_CM formula - derived bound]/((1 + 3.445 e^{-mu/2})^2 t) at mu_n (must be >= 0)'] = Dc('2e-3') - (Xt * exp(Xv) + Yt) / (1 - Yv)
    o['c_G'] = C1 * sqrt(Bm) / G2s
    lt = lol(L)
    o['b.2: G/sigma at mu = ell + ln ell <='] = (Iv(4) / 3) * (1 + lt) * E_CM(L + log(L), t)
    o['Th_min'] = vthw / (2 * sqrt(1 + lt)); ecm2 = E_CM(mu2, t); Tbar2 = tc * (Iv(4) / 3) * pe(1, mu2) * ecm2; o['Tbar(mu_II) ell'] = Tbar2
    o['b.5: mT + Tbar (must be <= 1.002)'] = mT + Tbar2 * t
    Umax = ((mT + Tbar2 * t) / o['Th_min']) ** 2 - 1; o['U_max'] = Umax
    rcoef = Umax ** 2 / (2 * (m1 / m2) ** 2); o['r bound coefficient'] = rcoef
    rmax = rcoef * ecm2 ** 2 * pec(0, 2 * x0, L); o['b.4: r <= (at mu_II)'] = rmax; kEc = sqrt(rmax)
    m1c = 1 - Dc('2.25') * et * kEc - E0; m4c = 1 - 2 * kEc * (et + Dc('0.184')) / om - E0; m5c = 1 - cu * kEc - Dc('2.1') * bII ** 2
    o['m4: m1 after (b.4) >='] = m1c; o['m4: m4 after (b.4) >='] = m4c; o['m4: m5 after (b.4) >='] = m5c
    mprod = (m1c / m2) ** 3 * (m4c / m3) * m5c; o['m4: factor of K'] = mprod
    ck = Dc('0.999') * 2 * (1 - et) / (16 * (1 + et) * Gs) * m5c; o['c_k'] = ck
    ej2 = E_J(mu2)
    if Lb > Dc('397.6'):                                                             # (b.5): only where B < ell^4 can happen (2.5e10 < ell^4)
        L5 = Iv(max(La, Dc('397.6')), Lb); mu5 = x0 * L5
        o['b.5: u lower bound (kappa_b = kappa), ell >= 397.6, mu >= x0 ell'] = (m1c / m2) * sqrt(2 * ck / (E * Dc('1.002'))) * Dc('0.999') * exp(H(x0, L5, 1, Dc('1.5'), Dc('0.75'))) / E_J(mu5)
    q4 = (8 * t ** 3 + 100 * t ** 4) * (1 + et) / (8 * (1 - et)); z4 = (8 * t ** 3 + 100 * t ** 4) / 2
    rho4n = sqrt(m1c * (1 + Dc('0.75') * t ** 4) ** 2 / m4c + 1)                         # rho4 = t^2 rho4n
    e1 = (8 * t + 100 * t * t) * (1 + et) / (8 * (1 - et)) + (8 * t + 100 * t * t) / 4 + 3 * pe(4, L) + t + rho4n / 2 + rcoef * ecm2 ** 2 * pec(2, 2 * x0, L) / 2
    o['eps1 ell^2'] = e1
    A = (1 - et) / ((1 + et) * Gs); th1 = A * (1 - e1 * t * t); o['th1'] = th1
    bmax = 4 * cb * t * pec(2, Iv(2), mu2) * ecm2 ** 2; o['kf (corner)'] = 1 - 6 * bmax - z4 / 12 - Dc('1e-10')
    o['beta-case: log(u^3 v lower bound/U_max^4) (must be >= 0)'] = log((m1c / m2) ** 3 * (m4c / m3) * (1 - Dc('1e-10')) / (4 * E ** 2 * 256 * cb * ej2 ** 4 * ecm2 ** 2)) \
        + H(x0, L, 4, 2, 3) - 4 * log(Umax)
    muN = L / 4 - Dc('3.75'); mFt = Dc('0.375') * lt + t; o['m_F t'] = mFt
    ecmN = E_CM(muN, t); ejN = E_J(muN); TNl = tc * (Iv(4) / 3) * pe(1, muN) * ecmN; o['Tbar_N ell'] = TNl
    ThN = th1 / sqrt(1 + 4 * mFt); o['Th_N'] = ThN; UN = ((mT + TNl * t) / ThN) ** 2 - 1; o['U_N'] = UN; aN = ThN * lq(UN) / 2; o['a_N'] = aN
    kN = mprod * o['kf (corner)'] * (1 - et) / (2 * E * ejN ** 2 * ecmN ** 2 * Gs); o['k_N'] = kN
    CN = 5 * exp(log(aN ** 4 * kN / 27) * Dc('0.2')) * exp(log(Iv(4)) * Dc('0.4')) * exp(log(1 + 4 * mFt) * Dc('-0.4')); o['C_N'] = CN
    dl0 = (log(Dc('0.4') * CN) + Dc('0.7') * log(L)) / Dc('0.8'); o['dl_0'] = dl0
    if not tail:
        a0 = L * (mT + TNl * t - th1)
    else:
        a0 = pe(3, L) + TNl + 7 + e1 * t                                           # ell (1 - th1) <= 7 + eps1' t: A >= (1 - 2t)(1 - 5t) >= 1 - 7t, A <= 1
    o['a0'] = a0; o['a0/th1'] = a0 / th1
    o['N: 2.5 + 2 dl_0 - a0/th1 (must be >= 0)'] = Dc('2.5') + 2 * dl0 - a0 / th1
    if not tail:
        o['N0: th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II)) (must be >= 0)'] = th1 / sqrt(1 - 15 * t) - (mT + Tbar2 * t)
    else:
        o['N0: [th1 (1 - 15/ell)^{-1/2} - (mT + Tbar(mu_II))]/t (must be >= 0)'] = Dc('0.5') - Dc('52.5') * t - e1 * t * (1 + Dc('0.5') * t) - pe(3, L) - Tbar2
    o['N0: 3.75 - a0/(2 th1) (must be >= 0)'] = Dc('3.75') - a0 / (2 * th1)
    o['F left'] = 16 * E ** 4 * kN * th1 ** 8; o['F right'] = (mT + Tbar2 * t) ** 9 * (1 + 4 * mFt) ** 6
    o['F: left - right (must be >= 0)'] = o['F left'] - o['F right']
    return o


# the bounds the proof quotes as valid for every ell (DJ_証明まとめ.md; dj_proof.check_consts), as (key, sense, bound)
QUOTED = [('F1: P <=', '<=', '0.7008'), ('w16', '<=', '0.8972'), ('eps1_max', '<=', '0.01457'), ('epsh_max', '<=', '0.1808'), ('c_S', '<=', '0.155'),
          ('R4: constants/sigma <=', '<=', '1.77'), ('R4: e0 needed', '<=', '1.26e-5'), ('th_bg', '>=', '0.8985'), ('c1F', '>=', '0.7857'),
          ('R5: K_F/sqrt(b) <=', '<=', '1.01e-3'), ('c_s', '<=', '0.102'), ('c_B2/sqrt(ell)', '<=', '0.0896'), ('kf (b < 0.1)', '>=', '0.4493'), ('cK', '>=', '0.02758'),
          ('Case I (Tz-B2): A2k/cKz <=', '<=', '0.04616'), ('cb ell', '<=', '0.05593'), ('P_II', '<=', '0.5223'), ('b_II ell', '<=', '0.01526'), ('brk (Case II)', '>=', '0.998'),
          ('kf (Case II)', '>=', '0.9975'), ('tc', '<=', '1.0779'), ('T_max ell', '<=', '0.1877'), ('c_kap', '>=', '4.935'), ('c_u', '<=', '0.48'), ('vth0', '>=', '0.7858'),
          ('m1: mu ell <', '<=', '7.7'), ('rhobar (xi >= 8)', '<=', '0.12501'), ('x_n', '>=', '0.1347'), ('mu_n', '>=', '7.44'), ('c_J', '>=', '0.0913'),
          ('m3: log Ch(ell, mu_n)', '>=', '2.8332'), ('x0 (certified lower bound)', '>=', '0.1531'), ('mu_II', '>=', '8.46'), ('r bound coefficient', '<=', '18.7'),
          ('m4: factor of K', '>=', '0.997'), ('eps1 ell^2', '<=', '0.80'), ('U_max', '<=', '5.96'), ('b.2: G/sigma at mu = ell + ln ell <=', '<=', '1.5'), ('c_G', '>=', '2.2e5'),
          ('b.5: u lower bound (kappa_b = kappa), ell >= 397.6, mu >= x0 ell', '>=', '6.0'), ('b.4: r <= (at mu_II)', '<=', '1e-6'), ('II-s: log(a_s/sigma) <=', '<=', '-29.89'),
          ('II-ch: A2k + B2a relative to cKz <=', '<=', '1e-3'), ('m4: m1 after (b.4) >=', '>=', '0.9994'), ('m4: m4 after (b.4) >=', '>=', '0.9994'), ('m4: m5 after (b.4) >=', '>=', '0.9994'),
          ('c_k', '>=', '0.1107'), ('b.1 first pass: P/(mu e^-mu) <=', '<=', '9.18')]
#  m3: log Ch >= 2.8332 is Ch >= 17 (e^2.8332 = 16.99..).


SENSE = {}     # name -> 'max' (an upper bound is checked: the worst is the largest value) or 'min'


def checks(o):
    """every condition and every quoted bound: name -> (ok, the relevant end as a float)."""
    out = {}
    for k, v in o.items():
        if 'must be' not in k: continue
        if '<= 1.002' in k: out[k] = (v.hi <= Dc('1.002'), float(v.hi)); SENSE[k] = 'max'
        elif '<= 1)' in k: out[k] = (v.hi <= 1, float(v.hi)); SENSE[k] = 'max'
        elif '> 0' in k: out[k] = (v.lo > 0, float(v.lo)); SENSE[k] = 'min'
        else: out[k] = (v.lo >= 0, float(v.lo)); SENSE[k] = 'min'
    for k, s, b in (WRONG.get('quoted') or QUOTED):
        if k not in o: continue                                                      # (b.5) below 397.6: not applicable
        v = o[k]; nm = 'quoted: %s %s %s' % (k, s, b)
        out[nm] = (v.hi <= Dc(b), float(v.hi)) if s == '<=' else (v.lo >= Dc(b), float(v.lo)); SENSE[nm] = 'max' if s == '<=' else 'min'
    return out


def run(ratio=Dc('1.001'), save=True, fn='results/dl_consts.json'):
    t0 = time.time(); pieces = []; La = ELL1; worst = {}; nsplit = 0; fails = []
    stack = []
    while La < ELL_TAIL:
        Lb = min(La * ratio, ELL_TAIL); stack.append((La, Lb, 0)); La = Lb
    stack.reverse()
    while stack:
        a, b, d = stack.pop()
        try:
            r = checks(consts_iv(a, b)); bad = [k for k, (ok, v) in r.items() if not ok]
        except Exception as e:
            r = {}; bad = ['exception: ' + repr(e)[:120]]
        if bad and d < 12:
            m = (a * b).sqrt(); stack.append((m, b, d + 1)); stack.append((a, m, d + 1)); nsplit += 1; continue
        if bad: fails.append({'piece': [str(a), str(b)], 'failed': bad[:8]})
        pieces.append((float(a), float(b)))
        for k, (ok, v) in r.items():
            if k not in worst or (v > worst[k][1] if SENSE[k] == 'max' else v < worst[k][1]):
                worst[k] = (ok, v, float(a))
    # the tail
    try:
        rt = checks(consts_iv(ELL_TAIL, Dc('Infinity'))); tailbad = [k for k, (ok, v) in rt.items() if not ok]
    except Exception as e:
        rt = {}; tailbad = ['exception: ' + repr(e)[:160]]
    out = {'pieces of [55.26, 1e6]': len(pieces), 'splits': nsplit, 'pieces that fail (must be empty)': fails, 'tail [1e6, inf): failing (must be empty)': tailbad,
           'tail [1e6, inf): values': {k: v for k, (ok, v) in rt.items()},
           'worst over [55.26, 1e6] (ok, value, at the left end of the piece)': worst, 'seconds': time.time() - t0}
    out['ok'] = bool(not fails and not tailbad and rt)
    if save: json.dump(out, open(fn, 'w'), indent=1)
    return out


# POWER: deliberately wrong versions must produce failing pieces (run on the first 30 pieces, the last 5 pieces below 1e6 and the tail)
WRONG = {}


def _q(key, sense, bound): return [(k, s, (bound if k == key else b)) for k, s, b in QUOTED]


WRONG_VERSIONS = {
    'eps1 ell^2 <= 0.76 (the number of DJ)': {'quoted': _q('eps1 ell^2', '<=', '0.76')},
    'A2k/cKz <= 0.0461 (the table row of DJ without the 1e-6)': {'quoted': _q('Case I (Tz-B2): A2k/cKz <=', '<=', '0.0461')},
    'c1F >= 0.7858': {'quoted': _q('c1F', '>=', '0.7858')},
    'K_F/sqrt(b) <= 0.0009999 (fails only near 1e6 and in the tail)': {'quoted': _q('R5: K_F/sqrt(b) <=', '<=', '0.0009999')},
    'c1 = 0.7905 (the rule constant of Case I)': {'C1': Dc('0.7905')},
}


def power(save=True, fn='results/dl_consts_power.json'):
    global C1
    t0 = time.time(); r = Dc('1.001'); edges = [ELL1]
    while edges[-1] < ELL_TAIL: edges.append(min(edges[-1] * r, ELL_TAIL))
    pcs = list(zip(edges[:-1], edges[1:])); pcs = pcs[:30] + pcs[-5:] + [(ELL_TAIL, Dc('Infinity'))]
    out = {}; c1keep = C1
    for name, w in WRONG_VERSIONS.items():
        WRONG.clear(); WRONG.update(w); C1 = w.get('C1', c1keep); nbad = 0; where = []
        try:
            for a, b in pcs:
                bad = [k for k, (ok, v) in checks(consts_iv(a, b)).items() if not ok]
                if bad: nbad += 1; where.append([str(a), bad[0]]) if len(where) < 3 else None
        finally:
            WRONG.clear(); C1 = c1keep
        out[name] = {'pieces checked': len(pcs), 'failing pieces': nbad, 'caught': nbad > 0, 'first failures': where}
        print(name, out[name]['failing pieces'], flush=True)
    out['ok'] = all(v['caught'] for v in out.values()); out['seconds'] = time.time() - t0
    if save: json.dump(out, open(fn, 'w'), indent=1)
    return out


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'power':
    print(power()['ok'])
elif __name__ == '__main__':
    r = run(); print(r['ok'], r['pieces of [55.26, 1e6]'], r['splits'], r['pieces that fail (must be empty)'][:3], r['tail [1e6, inf): failing (must be empty)'])
