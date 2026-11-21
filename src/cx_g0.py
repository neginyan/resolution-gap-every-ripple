"""Stage CX 2.2: the G = 0 states as a PROOF, and its step-by-step check in 60-digit decimal at random states, with deliberately wrong versions.
Python 3.11 grammar.  -> results/cx_g0.json

THEOREM G0 [proof].  Let the window have G = 0 (P = 2 x E1 = 0).  For every sigma > 0, b in (0, 1], L > 0 with L^2 >= 4 sigma^2 (this follows from
sigma^2 <= s^2 <= L^2/4), every tau, mu, kappa, x:
    (a) + (a') >= min(0.316/sigma, C0/sqrt(b)),   C0 = (3/2) sqrt(k/128) = 0.19950...,  k = 3 - 2/e.
For sigma <= e^{-55.26} and b <= 1 the right side is >= C0 = 0.1995 > 0.13972 >= gamma(ell) = T_0(ell)/sqrt(ell) for every ell >= 55.26.
PROOF.
 (1) G = 0 means E1 = E_rho[R'^2] = 0, so R' = 0 on the line (the Gaussian average has full support), R is constant, and its mean is 0 (no n = 0 term):
     R = 0 and h = 1.  The state is p = N_V(v) Gamma(w), V = sigma^2/b, Gamma = N(0, L^2); s_v = -v/V, s_w = -w/L^2, J_vv = 1/V, J_ww = 1/L^2.
 (2) v + sigma^2 s_v = (1 - b) v and w + sigma^2 s_w = (1 - sigma^2/L^2) w.  With v = sqrt(V) X, w = L Y (X, Y independent N(0, 1)),
     m_z = a X + c Y,  a = sqrt(V)(1 - b)/sqrt2 = sigma (1 - b)/sqrt(2 b),  c = (L - sigma^2/L)/sqrt2.
 (3) E[X^2 cos(aX + cY)] = (1 - a^2) e^{-(a^2+c^2)/2} (and the same with Y, c): expand cos(aX + cY) = cos aX cos cY - sin aX sin cY; E sin cY = 0;
     E cos cY = e^{-c^2/2}; E X^2 cos aX = -(d^2/da^2) e^{-a^2/2} = (1 - a^2) e^{-a^2/2}.  With phi = 1 - cos m_z and e := e^{-(a^2+c^2)/2}:
     E[s_w^2 phi] = (1/L^2)(1 - (1 - c^2) e),  E[s_v^2 phi] = (1/V)(1 - (1 - a^2) e),  den = sigma^2 (1/V + 1/L^2),
     2 A_w = 2 sigma^2 E[s_w^2 (1 - phi/4)] = (sigma^2/(2 L^2)) A1,  N_phi = (sigma^2/2) E[s_v^2 phi] = (sigma^2/(2V)) A2,
     A1 = 3 + (1 - c^2) e,  A2 = 1 - (1 - a^2) e,   so   Q := (a) + (a') = (2 A_w + N_phi)/(sigma den) = [A1/L^2 + A2/V] / [2 sigma (1/L^2 + 1/V)].
 (4) A1 >= k = 3 - 2/e:  (1 - c^2) e >= -c^2 e^{-c^2/2} >= -max_t t e^{-t/2} = -2/e.
 (5) A2 >= 1 - e^{-c^2/2}:  if a^2 <= 1, (1 - a^2) e <= (1 - a^2) e^{-a^2/2} e^{-c^2/2} <= e^{-c^2/2}; if a^2 > 1, (1 - a^2) e < 0.
 (6) c^2 >= (9/32) L^2:  sigma^2/L^2 <= 1/4, so c^2 = (L^2/2)(1 - sigma^2/L^2)^2 >= (L^2/2)(3/4)^2.
 (7) Put y = L^2, z = 9y/64 (so c^2/2 >= z), B = 1/V = b/sigma^2.  Q is the average of A1/(2 sigma) and A2/(2 sigma) with weights 1/y and B, so
     2 sigma Q >= F := lam k + (1 - lam)(1 - e^{-z}),  lam = (1/y)/(1/y + B) = sigma^2/(sigma^2 + b y).
     Case z >= 1:  1 - e^{-z} >= 1 - 1/e, so F >= min(k, 1 - 1/e) = 0.632, Q >= 0.316/sigma.
     Case z <= 1:  1 - e^{-z} >= z - z^2/2 >= z/2, so F >= (sigma^2 k + alpha y^2)/(sigma^2 + b y), alpha = (9/128) b; the numerator is
       >= max(sigma^2 k, 2 sigma y sqrt(k alpha)) (AM-GM).  If b y <= sigma^2 the denominator is <= 2 sigma^2 and F >= k/2;  if b y >= sigma^2 it is
       <= 2 b y and F >= sigma sqrt(k alpha)/b = sigma sqrt(9k/128)/sqrt(b).  So Q >= min(k/(4 sigma), (1/2) sqrt(9k/128)/sqrt(b)) = min(k/(4 sigma), C0/sqrt(b)).
 (8) k/4 = 0.566 > 0.316, so Q >= min(0.316/sigma, C0/sqrt(b)).  gamma(ell) = (1 + 2.1/ell + 2.5e-4)/sqrt(ell) decreases in ell, gamma(55.26) = 0.13972.  QED.
REMARKS.  The bound does not use tau, mu, kappa, x (the state at G = 0 does not depend on them), nor b <= 0.5: it holds on all of b in (0, 1].
The true minimum over L is Q ~ 1/sqrt(b) (stage CW; the main line's check Q sqrt(b) = 1.0002 at b = 0.5); C0 = 0.1995 is about 5 times below it.

CHECK (this module, 60-digit decimal):  each step at random states: (3) the Gaussian identity by the trapezoid rule in decimal (h = 0.1 on [-40, 40]:
aliasing error < e^{-(2 pi/h - |a|)^2/2} < 1e-600 for |a| <= 10; the sums in 200 digits since they cancel down to e^{-100}, truncation < e^{-800}); the closed form of (3) against ca_reduction.direct (float,
moderate sigma); the inequalities (4)-(8) at every state, in the order of the proof.  Deliberately wrong versions (must fail somewhere):
  WG1 (1 + a^2) in place of (1 - a^2) in (3);  WG2 k = 3 - 1/e in (4);  WG3 c^2 >= L^2/2 in (6);  WG4 C0 -> 1.2 (the true Q sqrt(b) ~ 1);
  WG5 1 - e^{-z} >= z on z <= 1 in (7)."""
import json, math, os, sys
from decimal import Decimal, getcontext
import numpy as np
import ca_reduction as CA          # imported first: its ca_dec sets the decimal context, which is then reset to 60 digits here

HERE = os.path.dirname(os.path.abspath(__file__))
C = getcontext(); C.prec = 60; C.Emax = 999999999999999999; C.Emin = -999999999999999999
D = Decimal


def _pi():
    C.prec += 10
    def arctan_inv(n):
        x = D(1) / n; x2 = x * x; s = x; t = x; k = 1
        while True:
            t = -t * x2; k += 2; d = t / k
            if abs(d) < D(10) ** (-(C.prec + 5)): break
            s += d
        return s
    p = 4 * (4 * arctan_inv(5) - arctan_inv(239)); C.prec -= 10
    return +p


PI = _pi()


def dexp(x): return D(x).exp()


def dexpm1(x):
    """e^x - 1 without cancellation (series for |x| < 1e-3)."""
    x = D(x)
    if abs(x) >= D('1e-3'): return x.exp() - 1
    s = D(0); t = D(1); k = 0
    while True:
        k += 1; t = t * x / k
        if abs(t) <= abs(s) * D(10) ** (-(C.prec + 5)) and k > 1: break
        s += t
    return s


def ge(l, r): return l >= r - abs(r) * D('1e-50')     # >= up to 50-digit rounding (equality cases, e.g. L^2 = 4 sigma^2 in (6))


def dcos(x):
    x = D(x); x = x - (2 * PI) * (x / (2 * PI)).to_integral_value()
    C.prec += 10; s = D(1); t = D(1); k = 0; x2 = x * x
    while True:
        k += 2; t = -t * x2 / (k * (k - 1))
        if abs(t) < D(10) ** (-(C.prec + 5)): break
        s += t
    C.prec -= 10
    return +s


def gauss_X2cos(a, h=D('0.1'), L=40):
    """E[X^2 cos(a X)] by the trapezoid rule in decimal."""
    n = int(L / h); s = D(0)
    for i in range(-n, n + 1):
        x = i * h; s += x * x * dexp(-x * x / 2) * dcos(a * x)
    return s * h / (2 * PI).sqrt()


def gauss_cos(c, h=D('0.1'), L=40):
    n = int(L / h); s = D(0)
    for i in range(-n, n + 1):
        x = i * h; s += dexp(-x * x / 2) * dcos(c * x)
    return s * h / (2 * PI).sqrt()


K = 3 - 2 / dexp(1); C0 = D(3) / 2 * (K / 128).sqrt()


def gamma(ell): ell = D(ell); return (1 + D('2.1') / ell + D('2.5e-4')) / ell.sqrt()


def Q_exact(lsig, lb, ly, wrong=None):
    """the closed form of (3) at sigma = e^lsig, b = e^lb, L^2 = e^ly (decimal)."""
    sig = dexp(lsig); b = min(dexp(lb), D(1)); y = max(dexp(ly), 4 * sig * sig); L = y.sqrt(); V = sig * sig / b     # the state set: b <= 1, L^2 >= 4 sigma^2 (exact)
    a = sig * (1 - b) / (2 * b).sqrt(); c = (L - sig * sig / L) / D(2).sqrt()
    e = dexp(-(a * a + c * c) / 2)
    A1 = 3 + (1 - c * c) * e
    A2 = (-dexpm1(-(a * a + c * c) / 2) - a * a * e) if wrong == 'WG1' else (-dexpm1(-(a * a + c * c) / 2) + a * a * e)   # 1 - (1 -+ a^2) e
    return (A1 / y + A2 / V) / (2 * sig * (1 / y + 1 / V)), A1, A2, a, c, sig, b, y


def steps(lsig, lb, ly, wrong=None):
    assert C.prec == 60
    """every inequality of the proof at one state; returns the list of (name, holds, lhs, rhs)."""
    Q, A1, A2, a, c, sig, b, y = Q_exact(lsig, lb, ly, wrong)
    k = (3 - 1 / dexp(1)) if wrong == 'WG2' else K
    out = []
    out.append(('(4) A1 >= k', ge(A1, k), A1, k))
    out.append(('(5) A2 >= 1 - e^{-c^2/2}', ge(A2, -dexpm1(-c * c / 2)), A2, -dexpm1(-c * c / 2)))
    c2lo = (y / 2) if wrong == 'WG3' else (D(9) / 32 * y)
    out.append(('(6) c^2 >= (9/32) L^2', ge(c * c, c2lo), c * c, c2lo))
    B = b / (sig * sig); lam = (1 / y) / (1 / y + B); z = c2lo / 2
    Fv = lam * k + (1 - lam) * (-dexpm1(-z))
    out.append(('(7a) 2 sigma Q >= F', ge(2 * sig * Q, Fv), 2 * sig * Q, Fv))
    if z >= 1:
        out.append(('(7b) F >= 0.632 (z >= 1)', ge(Fv, D('0.632')), Fv, D('0.632')))
        lower = D('0.316') / sig
    else:
        g = z if wrong == 'WG5' else z / 2
        out.append(('(7c) 1 - e^{-z} >= z/2 (z <= 1)', ge(-dexpm1(-z), g), -dexpm1(-z), g))
        Fl = (sig * sig * k + (D(9) / 128) * b * y * y) / (sig * sig + b * y)
        out.append(('(7d) F >= (sigma^2 k + alpha y^2)/(sigma^2 + b y)', ge(Fv, Fl), Fv, Fl))
        rhs = min(k / 2, sig * (D(9) * k / 128).sqrt() / b.sqrt())
        out.append(('(7e) ... >= min(k/2, sigma sqrt(9k/128)/sqrt b)', ge(Fl, rhs), Fl, rhs))
        lower = min(k / (4 * sig), ((D('1.2') if wrong == 'WG4' else C0)) / b.sqrt())
    final = min(D('0.316') / sig, (D('1.2') if wrong == 'WG4' else C0) / b.sqrt())
    out.append(('(8) Q >= min(0.316/sigma, C0/sqrt b)', ge(Q, final), Q, final))
    return out, Q, final


def states(n, seed):
    rng = np.random.default_rng(seed); S = []
    for i in range(n):
        ell = float(rng.choice([55.26, 961.0])) if i % 7 == 0 else float(rng.uniform(55.26, 961.0)); lsig = -ell
        u = rng.random()
        lb = 0.0 if u < 0.05 else (-2 * ell - 5 if u < 0.1 else float(rng.uniform(-2 * ell - 5, 0.0)))
        lylo = math.log(4) + 2 * lsig; lyhi = -lsig
        v = rng.random()
        if v < 0.05: ly = lylo
        elif v < 0.10: ly = lyhi
        elif v < 0.15: ly = math.log(4.0) + float(rng.normal(0, 0.3))          # c^2 ~ 2: where step (4) is tight
        elif v < 0.45:            # near the minimising L: y ~ sqrt(64 k V/9), V = sigma^2/b
            ly = 0.5 * (math.log(64 * 2.2642 / 9) + 2 * lsig - lb) + float(rng.normal(0, 1.5)); ly = min(max(ly, lylo), lyhi)
        else: ly = float(rng.uniform(lylo, lyhi))
        S.append((lsig, lb, ly, ell))
    return S


def run(n=2000, seed=23):
    R = {}
    # (3) the Gaussian identity in decimal at (a, c) pairs (small, moderate, up to 20)
    rng = np.random.default_rng(seed + 1); ac = [(D(0), D(0)), (D('1e-30'), D('1e-30')), (D(1), D(1)), (D(10), D('0.5'))]
    ac += [(D(repr(float(x))), D(repr(float(y)))) for x, y in rng.uniform(0, 10, (16, 2))]
    worst3 = D(0); worst3w = D(0); C.prec = 200          # the sum cancels down to e^{-(a^2 + c^2)/2} >= e^{-100}: 200 digits keep 60+ of them
    for a, c in ac:
        num = gauss_X2cos(a) * gauss_cos(c); cl = (1 - a * a) * dexp(-(a * a + c * c) / 2); clw = (1 + a * a) * dexp(-(a * a + c * c) / 2)
        sc = max(abs(cl), dexp(-(a * a + c * c) / 2), D('1e-300'))
        worst3 = max(worst3, abs(num - cl) / sc); worst3w = max(worst3w, abs(num - clw) / sc)
    C.prec = 60
    R['(3) Gaussian identity: max |trapezoid - closed| / e^{-(a^2+c^2)/2} (20 pairs, a, c in [0, 10]; 200-digit sums)'] = float(worst3)
    R['WG1 identity with (1 + a^2): max relative deviation'] = float(worst3w)
    # (3) the closed form against the physical quadrature (float, moderate sigma), ca_reduction.direct
    rr = np.random.default_rng(seed + 2); dev = 0.0
    for _ in range(6):
        sig = 10 ** rr.uniform(-1.6, -1.0); b = 10 ** rr.uniform(-1.5, -0.4); L2 = max(10 ** rr.uniform(-2.0, -0.5), 8.5 * sig ** 2); s2 = L2 / 8
        dd = CA.direct(sig, 0.01, b, L2, s2, [0.0], [0.0], nv=4000, nw=900)['sum']
        cf = float(Q_exact(math.log(sig), math.log(b), math.log(L2))[0]); dev = max(dev, abs(dd - cf) / cf)
    R['(3) closed form vs ca_reduction.direct (6 states, sigma 0.025-0.1): max rel. diff'] = dev
    # (4)-(8) at random states
    S = states(n, seed); fails = {}; minratio = None; worst = None; qs = []
    for lsig, lb, ly, ell in S:
        st, Q, final = steps(lsig, lb, ly)
        for name, ok, l, r in st:
            if not ok: fails.setdefault(name, []).append([lsig, lb, ly])
        rat = Q / final; qs.append(float(Q * dexp(lb).sqrt()))
        if minratio is None or rat < minratio: minratio = rat; worst = {'log_sigma': lsig, 'log_b': lb, 'log_L2': ly, 'Q': float(Q), 'bound': float(final)}
    R['states'] = len(S); R['steps_failing'] = {k: len(v) for k, v in fails.items()}; R['min Q / bound'] = float(minratio); R['worst'] = worst
    R['Q sqrt(b) over the states (min, median)'] = [min(qs), float(np.median(qs))]
    R['C0'] = float(C0); R['gamma(55.26)'] = float(gamma(55.26)); R['C0 > gamma(55.26)'] = bool(C0 > gamma(55.26))
    g = [gamma(55.26 + 10 * i) for i in range(100)]; R['gamma decreasing on the grid 55.26 .. 1045'] = all(g[i + 1] < g[i] for i in range(99))
    # deliberately wrong versions
    W = {}
    for w in ('WG1', 'WG2', 'WG3', 'WG4', 'WG5'):
        nf = 0
        for lsig, lb, ly, ell in S[:600]:
            st, Q, final = steps(lsig, lb, ly, wrong=w)
            if not all(ok for _, ok, _, _ in st): nf += 1
        W[w] = nf
    W['WG1 also: identity deviation'] = float(worst3w)
    R['wrong_versions: states (of 600) where a step fails'] = W
    return R


if __name__ == '__main__':
    R = run(int(sys.argv[1]) if len(sys.argv) > 1 else 2000)
    json.dump(R, open(os.path.join(HERE, 'results', 'cx_g0.json'), 'w'), indent=1); print(json.dumps(R, indent=1))
