"""Stage CZ: 60-DIGIT CHECKS of the closed forms and constants used in Lemmas CZ-1 ... CZ-5.  Python 3.11 grammar, decimal module (70 digits; mpmath is
not available in the lab).  Gaussian averages are computed by the trapezoid rule with a step of at most 1/5 of the width of the integrand (for an entire
integrand of Gaussian decay the error is below e^{-2 pi^2/h^2} <= e^{-493} in units of the width).
  (X1) the averages over w:  int Gamma E = k_E,  int Gamma E cos(w/sqrt2) = k_E e^{-se_E/4},  int Gamma E^2 = g_s,  int Gamma E^2 cos(w/sqrt2) =
       g_s e^{-se2/4},  int Gamma E^2 w^2 = g_s se2,  int Gamma E^2 |w| = g_s sqrt(2 se2/pi)      (Gamma = N(0, L^2), E = e^{-w^2/(2 s^2)}).
  (X2) the main identity of Lemma CZ-2 for one harmonic R = cos(n t - phi), t = sqrt(tau) s^, u = n^2 tau, e = e^{-y/2}, any e_E in [0, 1]:
       E[(s^^2 cos(n t - phi) + 2 sqrt(u) s^ sin(n t - phi)) (1 - e_E cos(sqrt(y) s^))]
           = (1 - e_E)(1 + u) e^{-u/2} cos(phi) + e_E Xi_1,   Xi_1 = cos(phi) e^{-u/2} [(1 + u)(1 - e cosh sqrt(yu)) + y e cosh sqrt(yu)].
       (multiplied by b k_E and summed over the harmonics with q_n this is M0 - b Psi_0 = k_E (1 - e_E)(b R_theta + t_rho) + k_E e_E b Xi.)
  (X3) |Xi_1| <= y M4 with M4 = 2.07 for y <= 1e-6 (grid in u, several y); sup_u u e^{-u/2} = 2/e, so c_2 = 2 Qb/e <= 0.184.
  (X4) Gaussian moments and tails: E s^^2 = 1, E s^^4 = 3, E s^^6 = 15; T_2(K) = E[s^^2 1{|s^| > K}] = 2 (K phi(K) + Q(K)); E[|s^| 1{|s^| > K}] = 2 phi(K);
       Q(K) <= phi(K)/K; T_2(K) <= 0.8 (K + 1) e^{-K^2/2}; 4 Q(K) + (y/2) T_2(K) + 4 sqrt(y) phi(K) <= (K + 5) phi(K) for y <= 1, K >= 20.
  (X5) the elementary inequalities on grids: 1 - e^{-u} <= 2u/(1 + u);  u^2/2 - u^4/24 <= 1 - cos u <= u^2/2;  0 <= u sin u <= u^2 (|u| <= 1);
       |cos a - chi sin a - cos(a + chi)| <= chi^2/2;  1 - cos a - d u sin a >= -d |u|.
-> results/cz_exact.json ; exit 1 if a check fails."""
import json, sys
from decimal import Decimal as D, getcontext
getcontext().prec = 70
PI = D('3.1415926535897932384626433832795028841971693993751058209749445923078164')
res = {}; ok_all = True


def rec(name, ok, **kw):
    global ok_all
    fmt = lambda v: ('%.6E' % v) if isinstance(v, D) else str(v)[:60]
    ok_all &= bool(ok); res[name] = {'ok': bool(ok), **{k: fmt(v) for k, v in kw.items()}}
    print('[%s] %s %s' % ('OK ' if ok else 'FAIL', name, {k: fmt(v) for k, v in kw.items()}), flush=True)


def dcos(x):
    x = D(x) % (2 * PI); s = D(0); t = D(1); k = 0
    while abs(t) > D('1e-80'):
        s += t; k += 2; t = -t * x * x / (k * (k - 1))
    return s


def dsin(x): return dcos(D(x) - PI / 2)


def dcosh(x): x = D(x); return (x.exp() + (-x).exp()) / 2


def gauss_avg(f, h=D('0.2'), R=45):
    """E[f(s^)] for s^ ~ N(0,1), trapezoid."""
    n = int(D(R) / h); s = D(0)
    for i in range(-n, n + 1):
        x = h * i; s += (-x * x / 2).exp() * f(x)
    return s * h / (2 * PI).sqrt()


def run():
    tol = D('1e-58')
    # ---- (X1)
    for L2, s2 in ((D('0.7'), D('0.1')), (D('3'), D('0.75')), (D('40'), D('2'))):
        L = L2.sqrt(); r = s2 / L2; kE = (r / (1 + r)).sqrt(); gs = (r / (2 + r)).sqrt(); seE = s2 / (1 + r); se2 = s2 / (2 + r)
        E = lambda om: (-(L * om) ** 2 / (2 * s2)).exp()
        c = lambda om: dcos(L * om / D(2).sqrt())
        hw = D('0.12') / (1 + 2 / r).sqrt()                                  # the integrands are as narrow as e^{-om^2 (1 + 2/r)/2}: step 0.12 widths
        v = [gauss_avg(lambda om: E(om), hw, 12), gauss_avg(lambda om: E(om) * c(om), hw, 12), gauss_avg(lambda om: E(om) ** 2, hw, 12),
             gauss_avg(lambda om: E(om) ** 2 * c(om), hw, 12), gauss_avg(lambda om: E(om) ** 2 * (L * om) ** 2, hw, 12)]
        w = [kE, kE * (-seE / 4).exp(), gs, gs * (-se2 / 4).exp(), gs * se2]
        err = max(abs(a - b) for a, b in zip(v, w))
        # |w|: not entire at 0 -> the half-line integral in closed form: int Gamma E^2 |w| = 2 int_0^inf ... = g_s sqrt(2 se2/pi) (elementary); check by a fine grid
        rec('(X1) w-averages (L^2=%s, s^2=%s)' % (L2, s2), err < tol, max_error=err)
        hh = D('0.002'); tot = D(0); a_ = 1 / L2 + 2 / s2
        for i in range(1, 6001):
            wv = hh * (D(i) - D('0.5')) * (1 / a_.sqrt()); tot += wv * (-a_ * wv * wv / 2).exp()
        tot = 2 * tot * hh / a_.sqrt() / (2 * PI * L2).sqrt()
        rec('(X1) int Gamma E^2 |w| = g_s sqrt(2 se2/pi) (midpoint rule, 1e-6)', abs(tot - gs * (2 * se2 / PI).sqrt()) < D('1e-6') * gs, lhs=tot, rhs=gs * (2 * se2 / PI).sqrt())
    # ---- (X2)
    worst = D(0)
    for y, tau, n, phi, eE in ((D('0.3'), D('0.7'), 1, D('0.4'), D('0.6')), (D('1e-3'), D('2.5'), 2, D('1.9'), D('0.999')), (D('0.05'), D('0.04'), 5, D('-2.2'), D('0.2')),
                               (D('1e-8'), D('6'), 1, D('3.0'), D('1')), (D('0.9'), D('1.3'), 3, D('0.0'), D('0'))):
        u = n * n * tau; st = tau.sqrt(); sy = y.sqrt(); e = (-y / 2).exp()
        lhs = gauss_avg(lambda s: (s * s * dcos(n * st * s - phi) + 2 * u.sqrt() * s * dsin(n * st * s - phi)) * (1 - eE * dcos(sy * s)))
        ch = dcosh((y * u).sqrt())
        Xi1 = dcos(phi) * (-u / 2).exp() * ((1 + u) * (1 - e * ch) + y * e * ch)
        rhs = (1 - eE) * (1 + u) * (-u / 2).exp() * dcos(phi) + eE * Xi1
        worst = max(worst, abs(lhs - rhs))
    rec('(X2) the identity of M0 for one harmonic (5 cases)', worst < tol, max_error=worst)
    # ---- (X3)
    mx = D(0)
    for y in (D('1e-6'), D('1e-9'), D('2e-11'), D('1e-20'), D('1e-40')):
        e = (-y / 2).exp()
        for i in range(0, 4001):
            u = D(i) / 10; ch = dcosh((y * u).sqrt())
            one_m = -((-y / 2 + ((y * u).sqrt())) .exp() + (-y / 2 - (y * u).sqrt()).exp()) / 2 + 1          # 1 - e cosh sqrt(yu)
            mx = max(mx, abs((-u / 2).exp() * ((1 + u) * one_m + y * e * ch)) / y)
    rec('(X3) |Xi_1| <= 2.07 y for y <= 1e-6 (u in [0, 400], 5 values of y)', mx <= D('2.07'), sup=mx)
    m1 = max(D(i) / 1000 * (-D(i) / 2000).exp() for i in range(0, 20001))
    rec('(X3) sup u e^{-u/2} = 2/e and c_2 = 2 Qb/e <= 0.184', abs(m1 - 2 / D(1).exp()) < D('1e-6') and D('0.5') / D(1).exp() <= D('0.184'), sup=m1, c2=D('0.5') / D(1).exp())
    # ---- (X4)
    mom = [gauss_avg(lambda s, k=k: s ** k) for k in (2, 4, 6)]
    rec('(X4) E s^2 = 1, E s^4 = 3, E s^6 = 15', max(abs(mom[0] - 1), abs(mom[1] - 3), abs(mom[2] - 15)) < tol, max_error=max(abs(mom[0] - 1), abs(mom[1] - 3), abs(mom[2] - 15)))
    okT = True; worstT = D(0)
    for K in (D(2), D(5), D('11.5'), D(20)):
        # tail integrals by the trapezoid rule on [K, K + 40] with the end correction h f(K)/2 (smooth one-sided: error ~ h^2; use Richardson)
        def tail(f, h):
            n = int(14 / h); s = f(K) / 2 * (-K * K / 2).exp()
            for i in range(1, n + 1):
                x = K + h * i; s += (-x * x / 2).exp() * f(x)
            return s * h / (2 * PI).sqrt()
        def rich(f):
            a, b, c = tail(f, D('0.08') / K), tail(f, D('0.04') / K), tail(f, D('0.02') / K)
            b1 = (4 * b - a) / 3; c1 = (4 * c - b) / 3; return (16 * c1 - b1) / 15
        Q = rich(lambda x: D(1)); T2h = rich(lambda x: x * x); A1 = rich(lambda x: x); ph = (-K * K / 2).exp() / (2 * PI).sqrt()
        e1 = abs(2 * T2h - 2 * (K * ph + Q)) / (2 * T2h); e2 = abs(2 * A1 - 2 * ph) / (2 * ph)
        okT &= e1 < D('1e-9') and e2 < D('1e-9') and Q <= ph / K and 2 * (K * ph + Q) <= D('0.8') * (K + 1) * (-K * K / 2).exp()
        worstT = max(worstT, e1, e2)
        if K >= 20:
            for y in (D(1), D('0.01'), D('1e-10')): okT &= 4 * Q + (y / 2) * 2 * (K * ph + Q) + 4 * y.sqrt() * ph <= (K + 5) * ph
    rec('(X4) T_2(K) = 2(K phi + Q), E|s|1{|s|>K} = 2 phi, Q <= phi/K, T_2 <= 0.8 (K+1) e^{-K^2/2}, tails <= (K+5) phi', okT, max_rel_error=worstT)
    # ---- (X5)
    ok5 = True
    for i in range(1, 4001):
        u = D(i) / 100
        ok5 &= 1 - (-u).exp() <= 2 * u / (1 + u)
    for i in range(-100, 101):
        u = D(i) / 100; c = dcos(u); s = dsin(u)
        ok5 &= u * u / 2 - u ** 4 / 24 <= 1 - c + D('1e-65') and 1 - c <= u * u / 2 + D('1e-65') and D('-1e-65') <= u * s <= u * u + D('1e-65')
    for i in range(-30, 31):
        for j in range(-30, 31):
            a = D(i) / 5; chi = D(j) / 7; dd = D(abs(j)) / 15
            ok5 &= abs(dcos(a) - chi * dsin(a) - dcos(a + chi)) <= chi * chi / 2 + D('1e-60')
            ok5 &= 1 - dcos(a) - dd * chi * dsin(a) >= -dd * abs(chi) - D('1e-60')
    rec('(X5) elementary inequalities on grids', ok5)
    res['all_ok'] = bool(ok_all)
    json.dump(res, open('results/cz_exact.json', 'w'), indent=1)
    print('all ok:', ok_all)
    return ok_all


if __name__ == '__main__':
    sys.exit(0 if run() else 1)
