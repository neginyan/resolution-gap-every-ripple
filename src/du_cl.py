"""Stage DU (addendum): the constant c_L of Lemma CZ-2 (line B1w1), closed.  Python 3.11 grammar.  Plan: DU_探索計画.md (written before computing).
Model: Claude Opus 5.5 (claude-opus-5-5).

CLAIMS (proofs in 本筋用要約_観測DU.md §c_L and in App. A of the paper I draft):
  (C1) E_rho[sh X1 cos(sqrt(y) sh)] = sqrt(b) sum_n q_n cos(phi_n) e^{-u_n/2} e^{-y/2} [c_n sinh c_n - u_n cosh c_n],   u_n = n^2 tau, c_n = sqrt(y u_n).
       For one harmonic (q = 1, X1 = -sqrt(b u) sin(sqrt(u) sh - phi)) the normalised identity is
       I(u, y, phi) := E[sh (-sqrt(u) sin(sqrt(u) sh - phi)) cos(sqrt(y) sh)] = cos(phi) e^{-(u+y)/2} [c sinh c - u cosh c].
  (C2) |E_rho[sh X1 cos u]| <= sqrt(b) c_L(y),  c_L(y) = c2 + y Qb (M2(y)/2 + M1(y)),  c2 = 2 Qb/e,
       M1(y) = sup_u u e^{-u/2} cosh sqrt(yu),  M2(y) = sup_u u e^{-u/2} (1 + u cosh sqrt(yu)).
  (C3) the 1/L^2 part of B1w is (sqrt2 sigma^2 sqrt(b)/L^2) int Gamma E w sin(w/sqrt2) dw . E_rho[sh X1 cos u], at most 2 sigma^2 b c_L k_E sqrt(se_E/pi)/L^2.
  (C4) M1, M2 are nondecreasing in y; M1(1e-4) <= 0.73584, M2(1e-4) <= 2.73800 (interval arithmetic with the DO watch), Qb (M2/2 + M1) <= 1,
       hence c_L <= c2 + y <= 0.184 + y for y <= 1e-4.
CHECKS: (B1) (C1) in 50-digit decimal; (B2) (C2) on random and planted windows; (B3) (C3) against the quadrature of cz_pieces; (B4) deliberately wrong
versions W1 (c2 with 1/e), W2 (M2 without (1 + u cosh)), W3 (M1 dropped), W4 (sign in (C1)); (C) the interval arithmetic and its power.
-> results/du_cl.json"""
import json, math, time, sys, os, functools, decimal
from decimal import Decimal as D, localcontext
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np

QB = 0.25


# ---------------------------------------------------------------- (B1) the identity in 50-digit decimal
def _dec_tools(prec=60):
    ctx = decimal.Context(prec=prec, Emax=10 ** 9, Emin=-10 ** 9)
    with localcontext(ctx):
        PI = D('3.14159265358979323846264338327950288419716939937510582097494459230781640628620899')
        def dcos(x):
            x = x % (2 * PI); s = D(0); t = D(1); k = 0
            while abs(t) > D('1e-75'):
                s += t; k += 2; t = -t * x * x / (k * (k - 1))
            return s
        def dsin(x): return dcos(x - PI / 2)
    return ctx, PI, dcos, dsin


def identity_case(u, y, phi, h=D('0.1'), span=40):
    ctx, PI, dcos, dsin = _dec_tools()
    with localcontext(ctx):
        u = D(u); y = D(y); phi = D(phi); su = u.sqrt(); sy = y.sqrt(); n = int(span / h)
        tot = D(0); wsum = D(0)
        for i in range(-n, n + 1):
            s = h * i; w = (-(s * s) / 2).exp()
            if i in (-n, n): w /= 2
            tot += w * s * (-su * dsin(su * s - phi)) * dcos(sy * s); wsum += w
        lhs = tot / wsum                                             # wsum -> sqrt(2 pi)/h (normalises the weight; the error is below e^{-2 pi^2/h^2})
        c = (y * u).sqrt(); ch = (c.exp() + (-c).exp()) / 2; shh = (c.exp() - (-c).exp()) / 2
        rhs = dcos(phi) * (-(u + y) / 2).exp() * (c * shh - u * ch)
        wrong = dcos(phi) * (-(u + y) / 2).exp() * (c * shh + u * ch)    # W4
        return lhs, rhs, wrong


# ---------------------------------------------------------------- (C2) on windows (float)
def M12_grid(y, umax=600.0, n=600001):
    uu = np.linspace(0, umax, n); c = np.cosh(np.sqrt(y * uu)); e = np.exp(-uu / 2)
    return float(np.max(uu * e * c)), float(np.max(uu * e * (1 + uu * c))), float(np.max(uu * e))


def closed_form(q, ph, tau, y):
    """E_rho[sh X1 cos u]/sqrt(b) by (C1)."""
    q = np.asarray(q, float); n = np.arange(1, len(q) + 1); u = n * n * tau; c = np.sqrt(y * u)
    return float(np.sum(q * np.cos(ph) * np.exp(-u / 2 - y / 2) * (c * np.sinh(c) - u * np.cosh(c))))


def quad_value(q, ph, tau, y, ns=200001, span=12.0):
    """E_rho[sh X1 cos u]/sqrt(b) by the trapezoid rule on the line (independent of (C1))."""
    sh = np.linspace(-span, span, ns); wt = np.exp(-sh ** 2 / 2); wt[[0, -1]] *= 0.5; wt /= wt.sum()
    t = math.sqrt(tau) * sh; X1 = np.zeros(ns)
    for k, (qq, pp) in enumerate(zip(q, ph), start=1):
        X1 += -math.sqrt(tau) * k * qq * np.sin(k * t - pp)                # X1/sqrt(b) = sqrt(tau) R'(t)
    return float(np.sum(wt * sh * X1 * np.cos(math.sqrt(y) * sh)))


def cL(y, M, version=None):
    M1, M2, M2w = M
    c2 = (QB / math.e) if version == 'W1' else 2 * QB / math.e
    if version == 'W2': return c2 + y * QB * (M2w / 2 + M1)
    if version == 'W3': return c2 + y * QB * (M2 / 2)
    if version == 'W6': return c2
    return c2 + y * QB * (M2 / 2 + M1)


def window_states(rng):
    S = []
    for y in (0.0, 1e-6, 1e-4, 0.01, 0.1, 1.0, 4.0, 10.0, 30.0):
        for _ in range(40):                                                    # random windows
            N = int(rng.integers(1, 9)); q = rng.random(N); q *= QB / q.sum(); ph = rng.uniform(0, 2 * math.pi, N)
            S.append(('random', q, ph, float(10 ** rng.uniform(-3, math.log10(50))), y))
        for tau in (2.0, 3.5616, 6.0, 0.5, 10.0, 0.1, 0.02):                              # planted: one harmonic at the maximum of u e^{-u/2} and nearby
            S.append(('planted', np.array([QB]), np.array([0.0]), tau, y))
            S.append(('planted pi', np.array([QB]), np.array([math.pi]), tau, y))
    return S


# ---------------------------------------------------------------- (C3) against the quadrature of cz_pieces
def b1w_L2_part(q, ph, tau, x, sig, b, L2, s2, nw=700):
    import cz_pieces as CP
    S = CP.window_samples(q, ph, tau, x); sh, wt, X1 = S['sh'], S['wt'], S['X1']
    L = math.sqrt(L2); r = s2 / L2; y = (1 - b) ** 2 * sig ** 2 / (2 * b)
    w, g, E = CP.w_grid(L, r, nw)
    # B1w (1/L^2 part) = -2 sqrt(b) < sh E X1 chi_w^{(L)} sin a >,  chi_w^{(L)} = -(sigma^2 w/sqrt2)/L^2,  a = sqrt(y) sh + w/sqrt2
    a = math.sqrt(y) * sh[None, :] + w[:, None] / math.sqrt(2)
    integrand = -2 * math.sqrt(b) * sh[None, :] * E[:, None] * X1[None, :] * (-(sig ** 2 * w[:, None] / math.sqrt(2)) / L2) * np.sin(a)
    val = float(np.sum(g[:, None] * wt[None, :] * integrand))
    kE = math.sqrt(r / (1 + r)); seE = s2 / (1 + r)
    return val, y, kE, seE


def run_states():
    rng = np.random.default_rng(20261117)
    Mc = {}; out = {}
    for y in (0.0, 1e-6, 1e-4, 0.01, 0.1, 1.0, 4.0, 10.0, 30.0): Mc[y] = M12_grid(y)
    worst = {k: 0.0 for k in ('lemma', 'W1', 'W2', 'W3', 'W6')}; broken = {k: 0 for k in worst}; err_cf = 0.0; n = 0; argw = None
    for kind, q, ph, tau, y in window_states(rng):
        cf = closed_form(q, ph, tau, y); qv = quad_value(q, ph, tau, y); err_cf = max(err_cf, abs(cf - qv) / max(1e-300, abs(qv) + 1e-12))
        for v in worst:
            ratio = abs(qv) / cL(y, Mc[y], None if v == 'lemma' else v)
            if ratio > worst[v]:
                worst[v] = ratio
                if v == 'lemma': argw = (kind, float(tau), y)
            if ratio > 1: broken[v] += 1
        n += 1
    out['(B2) states'] = n
    out['(B2) closed form (C1) against the trapezoid rule on the line: largest relative difference'] = err_cf
    out['(B2) largest |E[sh X1 cos u]|/(sqrt(b) c_L) (claim <= 1), and where'] = [worst['lemma'], argw]
    out['(B4) power: largest ratio and number of states broken'] = {
        'W1 c2 = Qb/e': [worst['W1'], broken['W1']], 'W2 M2 -> sup u e^{-u/2}': [worst['W2'], broken['W2']], 'W3 M1 dropped': [worst['W3'], broken['W3']],
        'W6 c_L = c2 (the y-term dropped)': [worst['W6'], broken['W6']]}
    out['(B2) M1, M2 on the grid (information)'] = {str(y): {'M1': Mc[y][0], 'M2': Mc[y][1], 'Qb(M2/2+M1)': QB * (Mc[y][1] / 2 + Mc[y][0])} for y in Mc}
    ok = worst['lemma'] <= 1 and broken['W1'] > 0 and broken['W6'] > 0 and err_cf < 1e-6
    # (B4') the pointwise step of the proof: e^{-u/2}(u cosh c + c sinh c) <= 2/e + y (M2/2 + M1) for every u >= 0 (grid), and its wrong versions
    uu = np.linspace(0, 200, 400001); pw = {}
    for y in (1e-4, 0.01, 0.1, 0.3, 1.0, 4.0, 30.0):
        c = np.sqrt(y * uu); e = np.exp(-uu / 2); g = float(np.max(e * (uu * np.cosh(c) + c * np.sinh(c))))
        M1, M2, m = Mc.get(y) or M12_grid(y)
        pw[str(y)] = {'lemma': g / (2 / math.e + y * (M2 / 2 + M1)), 'W2': g / (2 / math.e + y * (m / 2 + M1)), 'W3': g / (2 / math.e + y * M2 / 2)}
    out["(B4') the pointwise step g(u, y) = e^{-u/2}(u cosh c + c sinh c) <= 2/e + y(M2/2 + M1): largest ratio per y (lemma <= 1; W2, W3 must exceed 1 somewhere)"] = pw
    ok = ok and max(v['lemma'] for v in pw.values()) <= 1 + 1e-9 and max(v['W2'] for v in pw.values()) > 1 and max(v['W3'] for v in pw.values()) > 1
    # (B3) the 1/L^2 part of B1w by the 2D quadrature of cz_pieces; moderate sigma so that the part is visible
    rows = []; worst3 = 0.0; brk3 = 0
    cases = [(2.0, 0.3, 1.0, 0.25), (2.0, 0.3, 4.0, 1.0), (2.0, 0.1, 0.5, 0.1), (3.56, 0.3, 9.0, 2.25), (0.5, 0.3, 1.0, 0.25), (2.0, 0.45, 20.0, 5.0)]
    for tau, sig, L2, s2 in cases:
        for b in (0.05, 0.2, 0.5):
            x = b * tau; q = np.array([QB]); ph = np.array([0.0])
            val, y, kE, seE = b1w_L2_part(q, ph, tau, x, sig, b, L2, s2)
            My = M12_grid(y, n=60001)
            bound = 2 * sig ** 2 * b * cL(y, My) * kE * math.sqrt(seE / math.pi) / L2
            bW1 = 2 * sig ** 2 * b * cL(y, My, 'W1') * kE * math.sqrt(seE / math.pi) / L2
            rows.append([tau, sig, L2, s2, b, y, val, bound, abs(val) / bound]); worst3 = max(worst3, abs(val) / bound)
            if abs(val) > bW1: brk3 += 1
    out['(B3) the 1/L^2 part of B1w by 2D quadrature (cz_pieces) against 2 sigma^2 b c_L k_E sqrt(se_E/pi)/L^2: [tau, sigma, L2, s2, b, y, value, bound, ratio]'] = rows
    out['(B3) largest ratio (claim <= 1)'] = worst3
    out['(B3) W1 broken in (states)'] = brk3
    ok = ok and worst3 <= 1
    return out, ok


# ---------------------------------------------------------------- (C) interval arithmetic with the DO watch
def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


@trapped
def interval_part():
    import dl_interval as V
    from dl_interval import Iv, exp, sqrt
    def cosh(x): return (exp(x) + exp(-x)) / 2
    y = Iv(D('1e-4')); best1 = D(0); best2 = D(0); a1 = a2 = None; u0 = D(0)
    while u0 < D(60):
        h = D('0.005') if u0 < D(20) else D('0.05'); u1 = u0 + h
        U1 = Iv(u1); ch = cosh(sqrt(U1 * y)); e0 = exp(-Iv(u0) / 2)
        v1 = (U1 * e0 * ch).hi; v2 = (U1 * e0 * (1 + U1 * ch)).hi
        if v1 > best1: best1, a1 = v1, u0
        if v2 > best2: best2, a2 = v2, u0
        u0 = u1
    U = Iv(D(60)); k = Iv(D('0.4987'))
    t1 = (U * exp(-k * U)).hi; t2 = (U * (1 + U) * exp(-k * U)).hi
    c_ok = (D('0.01') / sqrt(U)).hi <= D('0.0013')
    d1 = (1 / U - k).hi < 0; d2 = (1 / U + 1 / (1 + U) - k).hi < 0
    M1 = max(best1, t1); M2 = max(best2, t2)
    s = Iv(D('0.25')) * (Iv(M2) / 2 + Iv(M1))
    c2 = (Iv(D('0.5')) / exp(Iv(1))).hi
    # power: lower bounds at grid points
    lo1 = D(0); lo2 = D(0)
    for kk in range(150, 450):
        uu = Iv(D(kk) / 100); chh = cosh(sqrt(uu * y)); ee = exp(-uu / 2)
        lo1 = max(lo1, (uu * ee * chh).lo); lo2 = max(lo2, (uu * ee * (1 + uu * chh)).lo)
    slo = (Iv(D('0.25')) * (Iv(lo2) / 2 + Iv(lo1))).lo
    return {'M1(1e-4) <= (pieces on [0, 60]; at the piece starting at u =)': [float(best1), float(a1)],
            'M2(1e-4) <= (pieces on [0, 60]; at the piece starting at u =)': [float(best2), float(a2)],
            'tail u >= 60: u e^{-0.4987 u} <= ; u(1+u) e^{-0.4987 u} <= ': [float(t1), float(t2)],
            'tail facts: sqrt(y u) <= 0.0013 u at u >= 60; d/du ln of the two tail bounds < 0 at u >= 60': [c_ok, d1, d2],
            'M1(1e-4) <=': float(M1), 'M2(1e-4) <=': float(M2), 'Qb (M2/2 + M1) <= (claim <= 1)': float(s.hi),
            'c2 = 2 Qb/e <= (claim <= 0.184)': float(c2),
            'POWER: lower bounds on a grid M1 >=, M2 >=, Qb(M2/2+M1) >= (the claims "<= 0.5" and "M2 <= 2.7" must fail)': [float(lo1), float(lo2), float(slo)],
            'ok': bool(s.hi <= 1 and c2 <= D('0.184') and c_ok and d1 and d2 and slo > D('0.5') and lo2 > D('2.7'))}


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    # (B1)
    worst = D(0); worst_w = None; nb = 0
    for u in ('0.01', '0.5', '2', '3.56', '10', '40'):
        for y in ('1e-8', '1e-4', '0.1', '1', '4'):
            for phi in ('0', '0.7', '2.5'):
                l, r, w = identity_case(u, y, phi)
                worst = max(worst, abs(l - r)); dw = abs(l - w)
                worst_w = dw if worst_w is None else min(worst_w, dw); nb += 1
    out['(B1) identity (C1), one harmonic, %d cases, 60-digit decimal: largest |lhs - rhs|' % nb] = float(worst)
    out['(B4) W4 (sign c sinh c + u cosh c): smallest |lhs - wrong| over the cases (must be large somewhere: the largest is reported below)'] = float(worst_w)
    ok1 = worst < D('1e-40')
    print(json.dumps(out, indent=1), flush=True)
    st, ok2 = run_states(); out.update(st); print(json.dumps(st, indent=1)[:3000], flush=True)
    iv = interval_part(); out['(C) interval arithmetic (DO watch: decimal.Inexact trapped)'] = iv; print(json.dumps(iv, indent=1), flush=True)
    # W4 must fail in the cases with phi = 0 and u > 0: |lhs - wrong| = 2 u cosh(c) e^{-(u+y)/2} cos(phi) > 0
    l, r, w = identity_case('2', '1e-4', '0'); out['(B4) W4 at u = 2, y = 1e-4, phi = 0: |lhs - wrong|'] = float(abs(l - w))
    ok4 = abs(l - w) > D('0.1')
    out['ok'] = bool(ok1 and ok2 and iv['ok'] and ok4); out['seconds'] = time.time() - t0
    print('ok', out['ok'], 'seconds %.0f' % out['seconds'])
    if save: json.dump(out, open(os.path.join(HERE, 'results', 'du_cl.json'), 'w'), indent=1)
    return out


if __name__ == '__main__':
    sys.exit(0 if run()['ok'] else 1)
