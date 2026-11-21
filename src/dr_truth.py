"""Stage DR (DR_探索計画.md sections C and E, written before this ran): THE TRUE QUANTITIES OF ROOM 1b BY DIRECT QUADRATURE.  Python 3.11 grammar.  [numerical]
For a window state p = N_V(v) Gamma(w) h(k'v, w)/Z, h = 1 + e^{-w^2/2s^2} R(t), the true
        Z, sigma^2 J_vv = b + W, sigma^2 J_ww = J, 2 A_w, N_phi, (a) + (a') = (2 A_w + N_phi)/(sigma den), den = b + W + J
are computed by two-dimensional quadrature (the formulas of dp_truth.direct; the v-grid here follows the highest harmonic up to 200001 points).
Double precision reaches only sigma = e^{-ell}, ell = 6..10, so this is NOT the class of the theorems (ell >= 960.8, x >= 5e11 sigma^2); it tests the same
formulas at a smaller ell.  Three tests:
 P  Lemma DR-P (every state with Delta = 2 pi sigma/sqrt(x) <= 1; the states of the families with Delta > 1 are recorded apart):  N_phi >= c_P (b + W),  c_P = (sigma^2/(8x)) (theta/(1+theta)) ((1-b) - 2 a sqrt(x)/pi)_+^2,  theta = e^{-10 pi^2/tau}/5,
    a = sqrt(x) N_1/(1-Qb) + Qb e^{-1/2}/(1-Qb).  T_P := N_phi/(c_P (b+W)) >= 1.  Families: spikes at v = 0 (many aligned harmonics), shifted spikes, random, one
    harmonic; tau from 0.05 to 2000.  POWER: theta := 1/5 (the Gaussian weight dropped), r := Delta (c_P x 16), the factor 1/5 := 1.
 T  Theorem DR-1 (conclusion):  ((a) + (a')) sigma >= kappa(B) = min(0.055, 0.459/(4B+1))  for tau >= 40 and B >= 200/tau (the analogue of beta <= 1e-6 tau).
    T := ((a)+(a')) sigma/kappa(B) >= 1.  POWER: 0.459 -> 0.6, 0.055 -> 0.3, (4B+1) -> 1.  Also tau in [3, 40] (outside the theorem; material).
 A  the assembled inequality of the proof of DR-1 (Lemma BE with the window's own constants and the exact nu_k):
        2 N_phi >= (1-e) W (1 - sigma^2/((1-e)(1-nu0))) - (rho_W (1-e) + c_4) W_perUB/(1-z) + b Psi (1/(1+z) - 1/(2(1-z))) - J/(4(1-z)) - rem,
    with Psi = 1 - e C (1-y) from the period average C.  POWER: (1-e) := 1;  Psi := 1.
-> results/dr_truth_P.json, dr_truth_T.json, dr_truth_S.json (steps of DR-P), dr_truth_T2.json (planted tight states)"""
import json, math, os, sys, time
import numpy as np

QB = 0.25
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'results', 'dr_truth.json')


def ripple(q, ph, t):
    R = np.zeros_like(t); Rp = np.zeros_like(t)
    for n, (qq, pp) in enumerate(zip(q, ph), start=1):
        if qq == 0: continue
        R += qq * np.cos(n * t - pp); Rp += -n * qq * np.sin(n * t - pp)
    return R, Rp


def quad(sig, x, b, L2, s2, q, ph, nvmax=200001):
    V = sig ** 2 / b; kp = math.sqrt(x) / sig; L = math.sqrt(L2); s = math.sqrt(s2); tau = x / b
    nmax = max(i + 1 for i, v in enumerate(q) if v != 0)
    nv = int(min(nvmax, max(3001, 2 * 9 * math.sqrt(tau) * nmax / 0.08))) | 1
    v = np.linspace(-9 * math.sqrt(V), 9 * math.sqrt(V), nv); wv = np.full(nv, v[1] - v[0]); wv[[0, -1]] *= 0.5
    nw1 = int(min(4001, max(1201, 2 * 9 * L / 0.15))) | 1
    w = np.unique(np.concatenate([np.linspace(-9 * L, 9 * L, nw1), np.linspace(-min(9 * s, 9 * L), min(9 * s, 9 * L), 1001)]))
    ww = np.zeros(len(w)); d = np.diff(w); ww[:-1] += d / 2; ww[1:] += d / 2
    t = kp * v; R, Rp = ripple(q, ph, t)
    NV = np.exp(-v ** 2 / (2 * V)) / math.sqrt(2 * math.pi * V) * wv
    G = np.exp(-w ** 2 / (2 * L2)) / math.sqrt(2 * math.pi * L2) * ww
    acc = np.zeros(5); env = np.exp(-w ** 2 / (2 * s2)); ch = max(50, int(2.5e6 / len(w)))
    for i in range(0, nv, ch):
        sl = slice(i, i + ch); Rr = R[sl][:, None]; Rpp = Rp[sl][:, None]; vv = v[sl][:, None]
        h = 1 + env[None, :] * Rr; pw = NV[sl][:, None] * G[None, :] * h
        sv = -vv / V + kp * env[None, :] * Rpp / h; sw = -w[None, :] / L2 - (w[None, :] / s2) * env[None, :] * Rr / h
        mz = ((vv + sig ** 2 * sv) + (w[None, :] + sig ** 2 * sw)) / math.sqrt(2); phi = 2 * np.sin(mz / 2) ** 2
        acc += np.array([pw.sum(), (pw * sv * sv).sum(), (pw * sw * sw).sum(), (pw * sw * sw * phi).sum(), (pw * sv * sv * phi).sum()])
    Z = acc[0]; Jvv, Jww, Swp, Svp = acc[1] / Z, acc[2] / Z, acc[3] / Z, acc[4] / Z
    S = sig ** 2
    return {'Z': Z, 's2Jvv': S * Jvv, 'J': S * Jww, 'twoAw': 2 * S * (Jww - Swp / 4), 'Nphi': S / 2 * Svp, 'nv': nv, 'nw': len(w),
            'N1': float(sum((i + 1) * abs(qq) for i, qq in enumerate(q))), 'N2': float(sum((i + 1) ** 2 * abs(qq) for i, qq in enumerate(q)))}


def period_C(sig, x, L2, s2, q, ph, nt=2048):
    """C = int Gamma <h cos psi>, psi = (sigma^2 (s~ + s_w) + w)/sqrt2 (period average), and W_per = x int Gamma <h_t^2/h>."""
    L = math.sqrt(L2); s = math.sqrt(s2)
    nmax = max(i + 1 for i, v in enumerate(q) if v != 0); nt = max(nt, 64 * nmax)
    t = np.linspace(0, 2 * math.pi, nt, endpoint=False); R, Rp = ripple(q, ph, t)
    nw1 = int(min(4001, max(1201, 2 * 9 * L / 0.15))) | 1
    w = np.unique(np.concatenate([np.linspace(-9 * L, 9 * L, nw1), np.linspace(-min(9 * s, 9 * L), min(9 * s, 9 * L), 1001)]))
    ww = np.zeros(len(w)); d = np.diff(w); ww[:-1] += d / 2; ww[1:] += d / 2
    G = np.exp(-w ** 2 / (2 * L2)) / math.sqrt(2 * math.pi * L2) * ww; env = np.exp(-w ** 2 / (2 * s2))
    h = 1 + env[None, :] * R[:, None]
    st = sig * math.sqrt(x) * env[None, :] * Rp[:, None] / h                      # sigma^2 s~ = sigma sqrt(x) h_t/h
    sw = sig ** 2 * (-w[None, :] / L2 - (w[None, :] / s2) * env[None, :] * R[:, None] / h)
    psi = (st + sw + w[None, :]) / math.sqrt(2)
    C = float(((h * np.cos(psi)).mean(axis=0) * G).sum())
    Wper = float(x * (((env[None, :] * Rp[:, None]) ** 2 / h).mean(axis=0) * G).sum())
    return C, Wper


def nu(k, tau, beta):
    n = np.arange(1, 400); return float(2 * np.sum(n ** float(k) * np.exp(-n * n * tau / 2 + n * beta)))


# ------------------------------------------------------------------ Lemma DR-P
def cP(sig, x, b, N1, wrong=None):
    tau = x / b
    a = math.sqrt(x) * N1 / (1 - QB) + QB * math.exp(-0.5) / (1 - QB)
    th = math.exp(-10 * math.pi ** 2 / tau) / 5
    if wrong == 'theta': th = 0.2
    if wrong == 'fifth': th = math.exp(-10 * math.pi ** 2 / tau)
    brk = max(0.0, (1 - b) - 2 * a * math.sqrt(x) / math.pi)
    c = sig ** 2 / (8 * x) * th / (1 + th) * brk ** 2
    if wrong == 'r': c *= 16
    return c


# ------------------------------------------------------------------ Theorem DR-1
def kappa(B, wrong=None):
    c1, c2, den = 0.055, 0.459, 4 * B + 1
    if wrong == 'W': c2 = 0.6
    if wrong == 'b': c1 = 0.3
    if wrong == 'e': den = 1.0
    return min(c1, c2 / den)


def assembled(sig, x, b, L2, s2, Q, C, wrong=None):
    """the right side of the 2 N_phi inequality in the proof of DR-1, with the window's own N1, N2 and the exact nu_k(tau, beta)."""
    S = sig ** 2; tau = x / b; B = b / S; y = (1 - b) ** 2 / (2 * B); e = math.exp(-y / 2); beta = (1 - b) * math.sqrt(tau / (2 * B))
    n0, n1, n2, n3, n4 = (nu(k, tau, beta) for k in range(5)); z = QB * n0 / 2
    N1, N2 = Q['N1'], Q['N2']; U1 = math.sqrt(x) * N1; s = math.sqrt(s2)
    gP = (x * N2 * (1 + QB) + U1 ** 2 + U1 * (1 + 2 * QB) / math.sqrt(math.e)) / (1 - QB) ** 2
    cchi = (U1 / (1 - QB) + math.sqrt(2 / math.pi) + QB * math.exp(-0.5) / (1 - QB)) / math.sqrt(2)
    W = Q['s2Jvv'] - b; J = Q['J']
    K1s2 = 1e-3 / (1 - QB) + S * (U1 ** 2 + S / (2 * s2)) / (1 - QB) ** 3
    rhoW = 48 * (1 + QB) * K1s2 / (1 - b) ** 2
    xi = sig * U1 / (1 - QB); zeta = S * QB * math.exp(-0.5) / (s * (1 - QB)); se2 = 1 / (1 / L2 + 2 / s2)
    c4 = e * (1 + QB) / (1 - QB) * (beta ** 2 * n2 / 2 + beta * n1 * ((xi + zeta) / math.sqrt(2) + S * math.sqrt(se2 / math.pi) / L2))
    WperUB = ((1 + z) * W + 0.5 * b * tau * QB * n2) / (1 - n0)
    Psi = 1 - e * C * (1 - y); Phi = 1 - C
    ome = (1 - e)
    if wrong == 'e': ome = 1.0
    if wrong == 'Psi': Psi = 1.0
    rem = (3 / 8 * S * QB * n0 + b * (1 + QB) * sig * cchi * n0 * (1 + QB / 2) + b * QB * S * tau ** 2 * n2 / (8 * x) + S * n0 * (1 + QB) * gP
           + n1 * (x * N1 * sig * cchi + sig * math.sqrt(x) * (1 + QB) * gP / math.sqrt(2)) + 0.5 * x * QB * n2 * (1 + QB) * sig * cchi + QB * S * tau ** 2 * n4 / 8
           + S * x * QB * n2 / (2 * (1 - n0)) + sig * tau * math.sqrt(x) * QB * n3 / (2 * math.sqrt(2)) + b * QB * (n0 + tau * n2)) / (1 - z)
    rhs = (ome * W * (1 - S / ((1 - e) * (1 - n0))) - (rhoW * (1 - e) + c4) * WperUB / (1 - z) + b * Psi * (1 / (1 + z) - 1 / (2 * (1 - z))) - J / (4 * (1 - z)) - rem)
    return {'rhs': rhs, 'Psi': Psi, 'Phi': Phi, 'rem': rem, 'rhoW': rhoW, 'c4': c4, 'nu0': n0, 'e': e}


# ------------------------------------------------------------------ windows
def win(rng, kind, nh, qs):
    q = np.zeros(nh)
    if kind == 'one': q[0] = qs; ph = np.zeros(nh)
    elif kind in ('spike', 'spike_pi', 'spike_half'):
        q[:] = qs / nh; ph = np.zeros(nh)
        if kind == 'spike_pi': ph = np.array([math.pi * (n + 1) for n in range(nh)])          # the spike moved by half a period
        if kind == 'spike_half': ph = np.array([math.pi / 2 * (n + 1) for n in range(nh)])    # by a quarter
    elif kind == 'top':
        q[-1] = qs; ph = rng.uniform(0, 2 * math.pi, nh)
    else:
        q = rng.uniform(0, 1, nh); q *= qs / q.sum(); ph = rng.uniform(0, 2 * math.pi, nh)
    return list(map(float, q)), list(map(float, ph))


def geom(rng, sig, mode):
    lo, hi = math.log(4 * sig ** 2), math.log(1 / sig)
    if mode == 'Lmin': L2 = 4 * sig ** 2
    elif mode == 'Lmax': L2 = 1 / sig
    elif mode == 'L1': L2 = math.exp(rng.uniform(math.log(0.3), math.log(3.0)))
    else: L2 = math.exp(rng.uniform(lo, hi))
    m2 = rng.choice(['smin', 'smax', 'r'])
    s2 = sig ** 2 if m2 == 'smin' else (L2 / 4 if m2 == 'smax' else math.exp(rng.uniform(math.log(sig ** 2), math.log(L2 / 4))))
    return float(L2), float(s2)


def run_P(n=150, seed=20261117):
    rng = np.random.default_rng(seed); rows = []; t0 = time.time()
    kinds = ['spike', 'spike', 'spike_pi', 'spike_half', 'rand', 'one', 'top']
    for i in range(n):
        ell = float(rng.choice([6.0, 8.0])); sig = math.exp(-ell)
        kind = kinds[i % len(kinds)]; nh = 1 if kind == 'one' else int(rng.integers(2, 13))
        tau = float(10 ** rng.uniform(-1.3, 3.3))
        if math.sqrt(tau) * nh > 800: tau = (800 / nh) ** 2 * rng.uniform(0.2, 1)
        lB = min(4.5, math.log10(0.003 / (tau * sig ** 2))); B = float(10 ** rng.uniform(min(0.0, lB - 1), lB))
        b = B * sig ** 2; x = tau * b
        q, ph = win(rng, kind, nh, float(rng.choice([0.25, 0.25, 0.05])))
        L2, s2 = geom(rng, sig, str(rng.choice(['Lmin', 'Lmin', 'L1', 'Lmax', 'r', 'r'])))
        Q = quad(sig, x, b, L2, s2, q, ph)
        row = {'ell': ell, 'kind': kind, 'nh': nh, 'tau': tau, 'B': B, 'x': x, 'L2': L2, 's2': s2, 'qsum': float(sum(q)), 'Nphi': Q['Nphi'], 's2Jvv': Q['s2Jvv'], 'J': Q['J'],
               'Z': Q['Z'], 'nv': Q['nv']}
        for wv in (None, 'theta', 'r', 'fifth'):
            c = cP(sig, x, b, Q['N1'], wv); row['T_P' if wv is None else 'T_P_wrong_' + wv] = (Q['Nphi'] / (c * Q['s2Jvv'])) if c > 0 else float('inf')
        row['E_phi_eff'] = Q['Nphi'] / (0.5 * Q['s2Jvv'])        # the s_v^2-weighted mean of phi
        row['E_phi_eff_times_4B'] = row['E_phi_eff'] * 4 * B
        rows.append(row)
    # the adversary planted by hand: a steep slope of many aligned harmonics at v = 0, the narrowest envelope (L = 2 sigma, s = sigma), x at the top of the class
    for ell in (6.0, 8.0):
        sig = math.exp(-ell)
        for nh, tau in ((120, 0.5), (200, 0.3), (120, 1.5), (60, 3.0), (300, 0.15), (300, 0.06), (40, 12.0), (20, 60.0)):
            q = [0.25 / nh] * nh; ph = [math.pi / 2] * nh; x = 0.003; b = x / tau
            if b > 0.5: continue
            Q = quad(sig, x, b, 4 * sig ** 2, sig ** 2, q, ph)
            row = {'ell': ell, 'kind': 'planted_slope', 'nh': nh, 'tau': tau, 'B': b / sig ** 2, 'x': x, 'L2': 4 * sig ** 2, 's2': sig ** 2, 'qsum': 0.25, 'Nphi': Q['Nphi'],
                   's2Jvv': Q['s2Jvv'], 'J': Q['J'], 'Z': Q['Z'], 'nv': Q['nv']}
            for wv in (None, 'theta', 'r', 'fifth'):
                c = cP(sig, x, b, Q['N1'], wv); row['T_P' if wv is None else 'T_P_wrong_' + wv] = (Q['Nphi'] / (c * Q['s2Jvv'])) if c > 0 else float('inf')
            row['E_phi_eff'] = Q['Nphi'] / (0.5 * Q['s2Jvv']); row['E_phi_eff_times_4B'] = row['E_phi_eff'] * 4 * row['B']
            rows.append(row)
    for r in rows:                                               # the condition of the lemma: Delta = 2 pi sigma/sqrt(x) = 2 pi/sqrt(tau B) <= 1
        r['Delta'] = 2 * math.pi / math.sqrt(r['tau'] * r['B']); r['in_lemma'] = bool(r['Delta'] <= 1)
    inl = [r for r in rows if r['in_lemma']]; outl = [r for r in rows if not r['in_lemma']]
    fin = [r for r in inl if math.isfinite(r['T_P'])]
    out = {'n': len(rows), 'n_in_lemma': len(inl), 'n_Delta_above_1': len(outl), 'n_cP_positive': len(fin), 'min_T_P': min(r['T_P'] for r in fin), 'argmin': min(fin, key=lambda r: r['T_P']),
           'min_T_P_tau_ge_3': min(r['T_P'] for r in fin if r['tau'] >= 3), 'ok': bool(all(r['T_P'] >= 1 for r in fin)),
           'min_T_P_Delta_above_1 (outside the lemma; recorded)': min([r['T_P'] for r in outl] or [None]), 'max_Delta': max(r['Delta'] for r in rows),
           'power': {wv: {'n_broken': int(sum(r['T_P_wrong_' + wv] < 1 for r in inl)), 'min': min(r['T_P_wrong_' + wv] for r in inl)} for wv in ('theta', 'r', 'fifth')},
           'min_E_phi_eff_times_4B_by_tau': {lab: min([r['E_phi_eff_times_4B'] for r in rows if lo <= r['tau'] < hi] or [None]) for lab, lo, hi in
                                             (('tau<1', 0, 1), ('1-10', 1, 10), ('10-40', 10, 40), ('40-2000', 40, 1e9))},
           'seconds': time.time() - t0, 'rows': rows}
    return out


def run_T(n=260, seed=20261118):
    rng = np.random.default_rng(seed); rows = []; t0 = time.time()
    kinds = ['rand', 'one', 'spike', 'top', 'rand', 'spike_pi']
    Bfix = [0.2, 1.0, 1.84, 5.0, 50.0, 300.0]
    for i in range(n):
        ell = float(rng.choice([6.0, 8.0, 8.0, 10.0])); sig = math.exp(-ell)
        kind = kinds[i % len(kinds)]; nh = 1 if kind == 'one' else int(rng.integers(2, 6))
        low = (i % 5 == 4)                                           # tau in [3, 40]: outside the theorem
        tau = float(10 ** rng.uniform(math.log10(3), math.log10(40))) if low else float(10 ** rng.uniform(math.log10(40), math.log10(1500)))
        B = Bfix[(i // 2) % len(Bfix)] if i % 2 == 0 else float(10 ** rng.uniform(math.log10(0.2), math.log10(300)))
        if tau * B * sig ** 2 > 0.003: B = 0.003 / (tau * sig ** 2) * rng.uniform(0.3, 1)
        if math.sqrt(tau) * nh > 800: nh = max(1, int(800 / math.sqrt(tau)))
        wdom = (i % 4 == 3) and not low                              # planted: the ripple dominates den (W >> 4B b), wide envelope: the place where 0.459/(4B+1) is tight
        if wdom:
            ell = float(rng.choice([8.0, 10.0])); sig = math.exp(-ell); kind = 'top'; nh = int(rng.integers(3, 6)); tau = float(rng.uniform(500, 1500))
            B = float(10 ** rng.uniform(math.log10(1.5), math.log10(40)))
        b = B * sig ** 2; x = tau * b
        q, ph = win(rng, kind, nh, 0.25 if wdom else float(rng.choice([0.25, 0.25, 0.24, 0.05, 0.005])))
        L2, s2 = geom(rng, sig, str(rng.choice(['Lmin', 'L1', 'L1', 'Lmax', 'r', 'r'])))
        if wdom: L2 = float(rng.choice([1 / sig, 30.0, 300.0])); s2 = L2 / 4
        Q = quad(sig, x, b, L2, s2, q, ph); C, Wper = period_C(sig, x, L2, s2, q, ph)
        den = Q['s2Jvv'] + Q['J']; summ = (Q['twoAw'] + Q['Nphi']) / (sig * den)
        row = {'ell': ell, 'kind': kind, 'nh': nh, 'tau': tau, 'B': B, 'x': x, 'L2': L2, 's2': s2, 'qsum': float(sum(q)), 'sum_sigma': summ * sig,
               'W_over_b': (Q['s2Jvv'] - b) / b, 'J_over_b': Q['J'] / b, 'aprime_share': Q['Nphi'] / (Q['twoAw'] + Q['Nphi']), 'in_analogue': bool(B >= 200 / tau and not low),
               'planted_Wdom': bool(wdom), 'beta_over_tau': (1 - b) * math.sqrt(tau / (2 * B)) / tau, 'C': C, 'Wper_over_W': Wper / max(Q['s2Jvv'] - b, 1e-300), 'Z': Q['Z'], 'nv': Q['nv'],
               'sum_sigma_times_B': summ * sig * B}
        row['T'] = summ * sig / kappa(B)
        for wv in ('W', 'b', 'e'): row['T_wrong_' + wv] = summ * sig / kappa(B, wv)
        for wv in (None, 'e', 'Psi'):
            A = assembled(sig, x, b, L2, s2, Q, C, wv)
            row['A_margin' if wv is None else 'A_margin_wrong_' + wv] = (2 * Q['Nphi'] - A['rhs']) / (2 * Q['Nphi'])
            if wv is None: row.update({'Psi': A['Psi'], 'Phi': A['Phi'], 'rem_over_2Nphi': A['rem'] / (2 * Q['Nphi']), 'nu0': A['nu0'], 'rhs_over_2Nphi': A['rhs'] / (2 * Q['Nphi'])})
        rows.append(row)
    ana = [r for r in rows if r['in_analogue']]; lowr = [r for r in rows if r['tau'] < 40]; oth = [r for r in rows if not r['in_analogue'] and r['tau'] >= 40]
    def mn(rs, k): return min(r[k] for r in rs) if rs else None
    out = {'n': len(rows), 'n_in_analogue': len(ana), 'n_tau_below_40': len(lowr), 'n_beta_large': len(oth),
           'min_T_in_analogue': mn(ana, 'T'), 'argmin_T': min(ana, key=lambda r: r['T']), 'min_T_tau_below_40': mn(lowr, 'T'), 'min_T_beta_large': mn(oth, 'T'),
           'ok_T': bool(all(r['T'] >= 1 for r in ana)),
           'power_T': {wv: {'n_broken': int(sum(r['T_wrong_' + wv] < 1 for r in ana)), 'min': mn(ana, 'T_wrong_' + wv)} for wv in ('W', 'b', 'e')},
           'min_A_margin_in_analogue': mn(ana, 'A_margin'), 'ok_A': bool(all(r['A_margin'] >= 0 for r in ana)),
           'min_A_margin_tau_below_40': mn(lowr, 'A_margin'), 'min_A_margin_beta_large': mn(oth, 'A_margin'),
           'max_rhs_over_2Nphi_in_analogue': max(r['rhs_over_2Nphi'] for r in ana),
           'power_A': {wv: {'n_broken': int(sum(r['A_margin_wrong_' + wv] < 0 for r in ana)), 'min': mn(ana, 'A_margin_wrong_' + wv)} for wv in ('e', 'Psi')},
           'min_sum_sigma_times_B_W_dominant': mn([r for r in ana if r['W_over_b'] > 20 and r['J_over_b'] < 0.05 * r['W_over_b'] and r['B'] > 3], 'sum_sigma_times_B'),
           'min_T_planted_Wdom': mn([r for r in rows if r['planted_Wdom']], 'T'), 'n_planted_Wdom': int(sum(r['planted_Wdom'] for r in rows)),
           'seconds': time.time() - t0, 'rows': rows}
    return out


def run_T2(n=24, seed=20261120):
    """planted after the first run of T (which showed that the W-dominant family of T was not tight: with a wide envelope the term e W Phi, dropped by the
    proof, is large).  Here the envelope is narrow (L^2 = c/B, so Phi << 1) and the ripple is as strong as the grid allows (one high harmonic, W/b in the
    thousands): the states where kappa(B) = 0.459/(4B+1) should be nearly attained.  POWER: 0.459 -> 0.6, 0.75, 1.0."""
    rng = np.random.default_rng(seed); rows = []; t0 = time.time(); ell = 10.0; sig = math.exp(-ell)
    for i in range(n):
        nh = int(rng.integers(12, 21)); tau = min(1600.0, (800.0 / nh) ** 2) * float(rng.uniform(0.8, 1.0)); B = float(10 ** rng.uniform(math.log10(1.5), math.log10(8)))
        b = B * sig ** 2; x = tau * b; q = [0.0] * nh; q[-1] = 0.25; ph = [float(rng.uniform(0, 2 * math.pi))] * nh
        L2 = float(rng.choice([0.02, 0.05, 0.1, 0.2])) / B; s2 = L2 / 4
        Q = quad(sig, x, b, L2, s2, q, ph); den = Q['s2Jvv'] + Q['J']; summ = (Q['twoAw'] + Q['Nphi']) / (sig * den)
        rows.append({'ell': ell, 'nh': nh, 'tau': tau, 'B': B, 'x': x, 'L2': L2, 's2': s2, 'W_over_b': (Q['s2Jvv'] - b) / b, 'J_over_b': Q['J'] / b, 'sum_sigma': summ * sig,
                     'T': summ * sig / kappa(B), 'T_0.6': summ * sig / kappa(B) * 0.459 / 0.6, 'T_0.75': summ * sig / kappa(B) * 0.459 / 0.75, 'T_1.0': summ * sig / kappa(B) * 0.459,
                     'kappa_is_W_branch': bool(0.459 / (4 * B + 1) <= 0.055), 'nv': Q['nv'], 'Z': Q['Z']})
    out = {'n': len(rows), 'min_T': min(r['T'] for r in rows), 'argmin': min(rows, key=lambda r: r['T']), 'ok': bool(all(r['T'] >= 1 for r in rows)),
           'power': {k: {'n_broken': int(sum(r[k] < 1 for r in rows)), 'min': min(r[k] for r in rows)} for k in ('T_0.6', 'T_0.75', 'T_1.0')},
           'seconds': time.time() - t0, 'rows': rows}
    return out


def run_S(n=60, seed=20261119):
    """the two steps of the proof of Lemma DR-P at fixed w:  (i) phi >= phi_r := ((1-b) r - sigma a)^2/pi^2 off I = {|v - v_k| < r}, r = Delta/4;
    (ii) int_{I^c} q >= theta int_I q, q = N_V h s_v^2.  POWER: (i) with phi_r x 4; (ii) with theta := 1/5."""
    rng = np.random.default_rng(seed); rows = []; t0 = time.time()
    kinds = ['spike', 'slope', 'rand', 'one', 'spike_pi']
    for i in range(n):
        ell = float(rng.choice([6.0, 8.0])); sig = math.exp(-ell); S = sig ** 2
        kind = kinds[i % len(kinds)]; nh = 1 if kind == 'one' else int(rng.integers(2, 40))
        tau = float(10 ** rng.uniform(-0.7, 2.7))
        lB = min(4.5, math.log10(0.003 / (tau * S))); B = float(10 ** rng.uniform(min(0.0, lB - 1), lB)); b = B * S; x = tau * b
        if kind == 'slope': q = [0.25 / nh] * nh; ph = [math.pi / 2] * nh
        else: q, ph = win(rng, kind, nh, 0.25)
        L2, s2 = geom(rng, sig, str(rng.choice(['Lmin', 'L1', 'r'])))
        V = S / b; kp = math.sqrt(x) / sig; Delta = 2 * math.pi / kp; r = Delta / 4; P = 2 * math.sqrt(2) * math.pi / (1 - b)
        N1 = sum((k + 1) * qq for k, qq in enumerate(q)); a = math.sqrt(x) * N1 / (1 - QB) + QB * math.exp(-0.5) / (1 - QB)
        phir = max(0.0, (1 - b) * r - sig * a) ** 2 / math.pi ** 2; th = math.exp(-10 * math.pi ** 2 / tau) / 5
        nv = int(min(400001, max(20001, 2 * 9 * math.sqrt(tau) * nh / 0.02))) | 1
        v = np.linspace(-9 * math.sqrt(V), 9 * math.sqrt(V), nv); t = kp * v; R, Rp = ripple(q, ph, t)
        NV = np.exp(-v ** 2 / (2 * V)); s = math.sqrt(s2); L = math.sqrt(L2)
        m_phi = float('inf'); m_ratio = float('inf'); m_ratio_w = None
        for w in [0.0, 0.3 * s, -s, 2 * s, 0.5 * L, -2 * L, 1e-3 * math.sqrt(V), -0.37 * math.sqrt(V), 1.1 * math.sqrt(V), float(rng.normal() * L), float(rng.normal() * math.sqrt(V))]:
            env = math.exp(-w * w / (2 * s2)); h = 1 + env * R
            sv = -v / V + kp * env * Rp / h; sw = -w / L2 - (w / s2) * env * R / h
            mz = ((v + S * sv) + (w + S * sw)) / math.sqrt(2); phi = 2 * np.sin(mz / 2) ** 2
            c = w * (1 - S / L2); u = ((1 - b) * v + c) / (2 * math.sqrt(2) * math.pi); dist = np.abs(u - np.round(u)) * P     # distance to the nearest v_k
            inI = dist < r; qv = NV * h * sv * sv
            if phir > 0 and (~inI).any(): m_phi = min(m_phi, float(np.min(phi[~inI])) / phir)
            mI = float(qv[inI].sum()); mO = float(qv[~inI].sum())
            if mI > 0:
                rat = mO / mI
                if rat < m_ratio: m_ratio = rat; m_ratio_w = w
        rows.append({'ell': ell, 'kind': kind, 'nh': nh, 'tau': tau, 'B': B, 'x': x, 'L2': L2, 's2': s2, 'Delta': Delta, 'in_lemma': bool(Delta <= 1), 'min_phi_over_phi_r_off_I': m_phi, 'min_outside_over_inside': m_ratio,
                     'theta': th, 'step_ii_margin': m_ratio / th if th > 0 else float('inf'), 'step_ii_wrong_theta_fifth': m_ratio / 0.2, 'w_at_min': m_ratio_w, 'nv': nv})
    allrows = rows; rows = [r for r in allrows if r['in_lemma']]
    out = {'n': len(allrows), 'n_in_lemma': len(rows), 'max_Delta': max(r['Delta'] for r in allrows),
           'min_step_ii_margin_Delta_above_1 (outside the lemma; recorded)': min([r['step_ii_margin'] for r in allrows if not r['in_lemma']] or [None]),
           'min_phi_over_phi_r': min(r['min_phi_over_phi_r_off_I'] for r in rows), 'ok_i': bool(all(r['min_phi_over_phi_r_off_I'] >= 1 for r in rows)),
           'power_i_phi_r_times_4_broken': int(sum(r['min_phi_over_phi_r_off_I'] < 4 for r in rows)),
           'min_step_ii_margin': min(r['step_ii_margin'] for r in rows), 'ok_ii': bool(all(r['step_ii_margin'] >= 1 for r in rows)),
           'min_step_ii_margin_tau_ge_20': min(r['step_ii_margin'] for r in rows if r['tau'] >= 20),
           'power_ii_theta_fifth_broken': int(sum(r['step_ii_wrong_theta_fifth'] < 1 for r in rows)), 'min_outside_over_inside': min(r['min_outside_over_inside'] for r in rows),
           'seconds': time.time() - t0, 'rows': allrows}
    return out


if __name__ == '__main__':
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    for k in ('P', 'T', 'S', 'T2'):                                   # one file per test, so that the two can run side by side
        if which not in (k, 'all'): continue
        n = int(sys.argv[2]) if len(sys.argv) > 2 else {'P': 150, 'T': 320, 'S': 60, 'T2': 24}[k]
        res = {'P': run_P, 'T': run_T, 'S': run_S, 'T2': run_T2}[k](n); res['python'] = sys.version.split()[0]; res['numpy'] = np.__version__
        json.dump(res, open(OUT.replace('.json', '_%s.json' % k), 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
        print(k, json.dumps({a: b for a, b in res.items() if a != 'rows'}, indent=1, default=str)[:3500])
