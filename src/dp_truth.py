"""Stage DP, room 2 (DP_探索計画.md section B.3 (3), written before this ran): THE LINES OF OPTION Fz AGAINST THE TRUE QUANTITY for b in (1/2, 1].
Python 3.11 grammar.  [numerical]
For a periodic window state p = N_V(v) Gamma(w) h(k'v, w)/Z the true (a) + (a') = (2 A_w + N_phi)/(sigma den) is computed by direct two-dimensional quadrature
(the formulas of ca_reduction.direct; here with a w-grid refined around the envelope |w| <~ s and 1 - cos written as 2 sin^2).  At the same state the lines of
option Fz (dj_lines, with gamma as the unknown) give the lower bound
        gamma* := (positive lines - remainder lines)/(target lines/gamma)      at the state's own a = 4 sigma/L^2,
with (mu, P, kappa) the window's own local quantities at the focus (t0 = 0, tau = x/b).  If the lines are lower bounds, TRUE >= gamma*.
This can be done in double precision only for moderate sigma: here sigma = e^{-ell}, ell in {7, 8, 9}.  The lines are written for every ell (eta = 1/ell,
U1(ell), K^2 = 8 ell + 100); their lemma conditions are imposed on the window and the state directly:
        sup|R| <= 1/ell,  sum q_n <= 1/4,  sqrt(x) sup|R'| <= U1(ell),  B = b/sigma^2 >= 50 (8 ell + 100),  y = (1 - b)^2 sigma^2/(2b) <= 1e-6,  r in [sigma^3, 1/4],
        sigma^2 <= s^2, L^2 <= 1/sigma;   x <= 0.003 (family X also x up to 0.05, flagged).
(The class condition x >= 5e11 sigma^2 only serves to prove U <= U1; here U <= U1 is checked on the window.)  So this is not the class of the theorem (ell >= 55.26)
but the same formulas at a smaller ell: a line that failed for b > 1/2 as a formula in b would show here.
STATES: b in (1/2, 1] (the room) and b in [0.2, 1/2] (control: the range of Theorem DJ-T).  WINDOWS: 1-3 harmonics with n^2 tau ~ 2 (where the t_rho term is largest),
phases 0 (crest), pi (trough), pi/2 (node), random; packets; one harmonic n = 1.
POWER: the same comparison with a line of Fz changed (hneg1 dropped, N1 dropped, the target d1 times 0.8, P4z doubled) must give TRUE < gamma*_wrong at some states.
-> results/dp_truth.json"""
import json, math, sys, time
import numpy as np
import dj_lines as J

QB = 0.25


def window(q, ph, t):
    R = np.zeros_like(t); Rp = np.zeros_like(t)
    for n, (qq, pp) in enumerate(zip(q, ph), start=1):
        if qq == 0: continue
        R += qq * np.cos(n * t - pp); Rp += -n * qq * np.sin(n * t - pp)
    return R, Rp


def direct(sig, x, b, L2, s2, q, ph):
    """the true (a) + (a') and the local quantities E0, E1, kappa at the focus t0 = 0."""
    V = sig ** 2 / b; kp = math.sqrt(x) / sig; L = math.sqrt(L2); s = math.sqrt(s2); tau = x / b
    nmax = max(i + 1 for i, v in enumerate(q) if v != 0)
    nv = int(min(30001, max(3001, 2 * 9 * math.sqrt(tau) * nmax / 0.05))) | 1
    v = np.linspace(-9 * math.sqrt(V), 9 * math.sqrt(V), nv); wv = np.full(nv, v[1] - v[0]); wv[[0, -1]] *= 0.5
    nw1 = int(min(6001, max(1501, 2 * 9 * L / 0.12))) | 1
    w = np.unique(np.concatenate([np.linspace(-9 * L, 9 * L, nw1), np.linspace(-min(9 * s, 9 * L), min(9 * s, 9 * L), 1201)]))
    ww = np.zeros(len(w)); d = np.diff(w); ww[:-1] += d / 2; ww[1:] += d / 2
    t = kp * v; R, Rp = window(q, ph, t)
    NV = np.exp(-v ** 2 / (2 * V)) / math.sqrt(2 * math.pi * V) * wv                      # weights in v
    th = NV / NV.sum(); E0 = float((th * R * R).sum()); E1 = float((th * Rp * Rp).sum()); kap = float((th * (t * t / tau) * Rp * Rp).sum()) / E1 if E1 > 0 else 1.0
    G = np.exp(-w ** 2 / (2 * L2)) / math.sqrt(2 * math.pi * L2) * ww                     # weights in w
    acc = np.zeros(5)                                                                    # Z, Jvv, Jww, E[sw^2 phi], E[sv^2 phi]
    env = np.exp(-w ** 2 / (2 * s2)); ch = 400
    for i in range(0, nv, ch):
        sl = slice(i, i + ch); Rr = R[sl][:, None]; Rpp = Rp[sl][:, None]; vv = v[sl][:, None]
        h = 1 + env[None, :] * Rr; pw = NV[sl][:, None] * G[None, :] * h
        sv = -vv / V + kp * env[None, :] * Rpp / h; sw = -w[None, :] / L2 - (w[None, :] / s2) * env[None, :] * Rr / h
        mz = ((vv + sig ** 2 * sv) + (w[None, :] + sig ** 2 * sw)) / math.sqrt(2); phi = 2 * np.sin(mz / 2) ** 2
        acc += np.array([pw.sum(), (pw * sv * sv).sum(), (pw * sw * sw).sum(), (pw * sw * sw * phi).sum(), (pw * sv * sv * phi).sum()])
    Z, Jvv, Jww, Swp, Svp = acc[0], acc[1] / acc[0], acc[2] / acc[0], acc[3] / acc[0], acc[4] / acc[0]
    den = sig ** 2 * (Jvv + Jww); Aw = sig ** 2 * (Jww - Swp / 4); Nphi = sig ** 2 / 2 * Svp
    return {'sum': (2 * Aw + Nphi) / (sig * den), 'Z': Z, 'E0': E0, 'E1': E1, 'kappa': kap, 'sigma^2 Jvv': sig ** 2 * Jvv}


def gamma_star(ell, mu, r, B, kap, P, a, drop=(), scale=None):
    """gamma* of option Fz at the point a (the largest gamma with Lambda_Fz(a) >= 0); scale = {tag: factor} changes lines (wrong versions)."""
    Y = np.array([[math.log(mu), math.log(r), math.log(B), math.log(kap)]]); lP = np.array([math.log(P)])
    T, aux = J.coeffs(ell, Y[:, 0], Y[:, 1], Y[:, 2], Y[:, 3], lP, gam=1.0)
    if scale:
        for tag, f in scale.items():
            ty, sg, Lc = T[tag]; T[tag] = (ty, sg, Lc + math.log(f))
    agg = J.aggregate(T, aux, ('Fz',), drop); lg1 = -0.5 * math.log(ell) - aux['lg']
    lf = J.lf_on(agg, np.array([[math.log(a)]]), ell, lg1)['Fz'][0, 0]
    return float(math.exp(lf) / math.sqrt(ell)) if np.isfinite(lf) else 0.0


WRONG = {'hneg1 dropped': {'drop': ('hneg1',)}, 'N1 dropped': {'drop': ('N1',)}, 'target d1 times 0.8': {'scale': {'d1': 0.8}}, 'P4z doubled': {'scale': {'P4z': 2.0}},
         'P1 times 1.05': {'scale': {'P1': 1.05}}}


def make_window(rng, ell, tau, x, kind):
    eta = 1 / ell; n0 = max(1, int(round(math.sqrt(2 / tau))))
    if kind == 'n1': q = [0.9 * eta]; ph = [float(rng.choice([0.0, math.pi, math.pi / 2]))]
    else:
        m = int(rng.integers(1, 4)); ns = sorted(set(int(max(1, n0 + k)) for k in rng.integers(-2, 3, m))); nmx = max(ns)
        if nmx > 400: return None
        q = [0.0] * nmx; ph = [0.0] * nmx
        p0 = {'crest': 0.0, 'trough': math.pi, 'node': math.pi / 2}.get(kind)
        for n in ns: q[n - 1] = 0.95 * eta / len(ns); ph[n - 1] = p0 if p0 is not None else float(rng.uniform(0, 2 * math.pi))
    return q, ph


def run(nper=14, seed=20261116, save=True):
    rng = np.random.default_rng(seed); t0 = time.time(); rows = []; skipped = 0
    for ell in (7.0, 8.0, 9.0):
        sig = math.exp(-ell); U1 = 0.25 * math.sqrt(2 * ell + 3.1) + 1e-6
        for room, (blo, bhi) in (('room 2: b in (1/2, 1]', (0.5, 1.0)), ('control: b in [0.2, 1/2]', (0.2, 0.5))):
            for kind in ('crest', 'trough', 'node', 'random', 'n1', 'X'):
                for _ in range(nper):
                    u = rng.random(); b = bhi if u < 0.15 else (blo * (1 + 1e-9) if u < 0.25 else float(rng.uniform(blo, bhi)))
                    x = math.exp(rng.uniform(math.log(1e-4), math.log(0.003))) if kind != 'X' else math.exp(rng.uniform(math.log(0.003), math.log(0.05)))
                    tau = x / b; win = make_window(rng, ell, tau, x, 'random' if kind == 'X' else kind)
                    if win is None: skipped += 1; continue
                    q, ph = win
                    r = math.exp(rng.uniform(math.log(1e-4), math.log(0.25))) if rng.random() < 0.7 else 0.25
                    lL2 = rng.uniform(math.log(4 * sig ** 2 / r * 1.0001), math.log(1 / sig)) if rng.random() < 0.6 else math.log(4 * sig / math.sqrt(b)) + rng.uniform(-2.5, 2.5)
                    L2 = float(np.clip(math.exp(lL2), sig ** 2 / r, 1 / sig)); s2 = r * L2
                    B = b / sig ** 2; y = (1 - b) ** 2 * sig ** 2 / (2 * b)
                    tt = np.linspace(0, 2 * math.pi, 20001); R, Rp = window(q, ph, tt); supR = float(np.max(np.abs(R))); U = math.sqrt(x) * float(np.max(np.abs(Rp)))
                    if not (supR <= 1 / ell and sum(q) <= QB and U <= U1 and B >= 50 * (8 * ell + 100) and y <= 1e-6 and s2 >= sig ** 2): skipped += 1; continue
                    d = direct(sig, x, b, L2, s2, q, ph)
                    if d['E1'] <= 0 or d['E0'] <= 0: skipped += 1; continue
                    mu = x * d['E1'] / d['E0']; P = 2 * x * d['E1']; a = 4 * sig / L2
                    g = gamma_star(ell, mu, r, B, d['kappa'], P, a)
                    row = {'ell': ell, 'room': room, 'family': kind, 'b': b, 'x': x, 'tau': tau, 'r': r, 'L2': L2, 'a/sigma': a / sig, 'mu': mu, 'P': P, 'kappa': d['kappa'],
                           'true (a) + (a\')': d['sum'], 'gamma* (Fz lines)': g, 'true/gamma*': d['sum'] / g if g > 0 else float('inf'), 'sigma^2 Jvv - b': d['sigma^2 Jvv'] - b}
                    for nm, kw in WRONG.items(): row['wrong: ' + nm] = d['sum'] / max(gamma_star(ell, mu, r, B, d['kappa'], P, a, **kw), 1e-300)
                    rows.append(row)
        print(ell, len(rows), round(time.time() - t0), flush=True)
    out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)', 'states': len(rows), 'skipped (a condition of the lemmas not met)': skipped}
    for room in ('room 2: b in (1/2, 1]', 'control: b in [0.2, 1/2]'):
        rr = [x for x in rows if x['room'] == room]; w = min(rr, key=lambda x: x['true/gamma*'])
        out[room] = {'states': len(rr), 'smallest true/gamma* (must be >= 1)': w['true/gamma*'], 'at': {k: w[k] for k in ('ell', 'family', 'b', 'x', 'r', 'L2', 'a/sigma', 'mu', 'P', 'kappa')},
                     'median true/gamma*': float(np.median([x['true/gamma*'] for x in rr])), 'smallest true (a) + (a\')': min(x["true (a) + (a')"] for x in rr),
                     'states with true < gamma*': int(sum(x['true/gamma*'] < 1 - 1e-9 for x in rr)),
                     'per family: smallest true/gamma*': {f: min(x['true/gamma*'] for x in rr if x['family'] == f) for f in sorted(set(x['family'] for x in rr))},
                     'wrong versions: states with true < gamma*_wrong (each must be > 0 in at least one of the two rooms)': {nm: int(sum(x['wrong: ' + nm] < 1 - 1e-9 for x in rr)) for nm in WRONG}}
    out['largest sigma^2 Jvv - 1 over the states (paper F: b + W_p = sigma^2 Jvv <= 1 for windows; the claim DP-2 does not use it, and some states tried here have it > 1)'] = float(max(x['sigma^2 Jvv - b'] + x['b'] - 1 for x in rows))
    caught = {nm: sum(out[room]['wrong versions: states with true < gamma*_wrong (each must be > 0 in at least one of the two rooms)'][nm] for room in ('room 2: b in (1/2, 1]', 'control: b in [0.2, 1/2]')) for nm in WRONG}
    out['wrong versions caught'] = {k: bool(v > 0) for k, v in caught.items()}
    out['ok'] = bool(all(out[room]['states with true < gamma*'] == 0 for room in ('room 2: b in (1/2, 1]', 'control: b in [0.2, 1/2]')) and sum(out['wrong versions caught'].values()) >= 3)
    out['rows'] = rows; out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_truth.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(); print(json.dumps({k: v for k, v in r.items() if k != 'rows'}, indent=1)[:6000])
