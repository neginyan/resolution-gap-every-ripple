"""Stage DS: two checks that go with the corrections of DS_証明まとめ.md section 13.  Python 3.11 grammar.
 (1) [numbers of a proof; interval arithmetic, Inexact trapped]  Lemma DR-R (R-1) assembled in the order of the rewritten proof:
        first the coefficients Kbar_i (rho_W and delta_4 at B = Bbar = 8 ell + 100, no other B), then  M sum_{a=0} Kbar_i + sqrt(M) sum_{a=1/2} Kbar_i + sum_{a=1} Kbar_i,
        M = 1 + tau/5e11, divided by (1 - z).  The Kbar_i are written here from the table (5) of the document, not taken from dr_be.remainders.
     It must equal dr_be.rho1 (which evaluates every term at Bbar and divides by Bbar, sqrt(Bbar), 1).  (R-2) is assembled the same way and must equal dr_be.rho2.
 (2) [numerical]  Lemma DR-P with a density Gamma that is not Gaussian (the lemma allows any positive differentiable density of w):
        a mixture of two Gaussians (not symmetric) and a logistic density.  The true N_phi and sigma^2 J_vv by direct quadrature, s_w = (ln Gamma)'(w) + h_w/h.
        T_P = N_phi/(c_P (b + W)) >= 1 for the states with Delta <= 1.  POWER: theta := 1/5 on the planted narrow-focus states.
-> results/ds_check.json"""
import decimal, functools, json, math, os, sys
from decimal import Decimal as Dc
import numpy as np
import dl_interval as I
from dl_interval import Iv
import dr_be as BE
import dr_truth as TR

HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, 'results', 'ds_check.json')


@BE.trapped
def r1_in_order():
    o = BE.V; ell = Iv(BE.ELL0); tau = 4 * I.log(ell) + 40; Bb = 8 * ell + 100; QB = Iv('0.25'); sig = I.exp(-1 * ell)
    U1, U2, gP, cchi = BE.window_consts(o, ell); n = 2.0000001 * I.exp(tau * -0.499999); z = QB * n / 2; r2 = I.sqrt(Iv(2))
    b = Bb * sig * sig
    Xi = (U1 / (1 - QB) + QB * I.exp(Iv('-0.5')) / (1 - QB)) / r2 + 1 / (2 * I.sqrt(BE.PI))
    d4 = Iv(5) / 3 * (tau * n + 2 * I.sqrt(2 * tau * Bb) * n * sig * Xi / (1 - b))                 # delta_4 at Bbar
    rhoW = 48 * (1 + QB) * (Iv('1e-3') / (1 - QB) + sig * sig * (U1 * U1 + 0.5) / ((1 - QB) * (1 - QB) * (1 - QB))) / ((1 - b) * (1 - b))   # rho_W at Bbar
    K0 = [Iv(3) / 8 * QB * n, QB * tau * n / 8, (1 + QB) * gP * n, QB * tau * tau * n / 8]                                  # a1, a3, a5, a8          (B^0)
    Kh = [I.sqrt(tau) * (U1 * cchi + (1 + QB) * gP / r2) * n, tau * I.sqrt(tau) * QB * n / (2 * r2)]                         # a6, a10                 (B^(1/2))
    K1 = [(1 + QB) * (1 + QB / 2) * sig * cchi * n, tau * QB * (1 + QB) * sig * cchi * n / 2, tau * sig * sig * QB * n / (2 * (1 - n)),   # a2, a7, a9      (B^1)
          QB * (1 + tau) * n, (rhoW + d4) * tau * QB * n / (2 * (1 - n))]                                                    # Phi-proportional, sandwich nu
    def S(lst):
        t = Iv(0)
        for v in lst: t = t + v
        return t
    M = 1 + tau / 5e11
    R1 = (M * S(K0) + I.sqrt(M) * S(Kh) + S(K1)) / (1 - z)
    R2 = (S(K0) + I.sqrt(Bb) * S(Kh) + Bb * S(K1)) / (1 - z)
    r1, _ = BE.rho1(o, ell, tau); r2_, _, _ = BE.rho2(o, ell, tau)
    return R1, r1, R2, r2_, M, tau, Bb


def r1_report():
    R1, r1, R2, r2_, M, tau, Bb = r1_in_order()
    with decimal.localcontext() as c:                    # the comparison of the two upper ends is not interval arithmetic: done outside the trap, at 80 digits
        c.prec = 80; rel = lambda a, d: float(abs(a.hi - d.hi) / d.hi); d1, d2 = rel(R1, r1), rel(R2, r2_)
    return {'R1_in_order_upper': float(R1.hi), 'dr_be_rho1_upper': float(r1.hi), 'rel_diff_R1': d1, 'R2_in_order_upper': float(R2.hi), 'dr_be_rho2_upper': float(r2_.hi),
            'rel_diff_R2': d2, 'M_minus_1': float((M - 1).hi), 'tau0': tau.f(), 'B_bar': Bb.f(),
            'ok': bool(d1 < 1e-25 and d2 < 1e-25 and R1.hi <= Dc('5.49e-11') and R2.hi <= Dc('4.76e-9'))}


def quad_gen(sig, x, b, s2, q, ph, w, G, dlnG, nvmax=200001):
    """as dr_truth.quad, for a density Gamma given on the grid w (values G, already multiplied by the quadrature weights) with (ln Gamma)' = dlnG."""
    V = sig ** 2 / b; kp = math.sqrt(x) / sig; tau = x / b
    nmax = max(i + 1 for i, v in enumerate(q) if v != 0)
    nv = int(min(nvmax, max(3001, 2 * 9 * math.sqrt(tau) * nmax / 0.08))) | 1
    v = np.linspace(-9 * math.sqrt(V), 9 * math.sqrt(V), nv); wv = np.full(nv, v[1] - v[0]); wv[[0, -1]] *= 0.5
    R, Rp = TR.ripple(q, ph, kp * v); NV = np.exp(-v ** 2 / (2 * V)) / math.sqrt(2 * math.pi * V) * wv
    acc = np.zeros(3); env = np.exp(-w ** 2 / (2 * s2)); ch = max(50, int(2.5e6 / len(w)))
    for i in range(0, nv, ch):
        sl = slice(i, i + ch); Rr = R[sl][:, None]; Rpp = Rp[sl][:, None]; vv = v[sl][:, None]
        h = 1 + env[None, :] * Rr; pw = NV[sl][:, None] * G[None, :] * h
        sv = -vv / V + kp * env[None, :] * Rpp / h; sw = dlnG[None, :] - (w[None, :] / s2) * env[None, :] * Rr / h
        mz = ((vv + sig ** 2 * sv) + (w[None, :] + sig ** 2 * sw)) / math.sqrt(2); phi = 2 * np.sin(mz / 2) ** 2
        acc += np.array([pw.sum(), (pw * sv * sv).sum(), (pw * sv * sv * phi).sum()])
    return {'Z': acc[0], 's2Jvv': sig ** 2 * acc[1] / acc[0], 'Nphi': sig ** 2 / 2 * acc[2] / acc[0], 'N1': float(sum((i + 1) * abs(v) for i, v in enumerate(q)))}


def gammas(sig, scale, s2):
    """two densities that are not Gaussian, on a grid that also resolves the envelope of width s."""
    s = math.sqrt(s2)
    def grid(lo, hi):
        w = np.unique(np.concatenate([np.linspace(lo, hi, 3001), np.linspace(-min(9 * s, hi), min(9 * s, hi), 1001)])); ww = np.zeros(len(w)); d = np.diff(w); ww[:-1] += d / 2; ww[1:] += d / 2
        return w, ww
    out = {}
    L1, L2, m1, m2 = scale, 0.35 * scale, 0.8 * scale, -1.7 * scale                       # mixture 0.6 N(m1, L1^2) + 0.4 N(m2, L2^2)
    w, ww = grid(m2 - 9 * L1, m1 + 9 * L1)
    g1 = 0.6 * np.exp(-(w - m1) ** 2 / (2 * L1 ** 2)) / (math.sqrt(2 * math.pi) * L1); g2 = 0.4 * np.exp(-(w - m2) ** 2 / (2 * L2 ** 2)) / (math.sqrt(2 * math.pi) * L2)
    G = g1 + g2; out['mixture'] = (w, G * ww, (-(w - m1) / L1 ** 2 * g1 - (w - m2) / L2 ** 2 * g2) / np.maximum(G, 1e-300))
    w, ww = grid(-45 * scale, 45 * scale); u = w / scale                                    # logistic: Gamma = e^{-u}/(scale (1+e^{-u})^2), (ln Gamma)' = -tanh(u/2)/scale
    out['logistic'] = (w, 0.25 / np.cosh(u / 2) ** 2 / scale * ww, -np.tanh(u / 2) / scale)
    return out


def dr_p_general(seed=20261121):
    rng = np.random.default_rng(seed); rows = []
    for i in range(14):
        ell = 8.0; sig = math.exp(-ell); planted = i >= 10
        if planted: nh = 200; tau = 0.02; x = 0.003; b = x / tau; q = [0.25 / nh] * nh; ph = [math.pi / 2] * nh; scale = 2 * sig; s2 = sig ** 2
        else:
            nh = int(rng.integers(1, 9)); tau = float(10 ** rng.uniform(0.5, 2.8)); B = float(10 ** rng.uniform(1.7, 3.5)); b = B * sig ** 2; x = tau * b
            q, ph = TR.win(rng, str(rng.choice(['spike', 'rand', 'top'])), nh, 0.25); scale = float(rng.choice([2 * sig, 30 * sig, 0.05, 1.0, 20.0])); s2 = float(rng.choice([sig ** 2, (scale / 2.5) ** 2]))
            s2 = max(s2, sig ** 2)
        for name, (w, G, dl) in gammas(sig, scale, s2).items():
            Q = quad_gen(sig, x, b, s2, q, ph, w, G, dl); c = TR.cP(sig, x, b, Q['N1']); cw = TR.cP(sig, x, b, Q['N1'], 'theta')
            rows.append({'Gamma': name, 'planted': planted, 'nh': nh, 'tau': tau, 'B': b / sig ** 2, 'x': x, 'scale': scale, 's2': s2, 'Z': Q['Z'], 'Delta': 2 * math.pi * sig / math.sqrt(x),
                         'T_P': Q['Nphi'] / (c * Q['s2Jvv']) if c > 0 else float('inf'), 'T_P_wrong_theta': Q['Nphi'] / (cw * Q['s2Jvv'])})
    fin = [r for r in rows if r['Delta'] <= 1 and math.isfinite(r['T_P'])]
    return {'n': len(rows), 'n_in_lemma_cP_positive': len(fin), 'max_Delta': max(r['Delta'] for r in rows), 'min_T_P': min(r['T_P'] for r in fin), 'ok': bool(all(r['T_P'] >= 1 for r in fin)),
            'max_abs_Z_minus_1': max(abs(r['Z'] - 1) for r in rows if not r['planted']),
            'power_theta_broken': int(sum(r['T_P_wrong_theta'] < 1 for r in rows if r['Delta'] <= 1)), 'min_wrong_theta': min(r['T_P_wrong_theta'] for r in rows if r['Delta'] <= 1), 'rows': rows}


def main(save=True):
    res = {'R_in_order': r1_report(), 'DR_P_general_Gamma': dr_p_general(), 'python': sys.version.split()[0], 'numpy': np.__version__}
    res['ok'] = bool(res['R_in_order']['ok'] and res['DR_P_general_Gamma']['ok'] and res['DR_P_general_Gamma']['power_theta_broken'] > 0)
    if save: json.dump(res, open(OUT, 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
    return res


if __name__ == '__main__':
    r = main(); print(json.dumps({k: ({a: b for a, b in v.items() if a != 'rows'} if isinstance(v, dict) else v) for k, v in r.items()}, indent=1, default=str))
