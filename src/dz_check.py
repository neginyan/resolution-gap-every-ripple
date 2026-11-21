"""Stage DZ, item 2.2: THE CHECKS OF THE METHOD of dz_truth (DZ_探索計画.md section 1).  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
 (c1) against dp_truth.direct of paper I (the brute two-dimensional quadrature in v and w), at ell = 8 where double precision suffices: 15 states, windows of
      the families of dz_windows at eta = 1/4, 0.1 and 1/ell, foci at crest, trough and node, tau from 0.002 to 2, both paths of dz_truth (Fourier and
      Gauss-Hermite); the largest relative difference must be below 1e-4 (the error of the brute quadrature);
 (c2) against the closed form of Lemma 11 of paper I (R = 0; Decimal, 1200 digits) at ell = 8, 55.26 and 960.8 (longdouble), 27 states: below 1e-12;
 (c3) the grid doubled (M x 4, Gauss-Legendre order 16) at 6 states of the families at ell = 55.26: below 1e-8; the two paths against each other: below 1e-8;
 (c4) the split form (R = 0 in closed form plus the ripple part on |w| <~ 14 s; used for L > 3) against the full w-quadrature, at L = 2 and 4, 4 windows: below 1e-12;
 POWER: (w1) 'drop III' and (w2) 'sign' at 6 states with a visible ripple: each must differ from the true value by more than 1e-3 at one state at least;
        (w3) a wrong closed form (A2 with the factor 1 - alpha^2 dropped) must differ from dz_truth at R = 0 by more than 1e-12 at one state.
-> results_DZ/dz_check.json"""
import json, math, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_truth as T, dz_windows as W, dp_truth as P

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    ell = 8.0; sig = math.exp(-ell); c1 = []
    cases = [('W1', {}, 0.25, 0.3, 0.002, 1.0, 0.05, 0.0), ('W1', {}, 0.25, 0.05, 0.003, 3.0, 0.2, math.pi), ('W1', {}, 0.1, 0.4, 0.0005, 1.0, 0.25, math.pi / 2),
             ('W1', {}, 1 / 8, 0.01, 0.003, 1.0, 0.05, 0.0), ('W2', {'m': 3, 'rho': 0.5}, 0.25, 0.2, 0.001, 0.5, 0.01, 0.0), ('W2', {'m': 3, 'rho': 0.8}, 0.1, 0.002, 0.003, 1.0, 0.02, math.pi),
             ('W2', {'m': 21, 'rho': 0.3}, 0.25, 0.3, 0.0005, 1.0, 0.1, 0.3), ('S', {'rho': 1.0}, 0.25, 0.7, 0.003, 1.0, 0.1, 0.0), ('S', {'rho': 1.0}, 0.25, 0.3, 0.003, 1.0, 0.1, 0.4),
             ('S', {'rho': 0.5}, 0.1, 0.05, 0.003, 2.0, 0.05, math.pi), ('Pt', {'rho': 0.5, 'n0': 12, 'D': 2}, 0.25, 0.3, 0.002, 1.0, 0.1, math.pi),
             ('Pc', {'rho': 0.5, 'n0': 12, 'D': 2}, 0.1, 0.1, 0.002, 1.0, 0.1, 0.0), ('Pt', {'rho': 1.0, 'n0': 8, 'D': 1.5}, 1 / 8, 0.5, 0.003, 1.0, 0.2, math.pi + 0.2),
             ('W1', {}, 0.25, 0.002, 0.003, 1.0, 0.02, 0.0), ('W2', {'m': 3, 'rho': 1.0}, 0.25, 0.003, 0.003, 1.5, 0.05, 1.0)]
    for fam, kw, eta, b, x, fac, r, t0f in cases:
        q, ph, info = W.build(fam, eta, x, ell, **kw)
        L2 = 4 * sig / math.sqrt(b) * fac; a = 4 * sig / L2
        # dp_truth.direct puts the focus at t = 0: shift the phases instead
        ph_s = [p - (n + 1) * t0f for n, p in enumerate(ph)]
        d = P.direct(sig, x, b, L2, r * L2, list(q), ph_s)
        for path in (None, 'gh', 'fourier'):
            if path == 'gh' and math.sqrt(x / b) * len(q) > 25: continue
            o = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', path=path, local=False)
            c1.append({'family': fam, 'eta': eta, 'b': b, 'x': x, 'tau': x / b, 't0': t0f, 'path': o['path'], 'direct': d['sum'], 'dz_truth': o["(a)+(a')"],
                       'relative difference': abs(o["(a)+(a')"] / d['sum'] - 1)})
    out['c1 against dp_truth.direct (ell = 8)'] = c1; out['c1 largest relative difference'] = max(c['relative difference'] for c in c1)
    c2 = []; w3 = []
    for ell2 in (8.0, 55.26, 960.8):
        for b in (0.3, 0.9, 1e-30):
            for a in (2.0, 1e-3, 30.0):
                o = T.truth(ell2, b=b, x=0.002, a=a, r=0.1, q=(0.0,), ph=(0.0,), local=False, prec='ld')
                g = T.g0_closed(ell2, b, a=a); c2.append(abs(o["(a)+(a')"] / g - 1))
                sg = math.exp(-ell2) if ell2 < 700 else 0.0
    out['c2 largest relative difference to Lemma 11 (27 states)'] = max(c2)
    # (w3) the wrong closed form: A2 = 1 - e (the factor 1 - alpha^2 dropped), ell = 8
    from decimal import Decimal as Dc, localcontext
    for b in (0.3, 0.9):
        with localcontext() as C:
            C.prec = 60; sgd = (-Dc(8)).exp(); bd = Dc(b); L2 = 4 * sgd / Dc(2); V = sgd ** 2 / bd; L = L2.sqrt()
            al = sgd * (1 - bd) / (2 * bd).sqrt(); c = (L - sgd ** 2 / L) / Dc(2).sqrt(); e = (-(al ** 2 + c ** 2) / 2).exp()
            A1 = 3 + (1 - c ** 2) * e; A2 = 1 - e; wrong = float((A1 / L2 + A2 / V) / (2 * sgd * (1 / L2 + 1 / V)))
        o = T.truth(8.0, b=b, x=0.002, a=2.0, r=0.1, q=(0.0,), ph=(0.0,), local=False); w3.append(abs(o["(a)+(a')"] / wrong - 1))
    out['w3 wrong closed form: largest difference (must be > 1e-12)'] = max(w3)
    c3 = []; c3p = []; wv = {'drop III': [], 'sign': []}
    ell = 55.26; sig = math.exp(-ell)
    for fam, kw, eta, b, x, a, r, t0f in [('W1', {}, 0.25, 1e-30, 0.003, 1e-14, 1e-3, 0.0), ('W2', {'m': 21, 'rho': 0.5}, 0.25, 1e-20, 1e-4, 1e-9, 1e-2, math.pi),
                                          ('S', {'rho': 1.0}, 0.25, 0.7, 0.002, 1.0, 0.05, 0.3), ('S', {'rho': 0.5}, 0.1, 1e-25, 0.002, 1e-12, 1e-4, 0.0),
                                          ('Pt', {'rho': 0.5, 'n0': 40, 'D': 3}, 0.25, 0.6, 0.0005, 1.0, 0.05, math.pi), ('Pc', {'rho': 1.0, 'n0': 30, 'D': 2}, 0.1, 1e-28, 0.001, 1e-14, 1e-3, 0.0)]:
        q, ph, info = W.build(fam, eta, x, ell, **kw)
        o1 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False)
        o2 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, M=4 * o1['M'], order=16)
        c3.append(abs(o2["(a)+(a')"] / o1["(a)+(a')"] - 1))
        if math.sqrt(x / b) * len(q) <= 25:
            o3 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, path='fourier', M=8192)
            o4 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, path='gh')
            c3p.append(abs(o3["(a)+(a')"] / o4["(a)+(a')"] - 1))
        for var in wv:
            ov = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, variant=var); wv[var].append(abs(ov["(a)+(a')"] / o1["(a)+(a')"] - 1))
    c4 = []
    for fam, kw, eta, b, x, r, t0f in [('S', {'rho': 1.0}, 0.25, 1e-40, 0.002, 1e-3, 0.3), ('Pt', {'rho': 0.5, 'n0': 40, 'D': 3}, 0.25, 1e-41, 0.0005, 1e-5, math.pi),
                                       ('W2', {'m': 21, 'rho': 0.5}, 0.1, 0.3, 0.001, 0.01, 0.0), ('W1', {}, 0.25, 1e-41, 0.003, 0.2, 0.0)]:
        q, ph, info = W.build(fam, eta, x, ell, **kw)
        for Lw in (2.0, 4.0):
            a = 4 * sig / Lw ** 2
            o1 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, force_split=False)
            o2 = T.truth(ell, b=b, x=x, a=a, r=r, q=q, ph=ph, t0=t0f, prec='d', local=False, force_split=True)
            c4.append(abs(o2["(a)+(a')"] / o1["(a)+(a')"] - 1))
    out['c4 split form against the full quadrature: largest relative difference'] = max(c4)
    out['c3 grid doubled: largest relative change'] = max(c3); out['c3 Fourier against Gauss-Hermite: largest relative difference'] = max(c3p)
    out['w1 drop III: largest relative difference (must be > 1e-3)'] = max(wv['drop III']); out['w2 sign: largest relative difference (must be > 1e-3)'] = max(wv['sign'])
    out['ok'] = bool(out['c1 largest relative difference'] < 1e-4 and out['c2 largest relative difference to Lemma 11 (27 states)'] < 1e-12 and max(c3) < 1e-8
                     and max(c3p) < 1e-8 and max(c4) < 1e-12 and out['w1 drop III: largest relative difference (must be > 1e-3)'] > 1e-3 and out['w2 sign: largest relative difference (must be > 1e-3)'] > 1e-3
                     and out['w3 wrong closed form: largest difference (must be > 1e-12)'] > 1e-12)
    out['seconds'] = time.time() - t0
    os.makedirs(os.path.join(ROOT, 'results_DZ'), exist_ok=True)
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_check.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if not k.startswith('c1 against')}, indent=1))
    return out


if __name__ == '__main__':
    main()
