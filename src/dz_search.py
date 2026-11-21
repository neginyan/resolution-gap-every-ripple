"""Stage DZ, item 2.2: THE SEARCH FOR SMALL TRUE g sqrt(ell) ON STRONG RIPPLES (DZ_探索計画.md sections 2-6).  [numerical]
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
Objective: Q sqrt(ell), Q = (a) + (a') the true quantity of dz_truth.truth (g >= (1 - |eps|) Q), MINIMISED over the state (t0, b, x, r, a) and the shape of
the window (dz_windows), for each family, ripple strength eta in {1/4, 0.1, 1/ell} and room:
  narrow (Theorem 2):  b <= 1/2, B = b/sigma^2 >= max(2.5e10, 50 (8 ell + 100));   resolution (Theorem 3):  1/2 < b <= 1;
  wide band (Theorem 4's band):  8 ell + 100 <= B < ell^4.
Box (log scales):  5e11 sigma^2 <= x <= 0.003 (spike family S: x >= 1e-3, packets: x <= 60/n0^2, see the narrowing in the report);
  sigma^2 <= r <= 1/4 (r < sigma^2 forces L^2 = s^2/r > 1 since s >= sigma);  max(4 sigma^2, 4 sigma/900) <= a <= 4 r/sigma (L <= 3; a larger L only adds background, see the report).
The objective uses the coarse t-grid of dz_truth (M_rule 'fast', up to 0.5% off); every reported value is re-evaluated on the fine grid
(dz_post.py).  Method: uniform starts in the unit cube of the parameters (seeded), each refined by Nelder-Mead in tanh coordinates (scipy), budget per start fixed.
Power (section 6): (p1) 'drop III', (p2) 'sign', (p4) 'sandwich' variants of dz_truth, searched with the same budget; (p3) a planted dip of depth 1/2 at a
secret point of the unit cube, multiplied into the objective, which the same search must find.
    python3 src/dz_search.py main [ell]   -> results_DZ/dz_search_<ell>.json
    python3 src/dz_search.py power        -> results_DZ/dz_power.json"""
import json, math, os, sys, time
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dz_truth as T, dz_windows as W

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAMS = {'W1': [], 'W2-3': ['rho'], 'W2-21': ['rho'], 'W2-61': ['rho'], 'S': ['rho'], 'Pt': ['rho', 'n0', 'D'], 'Pc': ['rho', 'n0', 'D']}
ROOMS = ('narrow', 'resolution', 'wide band')


def boxes(ell, room, fam):
    sig_l = -ell
    if room == 'narrow': bl = (math.log(max(2.5e10, 50 * (8 * ell + 100))) + 2 * sig_l, math.log(0.5))
    elif room == 'resolution': bl = (0.5, 1.0)
    else: bl = (math.log(8 * ell + 100) + 2 * sig_l, 4 * math.log(ell) + 2 * sig_l)
    xl = (math.log(5e11) + 2 * sig_l, math.log(0.003))
    if fam == 'S': xl = (math.log(1e-3), math.log(0.003))
    return bl, xl


def decode(z, ell, room, fam, eta, Lcap=3.0):
    """Lcap: the cap L <= Lcap of the main search (with r >= sigma^2, and a within e^{+-14} of sqrt(b)); None: the class box (L^2 <= 1/sigma by (P0),
    r >= sigma^3, log a uniform between its two ends), with the split form of dz_truth."""
    z = np.clip(np.asarray(z, float), 0, 1); bl, xl = boxes(ell, room, fam)
    t0 = 2 * math.pi * z[0]
    ex = math.exp if ell <= 200 else (lambda v: np.exp(np.longdouble(v)))      # ell > 200: longdouble (sigma^2 is below the double range)
    lb = math.log(bl[0] + (bl[1] - bl[0]) * z[1]) if room == 'resolution' else bl[0] + (bl[1] - bl[0]) * z[1]
    b = bl[0] + (bl[1] - bl[0]) * z[1] if room == 'resolution' else ex(lb)
    lx = xl[0] + (xl[1] - xl[0]) * z[2]
    rlo = -2 * ell if Lcap else -3 * ell
    lr = rlo + (math.log(0.25) - rlo) * z[3]        # r >= sigma^2 (r < sigma^2 forces L > 1: see the narrowing)
    la_lo = max(math.log(4) - 2 * ell, math.log(4 / Lcap ** 2) - ell) if Lcap else math.log(4) - 2 * ell; la_hi = math.log(4) + lr + ell
    lba = math.log(b) if ell <= 200 else lb
    if Lcap:
        la = min(max(0.5 * lba + (-14 + 28 * z[4]), la_lo), la_hi)   # a = sqrt(b) e^alpha, |alpha| <= 14, clipped to the box
    else:   # the class box: log a uniform on [log 4 sigma^2, log 4 r/sigma] (in the wide band the ripple balance a ~ r is far from sqrt(b))
        la = la_lo + (la_hi - la_lo) * z[4]
    sh = {}; k = 5
    for nm in FAMS[fam]:
        if nm == 'rho': sh['rho'] = math.exp(math.log(1e-3) * (1 - z[k]))
        if nm == 'n0': sh['n0'] = 5 + 145 * z[k]
        if nm == 'D': sh['D'] = 1 + 7 * z[k]
        k += 1
    if fam.startswith('W2-'): sh['m'] = int(fam.split('-')[1])
    x = ex(lx)
    if fam in ('Pt', 'Pc'):
        x = min(x, 60 / sh['n0'] ** 2); lx = min(lx, math.log(60 / sh['n0'] ** 2))
    return {'t0': t0, 'b': b, 'x': x, 'r': ex(lr), 'a': ex(la), 'shape': sh, 'log b': lb, 'log x': lx, 'log r': lr, 'log a': la}


def evaluate(z, ell, room, fam, eta, variant=None, full=False, prec=None, mode='all', M_rule='fast', pen=1e3, logobj=False, Lcap=3.0):
    """pen: the value returned for an inadmissible window (1e3; below the true values of the wide band, where pen = 1e300 is used: dz_ell.py)."""
    st = decode(z, ell, room, fam, eta, Lcap)
    fb = 'W2' if fam.startswith('W2') else fam
    q, ph, info = W.build(fb, eta, st['x'], ell, **st['shape'])
    if q is None: return (pen, None) if full else pen
    prec = prec or ('d' if ell <= 200 else 'ld')
    try:
        o = T.truth(ell, b=st['b'], x=st['x'], a=st['a'], r=st['r'], q=q, ph=ph, t0=st['t0'], variant=variant, local=full, prec=prec, M_rule=M_rule)
    except (FloatingPointError, ValueError, ZeroDivisionError, OverflowError):
        return (pen, None) if full else pen
    v = o['Q sqrt(ell)'] if not logobj else o['log Q sqrt(ell)']      # logobj (dz_ell at ell = 960.8): the logarithm, since Q can exceed the double range
    if not np.isfinite(v) or (v <= 0 and not logobj): v = pen
    if mode == 'bright':      # ripple-dominated states only: W >= b (penalty grows with log(b/W) below)
        wb = o['W/b (ripple part of den over b)']
        if not wb >= 1:
            v = (v + math.log(1 + 10 * min(100.0, math.log(1 / max(wb, 1e-300)))) + 1) if logobj else v * (1 + 10 * min(100.0, math.log(1 / max(wb, 1e-300)))) + 10
    if full:
        o.update({'state': st, 'window': info, 'family': fam, 'room': room, 'eta target': eta})
        return v, o
    return v


def search(ell, room, fam, eta, starts=6, maxfev=120, seed=0, variant=None, dip=None, nsample=400, mode='all', dipw=0.35, obj='Q', pen=1e3, logobj=False, Lcap=3.0):
    """stage 1: nsample uniform points of the unit cube; stage 2: Nelder-Mead from the best `starts` of them."""
    rng = np.random.default_rng(seed); d = 5 + len(FAMS[fam]); best = []; nev = [0]

    def f_unit(z):
        nev[0] += 1; v = evaluate(z, ell, room, fam, eta, variant, mode=mode, pen=pen, logobj=logobj, Lcap=Lcap)
        if obj == 'ratio' and v < 1e3:       # the sandwich inside the truth: Q/Q_h1 (dz_sandwich.py); ripple-dominated states only (mode 'bright')
            v1 = evaluate(z, ell, room, fam, eta, 'h1'); v = v / v1 if (v1 < 1e3 and (mode != 'bright' or v < 10 * v1)) else 1e3
        if dip is not None:   # a planted bowl below the true minimum: (z*, m) -> min(v, m (0.3 + 0.7 |z - z*|^2/dipw^2))
            v = min(v, dip[1] * (0.3 + 0.7 * float(((np.clip(z, 0, 1) - dip[0]) ** 2).sum()) / dipw ** 2))
        return v
    fp = lambda p: f_unit((1 + np.tanh(p)) / 2)
    Z0 = rng.random((nsample, d)); v0 = np.array([f_unit(z) for z in Z0]); order = np.argsort(v0)
    for s in range(starts):
        z0 = Z0[order[s]]; p0 = np.arctanh(np.clip(2 * z0 - 1, -0.999, 0.999))
        res = minimize(fp, p0, method='Nelder-Mead', options={'maxfev': maxfev, 'xatol': 1e-4, 'fatol': 1e-7, 'initial_simplex': p0 + 0.6 * np.vstack([np.zeros(d), np.eye(d)])})
        best.append((float(res.fun), ((1 + np.tanh(res.x)) / 2).tolist()))
    best.sort(key=lambda t: t[0])
    return best, nev[0]


def summarize(v, o):
    if o is None: return {'Q sqrt(ell)': v}
    keys = ('Q sqrt(ell)', 'W/b (ripple part of den over b)', 'path', 'mu', 'P', 'G', 'kappa', 'tau', 'eta', 'E0', 'L', 's')
    out = {k: o.get(k) for k in keys}; st = o['state']
    out.update({'t0': st['t0'], 'log b': st['log b'], 'log x': st['log x'], 'log r': st['log r'], 'log a': st['log a'], 'b': float(st['b']), 'x': float(st['x']),
                'r': float(st['r']), 'a': float(st['a']), 'shape': st['shape'], 'window': o['window']})
    return out


def run_combo(args):
    ell, room, fam, eta_name, eta, starts, maxfev, seed, mode = args
    t1 = time.time(); best, nev = search(ell, room, fam, eta, starts, maxfev, seed, mode=mode)
    v, o = evaluate(best[0][1], ell, room, fam, eta, full=True, mode=mode)
    return {'ell': ell, 'room': room, 'family': fam, 'eta': eta_name, 'eta value': eta, 'mode': mode, 'evaluations': nev, 'seconds': time.time() - t1,
            'min Q sqrt(ell)': best[0][0], 'at': summarize(v, o), 'z of the 5 best starts': [b[1] for b in best[:5]], 'values of the 5 best starts': [b[0] for b in best[:5]]}


def main(ell, starts=6, maxfev=150, procs=2):
    from multiprocessing import Pool
    etas = {'1/4': 0.25, '0.1': 0.1, '1/ell': 1 / ell}
    jobs = []; k = 0
    for mode in ('all', 'bright'):
        for room in ROOMS:
            for fam in FAMS:
                for en, ev in etas.items():
                    k += 1; jobs.append((ell, room, fam, en, ev, starts, maxfev, 1000 + k, mode))
    t0 = time.time(); rows = []
    with Pool(procs) as P:
        for r in P.imap_unordered(run_combo, jobs):
            rows.append(r); print(r['mode'], r['room'], r['family'], r['eta'], round(r['min Q sqrt(ell)'], 5), round(r['seconds']), flush=True)
    rows.sort(key=lambda r: (r['mode'], ROOMS.index(r['room']), list(FAMS).index(r['family']), r['eta']))
    out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'ell': ell, 'starts per combination': starts, 'Nelder-Mead evaluations per start': maxfev, 'rows': rows}
    for mode in ('all', 'bright'):
        for en in etas:
            rr = [r for r in rows if r['eta'] == en and r['mode'] == mode]; w = min(rr, key=lambda r: r['min Q sqrt(ell)'])
            out['smallest Q sqrt(ell) [%s], eta = %s' % (mode, en)] = {'value': w['min Q sqrt(ell)'], 'room': w['room'], 'family': w['family']}
            for room in ROOMS:
                r2 = [r for r in rr if r['room'] == room]; w2 = min(r2, key=lambda r: r['min Q sqrt(ell)'])
                out['smallest Q sqrt(ell) [%s], eta = %s, %s' % (mode, en, room)] = {'value': w2['min Q sqrt(ell)'], 'family': w2['family']}
    out['seconds'] = time.time() - t0
    os.makedirs(os.path.join(ROOT, 'results_DZ'), exist_ok=True)
    json.dump(out, open(os.path.join(ROOT, 'results_DZ', 'dz_search_%s.json' % ell), 'w'), indent=1)
    return out


if __name__ == '__main__':
    if sys.argv[1] == 'main':
        main(float(sys.argv[2]) if len(sys.argv) > 2 else 55.26)
