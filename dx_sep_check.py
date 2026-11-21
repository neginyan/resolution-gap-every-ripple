"""Stage DX, item 2.1: checks of the separation of eta (the ripple) and 1/ell in the code.  Python 3.11 grammar.
(A1b) explicit eta = Iv(1/L) equals eta=None (the published case) on every key, on pieces and points.
(A3)  the dependency map: at eta = 1/4 against eta = 1/ell, the keys predicted (before the run) to be free of eta are unchanged,
      and every other key changes; a planted 'forgotten separation' (eps1 keeps t) is caught.
(A4)  at eta = 1/4 the values of consts_iv equal the independent float formulas of stage DU (du_eta.py), and a wrong k1 (eta -> 1/ell) does not.
Interval arithmetic runs with the DO watch (decimal.Inexact trapped inside the interval module); here we only read values."""
import os, sys, json, math, decimal
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, 'src'))
import dl_consts as K
from dl_interval import Iv
D = decimal.Decimal

# predicted before the run: keys that do not depend on eta (they use only 1/ell, ell, and fixed numbers)
ETA_FREE = ['Gam sqrt(ell)', 'X1/sqrt(ell)', 'z2_max', 'F1: P <=', 'w16', 'c0 >=', 'm1: mu ell <', 'm_F t']
# added after the first run (honest note): two keys whose formulas hold only fixed numbers, ell and 1/ell, missed in the list above
ETA_FREE_ADDED = ['b.2: G/sigma at mu = ell + ln ell <=', 'kf (b < 0.1)']


def formal_free(src):
    """keys of consts_iv whose assignment does not depend on et (data flow over the source, in order; the if branches are both walked)"""
    import ast
    fn = ast.parse(src).body[0]; taint = {'et', 'eta'}; keys = {}
    def names(n):
        return {x.id for x in ast.walk(n) if isinstance(x, ast.Name)} | {('o', x.slice.value) for x in ast.walk(n)
                if isinstance(x, ast.Subscript) and isinstance(x.value, ast.Name) and x.value.id == 'o' and isinstance(x.slice, ast.Constant)}
    def walk(st):
        for s in st:
            if isinstance(s, ast.If): walk(s.body); walk(s.orelse); continue
            if not isinstance(s, ast.Assign) or any(isinstance(t, ast.Name) and t.id == 'et' for t in s.targets): continue
            dep = bool(names(s.value) & taint)
            for t in s.targets:
                for tt in (t.elts if isinstance(t, ast.Tuple) else [t]):
                    if isinstance(tt, ast.Name): (taint.add if dep else taint.discard)(tt.id)
                    elif isinstance(tt, ast.Subscript) and isinstance(tt.slice, ast.Constant):
                        keys[tt.slice.value] = dep; (taint.add if dep else taint.discard)(('o', tt.slice.value))
    walk(fn.body)
    return sorted(k for k, v in keys.items() if not v)


def val(x):
    return (float(x.lo), float(x.hi)) if hasattr(x, 'lo') else x


def same(a, b):
    return (a.lo == b.lo and a.hi == b.hi) if hasattr(a, 'lo') else a == b


def run():
    out = {}
    # (A1b)
    rows = []
    for La, Lb in [('55.26', '55.26'), ('55.26', '56'), ('960.8', '960.8'), ('960.8', '1000'), ('1e4', '1e4'), ('1e6', '1e6')]:
        L = Iv(D(La), D(Lb)); a = K.consts_iv(La, Lb); b = K.consts_iv(La, Lb, eta=1 / L)
        bad = [k for k in a if not same(a[k], b[k])]
        rows.append({'piece': [La, Lb], 'keys': len(a), 'differing keys': bad})
    out['A1b explicit eta = 1/L equals the published case'] = rows
    ok1 = all(not r['differing keys'] for r in rows)
    # (A3)
    mp = []
    for ell in ('55.26', '960.8', '1e4', '1e6'):
        a = K.consts_iv(ell, ell); b = {}; err = None
        try: K.consts_iv(ell, ell, eta=D('0.25'), _o=b)
        except Exception as ex: err = '%s: %s' % (type(ex).__name__, ex)   # the published constants break at eta = 1/4 (that is the work of 2.2-2.4); keys up to the break are compared
        a = {k: a[k] for k in b}
        unchanged = sorted(k for k in a if same(a[k], b[k])); changed = sorted(k for k in a if not same(a[k], b[k]))
        mp.append({'ell': ell, 'stopped at eta = 1/4': err, 'keys compared': len(b), '_keys': sorted(b), 'unchanged': unchanged, 'changed (number)': len(changed),
                   'predicted eta-free but changed': [k for k in ETA_FREE if k in changed],
                   'unchanged but not predicted': [k for k in unchanged if k not in ETA_FREE]})
    import inspect
    ff = formal_free(inspect.getsource(K.consts_iv)); exp_free = sorted(ETA_FREE + ETA_FREE_ADDED)
    for r in mp:
        r['changed although formally eta-free'] = [k for k in ff if k in r['_keys'] and k not in r['unchanged']]
        r['formally eta-dependent, unchanged in the arithmetic (eta enters only through terms below the precision, e.g. e^{-mu})'] = [k for k in r['unchanged'] if k not in ff]
    for r in mp: del r['_keys']
    out['A3 dependency map'] = mp
    out['A3 formally eta-free keys (data flow over the source)'] = ff
    out['A3 predicted list (+2 added after the first run)'] = exp_free
    num_ok = all(not r['changed although formally eta-free'] for r in mp if r['stopped at eta = 1/4'] is None)
    ok3 = (ff == exp_free) and num_ok and all(not r['predicted eta-free but changed'] for r in mp)
    # (A3) power: forget to separate eps1 (keeps t): the key eps1_max is then unchanged -> caught as 'unchanged but not predicted'
    src = open(K.__file__, encoding='utf-8').read()
    old = "eps1 = et * kE * Dc('2.25') / Dc('1.25')"; assert src.count(old) == 1
    g = {'__name__': 'dl_wrong', '__file__': K.__file__}; exec(compile(src.replace(old, "eps1 = t * kE * Dc('2.25') / Dc('1.25')"), 'dl_wrong', 'exec'), g)
    a = g['consts_iv']('960.8', '960.8'); b = {}
    try: g['consts_iv']('960.8', '960.8', eta=D('0.25'), _o=b)
    except Exception: pass
    gs = src.replace(old, "eps1 = t * kE * Dc('2.25') / Dc('1.25')"); fw = formal_free(gs[gs.index('def consts_iv'):])
    caught = same(a['eps1_max'], b['eps1_max']) and fw != sorted(ETA_FREE + ETA_FREE_ADDED) and 'eps1_max' in fw
    out['A3 power: forgotten separation of eps1 caught'] = caught
    # (A4) the independent float formulas of DU at eta = 1/4
    e = 0.25; kE = math.sqrt(0.2); om = 1 / (1 + 0.75 / 2.5e10) ** 2
    ref = {'k1_max': 1 + (e + 0.184) * kE, 'eps1_max': e * kE * 2.25 / 1.25, 'epsh_max': 2 * kE * (e + 0.184) / om,
           'q_max': (1 + e) / (400 * (1 - e)), 'Gam2 sqrt(ell)': None}
    b = {}; t = 1 / 960.8
    try: K.consts_iv('960.8', '960.8', eta=D('0.25'), _o=b)
    except Exception: pass
    ref['Gam2 sqrt(ell)'] = math.sqrt(1 + 10 * t) / (2 * (1 - e))
    cz = e * e / (math.e * (1 - e) ** 2); ref['c_s'] = math.sqrt(cz / 2) + 0.25 / math.sqrt(math.pi * 2.25)
    rows = []
    for k, r in ref.items():
        lo, hi = val(b[k]); rows.append({'key': k, 'consts_iv': [lo, hi], 'DU float': r, 'inside (rel 1e-12)': lo - 1e-12 * abs(r) <= r <= hi + 1e-12 * abs(r)})
    out['A4 values at eta = 1/4 vs independent formulas'] = rows
    ok4 = all(r['inside (rel 1e-12)'] for r in rows)
    wrongk1 = 1 + (t + 0.184) * kE; lo, hi = val(b['k1_max'])
    out['A4 power: k1 with eta -> 1/ell is outside'] = not (lo <= wrongk1 <= hi)
    out['ok'] = bool(ok1 and ok3 and caught and ok4 and out['A4 power: k1 with eta -> 1/ell is outside'])
    return out


if __name__ == '__main__':
    r = run(); os.makedirs(os.path.join(HERE, 'results_DX'), exist_ok=True)
    json.dump(r, open(os.path.join(HERE, 'results_DX', 'dx_sep_check.json'), 'w'), indent=1, default=str)
    print(json.dumps({k: v for k, v in r.items() if 'map' not in k}, indent=1, default=str)[:3000]); print('ok', r['ok'])
