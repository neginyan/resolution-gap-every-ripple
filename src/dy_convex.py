"""Stage DY, item 2.1: THE CONVEXITY LEMMA OF THE CHORD FORM, AND THE INVENTORY OF THE REMAINDERS READ FROM THE CODE.  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).
LEMMA (chord) [proof].  Let f_1, ..., f_m be nonnegative, nondecreasing and convex on [0, eta_bar].  Then every sum and every product of them is nonnegative,
nondecreasing and convex (product of two: (fg)'' = f''g + 2f'g' + fg'' >= 0, (fg)' = f'g + fg' >= 0; induction).  eta(lam) = 1/lam - 1 is convex and decreasing on
(0, 1] (eta' = -1/lam^2, eta'' = 2/lam^3).  For such an R, (R o eta)'' = R''(eta) eta'^2 + R'(eta) eta'' >= 0: R(eta(lam)) is convex in lam, so on [4/5, 1]
    R(eta(lam)) <= R(0) + (R(1/4) - R(0)) * 5 (1 - lam)        (the chord; eta(4/5) = 1/4, eta(1) = 0).
BASICS: eta, eta^2, 1/(1 - eta), 1/(1 - eta)^2, sqrt(CZ) = eta/(sqrt(e)(1 - eta)), (1 + eta)/(1 - eta); and 1 + eta (affine) in sums.  Each is nonnegative, nondecreasing
and convex on [0, 1/4].  So every remainder line built from them by sums and products with nonnegative eta-free factors is under its chord.
THE SPLIT where a remainder multiplies the sandwich (right after the lemma in the paper):  lam (1 - q) >= lam - q  (P2z's ringf, th0; lam <= 1, q >= 0);
    (2 lam - 1) k1(eta) <= (2 lam - 1)(1 + 0.184 k_E) + eta k_E  (d1);   (2 lam - 1)(1 + 2 eta k_E) <= (2 lam - 1) + 2 eta k_E  (d3)   (2 lam - 1 <= 1).
THE INVENTORY CHECK (read from the code).  The source of dk_table.lines is parsed (ast); every name assigned in it is typed from its expression, and every one of the
37 coefficients is typed by a grammar:
    F   eta-free and nonnegative (numbers, the state quantities r, B, kap, P, mu, b, kE, gs, ...);
    P   nonnegative, nondecreasing, convex in eta: eta;  P + P, P + F;  P * P, P * F;  P ** n (n >= 1);  x / F;  x / ome**k (1/(1 - eta)^k);  sqrt(CZ / F);
    FL  the sandwich factor fl = 1/(1 + eta);  RF  ringf = 1 - P (the sandwich remainder, split as lam ringf >= lam - (1 - ringf));
    X   anything else (ome = 1 - eta in a numerator, a P in a denominator, sqrt of another P, ...).
  Losses and den (sign -1) must be F or P;  gains (sign +1) must be F, FL * F, or RF * FL * F.  The basics met in each line are listed and compared with the
  hand-written INVENTORY below (written from reading the code, before the check ran).
  POWER: (p1) N2 multiplied by (1 - eta);  (p2) A1w with 1/(1 + eta) in place of (1 + eta);  (p3) d3 with sqrt(eta): each must be caught (type X or a changed inventory).
NUMBERS: (n1) every product of up to three of the six basics, on lam in [4/5, 1] (201 points): chord - value >= 0;  (n2) the coefficients of the 37 lines of
  dk_table at random states, as functions of lam through eta = 1/lam - 1: chord - value >= 0 for the losses (relative 1e-25).
-> results_DY/dy_convex.json"""
import ast, inspect, itertools, json, math, os, sys, time
from decimal import Decimal as Dc, localcontext
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dk_table as T, dk_lemma as K, dk_audit as AU

ETA_NAMES = {'eta'}
# hand-written (from the source of dk_table.lines, stage DY): line -> basics met (eta-free lines: empty)
# The first hand-written list (kept for the record) had three wrong rows: N4G listed 'eta' (N4G has M4g, which carries only 1/(1 - eta), and X1CZ),
# B2s and uB2s listed eta^2 and 1/(1-eta)^2 besides sqrt(CZ) (c_s = sqrt(CZ/2) + ...: the basic is sqrt(CZ) itself).  The check found them; corrected below.
INVENTORY_FIRST_WRONG_ROWS = {'N4G': ['1/(1-eta)', '1/(1-eta)^2', 'eta', 'eta^2'], 'B2s': ['1/(1-eta)', '1/(1-eta)^2', 'eta^2', 'sqrt(CZ)'],
                              'uB2s': ['1/(1-eta)', '1/(1-eta)^2', 'eta^2', 'sqrt(CZ)']}
INVENTORY = {
    'P1': [], 'P3z': [], 'P4z': [], 'M0Xi': [], 'A1v': [], 'B1w1': [],
    'P2z': ['sandwich fl', 'sandwich ringf: (1+eta)/(1-eta)'], 'hFz': ['sandwich fl'], 'cKz': ['sandwich fl'],
    'd1': ['eta'], 'd2': ['1/(1-eta)'], 'd3': ['eta'], 'd4': ['1/(1-eta)'],
    'N1': ['eta'], 'N2': ['eta'], 'N3': ['1/(1-eta)', 'eta'], 'N4': ['1/(1-eta)^2', 'eta', 'eta^2'], 'N4G': ['1/(1-eta)', '1/(1-eta)^2', 'eta^2'],
    'ring2': ['1/(1-eta)', 'eta^2'], 'A1w': ['eta'], 'A2k': ['1/(1-eta)'], 'A2a': ['eta'], 'A2b': ['1/(1-eta)', 'eta^2'], 'B1w2': ['1/(1-eta)', 'eta^2'],
    'B2a': ['1/(1-eta)^2'], 'B2b': ['1/(1-eta)^2', 'eta^2'], 'pair': ['1/(1-eta)'], 'hneg1': ['eta'], 'lossK': ['1/(1-eta)'],
    'B2c': ['1/(1-eta)'], 'B2s': ['1/(1-eta)', 'sqrt(CZ)'], 'B1m': ['1/(1-eta)'],
    'B1c': ['1/(1-eta)', '1/(1-eta)^2', 'eta^2', 'sqrt(CZ)'], 'B1l': ['1/(1-eta)'], 'uB2c': ['1/(1-eta)'], 'uB2s': ['1/(1-eta)', 'sqrt(CZ)'],
    'FzK': ['1/(1-eta)'],
}


class Ty:
    """core in {'F', 'P', 'X'}; sandwich: tuple of 'fl'/'rf'; basics: set of strings"""
    def __init__(s, core, sand=(), basics=()):
        s.core, s.sand, s.basics = core, tuple(sorted(sand)), set(basics)

    def __repr__(s): return 'Ty(%s,%s,%s)' % (s.core, s.sand, sorted(s.basics))


F = lambda: Ty('F')
X = lambda why='': Ty('X', basics={'X: ' + why})


def _num(n): return isinstance(n, ast.Constant) and isinstance(n.value, (int, float))


def _is_one(n): return _num(n) and n.value == 1


class Typer:
    def __init__(s, env): s.env = env

    def ty(s, n):
        e = s.env
        if isinstance(n, ast.Constant): return F()
        if isinstance(n, ast.Name):
            if n.id in ETA_NAMES: return Ty('P', basics={'eta'})
            return e.get(n.id, F())
        if isinstance(n, ast.Subscript): return F()                                   # q['...']: state quantities (eta-free; checked in dk_lemma.state)
        if isinstance(n, ast.IfExp):                                                   # a switch of a wrong version (1 if W_(...) else x) or a guard (x if brk > 0 else 0)
            b_, o_ = n.body, n.orelse
            return s.ty(o_) if isinstance(b_, ast.Constant) else (s.ty(b_) if isinstance(o_, (ast.Constant, ast.Call)) and s.ty(o_).core == 'F' else s.ty(b_))
        if isinstance(n, ast.UnaryOp): return X('unary minus') if s.ty(n.operand).core != 'F' else F()
        if isinstance(n, ast.Call):
            fn = n.func
            if isinstance(fn, ast.Attribute) and fn.attr == 'sqrt':
                a = s.ty(fn.value)
                if a.core == 'F' and not a.sand: return F()
                if a.basics <= {'CZ'} | {'eta^2', '1/(1-eta)^2'} and getattr(fn.value, '_cz', False): return Ty('P', basics={'sqrt(CZ)'})
                return X('sqrt of an eta-dependent quantity')
            if isinstance(fn, ast.Attribute) and fn.attr == 'exp': return F() if s.ty(fn.value).core == 'F' else X('exp')
            if isinstance(fn, ast.Name) and fn.id == 'min':
                ts = [s.ty(a) for a in n.args]
                return F() if all(t.core == 'F' and not t.sand for t in ts) else X('min of eta-dependent')
            if isinstance(fn, ast.Name) and fn.id in ('Dc', 'D'): return F()
            if isinstance(fn, ast.Attribute) and fn.attr in ('PI',): return F()
            return F() if all(s.ty(a).core == 'F' for a in n.args) else X('call')
        if isinstance(n, ast.Attribute): return F()
        if isinstance(n, ast.BinOp):
            a, b = n.left, n.right; A, B = s.ty(a), s.ty(b)
            if isinstance(n.op, ast.Add):
                if A.sand or B.sand: return X('sum with a sandwich factor')
                if 'X' in (A.core, B.core): return X('sum with X') if 'X' in (A.core, B.core) else F()
                core = 'P' if 'P' in (A.core, B.core) else 'F'; return Ty(core, basics=A.basics | B.basics)
            if isinstance(n.op, ast.Sub):
                if A.core == 'F' and not A.sand and B.core == 'F' and not B.sand: return F()      # eta-free differences (1 - b, 1 - z2/2 ...) are positive where used
                if _is_one(a) and isinstance(b, ast.Name) and b.id in ETA_NAMES: return Ty('OME')
                if _is_one(a) and B.core == 'P' and not B.sand: return Ty('F', sand=('rf',), basics={'sandwich ringf: ' + s.rf_label(B)})
                return X('difference with eta')
            if isinstance(n.op, ast.Mult):
                if 'OME' in (A.core, B.core): return X('(1 - eta) in a numerator')
                if 'X' in (A.core, B.core): return X('product with X')
                core = 'P' if 'P' in (A.core, B.core) else 'F'; return Ty(core, A.sand + B.sand, A.basics | B.basics)
            if isinstance(n.op, ast.Div):
                if _is_one(a) and isinstance(b, ast.BinOp) and isinstance(b.op, ast.Add) and _is_one(b.left) and isinstance(b.right, ast.Name) and b.right.id in ETA_NAMES:
                    return Ty('F', sand=('fl',), basics={'sandwich fl'})                       # fl = 1/(1 + eta)
                k = s.ome_power(b)
                if k is not None:                                                             # x / (F * ome**k)
                    if A.core == 'X' or A.core == 'OME': return X('numerator')
                    return Ty('P', A.sand, A.basics | {('1/(1-eta)' if k == 1 else '1/(1-eta)^%d' % k)})
                if B.core == 'F' and not B.sand and A.core != 'OME': return Ty(A.core, A.sand, A.basics) if A.core != 'X' else A
                return X('division by an eta-dependent quantity')
            if isinstance(n.op, ast.Pow):
                if A.core == 'F' and not A.sand and B.core == 'F': return F()
                if A.core == 'P' and _num(b) and b.value >= 1 and float(b.value).is_integer():
                    bs = set(A.basics)
                    if bs == {'eta'} and b.value == 2: bs = {'eta^2'}
                    return Ty('P', A.sand, bs)
                return X('power')
        return X(type(n).__name__)

    def rf_label(s, B): return '(1+eta)/(1-eta)' if '1/(1-eta)' in B.basics and 'eta' in B.basics else ','.join(sorted(B.basics))

    def ome_power(s, b):
        """b = (product of F factors and ome / ome**k): return k, else None"""
        fs = []
        def flat(n):
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Mult): flat(n.left); flat(n.right)
            else: fs.append(n)
        flat(b); k = 0
        for f in fs:
            if isinstance(f, ast.Name) and s.env.get(f.id) is not None and s.env[f.id].core == 'OME': k += 1; continue
            if isinstance(f, ast.BinOp) and isinstance(f.op, ast.Pow) and isinstance(f.left, ast.Name) and s.env.get(f.left.id) is not None and s.env[f.left.id].core == 'OME' and _num(f.right):
                k += int(f.right.value); continue
            t = s.ty(f)
            if t.core != 'F' or t.sand: return None
        return k if k > 0 else None


def analyse(src):
    """type every assignment of lines() and every coefficient of the dict T."""
    fn = ast.parse(src).body[0]; env = {}; ty = Typer(env); lines_ty = {}
    def walk(st):
        for s_ in st:
            if isinstance(s_, ast.With): walk(s_.body); continue
            if isinstance(s_, ast.Assign):
                tg = s_.targets[0]
                if isinstance(tg, ast.Tuple) and isinstance(s_.value, ast.Tuple):
                    for a, b in zip(tg.elts, s_.value.elts):
                        if isinstance(a, ast.Name): env[a.id] = ty.ty(b)
                elif isinstance(tg, ast.Tuple):
                    for a in tg.elts:
                        if isinstance(a, ast.Name): env[a.id] = F()                         # tuple unpacking from q[...] (state) -- eta handled by name
                elif isinstance(tg, ast.Name):
                    if tg.id == 'T' and isinstance(s_.value, ast.Dict):
                        for k, v in zip(s_.value.keys, s_.value.values):
                            sign = v.elts[1]
                            if isinstance(sign, ast.IfExp): sign = sign.orelse                # hneg1: '+1 if W_(...) else -1': the default branch
                            sg = (-1 if isinstance(sign.op, ast.USub) else 1) * int(sign.operand.value) if isinstance(sign, ast.UnaryOp) else int(sign.value)
                            lines_ty[k.value] = (sg, ty.ty(v.elts[3]))
                    else:
                        t = ty.ty(s_.value)
                        if tg.id == 'CZ': t = Ty('P', basics={'eta^2', '1/(1-eta)^2'}); t.cz = True
                        env[tg.id] = t
    # mark CZ: sqrt(CZ / F) is the basic sqrt(CZ); X1CZ = X1^2 + CZ carries eta^2/(1-eta)^2
    class M(ast.NodeTransformer):
        def visit_Call(self, n):
            self.generic_visit(n)
            if isinstance(n.func, ast.Attribute) and n.func.attr == 'sqrt':
                v = n.func.value; nm = [x.id for x in ast.walk(v) if isinstance(x, ast.Name)]
                if 'CZ' in nm and not any(x in nm for x in ('eta', 'X1CZ', 'ome')): v._cz = True
            return n
    fn = M().visit(fn); walk(fn.body)
    out = {}
    for k, (sg, t) in lines_ty.items():
        if sg < 0: ok = t.core in ('F', 'P') and not t.sand
        else: ok = t.core == 'F' and t.sand in ((), ('fl',), ('fl', 'rf'))
        bs = sorted(b for b in t.basics if not b.startswith('X'))
        out[k] = {'sign': sg, 'type': t.core, 'sandwich': list(t.sand), 'basics': bs, 'grammar ok': bool(ok), 'why not': sorted(b for b in t.basics if b.startswith('X'))}
    return out


def inventory_check(src=None):
    src = src or inspect.getsource(T.lines); a = analyse(src)
    bad = {k: v for k, v in a.items() if not v['grammar ok']}
    diff = {k: {'code': a[k]['basics'] if k in a else None, 'hand': INVENTORY.get(k)} for k in set(a) | set(INVENTORY)
            if k not in a or k not in INVENTORY or sorted(a[k]['basics']) != sorted(INVENTORY[k])}
    return a, bad, diff


def power():
    src = inspect.getsource(T.lines); out = {}
    V = {'(p1) N2 times (1 - eta)': ("(1 + eta * kE * r / (1 + r) + 2 * eta * kE / (1 + r)) / (16 * B)),", "(1 + eta * kE * r / (1 + r) + 2 * eta * kE / (1 + r)) * ome / (16 * B)),"),
         '(p2) A1w with 1/(1 + eta)': ("B * (1 + eta) / (4 * sqpi)),", "B / (1 + eta) / (4 * sqpi)),"),
         '(p3) d3 with sqrt(eta)': ("gam * (1 + 2 * eta * kE) / 4),", "gam * (1 + 2 * eta.sqrt() * kE) / 4),")}
    for nm, (o, n) in V.items():
        assert src.count(o) == 1, nm
        a, bad, diff = inventory_check(src.replace(o, n))
        out[nm] = {'flagged by the grammar': sorted(bad), 'inventory differences': sorted(diff), 'caught': bool(bad or diff)}
    return out


def numbers(seed=7, n=60):
    """(n1) products of up to three basics; (n2) the loss lines of dk_table as functions of lam."""
    lam = np.linspace(0.8, 1.0, 201); eta = 1 / lam - 1
    B = {'eta': eta, 'eta^2': eta ** 2, '1/(1-eta)': 1 / (1 - eta), '1/(1-eta)^2': 1 / (1 - eta) ** 2, 'sqrt(CZ)': eta / (math.sqrt(math.e) * (1 - eta)),
         '(1+eta)/(1-eta)': (1 + eta) / (1 - eta)}
    worst = 1.0; nprod = 0
    for k in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(B, k):
            f = np.prod([B[c] for c in combo], axis=0); ch = f[-1] + (f[0] - f[-1]) * 5 * (1 - lam); nprod += 1
            worst = min(worst, float(np.min(ch - f)))
    # (n2)
    w2 = Dc(1); cnt = 0
    for ell in (55.26, 960.8, 1e6):
        rng = np.random.default_rng(seed); st_, fam = AU.sample(ell, rng, n); c = K.context(ell); gam = AU.gamma(ell, c)
        for st in st_:
            q = K.state(ell, *st, c)
            with localcontext(c):
                def coef(e):
                    qq = dict(q); qq['eta'] = e; TT, brk = T.lines(qq, c, gam); return {k: v[3] for k, v in TT.items() if v[1] < 0}
                c0 = coef(Dc(0)); c4 = coef(Dc('0.25'))
                for lm in (Dc('0.81'), Dc('0.85'), Dc('0.9'), Dc('0.95'), Dc('0.99')):
                    cm = coef(1 / lm - 1); w = (lm - Dc('0.8')) / Dc('0.2')
                    for k in cm:
                        ch = w * c0[k] + (1 - w) * c4[k]; s_ = max(abs(ch), abs(cm[k]))
                        if s_ > 0: w2 = min(w2, (ch - cm[k]) / s_); cnt += 1
    return {'(n1) products of up to three basics': nprod, '(n1) smallest chord - value': worst,
            '(n2) loss-line coefficients compared (states x lam x lines)': cnt, '(n2) smallest (chord - value)/scale': float(w2),
            'ok': bool(worst >= -1e-12 and w2 >= Dc('-1e-25'))}


def run():
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    a, bad, diff = inventory_check()
    out['inventory read from the code (line -> sign, type, sandwich, basics)'] = a
    out['lines outside the grammar (must be empty)'] = sorted(bad); out['differences from the hand-written inventory (must be empty)'] = diff
    out['the first hand-written list: rows found wrong by the check (corrected)'] = INVENTORY_FIRST_WRONG_ROWS
    out['power'] = power(); out['numbers'] = numbers()
    out['ok'] = bool(not bad and not diff and all(v['caught'] for v in out['power'].values()) and out['numbers']['ok'] and len(a) == 37)
    out['seconds'] = time.time() - t0
    return out


if __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DY'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dy_convex.json'), 'w'), indent=1, default=str)
    print('bad', r['lines outside the grammar (must be empty)'], 'diff', r['differences from the hand-written inventory (must be empty)'])
    print('power', {k: v['caught'] for k, v in r['power'].items()}); print('numbers', r['numbers']); print(r['ok'])
