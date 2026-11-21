"""Stage DN (second review, ChatGPT 2 and 4), extended in stage DO (subtraction with 40-digit ends, ends near 0, infinite ends, crossing 0; the pre-DO
implementation as a fourth wrong version): tests of the interval arithmetic dl_interval and of the monotonicity of E_J.  Python 3.11 grammar.
(A) CORRECT ENCLOSURES: for random intervals (positive, negative, crossing 0, an end at 0, an infinite end) and sample points in them (both ends included),
    the true value of every operation (+, -, x, /, exp, ln, sqrt, integer powers, pe, pec, H, ln L/L, ln(1+U)/U), computed with 90 digits, lies in the
    computed interval; the reciprocal of an interval containing 0 raises ZeroDivisionError.
(B) WRONG VERSIONS, each must be caught (a true value outside the computed interval, or an empty interval):
    (i) no outward widening (WID = 0);  (ii) inward rounding (_dn and _up swapped);  (iii) division by an interval containing 0 allowed.
(C) RANGE: pieces of dl_consts (the first, one near 1e5, the last below 1e6, the tail) recomputed with Overflow and Underflow trapped: none occurs.
(D) MONOTONICITY: dE_J/dmu < 0 on mu in [0, 80] (pieces of 0.01, interval arithmetic) and, for mu >= 1, by the signs of the two terms of
    dE_J/dmu = -4.43 e^{-mu/2} (1 + 4.43 e^{-mu/2}) F + (1 + 4.43 e^{-mu/2})^2 F (1 - mu) e^{-mu}/32,  F = exp(mu e^{-mu}/32) > 0.
-> results/dn_ivtest.json"""
import json, math, sys, time, random
from decimal import Decimal as Dc, localcontext, Context, Overflow, Underflow
import dl_interval as V
from dl_interval import Iv

HP = Context(prec=90, Emax=10 ** 17, Emin=-10 ** 17)


def t_exp(x):
    with localcontext(HP): return x.exp()
def t_ln(x):
    with localcontext(HP): return x.ln()
def t_sqrt(x):
    with localcontext(HP): return x.sqrt()


def true_val(op, xs):
    with localcontext(HP):
        if op == '+': return xs[0] + xs[1]
        if op == '-': return xs[0] - xs[1]
        if op == '*': return xs[0] * xs[1]
        if op == '/': return xs[0] / xs[1]
        if op == 'exp': return t_exp(xs[0])
        if op == 'ln': return t_ln(xs[0])
        if op == 'sqrt': return t_sqrt(xs[0])
        if op == 'pow3': return xs[0] ** 3
        if op == 'pow2': return xs[0] ** 2
        if op == 'pe': k, c, x = Dc(xs[1]), Dc(xs[2]), xs[0]; return (k * x.ln() - c * x).exp() if x > 0 else (Dc(1) if k == 0 else Dc(0))
        if op == 'H': x, L = xs[0], xs[1]; return Dc(2) * x * L - Dc('0.5') * L.ln() - Dc('0.25') * x.ln()
        if op == 'lol': return xs[0].ln() / xs[0]
        if op == 'lq': u = xs[0]; return (1 + u).ln() / u
    raise ValueError(op)


def comp(op, ivs):
    if op == '+': return ivs[0] + ivs[1]
    if op == '-': return ivs[0] - ivs[1]
    if op == '*': return ivs[0] * ivs[1]
    if op == '/': return ivs[0] / ivs[1]
    if op == 'exp': return V.exp(ivs[0])
    if op == 'ln': return V.log(ivs[0])
    if op == 'sqrt': return V.sqrt(ivs[0])
    if op == 'pow3': return ivs[0] ** 3
    if op == 'pow2': return ivs[0] ** 2
    if op == 'pe': return V.pe(ivs[1], ivs[0], ivs[2])
    if op == 'H': return V.H(ivs[0], ivs[1], 2, Dc('0.5'), Dc('0.25'))
    if op == 'lol': return V.lol(ivs[0])
    if op == 'lq': return V.lq(ivs[0])
    raise ValueError(op)


def rnd(rng, lo, hi):
    """a random 40-digit decimal in [lo, hi] (floats)."""
    v = lo + (hi - lo) * rng.random()
    with localcontext(HP):                                                     # DO: built in 90 digits, so the ends really have about 40 digits
        return Dc(repr(v)) + Dc(rng.randrange(10 ** 20)) * Dc(10) ** (int(math.floor(math.log10(abs(v) + 1e-300))) - 36)


def cases(rng, n):
    out = []
    for _ in range(n):
        a, b = sorted([rnd(rng, -50, 50), rnd(rng, -50, 50)]); c, d = sorted([rnd(rng, -50, 50), rnd(rng, -50, 50)])
        out.append(('+', [(a, b), (c, d)])); out.append(('-', [(a, b), (c, d)])); out.append(('*', [(a, b), (c, d)]))
        p, q = sorted([rnd(rng, 0.01, 50), rnd(rng, 0.01, 50)]); s = rng.choice([1, -1])
        out.append(('/', [(a, b), ((p, q) if s > 0 else (-q, -p))]))
        out.append(('exp', [sorted([rnd(rng, -200, 200), rnd(rng, -200, 200)])]))
        lo, hi = sorted([abs(rnd(rng, 1e-6, 1e6)), abs(rnd(rng, 1e-6, 1e6))]); out.append(('ln', [(lo, hi)])); out.append(('sqrt', [(lo, hi)]))
        out.append(('pow3', [(a, b)])); out.append(('pow2', [(a, b)]))
        k = rng.choice([0, 1, 2, 3, Dc('4.5'), 5]); cc = rng.choice([1, 2, Dc('0.5')])
        out.append(('pe', [sorted([abs(rnd(rng, 1e-3, 30)), abs(rnd(rng, 1e-3, 30))]), k, cc]))
        out.append(('pe', [(abs(rnd(rng, 50, 100)), Dc('Infinity')), k, cc]))
        x0 = abs(rnd(rng, 0.5, 3)); L0 = abs(rnd(rng, 1, 30)); out.append(('H', [(x0, x0 + abs(rnd(rng, 0, 1))), (L0, L0 + abs(rnd(rng, 0, 10)))]))
        out.append(('lol', [(abs(rnd(rng, 2.72, 100)), Dc('Infinity'))]))
        u0 = rnd(rng, -0.5, 5); out.append(('lq', [sorted([u0, u0 + abs(rnd(rng, 0, 2))])]))
        u1 = rnd(rng, -1e-7, 1e-7); out.append(('lq', [sorted([u1, u1 + abs(rnd(rng, 0, 1e-7))])]))
        out.append(('exp', [(a, a)])); out.append(('ln', [(lo, lo)])); out.append(('*', [(a, a), (c, c)]))           # point intervals
        out.append(('*', [(Dc(0), abs(b) + 1), (abs(c) + 1, Dc('Infinity'))]))                                         # an end at 0 times an infinite end
        # DO: subtraction with 40-digit ends on both sides, ends near 0, an infinite end, intervals crossing 0
        out.append(('-', [(a, a), (c, c)])); out.append(('-', [(c, d), (a, b)]))
        with localcontext(HP):
            tiny = Dc(10) ** -100000 * abs(rnd(rng, 1, 9)); tiny2 = Dc(10) ** -100000 * abs(rnd(rng, 1, 9))
        out.append(('-', [(tiny, tiny * 3), (tiny2, tiny2 * 2)])); out.append(('*', [(tiny.copy_negate(), tiny), (a, b)])); out.append(('+', [(tiny.copy_negate(), tiny2), (tiny, tiny * 2)]))
        out.append(('-', [(abs(a) + 1, Dc('Infinity')), (c, d)])); out.append(('*', [(-abs(a) - 1, abs(b) + 1), (-abs(c) - 1, abs(d) + 1)]))
        out.append(('-', [(-abs(a) - 1, abs(b) + 1), (-abs(c) - 1, abs(d) + 1)]))
    return out


def samples(rng, lo, hi):
    pts = [lo, hi] if hi.is_finite() else [lo, abs(lo) * 10 + 1, abs(lo) * Dc(10) ** 5 + 1, Dc(10) ** 30]
    if hi.is_finite() and hi > lo:
        with localcontext(HP):                                                 # DO: interior points in 90 digits (so they stay inside [lo, hi])
            for _ in range(3): pts.append(lo + (hi - lo) * Dc(repr(rng.random())))
    return [p for p in pts if p.is_finite()]


def check_cases(rng, cs):
    """(number of cases, number of failures, first failures)."""
    nf = 0; first = []
    for op, args in cs:
        ivs = []; extra = []
        for x in args:
            if isinstance(x, tuple) or isinstance(x, list): ivs.append(Iv(x[0], x[1]))
            else: extra.append(x)
        try:
            ivv = comp(op, ivs + extra) if op != 'pe' else V.pe(args[1], Iv(args[0][0], args[0][1]), args[2])
        except ValueError as e:
            nf += 1; first.append((op, 'ValueError ' + str(e)[:60])) if len(first) < 5 else None; continue
        sp = [samples(rng, iv.lo, iv.hi) for iv in ivs]
        bad = False
        if len(sp) == 1:
            for x in sp[0]:
                tv = true_val(op, [x] + extra if op != 'pe' else [x, args[1], args[2]])
                if not (ivv.lo <= tv <= ivv.hi): bad = True; break
        else:
            for x in sp[0]:
                for y in sp[1]:
                    tv = true_val(op, [x, y])
                    if not (ivv.lo <= tv <= ivv.hi): bad = True; break
                if bad: break
        if bad:
            nf += 1
            if len(first) < 5: first.append((op, [str(a)[:20] for a in (ivs[0].lo, ivs[0].hi)], [str(ivv.lo)[:24], str(ivv.hi)[:24]]))
    return len(cs), nf, first


def zero_div_raises():
    try:
        Iv(1) / Iv(-1, 2); return False
    except ZeroDivisionError:
        return True


def zero_div_case(rng):
    """the true 1/y for y = 0.001 in Y = [-1, 2] must lie in the computed 1/Y (it cannot for a finite interval)."""
    try:
        r = Iv(1) / Iv(-1, 2)
    except ZeroDivisionError:
        return 'raised'
    return 'caught' if not (r.lo <= Dc(1000) <= r.hi) else 'not caught'


def _old_neg(self): return Iv(-self.hi, -self.lo)                      # the pre-DO negation (verification/pre_DO/dl_interval.py): rounds in the current context


def _old_lq(U):
    U = Iv.c(U)
    def f(v):
        if v.is_infinite(): return Iv(0)
        with localcontext(V.CTX) as c2:
            if abs(v) < Dc('1e-6'):
                c2.prec = V.PREC + 10
                s_ = sum(((-v) ** k_ / (k_ + 1) for k_ in range(9)), Dc(0))
                return Iv(s_ - abs(s_) * V.WID - Dc('1e-50'), s_ + abs(s_) * V.WID + Dc('1e-50'))
            c2.prec = V.PREC + 30; r = (1 + v).ln() / v
        return Iv(r - abs(r) * V.WID, r + abs(r) * V.WID)                       # the pre-DO line: outside the 40-digit context
    return Iv(f(U.hi).lo, f(U.lo).hi)


def run_wrong(name, rng, cs):
    keep = (V.WID, V._dn, V._up, Iv.inv, Iv.__neg__, V.lq)
    try:
        if name == '(iv) the pre-DO implementation (negation and lq outside the context)': Iv.__neg__ = _old_neg; V.lq = _old_lq
        if name == '(i) no widening': V.WID = Dc(0)
        if name == '(ii) inward rounding': d, u = V._dn, V._up; V._dn, V._up = u, d
        if name == '(iii) division across 0 allowed':
            def inv(self):
                with localcontext(V.CTX):
                    a = 1 / self.hi if self.hi != 0 else Dc('Infinity'); b = 1 / self.lo if self.lo != 0 else Dc('-Infinity')
                    return Iv(V._dn(min(a, b)), V._up(max(a, b)))
            Iv.inv = inv
        n, nf, first = check_cases(rng, cs)
        zc = zero_div_case(rng)
    finally:
        V.WID, V._dn, V._up, Iv.inv, Iv.__neg__, V.lq = keep
    caught = nf > 0 or zc == 'caught'
    return {'cases': n, 'failing cases': nf, 'first failures': [str(f)[:160] for f in first], 'the case 1/[-1, 2]': zc, 'caught': caught}


def range_check():
    import dl_consts as LC
    keep = (V.CTX.traps[Overflow], V.CTX.traps[Underflow]); V.CTX.traps[Overflow] = True; V.CTX.traps[Underflow] = True
    out = {}
    try:
        for a, b in ((Dc('55.26'), Dc('55.26') * Dc('1.001')), (Dc('99900'), Dc('100000')), (Dc('999000'), Dc('1000000')), (Dc('1000000'), Dc('Infinity'))):
            try:
                o = LC.consts_iv(a, b); LC.checks(o); out['[%s, %s]' % (a, b)] = 'no overflow or underflow'
            except (Overflow, Underflow) as e:
                out['[%s, %s]' % (a, b)] = 'TRAPPED: ' + type(e).__name__
    finally:
        V.CTX.traps[Overflow], V.CTX.traps[Underflow] = keep
    return out


def monotone_EJ():
    worst = None; npc = 0; m = Dc(0)
    while m < 80:
        mu = Iv(m, m + Dc('0.01')); x = V.exp(-mu / 2); F = V.exp(V.pe(1, mu) / 32)
        d = -Dc('4.43') * x * (1 + Dc('4.43') * x) * F + (1 + Dc('4.43') * x) ** 2 * F * (1 - mu) * V.exp(-mu) / 32
        worst = d.hi if worst is None or d.hi > worst else worst; npc += 1; m += Dc('0.01')
    return {'pieces of [0, 80]': npc, 'largest upper bound of dE_J/dmu (must be < 0)': float(worst), 'ok': bool(worst < 0)}


def run(n=300, seed=7, save=True, fn='results/dn_ivtest.json'):
    t0 = time.time(); rng = random.Random(seed); cs = cases(rng, n)
    nc, nf, first = check_cases(random.Random(seed + 1), cs)
    out = {'(A) correct version': {'cases': nc, 'failing cases (must be 0)': nf, 'first failures': [str(f)[:160] for f in first], 'reciprocal of an interval containing 0 raises': zero_div_raises()}}
    out['(B) wrong versions'] = {w: run_wrong(w, random.Random(seed + 1), cs) for w in ('(i) no widening', '(ii) inward rounding', '(iii) division across 0 allowed',
                                                                                  '(iv) the pre-DO implementation (negation and lq outside the context)')}
    out['(C) dl_consts pieces with Overflow and Underflow trapped'] = range_check()
    out['(D) E_J decreasing'] = monotone_EJ()
    out['ok'] = bool(nf == 0 and out['(A) correct version']['reciprocal of an interval containing 0 raises'] and all(v['caught'] for v in out['(B) wrong versions'].values())
                     and all(v == 'no overflow or underflow' for v in out['(C) dl_consts pieces with Overflow and Underflow trapped'].values()) and out['(D) E_J decreasing']['ok'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open(fn, 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(); print(json.dumps({k: v for k, v in r.items()}, indent=1)[:3000])
