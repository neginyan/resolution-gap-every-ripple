"""Stage DQ (instruction 2.4, Gemini hint 1): the E_J step of ring 4 as a proof by hand -- every bound is monotone in mu, so mu >= 6 reduces to mu = 6.
Python 3.11 grammar.  The proof is in DQ_証明まとめ.md section 12.4; this file evaluates its SEVEN numbers at mu = 6 once in interval arithmetic (with the watch),
as a check of the hand arithmetic (the interval run of DM over 7,400 pieces is then no longer needed by the chain; it stays as a cross-check).
  With x = e^{-mu}, beta = x/16, c = e^{1/(2 mu)}, A = c (1 + beta/2), Bbar = B0(1/16, beta) = (1 + 1/4 + (1/32)^{1/(2 + beta)})^2:
  beta, mu beta (mu >= 1), c, A, Bbar all DECREASE in mu (Bbar: (1/32)^{1/(2+beta)} increases in beta).  So for every mu >= 6, with the values at mu0 = 6:
  (a) mu - mu_cap >= 6 - [A0 ln(32 Bbar0) + 16 c_CM c0 beta0]
  (b) y1 <= Y0 e^{-6},  Y0 := 2 Bbar0 sqrt(e) e^{mu0 beta0/2} + c_CM/16                         (Y := y1 e^mu <= Y0; DM's bound of Y)
  (c) e^{mu/2} (sqrt(y1) + (y1/2)^{1/(2+b')}) <= sqrt(Y0) + sqrt(Y0/2) e^{mu0 beta0/4}            (ln(Y/2)/(2 + beta) <= ln(Y0/2)/2 as Y0 > 2)
  (d) the added term <= 2 c_CM/(64 sqrt e)
  Needed: (a) > 0, (b) <= 1/16, (c) <= 4.43, (d) <= 6.2e-4.  POWER: 4.43 -> 4.40 and the lower end mu0 = 4 must fail.
-> results/dq_ej.json"""
import json, sys, os, time, functools, decimal
from decimal import Decimal as Dc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cm_const as CM
from dl_interval import Iv, exp, log, sqrt


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


@trapped
def at(mu0=Dc(6), c443=Dc('4.43')):
    mu = Iv(mu0); x = exp(-mu); beta = x / 16; e = exp(Iv(1)); c = exp(1 / (2 * mu)); A = c * (1 + beta / 2); CI = CM.c_cm_iv()
    t = exp(log(Iv(1) / 32) / (2 + beta)); Bb = (Iv(1) + Iv(1) / 4 + t) ** 2
    mucap = A * log(32 * Bb) + 16 * CI * c * beta
    Y0 = 2 * Bb * sqrt(e) * exp(mu * beta / 2) + CI / 16
    lhs = sqrt(Y0) + sqrt(Y0 / 2) * exp(mu * beta / 4)
    add = 2 * CI / (64 * sqrt(e))
    vals = {'beta0': beta, '(1/32)^{1/(2+beta0)}': t, 'Bbar0': Bb, 'A0': A, 'mu_cap0': mucap, 'Y0': Y0, 'y1 bound Y0 e^-6': Y0 * x, '(c) left side': lhs, '(d) added term': add}
    conds = {'(a) mu0 - mu_cap0 > 0': (mu - mucap).lo, '(b) 1/16 - Y0 e^{-mu0} >= 0': (Iv(1) / 16 - Y0 * x).lo, '(c) 4.43 - left side >= 0': (c443 - lhs).lo,
             '(d) 6.2e-4 - added term >= 0': (Dc('6.2e-4') - add).lo, 'Y0 > 2 (used in (c))': (Y0 - 2).lo}
    return {k: [float(v.lo), float(v.hi)] for k, v in vals.items()}, {k: float(v) for k, v in conds.items()}


def run(save=True):
    t0 = time.time(); v, c = at(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'values at mu = 6 (interval ends)': v, 'conditions (all must be > 0 / >= 0)': c}
    _, cw = at(c443=Dc('4.40')); _, c4 = at(mu0=Dc(4))
    out['POWER'] = {'4.43 -> 4.40 fails (c)': bool(cw['(c) 4.43 - left side >= 0'] < 0), 'lower end mu0 = 4 fails': bool(any(x < 0 for k, x in c4.items() if k != 'Y0 > 2 (used in (c))')),
                    'mu0 = 4: conditions': c4}
    try:
        dm = json.load(open('results/do_appendix.json'))
        out['the interval run of DM (DO version, 7,400 pieces): smallest values (cross-check)'] = dm.get('E_J from DI-1 (K), mu >= 6', dm).get('smallest values on [6, 80]') if isinstance(dm, dict) else None
    except Exception as ex: out['the interval run of DM (DO version, 7,400 pieces): smallest values (cross-check)'] = repr(ex)[:80]
    out['ok'] = bool(all(x > 0 for x in c.values()) and out['POWER']['4.43 -> 4.40 fails (c)'] and out['POWER']['lower end mu0 = 4 fails'])
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dq_ej.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(); print(json.dumps(r, indent=1)); sys.exit(0 if r['ok'] else 1)
