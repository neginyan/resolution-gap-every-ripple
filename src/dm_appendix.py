"""Stage DM: the one step of the appendix lemmas that the reports had only on a grid -- the constant E_J of (F4) from Lemma DI-1 (K), in interval arithmetic.
Python 3.11 grammar.  DO_証明まとめ.md appendix A.4.  [computer-assisted proof]
Setting (DI-1 (iii) with lam = mu: s = sqrt(mu kappa_b), c = e^{1/(2 mu)}, b' = b/(mu kappa_b)) and kappa_b >= 16 b e^mu/mu, so b' <= beta := e^{-mu}/16.
  (a) mu > mu_cap = A ln(32 Bbar) + 16 c_CM c b'  with A = c (1 + b'/2) <= e^{1/(2 mu)} (1 + beta/2), Bbar = B0(1/16, b') <= B0(1/16, beta)    (B0 increases in b');
  (b) y1 = 2 Bbar e^{-mu/A} + c_CM b' <= 1/16, using e^{-mu/A} <= sqrt(e) e^{mu b'/2} e^{-mu} (proof of DI-1 (iii), mu >= 1/2);
  (c) sqrt(B1) = 1 + sqrt(y1) + (y1/2)^{1/(2 + b')} <= 1 + 4.43 e^{-mu/2}:  with Y := y1 e^mu <= 2 B0(1/16, beta) sqrt(e) e^{mu beta/2} + c_CM/16 (beta e^mu = 1/16),
      e^{mu/2} sqrt(y1) <= sqrt(Y) and e^{mu/2} (y1/2)^{1/(2+b')} <= exp(ln(Y/2)/(2 + beta) + mu beta/(2 (2 + beta)))   ((y/2)^{1/(2+b')} increases in b' as y/2 < 1;
      mu/2 - mu/(2 + beta) = mu beta/(2 (2 + beta)));
  (d) the added term (2 c_CM/(4 sqrt e)) b e^mu/(mu kappa_b) <= 2 c_CM/(64 sqrt e) <= 6.2e-4;  and B1 e^{b/(2 kappa_b)} <= (1 + 4.43 e^{-mu/2})^2 exp(mu e^{-mu}/32)
      (b/(2 kappa_b) = mu b'/2 <= mu e^{-mu}/32).  Together:  1 + eps <= E_J(mu) for every mu >= 6.
mu in [6, 80] in pieces of 0.01 and [80, inf) in one piece.  POWER: 4.43 -> 4.40, beta = e^{-mu} (N = 1 instead of 16), the lower end mu = 4: each must fail.
-> results/dm_appendix.json"""
import json, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
from decimal import Decimal as Dc
import dl_interval as V
from dl_interval import Iv, exp, log, sqrt, pe


def B0(E, bp): return (1 + sqrt(E) + exp(log(E / 2) / (2 + bp))) ** 2


def piece(m_lo, m_hi, c443=Dc('4.43'), N=16):
    mu = Iv(m_lo, m_hi); x = exp(-mu); beta = x / N; e = exp(Iv(1))
    c = exp(1 / (2 * mu)); A = c * (1 + beta / 2); Bb = B0(Iv(1) / 16, beta)
    CI = CM.c_cm_iv(); mucap = A * log(32 * Bb) + 16 * CI * c * beta
    mub = pe(1, mu) / N                                                               # mu beta
    Y = 2 * Bb * sqrt(e) * exp(mub / 2) + CI / N
    y1 = Y * x
    lhs = sqrt(Y) + exp(log(Y / 2) / (2 + beta) + mub / (2 * (2 + beta)))
    add = 2 * CI / (4 * sqrt(e)) / N
    return {'(a) mu - mu_cap > 0': (mu - mucap).lo, '(b) 1/16 - y1 >= 0': (Iv(1) / 16 - y1).lo, '(c) 4.43 - e^{mu/2}(sqrt(y1) + (y1/2)^{1/(2+b\')}) >= 0': (c443 - lhs).lo,
            '(d) 6.2e-4 - added term >= 0': (Dc('6.2e-4') - add).lo}


def run_all(c443=Dc('4.43'), N=16, mu0=Dc(6), step=Dc('0.01'), save=False, fn='results/dm_appendix.json'):
    t0 = time.time(); worst = {}; n = 0; bad = 0; m = mu0
    while m < 80:
        r = piece(m, min(m + step, Dc(80)), c443, N); n += 1; bad += any(v < 0 for v in r.values())
        for k, v in r.items(): worst[k] = v if k not in worst or v < worst[k] else worst[k]
        m += step
    rt = piece(Dc(80), Dc('Infinity'), c443, N)
    out = {'pieces of [%s, 80]' % mu0: n, 'failing pieces': bad, 'smallest values on [%s, 80]' % mu0: {k: float(v) for k, v in worst.items()},
           'tail [80, inf)': {k: float(v) for k, v in rt.items()}, 'tail fails': any(v < 0 for v in rt.values()), 'seconds': time.time() - t0}
    out['ok'] = bad == 0 and not out['tail fails']
    return out


def run(save=True, fn='results/dm_appendix.json'):
    out = {'E_J from DI-1 (K), mu >= 6': run_all()}
    out['power'] = {'4.43 -> 4.40': run_all(c443=Dc('4.40'))['ok'] is False, 'N = 1 (beta = e^{-mu})': run_all(N=1)['ok'] is False,
                    'lower end mu = 4': run_all(mu0=Dc(4))['ok'] is False}
    out['ok'] = out['E_J from DI-1 (K), mu >= 6']['ok'] and all(out['power'].values())
    if save: json.dump(out, open(fn, 'w'), indent=1)
    return out


if __name__ == '__main__':
    r = run(); print(r['ok'], r['E_J from DI-1 (K), mu >= 6']['smallest values on [6, 80]'], r['E_J from DI-1 (K), mu >= 6']['tail [80, inf)'], r['power'])
