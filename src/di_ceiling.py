"""Stage DI 2.2: THE BRIGHTNESS CEILING IN CLOSED FORM (Lemma DI-1), and the numerical ceiling under the hypothesis (H) of Lemma DI-M.  Python 3.11 grammar.

THE INEQUALITY OF THE TABLE (cs_psi, cy_psi; Lemma CM-1 for s = c = 1, the corollary of Lemma DH-1 for s = sqrt(lam kappa_b), c = e^{1/(2 lam)}):
    P/2 <= U(P) = c [ (1 + b'/2) s E^ ln(2 B0(E^, b')/E^) + c_CM b' s ],   E0 = P/(2 mu),  E^ = min(E0/s, 1/16),  b' = b/s^2,
    B0(E, b') = (1 + sqrt(E) + (E/2)^{1/(2 + b')})^2   (increasing in E and in b'; h(E) = ln(2 B0/E) decreasing on (0, 1/16]: (S1) of cs_psi).

LEMMA DI-1 [proof].  Let mu > 0, b > 0, 0 < s <= 1, c >= 1 and let P > 0 satisfy P/2 <= U(P).  Put b' = b/s^2, A = c (1 + b'/2), Bbar = B0(1/16, b').
 (i)   If mu > mu_cap := A ln(32 Bbar) + 16 c_CM c b', then E0/s < 1/16.
       Proof.  If E0/s >= 1/16 then E^ = 1/16, so U = c s [(1 + b'/2)(1/16) ln(32 Bbar) + c_CM b'], while P/2 = mu E0 >= mu s/16.  Hence
       mu <= A ln(32 Bbar) + 16 c_CM c b' = mu_cap.
 (ii)  Let mu > mu_cap, y = E0/s (< 1/16).  Then  y <= 2 B0(y, b') e^{-mu/A} + c_CM b'/(1 + b'/2).
       Proof.  The inequality reads  mu y <= A y ln(2 B0(y, b')/y) + c_CM c b'.  Put Y = 2 B0(y, b') e^{-mu/A}.  If y <= Y there is nothing to show.
       Otherwise y = Y (1 + th), th > 0, and ln(2 B0/y) = mu/A - ln(1 + th), so  A y ln(1 + th) <= c_CM c b',  i.e.  Y (1 + th) ln(1 + th) <= c_CM c b'/A.
       As (1 + th) ln(1 + th) >= th:  Y th <= c_CM c b'/A = c_CM b'/(1 + b'/2), and y = Y + Y th.
       Consequence: with y1 := 2 Bbar e^{-mu/A} + c_CM b' and, if y1 <= 1/16, B1 := B0(y1, b') (else B1 := Bbar):  y <= y1 (B0(y) <= Bbar), so B0(y, b') <= B1 and
            P = 2 mu s y  <=  4 mu s B1 e^{-mu/A} + 2 c_CM mu b/(s (1 + b'/2)).                                                        (C)
 (iii) THE CORNER FORM.  Let mu >= 1/2, kappa <= kappa_b <= 1/mu, and take lam = mu in the corollary of Lemma DH-1: s = sqrt(mu kappa_b), c = e^{1/(2 mu)},
       b' = b/(mu kappa_b).  If mu > mu_cap:
            P <= 4 mu e^{-mu} sqrt(e mu kappa_b) (1 + eps),      1 + eps = B1 exp(b/(2 kappa_b)) + (2 c_CM/(4 sqrt e)) b e^{mu}/(mu kappa_b).         (K)
       Proof.  mu/A = mu e^{-1/(2 mu)}/(1 + b'/2) >= (mu - 1/2)(1 - b'/2) >= mu - 1/2 - mu b'/2  (e^{-x} >= 1 - x, 1/(1 + x) >= 1 - x, mu >= 1/2), so
       e^{-mu/A} <= e^{-mu} sqrt(e) e^{mu b'/2} = e^{-mu} sqrt(e) e^{b/(2 kappa_b)};  the second term of (C) is <= 2 c_CM mu b/sqrt(mu kappa_b) =
       4 mu e^{-mu} sqrt(e mu kappa_b) * 2 c_CM b e^{mu}/(4 sqrt(e) mu kappa_b).
       Size of eps: with kappa_b >= N b e^{mu}/mu (N >= 1): b' e^{mu} <= 1/N, b/(2 kappa_b) <= mu e^{-mu}/(2 N), y1 <= (2 sqrt(e) Bbar e^{mu b'/2} + c_CM/N) e^{-mu},
       so  eps <= B1 e^{mu e^{-mu}/(2N)} - 1 + 0.00986/N (2 c_CM/(4 sqrt e) = 0.009861)  ~  9 e^{-mu/2} + 0.01/N.
 (iv)  kappa NOT SMALL (Lemma CM-1 alone, s = c = 1, b' = b): for mu > mu_cap(b):  P <= 4 mu B1 e^{-mu/(1 + b/2)} + 2 c_CM mu b/(1 + b/2).
 (vi)  EVERY mu.  Without the condition mu > mu_cap:  P <= max( (C) with B1 := B0(min(y1, 1/16), b'),  s c [ (1 + b'/2) ln(32 Bbar)/8 + 2 c_CM b' ] ).
       Proof.  Either E0/s < 1/16, and then (ii) and (C) hold as proved (mu > mu_cap was used only to exclude the other case), or E0/s >= 1/16, and then
       P/2 <= U(P) = c s [(1 + b'/2)(1/16) ln(32 Bbar) + c_CM b'].
       (In the numerical comparison below (C) alone was never exceeded for mu < mu_cap either; the condition is what the proof of (i) uses, it is not
       shown to be necessary.)
 (v)   THE MAX FORM (for larger b).  Under (ii), for every t > 0:  y <= max( 2 B0(y, b') e^{-mu/A + t},  c_CM b'/((1 + b'/2) t) ).
       Proof.  If y > Y e^{t} then ln(1 + th) > t in the proof of (ii), so A y t < c_CM c b'.
The function U and the facts used ((S1); P/2 <= U(P) for the pairs (s, c)) are those of cs_psi/cy_psi and dh_ceiling; nothing else is used.

THE HYPOTHESIS (H) OF LEMMA DI-M:  P <= mu/8;  P/2 <= U(P; mu, b, 1, 1);  P/2 <= U(P; mu, b, sqrt(lam kappa_b), e^{1/(2 lam)}) for every lam > 0 and kappa_b >= kappa
with lam kappa_b <= 1.  lP_H gives the largest P allowed by a finite subset of (H) (so lP_H >= the true supremum under (H): a search with it is on the safe side):
kappa_b in {kappa, max(kappa, b e^t) (t in ENV_T), max(kappa, N b e^{mu}/mu) (N in NS)}, lam in {min(mu, 1/kappa_b) f (f in LFAC)} and {min(1/kappa_b, f) (f in LFIX)}.
(The first version had only the first set of lam: for mu << 1 its c = e^{1/(2 mu)} is useless and the search found false alarms there; results/di_first.)
-> results/di_ceiling.json"""
import json, math, sys, time
import cm_const as CM                                    # DN: the constant of Lemma CM-1, sqrt2/(16e) (CM_C0325=1: 0.0325)
from decimal import Decimal as Dc, getcontext
import numpy as np
import dh_main as M, cy_psi as PS

LN2 = math.log(2.0)
ENV_T = (-8.0, -4.0, 0.0, 4.0, 8.0)
NS = (1.0, 4.0, 16.0, 256.0)
LFAC = (1.0, 2.0 ** -0.5, 0.5)
LFIX = (1.0, 4.0, 16.0)                 # lam = min(1/kappa_b, these) too: for small mu the pair with lam ~ 1 is the sharp one (c = e^{1/(2 lam)} stays bounded)


def lB0(ly, bp):
    """log B0(y, b') from log y."""
    with np.errstate(all='ignore'): return 2 * np.log1p(np.exp(ly / 2) + np.exp((ly - LN2) / (2 + bp)))


def closed_C(lmu, lb, ls, lc, wrong=None):
    """(C) of Lemma DI-1: log of the closed bound of P for the pair (s, c); and the flags (mu > mu_cap, y1 <= 1/16).  Arrays, logarithms."""
    lmu, lb, ls, lc = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, ls, lc))
    with np.errstate(all='ignore'):
        mu = np.exp(lmu); bp = np.exp(np.minimum(lb - 2 * ls, 700.0)); c = np.exp(lc); A = c * (1 + bp / 2)
        lBbar = lB0(math.log(1 / 16), bp); mu_cap = A * (math.log(32) + lBbar) + 16 * CM.C_CM * c * bp
        ly1 = np.logaddexp(LN2 + lBbar - mu / A, math.log(CM.C_CM) + lb - 2 * ls)
        lB1 = np.where(ly1 <= math.log(1 / 16), lB0(np.minimum(ly1, math.log(1 / 16)), bp), lBbar)
        t1 = math.log(4) + lmu + ls + lB1 - mu / A; t2 = math.log(2 * CM.C_CM) + lmu + lb - ls - np.log1p(bp / 2)
        if wrong == 'B1': t1 = t1 - lB1
        if wrong == 'noadd': t2 = np.full(t1.shape, -np.inf)
    return np.logaddexp(t1, t2), mu > mu_cap, ly1 <= math.log(1 / 16)


def closed_K(lmu, lb, lkb, wrong=None):
    """(K) of Lemma DI-1: log of 4 mu e^{-mu} sqrt(e mu kappa_b) (1 + eps), log(1 + eps), and the range flags (mu >= 1/2, mu kappa_b <= 1, mu > mu_cap).
    wrong: 'noe' (sqrt(mu kappa_b) for sqrt(e mu kappa_b)), 'B1' (B1 := 1), 'noadd' (the added term dropped), 'nobp' (the factor exp(b/(2 kappa_b)) dropped)."""
    lmu, lb, lkb = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, lkb))
    with np.errstate(all='ignore'):
        mu = np.exp(lmu); ls = 0.5 * (lmu + lkb); lc = 1 / (2 * mu); bp = np.exp(np.minimum(lb - 2 * ls, 700.0)); A = np.exp(lc) * (1 + bp / 2)
        lBbar = lB0(math.log(1 / 16), bp); mu_cap = A * (math.log(32) + lBbar) + 16 * CM.C_CM * np.exp(lc) * bp
        ly1 = np.logaddexp(LN2 + lBbar - mu / A, math.log(CM.C_CM) + lb - 2 * ls)
        lB1 = np.where(ly1 <= math.log(1 / 16), lB0(np.minimum(ly1, math.log(1 / 16)), bp), lBbar)
        e1 = (0.0 if wrong == 'B1' else lB1) + (0.0 if wrong == 'nobp' else np.exp(np.minimum(lb - lkb, 700.0)) / 2)
        e2 = math.log(2 * CM.C_CM / (4 * math.sqrt(math.e))) + lb + mu - lmu - lkb
        leps = e1 if wrong == 'noadd' else np.logaddexp(e1, e2)
        main = math.log(4) + lmu - mu + 0.5 * ((0.0 if wrong == 'noe' else 1.0) + lmu + lkb)
    return main + leps, leps, (mu >= 0.5) & (lmu + lkb <= 1e-12) & (mu > mu_cap)


def pstar(lmu, lb, ls, lc, iters=80):
    """the largest P with P/2 <= U(P; mu, b, s, c), in logarithms (bisection in log P on [-1e7, log(mu/8) + 50]).
    The test P/2 <= U(P) is evaluated as  log mu - log c - log(1 + b'/2) - log ln(2 B0/E^) - log(1 + t2/t1) <= 0  where E^ = E0/s < 1/16 (log P cancels
    exactly: at mu ~ 1e6 the form log P - log 2 - log U of dh_main loses 1e-10 in a difference whose slope in log P is ~ 1/mu, i.e. ~1e-4 in P), and as
    dh_main._lU in the capped branch."""
    lmu, lb, ls, lc = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, ls, lc))
    lo = np.full(lmu.shape, -1e7); hi = np.log(2 * 0.0625) + lmu + 50; lbp = lb - 2 * ls
    with np.errstate(all='ignore'): bp = np.exp(np.minimum(lbp, 700.0)); l1b = np.log1p(bp / 2)
    for _ in range(iters):
        m = 0.5 * (lo + hi); lEh = m - LN2 - lmu - ls
        with np.errstate(all='ignore'):
            free = lEh < math.log(1 / 16); lE = np.minimum(lEh, math.log(1 / 16))
            lh = np.log(LN2 + lB0(lE, bp) - lE)                                         # log ln(2 B0/E^)
            t21 = math.log(CM.C_CM) + lbp - l1b - lE - lh                                # log of (0.0325 b')/((1 + b'/2) E^ ln(2 B0/E^))
            resid = lmu - lc - l1b - lh - np.logaddexp(0.0, t21)                        # <= 0  <=>  P/2 <= U(P)   (free branch)
            f = np.where(free, resid <= 0, m - LN2 <= M._lU(m, lmu, lb, ls, lc))
        lo = np.where(f, m, lo); hi = np.where(f, hi, m)
    return hi


def lP_H(lmu, lb, lk, parts=('apriori', 'CM1', 'DH1')):
    """log of the largest P allowed by the finite subset of (H) described above.  parts: which parts of (H) are used (the wrong versions of the search drop some)."""
    lmu, lb, lk = (np.asarray(v, float) for v in np.broadcast_arrays(lmu, lb, lk))
    best = np.full(lmu.shape, np.inf)
    if 'apriori' in parts: best = np.minimum(best, lmu - math.log(8))
    if 'CM1' in parts: best = np.minimum(best, pstar(lmu, lb, np.zeros(lmu.shape), np.zeros(lmu.shape)))
    if 'DH1' in parts:
        with np.errstate(all='ignore'):
            kbs = [lk] + [np.maximum(lk, lb + t) for t in ENV_T] + [np.maximum(lk, math.log(N) + lb + np.exp(lmu) - lmu) for N in NS]
        for lkb in kbs:
            llam0 = np.minimum(lmu, -lkb)
            for llam in [llam0 + math.log(f) for f in LFAC] + [np.minimum(math.log(f), -lkb) for f in LFIX]:
                ok = np.isfinite(lkb) & np.isfinite(llam)
                lp = pstar(lmu, lb, 0.5 * (llam + np.where(ok, lkb, 0.0)), np.exp(-np.where(ok, llam, 0.0)) / 2)
                best = np.where(ok, np.minimum(best, lp), best)
    return best


def check_60():
    """60 digits: (a) the identity of (ii): for y = Y (1 + th):  mu y - A y ln(2 B0/y) = A y ln(1 + th);  (b) (mu - 1/2)(1 - b'/2) - (mu - 1/2 - mu b'/2) = b'/4;
    (c) the second term of (C) against (K): 2 c_CM mu b/sqrt(mu kappa_b) = 4 mu e^{-mu} sqrt(e mu kappa_b) * 2 c_CM b e^{mu}/(4 sqrt(e) mu kappa_b)."""
    getcontext().prec = 80; worst = Dc(0)
    for mu, A, B0v, th in ((Dc('13.8'), Dc('1.04'), Dc('1.01'), Dc('0.3')), (Dc('250'), Dc('1.002'), Dc('1.0000001'), Dc('7')), (Dc('5.5'), Dc('1.2'), Dc('1.3'), Dc('0.001'))):
        Y = 2 * B0v * (-mu / A).exp(); y = Y * (1 + th)
        worst = max(worst, abs((mu * y - A * y * (2 * B0v / y).ln()) / (A * y * (1 + th).ln()) - 1))
    for mu, bp in ((Dc('13.8'), Dc('0.001')), (Dc('0.7'), Dc('0.3'))):
        worst = max(worst, abs(((mu - Dc('0.5')) * (1 - bp / 2) - (mu - Dc('0.5') - mu * bp / 2)) / (bp / 4) - 1))
    for mu, b, kb in ((Dc('13.8'), Dc('1e-20'), Dc('1e-3')), (Dc('240'), Dc('1e-400'), Dc('1e-9'))):
        lhs = 2 * Dc(CM.C_CM_DEC) * mu * b / (mu * kb).sqrt(); e = Dc(1).exp()
        rhs = 4 * mu * (-mu).exp() * (e * mu * kb).sqrt() * 2 * Dc(CM.C_CM_DEC) * b * mu.exp() / (4 * e.sqrt() * mu * kb)
        worst = max(worst, abs(lhs / rhs - 1))
    return float(worst)


def run(n=40000, save=True):
    t0 = time.time(); rng = np.random.default_rng(20261113); out = {'60-digit check (the identities of the proof): largest error': check_60()}
    def sample(kind, n):
        if kind == 'inside':                       # mu in [5, 1e6], b <= e^{-mu}, kappa_b in [b e^{mu}/mu, 1/mu]
            lmu = rng.uniform(math.log(5.0), math.log(1e6), n); mu = np.exp(lmu); lb = -mu - rng.uniform(0, 80, n) * rng.choice([1.0, 0.05 * 1, 30.0], n)
            lo = lb + mu - lmu; lkb = lo + rng.uniform(0, 1, n) ** 2 * (-lmu - lo)
        elif kind == 'edge':                       # next to mu_cap, to kappa_b = b e^{mu}/mu and to mu kappa_b = 1
            lmu = np.log(rng.uniform(4.3, 6.0, n)); mu = np.exp(lmu); lb = -mu - rng.uniform(0, 12, n); lo = lb + mu - lmu
            w = rng.integers(0, 3, n); lkb = np.where(w == 0, lo + rng.uniform(0, 0.1, n), np.where(w == 1, -lmu - rng.uniform(0, 0.1, n), lo + rng.uniform(0, 1, n) * (-lmu - lo)))
        elif kind == 'wide':                       # the formula (K) wherever its range flags hold: b' e^{mu} not small (eps large), any b
            lmu = rng.uniform(math.log(0.5), math.log(3000.0), n); mu = np.exp(lmu); lb = rng.uniform(-3 * mu - 40, math.log(0.5), n); lkb = -lmu - rng.uniform(0, 1, n) ** 2 * 200
        else:                                      # outside: mu below mu_cap
            lmu = np.log(rng.uniform(0.5, 4.2, n)); mu = np.exp(lmu); lb = -mu - rng.uniform(0, 40, n); lo = lb + mu - lmu; lkb = lo + rng.uniform(0, 1, n) * (-lmu - lo)
        return lmu, lb, lkb
    rows = {}
    for kind in ('inside', 'edge', 'wide', 'outside'):
        lmu, lb, lkb = sample(kind, n); mu = np.exp(lmu)
        num = pstar(lmu, lb, 0.5 * (lmu + lkb), 1 / (2 * mu))                                  # the same pair (s, c) = (sqrt(mu kappa_b), e^{1/(2 mu)})
        cl, leps, ok = closed_K(lmu, lb, lkb); d = cl - num
        r = {'states': int(n), 'states with the range flags (mu >= 1/2, mu kappa_b <= 1, mu > mu_cap)': int(ok.sum())}
        if ok.any():
            r.update({'smallest log(closed/numerical) where the flags hold (must be >= 0)': float(d[ok].min()), 'median': float(np.median(d[ok])), 'largest': float(d[ok].max()),
                      'largest eps where the flags hold': float(np.expm1(leps[ok]).max()), 'median eps': float(np.median(np.expm1(leps[ok])))})
            r['wrong versions: states with closed < numerical (flags hold)'] = {w: int(np.sum(closed_K(lmu, lb, lkb, wrong=w)[0][ok] < num[ok] - 1e-12)) for w in ('noe', 'B1', 'noadd', 'nobp')}
        if (~ok).any(): r['outside the flags: states with closed < numerical'] = int(np.sum(d[~ok] < -1e-12)); r['outside the flags: smallest log(closed/numerical)'] = float(d[~ok].min())
        # (C) for a general pair (s, c): s in (0, 1], c in [1, e^2]
        ls = -rng.uniform(0, 1, n) ** 2 * 30; lc = rng.uniform(0, 1, n) ** 3 * 2; numC = pstar(lmu, lb, ls, lc); clC, f1, f2 = closed_C(lmu, lb, ls, lc); okC = f1
        if okC.any(): r['(C), general (s, c): states with mu > mu_cap'] = int(okC.sum()); r['(C): smallest log(closed/numerical) (must be >= 0)'] = float((clC - numC)[okC].min())
        rows[kind] = r; print(kind, json.dumps(r), flush=True)
    out['closed form against the numerical solution of the same inequality'] = rows
    # the closed form against the table's Psi_3 (list of lambda) and against lP_H, at corner-like states
    n2 = 4000; lmu = rng.uniform(math.log(8.0), math.log(2.5e5), n2); mu = np.exp(lmu); lb = -4 * mu + rng.uniform(-20, 20, n2); lk = -lmu - 1 - rng.uniform(0, 30, n2)
    lkb = np.maximum(lk, math.log(16.0) + lb + mu - lmu); cl, leps, ok = closed_K(lmu, lb, lkb)
    psi3 = M.lP_log(lmu, lb, lk, 'JEN'); lph = lP_H(lmu, lb, lk)
    out['closed form (K) with kappa_b = max(kappa, 16 b e^mu/mu) against the table\'s Psi_3 and against lP_H (corner-like states)'] = {
        'states': n2, 'flags hold': int(ok.sum()), 'log(closed/Psi_3): smallest, median, largest': [float((cl - psi3).min()), float(np.median(cl - psi3)), float((cl - psi3).max())],
        'log(closed/lP_H): smallest, median, largest': [float((cl - lph).min()), float(np.median(cl - lph)), float((cl - lph).max())],
        'log(lP_H/Psi_3): smallest, largest': [float((lph - psi3).min()), float((lph - psi3).max())], 'largest eps': float(np.expm1(leps).max())}
    print(json.dumps(out[list(out)[-1]]), flush=True)
    R = out['closed form against the numerical solution of the same inequality']
    out['ok'] = bool(out['60-digit check (the identities of the proof): largest error'] < 1e-60 and
                     all(r.get('smallest log(closed/numerical) where the flags hold (must be >= 0)', 0.0) >= -1e-7 and r.get('(C): smallest log(closed/numerical) (must be >= 0)', 0.0) >= -1e-7 for r in R.values())
                     and all(sum(r.get('wrong versions: states with closed < numerical (flags hold)', {}).get(w, 0) for r in R.values()) > 0 for w in ('noe', 'B1', 'noadd', 'nobp')))
    out['wrong versions caught (states, all families)'] = {w: int(sum(r.get('wrong versions: states with closed < numerical (flags hold)', {}).get(w, 0) for r in R.values())) for w in ('noe', 'B1', 'noadd', 'nobp')}
    out['outside the range (mu < mu_cap): states where (K) is below the numerical solution'] = int(R['outside'].get('outside the flags: states with closed < numerical', 0))
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/di_ceiling.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    o = run(); print({k: v for k, v in o.items() if not isinstance(v, dict)})
