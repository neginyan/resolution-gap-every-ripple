"""Stage CZ 2.3: INDEPENDENT CHECK OF THE NEW TABLE LINES.  The direct lemma (Lemmas CZ-1 ... CZ-5 with the class constants eta = 1/ell, Qb, U1) is
written out here once more, in the physical variables and in 50-digit decimals, as Phi = Num - gamma sigma den at one state
(ell, mu, b, r, kappa, P, A).  The table cz_cells.py at the zero-width box of the same state must be a lower bound of Phi/sigma at every A
(the table uses cruder forms), for each of the options Tz, Bz, Fz, POINTWISE in a' = 4 r A/sigma (the table's aggregates L, H, C, S, M of the option,
evaluated at a'; for Tz, Bz the better of the two branches):
    L a' + H/(a' + sigma) + C - S sqrt(a') - M/sqrt(a')  <=  Phi_option(A)/sigma     for every A in [4 sigma^3, 1].
A transcription error that makes a table line too small shows up as table_raw > Phi/sigma.  POWER: the deliberately wrong tables ZOPT['W'] =
'ring0' (the ring loss dropped), 'cK2' (chirp gain doubled), 'M40' (the Xi line dropped), 'hneg0' (the R_theta, t_rho line dropped), 'A1w0' (A1w dropped)
must all be caught.  (A1v and the 2 delta of the pair are never as large as 1e-9 of the total at any a': they cannot be tested this way; they are tested
against the exact pieces in cz_search.py and cz_pair.py.)
-> results/cz_point.json"""
import json, math, sys
from decimal import Decimal as Dc, getcontext
import numpy as np
import cz_cells as Z
getcontext().prec = 50
QB = Dc('0.25'); PI = Dc('3.14159265358979323846264338327950288419716939937510'); C2 = Dc('0.184'); M4 = Dc('2.07')


def dexp(x): return Dc(x).exp()


def dsqrt(x): return Dc(x).sqrt()


def om(x):
    """1 - e^{-x}, without cancellation for small x."""
    x = Dc(x)
    return x * (1 - x / 2 + x * x / 6 - x ** 3 / 24) if abs(x) < Dc('1e-12') else 1 - (-x).exp()


def lm1(y):
    """-ln(1 - y), without cancellation for small y."""
    y = Dc(y)
    return y + y * y / 2 + y ** 3 / 3 if abs(y) < Dc('1e-12') else -(1 - y).ln()


def point(ell, mu, lB, lr, kap, P, lA, opt):
    """Phi/sigma of the direct lemma for the option (Tz, Bz, Fz); returns Decimal.  SAND convention (factors inside, gamma = (1 + 2.5e-4)/sqrt(ell)).
    b = e^{lB} sigma^2, r = e^{lr}, A = e^{lA} (logarithms: the values underflow in floats for large ell)."""
    ell, mu, lB, lr, kap, P, lA = (Dc(repr(float(t))) for t in (ell, mu, lB, lr, kap, P, lA))
    sig = dexp(-ell); b = dexp(lB) * sig ** 2; r = dexp(lr); A = dexp(lA)
    eta = 1 / ell; s2 = sig ** 2 / A; L2 = s2 / r; s = dsqrt(s2); L = dsqrt(L2)
    U1 = QB * dsqrt(2 * ell + Dc('3.1')) + Dc('1e-6')
    y = (1 - b) ** 2 * sig ** 2 / (2 * b); dl = 2 * b / (1 - b)
    kE = dsqrt(r / (1 + r)); seE = s2 / (1 + r); se2 = s2 / (2 + r); gs = dsqrt(r / (2 + r))
    W = gs * P / 2; E0 = P / (2 * mu); D0 = E0 * gs * se2 / s2 ** 2
    K2 = 8 * ell + 100; K = dsqrt(K2); z0 = K * dsqrt(y)
    phiK = dexp(-K2 / 2) / dsqrt(2 * PI); QK = phiK / K; T2K = 2 * phiK * (K + 1 / K)          # upper bounds of Q(K), T_2(K)
    xi = sig * U1 / (1 - QB); zeta = sig ** 2 * eta * dexp(Dc('-0.5')) / (s * (1 - eta))
    # ---- w-branch (Lemma R_theta's A_w part, with the ring average by Lemma CZ-4)
    Lam1 = eta * kE * (2 + r) / ((1 + r) * L2)
    J2a = (1 / L2) * (1 + eta * kE * r / (1 + r)) + 2 * eta * kE * seE / (L2 * s2)
    ring = (K2 * D0 + eta ** 2 * T2K * gs * se2 / s2 ** 2) / (1 - eta)
    Jup = J2a + D0 / (1 - eta)
    M4w = 3 * (1 + eta * kE * r ** 2 / (1 + r) ** 2) + 6 * eta * kE * r / (1 + r) ** 2 + 3 * se2 * D0 / (1 - eta)
    twoAw = 2 * sig ** 2 * (1 / L2 + D0 / (1 + eta) - Lam1) - (sig ** 4 * (1 - b) ** 2 / (4 * b) * (J2a + ring) + sig ** 2 / 2 * M4w
                                                                 + sig ** 2 * Dc('1.5') * ((xi ** 2 + zeta ** 2) * Jup + sig ** 4 / L2 ** 2 * M4w))
    # ---- v-branch, direct form
    Psi0 = om(y / 2 + L2 / 4 + lm1(y)) if y < Dc('1e-12') else 1 - (1 - y) * dexp(-y / 2 - L2 / 4); cL = C2 + y
    M0 = b * Psi0 - kE * om(seE / 4) * b * (eta + C2) - kE * b * y * QB * M4
    A1 = b * sig * kE * dsqrt(15 * y * P) / 2 + b * sig ** 2 * (1 / (dsqrt(PI) * L) + eta * kE / dsqrt(PI * seE))
    A2 = b * (sig ** 2 * kap * W / (2 * (1 - eta)) + sig ** 4 * ((1 + eta * kE * r / (1 + r)) / L2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta))))
    B1w = 2 * sig ** 2 * b * cL * kE * dsqrt(seE / PI) / L2 + dsqrt(Dc(2)) * b * sig ** 2 * eta ** 2 * (1 + y / 2) * gs * dsqrt(2 * se2 / PI) / (s2 * (1 - eta))
    B2 = dsqrt(b) * sig ** 2 * U1 * dsqrt(kap) * W / (1 - eta) ** 2 + sig ** 4 * dsqrt(2 * b * P) * (kE * seE / L2 ** 2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta) ** 2))
    twoN = M0 - A1 - A2 - B1w - B2
    if opt == 'Fz':
        twoN -= sig ** 2 * (1 - b) * kap * W / (1 - eta)
    else:
        cd = Dc('0.5') - dl - z0 ** 2 / 24
        main = (W / (1 + eta)) * (1 - z0 ** 2 / 2) * om(se2 / 4)
        if opt == 'Tz':
            if cd <= 0: return None
            main += cd * y * (kap * W - gs * U1 ** 2 * T2K) / (1 + eta)
        else:
            main += (cd * y * kap * W / (1 - eta) if cd < 0 else 0)
        tails = (U1 ** 2 * gs / (1 - eta)) * (4 * QK + 2 * dl * dsqrt(y) * phiK)
        cv = sig * U1 / (dsqrt(Dc(2)) * (1 - QB)); c0 = cv + zeta / dsqrt(Dc(2)); c1 = sig ** 2 / (dsqrt(Dc(2)) * L2)
        FrB2 = (W / (1 - eta)) * (c0 + sig ** 2 * dsqrt(se2 / PI) / L2)
        FrB1 = (W / (1 - eta)) * ((c0 * dsqrt(2 * se2 / PI) + c1 * se2) / dsqrt(Dc(2)) + c0 ** 2 + c1 ** 2 * se2) + dsqrt(y * kap) * FrB2
        twoN += main - tails - min(FrB2, FrB1)
    den = b * (1 + eta * kE) + W / (1 - eta) + C2 * b * kE + sig ** 2 * (1 / L2 + D0 / (1 - eta) + Lam1)
    gam = (1 + Dc('2.5e-4')) / dsqrt(ell)
    return (twoAw + twoN / 2 - gam * sig * den) / sig


def table_aggregates(ell, mu, lB, lr, kap, P, opt):
    """the table's aggregates (sums of the lines per type, at the zero-width box) for the option: o2 (branch B2 / the only branch) and o1 (branch B1)."""
    X = np.array([[math.log(mu), math.log(mu), lr, lr, lB, lB, math.log(kap), math.log(kap), ell, ell]])
    lG = np.array([math.log(P) + 0.5 * (lr - math.log(2 + math.exp(lr)))])
    with np.errstate(all='ignore'):
        if opt == 'Fz': return Z.terms_cell(X, 0.0, True, lGc=lG, opts=(opt,), lGref=lG, debug='Fz'), None
        o2 = Z.terms_cell(X, 0.0, True, lGc=lG, opts=(opt,), lGref=lG, debug=opt)
        o1 = Z.terms_cell(X, 0.0, True, lGc=lG, opts=(opt,), lGref=lG, debug=opt + '1')
    return o2, o1


def ld2dec(v): return Dc(np.format_float_scientific(np.longdouble(v), precision=25, unique=False))


def table_at(o, ell, lr, lA):
    """the table's bound of Phi/sigma at a' = 4 r A/sigma from the aggregates: L a' + H/(a' + sigma) + C - S sqrt(a') - M/sqrt(a')  (decimal)."""
    ell, lr, lA = (Dc(repr(float(t))) for t in (ell, lr, lA))
    sig = dexp(-ell); ap = 4 * dexp(lr + lA) / sig
    L_, H_, C_, S_, M_ = (ld2dec(o[k][0]) for k in 'LHCSM')
    return L_ * ap + H_ / (ap + sig) + C_ + S_ * dsqrt(ap) + M_ / dsqrt(ap)


LINE_NAMES = ('ring T2', 'Xi', 'A1v', 'A1w', 'A2 kappa', 'A2 J2a', 'A2 J2b', 'B1w a', 'B1w b', 'B2 a', 'B2 b', 'tails')


def lemma_lines(ell, mu, lB, lr, kap, P, lA):
    """the halves of the bounds of Lemma CZ-2/4/5 that the z-lines of the table transcribe, in Num units, at one state (decimal); order = LINE_NAMES."""
    ell, mu, lB, lr, kap, P, lA = (Dc(repr(float(t))) for t in (ell, mu, lB, lr, kap, P, lA))
    sig = dexp(-ell); b = dexp(lB) * sig ** 2; r = dexp(lr); A = dexp(lA); eta = 1 / ell; s2 = sig ** 2 / A; L2 = s2 / r; s = dsqrt(s2); L = dsqrt(L2)
    U1 = QB * dsqrt(2 * ell + Dc('3.1')) + Dc('1e-6'); y = (1 - b) ** 2 * sig ** 2 / (2 * b); dl = 2 * b / (1 - b)
    kE = dsqrt(r / (1 + r)); seE = s2 / (1 + r); se2 = s2 / (2 + r); gs = dsqrt(r / (2 + r)); W = gs * P / 2
    K2 = 8 * ell + 100; K = dsqrt(K2); phiK = dexp(-K2 / 2) / dsqrt(2 * PI); T2K = 2 * phiK * (K + 1 / K); cL = C2 + y
    return [sig ** 4 * (1 - b) ** 2 / (4 * b) * eta ** 2 * T2K * gs * se2 / (s2 ** 2 * (1 - eta)),
            kE * b * y * QB * M4 / 2,
            b * sig * kE * dsqrt(15 * y * P) / 4,
            b * sig ** 2 * (1 / (dsqrt(PI) * L) + eta * kE / dsqrt(PI * seE)) / 2,
            b * sig ** 2 * kap * W / (4 * (1 - eta)),
            b * sig ** 4 * (1 + eta * kE * r / (1 + r)) / (2 * L2),
            b * sig ** 4 * eta ** 2 * gs * se2 / (2 * s2 ** 2 * (1 - eta)),
            sig ** 2 * b * cL * kE * dsqrt(seE / PI) / L2,
            b * sig ** 2 * eta ** 2 * (1 + y / 2) * gs * dsqrt(se2 / PI) / (s2 * (1 - eta)),
            dsqrt(b) * sig ** 2 * U1 * dsqrt(kap) * W / (2 * (1 - eta) ** 2),
            sig ** 4 * dsqrt(2 * b * P) * (kE * seE / L2 ** 2 + eta ** 2 * gs * se2 / (s2 ** 2 * (1 - eta) ** 2)) / 2,
            (U1 ** 2 * gs / (1 - eta)) * (4 * phiK / K + 2 * dl * dsqrt(y) * phiK + y * phiK * (K + 1 / K)) / 2]


def table_lines(ell, mu, lB, lr, kap, P, lA):
    """the same lines as the table has them (the negative lines of the group 'z', in the order they are added), in Num units at a' = 4 r A/sigma."""
    X = np.array([[math.log(mu), math.log(mu), lr, lr, lB, lB, math.log(kap), math.log(kap), ell, ell]])
    lG = np.array([math.log(P) + 0.5 * (lr - math.log(2 + math.exp(lr)))])
    cap = {}; Z.DIAG['CAPTURE'] = cap
    try:
        with np.errstate(all='ignore'): Z.terms_cell(X, 0.0, True, lGc=lG, opts=('Fz',), lGref=lG)
    finally:
        Z.DIAG['CAPTURE'] = None
    sig = dexp(-Dc(repr(ell))); ap = 4 * dexp(Dc(repr(lr)) + Dc(repr(float(lA)))) / sig
    ty = {'L': ap, 'C': Dc(1), 'S': dsqrt(ap), 'M': 1 / dsqrt(ap), 'H': 1 / (ap + sig)}
    out = []
    for line, t, p, c, grp in cap['terms']:
        if grp == 'z' and float(c[0]) <= 0 and not (t == 'C' and p == 2.0 and False): out.append(-ld2dec(c[0]) * sig ** Dc(repr(float(p))) * ty[t])
    return out


def line_check(n=60, seed=11, wrong=None):
    """every negative z-line of the table against the lemma's piece: 1 <= table/lemma <= 1/(1-b)^2 (1 + 1e-9) (the only slack at a zero-width box is
    (1-b) <= 1; the two Gaussian-tail lines are cruder: any ratio >= 1).  Returns (number of bad lines, per-line min and max ratio)."""
    rng = np.random.default_rng(seed); bad = []; mm = {k: [math.inf, 0.0] for k in LINE_NAMES}
    Z.ZOPT['W'] = wrong
    try:
        for i in range(n):
            ell = float(rng.choice([4.0, 6.0, 55.26, 300.0, 960.8])); mu, lB, lr, kap, P = sample(rng, ell)
            lA = float(rng.uniform(math.log(4.0) - 3 * ell, 0.0))
            tl = table_lines(ell, mu, lB, lr, kap, P, lA); ll = lemma_lines(ell, mu, lB, lr, kap, P, lA)
            if len(tl) != len(ll): bad.append({'ell': ell, 'reason': 'number of lines', 'table': len(tl), 'lemma': len(ll)}); continue
            b = math.exp(lB - 2 * ell)
            for nm, t, l in zip(LINE_NAMES, tl, ll):
                if l == 0: continue
                rt = float(t / l); mm[nm][0] = min(mm[nm][0], rt); mm[nm][1] = max(mm[nm][1], rt)
                hi = math.inf if nm in ('tails', 'ring T2') else (1 + 1e-9) / (1 - b) ** 2          # these two use a cruder constant for the Gaussian tail
                if not (1 - 1e-12 <= rt <= hi): bad.append({'ell': ell, 'line': nm, 'ratio': rt, 'state': [mu, lB, lr, kap, P, lA]})
    finally:
        Z.ZOPT['W'] = None
    return bad, mm


def sample(rng, ell):
    if ell < 20:                                                        # the transcription pass (large sigma: every line is visible)
        b = rng.uniform(math.log(300.0), math.log(0.49) + 2 * ell); r = rng.uniform(math.log(1e-4), math.log(0.25))      # beta >= 300: z0^2 = K^2 y <= 1 (the lemma's range)
        mu = math.exp(rng.uniform(math.log(1e-2), math.log(30.0))); kap = math.exp(rng.uniform(math.log(1e-3), math.log(1e3)))
        return mu, b, r, kap, 2 * mu * 0.0625 * math.exp(rng.uniform(-6, 0))
    b = rng.uniform(math.log(2.6e10), math.log(0.49) + 2 * ell)          # log beta
    r = rng.uniform(-3 * ell, math.log(0.25))                           # log r
    mu = math.exp(rng.uniform(math.log(1e-3), math.log(4 * ell)))
    kap = math.exp(rng.uniform(math.log(1e-6), math.log(1e6)))
    P = 2 * mu * 0.0625 * math.exp(rng.uniform(-40, 0))
    return mu, b, r, kap, P


def run(n=400, seed=3):
    rng = np.random.default_rng(seed); out = {'states': 0, 'violations': [], 'worst_gap': None, 'none_Tz': 0}
    def one(ell, st, opts=('Tz', 'Bz', 'Fz')):
        mu, b, r, kap, P = st; bad = []; gaps = []
        for opt in opts:
            o2, o1 = table_aggregates(ell, mu, b, r, kap, P, opt)
            for lA in np.linspace(math.log(4.0) - 3 * ell, 0.0, 41):
                pv = point(ell, mu, b, r, kap, P, lA, opt)
                if pv is None: continue                                          # Tz with a non-positive bracket: excluded by the table too
                trd = table_at(o2, ell, r, lA)
                if o1 is not None: trd = max(trd, table_at(o1, ell, r, lA))      # the table uses one of the two branches at each a'
                scale = abs(pv) + abs(trd) + Dc('1e-9000')
                gaps.append(float((pv - trd) / scale))
                if trd > pv + Dc('1e-9') * scale: bad.append({'ell': ell, 'opt': opt, 'state': list(st), 'logA': float(lA), 'table': str(trd)[:30], 'point': str(pv)[:30]})
        return bad, gaps
    allg = []
    for i in range(n):
        ell = float(rng.choice([55.26, 60.0, 100.0, 300.0, 960.8])); st = sample(rng, ell)
        bad, gaps = one(ell, st); out['states'] += 1; out['violations'] += bad[:2]; allg += gaps
    out['violation_count'] = len(out['violations']); out['min_relative_gap (point - table)/scale'] = min(allg) if allg else None
    # ---- the transcription pass: the same comparison at ell = 3.5, 4, 5, 6 and beta >= 300 (sigma = e^-ell is large, so the sigma-suppressed lines A1v, A1w, A2, B1w, B2,
    #      Xi are visible).  The table's formulas are algebraic in sigma; the pointwise inequality table <= point does not need ell >= 55.26.
    allt = []; vt = []
    for i in range(n):
        ell = float(rng.choice([3.5, 4.0, 5.0, 6.0])); st = sample(rng, ell)
        bad, gaps = one(ell, st); vt += bad[:2]; allt += gaps
    out['transcription_pass'] = {'states': n, 'violation_count': len(vt), 'violations': vt[:5], 'min_relative_gap': min(allt) if allt else None}
    # ---- power: wrong tables must be caught on the same kind of states
    power = {}
    for w in ('ring0', 'cK2', 'M40', 'hneg0', 'A1w0', 'A1v0', 'A20', 'B1w0', 'B20', 'Fz0'):
        Z.ZOPT['W'] = w; rngw = np.random.default_rng(seed + 1); c = 0
        try:
            for i in range(max(40, n // 3)):
                ell = float(rngw.choice([55.26, 60.0, 100.0, 300.0, 960.8])); st = sample(rngw, ell)
                if w == 'ring0': st = (1e-3, rngw.uniform(math.log(2.6e10), math.log(1e13)), st[2], st[3], 2e-3 * 0.0625)                # P2 dominant, beta small
                if w == 'cK2': st = (st[0], rngw.uniform(math.log(2.6e10), math.log(1e14)), rngw.uniform(math.log(1e-3), math.log(0.25)), 10.0 ** rngw.uniform(0, 6), 2 * st[0] * 0.0625)   # chirp visible
                if w == 'hneg0': st = (st[0], rngw.uniform(math.log(1e-3), math.log(0.49)) + 2 * ell, rngw.uniform(math.log(1e-2), math.log(0.25)), st[3], st[4])   # large b, r
                if w in ('M40', 'A1w0', 'A1v0', 'A20', 'B1w0', 'B20', 'Fz0'): ell = float(rngw.choice([3.5, 4.0, 5.0, 6.0])); st = sample(rngw, ell)                       # visible only at large sigma
                bad, _ = one(ell, st); c += int(len(bad) > 0)
        finally:
            Z.ZOPT['W'] = None
        power[w] = c
    out['power_wrong_tables_caught'] = power
    bad, mm = line_check(n)
    out['line_check'] = {'bad_lines': len(bad), 'first_bad': bad[:5], 'ratio_table_over_lemma (min, max)': mm}
    lw = {}
    for w in ('M40', 'A1w0', 'A1v0', 'A20', 'B1w0', 'B20'):
        bw, _ = line_check(max(10, n // 6), wrong=w); lw[w] = len(bw)
    out['line_check']['power_wrong_tables_caught'] = lw
    need = ('ring0', 'cK2', 'hneg0')                                       # the lines large enough to be seen in the total; the others by the line check
    out['ok'] = (out['violation_count'] == 0 and out['transcription_pass']['violation_count'] == 0 and all(power[k] > 0 for k in need)
                 and len(bad) == 0 and all(v > 0 for v in lw.values()))
    json.dump(out, open('results/cz_point.json', 'w'), indent=1, default=float)
    print(json.dumps({k: out[k] for k in ('states', 'violation_count', 'min_relative_gap (point - table)/scale', 'power_wrong_tables_caught', 'ok')}))
    print('line check:', out['line_check']['bad_lines'], {k: (round(v[0], 9), round(v[1], 6)) for k, v in mm.items()}, lw); [print(v) for v in bad[:4]]
    print('transcription pass:', {k: v for k, v in out['transcription_pass'].items() if k != 'violations'}); [print(v) for v in out['transcription_pass']['violations'][:4]]
    for v in out['violations'][:5]: print(v)
    return out


if __name__ == '__main__':
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
