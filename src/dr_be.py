"""Stage DR (DR_探索計画.md sections B and E, written before this ran): THE CONSTANTS OF THEOREM DR-1, LEMMA DR-P AND THEOREM DR-T.  Python 3.11 grammar.
[the numbers of a proof; decimal interval arithmetic of dl_interval.py with outward rounding, run with decimal.Inexact trapped in the default context]

THEOREM DR-1 (Lemma BE of paper H without the limits B <= 1e4 and ell <= 6907.8).  Class: (P0), (P3), (P4), q0_n <= 2 e^{-n^2 x/2}, 5e11 sigma^2 <= x <= 0.003.
For ell >= 960.8, 0 < B <= 8 ell + 100 and tau >= tau0(ell) := 4 ln(ell) + 40:   (a) + (a') >= kappa(B)/sigma,  kappa(B) = min(0.055, 0.459/(4B+1)).
The proof is the published one with three changes (DR_証明まとめ.md section 13): 1 - e >= y/(2+y) for general B; the remainders are written as
sigma^2 x (sigma-free ratio) by x = tau B sigma^2 and compared with the main term of each case (b Psi/4 for L^2 >= 1, sigma^2 J_ww > (1-eps1) sigma^2 for L^2 < 1);
a_4* is written relative to (1-e) W.  What is computed here:
 (1) the window constants at ell0 = 960.8 and the monotonicity facts used (U1 c_chi/ell, gamma_P/ell, (8 ell+100)/ell decrease: checked on a grid, proved by formula);
 (2) nu_bar(tau) = 2.0000001 e^{-0.499999 tau} >= nu_k(tau, beta) for tau >= 60, k <= 4, beta <= 1e-6 tau: the tail sum_{n>=2} n^4 e^{-0.499999 (n^2-1) tau} <= 1e-30;
 (3) the majorants rho_1 (L^2 >= 1: remainders/b) and rho_2 (L^2 < 1: remainders/sigma^2) at (ell0, tau0(ell0)), each term a product C(ell) tau^j nu_bar(tau)
     with C(ell)/ell^{3/2} non-increasing, j <= 5/2: so the value at (ell0, tau0(ell0)) bounds every ell >= ell0, tau >= tau0(ell) (Lemma DR-R);
 (4) the constants: rho_W <= 0.0801, c_1/2 (1-b)^2 >= 0.459, c_2/2 Psi_min - rho_1/2 >= 0.055, the L^2 < 1 case, the tail T_Lambda;
 (5) a float scan of rho_1, rho_2 over ell in [960.8, 1e15] and tau >= tau0(ell) and B (the sup is at the corner: numerical confirmation of (3));
 (6) wrong versions: tau0 = 2 ln ell + 10 and nu ~ e^{-tau/4} must break the remainder claim.
LEMMA DR-P / THEOREM DR-T.  (7) c_P/(sigma Gamma_ell) >= 1 on the states of room 1b with tau < tau0(ell): the worst corner in logarithms at ell0, increasing in ell.
(8) the map of room 1b: ell* with 5e11/(8 ell + 100) = tau0(ell).
-> results/dr_be.json"""
import decimal, functools, json, math, os, sys
from decimal import Decimal as Dc
import dl_interval as I
from dl_interval import Iv

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'results', 'dr_be.json')
PI = Iv('3.14159265358979323846', '3.14159265358979323847')
ELL0 = '960.8'


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


class F:                         # float operations with the same names as the interval ones
    sqrt = staticmethod(math.sqrt); exp = staticmethod(math.exp); log = staticmethod(math.log); pi = math.pi; one = 1.0


class V:
    sqrt = staticmethod(I.sqrt); exp = staticmethod(I.exp); log = staticmethod(I.log); pi = PI; one = Iv(1)


def window_consts(o, ell):
    """the window constants of paper H (06_certificates.tex, ch_bedge.U_consts): no upper limit on ell (they need x >= 5e11 sigma^2)."""
    QB = o.one * 0.25
    U1 = QB * o.sqrt(2 * ell + 3.1) + 1e-6; U2 = QB * (2 * ell + 3.1) + 1e-4
    gP = (U2 * (1 + QB) + U1 * U1 + U1 * (1 + 2 * QB) / o.sqrt(o.exp(o.one))) / ((1 - QB) * (1 - QB))
    cchi = (U1 / (1 - QB) + o.sqrt(2 / o.pi) + QB * o.exp(o.one * -0.5) / (1 - QB)) / o.sqrt(o.one * 2)
    return U1, U2, gP, cchi


def nu_bar(o, tau, wrong=None):
    return 2.0000001 * o.exp(tau * (-0.25 if wrong == 'nu' else -0.499999))


def tau0(o, ell, wrong=None):
    return 2 * o.log(ell) + 10 if wrong == 'tau0' else 4 * o.log(ell) + 40


def remainders(o, ell, tau, B, wrong=None):
    """the remainders of the 2 N_phi inequality divided by sigma^2, term by term (x = tau B sigma^2, b = B sigma^2); rho_W and delta_4 as well."""
    QB = o.one * 0.25; sig = o.exp(-1 * ell); U1, U2, gP, cchi = window_consts(o, ell)
    n = nu_bar(o, tau, wrong); z = QB * n / 2; r2 = o.sqrt(o.one * 2)
    bbar = B * sig * sig                                                     # b
    Xi = (U1 / (1 - QB) + QB * o.exp(o.one * -0.5) / (1 - QB)) / r2 + 1 / (2 * o.sqrt(o.pi))
    d4 = (o.one * 5 / 3) * (tau * n + 2 * o.sqrt(2 * tau * B) * n * sig * Xi / (1 - bbar))
    rhoW = 48 * (1 + QB) * (o.one * 1e-3 / (1 - QB) + sig * sig * (U1 * U1 + 0.5) / ((1 - QB) * (1 - QB) * (1 - QB))) / ((1 - bbar) * (1 - bbar))
    t = {'a1': o.one * 3 / 8 * QB * n,
         'a2': B * (1 + QB) * (1 + QB / 2) * sig * cchi * n,
         'a3': QB * tau * n / 8,
         'a5': (1 + QB) * gP * n,
         'a6': o.sqrt(tau * B) * (U1 * cchi + (1 + QB) * gP / r2) * n,
         'a7': tau * B * QB * (1 + QB) * sig * cchi * n / 2,
         'a8': QB * tau * tau * n / 8,
         'a9': tau * B * sig * sig * QB * n / (2 * (1 - n)),
         'a10': tau * o.sqrt(tau * B) * QB * n / (2 * r2),
         'Phi_prop': B * QB * (1 + tau) * n,
         'rho_bnu': (rhoW + d4) * B * tau * QB * n / (2 * (1 - n))}
    return t, {'nu': n, 'z': z, 'rhoW': rhoW, 'd4': d4, 'sig': sig, 'U1': U1, 'gP': gP, 'cchi': cchi, 'b': bbar}


BEXP = {'a1': 0, 'a2': 1, 'a3': 0, 'a5': 0, 'a6': 0.5, 'a7': 1, 'a8': 0, 'a9': 1, 'a10': 0.5, 'Phi_prop': 1, 'rho_bnu': 1}      # the power of B in each term


def rho2(o, ell, tau, B=None, wrong=None):
    """L^2 < 1: (sum of the remainders)/sigma^2 at B (default: the top B = 8 ell + 100, where every term is largest)."""
    B = 8 * ell + 100 if B is None else B
    t, c = remainders(o, ell, tau, B, wrong); s = None
    for v in t.values(): s = v if s is None else s + v
    return s / (1 - c['z']), t, c


def rho1(o, ell, tau, wrong=None):
    """L^2 >= 1: (sum of the remainders)/b = (1/B)(sum)/sigma^2, with 1/B <= M(tau) := 1 + tau/5e11 (B >= 1 or tau >= 5e11/B) and B <= 8 ell + 100
    in the terms that grow with B (they do not: after division by B the powers are 0, -1/2, -1; B-free terms use the top B only inside rho_W, delta_4, sigma terms)."""
    Bt = 8 * ell + 100; t, c = remainders(o, ell, tau, Bt, wrong); M = 1 + tau / 5e11; s = None
    for k, v in t.items():
        e = BEXP[k]
        w = v / Bt if e == 1 else (v / o.sqrt(Bt) * o.sqrt(M) if e == 0.5 else v * M)
        s = w if s is None else s + w
    return s / (1 - c['z']), c


@trapped
def check_window_and_nu():
    o = V; ell = Iv(ELL0); U1, U2, gP, cchi = window_consts(o, ell)
    # the tail of nu_k: sum_{n >= 2} n^4 e^{-0.499999 (n^2 - 1) tau} at tau = 60 (decreasing in tau); n >= 8 by a geometric series (ratio <= e^{-400})
    tail = Iv(0)
    for n in range(2, 8): tail = tail + n ** 4 * I.exp(Iv(60) * (-0.499999 * (n * n - 1)))
    tail = tail + 2 * 8 ** 4 * I.exp(Iv(60) * (-0.499999 * 63))
    return {'ell0': ELL0, 'U1': U1.f(), 'U2': U2.f(), 'gamma_P': gP.f(), 'c_chi': cchi.f(), 'nu_tail_sum_at_tau_60': float(tail.hi), 'nu_tail_ok': bool(tail.hi <= Dc('1e-30')),
            'note': 'nu_k <= 2 e^{-tau/2 + beta}(1 + tail) with beta <= 1e-6 tau; (n-1) <= (n^2-1) gives the exponent -0.499999 (n^2-1) tau for the ratio of term n to term 1'}


@trapped
def check_point():
    o = V; ell = Iv(ELL0); t0 = tau0(o, ell); QB = Iv('0.25')
    r2, terms, c = rho2(o, ell, t0); r1, _ = rho1(o, ell, t0)
    n, z, sig, b = c['nu'], c['z'], c['sig'], c['b']
    eps1 = n * (1 + 2 * QB) / (1 - QB * n / 2)
    Bt = 8 * ell + 100
    s2_over_1me = sig * sig * (1 + 4 * Bt / ((1 - b) * (1 - b)))                       # sigma^2/(1-e) <= sigma^2 (2+y)/y = sigma^2 (1 + 4B/(1-b)^2)
    c1 = 1 - s2_over_1me / (1 - n) - (c['rhoW'] + c['d4']) * (1 + z) / ((1 - z) * (1 - n))
    cW = c1 / 2 * (1 - b) * (1 - b)                                                     # (1-e) >= (1-b)^2/(4B + (1-b)^2) >= (1-b)^2/(4B+1)
    c2h = (1 / (1 + z) - 1 / (2 * (1 - z))) / 2
    Psi = 1 - I.exp(Iv('-0.25')) - sig * c['cchi']
    # the tail T_Lambda, Lambda = 1e-3/sigma^2: its ratio to sigma^2 J_ww is <= 22.3 T/sigma^2 <= 89300 Lambda^3 e^{-Lambda} (see the document); in logarithms
    Lam = I.exp(2 * ell) * 1e-3
    ln_tail = I.log(Iv(89300)) + 3 * I.log(Lam) - Lam
    tail_ok = bool(ln_tail.hi <= Dc('-1e800'))
    cJ = 1 - 1 / (8 * (1 - z)) - Iv('1e-100')
    A = c2h * Psi - r1 / 2                                                            # coefficient of b, L^2 >= 1
    cJ2 = (cJ - r2 / (2 * (1 - eps1))) * (1 - eps1)                                    # L^2 < 1: needs >= 0.459
    out = {'ell0': ELL0, 'tau0': t0.f(), 'B_top': Bt.f(), 'nu_bar': n.f(), 'rho_2_sum_over_sigma2': float(r2.hi), 'rho_1_sum_over_b': float(r1.hi),
           'terms_over_sigma2_at_B_top': {k: float(v.hi) for k, v in terms.items()}, 'rho_W': c['rhoW'].f(), 'delta_4': float(c['d4'].hi), 'eps_1': float(eps1.hi),
           'sigma2_over_1_minus_e': float(s2_over_1me.hi), 'c_1': c1.f(), 'coef_W': float(cW.lo), 'Psi_min': float(Psi.lo), 'coef_b_L2_ge_1': float(A.lo),
           'coef_J_L2_ge_1': float(cJ.lo), 'coef_J_L2_lt_1_times_1_minus_eps1': float(cJ2.lo), 'ln_tail_ratio_upper_is_minus_10_to_the': int(ln_tail.hi.adjusted()),
           'tail_ok': tail_ok}
    out['checks'] = {'remainder claim (R): rho_2 <= 2e-4': bool(r2.hi <= Dc('2e-4')), 'rho_1 <= 2e-4': bool(r1.hi <= Dc('2e-4')), 'rho_W <= 0.0801': bool(c['rhoW'].hi <= Dc('0.0801')),
                     'coef_W >= 0.459': bool(cW.lo >= Dc('0.459')), 'coef_b >= 0.055 (L^2 >= 1)': bool(A.lo >= Dc('0.055')), 'coef_J >= 0.459 (L^2 >= 1)': bool(cJ.lo >= Dc('0.459')),
                     'coef_J (1 - eps1) >= 0.459 (L^2 < 1)': bool(cJ2.lo >= Dc('0.459')), 'Psi_min >= 0.2211': bool(Psi.lo >= Dc('0.2211')), 'tail': tail_ok}
    out['ok'] = all(out['checks'].values())
    return out


@trapped
def check_wrong():
    o = V; ell = Iv(ELL0); res = {}
    for wv in ('tau0', 'nu'):
        t0 = tau0(o, ell, wv if wv == 'tau0' else None); r2, _, _ = rho2(o, ell, t0, wrong=wv if wv == 'nu' else None)
        res[wv] = {'rho_2_lower': float(r2.lo), 'claim_R_broken': bool(r2.lo > Dc('2e-4'))}
    return res


def scan():
    """float scan (numerical confirmation of Lemma DR-R): the sup of rho_1, rho_2 over ell >= 960.8, tau >= tau0(ell), B <= 8 ell + 100 is at the corner."""
    o = F; e0 = float(ELL0); c2, _, _ = rho2(o, e0, tau0(o, e0)); c1, _ = rho1(o, e0, tau0(o, e0))
    m1 = m2 = 0.0; npt = 0; worst = None
    for i in range(0, 141):
        ell = e0 * 10 ** (i * 12.0 / 140)
        for j in range(0, 60):
            tau = tau0(o, ell) * (1 + (10 ** (j / 6.0) - 1) * 0.05)
            if tau > 1400: continue
            r1, _ = rho1(o, ell, tau); m1 = max(m1, r1); npt += 1
            for fB in (1.0, 0.5, 0.1, 1e-2, 1e-4):
                B = (8 * ell + 100) * fB; r2, _, _ = rho2(o, ell, tau, B)
                if r2 > m2: m2 = r2; worst = (ell, tau, B)
    # the monotone ratios
    mono = True; prev = None
    for i in range(0, 400):
        ell = e0 * 10 ** (i * 14.0 / 399); U1, U2, gP, cchi = window_consts(o, ell)
        cur = (U1 * cchi / ell, gP / ell, (8 * ell + 100) / ell, U1 / math.sqrt(ell), cchi / math.sqrt(ell))
        if prev is not None: mono &= all(a <= b * (1 + 1e-13) for a, b in zip(cur, prev))
        prev = cur
    return {'points': npt, 'rho_1_corner': c1, 'rho_1_max_scan': m1, 'rho_2_corner': c2, 'rho_2_max_scan': m2, 'rho_2_argmax': worst,
            'sup_at_corner': bool(m1 <= c1 * (1 + 1e-12) and m2 <= c2 * (1 + 1e-12)), 'ratios_C_over_ell_nonincreasing': bool(mono)}


@trapped
def check_P():
    """Theorem DR-T on tau < tau0(ell):  ln(c_P/(sigma Gamma_ell)) >= ell - 10 pi^2 (8 ell + 100)/5e11 - ln 6 - ln 8 - ln(tau0(ell)(8 ell + 100)) + 2 ln(brk) - ln Gamma_ell,
    brk = 1 - (8 ell+100) sigma^2 - 2 a sqrt(x)/pi with a sqrt(x) <= ((4/3) U1 + 0.21) sigma sqrt(tau0 (8 ell + 100)).  At ell0; the derivative in ell is > 0.9."""
    o = V; ell = Iv(ELL0); t0 = tau0(o, ell); Bt = 8 * ell + 100; sig = I.exp(-1 * ell); U1 = window_consts(o, ell)[0]
    a = U1 * 4 / 3 + 0.21
    brk = 1 - Bt * sig * sig - 2 * a * sig * I.sqrt(t0 * Bt) / PI
    Gam = I.sqrt((1 + 10 / ell) / ell)
    lnr = ell - 10 * PI * PI * Bt / 5e11 - I.log(Iv(48)) - I.log(t0 * Bt) + 2 * I.log(brk) - I.log(Gam)
    theta_term = (10 * PI * PI * Bt / 5e11)
    return {'ell0': ELL0, 'ln_cP_over_sigma_Gamma_lower': float(lnr.lo), 'ten_pi2_over_tau_max': float(theta_term.hi), 'brk_lower': float(brk.lo), 'Gamma_ell0': Gam.f(),
            'ok': bool(lnr.lo >= 900),
            'note': 'theta/(1+theta) = 1/(1 + 5 e^{10 pi^2/tau}) >= e^{-10 pi^2/tau}/6 and tau >= 5e11/(8 ell + 100); d/d ell of the bound >= 1 - 1.6e-9 - 8/(8 ell+100) - 4/(ell tau0) - 1/(2 ell) - tiny > 0.99'}


def room_map():
    f = lambda L: 5e11 / (8 * L + 100) - (4 * math.log(L) + 40)
    lo, hi = 1e3, 1e12
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if f(mid) > 0: lo = mid
        else: hi = mid
    rows = []
    for L in (960.8, 1e4, 1e6, 1e8, lo, 1e9, 1e10, 1e12, 1e15):
        t0 = 4 * math.log(L) + 40; rows.append({'ell': L, 'tau0': t0, 'B_top': 8 * L + 100, 'tau_min_in_room': 5e11 / (8 * L + 100), 'B_min_where_tau_lt_tau0': 5e11 / t0,
                                                'room_1b_has_tau_below_tau0': bool(5e11 / (8 * L + 100) < t0)})
    return {'ell_star': lo, 'rows': rows, 'note': 'for ell <= ell_star every state of room 1b has tau >= tau0(ell) (Theorem DR-1 alone); above, the states with tau < tau0 are covered by Lemma DR-P'}


def main(save=True):
    res = {'window_and_nu': check_window_and_nu(), 'point': check_point(), 'wrong_versions': check_wrong(), 'scan': scan(), 'DR_P': check_P(), 'map': room_map(),
           'python': sys.version.split()[0], 'inexact_trapped': True}
    res['ok'] = bool(res['window_and_nu']['nu_tail_ok'] and res['point']['ok'] and res['scan']['sup_at_corner'] and res['scan']['ratios_C_over_ell_nonincreasing'] and res['DR_P']['ok']
                     and all(v['claim_R_broken'] for v in res['wrong_versions'].values()))
    if save: json.dump(res, open(OUT, 'w'), indent=1, default=str)
    return res


if __name__ == '__main__':
    r = main(); print(json.dumps(r, indent=1, default=str)[:6000]); print('ok', r['ok'])
