"""Stage DX, item 2.5: THE ROOM OF THEOREM 3 (b in (1/2, 1]) FOR EVERY RIPPLE eta <= eta_bar = 1/4, target coefficient 1.  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).
The steps are those of dp_room2 (paper I, Proposition 13) with eta separated from 1/ell and every eta-remainder at eta_bar = 1/4 (uniform):
  Lambda_Fz >= th sqrt(b) - gamma k1 b - gamma k2 P1/3 - (2 ell + 1/2) sigma,  th = sqrt((1 - eps1 - e2)(1 - eps_h - e2) omega),
  eps1 = eta_bar k_E 1.8, eps_h = 2 k_E (eta_bar + 0.184)/omega, k1 = 1 + (eta_bar + 0.184) k_E, k2 = 1/(2 (1 - eta_bar)) = 2/3, k_E = sqrt(0.2).
PART H (by hand, checked here in exact rational arithmetic, fractions.Fraction): the main inequality at the two ends b = 1 and b = 1/2 (concave in b),
  for every gamma in [0, GMAX], with rational outer bounds of every constant; ell enters only through the tail (2 ell + 1/2) sigma (largest at ell = 55.26).
PART C (computed: interval arithmetic on ONE piece [55.26, inf), decimal.Inexact trapped = the DO watch): the side conditions (R1')-(R5') and (d4 + N4G)/P2z
  with eta = 1/4 in every remainder (e_L + e_S <= e2 = 1e-12, R4' <= 1.86, K_F <= ell sigma, (d4 + N4G)/P2z <= es_sigma), and the main inequality once more.
POWER: GMAX + 0.02 must fail (part H and part C); eta_bar = 0.3 at gamma = GMAX must fail; with eta forgotten (1/ell in the remainders) the margin is larger
(the check must see the difference).  -> results_DX/dx_room2.json"""
import json, os, sys, time, inspect, functools, decimal
from fractions import Fraction as Fr
from decimal import Decimal as Dc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dl_interval as V
from dl_interval import Iv
import dp_room2 as R2

GMAX = Fr(49, 100)

# ---- PART H: exact rational arithmetic
def hand(gamma=GMAX, etab=Fr(1, 4)):
    """the main inequality at b = 1 and b = 1/2 with rational outer bounds; returns the two margins of th^2 against the squared right-hand sides."""
    kE_hi = Fr(4473, 10000); assert kE_hi ** 2 >= Fr(1, 5)                            # k_E = sqrt(0.2) <= 0.4473
    om_lo = 1 - Fr(1, 10 ** 40)                                                        # omega >= (1 + 1.5 sigma^2)^-2 >= 1 - 3 sigma^2, sigma <= e^-55
    e2 = Fr(1, 10 ** 12)
    eps1 = etab * kE_hi * Fr(18, 10); epsh = 2 * kE_hi * (etab + Fr(184, 1000)) / om_lo
    th2_lo = (1 - eps1 - e2) * (1 - epsh - e2) * om_lo
    k1 = 1 + (etab + Fr(184, 1000)) * kE_hi; k2 = 1 / (2 * (1 - etab)); P1 = Fr(8829, 10000); G = P1 / 3
    # tail (2 ell + 1/2) sigma <= 111 e^-55.26 at ell = 55.26 (ell sigma decreases for ell > 1); e >= 2.718, so e^-55 <= 2.718^-55
    tail = Fr(1115, 10) * Fr(1000, 2718) ** 55
    r1 = gamma * k1 + gamma * k2 * G + tail                                             # b = 1:   th >= r1
    rh = gamma * k1 / 2 + gamma * k2 * G + tail                                         # b = 1/2: th/sqrt2 >= rh  <=>  th^2 >= 2 rh^2
    m1 = th2_lo - r1 ** 2; mh = th2_lo - 2 * rh ** 2
    return {'k_E <=': float(kE_hi), 'eps1 <=': float(eps1), 'eps_h <=': float(epsh), 'th^2 >=': float(th2_lo), 'k1 <=': float(k1), 'k2 =': float(k2),
            'P1 <= (paper I, F1\')': float(P1), 'tail <=': float(tail),
            'b = 1: th^2 - (gamma k1 + gamma k2 P1/3 + tail)^2 (must be > 0)': float(m1), 'b = 1/2: th^2 - 2 (gamma k1/2 + gamma k2 P1/3 + tail)^2 (must be > 0)': float(mh),
            'exact signs': [m1 > 0, mh > 0], 'ok': bool(m1 > 0 and mh > 0)}


# ---- PART C: dp_room2.consts with eta separated (text substitution, every one asserted)
SRC = inspect.getsource(R2.consts)
REPL = [("def consts(gamma='0.6', cm=True):", "def consts_eta(gamma='0.6', cm=True, etab=Dc('0.25'), C1R=Dc('0.78'), rule_gam2='J'):"),
        ("kE = sqrt(Iv(Dc('0.2'))); k1 = 1 + (t + Dc('0.184')) * kE; k2 = 1 / (2 * (1 - t))",
         "et = Iv(etab); kE = sqrt(Iv(Dc('0.2'))); k1 = 1 + (et + Dc('0.184')) * kE; k2 = 1 / (2 * (1 - et))"),
        ("eps1 = t * kE * Dc('1.8'); epsh = 2 * kE * (t + Dc('0.184')) / om", "eps1 = et * kE * Dc('1.8'); epsh = 2 * kE * (et + Dc('0.184')) / om"),
        ("CZ = t * t / (exp(Iv(1)) * (1 - t) ** 2)", "CZ = et * et / (exp(Iv(1)) * (1 - et) ** 2)"),
        ("M4c = 3 * (1 + t * kE * Dc('0.0625') / Dc('1.5625')) + 6 * t * kE * Dc('0.25') / Dc('1.5625'); M4g = 3 * (Iv(1) / 24) / (2 * 4 * (1 - t))",
         "M4c = 3 * (1 + et * kE * Dc('0.0625') / Dc('1.5625')) + 6 * et * kE * Dc('0.25') / Dc('1.5625'); M4g = 3 * (Iv(1) / 24) / (2 * 4 * (1 - et))"),
        ("+ gam * sg * (1 + 2 * t * kE) / 2", "+ gam * sg * (1 + 2 * et * kE) / 2"),
        ("t ** 2 * 2 * sg * sg / (16 * sqrt(Iv(2)) * (1 - t))   # ring2", "et ** 2 * 2 * sg * sg / (16 * sqrt(Iv(2)) * (1 - et))   # ring2"),
        ("+ sg * sg * (1 + t) / 4", "+ sg * sg * (1 + et) / 4"),
        ("+ shs * t ** 2 / (8 * sqrt(Iv(2)) * (1 - t))", "+ shs * et ** 2 / (8 * sqrt(Iv(2)) * (1 - et))"),
        ("shs * t ** 2 / (2 * sqrt(Iv(2)) * (1 - t) ** 2)))", "shs * et ** 2 / (2 * sqrt(Iv(2)) * (1 - et) ** 2)))"),
        ("cS = (1 + t) / (4 * sqrt(LC.PI))", "cS = (1 + et) / (4 * sqrt(LC.PI))"),
        ("+ t * t * (1 + Dc('0.5') * sg * sg) / (2 * sqrt(LC.PI) * 2 * (1 - t))", "+ et * et * (1 + Dc('0.5') * sg * sg) / (2 * sqrt(LC.PI) * 2 * (1 - et))"),
        ("KF = U1q * (Dc('0.375') * 2 / 3 / (1 - t) + sqrt(2 * P1) / (12 * (1 - t) ** 2))", "KF = U1q * (Dc('0.375') * 2 / 3 / (1 - et) + sqrt(2 * P1) / (12 * (1 - et) ** 2))"),
        ("* sg * (1 + t) / (8 * (1 - t))            # q", "* sg * (1 + et) / (8 * (1 - et))            # q"),
        # (R4') at eta = 1/4: R4' <= 1.92 > 1.86; the tail (2 ell + 1/2) sigma still covers ell sigma (R5') + 2 sigma (R4') for ell >= 1.5
        ("o['1.86 - R4\\' (must be >= 0)'] = Dc('1.86') - R4", "o['2 - R4\\' (must be >= 0)'] = Dc(2) - R4"),
        ("o['(d4 + N4G)/P2z / es_sigma (must be <= 1)'] = (1 + t) / (1 - q) * (gam / (2 * (1 - t)) * t ** 2 + Dc('1.5') * ((X1q * sgL + CZ * sg) / (2 * (1 - t)) + Dc('1.5') * sg / (32 * (1 - t))) * t ** 2)",
         "o['(d4 + N4G)/P2z / es_sigma (must be <= 1)'] = (1 + et) / (1 - q) * (gam / (2 * (1 - et)) * t ** 2 + Dc('1.5') * ((X1q * sgL + CZ * sg) / (2 * (1 - et)) + Dc('1.5') * sg / (32 * (1 - et))) * t ** 2)"),
        ("o['Case I: c1 sqrt(1/2)/Gam2 - P1/3 (must be > 0)'] = Dc('0.78') * sqrt(Iv(Dc('0.5'))) * 2 * (1 - t0) / sqrt((1 + 10 * t0) * t0) - G",
         "o['Case I: c1 sqrt(1/2)/Gam2 - P1/3 (must be > 0)'] = C1R * sqrt(Iv(Dc('0.5'))) * 2 * ((1 - t0) if rule_gam2 == 'I' else 1) / sqrt((1 + 10 * t0) * t0) - G"),
        ]
for a_, b_ in REPL:
    assert SRC.count(a_) == 1, a_
    SRC = SRC.replace(a_, b_)
NS = dict(R2.__dict__); exec(compile(SRC, 'dp_room2.consts (eta separated, dx_room2)', 'exec'), NS); consts_eta = R2.trapped(NS['consts_eta'])


def run():
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'python': sys.version.split()[0]}
    import math
    G55 = math.sqrt((1 + 10 / 55.26) / 55.26)
    out['Gamma_ell at ell = 55.26 (the coefficient-1 target; Gamma decreases in ell)'] = G55
    out['PART H (hand, exact rationals): gamma = GMAX = %s' % GMAX] = hand(GMAX)
    out['PART H: gamma = Gamma_55.26 upper bound 0.1462'] = hand(Fr(1462, 10000))
    out['PART H power: gamma = GMAX + 0.02 (must fail)'] = hand(GMAX + Fr(2, 100))
    out['PART H power: eta_bar = 0.3 at GMAX (must fail)'] = hand(GMAX, Fr(3, 10))
    oc = consts_eta(str(float(GMAX)), C1R=Dc('0.75')); v = R2.verdict(oc); out['PART C (interval, one piece [55.26, inf), DO watch): gamma = GMAX, rule c1 = 0.75'] = v
    out['PART C values'] = {'e_L': float(oc['e_L'].hi), 'e_S': float(oc['e_S'].hi), "R4'": float(oc["R4': constants/sigma"].hi), 'K_F/(ell sigma)': float(oc["R5': K_F/(ell sigma)"].hi),
                            'th (lower)': float(oc['th'].lo), 'k1': float(oc['k1'].hi), 'k2': float(oc['k2'].hi), 'eps1': float(oc['eps1_max'].hi), 'eps_h': float(oc['epsh_max'].hi)}
    og = consts_eta('0.1462', C1R=Dc('0.75')); out['PART C: gamma = 0.1462 >= Gamma_ell (coefficient 1): margins b = 1, 1/2'] = [float(og['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo),
                                                                                                                 float(og['Lambda_Fz lower bound at b = 1/2 (must be >= 0)'].lo)]
    op = consts_eta(str(float(GMAX + Fr(2, 100))), C1R=Dc('0.75')); o3 = consts_eta(str(float(GMAX)), etab=Dc('0.3'), C1R=Dc('0.75'))
    of = consts_eta(str(float(GMAX)), etab=Dc(1) / Dc('55.26'), C1R=Dc('0.75'))
    out['PART C power (each must be False)'] = {'gamma = GMAX + 0.02: b = 1 margin >= 0': bool(op['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo >= 0),
                                                'eta_bar = 0.3: b = 1 margin >= 0': bool(o3['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo >= 0)}
    out['PART C power: eta forgotten (1/55.26 in the remainders): b = 1 margin (larger than the eta = 1/4 value; seen)'] = [float(of['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo),
                                                                                                                     float(oc['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo)]
    # the published record is reproduced by consts_eta at eta = 1/ell? (it is not: one piece has eta = t as an interval; checked against dp_room2.consts directly)
    o0 = R2.trapped(R2.consts)(); same = {k: (float(o0[k].lo), float(o0[k].hi)) for k in ('th', 'k1', 'k2')}
    out['paper I (dp_room2.consts, eta = 1/ell): th, k1, k2'] = same
    out['ok'] = bool(out['PART H (hand, exact rationals): gamma = GMAX = %s' % GMAX]['ok'] and out['PART H: gamma = Gamma_55.26 upper bound 0.1462']['ok']
                     and not out['PART H power: gamma = GMAX + 0.02 (must fail)']['ok'] and not out['PART H power: eta_bar = 0.3 at GMAX (must fail)']['ok']
                     and all(a for a, b in v.values()) and not any(out['PART C power (each must be False)'].values())
                     and out['PART C power: eta forgotten (1/55.26 in the remainders): b = 1 margin (larger than the eta = 1/4 value; seen)'][0]
                     > out['PART C power: eta forgotten (1/55.26 in the remainders): b = 1 margin (larger than the eta = 1/4 value; seen)'][1] + 0.1)
    out['seconds'] = time.time() - t0
    return out


if __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dx_room2.json'), 'w'), indent=1, default=str); print(json.dumps(r, indent=1, default=str))
