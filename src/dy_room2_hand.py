"""Stage DY, item 2.4 (Theorem 3), revised in stage EA: THE SIDE CONDITIONS AND THE MAIN CHAIN OF THE ROOM b in (1/2, 1] BY HAND, in exact rational arithmetic (fractions).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  [proof: every number below is an exact rational upper (or lower) bound; the script only does the arithmetic]
Setting (paper J, Theorem 3): eta <= eta_bar = 1/4 in every remainder (uniform), gamma <= 0.49, ell >= 55.26, sigma = e^-ell, B >= 1/(2 sigma^2), b <= 1, P <= P1.
The terms are those of dp_room2.consts (paper I, Proposition 13) with eta = 1/4 (dx_room2.consts_eta, stage DX).  MONOTONICITY: every term is a product of
nonnegative factors that do not increase in ell for ell >= 55.26:  t = 1/ell;  sigma;  ell sigma (decreasing for ell > 1);  sqrt(sigma);  X1^2/ell and U1^2/ell
(sqrt(2 + 3.1 t) decreases);  everything else is a number (eta = 1/4 is fixed).  So the worst case is ell = 55.26 and the bounds below are evaluated there.
RATIONAL BOUNDS USED:  e >= 2.71828 (e = 2.718281828...);  e^-x <= (1/2.71828)^floor(x) / (sum_{j<=3} f^j/j!) with f = x - floor(x) (the partial sum is <= e^f);
  sqrt(0.2) <= 0.44722 (stage EA; 0.4473 was too coarse for eps_h <= 0.3882, see the power check);  sqrt(pi) >= 1.7724;  sqrt2 >= 1.4142;  sqrt(2 + 3.1/55.26) <= 1.4340;  sqrt(2 P1) <= 1.3289;  sqrt(P1) <= 0.9397;  sqrt(7.5) <= 2.7387;
  P1 <= 0.8829 (paper I, (F1'); it does not involve eta);  (1 + 1.5 sigma^2)^2 <= 1 + 4 sigma^2.  Each sqrt bound is checked here by squaring.
CONDITIONS:  e_L + e_S <= e2 = 1e-12;  R4' <= 2 (paper J; paper I had 1.86);  K_F <= ell sigma;  (d4 + N4G)/P2z <= es_sigma;  Case I: c1 sqrt(1/2)/Gam2 - P1/3 > 0 (c1 = 0.77,
  the rule's Gam2 = Gamma/2, Gamma = sqrt((1 + 10/ell)/ell) <= its value at 55.26).
THE MAIN CHAIN (stage EA, eq. (14)-(15) of paper J): eps1 = eta_bar kE 1.8 <= 0.2013;  eps_h = 2 kE (eta_bar + 0.184)/omega <= 0.3882 (1/omega <= 1 + 4 sigma^2);
  theta^2 >= (1 - 0.2013 - e2)(1 - 0.3882 - e2) omega >= 0.48864;  k1 = 1 + (eta_bar + 0.184) kE <= 1.19413;  with gamma = 0.49, k2 = 1/(2(1 - eta_bar)) = 2/3, G <= P1/3,
  tail = (2 ell + 1/2) sigma:  b = 1:  0.48864 - (gamma 1.19413 + gamma k2 P1/3 + tail)^2 >= 0.0245;   b = 1/2:  0.48864 - 2 (gamma 1.19413/2 + gamma k2 P1/3 + tail)^2 >= 0.1864 (0.18646).
  Each printed bound is checked against the exact rational value, and the margins are computed from the printed bounds (so the printed chain is valid).
POWER (each must fail): sqrt(0.2) <= 0.4473 kept (then eps_h <= 0.3882 fails);  e2 = 4e-13;  R4' <= 1.9;  eta_bar = 0.6 (K_F > ell sigma);  c1 = 0.002 (Case I).  And the hand bounds are above the interval values of stage DX.
-> results_DY/dy_room2_hand.json"""
import json, os, sys, time
from fractions import Fraction as Fr

ELO = Fr(271828, 100000)


def expneg_upper(x):
    """an upper bound of e^-x for a rational x >= 0"""
    n = int(x); f = x - n; ps = 1 + f + f * f / 2 + f ** 3 / 6
    return (1 / ELO) ** n / ps


def sq_ok(x, s, upper=True):
    """s is an upper (lower) bound of sqrt(x): s^2 >= x (<= x)"""
    return s * s >= x if upper else s * s <= x


def run(gamma=Fr(49, 100), eta=Fr(1, 4), e2=Fr(1, 10 ** 12), r4b=Fr(2), c1=Fr(77, 100), kE=Fr(44722, 100000)):
    L = Fr(5526, 100); t = 1 / L; sg = expneg_upper(L); shs = expneg_upper(L / 2); sgL = L * sg
    spi = Fr(17724, 10000); s2 = Fr(14142, 10000); P1 = Fr(8829, 10000)
    r23 = Fr(14340, 10000); s2P1 = Fr(13289, 10000); sP1 = Fr(9397, 10000); s75 = Fr(27387, 10000)
    sqrt_checks = {'sqrt(0.2) <= %s' % float(kE): sq_ok(Fr(1, 5), kE), 'sqrt(pi) >= 1.7724 (pi >= 3.14159)': sq_ok(Fr(314159, 100000), spi, False),
                   'sqrt2 >= 1.4142': sq_ok(Fr(2), s2, False), 'sqrt(2 + 3.1 t) <= 1.4340': sq_ok(2 + Fr(31, 10) * t, r23), 'sqrt(2 P1) <= 1.3289': sq_ok(2 * P1, s2P1),
                   'sqrt(P1) <= 0.9397': sq_ok(P1, sP1), 'sqrt(7.5) <= 2.7387': sq_ok(Fr(75, 10), s75)}
    X1q = Fr(16, 9) * (r23 / 4 + Fr(1, 10 ** 6) * Fr(1, 7)) ** 2                 # sqrt(t) <= 1/7 (t <= 1/49)
    U1q = X1q * 9 / 16
    CZ = eta * eta / (ELO * (1 - eta) ** 2)
    M4c = 3 * (1 + eta * kE * Fr(625, 10000) / Fr(15625, 10000)) + 6 * eta * kE * Fr(25, 100) / Fr(15625, 10000); M4g = 3 * Fr(1, 24) / (8 * (1 - eta))
    eps1 = eta * kE * Fr(18, 10); Q2 = 1 + eps1
    inv_om = 1 + 4 * sg * sg                                                         # 1/omega = (1 + 1.5 sigma^2)^2 <= 1 + 4 sigma^2
    e50 = expneg_upper(Fr(50))
    terms = {'N2': Q2 * sg * sg / 4, 'd3': gamma * sg * (1 + 2 * eta * kE) / 2,
             'N4': Fr(3, 4) * sg * ((X1q * sgL + CZ * sg) * Q2 + M4c * sg / 4),
             'ring2': Fr(8, 10) * e50 * 11 * sgL * eta ** 2 * 2 * sg * sg / (16 * s2 * (1 - eta)),
             'A2a': sg * sg * (1 + eta) / 4, 'A2b': shs * eta ** 2 / (8 * s2 * (1 - eta)),
             'B2b': s2P1 / 4 * (Fr(895, 10000) * sg * sg + shs * eta ** 2 / (2 * s2 * (1 - eta) ** 2))}
    eL = sum(terms.values())
    cS = (1 + eta) / (4 * spi) + (Fr(184, 1000) + sg * sg) * Fr(2, 10) / (2 * spi) + eta * eta * (1 + sg * sg / 2) / (2 * spi * 2 * (1 - eta))
    eS = 2 * cS * shs * (1 + sg) * inv_om
    R4 = (M4c + M4g) / 2 + Fr(625, 10000) * Fr(207, 100) * kE + s75 * kE * sP1 / 4 + Fr(1, 10 ** 9)
    KF = U1q * (Fr(375, 1000) * Fr(2, 3) / (1 - eta) + s2P1 / (12 * (1 - eta) ** 2))
    q = (8 * t + 100 * t * t) * 2 * sgL * sg * (1 + eta) / (8 * (1 - eta))
    d4 = (1 + eta) / (1 - q) * (gamma / (2 * (1 - eta)) * t ** 2 + Fr(3, 2) * ((X1q * sgL + CZ * sg) / (2 * (1 - eta)) + Fr(3, 2) * sg / (32 * (1 - eta))) * t ** 2)
    Gam2sq_ok = (1 + 10 * t) * t <= Fr(1462, 10000) ** 2                             # Gamma(55.26) <= 0.1462 (and Gamma decreases in ell)
    caseI = c1 * Fr(7071, 10000) * 2 / Fr(1462, 10000) - P1 / 3                      # sqrt(1/2) >= 0.7071 (0.7071^2 <= 1/2), 1/Gam2 = 2/Gamma >= 2/0.1462
    out = {'sqrt bounds (each squared)': sqrt_checks, 'sqrt(1/2) >= 0.7071': Fr(7071, 10000) ** 2 <= Fr(1, 2), 'Gamma(55.26) <= 0.1462': Gam2sq_ok,
           'sigma <= (rational)': float(sg), 'sqrt(sigma) <=': float(shs), 'terms of e_L (rational upper bounds)': {k: float(v) for k, v in terms.items()},
           'e_L <=': float(eL), 'c_S <=': float(cS), 'e_S <=': float(eS),
           'e2 - (e_L + e_S) (must be > 0)': float(e2 - eL - eS), "R4' <=": float(R4), "%s - R4' (must be > 0)" % r4b: float(r4b - R4),
           'K_F/(ell sigma) <=': float(KF), '1 - K_F/(ell sigma) (must be > 0)': float(1 - KF), 'q <=': float(q),
           '(d4 + N4G)/P2z / es_sigma <= (must be < 1)': float(d4), 'Case I: c1 sqrt(1/2)/Gam2 - P1/3 >= (must be > 0)': float(caseI)}
    # THE MAIN CHAIN (stage EA)
    eps1_x = eta * kE * Fr(18, 10); epsh_x = 2 * kE * (eta + Fr(184, 1000)) * inv_om; k1_x = 1 + (eta + Fr(184, 1000)) * kE
    B_e1, B_eh, B_th, B_k1 = Fr(2013, 10000), Fr(3882, 10000), Fr(48864, 100000), Fr(119413, 100000)
    th_x = (1 - B_e1 - e2) * (1 - B_eh - e2) / inv_om
    tail = (2 * L + Fr(1, 2)) * sg; k2 = 1 / (2 * (1 - eta))
    m1 = B_th - (gamma * B_k1 + gamma * k2 * P1 / 3 + tail) ** 2
    mh = B_th - 2 * (gamma * B_k1 / 2 + gamma * k2 * P1 / 3 + tail) ** 2
    chain = {'eps1 (exact)': float(eps1_x), 'eps1 <= 0.2013': eps1_x <= B_e1, 'eps_h (exact upper)': float(epsh_x), 'eps_h <= 0.3882': epsh_x <= B_eh,
             'theta^2 from the printed eps (exact lower)': float(th_x), 'theta^2 >= 0.48864': th_x >= B_th, 'k1 (exact)': float(k1_x), 'k1 <= 1.19413': k1_x <= B_k1,
             'margin at b = 1 (from the printed bounds)': float(m1), 'margin b = 1 >= 0.0245': m1 >= Fr(245, 10000),
             'margin at b = 1/2 (from the printed bounds)': float(mh), 'margin b = 1/2 >= 0.1864': mh >= Fr(1864, 10000)}
    out['main chain (eq. 14-15)'] = chain
    chain_ok = all(v for k, v in chain.items() if isinstance(v, bool))
    out['exact signs main chain'] = chain_ok
    ok = (chain_ok and all(sqrt_checks.values()) and out['sqrt(1/2) >= 0.7071'] and Gam2sq_ok and e2 - eL - eS > 0 and r4b - R4 > 0 and 1 - KF > 0 and d4 < 1 and caseI > 0)
    out['exact signs'] = {'e_L + e_S < e2': e2 - eL - eS > 0, "R4' < bound": r4b - R4 > 0, 'K_F < ell sigma': 1 - KF > 0, '(d4 + N4G)/P2z < es_sigma': d4 < 1, 'Case I': caseI > 0}
    out['ok'] = bool(ok)
    return out


def main():
    t0 = time.time(); r = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'hand (eta_bar = 1/4, gamma = 0.49, c1 = 0.77)': run()}
    p0 = run(kE=Fr(4473, 10000))
    r['power: sqrt(0.2) <= 0.4473 (must fail: eps_h <= 0.3882)'] = p0['ok']
    r['power: sqrt(0.2) <= 0.4473: eps_h <= 0.3882 holds?'] = p0['main chain (eq. 14-15)']['eps_h <= 0.3882']
    r['power: e2 = 4e-13 (must fail)'] = run(e2=Fr(4, 10 ** 13))['ok']
    r["power: R4' <= 1.9 (must fail)"] = run(r4b=Fr(19, 10))['ok']
    r['power: eta_bar = 0.6 (must fail: K_F)'] = run(eta=Fr(6, 10))['ok']
    r['power: c1 = 0.002 (must fail: Case I)'] = run(c1=Fr(2, 1000))['ok']
    # the same quantities from the interval part of stage DX (dx_room2, one piece): the hand bounds must be above them
    try:
        dx = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX', 'dx_room2.json')))
        v = dx['PART C values']; h = r['hand (eta_bar = 1/4, gamma = 0.49, c1 = 0.77)']
        r['hand >= interval (stage DX)'] = {'e_L': h['e_L <='] >= v['e_L'], 'e_S': h['e_S <='] >= v['e_S'], "R4'": h["R4' <="] >= v["R4'"], 'K_F': h['K_F/(ell sigma) <='] >= v['K_F/(ell sigma)']}
    except Exception as e:
        r['hand >= interval (stage DX)'] = {'error': repr(e)}
    r['ok'] = bool(r['hand (eta_bar = 1/4, gamma = 0.49, c1 = 0.77)']['ok'] and not r['power: e2 = 4e-13 (must fail)']
                   and not r['power: sqrt(0.2) <= 0.4473 (must fail: eps_h <= 0.3882)'] and not r['power: sqrt(0.2) <= 0.4473: eps_h <= 0.3882 holds?'] and not r["power: R4' <= 1.9 (must fail)"]
                   and not r['power: eta_bar = 0.6 (must fail: K_F)'] and not r['power: c1 = 0.002 (must fail: Case I)']
                   and all(x is True for x in r['hand >= interval (stage DX)'].values()))
    r['seconds'] = time.time() - t0
    return r


if __name__ == '__main__':
    r = main(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DY'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dy_room2_hand.json'), 'w'), indent=1, default=str); print(json.dumps(r, indent=1, default=str))
