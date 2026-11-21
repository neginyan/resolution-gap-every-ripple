"""Stage DP, room 2: THE CONSTANTS OF THE PROOF OF THEOREM DP-2 (b in (1/2, 1]) for every ell >= 55.26, by interval arithmetic on ONE piece [55.26, inf)
(every quantity below is monotone in 1/ell and in sigma = e^-ell in the direction that makes ell = 55.26 the worst), with decimal.Inexact trapped in the default
context.  Python 3.11 grammar.  The proof itself is elementary (DP_証明まとめ.md section 10); this is its check.
THEOREM DP-2.  ell >= 55.26, 1/2 < b <= 1, mu > 0, sigma^3 <= r <= 1/4, kappa > 0, P > 0 with (A) P <= mu/8, (K) kappa P <= 2 U1^2, (CM).  Then for every a > 0 and
every gamma in [0, 0.6]:  Lambda_Fz(a) >= 0  (the corrected lines of option Fz).
STEPS:  (F1') P <= P1 := 2[(1.5/16) ln(32 B0(1/16, 1)) + c_CM] (<= 0.8829), G <= P1/3.
  (R1') N1 = eps1 P1line;  (N2 + d3 + N4 + ring2 + A2a + A2b + B2b)/P1line <= e_L;   d4 + N4G <= es_sigma P2z.      (R2') hneg1 = eps_h P4z.
  (R3') S-type <= e_S P4z (a <= 1), <= e_S P1line (a >= 1).       e2 := 1e-12 >= e_L + e_S.
  (R4') N3 + M0Xi + A1v + pair <= 1.86 sigma.     (R5') FzK + A2k + B2a <= ell sigma  (from (K)).
  Lambda_Fz >= th sqrt(b) - gamma k1 b - gamma k2 P1/3 - (2 ell + 1/2) sigma,  th := sqrt((1 - eps1 - e2)(1 - eps_h - e2) omega);  concave in b: the ends b = 1/2, 1.
-> results/dp_room2.json"""
import json, functools, decimal, time
from decimal import Decimal as Dc
import dl_interval as V
from dl_interval import Iv, exp, log, sqrt, pe
import dl_consts as LC


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


def consts(gamma='0.6', cm=True):
    L = Iv(Dc('55.26'), V.INF); t = 1 / L; sg = exp(-L); shs = exp(-L / 2); sgL = pe(1, L); o = {}
    kE = sqrt(Iv(Dc('0.2'))); k1 = 1 + (t + Dc('0.184')) * kE; k2 = 1 / (2 * (1 - t)); gam = Iv(Dc(gamma))
    P1 = 2 * ((Dc('1.5') / 16) * (log(Iv(32)) + LC.lB0(Iv(Dc(1) / 16), Iv(1))) + LC.CI) if cm else Iv(Dc(1000))       # cm = False: a wrong version (no (CM): P as large as 1000)
    o['P1 (F1\')'] = P1; G = P1 / 3
    om = 1 / (1 + Dc('1.5') * sg * sg) ** 2                                             # B >= 1/(2 sigma^2): omega = (1 + 3/(4B))^-2 >= (1 + 1.5 sigma^2)^-2
    eps1 = t * kE * Dc('1.8'); epsh = 2 * kE * (t + Dc('0.184')) / om; o['eps1_max'] = eps1; o['epsh_max'] = epsh
    X1q = (Iv(Dc(16)) / 9) * (sqrt(2 + Dc('3.1') * t) / 4 + Dc('1e-6') * sqrt(t)) ** 2     # X1^2/ell
    U1q = X1q * 9 / 16                                                                  # U1^2/ell
    CZ = t * t / (exp(Iv(1)) * (1 - t) ** 2)
    M4c = 3 * (1 + t * kE * Dc('0.0625') / Dc('1.5625')) + 6 * t * kE * Dc('0.25') / Dc('1.5625'); M4g = 3 * (Iv(1) / 24) / (2 * 4 * (1 - t))
    Q2 = 1 + eps1
    eL = (Q2 * sg * sg / 4                                                             # N2/P1 = Q2/(8B), B >= 1/(2 sigma^2)
          + gam * sg * (1 + 2 * t * kE) / 2                                            # d3
          + Dc('0.75') * sg * ((X1q * sgL + CZ * sg) * Q2 + M4c * sg / 4)              # N4
          + Dc('0.8') * exp(Iv(Dc(-50))) * 11 * sgL * t ** 2 * 2 * sg * sg / (16 * sqrt(Iv(2)) * (1 - t))   # ring2 (1/B <= 2 sigma^2)
          + sg * sg * (1 + t) / 4                                                      # A2a (b <= 1)
          + shs * t ** 2 / (8 * sqrt(Iv(2)) * (1 - t))                                 # A2b (b <= 1)
          + sqrt(2 * P1) / 4 * (Dc('0.0895') * sg * sg + shs * t ** 2 / (2 * sqrt(Iv(2)) * (1 - t) ** 2)))   # B2b (b <= 1, P <= P1)
    cS = (1 + t) / (4 * sqrt(LC.PI)) + (Dc('0.184') + sg * sg) * Dc('0.2') / (2 * sqrt(LC.PI)) + t * t * (1 + Dc('0.5') * sg * sg) / (2 * sqrt(LC.PI) * 2 * (1 - t))
    eS = V.imax(2 * cS * shs * (1 + sg) / om, 2 * cS * shs)                            # (R3'): a <= 1 against P4z; a >= 1 against P1 (b <= 1)
    o['e_L'] = eL; o['e_S'] = eS; e2 = Dc('1e-12'); o['e2 - (e_L + e_S) (must be >= 0)'] = e2 - (eL + eS)
    R4 = (M4c + M4g) / 2 + Dc('0.0625') * Dc('2.07') * kE + sqrt(Iv(Dc('7.5'))) * kE * sqrt(P1) / 4 + Dc('1e-9'); o['R4\': constants/sigma'] = R4
    o['1.86 - R4\' (must be >= 0)'] = Dc('1.86') - R4
    KF = U1q * (Dc('0.375') * 2 / 3 / (1 - t) + sqrt(2 * P1) / (12 * (1 - t) ** 2)); o['R5\': K_F/(ell sigma)'] = KF; o['1 - K_F/(ell sigma) (must be >= 0)'] = 1 - KF
    q = (8 * t + 100 * t * t) * 2 * pe(1, L) * sg * (1 + t) / (8 * (1 - t))            # q = K^2 (1 + eta)/(8B(1 - eta)) <= (8 ell + 100) 2 sigma^2 (...)/8: tiny
    o['(d4 + N4G)/P2z / es_sigma (must be <= 1)'] = (1 + t) / (1 - q) * (gam / (2 * (1 - t)) * t ** 2 + Dc('1.5') * ((X1q * sgL + CZ * sg) / (2 * (1 - t)) + Dc('1.5') * sg / (32 * (1 - t))) * t ** 2)
    th = sqrt((1 - eps1 - e2) * (1 - epsh - e2) * om); o['th'] = th; o['k1'] = k1; o['k2'] = k2
    tail = (2 * sgL + Dc('0.5') * sg)                                                  # (2 ell + 1/2) sigma
    f1 = th - gam * k1 - gam * k2 * G - tail; fh = th * sqrt(Iv(Dc('0.5'))) - gam * k1 * Dc('0.5') - gam * k2 * G - tail
    o['Lambda_Fz lower bound at b = 1 (must be >= 0)'] = f1; o['Lambda_Fz lower bound at b = 1/2 (must be >= 0)'] = fh
    t0 = 1 / Iv(Dc('55.26'))                                                           # 1/Gam2 = 2 (1 - t)/sqrt((1 + 10 t) t) decreases in t: its smallest value is at ell = 55.26
    o['Case I: c1 sqrt(1/2)/Gam2 - P1/3 (must be > 0)'] = Dc('0.78') * sqrt(Iv(Dc('0.5'))) * 2 * (1 - t0) / sqrt((1 + 10 * t0) * t0) - G
    return o


def verdict(o):
    out = {}
    for k, v in o.items():
        if '(must be >= 0)' in k: out[k] = (bool(v.lo >= 0), float(v.lo))
        elif '(must be > 0)' in k: out[k] = (bool(v.lo > 0), float(v.lo))
        elif '(must be <= 1)' in k: out[k] = (bool(v.hi <= 1), float(v.hi))
    return out


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Fable 5.2 (claude-fable-5-2)'}
    o = trapped(consts)(); v = verdict(o)
    out['gamma = 0.6: conditions (ok, value)'] = v
    out['values (upper ends, or lower end for th)'] = {'P1': float(o["P1 (F1')"].hi), 'eps1_max': float(o['eps1_max'].hi), 'epsh_max': float(o['epsh_max'].hi), 'e_L': float(o['e_L'].hi), 'e_S': float(o['e_S'].hi),
                                                       'R4\'': float(o["R4': constants/sigma"].hi), 'K_F/(ell sigma)': float(o["R5': K_F/(ell sigma)"].hi), 'th (lower)': float(o['th'].lo), 'k1': float(o['k1'].hi), 'k2': float(o['k2'].hi)}
    out['quoted in the text'] = {'P1 <= 0.8829': bool(o["P1 (F1')"].hi <= Dc('0.8829')), 'eps1 <= 0.01457': bool(o['eps1_max'].hi <= Dc('0.01457')), 'eps_h <= 0.1808': bool(o['epsh_max'].hi <= Dc('0.1808')),
                                 'th >= 0.8984': bool(o['th'].lo >= Dc('0.8984')), 'k1 <= 1.0904': bool(o['k1'].hi <= Dc('1.0904')), 'k2 <= 0.50922': bool(o['k2'].hi <= Dc('0.50922'))}
    o72 = trapped(consts)('0.72'); out['gamma = 0.72: lower bounds at b = 1, 1/2 (both >= 0: the proof also gives 0.72)'] = [float(o72['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo), float(o72['Lambda_Fz lower bound at b = 1/2 (must be >= 0)'].lo)]
    o75 = trapped(consts)('0.75'); ocm = trapped(consts)('0.6', cm=False)
    out['power (each must be False)'] = {'gamma = 0.75: lower bound at b = 1 >= 0': bool(o75['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo >= 0),
                                         'no (CM) (P up to 1000): lower bound at b = 1 >= 0': bool(ocm['Lambda_Fz lower bound at b = 1 (must be >= 0)'].lo >= 0)}
    out['ok'] = bool(all(a for a, b in v.values()) and all(out['quoted in the text'].values()) and not any(out['power (each must be False)'].values())
                     and min(out['gamma = 0.72: lower bounds at b = 1, 1/2 (both >= 0: the proof also gives 0.72)']) >= 0)
    out['seconds'] = time.time() - t0
    if save: json.dump(out, open('results/dp_room2.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    print(json.dumps(run(), indent=1))
