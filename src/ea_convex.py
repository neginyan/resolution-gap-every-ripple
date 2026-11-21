"""Stage EA, item 1.3: THE LINE B1m OF PAPER J READ BY THE PARSER, with the repaired constant X1_B1(eta) = U1/(1 - eta) + sqrt(CZ(eta)) in it.
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
Paper J replaces, in the one line B1m, X1 = U1/(1 - Qb) by X1_B1(eta) (Sec. IV A).  The code of the interval proofs evaluates X1_B1 as a function of eta at each end
(dy_jsrc: X1Bn = u1n/(1 - et) + sqrt(CZ) sqrt(t)).  Here the source of dk_table.lines is transformed in exactly that way (one assignment added, X1 -> X1B1 in B1m only)
and given to the parser of dy_convex (the grammar of Lemma 5): B1m must be in the grammar (a loss of type P) and its basics, read from the code, are reported;
the other 36 lines must be read as in results_DY/dy_convex.json.
NUMBERS: the transformed B1m equals the published B1m times X1_B1(eta)/X1 at random states and eta in {0, 1/8, 1/4} (Decimal, 1e-40 relative), and it lies under
its chord in lam = 1/(1 + eta) on [4/5, 1] (201 points).
POWER: (q1) X1_B1 = U1 * (1 - eta) + sqrt(CZ) (1 - eta in a numerator) and (q2) X1_B1 = U1/(1 - eta) + sqrt(eta) must be caught by the grammar.
-> results_EA/ea_convex.json"""
import inspect, json, os, sys, time
from decimal import Decimal as Dc, localcontext
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dk_table as T, dk_lemma as K, dy_convex as C

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ADD = "X1 = U1 / (1 - QB); CZ = eta ** 2 / (Dc(1).exp() * ome ** 2); X1CZ = X1 ** 2 + CZ"
B1M = "'B1m': ('M', -1, Dc('1.5'), fF * X1 / (sq2 * sqpi * (2 + r).sqrt()) * (4 * r).sqrt()),"


def j_source(x1b1="U1 / ome + CZ.sqrt()"):
    src = inspect.getsource(T.lines)
    assert src.count(ADD) == 1 and src.count(B1M) == 1
    src = src.replace(ADD, ADD + "\n        X1B1 = " + x1b1)
    return src.replace(B1M, B1M.replace("fF * X1 /", "fF * X1B1 /"))


def main():
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    a = C.analyse(j_source())
    pub = json.load(open(os.path.join(ROOT, 'results_DY', 'dy_convex.json')))['inventory read from the code (line -> sign, type, sandwich, basics)']
    out['B1m of paper J read from the transformed code'] = a['B1m']
    out['B1m of paper I (results_DY/dy_convex.json)'] = pub['B1m']
    others = sorted(k for k in a if k != 'B1m' and a[k] != pub[k])
    out['other lines read differently (must be empty)'] = others
    out['lines'] = len(a)
    pw = {}
    for nm, x in (('(q1) U1 * (1 - eta) + sqrt(CZ)', 'U1 * ome + CZ.sqrt()'), ('(q2) U1/(1 - eta) + sqrt(eta)', 'U1 / ome + eta.sqrt()')):
        b = C.analyse(j_source(x))['B1m']; pw[nm] = {'read as': b, 'caught': not b['grammar ok']}
    out['power'] = pw
    # numbers: the transformed line against the published one, and the chord
    ns = {}
    exec(compile(j_source().replace('def lines(', 'def lines_J(', 1), 'j', 'exec'), T.__dict__, ns)
    rng = np.random.default_rng(11); worst = Dc(0); chord_min = None
    with localcontext() as c:
        c.prec = 60
        for i in range(12):
            st = dict(ell=Dc(str(round(55.26 + 900 * rng.random(), 3))), r=Dc(str(10 ** (-6 * rng.random()) / 4)), B=Dc(str(10 ** (10.4 + 5 * rng.random()))),
                      kap=Dc(str(rng.random() * 3)), P=Dc(str(rng.random() * 0.8)), mu=Dc(str(1 + 20 * rng.random())), b=Dc(str(10 ** (-30 * rng.random()))))
            st['kE'] = Dc('0.2').sqrt(); st['gs'] = (st['r'] / (2 + st['r'])).sqrt()
            vals = []
            for k in range(201):
                lam = Dc(4) / 5 + Dc(k) / 1000; eta = 1 / lam - 1
                q = dict(st, eta=eta)
                cJ = ns['lines_J'](q, c, Dc('0.4'))
                cJ = (cJ[0] if isinstance(cJ, tuple) else cJ)['B1m'][3]
                if k in (0, 100, 200):
                    cI = T.lines(q, c, Dc('0.4')); cI = (cI[0] if isinstance(cI, tuple) else cI)['B1m'][3]
                    U1 = Dc('0.25') * (2 * q['ell'] + Dc('3.1')).sqrt() + Dc('1e-6'); X1 = U1 / (1 - Dc('0.25'))
                    CZ = eta ** 2 / (Dc(1).exp() * (1 - eta) ** 2); ratio = (U1 / (1 - eta) + CZ.sqrt()) / X1
                    worst = max(worst, abs(cJ / (cI * ratio) - 1))
                vals.append(cJ)
            for k in range(201):
                lam = Dc(4) / 5 + Dc(k) / 1000; ch = vals[200] + (vals[0] - vals[200]) * 5 * (1 - lam)
                m = (ch - vals[k]) / vals[0]; chord_min = m if chord_min is None or m < chord_min else chord_min
    out['numbers: largest |B1m_J / (B1m_I X1_B1/X1) - 1|'] = float(worst)
    out['numbers: smallest (chord - value)/value at eta = 1/4 (must be >= -1e-40)'] = float(chord_min)
    out['ok'] = bool(a['B1m']['grammar ok'] and a['B1m']['type'] == 'P' and 'sqrt(CZ)' in a['B1m']['basics'] and not others and len(a) == 37
                     and all(v['caught'] for v in pw.values()) and worst < Dc('1e-40') and chord_min >= Dc('-1e-40'))
    out['seconds'] = time.time() - t0
    os.makedirs(os.path.join(ROOT, 'results_EA'), exist_ok=True)
    json.dump(out, open(os.path.join(ROOT, 'results_EA', 'ea_convex.json'), 'w'), indent=1, default=str)
    print(json.dumps(out, indent=1, default=str))
    return out


if __name__ == '__main__':
    main()
