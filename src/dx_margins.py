"""Stage DX, item 2.4: the rule constants of paper J and the margins at the two ends  [numerical estimate; not a proof].  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).
Ends: A = (lam = 1, coefficient 1), B = (lam = 4/5, coefficient lam/Upsilon = 3/5, eta = 1/4); stress row S = gains at 3/5 with the remainders at 1/4.
Modes: 'uniform' (every remainder at eta_bar = 1/4 at both ends; the form asked in DX 2.2) and 'chord' (remainders under their chord in lam: eta = 0 at A).
The constants of the proof that are not the rule's (A2C = the 2.1 of (R7)/(m3)/(m4)) are taken per end as the needed value rounded up to 0.1.
-> results_DX/dx_margins.json"""
import json, math, os, sys, time
from decimal import Decimal as Dc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dx_consts as X
import dl_consts as LC

ENDS = {'uniform': {'A': ('1', '0.25'), 'B': ('0.8', '0.25'), 'S': ('0.6', '0.25')},
        'chord': {'A': ('1', '0'), 'B': ('0.8', '0.25'), 'S': ('0.6', '0.25')}}
ELLS4 = ('55.26', '960.8', '10000', '1000000')
WORRY = ['Case I (Fz): c1F - K_F/sqrt(b) - c1 (must be >= 0)', 'Case I (Tz-B2): [(1 - a2k - 1e-6) cK c_T sqrt(ell) - c_B2]/sqrt(ell) (must be >= 0)',
         'II-ch: slack (must be >= 0)', 'II-s: slack (must be >= 0)']


def mg(k, v):
    """the margin of a condition (>= 0 when it holds): the value for '>= 0' and '> 0', the room below the bound for '<= 1' and '<= 1.002'"""
    return (1.002 - v) if '<= 1.002' in k else ((1 - v) if '<= 1)' in k else v)


def dense(n=60):
    a, b = math.log(55.26), math.log(1e6)
    return ['55.26'] + ['%.6g' % math.exp(a + (b - a) * i / (n - 1)) for i in range(1, n)]


def a2c_for(ell, lam, et, mode, rule):
    o, e = X.point(ell, lam, etab=Dc(et), mode=mode, **rule)
    if e or 'kf (Case II)' not in o: return Dc('2.1')
    need = X.a2c_needed(o, lam, Dc(et) if Dc(et) > 0 else Dc(0))
    return Dc(math.ceil(need * 10)) / 10


def evaluate(ell, end, mode, rule, a2c=None):
    lam, et = ENDS[mode][end]
    if a2c is None: a2c = a2c_for(ell, lam, et, mode, rule)
    o, e = X.point(ell, lam, etab=Dc(et), mode=mode, A2C=a2c, **rule)
    return o, e, X.checks(o), a2c


def scan(mode, ells=('55.26', '960.8'), ends=('A', 'B')):
    best = None; rows = []
    for c1 in [Dc(x) / 100 for x in range(60, 80)]:
        for cch in [Dc(x) / 10 for x in range(12, 25)]:
            for ct in (Dc('5'), Dc('6.5'), Dc('8')):
                rule = {'C1': c1, 'CT': ct, 'CCH': cch}; v = 9.0
                for ell in ells:
                    for end in ends:
                        o, e, c, _ = evaluate(ell, end, mode, rule)
                        v = min(v, -9.0 if e else min(mg(k, x) for k, (ok, x) in c.items()))
                rows.append((v, str(c1), str(cch), str(ct)))
                if best is None or v > best[0]: best = (v, str(c1), str(cch), str(ct))
    rows.sort(reverse=True)
    return best, rows[:10]


def table(mode, rule, ells=ELLS4):
    out = {}
    for end in ('A', 'B', 'S'):
        for ell in ells:
            o, e, c, a2c = evaluate(ell, end, mode, rule)
            out['%s ell=%s' % (end, ell)] = {'error': e, 'A2C used': str(a2c), 'failing': [k for k, (ok, v) in c.items() if not ok],
                                             'worry margins': {k: c[k][1] for k in WORRY if k in c}, 'min margin over all conditions': min((mg(k, v) for k, (ok, v) in c.items()), default=None),
                                             'all conditions': {k: v for k, (ok, v) in c.items()}}
    return out


def quoted(mode, rule, ells):
    """the 48 quoted bounds of paper I: the J value (worst over the ell grid and the ends A, B) and whether the old bound still holds"""
    res = {}
    for k, s, b in LC.QUOTED:
        worst = None; where = None
        for end in ('A', 'B'):
            for ell in ells:
                o, e, c, a2c = evaluate(ell, end, mode, rule)
                if k not in o: continue
                v = float(o[k].hi) if s == '<=' else float(o[k].lo)
                if worst is None or (v > worst if s == '<=' else v < worst): worst, where = v, (end, ell)
        if worst is None: res[k] = {'sense': s, 'paper I bound': b, 'J worst': None}; continue
        old_ok = worst <= float(b) if s == '<=' else worst >= float(b)
        dig = 4; e10 = math.floor(math.log10(abs(worst))) if worst != 0 else 0; sc = 10 ** (e10 - dig + 1)
        prop = (math.ceil(worst / sc) * sc) if s == '<=' else (math.floor(worst / sc) * sc)
        res[k] = {'sense': s, 'paper I bound': b, 'J worst': worst, 'at': where, 'paper I bound still holds': old_ok, 'proposed J bound (4 digits, outward)': float('%.4g' % prop)}
    return res


def run():
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'status': 'numerical estimate (interval arithmetic read at points); not a proof',
                             'python': sys.version.split()[0]}
    for mode in ('uniform', 'chord'):
        best, top = scan(mode); out[mode + ': best rule on ell = 55.26, 960.8 (min over every condition, both ends)'] = best
        out[mode + ': top 10'] = top
    # the DU starting point and the chosen rule
    du = {'C1': Dc('0.62'), 'CT': Dc('6.5'), 'CCH': Dc('1.7')}
    b = out['chord: best rule on ell = 55.26, 960.8 (min over every condition, both ends)']
    rule = {'C1': Dc(b[1]), 'CT': Dc(b[3]), 'CCH': Dc(b[2])}
    out['chosen rule (chord)'] = {k: str(v) for k, v in rule.items()}
    for mode in ('uniform', 'chord'):
        out['table %s, DU rule (c1 0.62, c_T 6.5, c_ch 1.7)' % mode] = table(mode, du)
    bu = out['uniform: best rule on ell = 55.26, 960.8 (min over every condition, both ends)']
    out['table uniform, its best rule'] = table('uniform', {'C1': Dc(bu[1]), 'CT': Dc(bu[3]), 'CCH': Dc(bu[2])})
    out['table chord, chosen rule'] = table('chord', rule)
    # dense ell grid, chord + chosen rule: every condition at both ends
    dn = dense(); bad = []; mins = {}
    for end in ('A', 'B'):
        for ell in dn:
            o, e, c, a2c = evaluate(ell, end, 'chord', rule)
            if e: bad.append((end, ell, e)); continue
            for k, (ok, v) in c.items():
                if not ok: bad.append((end, ell, k))
                if k not in mins or mg(k, v) < mins[k][0]: mins[k] = (mg(k, v), end, ell)
    out['chord, chosen rule, dense grid (60 ell from 55.26 to 1e6, ends A and B): failing (must be empty)'] = bad
    out['chord, chosen rule, dense grid: smallest margin of each condition (margin, end, ell)'] = mins
    out['quoted 48 (chord, chosen rule, dense grid)'] = quoted('chord', rule, dn)
    out['seconds'] = time.time() - t0
    return out


if __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dx_margins.json'), 'w'), indent=1, default=str)
    for k in r:
        if 'best' in k or 'chosen' in k or 'failing' in k: print(k, r[k])
    print('seconds', r['seconds'])
