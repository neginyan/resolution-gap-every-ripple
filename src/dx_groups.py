"""Stage DX, items 2.2 (FrB1) and 2.3: the 30 groups of dm_groups (lemma piece -> closed form -> elementary steps -> table) at eta = 1/4.  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  [numerical audit in decimal of written chains; not a proof]
(a) the published chains and table, with the ripple eta = 1/4 (dm_groups.run_ell with modify: q['eta'] = 1/4): which groups break (DU: FrB1, step 1).
(b) FrB1 with X1 -> X1_B1 = U1/(1 - eta_bar) + sqrt(CZ(eta_bar)) in the B1m term of the chain and in the table line B1m (the factor X1_B1/X1 depends on ell only):
    the steps 'c0hat <= X1_B1/sqrt2' (A <= 1, 1/(1 - eta) <= 1/(1 - eta_bar), CZ increasing) and 'c0hat^2 <= X1^2 + CZ' ((p + q)^2 <= 2p^2 + 2q^2) unchanged.
(c) power: (b) with the old X1 in the chain but the new table (the step fails), and (b) at eta = 0.3 > 1/4 (must break).
-> results_DX/dx_groups.json"""
import json, os, sys, time, inspect
from decimal import Decimal as Dc, localcontext
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dk_lemma as K, dk_table as T, dm_groups as M

SRC = inspect.getsource(M.chains)
R = [("        X1 = U1 / Dc('0.75'); CZ = eta ** 2 / (e * ome ** 2);",
      "        X1 = U1 / Dc('0.75'); CZ = eta ** 2 / (e * ome ** 2); EB = Dc(ETAB); X1B = U1 / (1 - EB) + (EB ** 2 / (e * (1 - EB) ** 2)).sqrt() if NEWC else X1;")]
SRC = SRC.replace(R[0][0], R[0][1], 1)
assert SRC.count('ss * (X1 / sq2) * mm') == 3
SRC = SRC.replace('ss * (X1 / sq2) * mm', 'ss * (X1B / sq2) * mm')
SRC = SRC.replace("'c0hat <= X1/sqrt2 (U1 (4/3 - 1/(1-eta)) >= sqrt(CZ), A <= 1)'", "'c0hat <= X1_B1/sqrt2 (A <= 1, eta <= eta_bar)'")
NS = dict(M.__dict__); NS['ETAB'] = '0.25'; NS['NEWC'] = True
exec(compile(SRC, 'dm_groups.chains (FrB1 with X1_B1)', 'exec'), NS); chains_new = NS['chains']
CH0 = M.chains


def _eta(v):
    def f(q, la, c):
        q['eta'] = Dc(v); return q, la
    return f


def b1m_factor(ell, c, etab=Dc('0.25')):
    with localcontext(c):
        U1 = T.QB * (2 * K.D(ell) + Dc('3.1')).sqrt() + Dc('1e-6'); X1 = U1 / (1 - T.QB)
        return str((U1 / (1 - etab) + (etab ** 2 / (Dc(1).exp() * (1 - etab) ** 2)).sqrt()) / X1)


def one(ell, eta, version, n, m, seed=11):
    """version: 'published' | 'X1_B1' | 'X1_B1 table, old chain'"""
    c = K.context(ell); T.WRONG.clear()
    if version != 'published': T.WRONG['scale'] = {'B1m': b1m_factor(ell, c)}
    M.chains = chains_new if version == 'X1_B1' else CH0
    try:
        r = M.run_ell(ell, n, m, seed=seed, modify=_eta(eta))
    finally:
        T.WRONG.clear(); M.chains = CH0
    fails = {g: {'failing points': v['failing points'], 'first failure': v['first failure']} for g, v in r['groups'].items() if v['failing points']}
    return {'points': r['points'], 'exceptions': r['number of exceptions'], 'first exceptions': r['exceptions'][:2], 'groups that fail': fails}


def run(ells=(55.26, 955.8, 1e6, 1e12), n=150, m=13):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    for ell in ells:
        for ver in ('published', 'X1_B1'):
            r = one(ell, '0.25', ver, n, m); out['%s ell=%g eta=1/4' % (ver, ell)] = r
            print(ver, ell, r['points'], r['exceptions'], {g: v['failing points'] for g, v in r['groups that fail'].items()}, round(time.time() - t0), flush=True)
    for ell in (55.26, 955.8):
        r = one(ell, '0.25', 'X1_B1 table, old chain', 60, 9); out['power: X1_B1 table, old chain step, ell=%g' % ell] = r
        r2 = one(ell, '0.3', 'X1_B1', 60, 9); out['power: X1_B1 at eta = 0.3, ell=%g' % ell] = r2
        print('power', ell, {g: v['failing points'] for g, v in r['groups that fail'].items()}, {g: v['failing points'] for g, v in r2['groups that fail'].items()}, flush=True)
    pub = [v for k, v in out.items() if k.startswith('published')]; new = [v for k, v in out.items() if k.startswith('X1_B1 ell')]
    out['published at eta = 1/4: groups that fail somewhere'] = sorted({g for v in pub for g in v['groups that fail']})
    out['X1_B1 at eta = 1/4: groups that fail somewhere (must be empty)'] = sorted({g for v in new for g in v['groups that fail']})
    out['power caught'] = {k: bool(v['groups that fail']) for k, v in out.items() if k.startswith('power')}
    out['ok'] = (not out['X1_B1 at eta = 1/4: groups that fail somewhere (must be empty)']) and all(v['exceptions'] == 0 for v in new) and all(out['power caught'].values())
    out['seconds'] = time.time() - t0
    return out


if __name__ == '__main__':
    r = run(); d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); os.makedirs(d, exist_ok=True)
    json.dump(r, open(os.path.join(d, 'dx_groups.json'), 'w'), indent=1, default=str); print(r['ok'], r['published at eta = 1/4: groups that fail somewhere'], r['seconds'])
