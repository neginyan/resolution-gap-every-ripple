"""Stage DX, items 2.2 and 2.3: THE LINES OF PAPER J (decimal) and their audit against the lemma at eta <= 1/4.  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  [numerical audit in decimal; not a proof]
lines_J(q, c, gam, lam, etr, mode, x1new): the 37 lines of dk_table with
  - every remainder at etr (mode 'uniform': etr = 1/4 at both ends; mode 'chord': etr = 0 at lam = 1 and 1/4 at lam = 4/5);
  - the sandwich: the gains P2z, hFz, cKz carry lam in place of 1/(1 + eta) (chord: lam ringf >= lam - (1 - ringf) for P2z);
    the target is (lam/Upsilon) gamma den with lam/Upsilon = 2 lam - 1:  d2, d4 -> lam gamma G/2 ...,  d1 -> (2 lam - 1) k1 (uniform) or
    (2 lam - 1)(1 + 0.184 k_E) + etr k_E (chord),  d3 -> (2 lam - 1)(1 + 2 etr k_E)/4 (uniform) or ((2 lam - 1) + 2 etr k_E)/4 (chord);
  - FrB1 (x1new): the B1m line with X1_B1 = U1/(1 - etr) + sqrt(CZ(etr)) in place of X1 = (4/3) U1.
Every coefficient is affine in lam (uniform: lam and 2 lam - 1 times constants; chord: the line at lam is the interpolation of the two end lines).
The audit (run_audit): states and a-grids of dk_audit.sample/a_grid; the lemma (dk_lemma.pieces) at the ripple eta with the target
gamma (1 - eta)/(1 + eta) and lam = 1/(1 + eta); the J table at that lam; (L) every group, (S) every option total."""
import json, math, os, sys, time
from decimal import Decimal as Dc, localcontext
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dk_lemma as K, dk_table as T, dk_audit as AU

ETB = Dc('0.25'); LAM_B = Dc('0.8')
WRONG = {}     # 'forget eta' (remainders at 1/ell), 'old X1' (x1new off), 'target 1' (lemma target not scaled: the claim with coefficient 1), 'lam on remainders'


def lines_J(q, c, gam, lam, etr, mode='uniform', x1new=True):
    W_ = WRONG.get
    with localcontext(c):
        lam = Dc(lam); etr = Dc(etr); qq = dict(q); qq['eta'] = (1 / q['ell']) if W_('forget eta') else etr
        TT, brk = T.lines(qq, c, gam); e = qq['eta']; kE = q['kE']; fle = 1 / (1 + e)
        def sc(k, f):
            t, s, p, cc = TT[k]; TT[k] = (t, s, p, cc * f)
        # the gains: fl(etr) -> lam
        if mode == 'chord':
            Kz2 = 8 * q['ell'] + 100; ringf = 1 - Kz2 * (1 + e) / (8 * (1 - e) * q['B'])
            sc('P2z', (lam - (1 - ringf)) / (ringf * fle) if ringf != 0 else Dc(0))
        else:
            sc('P2z', lam / fle)
        sc('hFz', lam / fle); sc('cKz', lam / fle)
        # the target
        k1 = 1 + (e + Dc('0.184')) * kE
        if mode == 'chord':
            sc('d1', ((2 * lam - 1) * (1 + Dc('0.184') * kE) + e * kE) / k1); sc('d3', ((2 * lam - 1) + 2 * e * kE) / (1 + 2 * e * kE))
        else:
            sc('d1', 2 * lam - 1); sc('d3', 2 * lam - 1)
        sc('d2', lam * (1 - e)); sc('d4', lam * (1 - e))
        # FrB1
        if x1new and not W_('old X1'):
            U1 = T.QB * (2 * q['ell'] + Dc('3.1')).sqrt() + Dc('1e-6'); X1 = U1 / (1 - T.QB); CZ = e ** 2 / (Dc(1).exp() * (1 - e) ** 2)
            sc('B1m', (U1 / (1 - e) + CZ.sqrt()) / X1)
    return TT, brk


def lines_at(q, c, gam, lam, mode, x1new=True):
    """the J lines at lam: uniform -> lines_J(lam, 1/4); chord -> the interpolation of the two end lines (affine in lam)."""
    with localcontext(c):
        lam = Dc(lam)
        if mode == 'uniform': return lines_J(q, c, gam, lam, ETB, 'uniform', x1new)
        A, brk = lines_J(q, c, gam, Dc(1), Dc(0), 'chord', x1new); B, _ = lines_J(q, c, gam, LAM_B, ETB, 'chord', x1new)
        w = (lam - LAM_B) / (1 - LAM_B); out = {}
        for k in A:
            ta, sa, pa, ca = A[k]; tb, sb, pb, cb = B[k]; assert (ta, sa, pa) == (tb, sb, pb)
            out[k] = (ta, sa, pa, w * ca + (1 - w) * cb)
        return out, brk


def affinity(n=40, seed=5, ells=(55.26, 960.8, 1e6)):
    """(B1): for the uniform form, every coefficient at lam in {0.8, 0.85, 0.93} equals the interpolation of lam = 0.8 and lam = 1 (relative 1e-40);
    and a wrong version (a coefficient with lam^2) is caught."""
    res = {}; worst = Dc(0); worst_w = Dc(0)
    for ell in ells:
        rng = np.random.default_rng(seed); st_, fam = AU.sample(ell, rng, n); c = K.context(ell); gam = AU.gamma(ell, c)
        for st in st_:
            q = K.state(ell, *st, c)
            with localcontext(c):
                L1, _ = lines_J(q, c, gam, 1, ETB); L0, _ = lines_J(q, c, gam, LAM_B, ETB)
                for lam in (Dc('0.85'), Dc('0.93'), Dc('0.6')):
                    Lm, _ = lines_J(q, c, gam, lam, ETB); w = (lam - LAM_B) / (1 - LAM_B)
                    for k in Lm:
                        x = Lm[k][3]; y = w * L1[k][3] + (1 - w) * L0[k][3]; s_ = max(abs(x), abs(y))
                        if s_ > 0: worst = max(worst, abs(x - y) / s_)
                        if k == 'hFz':          # the wrong version: hFz with lam^2
                            xw = x * lam; s2 = max(abs(xw), abs(y))
                            if s2 > 0: worst_w = max(worst_w, abs(xw - y) / s2)
    res['largest relative deviation from affinity (uniform; lam = 0.85, 0.93, 0.6)'] = float(worst)
    res['wrong version hFz x lam (lam^2): largest deviation'] = float(worst_w)
    res['ok'] = bool(worst < Dc('1e-40') and worst_w > Dc('1e-3'))
    return res


def eval_J(ell, st, la, c, gam, eta, mode, x1new=True, pre=None):
    with localcontext(c):
        eta = Dc(eta); lam = 1 / (1 + eta)
        if pre is None:
            q = K.state(ell, *st, c, eta=eta)
            q['gam'] = gam if WRONG.get('target 1') else gam * (1 - eta) / (1 + eta)
            TT, brk = lines_at(q, c, gam, lam, mode, x1new)
        else:
            q, TT, brk = pre
        o, tot, alt, scale = K.pieces(q, la, c); sig = q['sig']; V = {k: T.value(TT, k, la, sig, c) for k in TT}
        res = {'groups': {}, 'tot': {}}
        for name, tags, kind, f in AU.GROUPS:
            l = f(o) * (q['gam'] if kind == 'den' else 1); t = sum(V[k] for k in tags)
            if kind != 'gain': t = -t
            if l == 0: res['groups'][name] = (None, t == 0 or kind != 'gain'); continue
            rt = t / l; ok = (rt <= 1 + AU.TOL) if kind == 'gain' else (rt >= 1 - AU.TOL)
            res['groups'][name] = (rt, ok)
        for k, tags in T.OPT.items():
            if k.startswith('Tz') and not brk > 0: continue
            if k not in tot: res['tot'][k] = (None, False); continue
            lamk = sum(V[t] for t in T.SHARED + tags); d = (tot[k] - lamk) / scale; res['tot'][k] = (d, d >= -AU.TOL)
    return res, (q, TT, brk)


def audit(ell, eta, mode, n=200, m=13, seed=3, x1new=True):
    rng = np.random.default_rng(seed + int(ell) % 100000); states, fam = AU.sample(ell, rng, n); c = K.context(ell); gam = AU.gamma(ell, c)
    G = {nm: {'min': None, 'viol': 0, 'first': None} for nm, *_ in AU.GROUPS}; S = {k: {'min': None, 'viol': 0, 'first': None} for k in T.OPT}; npts = 0; exc = []
    for i, st in enumerate(states):
        try:
            pre = None
            for la in AU.a_grid(ell, st[1], st[2], c, m):
                res, pre = eval_J(ell, st, la, c, gam, eta, mode, x1new, pre); npts += 1
                for nm, (rt, ok) in res['groups'].items():
                    g = G[nm]
                    if rt is not None and (g['min'] is None or rt < g['min']): g['min'] = rt
                    if not ok:
                        g['viol'] += 1
                        if g['first'] is None: g['first'] = {'family': fam[i], 'state': [str(x)[:12] for x in st], 'la': str(la)[:14], 'ratio': str(rt)[:14]}
                for k, (d, ok) in res['tot'].items():
                    s = S[k]
                    if d is not None and (s['min'] is None or d < s['min']): s['min'] = d
                    if not ok:
                        s['viol'] += 1
                        if s['first'] is None: s['first'] = {'family': fam[i], 'state': [str(x)[:12] for x in st], 'la': str(la)[:14], 'diff': str(d)[:14]}
        except Exception as ex:
            exc.append({'family': fam[i], 'error': repr(ex)[:160]})
    f = lambda x: None if x is None else float(x)
    out = {'ell': ell, 'eta': str(eta), 'mode': mode, 'points': npts, 'exceptions': len(exc), 'first exceptions': exc[:2],
           'groups with violations': {nm: {'violations': g['viol'], 'first': g['first']} for nm, g in G.items() if g['viol']},
           'smallest group ratio (losses/den: table/lemma, must be >= 1; gains: must be <= 1)': {nm: f(g['min']) for nm, g in G.items()},
           'totals with violations': {k: {'violations': s['viol'], 'first': s['first']} for k, s in S.items() if s['viol']},
           'totals: min (Phi - Lambda_J)/scale': {k: f(s['min']) for k, s in S.items()}}
    out['ok'] = not out['groups with violations'] and not out['totals with violations'] and not exc
    return out


def run(ells=(55.26, 960.8, 1e4, 1e6, 1e12), etas=('1/ell', '0.05', '0.15', '0.25'), n=200, m=13):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)', 'affinity (B1)': affinity()}
    print('affinity', out['affinity (B1)'], flush=True)
    for mode in ('uniform', 'chord'):
        for ell in ells:
            for et in etas:
                eta = (Dc(1) / Dc(ell)) if et == '1/ell' else Dc(et)
                r = audit(ell, eta, mode, n, m); out['%s ell=%g eta=%s' % (mode, ell, et)] = r
                print(mode, ell, et, r['points'], r['ok'], list(r['groups with violations'])[:3], list(r['totals with violations'])[:3], round(time.time() - t0), flush=True)
    out['ok'] = all(v['ok'] for k, v in out.items() if isinstance(v, dict) and 'ok' in v)
    out['seconds'] = time.time() - t0
    return out


POWER = {'forget eta (remainders at 1/ell), lemma at eta = 1/4': {'forget eta': True},
         'old X1 in B1m (x1new off)': {'old X1': True},
         'target with coefficient 1 (not lam/Upsilon)': {'target 1': True},
         'dk_table P2z x1.01': {'T': 'P2z x1.01'}, 'dk_table N1 x0.99': {'T': 'N1 x0.99'}, 'dk_table B2c x0.99': {'T': 'B2c x0.99'},
         'dk_table FrB1 x 0.9/1.2936': {'Tscale': {k: '0.6957' for k in ('B1m', 'B1c', 'B1l', 'uB2c', 'uB2s')}}}


def power(ells=(55.26, 960.8), n=60, m=9):
    out = {}
    for nm, w in POWER.items():
        WRONG.clear(); T.WRONG.clear()
        for k, v in w.items():
            if k == 'T': T.WRONG[v] = True
            elif k == 'Tscale': T.WRONG['scale'] = v
            else: WRONG[k] = v
        try:
            r = {}
            for mode in ('uniform', 'chord'):
                for ell in ells:
                    a = audit(ell, Dc('0.25'), mode, n, m, seed=17)
                    r['%s %g' % (mode, ell)] = sum(v['violations'] for v in a['groups with violations'].values()) + sum(v['violations'] for v in a['totals with violations'].values())
        finally:
            WRONG.clear(); T.WRONG.clear()
        out[nm] = {'violations (mode ell)': r, 'caught': any(v > 0 for v in r.values())}
        print('power', nm, r, flush=True)
    # expected NOT to be caught here: the old X1 in B1m keeps every group total valid (the FrB1 group has its own slack, smallest ratio 1.29 in paper I);
    # it breaks the written step 'c0hat <= X1/sqrt2' of the chain, which dx_groups.py checks (there it is caught)
    NOT_HERE = ('old X1 in B1m (x1new off)',)
    out['expected not visible to this audit (checked by dx_groups)'] = list(NOT_HERE)
    out['ok'] = all(v['caught'] for k, v in out.items() if isinstance(v, dict) and k not in NOT_HERE)
    return out


if __name__ == '__main__':
    d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'results_DX'); os.makedirs(d, exist_ok=True)
    if len(sys.argv) > 1 and sys.argv[1] == 'power':
        r = power(); json.dump(r, open(os.path.join(d, 'dx_table_power.json'), 'w'), indent=1, default=str); print(r['ok'])
    else:
        r = run(); json.dump(r, open(os.path.join(d, 'dx_table.json'), 'w'), indent=1, default=str); print(r['ok'], r['seconds'])
