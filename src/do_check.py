"""Stage DO 1.1: the interval proofs re-run on the FIXED interval arithmetic (dl_interval: copy_negate, lq inside the context), with a machine check that no
decimal operation rounds outside the 40-digit context CTX.  Python 3.11 grammar.  DO_探索計画.md sections 1-2 (written before this ran).
THE CHECK: while an interval function runs, the DEFAULT decimal context traps Inexact.  The interval operations work in localcontext(CTX) (a copy of CTX,
whose traps are off), so they never raise; any operation that rounds in the default context raises decimal.Inexact.  (Exact operations, comparisons,
float() and Decimal(repr(float)) do not round and do not raise.)
  (T1) the fixed implementation: dl_consts.consts_iv + checks on four pieces (the first, near 1e5, the last below 1e6, the tail): no Inexact;
  (T2) POWER: the pre-DO implementation (verification/pre_DO/dl_interval.py, in a subprocess) on the same pieces: Inexact is raised;
  (R1) dl_consts.run (9,809 pieces and the tail) with every consts_iv and checks call trapped, and dl_consts.power;
  (R2) dl_review: the interval parts (far side, E_J >= E_CM, (b.5)) trapped, and its decimal part (C1, C2) as before;
  (R3) dm_appendix.run (E_J of (F4)) trapped;  (R4) the derivative of E_J on [0, 80] (dn_ivtest.monotone_EJ) trapped;
  (R5) comparison with the records of stage DN (computed on the defective arithmetic): the worst values agree to the rounding level.
ADDED AFTER THE FIRST RUN (DO_探索計画.md section 6, written before these ran): the first run stopped in (R2) at dl_review.ej_ge_ecm, t = Iv(0, 1/Dc('55.26')),
a division in the 28-digit default context (it rounded UP by 3.0e-30, so the enclosure of 1/ell held).  Fixed to t = Iv(0, (1/Iv(55.26)).hi).
  (T0) the trap set BEFORE importing cm_const, dl_interval, dl_consts, dl_review, dm_appendix, dn_ivtest (module-level constants): no Inexact;
  (T3) POWER: the pre-DO dl_review (verification/pre_DO/dl_review.py) raises Inexact in ej_ge_ecm, the fixed one does not;
       and the direction of that rounding, computed with 80 digits (the old t minus the true 1/55.26 must be >= 0 for the old record to be valid).
-> results/do_check.json, do_consts.json, do_consts_power.json, do_review.json, do_appendix.json"""
import json, os, subprocess, sys, time, functools
import decimal
from decimal import Decimal as Dc
import cm_const as CM
assert not CM.OLD, 'run with the corrected constant c_CM'
import dl_interval as V, dl_consts as LC, dl_review as RV, dm_appendix as AP, dn_ivtest as IT


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


PIECES = ((Dc('55.26'), Dc('55.26') * Dc('1.001')), (Dc('99900'), Dc('100000')), (Dc('999000'), Dc('1000000')), (Dc('1000000'), Dc('Infinity')))
CODE_OLD = r'''
import sys, decimal
sys.path.insert(0, %r)
import dl_interval as V; assert 'copy_negate' not in open(V.__file__).read(), V.__file__
sys.path.insert(1, %r)
import dl_consts as LC
from decimal import Decimal as Dc
ctx = decimal.getcontext(); ctx.traps[decimal.Inexact] = True
res = []
for a, b in ((Dc('55.26'), Dc('55.26') * Dc('1.001')), (Dc('1000000'), Dc('Infinity'))):
    try:
        LC.checks(LC.consts_iv(a, b)); res.append('no Inexact')
    except decimal.Inexact:
        res.append('Inexact raised')
print(res)
'''


def t1():
    out = {}
    for a, b in PIECES:
        try:
            trapped(lambda: LC.checks(LC.consts_iv(a, b)))(); out['[%s, %s]' % (a, b)] = 'no Inexact'
        except decimal.Inexact as e:
            out['[%s, %s]' % (a, b)] = 'Inexact raised'
    return out


def t2():
    here = os.path.dirname(os.path.abspath(__file__))
    p = subprocess.run([sys.executable, '-c', CODE_OLD % (os.path.join(here, 'verification', 'pre_DO'), here)], capture_output=True, text=True, cwd=here)
    return {'stdout': p.stdout.strip()[-200:], 'stderr': p.stderr.strip()[-300:], 'returncode': p.returncode}


CODE_T0 = r'''
import sys, decimal
sys.path.insert(0, %r)
decimal.getcontext().traps[decimal.Inexact] = True
res = {}
for m in ('cm_const', 'dl_interval', 'dl_consts', 'dl_review', 'dm_appendix', 'dn_ivtest'):
    try:
        __import__(m); res[m] = 'no Inexact'
    except decimal.Inexact:
        res[m] = 'Inexact raised'; break
print(res)
'''


def t0():
    here = os.path.dirname(os.path.abspath(__file__))
    p = subprocess.run([sys.executable, '-c', CODE_T0 % here], capture_output=True, text=True, cwd=here)
    return {'stdout': p.stdout.strip()[-400:], 'stderr': p.stderr.strip()[-300:], 'returncode': p.returncode}


def t3():
    import importlib.util
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location('dl_review_preDO', os.path.join(here, 'verification', 'pre_DO', 'dl_review.py'))
    old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
    assert "1 / Dc('55.26'))" in open(spec.origin).read()
    out = {}
    try:
        trapped(old.ej_ge_ecm)(); out['pre-DO ej_ge_ecm'] = 'no Inexact'
    except decimal.Inexact:
        out['pre-DO ej_ge_ecm'] = 'Inexact raised'
    try:
        trapped(RV.ej_ge_ecm)(); out['fixed ej_ge_ecm'] = 'no Inexact'
    except decimal.Inexact:
        out['fixed ej_ge_ecm'] = 'Inexact raised'
    old_t = Dc(1) / Dc('55.26')                                          # what the old line computed (default context, 28 digits)
    with decimal.localcontext(decimal.Context(prec=80)):
        d = old_t - Dc(1) / Dc('55.26')
    out['old t - 1/55.26 (80 digits; >= 0: the old interval [0, t] still enclosed 1/ell)'] = str(d)
    out['old record valid'] = bool(d >= 0)
    return out


def run(save=True):
    t0_ = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    out['(T0) the trap set before importing the interval modules'] = t0(); print('T0', out['(T0) the trap set before importing the interval modules'], flush=True)
    out['(T3) power: dl_review before and after the DO fix'] = t3(); print('T3', out['(T3) power: dl_review before and after the DO fix'], flush=True)
    out['(T1) fixed implementation, Inexact trapped in the default context'] = t1(); print('T1', out['(T1) fixed implementation, Inexact trapped in the default context'], flush=True)
    out['(T2) power: the pre-DO implementation, Inexact trapped'] = t2(); print('T2', out['(T2) power: the pre-DO implementation, Inexact trapped'], flush=True)
    keep = (LC.consts_iv, LC.checks)
    LC.consts_iv = trapped(keep[0]); LC.checks = trapped(keep[1])
    try:
        c = LC.run(save=False)
        if save: json.dump(c, open('results/do_consts.json', 'w'), indent=1)
        pw = LC.power(save=False)
        if save: json.dump(pw, open('results/do_consts_power.json', 'w'), indent=1)
    finally:
        LC.consts_iv, LC.checks = keep
    out['(R1) dl_consts.run ok'] = c['ok']; out['(R1) dl_consts.power ok'] = pw['ok']; print('R1', c['ok'], pw['ok'], round(c['seconds']), flush=True)
    keepr = (RV.far_side, RV.ej_ge_ecm, RV.b5_kappa)
    RV.far_side, RV.ej_ge_ecm, RV.b5_kappa = (trapped(f) for f in keepr)
    try:
        rv = RV.run(save=False)
        if save: json.dump(rv, open('results/do_review.json', 'w'), indent=1)
    finally:
        RV.far_side, RV.ej_ge_ecm, RV.b5_kappa = keepr
    out['(R2) dl_review ok'] = rv['ok']; print('R2', rv['ok'], flush=True)
    ap = trapped(AP.run)(save=False)
    if save: json.dump(ap, open('results/do_appendix.json', 'w'), indent=1)
    out['(R3) dm_appendix ok'] = ap['ok']; print('R3', ap['ok'], flush=True)
    ej = trapped(IT.monotone_EJ)(); out['(R4) dE_J/dmu < 0 on [0, 80]'] = ej; print('R4', ej, flush=True)
    dn = json.load(open('results/dn_consts.json')); wk = 'worst over [55.26, 1e6] (ok, value, at the left end of the piece)'
    dmax = 0.0
    for k in dn[wk]:
        x, y = dn[wk][k][1], c[wk][k][1]
        if x != y: dmax = max(dmax, abs(x - y) / max(abs(x), abs(y), 1e-300))
    out['(R5) largest relative difference of the worst values, fixed vs DN (defective) arithmetic'] = dmax
    dr = json.load(open('results/dn_review.json'))
    out['(R5) dl_review interval parts equal to DN at the printed digits'] = {k: (dr[k] == rv[k]) for k in ('(D) far side', '(G3) E_J >= E_CM', '(G2) (b.5) kappa_b mu < 1')}
    T0o = out['(T0) the trap set before importing the interval modules']['stdout']; T3o = out['(T3) power: dl_review before and after the DO fix']
    out['ok'] = bool('Inexact raised' not in T0o and T0o.count('no Inexact') == 6 and T3o['pre-DO ej_ge_ecm'] == 'Inexact raised'
                     and T3o['fixed ej_ge_ecm'] == 'no Inexact' and T3o['old record valid'] and all(v == 'no Inexact' for v in out['(T1) fixed implementation, Inexact trapped in the default context'].values())
                     and 'Inexact raised' in out['(T2) power: the pre-DO implementation, Inexact trapped']['stdout']
                     and c['ok'] and pw['ok'] and rv['ok'] and ap['ok'] and ej['ok'] and dmax < 1e-20)
    out['seconds'] = time.time() - t0_
    if save: json.dump(out, open('results/do_check.json', 'w'), indent=1)
    return out


if __name__ == '__main__':
    print(run()['ok'])
