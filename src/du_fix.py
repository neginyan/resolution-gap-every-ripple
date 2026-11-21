"""Stage DU (addendum, section 2): a number written into the interval proof of Theorems 2 and 4 was below its true value, corrected and re-run.  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).

FOUND (the census of 'numerical' constants, DU addendum section 2).  Step (b.1), first pass, of the proof of Theorem 2 (dl_consts.consts_iv, line 74 of its source)
writes two numbers into the formulas:  mu P <= 14.29  and  mu b/2 <= 9.545 c_b,  where P <= min(mu/8, 9 mu e^{-0.4 mu}) and b < c_b P^2.
  Proof of the right values: phi1(mu) := mu min(mu/8, 9 mu e^{-0.4 mu}) and phi2(mu) := (mu/2) min(mu/8, 9 mu e^{-0.4 mu})^2.  The first argument of min increases,
  the second, 9 mu e^{-0.4 mu}, is the smaller one exactly for mu >= mu* := ln(72)/0.4 = 10.6917 (where they are equal), and mu^2 e^{-0.4 mu}, mu^3 e^{-0.8 mu}
  decrease for mu >= 5 and mu >= 3.75.  So both sups are attained at mu*:  sup phi1 = mu*^2/8 = 14.28897 <= 14.29  (correct),
  sup phi2 = mu*^3/128 = 9.54831  >  9.545  (the written number is 3.3e-3 too small).  The pass needs mu b/2 <= phi2 c_b; with 9.545 the bound is not proved.
CORRECTION.  9.545 -> 9.549 (>= mu*^3/128, checked here in interval arithmetic), nothing else changed.  The patched source of dl_consts is loaded as the module
dl_consts (a copy in a temporary folder; the original file is not changed, so the records of the earlier stages stay valid), and the two interval proofs that
contain the line are run again with the watch of stage DO (decimal.Inexact trapped):
  (A) Theorem 2 (DJ-T):   dl_consts.run on the 9,809 pieces of [55.26, 1e6] and the tail;
  (B) Theorem 4 (DP-1a):  dq_room1_low.run (dp_room1 with B_1 = 8 ell + 100) on the 6,952 pieces of [960.8, 1e6] and the tail, with its power check.
The smallest margins are compared with the stored records (results/dl_consts.json, results/dq_room1_low.json).
-> results/du_fix.json"""
import json, os, sys, time, tempfile, importlib.util, functools, decimal, shutil
from decimal import Decimal as Dc
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); os.chdir(HERE)


def trapped(fn):
    @functools.wraps(fn)
    def w(*a, **k):
        ctx = decimal.getcontext(); old = ctx.traps[decimal.Inexact]; ctx.traps[decimal.Inexact] = True
        try: return fn(*a, **k)
        finally: ctx.traps[decimal.Inexact] = old
    return w


@trapped
def sups():
    from dl_interval import Iv, log, exp
    mus = log(Iv(72)) / Iv(Dc('0.4'))
    s1 = mus * mus / 8; s2 = mus * mus * mus / 128
    # the crossing: mu/8 = 9 mu e^{-0.4 mu} at mu*; the monotonicity facts (derivatives): d/dmu ln(mu^2 e^{-0.4 mu}) = 2/mu - 0.4 < 0 for mu > 5;
    # d/dmu ln(mu^3 e^{-0.8 mu}) = 3/mu - 0.8 < 0 for mu > 3.75;  mu* > 5
    return {'mu* = ln 72/0.4 in': [float(mus.lo), float(mus.hi)], 'mu* > 5': bool(mus.lo > 5),
            'sup mu P = mu*^2/8 <=': float(s1.hi), '14.29 is an upper bound': bool(s1.hi <= Dc('14.29')),
            'sup (mu/2) P^2 = mu*^3/128 in': [float(s2.lo), float(s2.hi)], '9.545 is an upper bound (it is NOT)': bool(s2.hi <= Dc('9.545')),
            '9.549 is an upper bound': bool(s2.hi <= Dc('9.549'))}


def load_patched():
    src = open(os.path.join(HERE, 'dl_consts.py'), encoding='utf-8').read()
    old = "Dc('9.545') * cbl"; assert src.count(old) == 1
    tmp = tempfile.mkdtemp(prefix='du_fix_'); p = os.path.join(tmp, 'dl_consts.py')
    open(p, 'w', encoding='utf-8').write(src.replace(old, "Dc('9.549') * cbl"))
    spec = importlib.util.spec_from_file_location('dl_consts', p); mod = importlib.util.module_from_spec(spec)
    sys.modules['dl_consts'] = mod; spec.loader.exec_module(mod)
    return mod, tmp


def margins(rec):
    """the smallest/largest values per condition from a dl_consts-like record (whatever the keys are), for comparison."""
    out = {}
    for k in ('worst', 'smallest margins', 'worst values', 'minima'):
        if k in rec: out[k] = rec[k]
    return out


def run(save=True):
    t0 = time.time(); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    out['(0) the two sups'] = sups(); print(out['(0) the two sups'], flush=True)
    LC, tmp = load_patched()
    try:
        out['(0) the patched module is the one in use'] = bool("Dc('9.549')" in open(LC.__file__, encoding='utf-8').read() and sys.modules['dl_consts'] is LC)
        keep = (LC.consts_iv, LC.checks); LC.consts_iv = trapped(keep[0]); LC.checks = trapped(keep[1])
        try: rA = LC.run(save=False)
        finally: LC.consts_iv, LC.checks = keep
        out['(A) Theorem 2 (DJ-T), corrected constant: ok'] = bool(rA.get('ok')); out['(A) record'] = rA
        print('A', rA.get('ok'), round(time.time() - t0), flush=True)
        # dp_room1 (imported by dq_room1_low) traps every piece itself
        import dq_room1_low as DQL                 # imports dp_room1, which reads the source of the patched dl_consts.consts_iv
        import dp_room1 as RM
        out['(0) dp_room1 uses the patched source'] = bool("9.549" in RM.SRC and "9.545" not in RM.SRC)
        rB = DQL.run(save=False); out['(B) Theorem 4 (DP-1a, B_1 = 8 ell + 100), corrected constant: ok'] = bool(rB.get('ok')); out['(B) record'] = rB
        print('B', rB.get('ok'), round(time.time() - t0), flush=True)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    s = out['(0) the two sups']
    out['ok'] = bool(s['mu* > 5'] and s['14.29 is an upper bound'] and not s['9.545 is an upper bound (it is NOT)'] and s['9.549 is an upper bound']
                     and out['(0) the patched module is the one in use'] and out['(0) dp_room1 uses the patched source']
                     and out['(A) Theorem 2 (DJ-T), corrected constant: ok'] and out['(B) Theorem 4 (DP-1a, B_1 = 8 ell + 100), corrected constant: ok'])
    out['seconds'] = time.time() - t0; print('ok', out['ok'], round(out['seconds']))
    if save: json.dump(out, open(os.path.join(HERE, 'results', 'du_fix.json'), 'w'), indent=1, default=str)
    return out


if __name__ == '__main__':
    sys.exit(0 if run()['ok'] else 1)
