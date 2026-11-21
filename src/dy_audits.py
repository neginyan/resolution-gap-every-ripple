"""Stage DY, item 2.4 (the part left in DX): the audits of paper I, dk_audit (lines against lemmas, 12 ell, n = 1500, m = 25) and dm_groups (the 30 groups),
re-run FROM SCRATCH with the eta-separated code of this stage at eta = 1/ell (the default), and compared with the published records results/dk_audit.json and
results/dm_groups.json by the published common.py (floats to 1e-9 relative, both <= 1e-6 equal; everything else exactly).  Python 3.11 grammar.
Model: Claude Opus 5.5 (claude-opus-5-5).  The runs are made in a temporary copy of the work tree (src/, results/ without the two records, verification/).
    python3 src/dy_audits.py  -> results_DY/dy_audits.json"""
import json, os, shutil, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def main():
    t0 = time.time(); T = tempfile.mkdtemp(prefix='dy_audits_'); out = {'model': 'Claude Opus 5.5 (claude-opus-5-5)'}
    for d in ('src', 'results', 'verification'):
        shutil.copytree(os.path.join(ROOT, d), os.path.join(T, d), ignore=shutil.ignore_patterns('__pycache__'))
    for f in ('dk_audit.json', 'dm_groups.json'): os.remove(os.path.join(T, 'results', f))
    env = dict(os.environ); env['PYTHONPATH'] = os.pathsep.join([os.path.join(T, 'src')] + [p for p in env.get('PYTHONPATH', '').split(os.pathsep) if p])
    sys.dont_write_bytecode = True; sys.path.insert(0, os.path.join(ROOT, 'verification')); import common as CMN
    for name, args, rec in (('dk_audit', ['run'], 'dk_audit.json'), ('dm_groups', [], 'dm_groups.json')):
        t1 = time.time(); p = subprocess.run([sys.executable, os.path.join(T, 'src', name + '.py')] + args, cwd=T, env=env, capture_output=True, text=True)
        new = json.load(open(os.path.join(T, 'results', rec))); old = json.load(open(os.path.join(ROOT, 'results', rec)))
        # the published dm_groups record carries one key written by hand after its run (a later stage's 'note' on how 'power ok' was recomputed); it is not
        # produced by the run and is left out of the comparison (reported)
        hand = {k: old.pop(k) for k in ('note',) if k in old and k not in new}
        d = CMN.diff(CMN.strip(new), CMN.strip(old))
        out[name] = {'exit': p.returncode, 'seconds': time.time() - t1, 'record equals the published one (common.py)': d is None,
                     'first difference': None if d is None else str(d)[:300], 'keys of the published record written by hand (not compared)': hand, 'ok in the new record': new.get('ok')}
        if p.returncode != 0: print(p.stdout[-800:], p.stderr[-800:])
        print(name, out[name]['exit'], out[name]['record equals the published one (common.py)'], round(out[name]['seconds']), flush=True)
    shutil.rmtree(T, ignore_errors=True)
    out['ok'] = all(v['exit'] == 0 and v['record equals the published one (common.py)'] for k, v in out.items() if isinstance(v, dict))
    out['seconds'] = time.time() - t0
    os.makedirs(os.path.join(ROOT, 'results_DY'), exist_ok=True)
    json.dump(out, open(os.path.join(ROOT, 'results_DY', 'dy_audits.json'), 'w'), indent=1); print(out['ok'])


if __name__ == '__main__':
    main()
