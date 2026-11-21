"""Paper J -- the full verification (about 75 minutes; with --full also the searches, several hours).  Python 3.11 grammar.
    python3 verification/run_all.py --h-repo PATH_H --i-repo PATH_I [--full]      (or the environment variables H_REPO, I_REPO)
PATH_H is the repository of paper H (resolution-gap-weak-ripple, v1.3): some modules import modules of it, which are not copied here.
PATH_I is the published repository of paper I (resolution-gap-every-focus, v1.0): this repository starts from it.
It runs verification/quick.py first, then, in a temporary copy, compares every new record with the stored one (the comparison of paper I's common.py):
  (I)   paper I on the eta-separated code (eta = 1/ell): Propositions 12 and 14 on all pieces (du_fix.py), (R1) and (R3) (dp_r1.py), the true quantities at the
        resolution (dp_truth.py); the two audits of paper I re-run from scratch against the published records (dy_audits.py);
  (II)  the 30 groups at eta = 1/4 (dx_groups.py), the lines against the lemmas at strong ripples (dx_table.py, with its power), Theorem 3 at eta_bar = 1/4
        with interval arithmetic (dx_room2.py);
  (III) paper J's interval proofs at the two ends: Theorem 2 (9,810 pieces and the tail; two runs per end), Theorem 4 (6,953 pieces), (R1)/(R3), the wrong
        versions (dy_run.py), the corner search before the proofs (dy_corner.py);
  (IV)  the map figure of paper J drawn again (dz_figure.py); the searches for the true g sqrt(ell): their stored records read and summarised (with --full:
        re-run: dz_search.py, dz_post.py, dz_power.py, dz_sandwich.py, dz_wide.py, dz_ell.py);
  (V)   with the repository of paper I: every file of this repository that comes from it is identical to the published file, except the five modules that
        separate eta from 1/ell, whose published versions have the recorded sha256;
  (VI)  with the repository of paper H: the statements of paper H used here are in its text."""
import glob, hashlib, json, os, sys, shutil, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import ROOT, RES, check, finish, workdir, run, rerun_and_compare, h_src, i_repo

CHANGED = {'src/dj_lines.py', 'src/dk_lemma.py', 'src/dl_consts.py', 'src/dp_r1.py', 'src/dp_room1.py'}
NOT_FROM_I = ('paper/', 'verification/quick.py', 'verification/run_all.py', 'verification/common.py', 'README.md', 'CITATION.cff', '.github/')


def sha(p): return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def main():
    full = '--full' in sys.argv
    q = subprocess.run([sys.executable, os.path.join(ROOT, 'verification', 'quick.py')], capture_output=True, text=True)
    print(''.join('    ' + l + '\n' for l in q.stdout.splitlines() if l.strip()), end='')
    check('verification/quick.py', q.returncode == 0)
    hs = h_src(); ir = i_repo()
    check('the repository of paper H is given (--h-repo or H_REPO): %s' % (os.path.dirname(hs) if hs else 'not given'), hs is not None)
    check('the repository of paper I is given (--i-repo or I_REPO): %s' % (ir or 'not given'), ir is not None)
    w = workdir()
    try:
        if hs:
            rerun_and_compare(w, 'du_fix.py', 'du_fix.json', '(I) paper I: Propositions 12 and 14 on all pieces at eta = 1/ell', hsrc=hs)
            rerun_and_compare(w, 'dp_r1.py', 'dp_r1.json', '(I) paper I: (R1) and (R3) at eta = 1/ell', hsrc=hs)
        rerun_and_compare(w, 'dp_truth.py', 'dp_truth.json', '(I) paper I: Theorem 3 against the true quantities')
        if hs:
            rerun_and_compare(w, 'dy_audits.py', 'results_DY/dy_audits.json', '(I) the audits of paper I at eta = 1/ell, from scratch, against the published records', hsrc=hs)
            rerun_and_compare(w, 'dx_groups.py', 'results_DX/dx_groups.json', '(II) the 30 groups at eta = 1/4: published (FrB1 breaks) and X1_B1 (none breaks)', hsrc=hs)
            rerun_and_compare(w, 'dx_table.py', 'results_DX/dx_table.json', '(II) the lines against the lemmas at strong ripples (chord and uniform forms)', hsrc=hs)
            rerun_and_compare(w, 'dx_table.py', 'results_DX/dx_table_power.json', '(II) power of that audit', args=('power',), hsrc=hs)
            rerun_and_compare(w, 'dx_room2.py', 'results_DX/dx_room2.json', '(II) Theorem 3 at eta_bar = 1/4 with interval arithmetic', hsrc=hs)
            for e in 'AB':
                rerun_and_compare(w, 'dy_run.py', 'results_DY/dy_r1_%s.json' % e, '(III) (R1), (R3), tiny bounds, end %s' % e, args=('r1', e), hsrc=hs)
                for ph in ('measure', 'final'):
                    rerun_and_compare(w, 'dy_run.py', 'results_DY/dy_t2_%s_%s.json' % (e, ph), '(III) Theorem 2, end %s, %s run' % (e, ph), args=('t2', e, ph), hsrc=hs)
                rerun_and_compare(w, 'dy_run.py', 'results_DY/dy_t4_%s.json' % e, '(III) Theorem 4, end %s' % e, args=('t4', e), hsrc=hs)
                rerun_and_compare(w, 'dy_run.py', 'results_DY/dy_power_%s.json' % e, '(III) wrong versions, end %s' % e, args=('power', e), hsrc=hs)
            rerun_and_compare(w, 'dy_corner.py', 'results_DY/dy_corner.json', '(III) the corner search at ell = 55.26 before the proofs', hsrc=hs)
        rc, out, sec = run(w, 'dz_figure.py')
        try:
            import matplotlib.image as mi, numpy as np
            same = np.array_equal(mi.imread(os.path.join(w, 'paper', 'figures', 'fig_map_J.png')), mi.imread(os.path.join(ROOT, 'paper', 'figures', 'fig_map_J.png')))
        except Exception:
            same = False
        check('(IV) the map of paper J drawn again, identical to the stored PNG pixel by pixel', rc == 0 and same)
        if full:
            for ell in ('55.26',):
                rerun_and_compare(w, 'dz_search.py', 'results_DZ/dz_search_%s.json' % ell, '(IV) the search for the true g sqrt(ell), ell = %s (re-run)' % ell, args=('main', ell))
            rerun_and_compare(w, 'dz_post.py', 'results_DZ/dz_post.json', '(IV) the minimisers on the fine grid (re-run)')
            rerun_and_compare(w, 'dz_power.py', 'results_DZ/dz_power.json', '(IV) the power of the search (re-run)')
            rerun_and_compare(w, 'dz_sandwich.py', 'results_DZ/dz_sandwich.json', '(IV) the sandwich inside the true quantity, Q/Q_h1 (re-run)')
            rerun_and_compare(w, 'dz_wide.py', 'results_DZ/dz_wide.json', '(IV) the band of Theorem 4 with the class box (re-run)')
            rerun_and_compare(w, 'dz_ell.py', 'results_DZ/dz_ell.json', '(IV) the minimisers at other ell, among them 960.8 (re-run)')
        else:
            P = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_post.json'))); W = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_power.json')))
            E = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_ell.json'))); Sd = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_sandwich.json')))
            Wd = json.load(open(os.path.join(ROOT, 'results_DZ', 'dz_wide.json')))
            mins = {k: v['value'] for k, v in P['55.26'].items() if k.startswith('smallest Q sqrt(ell) [')}
            check('(IV) the search for the true g sqrt(ell) (stored records read; --full re-runs): smallest values at ell = 55.26: %s; power: %s; Q/Q_h1 search: %s; '
                  'wide band, other ell: ok = %s, %s'
                  % (', '.join('%s %.4g' % (k[len('smallest Q sqrt(ell) '):], v) for k, v in mins.items()), W['ok'],
                     ', '.join('%s %.3f' % (k[len('search: smallest Q/Q_h1, '):], v['value']) for k, v in Sd.items() if k.startswith('search: smallest')), Wd['ok'], E['ok']),
                  W['ok'] and E['ok'] and Sd['ok'] and Wd['ok'])
        if ir:
            bad = []; changed = {}
            for dp, dn, fs in os.walk(ir):
                if '.git' in dp or '__pycache__' in dp: continue
                for f in fs:
                    rel = os.path.relpath(os.path.join(dp, f), ir).replace(os.sep, '/')
                    if rel.startswith(NOT_FROM_I): continue
                    mine = os.path.join(ROOT, rel)
                    if not os.path.exists(mine): bad.append('missing ' + rel); continue
                    if rel in CHANGED: changed[rel] = sha(os.path.join(ir, rel)); continue
                    if sha(mine) != sha(os.path.join(dp, f)): bad.append('differs ' + rel)
            man = json.load(open(os.path.join(ROOT, 'results_DY', 'dy_overlay_manifest.json')))['published sha256 of the changed modules']
            ok = not bad and changed == man
            check('(V) the files that come from the published repository of paper I are identical to it; the 5 changed modules have the recorded published sha256',
                  ok, '; '.join(bad[:5]))
        if hs:
            H = ''.join(open(f, encoding='utf-8').read() for f in sorted(glob.glob(os.path.join(os.path.dirname(hs), 'paper', 'sections', '*.tex'))))
            want = {'Lemma CM-1': r"xE_1\le\Bigl(1+\frac b2\Bigr)E_0\ln\frac{2B_0}{E_0}+\frac{\sqrt2}{e}\,b\,E_0'", 'the proof of CM-1 uses only f >= 0': r"The proof uses only $f\ge0$",
                    'Lemma BE, range (v1.3)': r"Let $\sigma\in[10^{-3000},e^{-55.26}]$", 'Lemma R_theta': r"\label{lem:Rtheta}", 'Lemma A4*': r"Lemma A4*",
                    'Theorem H1 with the sandwich ratio': r"g\sqrt\ell\ \ge\ (1-\bar\varepsilon)\,\frac{\lambda}{\Upsilon}\Bigl(1+\frac{12.1}{\ell}+2.5\times10^{-4}\Bigr)",
                    'the certificates use eta_bar = 1/2': r"$\bar\eta=1/2$ in the remainders"}
            miss = [k for k, v in want.items() if v not in H]
            check('(VI) the statements of paper H used here are in its text: %s' % ', '.join(want), not miss, ('missing: ' + ', '.join(miss)) if miss else '')
    finally:
        shutil.rmtree(w, ignore_errors=True)
    finish()


if __name__ == '__main__':
    main()
