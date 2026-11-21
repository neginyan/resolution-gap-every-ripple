"""Paper J -- the short check (a few minutes; it is the check of the GitHub Actions workflow; no other repository needed).  Python 3.11 grammar.
Reruns, in a temporary copy, and compares each new record with the stored one (verification/common.py, the comparison of paper I's published common.py):
  paper I on the eta-separated code (eta = 1/ell, the default): the self-test of the interval arithmetic, Lemmas 15, 20, 21, 27, Proposition 13, Proposition 6
      and Lemma 7, and the map of Theorem 1 of paper I;
  paper J: the separation of eta from 1/ell (dx_sep_check.py); the chord inventory read from the code (Lemma 5, App. B); the table of how the lemmas use eta
      (App. A; dz_lemma_table.py); the line B1m with X1_B1(eta) read by the parser (ea_convex.py); the tail with eta and 1/ell separated (App. D); Theorem 3 at eta_bar = 1/4 by hand (exact rationals); the method of the
      true quantity (dz_check.py).
The full verification is verification/run_all.py."""
import os, sys, shutil
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import ROOT, check, finish, workdir, run, rerun_and_compare
import map_check


def main():
    w = workdir()
    try:
        rerun_and_compare(w, 'dn_ivtest.py', 'dn_ivtest.json', 'paper I (i): interval arithmetic: true values inside, wrong versions caught')
        rerun_and_compare(w, 'dq_m4.py', 'dq_m4.json', 'paper I (iii): Lemma 15, M4(1e-4) <= 2.0475')
        rerun_and_compare(w, 'du_cl.py', 'du_cl.json', 'paper I (iii): Lemma 20, M1 and M2 at y = 1e-4')
        rerun_and_compare(w, 'dv_m3.py', 'dv_m3.json', 'paper I (iii): Lemma 21 (by hand)')
        rerun_and_compare(w, 'dq_ej.py', 'dq_ej.json', 'paper I (iii): Lemma 27, E_J')
        rerun_and_compare(w, 'dp_room2.py', 'dp_room2.json', 'paper I (iii): Proposition 13 at eta = 1/ell')
        rerun_and_compare(w, 'dr_be.py', 'dr_be.json', 'paper I (iv): Proposition 6 and the constants of Theorem 5')
        rerun_and_compare(w, 'ds_check.py', 'ds_check.json', 'paper I (iv): Lemma 7')
        m = map_check.run()
        check('paper I (vi): the map of the five rooms: %d points, %d gaps' % (m['points'], m['n_gaps']), m['ok'])
        rerun_and_compare(w, './dx_sep_check.py', 'results_DX/dx_sep_check.json', 'J: eta separated from 1/ell (explicit eta, dependency map, wrong versions)')
        rerun_and_compare(w, 'dy_convex.py', 'results_DY/dy_convex.json', 'J, Lemma 5 and App. B: the chord inventory read from the code, with wrong versions')
        rerun_and_compare(w, 'ea_convex.py', 'results_EA/ea_convex.json', 'J, Sec. IV A and App. B: the line B1m with X1_B1(eta), read by the parser, with wrong versions')
        rerun_and_compare(w, 'dz_lemma_table.py', 'results_DZ/dz_lemma_table.json', 'J, App. A: how the lemmas use eta (inventory against the table; steps e1-e8)')
        rerun_and_compare(w, 'dy_tail.py', 'results_DY/dy_tail.json', 'J, App. D: the tail with eta and 1/ell separated (a1 = 7 gives paper I exactly)')
        rerun_and_compare(w, 'dy_room2_hand.py', 'results_DY/dy_room2_hand.json', 'J, Theorem 3: by hand at eta_bar = 1/4 (exact rationals; the side conditions and the main chain eps1, eps_h, theta^2, k1, margins), with wrong versions')
        rerun_and_compare(w, 'dz_check.py', 'results_DZ/dz_check.json', 'J, Sec. VI: the true quantity at any ell, against the brute quadrature and Lemma 11')
    finally:
        shutil.rmtree(w, ignore_errors=True)
    finish()


if __name__ == '__main__':
    main()
