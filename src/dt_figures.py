"""Stage DT: figures 2-4 of the paper I draft, from the stored records and from formulas.  Python 3.11 grammar.
  fig_cases  (Fig. 2): (a) schematic of Cases I and II of the rule (illustrative values, stated in the caption);
                       (b) smallest (F^2 - 1) ell found by the searches: Theorem 2 from results/dl_n4check.json (d), Theorem 4 (rule branch,
                           band 8 ell + 100 <= B < 5e5) from results/dq_low.json (S).
  fig_lemma7 (Fig. 3): schematic of the proof of Lemma 7 (not to scale).
  fig_true   (Fig. 4): Proposition 6 against the true quantity: results/dr_truth_T.json (rows with in_analogue) and results/dr_truth_T2.json, with kappa(B).
  python3 dt_figures.py [outdir]   (default paperI/figures)  -> fig_cases.pdf/.png, fig_lemma7.pdf/.png, fig_true.pdf/.png; returns the data used."""
import json, math, os, sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
J = lambda f: json.load(open(os.path.join(HERE, 'results', f), encoding='utf-8'))


def data():
    d = J('dl_n4check.json')['(d) search minima, corrected N4']
    thm2 = sorted((float(k), v['smallest (F^2 - 1) ell, corrected N4 (seeded search, 400 per family)']) for k, v in d.items())
    s = J('dq_low.json')['(S) search']
    thm4 = sorted((float(k), v['F_rule']['(F^2 - 1) ell']) for k, v in s.items())
    T = J('dr_truth_T.json'); T2 = J('dr_truth_T2.json')
    tr = [(r['B'], r['sum_sigma']) for r in T['rows'] if r['in_analogue']]
    t2 = [(r['B'], r['sum_sigma']) for r in T2['rows']]
    return {'thm2': thm2, 'thm4': thm4, 'true_T': tr, 'true_T2': t2}


def kappa(B):
    return np.minimum(0.055, 0.459 / (4 * np.asarray(B) + 1))


def fig_cases(D, stem):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 3.0), dpi=200)
    sig, b, om = 1e-4, 1e-3, 1.0                                     # illustrative values (not a state of the class)
    a = np.logspace(-6, 1, 400)
    P1 = a / 2; P4 = (b * om / 2) / (a + sig); bg = P1 + P4
    G2, al, be, chi = 0.08, 0.05, 0.004, 0.02                          # Case II: a bright ripple
    ax1.loglog(a, P1, color='#2171b5', lw=0.9, ls='--', label='P1')
    ax1.loglog(a, P4, color='#6baed6', lw=0.9, ls='--', label='P4z')
    ax1.loglog(a, bg, color='#08306b', lw=1.4, label='P1 + P4z')
    ax1.axhline(0.01, color='#238b45', lw=1.0, ls=':', label='target, Case I')
    ax1.loglog(a, bg + al * G2 * a + be * G2 / (a + sig) + chi * G2, color='#d94801', lw=1.4, label='+ P2z + hFz + cKz')
    ax1.axhline(0.06, color='#a63603', lw=1.0, ls=':', label='target, Case II')
    ax1.set_xlabel(r'$a=4\sigma/L^2$'); ax1.set_ylabel('value of the lines (illustrative)'); ax1.set_title('(a) schematic', fontsize=9)
    ax1.legend(fontsize=5.5, loc='lower left', framealpha=0.9); ax1.set_ylim(1e-3, 10)
    x2, y2 = zip(*D['thm2']); x4, y4 = zip(*D['thm4'])
    ax2.loglog(x2, y2, 's-', color='#238b45', ms=4, lw=0.9, label='Theorem 2')
    ax2.loglog(x4, y4, '^-', color='#d94801', ms=4, lw=0.9, label='Theorem 4 (low band, rule)')
    ax2.axhline(10, color='k', lw=0.8, ls='--'); ax2.text(70, 11.5, 'needed: 10', fontsize=7)
    ax2.set_xlabel(r'$\ell$'); ax2.set_ylabel(r'smallest $(F^2-1)\ell$ found'); ax2.set_title('(b) searches (numerical)', fontsize=9)
    ax2.legend(fontsize=7, loc='upper left')
    fig.tight_layout(); fig.savefig(stem + '.pdf'); fig.savefig(stem + '.png'); plt.close(fig)


def fig_lemma7(stem):
    fig, ax = plt.subplots(figsize=(7.0, 2.6), dpi=200)
    V = 60.0; v = np.linspace(-22, 22, 2000); g = np.exp(-v ** 2 / (2 * V))
    ax.plot(v, g, color='#555555', lw=1.2)
    D, Pk, c0 = 1.0, 7.0, 3.2                                         # not to scale: Delta = 1, spacing 7
    for k in range(-3, 4):
        vk = k * Pk + c0
        if abs(vk) > 21: continue
        ax.axvspan(vk - D / 4, vk + D / 4, color='#fdd0a2', alpha=0.9, lw=0)
        ax.plot([vk], [0.03], 'o', color='#d94801', ms=4)
        e = 1 if vk >= 0 else -1
        for j, col in ((1, '#2171b5'), (2, '#6baed6')):
            u = vk - j * e * D
            ax.axvspan(u - D / 4, u + D / 4, color=col, alpha=0.35, lw=0)
        if k in (0, 2):
            ax.annotate('', xy=(vk - 2 * e * D, 0.22 + 0.04 * k), xytext=(vk, 0.22 + 0.04 * k), arrowprops=dict(arrowstyle='->', color='#08306b', lw=0.9))
    ax.text(c0 + 2 * Pk + 0.6, 0.35, r'$I_k$ (radius $\Delta/4$) and its copies' '\n' r'one and two periods $\Delta$ toward the centre', fontsize=7)
    ax.text(-21.5, 0.9, r'Gaussian focus $\mathcal{N}_V(v)$', fontsize=7)
    ax.text(c0 + 0.3, 0.06, r'$v_k$', fontsize=7, color='#d94801')
    ax.annotate('', xy=(c0 + Pk, -0.08), xytext=(c0, -0.08), arrowprops=dict(arrowstyle='<->', color='k', lw=0.7))
    ax.text(c0 + Pk / 2, -0.17, r'$P=2\sqrt{2}\pi/(1-b)\geq8.88$', fontsize=7, ha='center')
    ax.set_xlim(-22, 22); ax.set_ylim(-0.25, 1.1); ax.set_yticks([]); ax.set_xlabel(r'$v$ (fixed $w$; not to scale)')
    for s_ in ('top', 'right', 'left'): ax.spines[s_].set_visible(False)
    fig.tight_layout(); fig.savefig(stem + '.pdf'); fig.savefig(stem + '.png'); plt.close(fig)


def fig_true(D, stem):
    fig, ax = plt.subplots(figsize=(3.4, 2.8), dpi=200)
    B, y = zip(*D['true_T']); B2, y2 = zip(*D['true_T2'])
    ax.loglog(B, y, '.', color='#2171b5', ms=3, label='true, 197 states')
    ax.loglog(B2, y2, 'x', color='#d94801', ms=4, label='true, 24 planted tight states')
    Bs = np.logspace(math.log10(min(B + B2)) - 0.2, math.log10(max(B + B2)) + 0.2, 300)
    ax.loglog(Bs, kappa(Bs), color='k', lw=1.0, label=r'bound $\kappa(B)$')
    ax.set_xlabel(r'$B=b/\sigma^2$'); ax.set_ylabel(r"$((a)+(a'))\,\sigma$"); ax.legend(fontsize=6)
    fig.tight_layout(); fig.savefig(stem + '.pdf'); fig.savefig(stem + '.png'); plt.close(fig)


def main(outdir=os.path.join(HERE, 'paperI', 'figures')):
    os.makedirs(outdir, exist_ok=True); D = data()
    fig_cases(D, os.path.join(outdir, 'fig_cases')); fig_lemma7(os.path.join(outdir, 'fig_lemma7')); fig_true(D, os.path.join(outdir, 'fig_true'))
    return D


if __name__ == '__main__':
    D = main(*(sys.argv[1:2]))
    print({k: (v if len(v) < 12 else len(v)) for k, v in D.items()})
