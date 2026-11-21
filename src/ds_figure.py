"""Stage DS: the map of the (ell, B) plane for the draft of paper I (the same formulas as dr_figure.py, with the names the theorems have in the paper).  Python 3.11 grammar.
  Theorem H1 of paper H: 55.26 <= ell <= 960.8, B < 2.5e10 (tau >= 20);   Theorem 2 (lab: DJ-T): B >= max(2.5e10, 50 (8 ell + 100)), b <= 1/2;
  Theorem 3 (DP-2): b in (1/2, 1];   Theorem 4 (DP-1a): ell >= 960.8, 8 ell + 100 <= B < ell^4;   Theorem 5 (DR-T): ell >= 960.8, B <= 8 ell + 100.
  python3 ds_figure.py  -> paperI/figures/fig_map.pdf, fig_map.png"""
import math, os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))


def draw(stem=os.path.join(HERE, 'paperI', 'figures', 'fig_map')):
    l0, l1 = 55.26, 1e12; ytop = 46.0; ybot = 0.0
    L = np.logspace(math.log10(l0), math.log10(l1), 3000); lg = np.log10(L)
    t2 = np.log10(np.maximum(2.5e10, 50 * (8 * L + 100)))
    fig, ax = plt.subplots(figsize=(7.0, 4.9), dpi=200)
    c_h1, c_2, c_4, c_5, c_3 = '#9ecae1', '#c7e9c0', '#fdd0a2', '#fde0ef', '#bcbddc'
    m = L <= 960.8; n = L >= 960.8; b1 = np.log10(8 * L + 100)
    ax.fill_between(lg[m], ybot, math.log10(2.5e10), color=c_h1, lw=0)
    ax.fill_between(lg, t2, ytop - 2.4, color=c_2, lw=0)
    ax.fill_between(lg, ytop - 2.4, ytop, color=c_3, lw=0)
    ax.fill_between(lg[n], b1[n], np.minimum(t2[n], 4 * lg[n]), color=c_4, lw=0)
    ax.fill_between(lg[n], ybot, b1[n], color=c_5, lw=0)
    tau0 = 4 * np.log(L) + 40; bp = np.log10(5e11 / tau0); k = n & (bp < b1)
    ax.fill_between(lg[k], bp[k], b1[k], facecolor='none', hatch='////', edgecolor='#c51b8a', lw=0)
    ax.plot(lg[n], 4 * lg[n], color='#d94801', lw=0.9, ls='--')
    ax.plot(lg, t2, color='#238b45', lw=1.0); ax.plot(lg[n], b1[n], color='#d94801', lw=1.0); ax.axvline(math.log10(960.8), color='k', lw=0.7, ls=':')
    ax.plot(lg[m], np.full(m.sum(), math.log10(2.5e10)), color='#2171b5', lw=1.0)
    ax.text(2.37, 5.2, 'Theorem H1\nof paper H', ha='center', va='center', fontsize=8)
    ax.text(5.7, 26.0, 'Theorem 2\nnarrow focus', ha='center', va='center', fontsize=8.5)
    ax.text(6.5, ytop - 1.2, r'Theorem 3: focus at the resolution, $b\in(1/2,1]$ (far above this frame)', ha='center', va='center', fontsize=7.5)
    ax.text(6.7, 8.9, 'Theorem 4: wide focus', ha='center', va='center', fontsize=8.5)
    ax.text(6.2, 2.4, 'Theorem 5: very wide focus', ha='center', va='center', fontsize=8.5, bbox=dict(facecolor='white', edgecolor='none', alpha=0.75, pad=1.2))
    ax.annotate('Lemma 7 needed\nonly here', xy=(10.6, 10.3), xytext=(9.6, 15.5), fontsize=7, color='#7a0177', ha='center', arrowprops=dict(arrowstyle='->', color='#7a0177', lw=0.7))
    ax.text(8.3, 4 * 8.3 - 3.4, r'$B=\ell^4$', fontsize=7, color='#d94801', ha='center')
    ax.text(math.log10(960.8) + 0.07, 34.0, r'$\ell=960.8$', fontsize=7, rotation=90, va='center')
    ax.set_xlim(math.log10(l0), math.log10(l1)); ax.set_ylim(ybot, ytop)
    ax.set_xlabel(r'$\log_{10}\ell$,  $\ell=\ln(1/\sigma)$  (finer resolution $\rightarrow$)'); ax.set_ylabel(r'$\log_{10}B$,  $B=b/\sigma^2=1/V$  (narrower focus $\uparrow$)')
    os.makedirs(os.path.dirname(stem), exist_ok=True); fig.tight_layout(); fig.savefig(stem + '.pdf'); fig.savefig(stem + '.png'); plt.close(fig)
    return stem + '.png'


if __name__ == '__main__':
    print(draw())
