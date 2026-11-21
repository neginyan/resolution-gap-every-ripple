"""Stage DZ: the map of the (ell, B) plane for paper J, with the coefficient of each room (lambda/Upsilon = (1 - eta)/(1 + eta) or 1).
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).  Drawn from ds_figure.py of paper I (the same boundaries); only the labels change.
  Theorem H1 of paper H: 55.26 <= ell <= 960.8, B < 2.5e10 (tau >= 20);   Theorem 2 (lab: DJ-T): B >= max(2.5e10, 50 (8 ell + 100)), b <= 1/2;
  Theorem 3 (DP-2): b in (1/2, 1];   Theorem 4 (DP-1a): ell >= 960.8, 8 ell + 100 <= B < ell^4;   Theorem 5 (DR-T): ell >= 960.8, B <= 8 ell + 100.
  python3 src/dz_figure.py  -> paper/figures/fig_map_J.pdf, fig_map_J.png"""
import math, os
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)


def draw(stem=os.path.join(ROOT, 'paper', 'figures', 'fig_map_J')):
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
    ax.plot(lg[n], 4 * lg[n], color='#d94801', lw=0.9, ls='--')
    ax.plot(lg, t2, color='#238b45', lw=1.0); ax.plot(lg[n], b1[n], color='#d94801', lw=1.0); ax.axvline(math.log10(960.8), color='k', lw=0.7, ls=':')
    ax.plot(lg[m], np.full(m.sum(), math.log10(2.5e10)), color='#2171b5', lw=1.0)
    ax.text(2.37, 5.2, 'Theorem H1\nof paper H\n' + r'$\frac{1-\eta}{1+\eta}$', ha='center', va='center', fontsize=8)
    ax.text(4.6, 27.0, 'Theorem 2: narrow focus\n' + r'coefficient $\frac{1-\eta}{1+\eta}$', ha='center', va='center', fontsize=8.5)
    ax.text(6.5, ytop - 1.2, r'Theorem 3: focus at the resolution, $b\in(1/2,1]$, coefficient $1$ (far above this frame)', ha='center', va='center', fontsize=7.2)
    ax.text(5.6, 9.0, r'Theorem 4: wide focus, $\frac{1-\eta}{1+\eta}$', ha='center', va='center', fontsize=8.5)
    ax.text(6.2, 2.4, r'Theorem 5 of paper I: very wide focus, coefficient $1$', ha='center', va='center', fontsize=8, bbox=dict(facecolor='white', edgecolor='none', alpha=0.75, pad=1.2))
    ax.text(8.3, 4 * 8.3 - 3.4, r'$B=\ell^4$', fontsize=7, color='#d94801', ha='center')
    ax.text(math.log10(960.8) + 0.07, 34.0, r'$\ell=960.8$', fontsize=7, rotation=90, va='center')
    ax.set_xlim(math.log10(l0), math.log10(l1)); ax.set_ylim(ybot, ytop)
    ax.set_xlabel(r'$\log_{10}\ell$,  $\ell=\ln(1/\sigma)$  (finer resolution $\rightarrow$)'); ax.set_ylabel(r'$\log_{10}B$,  $B=b/\sigma^2=1/V$  (narrower focus $\uparrow$)')
    os.makedirs(os.path.dirname(stem), exist_ok=True); fig.tight_layout(); fig.savefig(stem + '.pdf'); fig.savefig(stem + '.png'); plt.close(fig)
    return stem + '.png'


if __name__ == '__main__':
    print(draw())
