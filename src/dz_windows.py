"""Stage DZ, item 2.2: the window families of DZ_探索計画.md section 2, built from an UNBLURRED profile f = 1 + sum_n a_n cos(n t - phi_n) >= 0.
Python 3.11 grammar.  Model: Claude Opus 5.5 (claude-opus-5-5).
The blurred coefficients are q_n = a_n e^{-n^2 x/2} (x = (k' sigma)^2 of the state), R = sum q_n cos(n t - phi_n), eta = sup|R|.
Class conditions checked here: f >= 0 (on a grid fine enough for the highest harmonic, with the exact lower bound 1 - sum|a_n| tried first);
(P2) |a_n| <= |a_1|;  (P3) sum q_n <= 1/4;  sqrt(x) sup|R'| <= U1(ell).  Every family is ALIGNED at one point t*, so that sup|R| = sum q_n = eta exactly
(for eta = 1/4 this is forced by (P3)); the amplitude a_1 is fixed by eta, the shape by the parameters.
FAMILIES:
  W1  one harmonic: a_1 cos t.
  W2  two harmonics: a_1 cos t + rho a_1 cos(m t), m odd in {3, 21, 61} (aligned at 0; at pi both are at their trough, R(pi) = -eta).
  S   spike: a_1 [cos t + rho sum_{n=2}^N cos(n t)] (all harmonics up to the blur scale, a comb of spacing 2 pi: a blurred spike at t = 0 on the fundamental's crest).
  Pt  packet at the TROUGH: a_1 cos t - rho a_1 sum_n g_n cos(n (t - pi)), g_n = exp(-(n - n0)^2/(2 D^2)): a fine packet localized at t = pi, where the
      fundamental is at its trough, both negative: R(pi) = -eta, h = 1 - eta E there (the brightness of the packet sits where h is smallest).
  Pc  the same packet at the CREST (t = 0, sign +): R(0) = +eta, h = 1 + eta E there."""
import math
import numpy as np

QB = 0.25


def build(fam, eta, x, ell, rho=1.0, m=3, n0=60.0, D=3.0, N=None):
    """returns (q, ph, info) or (None, None, reason).  q, ph are lists over n = 1..nmax."""
    a = {}; ph = {}
    if fam == 'W1':
        a[1] = 1.0
    elif fam == 'W2':
        a[1] = 1.0; a[int(m)] = float(rho)
    elif fam == 'S':
        Nmax = int(min(4000, math.ceil(math.sqrt(2 * 60 / x)))) if N is None else int(N)
        a[1] = 1.0
        for n in range(2, Nmax + 1): a[n] = float(rho)
    elif fam in ('Pt', 'Pc'):
        a[1] = 1.0; n0 = float(n0); D = float(D)
        for n in range(max(2, int(n0 - 3.5 * D)), int(n0 + 3.5 * D) + 1):
            g = math.exp(-(n - n0) ** 2 / (2 * D * D))
            if g < 1e-12: continue
            if fam == 'Pt':   # -rho g cos(n (t - pi)) = rho g cos(n t - (n + 1) pi)
                a[n] = float(rho) * g; ph[n] = ((n + 1) % 2) * math.pi
            else:
                a[n] = float(rho) * g; ph[n] = 0.0
    else:
        raise ValueError(fam)
    nmax = max(a)
    blur = {n: math.exp(-n * n * x / 2) for n in a}
    tot = sum(a[n] * blur[n] for n in a)
    a1 = eta / tot                                   # aligned: sup|R| = sum q_n = eta
    an = {n: a1 * a[n] for n in a}
    q = [0.0] * nmax; p = [0.0] * nmax
    for n in an:
        q[n - 1] = an[n] * blur[n]; p[n - 1] = ph.get(n, 0.0)
    # drop harmonics below 1e-30 eta after the blur (they do not change anything at double precision)
    for i in range(nmax):
        if q[i] < 1e-30 * eta: q[i] = 0.0
    last = max(i for i in range(nmax) if q[i] > 0) + 1; q = q[:last]; p = p[:last]
    info = {'a1': a1, 'sum|a_n|': sum(abs(v) for v in an.values()), 'nmax (after blur)': last}
    if any(abs(an[n]) > abs(an[1]) * (1 + 1e-12) for n in an): return None, None, '(P2)'
    if sum(q) > QB * (1 + 1e-12): return None, None, '(P3)'
    if info['sum|a_n|'] > 1:   # f >= 0 on a grid (the profile is a trigonometric polynomial of degree nmax)
        K = max(4096, 16 * nmax); t = np.linspace(0, 2 * math.pi, K, endpoint=False); f = np.ones(K)
        for n in an: f += an[n] * np.cos(n * t - ph.get(n, 0.0))
        info['min f'] = float(f.min())
        if f.min() < 0: return None, None, 'f < 0'
    t = np.linspace(0, 2 * math.pi, max(4096, 16 * last), endpoint=False); R = np.zeros_like(t); Rp = np.zeros_like(t)
    for i, (qq, pp) in enumerate(zip(q, p), start=1):
        if qq: R += qq * np.cos(i * t - pp); Rp -= i * qq * np.sin(i * t - pp)
    U1 = 0.25 * math.sqrt(2 * ell + 3.1) + 1e-6
    info['eta (grid)'] = float(np.abs(R).max()); info['sqrt(x) sup|R\'|'] = math.sqrt(x) * float(np.abs(Rp).max())
    if info["sqrt(x) sup|R'|"] > U1: return None, None, 'U > U1'
    return q, p, info
