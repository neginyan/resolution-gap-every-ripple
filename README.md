# resolution-gap-every-ripple

**Wherever the observer focuses, whatever the ripple: the lower side of the logarithmic law of the resolution gap for every window of the class**

Code, stored results, interval-arithmetic proofs and a verification script for the paper by Taishi Namba (2026).

**Paper:** T. Namba, *Wherever the observer focuses, whatever the ripple: the lower side of the logarithmic law of the resolution gap for every window of the class*, preprint, Zenodo (2026), [doi:10.5281/zenodo.24418628](https://doi.org/10.5281/zenodo.24418628) (all versions; v1.0 is [10.5281/zenodo.24418629](https://doi.org/10.5281/zenodo.24418629)).

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24418549.svg)](https://doi.org/10.5281/zenodo.24418549)
[![verify](https://github.com/neginyan/resolution-gap-every-ripple/actions/workflows/verify.yml/badge.svg)](https://github.com/neginyan/resolution-gap-every-ripple/actions/workflows/verify.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

## The result in brief

This is the follow-up to [paper I](https://doi.org/10.5281/zenodo.24371172) (code: [resolution-gap-every-focus](https://github.com/neginyan/resolution-gap-every-focus)), which proved the lower side of the logarithmic law of the resolution gap at every focus and every resolution for windows with a weak ripple (η = sup|R| ≤ 1/ℓ). Here the ripple may be as strong as the window class allows, η ≤ 1/4.

- **Theorem 1 (every focus, every ripple of the class).** For every admissible window and every ℓ = ln(1/σ) ≥ 55.26, every state satisfies g√ℓ ≥ (1 − ε̄)(1 − η)/(1 + η); for ℓ ≥ 960.8, g√ℓ ≥ (1 − ε̄)(1 − η)/(1 + η)√(1 + 10/ℓ). The factor (1 − η)/(1 + η) is the ratio λ/Υ of the ripple sandwich of paper H; it is at least 3/5.
- **At the resolution the coefficient stays one.** When the focus sits at the resolution, (a) + (a′) ≥ 0.49 whenever the ripple reaches the focus (G > 0), and ≥ 0.1995 otherwise, for every ripple of the class; both are above Γ_ℓ ≤ 0.1462 (Theorem 3, by hand).
- **Two ends instead of a continuum.** Every remainder of the local expansion is a product of six non-negative, increasing, convex functions of η, so it lies under its chord in λ = 1/(1 + η) (Lemma 5); with the target scaled by λ/Υ = 2λ − 1, interval proofs at η = 0 and η = 1/4 cover every ripple in between.
- **The lemmas re-read.** Every lemma of paper I and every lemma it borrows was read again for its use of η (Table of App. A). One written step needed η ≤ 1/ℓ; it is repaired by a larger constant, with no new lemma.
- **The true quantity at strong ripples.** On windows with η = 1/4 the smallest true ((a) + (a′))√ℓ found is 3.40 at ℓ = 55.26 (so g√ℓ ≥ (1 − ε̄) 3.40 there), far above one, and at those states the factors of the ripple sandwich move the true quantity by a few per cent (numerical). The paper conjectures that the coefficient one holds for every ripple of the class.
- **Computer assistance by decimal interval arithmetic** with outward rounding, run with `decimal.Inexact` trapped.
- **Tried to break first.** Every claim was attacked with adversarial searches before it was proved, and every search reports the deliberately wrong versions it can break.

Every statement in the paper carries its status: proof, computer-assisted proof, derivation, numerical, or conjecture.

## Verify

```bash
pip install -r requirements.txt
python verification/quick.py                                     # about one minute; no other repository needed
python verification/run_all.py --h-repo ../resolution-gap-weak-ripple --i-repo ../resolution-gap-every-focus   # about an hour
```

`quick.py` reruns the checks of paper I that need no other repository (on the code in which η is a separate argument, at η = 1/ℓ), the separation of η from 1/ℓ, the chord inventory read from the code (with the repaired line B1m), the table of how the lemmas use η, the tail, the hand proof of Theorem 3 at η = 1/4 (every step of its chain in exact rationals), and the checks of the method that computes the true quantity. It is the check of the GitHub Actions workflow.

`run_all.py` runs `quick.py` and then the interval proofs of Theorems 2 and 4 at both ends (9,810 and 6,952 pieces and the tails), the absorptions (R1) and (R3), the audits of paper I re-run from scratch, the audits at strong ripples, the figure, and reads the stored records of the searches (`--full` re-runs them, several hours). Some modules import modules of paper H's repository (v1.3), which are not copied here: pass its location with `--h-repo` (or `H_REPO`). With `--i-repo` (or `I_REPO`) it also checks that every file taken from the published repository of paper I is unchanged, except the five modules that separate η from 1/ℓ.

Every rerun is made in a temporary copy and compared with the stored record entry by entry (flags, counts and interval bounds exactly; double-precision floats up to a relative 10⁻⁹); the stored records are never overwritten. Theorem H1 is certified by the repository of paper H, not here.

## What is where

| result | status | script → results |
|---|---|---|
| Theorem 1 (assembly; the map of the five rooms) | proof | `paper/sections/02_main_theorem.tex`; map: `verification/map_check.py`, `src/dz_figure.py` |
| Theorem 2 (narrow focus), both ends | computer-assisted | `src/dy_run.py t2 A` (or `B`; `measure`, then `final`) → `results_DY/dy_t2_*.json` |
| Theorem 3 (focus at the resolution) at η = 1/4 | proof (exact rationals) | `src/dy_room2_hand.py` → `results_DY/dy_room2_hand.json` |
| Theorem 4 (wide focus), both ends | computer-assisted | `src/dy_run.py t4 A` (or `B`) → `results_DY/dy_t4_*.json` |
| (R1), (R3); wrong versions | computer-assisted | `src/dy_run.py r1 A`, `src/dy_run.py power A` (or `B`) → `results_DY/dy_r1_*.json`, `results_DY/dy_power_*.json` |
| Lemma 5 (the chord) and the inventory of the 37 lines | proof; inventory read from the code | `src/dy_convex.py` → `results_DY/dy_convex.json`; the line B1m with X₁,B1(η): `src/ea_convex.py` → `results_EA/ea_convex.json` |
| how the lemmas use η (App. A) | proof (reading); steps checked | `src/dz_lemma_table.py` → `results_DZ/dz_lemma_table.json` |
| the tail with η and 1/ℓ separated | computer-assisted | `src/dy_tail.py` → `results_DY/dy_tail.json` |
| η separated from 1/ℓ; audits at strong ripples | — / numerical | `dx_sep_check.py`, `src/dx_groups.py`, `src/dx_table.py`, `src/dx_room2.py` → `results_DX/` |
| searches before the proofs | numerical | `src/dy_corner.py`, `src/dx_search.py` |
| the true g√ℓ at strong ripples | numerical | `src/dz_truth.py`, `src/dz_windows.py`, `src/dz_search.py`, `src/dz_post.py`, `src/dz_power.py`, `src/dz_ell.py`, `src/dz_check.py` → `results_DZ/` |
| paper I (unchanged except five modules) | as in paper I | `src/`, `results/` |

| folder | content |
|---|---|
| `src/` | the code (Python 3, NumPy, SciPy, Matplotlib): paper I's modules and the new `dx_*`, `dy_*`, `dz_*` |
| `results/` | the stored records of paper I (unchanged) |
| `results_DX/`, `results_DY/`, `results_DZ/`, `results_EA/` | the stored records of this paper |
| `verification/` | `quick.py`, `run_all.py`, `map_check.py`, `common.py` |
| `paper/` | LaTeX source of the paper (REVTeX 4.2), its figure and the PDF of v1.0 (`paper/paperJ_v1.0.pdf`) |

The working record of the proofs (the stage reports of the lab sessions) is kept by the author.

## Known issues

None at present.

## Related work by the author

- T. Namba, *Wherever the observer focuses: the lower side of the logarithmic law of the resolution gap at every focus and every resolution*, Zenodo (2026), [doi:10.5281/zenodo.24371172](https://doi.org/10.5281/zenodo.24371172) (paper I; code [resolution-gap-every-focus](https://github.com/neginyan/resolution-gap-every-focus), [doi:10.5281/zenodo.24370921](https://doi.org/10.5281/zenodo.24370921)).
- T. Namba, *Beyond few harmonics: the lower side of the logarithmic law of the resolution gap for windows with a weak ripple*, Zenodo (2026), [doi:10.5281/zenodo.23932698](https://doi.org/10.5281/zenodo.23932698) (paper H; code [resolution-gap-weak-ripple](https://github.com/neginyan/resolution-gap-weak-ripple)); this work uses its version 1.3 ([doi:10.5281/zenodo.24369012](https://doi.org/10.5281/zenodo.24369012)).
- T. Namba, *How fine can a hidden ripple be? A two-sided logarithmic law for the resolution gap of the arrow of time*, Zenodo (2026), [doi:10.5281/zenodo.23856796](https://doi.org/10.5281/zenodo.23856796) (paper F; code [resolution-gap-two-sided](https://github.com/neginyan/resolution-gap-two-sided)).

Papers F, H and I and their repositories are not changed by this work.

## Use of AI assistants

The study was carried out with AI assistants (Anthropic Claude, Google Gemini and OpenAI ChatGPT). Their roles are described in the acknowledgments of the paper. The author directed the research and takes full responsibility for it.

## Citation

Please cite the paper ([doi:10.5281/zenodo.24418628](https://doi.org/10.5281/zenodo.24418628)) and this repository; see `CITATION.cff`. The code is archived at Zenodo: [doi:10.5281/zenodo.24418549](https://doi.org/10.5281/zenodo.24418549) (all versions; v1.0.0 is [10.5281/zenodo.24418550](https://doi.org/10.5281/zenodo.24418550)).

## License

MIT © 2026 Taishi Namba
