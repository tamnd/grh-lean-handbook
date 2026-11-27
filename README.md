# The GRH Lean Handbook

[lsernau/grh-lean](https://github.com/lsernau/grh-lean) is a Lean 4 project that states a proof of the Generalized Riemann Hypothesis for Dirichlet L-functions. This handbook explains that proof as mathematics, for a graduate student in number theory who does not read Lean. It comes as a set of books in PDF and EPUB. The book follows the readable edition `grh/` of the source, at the commit in `EDITION`.

## The status of the claim

The handbook keeps three things apart.

1. **What Lean checks.** The source states five theorems in `grh/src/Main.lean`. Lean accepts them if the build and the axiom check pass. The source reports these checks: `lake build`, `scripts/PrintAxioms.lean`, three independent kernels and Comparator. The repository has no logs and no CI for any of them, and the Comparator run used a stand-in for its sandbox. We did not run the checks again.
2. **What the source says.** The documents, the docstrings and the names are notes by the same author as the code. Lean checks none of them.
3. **What the book explains.** Each chapter explains the mathematics of one part of the source. Each chapter has a status: `drafted`, `checked` or `reviewed`. A model can set `drafted` only. `checked` and `reviewed` need a named person.

The book does not say in its own voice that the proof is correct. It says what the source claims, what Lean accepts if the reported checks hold, and what each chapter explains. Volume 0 gives the details.

## The volumes

| Vol | Title | Source | Words |
|---|---|---|---|
| 0 | Guide | the documents, Statements, Main, every flag | 30,000 |
| 1 | The proof in outline | New/Main, New/Reduction | 45,000 |
| 2 | Analytic number theory | Lib/Analytic, Reduction/Data/Existence (in part) | 30,000 |
| 3 | Number fields, class field theory and complex multiplication | Lib/ClassField, Lib/Cyclotomic, Lib/CM | 35,000 |
| 4 | Unitary groups and automorphic forms | Lib/Adelic, Lib/General/Groups | 30,000 |
| 5 | Representations of real, p-adic and finite groups | Lib/DiscreteSeries, Lib/GLn, Lib/LocalGL, New/Appendix | 40,000 |
| 6 | The theta correspondence and the Siegel-Weil formula | Lib/Weil, Lib/SiegelWeil, Lib/DiscreteSeries/Theta | 45,000 |
| 7 | Cohomology and p-adic Hodge theory | Lib/Cohomology, Lib/PadicHodge, Lib/PadicComparison, Lib/General/Geometry, Lib/General/Algebra | 45,000 |
| 8 | Shimura varieties and Galois representations | Lib/Shimura, Lib/GaloisRep | 40,000 |
| 9 | Theorem A: short forms | New/UpperBound, New/Derivatives (without Sharpness) | 45,000 |
| 10 | Theorem B: enough forms | New/Spanning | 55,000 |
| 11 | Theorem C: long forms | New/Determinant, New/OneLift, New/Derivatives/Sharpness | 60,000 |
| 12 | Congruences and Selmer groups | New/Congruences | 45,000 |

The words are targets. The total is about 545,000 words. Each volume has a plan in `content/NN-*/volume.yaml`, with its chapters. A volume with no written chapter is not built. `ledger/coverage.md` shows what is written, and the books are in the [releases](https://github.com/tamnd/grh-lean-handbook/releases).

## How to build

The builder is the Python package `ghb`. It needs Python 3.11 or later, PyYAML, Pillow, fontTools and pypdf. A PDF needs pandoc 3.12 and tectonic. An EPUB needs pandoc. The builder reads the source as text and does not build Lean.

```sh
git clone https://github.com/lsernau/grh-lean ../grh-lean
git -C ../grh-lean checkout "$(awk '/^grh /{print $2}' EDITION)"
pip install .
python3 -m ghb check --volume all
python3 -m ghb build --volume 1 --formats pdf,epub --out /tmp/ghb-out
python3 -m ghb join --in /tmp/ghb-out
python3 -m ghb ledger --write
python3 -m ghb survey
```

- `check` tests the names, the paths, the links, the front matter and the style of each section. It fails on a problem and reports a warning for a link to a chapter that is not written yet.
- `build` makes the PDF and the EPUB of each volume. `--volume` takes a number, a list such as `1,9`, `all`, or `front` for the front pages alone.
- `join --in DIR` joins the volume PDFs of the edition in `DIR`, the front pages then volumes 0 to 12, into `DIR/grh-lean-handbook-<version>.pdf`. Each volume keeps its outline under a bookmark with its title, its links, and its page labels with the prefix `N:`.
- `ledger --write` writes `ledger/files.yaml`, `ledger/decls.yaml` and `ledger/coverage.md`. `ledger --diff A B` lists what changed in the source between two commits.
- `survey` gives the words and the source files of each volume.

The option `--source PATH` sets the clone of the source. The default is `../grh-lean`.

## How to write a chapter

The brief for a writer is `prompts/chapter.md`, and the brief for a checker is `prompts/review.md`. A chapter is a folder `content/NN-volume/<chapter>/`, with one file for each section. A pull request for a chapter passes `ghb check` before it merges.

## Licence

The text is under CC BY 4.0 (`LICENSE-CONTENT`). The code is under the MIT License (`LICENSE`). The source lsernau/grh-lean is under the Apache License 2.0. The book quotes Lean names and short statements from it with attribution.
