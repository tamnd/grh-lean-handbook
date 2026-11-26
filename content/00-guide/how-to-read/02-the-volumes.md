---
title: The volumes and the map of the proof
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The volumes and the map of the proof

This section gives the shape of the proof, the thirteen volumes that explain it, and the reasons for their order. The order of the volumes comes from the shape of the proof, so the shape comes first.

### The shape of the proof

The proof has a clear shape at the top. Read the following chain from the bottom up. Each line is a statement, and each statement comes from the one below it.

1. The background theories: analytic number theory, class field theory, automorphic forms on unitary groups, representations of real, $p$-adic and finite groups, the theta correspondence, cohomology and $p$-adic Hodge theory, Shimura varieties and Galois representations.
2. Theorems A, B and C. They are statements about a lattice of automorphic forms that the argument builds from data $D$ at a scale $x$.
3. The star inequality: $m \cdot \mathrm{rem} \leq f a \log^5 b$, where $\mathrm{rem}$ is the total remainder of a prime sum, $m$ is about $\sqrt{x}$, and $f$, $a$, $b$ are sizes of the data.
4. The one-sided bound: for $18480 \mid q_0$, a prime $d \equiv q_0/2 - 1 \bmod q_0$ and $\varepsilon > 0$, the weighted prime remainder satisfies $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for all large $y$.
5. The half-plane theorem: $L(s, \chi) \neq 0$ for $\operatorname{Re} s > 1/2$, except at the pole of a principal L-function.
6. The five theorems of the source.

The step from 2 to 3 compares two bounds for the covolume of one lattice. Theorems A and B give an upper bound by short vectors, and Theorem C gives a lower bound by a product formula. The two bounds share a main amount, which cancels, and the prime sum is what remains. The step from 3 to 4 uses an identity for $\mathrm{rem}$ and the prime number theorem at a second scale. The step from 4 to 5 is Landau's criterion, applied with quadratic twists. The step from 5 to 6 is the reflection of zeros $s \mapsto 1 - s$. [The plan in one page](/chapter/theorem-and-plan/#the-plan-in-one-page) states each link exactly, with its Lean name.

The map below shows where each link is explained. An arrow points from a volume to the volume that uses it.

```text
                 the five theorems
                        ^
     Vol 1  The proof in outline: links 2 to 6,
            with Theorems A, B and C stated
       ^          ^            ^
       |          |            |
     Vol 9      Vol 10       Vol 11 <------ Vol 12
     Thm A      Thm B        Thm C        Congruences
       ^          ^            ^              ^
       |          |            |              |
       +----------+-----+------+--------------+
                        |
       the background theories, Volumes 2 to 8
                 (link 1 of the chain)

     Vol 0  Guide: the claim, the statements, the
            notation, the sizes, the Lean, the index
```

Volume 2 is used by Volume 1 as well as by the argument volumes: the analytic steps 4 to 6 of the chain rest on it.

### The thirteen volumes

The table gives each volume, the part of the source that it explains, and the number of chapters in its plan. The source is the readable edition. `New` is the folder of the argument and `Lib` is the folder of the background.

| Vol | Title | Source | Chapters |
|---|---|---|---|
| 0 | Guide | the documents, Statements, Main | 10 |
| 1 | The proof in outline | New/Main, New/Reduction | 13 |
| 2 | Analytic number theory | Lib/Analytic | 7 |
| 3 | Number fields, class field theory and complex multiplication | Lib/ClassField, Lib/Cyclotomic, Lib/CM | 5 |
| 4 | Unitary groups and automorphic forms | Lib/Adelic, Lib/General/Groups | 5 |
| 5 | Representations of real, p-adic and finite groups | Lib/DiscreteSeries, Lib/GLn, Lib/LocalGL, New/Appendix | 6 |
| 6 | The theta correspondence and the Siegel-Weil formula | Lib/Weil, Lib/SiegelWeil | 6 |
| 7 | Cohomology and p-adic Hodge theory | Lib/Cohomology, Lib/PadicHodge, Lib/PadicComparison | 6 |
| 8 | Shimura varieties and Galois representations | Lib/Shimura, Lib/GaloisRep | 5 |
| 9 | Theorem A: short forms | New/UpperBound, New/Derivatives | 13 |
| 10 | Theorem B: enough forms | New/Spanning | 12 |
| 11 | Theorem C: long forms | New/Determinant, New/OneLift | 16 |
| 12 | Congruences and Selmer groups | New/Congruences | 10 |

The plan has 114 chapters. The source column is a guide, not a rule: a chapter can explain a file of another folder when its argument needs it. Each chapter lists the files that it explains.

**Volume 0, Guide.** This volume. It says what the source claims and what evidence there is ([the claim and its status](/chapter/claim-and-status/)). It reads the five statements against Mathlib line by line ([the statements](/chapter/statements/)). It fixes the notation and the sizes, gives the little Lean that a reader needs, keeps the register of findings, compares the two editions of the source, and gives the index of Lean names.

**Volume 1, The proof in outline.** This volume proves the five theorems from Theorems A, B and C, with full proofs of every step above them. It is the spine of the book. A reader who stops after Volume 1 knows the whole design, every size, and every place where the three theorems enter. Chapters 2 to 4 are the analytic reduction. Chapter 5 explains the method with model cases. Chapters 6 to 12 set up the data, the prime sums and the lattices, and state Theorems A, B and C. Chapter 13 proves the star inequality and ends the proof.

**Volumes 2 to 8, the background.** Each volume treats one subject. It states the classical theory with a source, then defines the object of the source, which can be weaker or narrower, and proves what the argument needs about it. Volume 2 gives the analytic number theory: L-functions, Landau's theorem, the prime number theorem in progressions, primes in windows, zero density for quadratic twists, and sets without three-term progressions. Volume 3 gives CM fields, class field theory, local duality and CM elliptic curves. Volume 4 gives hermitian spaces over the adeles, reduction theory, automorphic forms on definite unitary groups, a simple trace formula and congruence subgroups. Volume 5 gives discrete series, Bessel subgroups, Weyl modules, the characters of $\mathrm{GL}_n$ over a finite field, and Satake parameters. Volume 6 gives the Weil representation, theta lifts and the seesaw, Bessel periods, the Siegel-Weil formula and the Rallis inner product formula. Volume 7 gives schemes, cohomology, period rings, Kisin modules and Fitting ideals. Volume 8 gives the Shimura varieties and the Galois representations attached to forms.

**Volumes 9 to 12, the argument.** Volume 9 proves Theorem A, which says that the lattice has short vectors. Volume 10 proves Theorem B, which says that there are enough of them to span. Volume 11 proves Theorem C, the lower bound for the covolume by a height argument. Volume 12 proves the existence of regular families of twists, by congruences and Selmer groups. Theorem C needs this result. Each argument volume opens with the exact statement of its theorem and a plan of its proof, and closes with the proof.

### Why the volumes are in this order

The order follows five principles of the plan of the book.

*The whole proof first.* Volume 1 comes before all the theory because it shows the purpose of everything else. Without it, a reader of Volume 6 sees a theta lift and does not know why the argument needs its size. With it, the reader knows the exact statement that the lift must satisfy, where it enters the star inequality, and which loss the argument can afford. Each later volume opens by showing its place on this map.

*Theory by subject, in the order of learning.* The background follows the order in which a student learns it: analysis, then arithmetic, then automorphic forms, then representations, then theta, then geometry, then Galois representations. A later background volume can use an earlier one. In the source the folder `Lib` imports nothing from the folder `New`, so the background volumes can be read without the argument volumes.

*The classical theory first, then the form of the source.* Each background chapter states the textbook theory with a source before it defines the object of the source. The source often builds a narrower object than the literature, because it needs less. For example, its $\ell$-adic cohomology is defined as an Ext on test rings. The book shows the classical object first, so that the reader can measure the difference.

*The argument by theorem.* The folder `New` is cut into four volumes, one for each of Theorems A, B and C and one for the congruences. The folders of the source do not have this cut: they import each other in both directions. The book cuts by theorem because a reader judges one theorem at a time.

*Forward references are statements.* A volume can need a result that a later volume proves. Then it states that result in full, as a numbered theorem with its hypotheses and sizes, and links to the proof. It never says "by a later argument". So a reader can read Volume 1 in full and know exactly what is still to be proved: Theorems A, B and C, as stated in [Theorems A, B and C](/chapter/theorems-a-b-c/), and the background results that each volume states.

The order of reading is not the order of writing. The chapters of Volume 1 were written first, then the guide, then the opening chapters of Volumes 9 to 11, and the other volumes follow. So at a given edition some chapters of a path can be missing. Section 5 says how to see which.

### The size of the book

The plan aims at about 545,000 words: 30,000 for Volume 0, 45,000 for Volume 1, and 30,000 to 60,000 for each other volume. Volumes 0 and 1 are the book that most readers need. They come first, as one milestone. A reader who reads only these two volumes has a complete proof of the five theorems from Theorems A, B and C and the background results that Volume 1 states.
