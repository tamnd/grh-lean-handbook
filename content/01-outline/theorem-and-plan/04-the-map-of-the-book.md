---
title: The map of the book
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The map of the book

The book has thirteen volumes, numbered from 0 to 12. Volume 0 is a guide. Volume 1, this volume, proves the five theorems from Theorems A, B and C, with full proofs of every step above them. Volumes 2 to 8 are the background theories, written by subject. Volumes 9 to 12 are the argument: one volume for each of Theorems A, B and C, and one for the congruences that Theorem C needs. This section gives a diagram of the volumes, the reading paths, and the chapter map of Volume 1.

### The thirteen volumes

The diagram shows which volumes use which. Read it from the bottom up, as the chain of Section 2.

```text
              Vol 0  Guide
                |
              Vol 1  The proof in outline
                |    (states A, B and C; proves the rest)
     +----------+----------+-----------+
     |          |          |           |
   Vol 9      Vol 10     Vol 11 <--- Vol 12
   Thm A      Thm B      Thm C       Congruences
     |          |          |           |
     +----------+-----+----+-----------+
                      |
     the background theories, Volumes 2 to 8:
       2  Analytic number theory
       3  Number fields, class field theory
          and complex multiplication
       4  Unitary groups and automorphic forms
       5  Representations of real, p-adic
          and finite groups
       6  The theta correspondence and the
          Siegel-Weil formula
       7  Cohomology and p-adic Hodge theory
       8  Shimura varieties and Galois
          representations
```

The order of the background volumes is the order of learning: analysis, then arithmetic, then automorphic forms, then representations, then theta, then geometry, then Galois representations. Each background volume can be read without the argument volumes. Each argument volume opens with the exact statement of its theorem and a plan of its proof, and closes with the proof. In the source the background is the folder `Lib`, which imports nothing from the folder `New` of the argument.

### The reading paths

Each path starts with Volume 0 and this volume. A path lists the volumes in the order in which to read them. The numbers in parentheses are chapters.

```text
The design        0 -> 1
  (to judge the method)

The analytic part 0 -> 1 -> 2
                    -> the size chapters of 9 and 10

Theorem A         0 -> 1 -> 3 (CM) -> 4 (1, 2)
                    -> 6 (1 to 3) -> 9

Theorem B         0 -> 1 -> 4 -> 5 (1 to 3)
                    -> 6 (4) -> 10

Theorem C         0 -> 1 -> 6 -> 7 -> 8
                    -> 11 -> 12

The Lean reader   0 (5 to 8), then any chapter
  (to check the formalization), with its Lean lines
```

[How to read this book](/chapter/how-to-read/) gives the paths with the chapters of each volume, and the form and the status of a chapter.

### The chapter map of Volume 1

Volume 1 follows the chain of Section 2 from the top down. Chapters 2 to 4 are the analytic reduction, from the five theorems down to the one-sided bound. Chapter 5 explains the method. Chapters 6 to 12 set up the data, the prime sums and the lattices, and state Theorems A, B and C. Chapter 13 proves the star inequality and the end of the proof.

1. [The theorem and the plan](/chapter/theorem-and-plan/). This chapter: the five statements, the status of the claim, the plan, the idea and the maps.
2. [From the half-plane to the line](/chapter/half-plane-to-line/). The reflection of zeros for every Dirichlet character, primitive or not, and the five theorems from the half-plane theorem.
3. [The weighted prime remainder](/chapter/weighted-prime-remainder/). The weights $\lambda = \Lambda(1 - \chi_K)$ on $n \equiv 1 \bmod q$, the remainder $R_q$, the constant $c_q$, and the poles of the Mellin transform with the sign of each residue.
4. [Landau's criterion](/chapter/landau-criterion/). Landau's theorem for Dirichlet series with coefficients of one sign, and the criterion: a one-sided bound for every prime $d$ of a class gives no zeros in $\operatorname{Re} s > \beta$. The choice of $d$ through the quadratic twists.
5. [Why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/). The idea of the method of Section 3 in full, with the model cases of Liouville and Bost.
6. [Fields, places and twists](/chapter/fields-places-twists/). The parameters $q_0$ and $d$, the fields $K$ and $E = K(\zeta_{q_1})$, the places of $E$ read in $(\mathbb{Z}/q_1)^\times$, and the twists.
7. [The data and its sizes](/chapter/data-and-sizes/). Every field of the data, the five scale inequalities, the table of sizes and the weights.
8. [The data exist](/chapter/data-exist/). Sets with no three-term progressions, primes in windows, and the recipe for the data.
9. [Prime sums and the total remainder](/chapter/prime-sums/). The prime sums, the main amount, and the identity for $\mathrm{rem}$ in terms of $R_{q_0}$ and $R_1$.
10. [Twisted lattices](/chapter/twisted-lattices/). Index, covolume, heights, the product formula, and the inequality $c + 2\delta \geq 0$ in its general form.
11. [The lattice of integral target forms](/chapter/integral-target-forms/). The target forms, the target lattice, and its volume, which is a chain determinant.
12. [Theorems A, B and C](/chapter/theorems-a-b-c/). The exact statements, with their sizes and errors, and a plan of each proof.
13. [The main inequality and the end of the proof](/chapter/main-inequality/). The star inequality with every error term, the one-sided bound, the prime number theorem at the second cut-off, and the half-plane theorem.

The chapters depend on each other as follows. An arrow points from a chapter to a chapter that uses it.

```text
 6 -> 7 -> 8 ---------------------+
      |                           |
      +--> 9 ---------+           |
      |               v           v
      +--> 11 -----> 12 -------> 13 --> 2 --> the five
           ^                      ^           theorems
 10 -------+                      |
                                  |
 3 -> 4 --------------------------+
```

Chapter 3 is also used by chapters 9 and 13, which use the remainder $R_q$ and the prime number theorem for it. Chapter 13 gives the one-sided bound, and with the criterion of chapter 4 it proves the half-plane theorem. Chapter 2 turns that into the five theorems. Chapter 5 explains the method, and no proof in another chapter depends on it. Chapter 1 uses nothing.
