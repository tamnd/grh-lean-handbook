---
title: Clashes of letters
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/LevelAndTwists.lean
decls:
  - New.Data.M
  - New.Data.liftWeight
  - New.Data.untwistedLiftChar_hasWeight
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Clashes of letters

The chapters of Volume 1 were written one at a time, and each follows the comments of the Lean files that it explains. So the same letter sometimes names two objects, and the same object sometimes has two letters. This section lists each clash that a reader of Volume 1 can meet, and it gives the choice of the book. A later edition of Volume 1 can use this list to remove the clashes. The list does not change any statement of Volume 1: in each chapter the letter is defined before it is used, or the clash is noted below.

### One letter for two objects

1. The letter $M$. In the book $M = p_0 p_1$ is the principal level, `New.Data.M`. [The main inequality](/chapter/main-inequality/) also uses $M$ for the main amount of the source, and [the data exist](/chapter/data-exist/) once puts $M = q_0 d$ in a proof. The book writes $\mathrm{main}$ for the main amount and does not give $q_0 d$ a letter.
2. The letter $t$. In the book $t = 5r$. [The prime sums](/chapter/prime-sums/) uses $t$ for the number $3 l_0 2^s$ in one proof, and other chapters use $t$ for a real variable and for an exponent. The book writes $u$ for a local real variable.
3. The letter $L$. In the book $L(s, \chi)$ is the $L$-function. The table of sizes in [the data and its sizes](/chapter/data-and-sizes/) writes $L = \log x$, and [the main inequality](/chapter/main-inequality/) writes $L = f a \log^4 b$ for the loss. The book writes $\log x$ and $\mathrm{loss}$.
4. The letter $\varepsilon$. In the book $\varepsilon$ is the scale exponent of the data. [The theorem and the plan](/chapter/theorem-and-plan/) uses $\varepsilon$ for the margin in the bound $R_{q_0}(y) \leq y^{-1/2+\varepsilon}$, and [Theorems A, B and C](/chapter/theorems-a-b-c/) uses it for the error of a near isometry. The book writes $\eta$ for the margin and $\varepsilon_0$ for the error.
5. The letter $\delta$. In the book $\delta$ is the bound of an index. [The data and its sizes](/chapter/data-and-sizes/) also writes $\delta = \min(1/200, \varepsilon/7)$. The book writes $\varepsilon_1$ for this number.
6. The letter $\sigma$. In Sections 2 to 4 $\sigma$ is an infinite place of $E$. In the lattice chapters it is an automorphism of $\mathbb{C}$. The book keeps both and says in each chapter which one it means.
7. The letter $\Lambda$. The book keeps $\Lambda(n)$ for the von Mangoldt function and $\Lambda(s, \chi)$ for the completed $L$-function (Section 4). [The twisted lattices](/chapter/twisted-lattices/) also uses $\Lambda$ for a lattice of $\mathbb{R}^n$ in a model case; the book writes $\mathcal{L}$ there.
8. The letter $\psi$. In the book $\psi$ is a Dirichlet character in a sum over characters, or an additive character in a Fourier sum. The model cases of Volume 1, for example in [Landau's criterion](/chapter/landau-criterion/), also use the Chebyshev function of the primes. The book writes it $\psi(x)$ with a real argument, and only where no character sum occurs.
9. The letter $E$. In the book $E$ is the CM field. The comments of the source write $E_\chi$ for the entire $L$-function, and so do two chapters of Volume 1. The book writes $\tilde L(s, \chi)$ (Section 4).
10. The letter $q$. In the book $q$ is a modulus and $q_0$ is the modulus of the parameters. [The main inequality](/chapter/main-inequality/) writes $q_0 = 2q$ in one proof and $q_0 = 18480 q$ in another, so $q$ has two meanings there. The book writes $q_0$ only.
11. The letter $c$. Volume 1 uses $c$ for a covolume bound, for $c_q$, and for constants. The book keeps $c$ for the covolume bound and $c_q$ with its subscript, and writes $C$ with a subscript for other constants.
12. The word "err". The book writes $\mathrm{err}_0$ for the unit $f a \log^3 b$, $\mathrm{err}(p)$ for a divisibility error, and $\mathrm{err}$ for the total error (Section 4).
13. The letter $\mathcal{P}$. Volume 1 uses it for a set of primes and for the Poincaré map. The book writes $\mathcal{P}$ for the Poincaré map and $U$ for a set of primes.

### Two letters for one object

1. The primes of the principal level: the book writes $p_0, p_1$. [The data exist](/chapter/data-exist/) writes $g_0, g_1$.
2. The Chowla and Selberg constant: the book writes $C_d$. [The weighted prime remainder](/chapter/weighted-prime-remainder/) writes $\mathrm{cs}_d$.
3. The remainder: the book writes $R_q(y)$. Volume 1 also writes $R_q(z)$, $R_q^{(d)}$ and $R$.
4. The constant of the parameters: the book writes $C_P$. Volume 1 also writes $c_P$ and $c$.
5. The local loss of an index: the book writes $e(\ell)$. Volume 1 also writes $\delta_\ell$.
6. A set of primes: the book writes $U$. Volume 1 also writes $T$, which the book keeps for the type of twists.
7. A twist: the book writes $\vartheta$ for the twists of the data and $\xi$ for an abstract twist. Volume 1 mixes them.
8. The Gram determinant: the book writes $\operatorname{Gram}(\xi)$. Volume 1 also writes $G(\xi)$, and it writes $G$ for the group as well as $\bar G$.
9. The power of a logarithm: the book writes $\log^5 b$. Volume 1 also writes $(\log b)^5$. Both are $(\log b)^5$.
10. The algebraic closure: the book writes $\bar{\mathbb{Q}}_\ell$. Volume 1 also writes $\overline{\mathbb{Q}_\ell}$.

### Clashes inside the source

Three clashes are in the comments of the Lean files, not in Volume 1.

1. The file of the rows writes $h$ for the gap, $h_2$ for half the gap, and $w_j$ for the weights of the lifts. The file of the data writes $\Delta$, $\Delta/2$ and $\kappa_j$. The book writes $\Delta$, $\Delta/2$ and $\kappa_j$.
2. The weight of the $j$-th lift is $\kappa_j(\sigma) = \kappa(\sigma) + (j + 1/2)\Delta$ in the file of the data. The comment of `New.Data.untwistedLiftChar_hasWeight` writes $\kappa_j = \kappa_0 + j\Delta$ with $\kappa_0 = \kappa + \Delta/2$, which is the same number. The comment of the target parameter writes $\kappa_s = \kappa + (s + 1/2)\Delta$ with $s$ a half-integer, which is a different indexing. The book uses $\kappa_j$ only for $j \in \mathbb{N}$, as Lean defines it.

Lean: `New.Data.liftWeight` (New/Reduction/Data/AdmissibleData.lean), `New.Data.untwistedLiftChar_hasWeight` (New/Reduction/Data/LevelAndTwists.lean).

3. The comment of one lemma of the filling step asks $b^{19} \leq M$. This is finding F-093 of the register. The book states the bound that Lean states.

Lean: `New.Data.M` (New/Reduction/Data/AdmissibleData.lean).

### Gaps in Volume 1

Volume 1 does not define every object that this chapter lists. It does not define the spaces $W_j$ and $V$, and it uses $\zeta_{q_1}$ before it defines $q_1$. It defines $c_q$ in three ways: as $\operatorname{Re} G_q(1)$, as a limit of the sums, and as a constant in an asymptotic formula. It uses $q_0$ under different hypotheses in different chapters. The book takes the definitions of Sections 2 to 5 as the definitions in all volumes.
