---
title: The data and its sizes
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The data and its sizes

This chapter defines the data $D$ of the argument and proves the bounds for every quantity that the data determine. The argument of the source fixes the parameters $P = (q_0, d)$ once ([fields, places and twists](/chapter/fields-places-twists/)). Then, for each large integer $x$, it uses one choice of data: three scales $x \leq x_1 \leq b$, two ranks $m$ and $r$, the exponent $s$ of a cyclotomic tower, a set of places with weights, two primes $p_0, p_1$ and a prime level $N$. Every later chapter takes $D$ as given and cites this chapter for its sizes. The chapter has one table that collects all the sizes ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)).

### Why the data are large

The method compares two bounds for the covolume of one lattice ([why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/)). The upper bound comes from short vectors (Theorem A), with the count of translates from Theorem B. The lower bound comes from a product formula (Theorem C). Both bounds contain the same main amount. The difference of the two bounds contains the total remainder of a prime sum, multiplied by the number $m$ of theta lifts. All other terms are errors. The method works only if every error is small against the main terms, and the errors are products of the quantities of the data: the number $f$ of infinite places of a field $E$ (about $x^{11}$), the ranks (about $x^5$), the gap between weights (about $x^{40}$), the order $a = xb$ of the prime sum, and logarithms of these.

The source makes all errors small by a single device. It separates the scales by fixed powers on a logarithmic scale:
$$C_P \ll \log\log b \ll \log x \ll \log x_1 \ll \log b .$$
Here $C_P$ is one constant that depends only on the parameters. Each sign $\ll$ is an explicit inequality with an explicit factor: $10^{12}$, $100$, $10^{6}$ and $10^{6}$. A fifth inequality compares $\log\log x_1$ with $\log\log b$. These five scale inequalities are fields of the data. Every other size in this chapter follows from them by comparison of logarithms.

Here is a picture in words. Put the four numbers $\log\log b$, $\log x$, $\log x_1$, $\log b$ on one line. The number $\log x$ is at least $100$ times $\log\log b$, and each of $\log x_1$ and $\log b$ is at least $10^6$ times the number before it. A quantity of the data that is a fixed power of $x$, such as $f \approx x^{11}$, has logarithm about $11 \log x$. That is negligible against $\log x_1$. A power of $\log b$, such as $\log^3 b$, has logarithm $3\log\log b$, which is negligible against $\log x$.

### How large is large

The numbers are not small. The constant $C_P$ is at least $64$ ([Lemma](/decl/New.Data.le_constantBound/)), so the first scale inequality gives
$$\log\log b \geq 10^{12} \cdot 64 = 6.4 \cdot 10^{13}.$$
So $\log b \geq \exp(6.4 \cdot 10^{13})$, and $x \geq (\log b)^{100}$. The source never evaluates these numbers. The argument is asymptotic in $x$, but each threshold is explicit. A statement "for large $x$" in this book always means: for data $D$ that satisfy the five scale inequalities. The next chapter ([the data exist](/chapter/data-exist/)) shows that such data exist for every large integer $x$.

### What the chapter uses

The chapter uses the parameters and the field of the previous chapter: the modulus $q_0$, the prime $d$, the field $K = \mathbb{Q}(\sqrt{-d})$, the tower degree $\operatorname{towerDeg}(s)$, the modulus $q_1 = q_0 \operatorname{towerDeg}(s)$ (`New.Parameters.q₁`), the field $E = K(\zeta_{q_1})$ with $\zeta_{q_1}$ a primitive root of unity of order $q_1$, its group of infinite places $\Phi \cong (\mathbb{Z}/q_1)^\times$, and the number $\Omega$. It uses one bound from the theory of the field that the book proves in Volume 9: the root discriminant $\mathrm{rd}_E$ lies in $[x^{10}, x^{12}]$. It uses the Minkowski bound for the class number, in a crude form. It uses no analytic number theory. The chapter is the reference for sizes: it proves nothing deep, but every later bound rests on it.

### The plan

Section 2 defines the constant $C_P$ and the scales, and states the five scale inequalities with their exponential forms. Section 3 defines the ranks $m$, $r$, the exponent $s$ and the derived ranks $k$, $t$, $\Delta$, $n_j$, and bounds them and the invariants of the field $E$. Section 4 defines the places $\Phi_a$ and $\Phi_b$ and the weights $\kappa$. Section 5 defines the primes $p_0$, $p_1$, the principal level $M = p_0 p_1$ and the level $N$, and bounds them with $\Omega$. Section 6 collects all sizes in one table and explains the automation that the source uses to prove them. Section 7 has the exercises and the notes.

The proofs are short. Each row of the table is a comparison of two quantities on a logarithmic scale. The proof writes the logarithm of each quantity as a linear expression in the six numbers
$$\log x, \quad \log x_1, \quad \log b, \quad \log\log x_1, \quad \log\log b, \quad C_P,$$
with explicit constants, and then uses the five scale inequalities. Only three rows need an outside input: the root discriminant, the class number, and the lower end $N_-$ of the range of the level.

Lean accepts the statements of this chapter if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
