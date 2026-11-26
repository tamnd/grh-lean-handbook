---
title: Exercises and notes
lean:
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - New/Spanning/MainTerm/BadTypes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. Let $A$ be an endomorphism of a finite-dimensional vector space $X$ with $A(X) \subseteq U$ for a subspace $U$. Prove that $\operatorname{tr}(A) = \operatorname{tr}(A|_U)$. Deduce the lemma on the trace on good forms from it. *Hint.* Extend a basis of $U$ to a basis of $X$ and look at the rows of the matrix of $A$ below the block of $U$.

2. Let $A = 0$ on $\mathbb{C}$ and $A' = 0$ on $\mathbb{C}^2$. Show that $\operatorname{tr}(A^n) = \operatorname{tr}(A'^n)$ for all $n \geq 1$ but that the characteristic polynomials differ. Then show that if $\operatorname{tr}(A^n) = \operatorname{tr}(A'^n)$ for all $n \geq 1$, the characteristic polynomials agree up to a factor $X^j$. *Hint.* For the second part, apply the proof of the lemma on traces of powers to the polynomials $P$ with $P(0) = 0$; they separate the nonzero eigenvalues.

3. Prove that the number of primitive polynomials of degree $r$ over $\mathbb{F}_q$ is exactly $\varphi(q^r - 1)/r$. List them for $q = 2$ and $r = 3$. *Hint.* The $r$ roots of a primitive polynomial are the conjugates $\xi, \xi^q, \dots, \xi^{q^{r-1}}$ of one generator $\xi$ of $\mathbb{F}_{q^r}^\times$, and they are distinct. For $q = 2$, $r = 3$ there are $\varphi(7)/3 = 2$ of them: $X^3 + X + 1$ and $X^3 + X^2 + 1$.

4. Let $r = 2$ and $M = 1$, and let $q \geq 3$. Count exactly the monic quadratics over $\mathbb{F}_q$ that are not allowed, and compare the count with the bound $(1 + M + r)q^{r-1} = 4q$. *Hint.* Use inclusion and exclusion over the three conditions: a square factor, a root at $0$, a root at $1$. Each of the three sets has $q$ elements. Any two of them meet in one polynomial, $X(X-1)$, $X^2$ or $(X-1)^2$, and the three have no common element. The answer is $3q - 3$.

5. Let $G$ be a finite group and $e$ a central idempotent of $\mathbb{C}[G]$. Prove that the coefficient of $e$ at the identity is $\dim(e\,\mathbb{C}[G])/|G|$. For $e = e_\pi$ the idempotent of an irreducible representation $\pi$, deduce that the coefficient is $(\dim \pi)^2/|G|$. *Hint.* The trace of left multiplication by $g$ on $\mathbb{C}[G]$ is $|G|$ if $g = 1$ and $0$ otherwise.

6. Let $\chi$ be a character of $\mathbb{F}_q^\times$. Show that the one-dimensional representation $\chi \circ \det$ of $\mathrm{GL}_2(\mathbb{F}_q)$ is not cuspidal. Explain why this removes the term $1$ of Eichler's identity $h = \dim S_2(\Gamma_0(p)) + 1$ in the analogue for good forms. *Hint.* A representation is cuspidal when it has no nonzero vector fixed by the unipotent radical $N$ of the Borel subgroup. The group $N$ consists of matrices of determinant $1$.

7. In the lemma on sums of terms, suppose one applies the argument to $V$ alone and then to $V'$ alone. Show that one obtains $p, p' \in \mathcal{H}$ with $p_V = R_V$ and $p'_{V'} = R_{V'}$, and explain why the theorem on equal determinants of the Rallis operator does not follow. *Hint.* The theorem on equal determinants compares one element of $\mathcal{H}$ on two spaces. Nothing relates $p_{V'}$ to $p'_{V'}$.

## Notes and references

The comparison of the dimensions of spaces of automorphic forms on a definite and an indefinite form of the same group goes back to Eichler's work on quaternion algebras, whose trace identity for Brandt matrices is the model case of the opening section. The representation theoretic form is the correspondence of H. Jacquet and R. P. Langlands, *Automorphic Forms on GL(2)*, Lecture Notes in Mathematics 114, Springer, 1970, chapter 16, for the multiplicative group of a quaternion algebra.

For unitary groups the analogous comparisons use the simple trace formula with a test function that is cuspidal at one place. The source names as related work Y. Flicker and D. Kazhdan (1988), M. Harris and J.-P. Labesse, *Conditional base change for unitary groups* (2004), Proposition 1.10.5, J.-P. Labesse, *Changement de base CM et séries discrètes* (2011), Theorems 5.4 and 5.5, and J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120 (1989), chapter 1. These are given here as the source names them. The source does not follow any one of them. Its comparison of traces is proved in [the simple trace formula](/chapter/trace-formula/) from the definitions, for test functions built from Green's idempotents.

The cuspidal representations of $\mathrm{GL}_r(\mathbb{F}_q)$ attached to irreducible polynomials, and the degree formula for the characters of labels, are due to J. A. Green, *The characters of the finite general linear groups*, Transactions of the American Mathematical Society 80 (1955). The source names A. Dudko, *Plancherel measures for GL(n,q)*, arXiv 0806.1345 (2008), for the share of a type in the regular representation. The counts of polynomials over finite fields are standard. R. Lidl and H. Niederreiter, *Finite Fields*, Encyclopedia of Mathematics and its Applications 20, 1983, chapter 3, counts the primitive polynomials (Theorem 3.5) and the irreducible ones. The source proves the weaker counts it needs directly, and the totient bound in [primes in windows](/chapter/primes-in-windows/).

The research notes describe the step from equal traces to equal characteristic polynomials by Newton's identities. The source uses the generalized eigenspaces instead: the traces of all polynomials in an operator determine the dimensions of its generalized eigenspaces. Both routes need the trace of the identity, the case $n = 0$, and characteristic $0$. The research notes also name the Hecke algebras of Lib/Shimura/HeckeTower as an input of this step. The source uses instead the universal level algebras of Lib/Adelic/TraceFormula/LevelAlgebra.lean and the split Hecke operators of Lib/Weil/Unramified/SplitHecke.lean.

The rare bad types are the only place where the chapter needs the sizes of the level primes and of the field. The equal multiplicities need only $r \geq 2$, the gap $500r^3 + 10r^5 \leq \Delta$, and an even number of infinite places.

Status: drafted by a model from the Lean source at pin 72fead1 and the research notes. The chapter states what the source states. It does not claim that the source proof is correct, and it does not claim that the Generalized Riemann Hypothesis is proved.
