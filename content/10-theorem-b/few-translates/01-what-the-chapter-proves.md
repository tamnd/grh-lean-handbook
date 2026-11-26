---
title: What the chapter proves
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/SecondMoment/PositiveType.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the first layer of the proof of Theorem B. It is finite-dimensional linear algebra over $\mathbb{C}$, and it knows nothing about automorphic forms. It proves three results. The first turns two numbers, an error of near isometry and a second moment, into a statement of average position, called spread. The second turns spread into a small set of translates whose images span almost all of the target. The third is a lemma on functions of positive type on a finite group, which [the chapter on moments](/chapter/moments/) uses to show that the elements of $\bar G$ with a singular minor are rare.

The place of the chapter in the argument is shown in [Theorem B and its plan](/chapter/theorem-b-plan/). Theorem B asks for a set $t \subseteq \bar G$ with $\#t \cdot \dim \mathrm{src} \leq 5\, d_T \log(1 + 2b^2)$ such that the images $s\mathfrak{p}(\mathrm{src})$, $s \in t$, span at least $(1 - 4/b^2)\, d_T$ dimensions of the target. [The section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) reduces this to two inequalities (NI) and (SM) for the scaled Poincaré map. This chapter proves the reduction. The rest of the volume proves (NI) and (SM). [The plan of the whole proof](/chapter/theorem-and-plan/) shows where Theorem B enters the main inequality.

### The question

Let $V$ and $W$ be finite-dimensional complex vector spaces with $\dim V = d$ and $\dim W = n$, and let $B_s : V \to W$ be linear maps indexed by a set $\Theta$. When do a few of the images $B_s(V)$ span almost all of $W$? A lower bound for the number is clear: $k$ images span at most $kd$ dimensions, so one needs at least $n/d$ of them. The question is when about $n/d$ images suffice, up to a factor that does not depend on $n$ and $d$.

Two extreme cases show what can happen. If all $B_s$ have the same image, no number of them spans more than $d$ dimensions. If the images are in general position, then $\lceil n/d \rceil$ of them span $W$. The source needs a condition between these extremes that it can verify for Poincaré series. The verification is a computation of inner products, so the condition must be a statement about inner products and their averages.

### A model case

Let $\Gamma = \mathbb{Z}/n\mathbb{Z}$ act on $T = \mathbb{C}^n$ by the cyclic shift, $\rho(s)e_j = e_{j + s}$, with indices modulo $n$. Let $1 \leq d \leq n$, let $S = \mathbb{C}^d$, and let $B : S \to T$ send $e_i$ to $e_i$ for $0 \leq i < d$. The translates $\rho(s)B$ have the images $\mathrm{span}(e_s, \dots, e_{s + d - 1})$, which are blocks of $d$ consecutive coordinates. If $d$ divides $n$, then the $n/d$ shifts $s = 0, d, 2d, \dots$ span $T$, and no smaller number does.

Now compute the two numbers of this chapter. The map $B$ is an isometry. The operator $B^*\rho(s)B$ on $S$ has the matrix entries $\langle \rho(s)e_j, e_i\rangle$, which are $1$ if $i \equiv j + s \pmod n$ and $0$ otherwise. Its squared Hilbert-Schmidt norm is the number of pairs $(i, j)$ in $\{0, \dots, d - 1\}^2$ with $i \equiv j + s$. Each pair has exactly one such $s$, so

$$\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 = d^2, \qquad\text{that is,}\qquad \dim T \cdot \sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 = |\Gamma|\,(\dim S)^2.$$

This equality is the hypothesis of the spread theorem below with the error $0$. The [section on the greedy cover](/chapter/few-translates/#the-greedy-cover) then gives the right count $n/d$ up to a logarithm.

Compare the opposite extreme. If $\rho(s)$ acts as the identity on the image of $B$ for every $s$, then $B^*\rho(s)B = B^*B = 1_S$ for the isometry $B$, so $\|B^*\rho(s)B\|^2 = d$ and the sum is $|\Gamma| d$. Then $\dim T \cdot \sum_s \|B^*\rho(s)B\|^2 = |\Gamma|\, n d$, which exceeds $|\Gamma| d^2$ by the factor $n/d$. A large second moment means that the translates overlap.

### Why a second moment

The quantity $\|B^*\rho(s)B\|^2$ measures the overlap of the image of $B$ with the image of $\rho(s)B$. For isometries $B$ it is the sum of the squared cosines of the principal angles between the two images. Its mean over $s$ cannot be small for every $B$. [The section on one translate](/chapter/few-translates/#one-translate) proves the Cauchy-Schwarz bound

$$\frac{1}{|\Gamma|}\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \geq \frac{(\dim S)^2}{\dim T}$$

for an isometry $B$ (Exercise 2). In the model case it is an equality. In general, a family whose mean is close to this least value behaves like a family of subspaces in random position: no subspace $F$ of $T$ can contain a large part of every translate. This is the content of spread.

The mean has one term that is never small: the term $s = 1$, which is $\|B^*B\|^2 = \dim S$ for an isometry. So the mean is at least $\dim S/|\Gamma|$, and the hypothesis can hold with a small error only if $|\Gamma|$ is much larger than $\dim T/\dim S$. In the source, $\bar G$ is a product of general linear groups $\mathrm{GL}_r$ over the residue fields of the two level primes, with $r$ the large rank of the data, and the identity part of the second moment is at most $b^{-11kf}$ times the main part, by [the standing hypotheses](/chapter/theorem-b-plan/#conventions-that-change-the-meaning).

### What the chapter uses

The chapter uses finite-dimensional linear algebra over $\mathbb{C}$: orthogonal projections, adjoints, the trace, and the dimension formula $\dim(F + G) + \dim(F \cap G) = \dim F + \dim G$. It uses the Cauchy-Schwarz inequality in the space of linear maps with the Hilbert-Schmidt inner product. The last section uses additive characters of a finite field and their orthogonality, which is in [the notation of Volume 0](/chapter/notation/). Nothing in the chapter depends on another chapter of this volume.

### The plan of the chapter

[Section 2](/chapter/few-translates/#hilbert-schmidt-norms-and-near-isometries) defines the Hilbert-Schmidt norm in the form of the source and the near isometry in mean square. It compares the near isometry with the usual notion, and it proves the rules that the chapter on moments uses to pass from the Poincaré map $P$ to its good part $e_0P$.

[Section 3](/chapter/few-translates/#one-translate) proves that a near isometry with a small second moment spreads. The proof is one application of the Cauchy-Schwarz inequality, followed by the near isometry on one well-chosen subspace.

[Section 4](/chapter/few-translates/#the-greedy-cover) proves that a spread family has a small subfamily whose images span almost everything. The choice is greedy: at each step take the translate that adds the most dimensions. Spread says that this step removes a fixed share of the missing dimensions. So the missing share decays like $e^{-l\cdot\mathrm{rate}}$ after $l$ steps, with $\mathrm{rate} = 2\dim V/(5\dim W)$, and $\log(1/(16\varepsilon))/\mathrm{rate}$ steps leave at most the share $16\varepsilon$. This is the logarithm in Theorem B.

[Section 5](/chapter/few-translates/#positive-type-and-singular-minors) proves the lemma on positive type. Let $\Theta \geq 0$ be a function of positive type on a finite group $G$ that acts on $k^n$, with $k$ a field with $q$ elements. If the stabilizers of nonzero vectors have small $\Theta$-mass, then the set of $s$ where a minor $\det(A_1^{\mathsf T}\pi(s)A_0)$ vanishes has $\Theta$-mass at most about $2\Theta(G)/q$. The proof counts the kernel of the minor by an additive character and bounds the character sum by the Cauchy-Schwarz inequality in a tensor product.

Section 6 has the exercises and the notes.

### The sketch of the main proof

Here is the whole argument for the first two results in five lines. Let $T_0$ be the target, $W \subseteq T_0$ a subspace with share $\alpha$, and $\Sigma = \sum_s \rho(s)BB^*\rho(s)^*$.

1. $\sum_s \|\mathrm{pr}_W\rho(s)B\|^2 = \operatorname{Re}\langle \mathrm{pr}_W, \Sigma\rangle_{\mathrm{HS}} \leq \|\mathrm{pr}_W\|\,\|\Sigma\| = \sqrt{\alpha\dim T_0}\,\|\Sigma\|$.
2. $\|\Sigma\|^2 = |\Gamma|\sum_s\|B^*\rho(s)B\|^2$, the second moment.
3. So some $s$ has $\|\mathrm{pr}_W\rho(s)B\|^2 \leq \sqrt{\alpha(1 + \varepsilon)}\dim S \leq \frac{1 + \alpha + \varepsilon}{2}\dim S$.
4. On the preimage $U$ of $W$ the near isometry gives $\dim U - \varepsilon\dim S \leq \|\mathrm{pr}_W\rho(s)B\|^2$. This is spread.
5. Spread makes each greedy step multiply the missing dimension by at most $1 - \mathrm{rate}$.

The rest of the chapter makes each line exact, with the hypotheses that Lean states.
