---
title: What the chapter proves
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter proves input 4 of [the four inputs](/chapter/theorem-c-plan/#the-four-inputs) of Theorem C. It bounds the height of the quotient of two Gram determinants of one lift: the determinant at the trivial twist over the determinant at a twist from a regular family. The whole chapter is the proof of one file, `New/OneLift/LiftVolumeHeight.lean`. The file defines a comparison operator, proves that the operators built from the gluing maps are comparison operators, and then proves the height bound.

### The statement

Fix $1 \leq j \leq m$. Let $W_j$ be the hermitian space of rank $r$ of the $j$-th lift and $V_j$ the definite space of rank $r + t$ ([the data and its sizes](/chapter/data-and-sizes/)). For a twist $\vartheta$, let $\Theta_\vartheta = \Theta_{j,\vartheta}$ be the good lift: the theta lift at $\vartheta$ on the good forms on $W_j$, with values in the forms on $V_j$ ([the chain determinant](/chapter/chain-determinant/#good-forms-and-the-factorization)). Let $d$ be the dimension of the good forms on $W_j$. For an $m$-fold twist $\xi$, the *lift determinant* is

$$Z_j(\xi) = |\det|^2\big(\Theta_{\xi^j}\big) = \det\big(\Theta_{\xi^j}^*\,\Theta_{\xi^j}\big).$$

Lean: `New.Data.liftDeterminant` (New/Determinant/Chain/NormOfChain.lean).

Here $\xi^j$ is the $j$-th power of $\xi$ as a tame character, and $|\det|$ is Mathlib's `LinearMap.normDet`. Let $\theta$ be a regular family of $m$-fold twists, one twist $\theta(\iota)$ for each prime $\ell$ and each isomorphism $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ ([regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists)). Heights are those of [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers).

**Theorem (The height of one lift determinant).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most

$$d\,k\,\big(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}\big).$$

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

Here $k = r + 1 - m$, $\mathrm{denominatorBudget} = f a\log^3 b/(m k)$, and $\mathrm{directionAmount}$ is the sum over the infinite places of the size of a derivative less its prime sum ([regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists)). In Lean the factor $d$ is `D.targetDim`, the dimension of the target forms, and the proof uses `targetDim_eq_finrank_goodForms_spaceW` to identify it with the dimension of the good forms on $W_j$.

Section 7 proves the theorem. It also proves the corollary that the proof of Theorem C uses: there is a family with small ratios for which the bound reads $d\,(f a\log^4 b/m - k\cdot\mathrm{directionAmount})$ for every $j$.

### The method

The source does not compute $Z_j(\vartheta)$. It compares $Z_j(\vartheta)$ with $Z_j(1)$ through an operator $U_\vartheta$ on the forms on $V_j$. Let $L_\vartheta$ be the range of $\Theta_\vartheta$, the space of *lifts*, and let $\mathrm{pr}_\vartheta$ be the orthogonal projection onto $L_\vartheta$. Let

$$\Delta(\vartheta) = \det\big(\mathrm{pr}_\vartheta\,U_\vartheta\big|_{L_\vartheta}\big),$$

the determinant of the compression of $U_\vartheta$ to the lifts. Suppose that $\langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle = \rho_j(\vartheta)\,\langle y', U^\circ y\rangle$, with a positive definite operator $U^\circ$ that does not depend on $\vartheta$ and a number $\rho_j(\vartheta) \neq 0$. Then a lemma of linear algebra (Section 2) gives

$$Z_j(\vartheta)\,\Delta(\vartheta) = C\,\rho_j(\vartheta)^d, \qquad C = \det U^\circ \neq 0 .$$

Divide the identity at $\vartheta = \xi^j$ by the identity at $\vartheta = 1$, where $\rho_j(1) = 1$:

$$\frac{Z_j(1)}{Z_j(\xi)} = \frac{\Delta(\xi^j)}{\Delta(1)}\,\rho_j(\xi^j)^{-d}.$$

So the height of $Z_j(1)/Z_j(\xi)$ is at most the height of $\Delta(\xi^j)/\Delta(1)$ plus $d$ times the height of $\rho_j^{-1}$. The second height is [the height of the inverse ratio of Hecke values](/chapter/hecke-values/), which is at most $10 m x_1 + k(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$. The first height needs two bounds.

1. *Archimedean.* Every conjugate $\sigma(\Delta(1))$ is at most $\exp(3 d f m b\log^2 b)$. The eigenvalues of $\mathrm{pr}_1 U_1$ are bounded at every $\sigma$, because $U_1$ is short at every $\sigma$ and the projection does not raise the norm at $\sigma$ of a form orthogonal to the false lifts.
2. *$\ell$-adic.* At $\iota$, $|\iota(\Delta(\xi^j))| \leq \exp(d\,r\,\beta(\ell))$, where $\beta(\ell)$ is the denominator bound of the regular family. The operator $U_{\xi^j}$ keeps integrality at $\iota$, and an operator $\Lambda$ with $|\iota\det\Lambda| \geq \exp(-d r\beta(\ell))$ clears the denominators of the projection.

The five properties that the method needs are the fields of the structure `IsComparisonOperator` (Section 3). The operator of the source is

$$U_\vartheta = n_{\mathrm{Aut}}\,h_j^2\;\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*,$$

with the gluing maps of [the comparison operator, part 2](/chapter/comparison-operator-2/). Sections 3 to 5 prove the five properties for it.

### A model case

Take $d = 1$ and $V = \mathbb{C}^2$ with the standard inner product. Let the lift send the one good form to $v = (1, 2)$, and let $U = \mathrm{diag}(1, 0)$. Then $Z = |v|^2 = 5$. The compression of $U$ to the line $\mathbb{C}v$ is the scalar $\Delta = \langle v, Uv\rangle/\langle v, v\rangle = 1/5$. So $Z\,\Delta = \langle v, U v\rangle = 1$, which is the identity $Z\Delta = C\rho^d$ with $C\rho = 1$.

At the prime $5$, $\Delta = 1/5$ is not integral. The integral vector $(1, 0)$ projects to $\tfrac15 v$, so the projection to the line has denominator $5$. The operator $\Lambda = 5$ on the line clears it, and $|\iota_5(\det\Lambda)|_5 = 5^{-1} = \exp(-\log 5)$. The bound of item 2 reads $|\iota_5(\Delta)|_5 \leq \exp(\log 5) = 5$, and here it is an equality. In the source the rank is $d$, the denominator of the projection is bounded at every $\ell$ by the regular family, and the sum of the losses over all $\ell$ is the budget $d\,r\cdot\mathrm{denominatorBudget}$.

At infinity, $|\sigma(\Delta)| = 1/5$ for every $\sigma$. In general $\Delta(1)$ is a product of $d$ eigenvalues, and each eigenvalue of $\mathrm{pr}_1 U_1$ has absolute value at most $\exp(3 f m b\log^2 b)$ after any $\sigma$.

### The sections

1. This section.
2. Determinants of compressions, the norms $\|\varphi\|_\sigma^2$ of forms, and forms of valuation $0$ at a place.
3. The definition of a comparison operator, the operator $U_\vartheta$, and its inner products on the lifts.
4. Tight frames of integral tuples. They write $U_\vartheta$ as a sum of operators of rank one and prove that $U_\vartheta$ keeps integrality.
5. The size of $U_1$ at every $\sigma$, and the theorem that $U_\vartheta$ is a comparison operator.
6. The lifts: their dimension, the projection bound on the lifts, and the compression.
7. The height bound and its corollary.
8. Exercises, and notes and references.

### Imports

The file imports `New/OneLift/ComparisonOperator/GluingMaps.lean` and `New/OneLift/HeckeValues/TwistedValueHeights.lean`. The first belongs to chapter 14, [the comparison operator, part 2](/chapter/comparison-operator-2/), and the second to chapter 15, [Hecke values of character lifts](/chapter/hecke-values/). Both chapters are earlier than this chapter in `volume.yaml`, so no file of this chapter imports a file of a later chapter. We state each result of these chapters that we use, in one line with a link.

### Background

The background is in earlier volumes. Heights and their calculus are in [twisted lattices](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers) of Volume 1. The gauge, integral forms and the integrality of inner products are in [the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge) of Volume 4. Weyl modules, their Gram matrices and hook numbers are in [Weyl modules](/chapter/weyl-modules/). The lift, its injectivity and its Hecke polynomial are in [single theta lifts](/chapter/single-theta-lifts/), and the tested forms and the projection bound are in [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms).
