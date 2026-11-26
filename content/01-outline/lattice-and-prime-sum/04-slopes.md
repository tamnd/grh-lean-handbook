---
title: The slope inequality
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The slope inequality

This section gives the model case in rank $n$. It defines the degree and the slopes of a Euclidean lattice and proves the slope inequality for an injective map. The proof is Liouville's inequality of Section 2 for one determinant. Then it states the form of Bost with a filtration, and it gives a dictionary to the bounds of the source. The source does not use slopes, but the slope inequality is the standard form of the lower bound of the method.

### Degrees and slopes

**Definition (Euclidean lattice).** A *Euclidean lattice* $\bar{\mathcal{E}} = (\mathcal{E}, \|\cdot\|)$ is a free $\mathbb{Z}$-module $\mathcal{E}$ of finite rank $n$ with a Euclidean norm $\|\cdot\|$ on $\mathcal{E}_{\mathbb{R}} = \mathcal{E} \otimes \mathbb{R}$. Its *covolume* is
$$\operatorname{covol}(\bar{\mathcal{E}}) = \|e_1 \wedge \dots \wedge e_n\| = \bigl(\det \operatorname{Gram}(e_1, \dots, e_n)\bigr)^{1/2}$$
for a $\mathbb{Z}$-basis $e_1, \dots, e_n$ of $\mathcal{E}$. It does not depend on the basis. Its *degree* is $\widehat{\deg}\,\bar{\mathcal{E}} = -\log \operatorname{covol}(\bar{\mathcal{E}})$, and for $n \geq 1$ its *slope* is $\hat\mu(\bar{\mathcal{E}}) = \widehat{\deg}\,\bar{\mathcal{E}} / n$.

A sublattice $F' \subset F$ is *saturated* if $F/F'$ has no torsion. It carries the restricted norm. The *maximal slope* of $\bar F$ is
$$\hat\mu_{\max}(\bar F) = \max \{ \hat\mu(\bar F') : F' \subset F, \ F' \neq 0 \}.$$
The maximum exists, because saturated sublattices of rank $r$ give primitive vectors of $\bigwedge^r F$, and a lattice has only finitely many vectors of bounded norm.

**Example (Integral lattices).** Let $F = \mathbb{Z}^N$ with a norm whose Gram matrix $G$ in the standard basis has integer entries. Then every sublattice $F'$ has $\operatorname{covol}(\bar F')^2 = \det(U G U^{\mathsf T})$ for an integer matrix $U$. This is a positive integer. So $\widehat{\deg}\,\bar F' \leq 0$ for every $F'$, and $\hat\mu_{\max}(\bar F) \leq 0$. For the standard norm, $\hat\mu_{\max}(\mathbb{Z}^N) = 0$.

This is the rank-$n$ form of "a nonzero integer has absolute value at least $1$".

### The height of a map

Let $\bar{\mathcal{E}}$ and $\bar F$ be Euclidean lattices and let $\varphi\colon \mathcal{E}_{\mathbb{Q}} \to F_{\mathbb{Q}}$ be $\mathbb{Q}$-linear and not $0$. At the place $\infty$, let $\|\varphi\|_\infty$ be the operator norm of $\varphi_{\mathbb{R}}$. At a prime $p$, give $F_{\mathbb{Q}_p}$ the norm $\|v\|_p = \max_i |v_i|_p$ in the coordinates of a $\mathbb{Z}$-basis of $F$, and similarly for $\mathcal{E}$. Let $\|\varphi\|_p$ be the operator norm. It is a power $p^k$, and $\varphi(\mathcal{E}_{\mathbb{Z}_p}) \subset p^{-k} F_{\mathbb{Z}_p}$. For all but finitely many $p$, the matrix of $\varphi$ has $p$-integral entries and one entry that is a $p$-adic unit, so $\|\varphi\|_p = 1$. The *height* of $\varphi$ is
$$h(\varphi) = \sum_{p \leq \infty} \log \|\varphi\|_p .$$
If $\varphi(\mathcal{E}) \subset F$, the finite terms are $\leq 0$, and $h(\varphi) \leq \log\|\varphi\|_\infty$. The finite terms are the denominators of $\varphi$. They play the role of the index in the source.

### The slope inequality for an injective map

**Theorem (Slope inequality).** Let $\bar{\mathcal{E}}$ and $\bar F$ be Euclidean lattices, with $\mathcal{E}$ of rank $n \geq 1$, and let $\varphi\colon \mathcal{E}_{\mathbb{Q}} \to F_{\mathbb{Q}}$ be injective. Then
$$\widehat{\deg}\,\bar{\mathcal{E}} \leq n \bigl( \hat\mu_{\max}(\bar F) + h(\varphi) \bigr).$$

*Proof.* Let $F' = F \cap \varphi(\mathcal{E}_{\mathbb{Q}})$. It is a saturated sublattice of rank $n$, with the norm of $F$. Let $e = e_1 \wedge \dots \wedge e_n$ for a basis of $\mathcal{E}$ and let $f$ be a generator of $\bigwedge^n F'$. The map $\bigwedge^n \varphi$ sends $e$ to $c f$ for a number $c \in \mathbb{Q}^\times$, since $\varphi$ is injective.

At $\infty$. Let $u_1, \dots, u_n$ be an orthonormal basis of $\mathcal{E}_{\mathbb{R}}$. Then $e = \pm\operatorname{covol}(\bar{\mathcal{E}})\, u_1 \wedge \dots \wedge u_n$, and by Hadamard's inequality
$$|c| \, \|f\| = \|\bigwedge^n\varphi(e)\| = \operatorname{covol}(\bar{\mathcal{E}})\, \|\varphi u_1 \wedge \dots \wedge \varphi u_n\| \leq \operatorname{covol}(\bar{\mathcal{E}}) \prod_i \|\varphi u_i\| \leq \operatorname{covol}(\bar{\mathcal{E}})\, \|\varphi\|_\infty^n .$$
Since $\|f\| = \operatorname{covol}(\bar F')$, this is $\log|c| \leq \widehat{\deg}\,\bar F' - \widehat{\deg}\,\bar{\mathcal{E}} + n \log\|\varphi\|_\infty$.

At $p$. Let $\|\varphi\|_p = p^k$. Then $\varphi(\mathcal{E}_{\mathbb{Z}_p}) \subset p^{-k} F_{\mathbb{Z}_p} \cap F'_{\mathbb{Q}_p} = p^{-k} F'_{\mathbb{Z}_p}$, because $F'$ is saturated. So $\bigwedge^n\varphi(e) \in p^{-kn} \bigwedge^n F'_{\mathbb{Z}_p}$. Since $f$ generates $\bigwedge^n F'_{\mathbb{Z}_p}$, this gives $\log|c|_p \leq n \log\|\varphi\|_p$.

The product formula for $c$ gives $0 = \log|c| + \sum_p \log|c|_p$. Add the bounds:
$$0 \leq \widehat{\deg}\,\bar F' - \widehat{\deg}\,\bar{\mathcal{E}} + n\, h(\varphi).$$
Finally $\widehat{\deg}\,\bar F' = n\,\hat\mu(\bar F') \leq n\,\hat\mu_{\max}(\bar F)$. $\square$

This is Section 2 for the number $c$: Hadamard's inequality bounds it at $\infty$, integrality bounds it at each prime, and the product formula joins the bounds.

### The form with a filtration

Bost uses the inequality with a filtration. Let $\mathcal{E}_{\mathbb{Q}} = \mathcal{E}^0 \supset \mathcal{E}^1 \supset \dots \supset \mathcal{E}^N = 0$ be a filtration by subspaces, and let $\varphi_i\colon \mathcal{E}^i \to F_{i,\mathbb{Q}}$ be linear maps to Euclidean lattices $\bar F_i$ with $\ker \varphi_i = \mathcal{E}^{i+1}$. Give $\mathcal{E}^i \cap \mathcal{E}$ the norm of $\mathcal{E}$. Then
$$\widehat{\deg}\,\bar{\mathcal{E}} \leq \sum_{i=0}^{N-1} \dim(\mathcal{E}^i/\mathcal{E}^{i+1}) \bigl( \hat\mu_{\max}(\bar F_i) + h(\varphi_i) \bigr).$$
*Sketch.* Apply the theorem to the injective map induced by $\varphi_i$ on each graded piece $\mathcal{E}^i/\mathcal{E}^{i+1}$, and add. The degree is additive in exact sequences, because covolumes multiply. $\square$

In the applications of Bost, $\mathcal{E}$ is a space of sections, the filtration is by the order of vanishing at a point, and $\varphi_i$ takes the $i$-th jet. The source cites Bost, *Algebraic leaves of algebraic foliations over number fields* (2001), and Gaudron, *Pentes des fibrés vectoriels adéliques sur un corps global* (2006), for this circle of ideas. Its list of references gives no place in these works.

### A dictionary to the source

The source has the two bounds of the slope inequality, in the language of Gram determinants. The dictionary below uses the notions of [twisted lattices](/chapter/twisted-lattices/).

| slopes | source |
|---|---|
| Euclidean lattice $\bar{\mathcal{E}}$ | the target forms, with an integral structure at each $\iota\colon \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ and the norms of the lifts $\Theta_1 y$ |
| $\widehat{\deg} \geq -c/2$ for the span of $y$ | covolume at most $c$: $\lvert\det \operatorname{Gram}(\sigma\Theta_1 y)\rvert \leq e^c$ for every $\sigma$ |
| finite part of $h(\varphi)$ | index at most $\delta$: a matrix with determinant of valuation at most $e(\ell)$ makes $y$ integral at $\iota \mid \ell$, with $\sum_\ell e(\ell) \log \ell \leq \delta$ |
| upper bound for $\widehat{\deg}$ | Theorem C: $c + 2\delta \geq d_T(\mathrm{main} - 3 f a \log^4 b)$ |
| lower bound for $\widehat{\deg}$ | Hadamard's inequality for the short forms of Theorem A |

In this dictionary Theorem C says: a sublattice of nearly full rank $n \geq (1 - 4/b^2) d_T$, corrected by its denominators, has degree at most about $-\tfrac12 d_T \cdot \mathrm{main}$. Its vectors are long: their squared lengths are about $\exp(\mathrm{main})$ or more on average. Theorem C does not bound $\hat\mu_{\max}$: it says nothing about sublattices of small rank. The method does not need more, because Theorem B gives a family of nearly full rank.

The proof of Theorem C has the shape of the proof above. It takes one family of numbers, the ratios $Z(1)/Z(\xi_\iota)$ of the Gram determinants of the lifts for the trivial twist and for a twist $\xi_\iota$, and bounds it at every place. The main amount enters through this bound: the family $Z(1)/Z(\xi_\iota)$ has height at most $d_T(b + f a \log^4 b - \mathrm{main})$, which is a large negative number. This is `New.Data.heightLe_chainDeterminant_one_div` in the source. [Theorems A, B and C](/chapter/theorems-a-b-c/) gives the details.

**Remark (Formalization).** The source has no Euclidean lattices over $\mathbb{Z}$, no degrees and no slopes. The target is a complex vector space with an integral structure for each $\iota$ ([twisted lattices](/chapter/twisted-lattices/)). The bounds are stated as two predicates on a family $y$: `New.TwistedLattice.CovolumeLe` (a bound for every conjugate of a Gram determinant, for the trivial twist only) and `New.TwistedLattice.IndexLe` (a bound for the denominators, with one matrix for each $\iota$ that works for all twists). The argument needs no maximal slope, so slopes are a guide to the reader, not an input of the proof.
