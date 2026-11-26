---
title: Lifts and projections
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.finrank_range_goodLift
  - New.Data.range_goodLift_le_range_inf_ker
  - New.Data.normSqAt_starProjection_range_goodLift_le
  - New.Data.liftCompression
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lifts and projections

This section studies the space $L_\vartheta$ of lifts, the range of the good lift $\Theta_\vartheta$ in the forms $\mathcal{F}_\vartheta$ on $V_j$. It proves three facts. The space $L_\vartheta$ has dimension $d$. It lies in the image of the good idempotent and in the kernel of a Hecke polynomial at every split place off the level. The orthogonal projection onto $L_\vartheta$ does not raise the norm at any $\sigma$ of a form that is orthogonal to the false lifts. Then it defines the compression of an operator to the lifts, whose determinant is $\Delta(\vartheta)$ of Section 1.

The third fact is the archimedean input of Section 7. The projection $\mathrm{pr}_\vartheta$ is defined by the inner product at $\sigma = 1$. An automorphism $\sigma$ of $\mathbb{C}$ does not respect it. So a bound for $\|\mathrm{pr}_\vartheta y\|_\sigma$ is not automatic, and it needs a property of $y$: orthogonality to the false lifts.

### Inputs

We use these results of earlier chapters, one line each.

- *Injectivity.* The single lift $\Theta_{j,\vartheta}$ is injective on the forms of level $J_M$ on $W_j$ (`New.Data.singleLift_injective`, [injectivity](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift)).
- *Range of the good lift.* A subspace $N$ that contains every lift $\Theta_\vartheta y$ of a good eigenform $y$ with $\Theta_\vartheta y$ in the range of some $e_c$ contains $L_\vartheta$ (`New.Data.range_goodLift_le`, [the lift keeps the good forms](/chapter/chain-determinant/#good-forms-and-the-factorization)).
- *Pieces of the good idempotent.* The range of $e_c$ lies in the range of $e_0$ for every good tuple family $c$ (`New.Data.range_tupleIdem_le`, same section).
- *The root kills the lift.* For $w$ split with $w, \bar w$ off the places of the pair, $H_w(x_w)\,\Theta_{j,\vartheta}\,y = 0$ for every form $y$ of level $J_M$, with $x_w$ = `liftHeckeRoot w` (`New.Data.heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero`, [Hecke polynomials of the lift](/chapter/single-theta-lifts/#hecke-polynomials-of-the-lift)).
- *Projection bound.* If $e_0$ is a central idempotent, $w$ is split off the level, $Z \subseteq \mathrm{range}(e_0)\cap\ker H_w(x_w)$, and $y$ is orthogonal to the false lifts for $e_0$ and $Z^\perp$, then $\|\mathrm{pr}_Z y\|_\sigma^2 \leq \|y\|_\sigma^2$ for every $\sigma$ (`New.DescentPair.normSqAt_starProjection_le`, [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms)).
- *Split places exist.* Infinitely many finite places $w$ of $E$ are split and lie, with $\bar w$, outside the places of a given descent pair (`New.Selmer.frequently_isSplit_notMem_places`, [lift settings](/chapter/main-summands/#lift-settings-and-representations-of-a-type)).
- *The good idempotent is central.* $e_0$ is a central idempotent of the group algebra of $\mathsf{G}_M$ (`New.Data.isCentralProj_e₀`, [labels and the good idempotent](/chapter/upper-bound-objects/#labels-and-the-good-idempotent)).

Recall from [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms) that the false lifts at $w$ for $e_0$ and a subspace $Z'$ are $\mathrm{FL}_w(e_0, Z') = \mathrm{range}(e_0)\cap\ker H_w(x_w)\cap Z'$. A form is orthogonal to the false lifts if it is orthogonal to $\mathrm{FL}_w(e_0, Z')$ for every split $w$ off the level. In this chapter $Z' = L_\vartheta^\perp$. So a false lift is a form that the good idempotent and the Hecke polynomial at $w$ cannot tell from a lift, but that is orthogonal to all the lifts.

### The dimension of the lifts

**Lemma (Dimension of the lifts).** For every twist $\vartheta$ and $1 \leq j \leq m$,

$$\dim L_\vartheta = \dim\{\text{good forms on } W_j\} = d .$$

Lean: `New.Data.finrank_range_goodLift` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The good lift is the restriction of the single lift to the good forms, which are forms of level $J_M$. The single lift is injective, so the good lift is injective. An injective linear map keeps the dimension of its source. $\square$

So in the identity $Z_j(\vartheta)\,\Delta(\vartheta) = C\rho_j(\vartheta)^d$ the operator on $L_\vartheta$ and the operator $U^\circ$ on the good forms have the same rank $d$. The bound $\exp(-\dim L_\vartheta\cdot r\beta)$ of `ClearsProjection` also becomes $\exp(-d r\beta)$ by this lemma.

### Where the lifts lie

**Lemma (Where the lifts lie).** Let $w$ be a finite place of $E$ with $\bar w \neq w$ and $w$ outside the places of the $j$-th descent pair at $\vartheta$ and their conjugates. Then

$$L_\vartheta \subseteq \mathrm{range}(e_0)\cap\ker H_w(x_w).$$

Lean: `New.Data.range_goodLift_le_range_inf_ker` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Apply the lemma on the range of the good lift to $N = \mathrm{range}(e_0)\cap\ker H_w(x_w)$. This is a subspace. Let $y$ be a good eigenform such that $\Theta_\vartheta y$ is in the range of $e_c$ for a good tuple family $c$. By the lemma on pieces, $\Theta_\vartheta y$ is in the range of $e_0$. The form $y$ is good, so it has level $J_M$, and the root kills its lift: $H_w(x_w)\Theta_\vartheta y = 0$. So $\Theta_\vartheta y \in N$. The lemma on the range of the good lift gives $L_\vartheta \subseteq N$. $\square$

In other words, $L_\vartheta$ lies in $\mathrm{range}(e_0)\cap\ker H_w(x_w)$, and the false lifts are the part of this space orthogonal to $L_\vartheta$. The space $\mathrm{range}(e_0)\cap\ker H_w(x_w)$ splits as $L_\vartheta \oplus \mathrm{FL}_w(e_0, L_\vartheta^\perp)$.

### The projection bound on the lifts

**Theorem (Projection to the lifts).** Let $y \in \mathcal{F}_\vartheta$ be orthogonal to the false lifts for $e_0$ and $L_\vartheta^\perp$. Then for every $\sigma \in \mathrm{Aut}(\mathbb{C})$,

$$\|\mathrm{pr}_\vartheta\,y\|_\sigma^2 \leq \|y\|_\sigma^2 .$$

Lean: `New.Data.normSqAt_starProjection_range_goodLift_le` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* By the input on split places, there is a finite place $w$ that is split and lies, with $\bar w$, outside the places of the pair. One such $w$ is enough. A split place has $\bar w \neq w$. By the previous lemma, $Z = L_\vartheta$ lies in $\mathrm{range}(e_0)\cap\ker H_w(x_w)$. The idempotent $e_0$ is central. So the projection bound of [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms) applies with $Z = L_\vartheta$, and it gives the claim. $\square$

The proof of the projection bound in the earlier chapter is short, and we recall it to show where each hypothesis enters. Write $y = z + x$ with $z \in L_\vartheta$ and $x \in \ker e_0 + \mathrm{range}\,H_w(x_w)^\dagger$, where the dagger is the adjoint of the Hecke polynomial. This uses the orthogonality to the false lifts. Vectors of $\ker e_0$ are orthogonal at every $\sigma$ to the range of $e_0$, because $e_0$ is self-adjoint for every $\langle\cdot,\cdot\rangle_\sigma$. Vectors in the range of the adjoint are orthogonal at every $\sigma$ to the kernel of $H_w(x_w)$. So $x$ is orthogonal to $L_\vartheta$ at every $\sigma$. At $\sigma = 1$ this gives $\mathrm{pr}_\vartheta y = z$, and at $\sigma$ it gives $\|z\|_\sigma^2 \leq \|z + x\|_\sigma^2$.

The bound at $\sigma = 1$ is Bessel's inequality and needs no hypothesis. At other $\sigma$ it can fail for a general form. The value $\sigma(\mathrm{pr}_\vartheta y)$ is not the projection of anything for the pairing $\langle\cdot,\cdot\rangle_\sigma$, because $\sigma$ need not commute with complex conjugation. The theorem avoids this, because the decomposition $y = z + x$ is orthogonal at every $\sigma$ at once.

### The compression

**Definition (Compression to the lifts).** For a family $U$ of operators $U_\vartheta$ on $\mathcal{F}_\vartheta$, the compression of $U_\vartheta$ to the lifts is the operator

$$\mathrm{pr}_\vartheta\,U_\vartheta\big|_{L_\vartheta} \colon L_\vartheta \to L_\vartheta, \qquad z \mapsto \mathrm{pr}_\vartheta(U_\vartheta z).$$

Its determinant is $\Delta(\vartheta)$.

Lean: `New.Data.liftCompression` (New/OneLift/LiftVolumeHeight.lean).

In Lean the projection is `orthogonalProjectionOnto` of the subspace $L_\vartheta$, with values in $L_\vartheta$, and the restriction is `domRestrict`. The determinant is `LinearMap.det` on the finite dimensional space $L_\vartheta$. The compression is the operator $\mathrm{pr}_K\,U\,\iota_K$ of [the determinant lemma of Section 2](/chapter/lift-volume-height/#determinants-norms-and-integral-scalings) with $K = L_\vartheta$.

**Remark (Formalization).** The determinant is taken on $L_\vartheta$, not on $\mathcal{F}_\vartheta$. The compression is a map of $L_\vartheta$ to itself because `orthogonalProjectionOnto` has values in the subspace. The dimension $d$ is positive (`New.Data.targetDim_pos`), but no proof of this chapter uses that fact.

### What the section gives

Section 7 uses the three results in this way. The dimension lemma fixes the exponent $d$ in the bounds of the determinant. The projection theorem bounds every eigenvalue of the compression of $U_1$ at every $\sigma$: an eigenvector $z$ with eigenvalue $\alpha$ gives $|\sigma(\alpha)|^2\|z\|_\sigma^2 = \|\mathrm{pr}_1 U_1 z\|_\sigma^2 \leq \|U_1 z\|_\sigma^2$, because $U_1 z$ is orthogonal to the false lifts by property 3. The compression itself is the operator whose determinant enters the identity $Z_j(\vartheta)\Delta(\vartheta) = C\rho_j(\vartheta)^d$.
