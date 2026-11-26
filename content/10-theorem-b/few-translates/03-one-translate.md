---
title: One translate
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/SecondMoment/PositiveType.lean
decls:
  - New.inner_sum_sum_eq_card_mul
  - New.inner_hilbertSchmidtVector_translate
  - New.sq_sum_hilbertSchmidtNorm_orthoProj_comp_le
  - New.IsSpread
  - New.isSpread_of_second_moment
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One translate

This section proves the spread theorem: a near isometry whose translates have a second moment close to the least possible value spreads. The statement is [Theorem](/decl/New.isSpread_of_second_moment/), which [the section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) states with a short proof. Here the proof is complete. It has two parts. The first is an identity for sums over a finite group, which shows that the second moment is the squared norm of one vector. The second is the Cauchy-Schwarz inequality for that vector, followed by the near isometry on one subspace.

Throughout, $\Gamma$ is a finite group and $\rho$ is a representation of $\Gamma$ on a finite-dimensional complex inner product space $T$. The representation is *unitary* if $\langle\rho(s)x, \rho(s)y\rangle = \langle x, y\rangle$ for all $s, x, y$. Then $\rho(s)^* = \rho(s^{-1})$ (`New.adjoint_rep_of_unitary`).

### Sums over a group

The classical notion behind the identity is the function of positive type. A function $\varphi$ on a group $G$ is *of positive type* if $\sum_{a, b}\overline{c_a}c_b\,\varphi(a^{-1}b) \geq 0$ for every finitely supported family of complex numbers $c_a$. By the construction of Gelfand, Naimark and Segal, this holds if and only if $\varphi(a^{-1}b) = \langle u(a), u(b)\rangle$ for some vectors $u(a)$ of a Hilbert space (Folland, *A Course in Abstract Harmonic Analysis*, Section 3.3). The source uses the second form as its definition. It never needs the first.

**Lemma (Sums over a group).** Let $G$ be a finite group, let $H$ be a complex inner product space, and let $u, v : G \to H$ and $f : G \to \mathbb{C}$ satisfy $\langle u(a), v(b)\rangle = f(a^{-1}b)$ for all $a, b \in G$. Then

$$\Bigl\langle\sum_{a \in G}u(a), \sum_{b \in G}v(b)\Bigr\rangle = |G|\sum_{s \in G}f(s).$$

Lean: `New.inner_sum_sum_eq_card_mul` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* For fixed $a$, the map $b \mapsto a^{-1}b$ is a bijection of $G$, so $\sum_b f(a^{-1}b) = \sum_s f(s)$. Sum over $a$. $\square$

With $u = v$, the lemma says that the squared norm of $\sum_a u(a)$ is $|G|$ times the sum of the function $s \mapsto \langle u(1), u(s)\rangle$. This is the form in which a second moment becomes a squared norm.

**Lemma (Translates have positive type).** Let $\rho$ be unitary, let $B : S \to T$, and let $s, t \in \Gamma$. Then

$$\bigl\langle \rho(s)B(\rho(s)B)^*,\ \rho(t)B(\rho(t)B)^*\bigr\rangle_{\mathrm{HS}} = \|B^*\rho(s^{-1}t)B\|^2.$$

So $s \mapsto \|B^*\rho(s)B\|^2$ is of positive type, with $u(s)$ the Hilbert-Schmidt vector of $\rho(s)BB^*\rho(s)^*$.

Lean: `New.inner_hilbertSchmidtVector_translate` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Put $X = \rho(s)B$ and $Y = \rho(t)B$. By the trace form, the left side is $\operatorname{tr}(XX^*YY^*)$. By the cyclic property of the trace it is $\operatorname{tr}(Y^*XX^*Y) = \operatorname{tr}((X^*Y)^*(X^*Y)) = \|X^*Y\|^2$. Finally $X^*Y = B^*\rho(s)^*\rho(t)B = B^*\rho(s^{-1}t)B$, since $\rho$ is unitary. $\square$

[The chapter on moments](/chapter/moments/) uses this lemma to discharge the hypothesis of positive type in its second moment bound ([Theorem](/decl/New.Filling.sum_secondMoment_le/)). There the function is the second moment $\mathcal{M}(s) = \|P^*\rho(s)P\|^2$ of the amplitude blocks, and the lemma writes it as a Gram matrix. So the hypothesis of positive type is not an open assumption of the source.

### The Cauchy-Schwarz bound

**Lemma (Cauchy-Schwarz for translates).** Let $\rho$ be unitary, let $B : S \to T$, and let $W$ be a subspace of $T$. Then

$$\Bigl(\sum_{s \in \Gamma}\|\mathrm{pr}_W\rho(s)B\|^2\Bigr)^2 \leq \dim W\cdot|\Gamma|\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2.$$

Lean: `New.sq_sum_hilbertSchmidtNorm_orthoProj_comp_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $\Sigma = \sum_s \rho(s)B(\rho(s)B)^*$, an operator on $T$, and identify it with the sum of the Hilbert-Schmidt vectors. By the lemma on projections of [the section on Hilbert-Schmidt norms](/chapter/few-translates/#hilbert-schmidt-norms-and-near-isometries), applied to $A = \rho(s)B$ for each $s$,

$$\sum_s\|\mathrm{pr}_W\rho(s)B\|^2 = \operatorname{Re}\langle\mathrm{pr}_W, \Sigma\rangle_{\mathrm{HS}} \leq \|\mathrm{pr}_W\|\,\|\Sigma\|.$$

The left side is $\geq 0$, so we may square. Now $\|\mathrm{pr}_W\|^2 = \dim W$. By the lemma on translates, the vectors $u(s)$ of $\rho(s)BB^*\rho(s)^*$ satisfy $\langle u(s), u(t)\rangle = \|B^*\rho(s^{-1}t)B\|^2$, and the lemma on sums over a group gives $\|\Sigma\|^2 = |\Gamma|\sum_s\|B^*\rho(s)B\|^2$. $\square$

**Remark (The least second moment).** Take $W = T_0$, the range of a symmetric projection $\mathrm{pr}_0$ that commutes with $\rho$, and suppose that $\mathrm{pr}_0B$ is a near isometry with the error $\varepsilon \leq 1$. Then $\|\mathrm{pr}_0\rho(s)B\| = \|\rho(s)\mathrm{pr}_0B\| = \|\mathrm{pr}_0B\|$, and the definition with $U = S$ gives $\|\mathrm{pr}_0B\|^2 \geq (1 - \varepsilon)\dim S$. The lemma gives

$$\dim T_0\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \geq |\Gamma|\,(1 - \varepsilon)^2(\dim S)^2.$$

So the hypothesis of the spread theorem below, with the factor $1 + \varepsilon$ on the right, says that the second moment is within the factor $(1 + \varepsilon)/(1 - \varepsilon)^2$ of its least value. For isometries and $\varepsilon = 0$, this is the bound of Welch for the frame potential, and equality holds for tight frames (see the notes).

### Spread

**Definition (Spread).** Let $V$ and $W$ be complex vector spaces, let $\Theta$ be an index set, let $B_s : V \to W$ be linear for $s \in \Theta$, and let $\eta \in \mathbb{R}$. The maps $B_s$ *spread with the error* $\eta$ if for every subspace $F$ of $W$, with $\alpha = \dim F/\dim W$, there is $s \in \Theta$ with

$$\dim B_s^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \eta\Bigr)\dim V.$$

Lean: `New.IsSpread` (New/Spanning/SecondMoment/FewTranslates.lean).

**Remark (Formalization).** The share $\alpha$ is a quotient of two natural numbers in $\mathbb{R}$, so $\alpha = 0$ when $\dim W = 0$. Then $F = 0$, and the condition reads $\dim\ker B_s \leq (\frac{1}{2} + \eta)\dim V$. The dimensions are `finrank`, which is $0$ for an infinite-dimensional space. Every use in the source has finite-dimensional $V$ and $W$, so the convention has no effect there.

Why the value $(1 + \alpha)/2$? For one map in general position, $\dim B_s^{-1}(F)$ is $\max(0, \dim V - \dim W + \dim F)$, which is small when $\dim V$ is small against $\dim W$. Spread asks much less. It allows a preimage of half of $V$ even for $F = 0$, and it lets the preimage grow linearly with $\alpha$ up to all of $V$. This is the price of the Cauchy-Schwarz argument: it bounds the mean of $\|\mathrm{pr}_F\rho(s)B\|^2$ by a square root, $\sqrt{\alpha(1 + \varepsilon)}\dim S$, and the bound $\sqrt\alpha \leq (1 + \alpha)/2$ turns it into a linear function of $\alpha$. [The greedy cover](/chapter/few-translates/#the-greedy-cover) shows that this weak position is enough: what matters is that the bound stays a fixed share below $\dim V$ while $\alpha$ stays below $1$.

### The spread theorem

**Theorem (One translate).** Let $\Gamma$ be a finite group with a unitary representation $\rho$ on $T$. Let $\mathrm{pr}_0$ be a symmetric projection of $T$ that commutes with $\rho(s)$ for every $s \in \Gamma$, and let $T_0$ be its range. Let $B : S \to T$ be linear and $\varepsilon \geq 0$. Suppose that

1. $\mathrm{pr}_0B$ is a near isometry with the error $\varepsilon$, and
2. $\dim T_0\cdot\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \leq |\Gamma|\,(1 + \varepsilon)(\dim S)^2$.

Then the maps $\mathrm{pr}_0\rho(s)B : S \to T_0$, $s \in \Gamma$, spread with the error $\frac{3}{2}\varepsilon$.

Lean: `New.isSpread_of_second_moment` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $F$ be a subspace of $T_0$, with $\alpha = \dim F/\dim T_0$, and let $W \subseteq T$ be $F$ viewed in $T$. Then $\dim W = \alpha\dim T_0$. If $\dim T_0 = 0$ this holds with both sides $0$, since then $F = 0$. Write $m = \sum_s\|B^*\rho(s)B\|^2$ for the second moment.

*Step 1: a good translate.* By the Cauchy-Schwarz lemma and hypothesis 2,

$$\Bigl(\sum_s\|\mathrm{pr}_W\rho(s)B\|^2\Bigr)^2 \leq \alpha|\Gamma|\cdot\dim T_0\, m \leq \alpha(1 + \varepsilon)\,\bigl(|\Gamma|\dim S\bigr)^2.$$

Since $4\alpha(1 + \varepsilon) \leq (\alpha + 1 + \varepsilon)^2$, the right side is at most $\bigl(|\Gamma|\cdot\frac{\alpha + 1 + \varepsilon}{2}\dim S\bigr)^2$. Both bases are $\geq 0$, so

$$\sum_s\|\mathrm{pr}_W\rho(s)B\|^2 \leq |\Gamma|\cdot\frac{\alpha + 1 + \varepsilon}{2}\dim S.$$

A sum of $|\Gamma|$ terms has a term at most the mean. So there is $s \in \Gamma$ with $\|\mathrm{pr}_W\rho(s)B\|^2 \leq \frac{\alpha + 1 + \varepsilon}{2}\dim S$. Fix this $s$.

*Step 2: the preimage.* Let $U \subseteq S$ be the preimage of $F$ under $\mathrm{pr}_0\rho(s)B$. For $x \in U$ we claim

$$\rho(s)\,\mathrm{pr}_0Bx = \mathrm{pr}_W\,\rho(s)Bx.$$

Put $y = \rho(s)Bx$. The vector $\mathrm{pr}_0y$ lies in $W$, because $x \in U$. The difference $y - \mathrm{pr}_0y$ is orthogonal to $T_0$, because $\mathrm{pr}_0$ is a symmetric projection, and so it is orthogonal to $W \subseteq T_0$. So $\mathrm{pr}_0y$ is the orthogonal projection of $y$ onto $W$. Finally $\mathrm{pr}_0\rho(s) = \rho(s)\mathrm{pr}_0$.

*Step 3: the comparison.* For every $x \in S$, apply the claim to $\mathrm{pr}_Ux \in U$. Since $\rho(s)$ preserves norms,

$$\|\mathrm{pr}_0B\,\mathrm{pr}_Ux\| = \|\rho(s)\mathrm{pr}_0B\,\mathrm{pr}_Ux\| = \|\mathrm{pr}_W\rho(s)B\,\mathrm{pr}_Ux\|.$$

By the comparison lemma and the lemma on projections, $\|\mathrm{pr}_0B\,\mathrm{pr}_U\| \leq \|\mathrm{pr}_W\rho(s)B\,\mathrm{pr}_U\| \leq \|\mathrm{pr}_W\rho(s)B\|$.

*Step 4: the near isometry.* Hypothesis 1 with the subspace $U$ gives

$$\dim U - \varepsilon\dim S \leq \|\mathrm{pr}_0B\,\mathrm{pr}_U\|^2 \leq \frac{\alpha + 1 + \varepsilon}{2}\dim S.$$

So $\dim U \leq \bigl(\frac{1 + \alpha}{2} + \frac{3}{2}\varepsilon\bigr)\dim S$. $\square$

The error $\frac{3}{2}\varepsilon$ has two parts. The part $\frac{1}{2}\varepsilon$ comes from the second moment, through $\sqrt{\alpha(1 + \varepsilon)} \leq (\alpha + 1 + \varepsilon)/2$. The part $\varepsilon$ comes from the near isometry.

**Remark (Formalization).** In Lean the maps of the conclusion are $\mathrm{pr}_0\rho(s)B$ followed by the corestriction of $\mathrm{pr}_0$ to its range (`LinearMap.rangeRestrict`), so their target is the space $T_0$ itself and not $T$. This matters: the share $\alpha$ in the definition of spread is measured in the target, so the theorem measures $\alpha$ in $T_0$, whose dimension $d_T$ is the one in hypothesis 2. The hypothesis of near isometry is on $\mathrm{pr}_0B$, a map into $T$, and the hypothesis of the second moment is on $B$ itself, not on $\mathrm{pr}_0B$. The projection enters the second moment only through the factor $\dim T_0$. In the source this is an advantage: the moment computation of the chapter on moments is for the full Poincaré map $P$, and it never sees the idempotent $e_0$.

### The model case again

In the model case of [the opening section](/chapter/few-translates/#what-the-chapter-proves), take $\mathrm{pr}_0 = 1$, so $T_0 = T = \mathbb{C}^n$, and let $B$ be the inclusion of the first $d$ coordinates. Both hypotheses hold with $\varepsilon = 0$. So for every subspace $F$ of $\mathbb{C}^n$ of dimension $\alpha n$ some shift $\rho(s)B$ has $\dim(\rho(s)B)^{-1}(F) \leq \frac{1 + \alpha}{2}d$.

Check this for $F$ spanned by the first $d$ coordinates, with $n = 2d$, so $\alpha = \frac{1}{2}$. The shift by $s$ has the preimage of dimension $\max(0, d - |s|)$ for $|s| \leq d$, with $s$ taken in $(-d, d]$. The mean over the $2d$ shifts of $\|\mathrm{pr}_F\rho(s)B\|^2$ is $d^2/(2d) = d/2$, the Cauchy-Schwarz bound of Step 1 is $\sqrt{1/2}\,d \approx 0.71\,d$, and Step 1 then uses the larger bound $\frac{3}{4}d$. The shift $s = d$ has the preimage $0$. The bound of the theorem is $\frac{3}{4}d$.

### The constants in the source

[The theorem on the good Poincaré maps](/decl/New.Data.isSpread_goodPoincare/) applies the spread theorem with $\Gamma = \bar G$, $\mathrm{pr}_0 = e_0$, $B$ the scaled Poincaré map $P$, and $\varepsilon = (8b^2)^{-1}$. The two hypotheses come from the rest of the volume:

1. $e_0P$ is a near isometry with the error $5b^{-4}$, by [the theorem on good forms](/decl/New.Data.isNearIsometry_e₀_comp_scaledPoincare/). Since $5b^{-4} \leq (8b^2)^{-1}$ for $b^2 \geq 40$, the monotonicity lemma gives the error $\varepsilon$.
2. $d_T\sum_s\|P^*sP\|^2 \leq \#\bar G\,(1 + 9b^{-4})(\dim S)^2$, by [the second moment with the dimension](/decl/New.Data.targetDim_mul_sum_hilbertSchmidtNorm_sq_le/). Since $9b^{-4} \leq (8b^2)^{-1}$ for $b^2 \geq 72$, hypothesis 2 holds.

So the good Poincaré maps spread with the error $\frac{3}{2}(8b^2)^{-1}$. The two errors $5b^{-4}$ and $9b^{-4}$ are much smaller than the $\varepsilon$ that the cover needs. The size of $\varepsilon$ is set by the share $16\varepsilon = 2/b^2$ that Theorem B can afford to miss.
