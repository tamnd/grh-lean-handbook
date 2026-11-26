---
title: False lifts and lift generators
lean:
  - New/Congruences/FirstOrder/DenominatorBound.lean
decls:
  - New.Selmer.exists_heckePolyOnForms_eq_zero
  - New.Selmer.typeProjection_sub_starProjection_mem
  - New.Selmer.IsLiftGenerator
  - New.Selmer.IsLiftGenerator.mono
  - New.Selmer.span_mem_invtSubmodule_heckePolyOnForms
  - New.Selmer.IsLiftGenerator.typeProjection_eq_zero_or_mem_range
  - New.Selmer.IsLiftGenerator.exists_isMainSummandLike
  - New.Selmer.span_isLiftGenerator_mem_invtSubmodule_heckePolyOnForms
  - New.Selmer.span_isLiftGenerator_mem_invtSubmodule_typeProjection
  - New.Selmer.span_isLiftGenerator_mem_invtSubmodule
  - New.Selmer.typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts
  - New.Selmer.mem_integralForms_ofIso_iff
  - New.Selmer.IsLiftGenerator.exists_isMainSummandLike_hasTwistedLattice
status: drafted
drafted_by: writer@claude-opus-5-5
---
## False lifts and lift generators

The last section needs two inputs on forms. First, the form $y$ must agree with its projection to $Z$ at every system that is a weak lift. Second, every system that meets $Z$ must lift a main summand with a twisted lattice. This section proves both. The forms are those of the descent pair $O$, with the Hecke polynomial operators $\mathrm{heckePolyOnForms}_w(\xi)$ at split places $w$ off the places of $O$ and their conjugates, and the lift Hecke root $\xi_w = (\chi_W(\mathrm{Frob}_w)\, q_w^{t'-1})^{-1}$ (`New.DescentPair.liftHeckeRoot`). The projection $\mathrm{typeProjection}(c)$ is the action of the idempotent of the types $c$ ([lift settings](/chapter/main-summands/#lift-settings-and-representations-of-a-type)). A form $y$ is *orthogonal to the false lifts* for $E$ and $Z^\perp$ if, at every such $w$, it is orthogonal to the forms in $Z^\perp$ and in the image of $E$ that $\mathrm{heckePolyOnForms}_w(\xi_w)$ kills ([tested forms](/chapter/character-lifts/#point-forms-and-tested-forms)).

### False lifts

**Lemma (One Hecke polynomial kills the weak lifts).** For base data $B$ there is a split place $w$ off the places of $O$ and their conjugates such that $\mathrm{heckePolyOnForms}_w(\xi_w)\, v = 0$ for every form $v$ whose algebraic form is nonzero, of base level and in a system $x$ that is a weak lift.

Lean: `New.Selmer.exists_heckePolyOnForms_eq_zero` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Most places are off the base level, and split places off the places of $O$ occur frequently, so some $w$ has both properties. The form $v$ is then an eigenform at $w$ with the Hecke polynomial of $x$. Since $x$ is a weak lift, the numbers $\chi_W(\mathrm{Frob}_w)\, q_w^i$, $i < t'$, are roots of this polynomial ([root chains](/decl/New.Selmer.isRoot_hecke_chain/)). The last of them is $\xi_w^{-1} \neq 0$. The operator acts on $v$ by the reversed polynomial at $\xi_w$, which is $0$. $\square$

**Lemma (Projection off $Z$).** Let $Z$ be stable under every $\mathrm{heckePolyOnForms}_u(\xi)$ and under $\mathrm{typeProjection}(c)$, let the range of $\mathrm{typeProjection}(c)$ lie in the image of $E$, and let $y$ be orthogonal to the false lifts for $E$ and $Z^\perp$. Let $M$ be a subspace, and let one operator $T = \mathrm{heckePolyOnForms}_w(\xi_w)$ kill every form in the range of $\mathrm{typeProjection}(c)$ that is nonzero in a system and not in $M$. Then $\mathrm{typeProjection}(c)(y - P_Z y) \in M$, with $P_Z$ the orthogonal projection to $Z$.

Lean: `New.Selmer.typeProjection_sub_starProjection_mem` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $U$ be the range of $\mathrm{typeProjection}(c)$ intersected with $Z^\perp$, and $K = U \cap \ker T$. The range is stable under the Hecke operators, and so is $Z^\perp$, since the adjoint of the operator at $u$ is the operator at $\bar u$. So $U$ is stable. The operators at $u$ and $w$ commute, so $K$ is stable, and so is $U \cap K^\perp$.

A stable subspace lies in $M$ if its nonzero isotypic forms do ([isotypic forms](/decl/New.Selmer.le_of_isotypic_mem/)). Let $v \in U \cap K^\perp$ be nonzero in a system. If $v \notin M$, then $Tv = 0$ by hypothesis, so $v \in K$, and $\langle v, v \rangle = 0$, which is false. So $U \cap K^\perp \leq M$.

The form $u_0 = \mathrm{typeProjection}(c)(y - P_Z y)$ lies in $U$, since the projection is symmetric and keeps $Z$. Let $u \in K$. Then $u$ is a false lift at $w$: it lies in the image of $E$, in $\ker T$ and in $Z^\perp$. So $y$ is orthogonal to $u$, and so is $P_Z y \in Z$. Since $\mathrm{typeProjection}(c)$ is symmetric and fixes $u$, $\langle u, u_0 \rangle = \langle u, y - P_Z y \rangle = 0$. So $u_0 \in U \cap K^\perp \leq M$. $\square$

**Theorem (Agreement off the weak lifts).** Let $\vartheta$ be an auxiliary twist, $c$ a lift setting for $O$ and $\vartheta$, and $Z$, $E$, $y$ as in the previous lemma. If every form in the range of $\mathrm{typeProjection}(c)$ that is nonzero in a system $x$ and not in $M$ has $x$ a weak lift, then $\mathrm{typeProjection}(c)(y - P_Z y) \in M$.

Lean: `New.Selmer.typeProjection_sub_starProjection_mem_of_isOrthogonalToFalseLifts` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* [The base level](/decl/New.Selmer.exists_baseLevel/) gives base data $B$ such that the forms of type $c$ have base level. The first lemma gives $w$, and its operator kills the forms in the hypothesis. Apply the previous lemma. $\square$

### Lift generators

**Definition (Lift generator).** A form $y$ is a *lift generator* of $Z$ for $\vartheta$, $E$ and the bound $\mathrm{sel}$ if:

- $y \in Z$;
- $y$ lies in the range of $\mathrm{typeProjection}(c)$ for some lift setting $c$ for $O$ and $\vartheta$ whose range lies in the image of $E$;
- $y$ has the Hecke polynomials of the lift of some eigenvalues $z$ (`New.DescentPair.HasLiftHeckePolynomial`), and there are a main summand $R$ for $z$ and a pair $V$ with $\mu_O = \mu_V \cdot \vartheta$ (on the $U(1)$ characters), and $\gamma$, $s$ such that the divisible Selmer length of $\vartheta^{-1}_\ell R$ is at most $\mathrm{sel}$.

Lean: `New.Selmer.IsLiftGenerator` (New/Congruences/FirstOrder/DenominatorBound.lean).

**Lemma.** A lift generator for $\mathrm{sel}$ is one for every $\mathrm{sel}' \geq \mathrm{sel}$.

Lean: `New.Selmer.IsLiftGenerator.mono` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* The Selmer length bound is monotone (`New.Selmer.HasDivisibleSelmerLengthLe.mono`). $\square$

**Lemma (Spans of lifts).** The span of a set of forms with lift Hecke polynomials is stable under every $\mathrm{heckePolyOnForms}_w(\xi)$. So the span of the lift generators is stable under these operators, and under every $\mathrm{typeProjection}(c)$, and both hold together.

Lean: `New.Selmer.span_mem_invtSubmodule_heckePolyOnForms`, `New.Selmer.span_isLiftGenerator_mem_invtSubmodule_heckePolyOnForms`, `New.Selmer.span_isLiftGenerator_mem_invtSubmodule_typeProjection`, `New.Selmer.span_isLiftGenerator_mem_invtSubmodule` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* A form with a lift Hecke polynomial is an eigenvector of each operator, which gives the first claim. For the projection, the next lemma shows that $\mathrm{typeProjection}(c)$ sends a lift generator $v$ to $0$ or to $v$. $\square$

**Lemma.** Let $v$ be a lift generator. For every $c$, either $\mathrm{typeProjection}(c)\, v = 0$, or $v$ lies in its range and is nonzero in some system $x$.

Lean: `New.Selmer.IsLiftGenerator.typeProjection_eq_zero_or_mem_range` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $v$ be in the range of $\mathrm{typeProjection}(c')$. If $c \neq c'$, the idempotents are orthogonal, so $\mathrm{typeProjection}(c)\, v = 0$. So if $\mathrm{typeProjection}(c)\, v \neq 0$, then $c = c'$ and $v$ is in the range. If $v$ were nonzero in no system, the line $\mathbb{C} v$, which is Hecke stable, would have no nonzero isotypic form outside $\ker \mathrm{typeProjection}(c)$. Then the line lies in the kernel by the criterion for isotypic forms, which contradicts $\mathrm{typeProjection}(c)\, v \neq 0$. $\square$

**Lemma (A lift generator lifts a main summand).** Let $v$ be a lift generator for $\mathrm{sel}$ that is nonzero in $x$. Then there are $\mathrm{wt}$ and $R$ such that $R$ is a main summand with $t'$ characters, $\operatorname{tr} N_x = \vartheta^{-1}_\ell \operatorname{tr} R + \sum_{e<t'} \chi^e$, and for some $\gamma$ and $y$ the divisible Selmer length of the twisted row is at most $\mathrm{sel}$.

Lean: `New.Selmer.IsLiftGenerator.exists_isMainSummandLike` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* The system $x$ contains a Hecke eigenform $v$ with an attached Galois representation $x.\mathrm{galRep}$ ([attached representations](/chapter/attached-representations/)). The main summand property of $R$ for $V$ turns the lift Hecke polynomial of $v$ into the trace identity, using $\mu_O = \mu_V \vartheta$. The rank differences of $V$ and $O$ are both $\#n - \#r$. $\square$

**Lemma (Lifts with twisted lattices).** Let $v_0$ be a lift generator for $\mathrm{sel}$, nonzero in $x_0$, and $v$ a lift generator for $\infty$, nonzero in $x$. Then $x$ lifts with a twisted lattice for $x_0$ and $\mathrm{sel}$.

Lean: `New.Selmer.IsLiftGenerator.exists_isMainSummandLike_hasTwistedLattice` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* If $x = x_0$, apply the previous lemma to $v_0$; a Selmer length bound gives a twisted lattice (`New.Selmer.HasDivisibleSelmerLengthLe.hasTwistedLattice`). If $x \neq x_0$, apply it to $v$ and keep the lattice; the condition for $x = x_0$ is void. $\square$

**Lemma (Integral forms).** A form $y$ is integral at the $\ell$-adic place of $\iota_\ell$ if and only if its algebraic form has $\ell$-integral values at the points integral above $\ell$.

Lean: `New.Selmer.mem_integralForms_ofIso_iff` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Both say that the Weyl gauge of each value is at most $1$ ([the $p$-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). $\square$
