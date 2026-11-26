---
title: One step of unfolding
lean:
  - Lib/Weil/Periods/Unfolding.lean
  - Lib/Weil/Periods/ConstantTerm.lean
decls:
  - New.Grading.unfoldStep
  - New.Grading.integral_tsum_classTerm_eq_zero
  - New.Grading.exists_equiv_agreeingTranslates
  - New.Grading.hasSum_unfoldStep
  - New.Grading.integral_besselGroup_unfold
  - New.Grading.isEquivariant_unfoldStep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One step of unfolding

This section proves the main theorem of the chapter. Let $Y$ grade $V$ with a string of length $s$, and let $Y'$ grade $V'$ with a string of length $s - 1$. Let $W$ be an equivariant function on the Bessel group $R$ of $Y$, and let $y$ be a rapidly decreasing automorphic function on $G' = U(V')(\mathbb{A})$. The theorem writes the period of $W$ against the theta lift of $y$ as the period of $y$ against a new function $W'$ over the Bessel group $R'$ of $Y'$. The section then proves that the translates of $W'$ are again equivariant, so that the step can be repeated. The seesaw of [seesaw identity, part 1](/chapter/seesaw-identity-1/) repeats it.

### The unfolded function

Fix $\Phi \in \mathcal{S}(\operatorname{Hom}(V, V'))$. Write $\omega(g, h)$ for the Weil action of $G \times G'$ on $\mathcal{S}(\operatorname{Hom}(V, V'))$, twisted by the characters $\alpha$ of the Weil data. The theta kernel is $\theta(g, h) = \theta\big(\omega(g, h)\Phi\big)$. For $g \in G$ and $h \in G'$, put

$$\mathrm{CT}(g, h) = \mathrm{CT}_{\operatorname{grade}'}\big(\omega(g, h)\Phi\big)(T),$$

the constant term at $T$ for the weights of $Y'$ (Lean: `New.Grading.constTermAtStringMap`).

**Definition (The unfolded function).** For a function $W$ on $R$, the unfolded function is

$$W'(h) = \int_{[R]} W(r)\, \mathrm{CT}(r, h)\, d\mu_R(r), \qquad h \in G'.$$

Lean: `New.Grading.unfoldStep` (Lib/Weil/Periods/ConstantTerm.lean).

For equivariant $W$ the integrand is continuous and invariant under $R(E)$, so the integral is a true integral over the compact quotient $[R]$. The function $W'$ is continuous, and it is left invariant under $R'(E)$ (Lean: `New.Grading.continuous_unfoldStep`, `New.Grading.unfoldStep_rat_mul`). Invariance follows from the substitution law of [Proposition](/decl/New.Grading.constTerm_mul/) and [Lemma](/decl/New.Grading.hasDegreeGe_zero_mul_stringMap_mul_sub/): for $\gamma \in R'(E)$ the map $\gamma^{-1} T$ is in the class of $T$.

### The terms of the theta kernel

Take the weights $d = 0$ on $V'$. They are odd under the string reversal. Then a map has positive degree at the entry $(b, a)$ exactly when $\operatorname{grade}(a) < 0$. For a class $x$ of rational maps modulo $\Lambda_0$, with chosen representative $w_x$, the term of $x$ is

$$k_x(h, r) = W(r)\, \mathrm{CT}_0\big(\omega(r, h)\Phi\big)(w_x).$$

Lean: `New.Grading.classTerm` (Lib/Weil/Periods/Unfolding.lean).

By [Theorem](/decl/New.Grading.hasSum_constTerm/) the terms add up to $W(r)\theta(r, h)$ (Lean: `New.Grading.tsum_classTerm`). Their norms have a sum that is bounded by a constant times $\|\omega(r, h)\Phi\|$. The pairs $(\gamma, \delta)$ of rational points, with $\gamma \in R(E)$ and $\delta$ rational and not lowering the weights $d$, act on the classes by $x \mapsto \delta w_x \gamma^{-1}$. By the substitution law, $k_{(\gamma, \delta) x}(\delta h, \gamma r) = k_x(h, r)$ (Lean: `New.Grading.classTerm_smul`).

**Lemma (Integrability of the terms).** Let $W$ be equivariant. For every $h \in G'$ and every set $S$ of classes,

$$\int_{[R]} \sum_{x \in S} |k_x(h, r)|\, d\mu_R(r) < \infty .$$

So the sum over $S$ may be integrated term by term.

Lean: `New.Grading.lintegral_tsum_enorm_classTerm_lt_top` and `New.Grading.hasSum_integral_classTerm` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* The function $r \mapsto \sum_x |k_x(h, r)|$ is bounded on $R$ by $\sup |W| \cdot M \cdot \|\omega(r, h)\Phi\|$, where $M$ is the constant of the Fourier expansion. On a compact fundamental set of $R(E) \backslash R$ both factors are bounded, and the sum is invariant under $R(E)$. The measure $\mu_R$ is finite. $\square$

### The classes that do not survive

**Theorem (Vanishing of the classes that do not survive).** Let $W$ be equivariant, and let $d$ be odd under the string reversal of $Y'$. Let $S$ be a set of classes modulo $\Lambda_d$ that is stable under $R(E)$ and such that no chosen representative $w_x$, $x \in S$, survives the unipotent twists for $d$. Then for every $h \in G'$,

$$\int_{[R]} \sum_{x \in S} k_x(h, r)\, d\mu_R(r) = 0.$$

Lean: `New.Grading.integral_tsum_classTerm_eq_zero`, with `New.Grading.exists_classTerm_mul_eq_of_not_survives` and `New.Grading.tsum_integral_eq_of_not_survives` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* Integrate term by term, by the lemma, and group the terms into orbits of $R(E)$. The sum over one orbit unfolds to an integral over the quotient of $R$ by the stabiliser $R(E)_x$ of a class $x$:

$$\sum_{x' \in R(E) x} \int_{[R]} k_{x'}(h, r)\, d\mu_R = \int_{R(E)_x \backslash R} k_x(h, r)\, dr.$$

Since $w_x$ does not survive, there is $u \in U$ with $u - 1$ of degree $\geq 2$ and $w_x(u - 1)$ of degree $\geq 1$, such that $\beta(T u, T) \neq \beta(w_x u, w_x)$. By the equivariance of $W$, the substitution law and [Proposition](/decl/New.Grading.constTerm_eq_homBicharacter_mul/), left translation by $u$ multiplies $k_x(h, \cdot)$ by a constant $c$ with $|c| = 1$ and $c \neq 1$. A continuous function on $R$ that is left invariant under a discrete subgroup $\Gamma$, and that is multiplied by a constant $c \neq 1$ of modulus $1$ under left translation by one element $u$, has integral $0$ over $\Gamma \backslash R$ (Lean: `New.integral_quotMeasure_eq_zero_of_twist`). Apply it with $\Gamma = R(E)_x$. $\square$

### The classes that survive

Let $\mathcal{C}$ be the set of classes modulo $\Lambda_0$ whose chosen representative agrees with $T$ (Lean: `New.Grading.agreeingClasses`). Let $\mathcal{D}$ be the set of classes that some rational $\delta \in G'(E)$ moves into $\mathcal{C}$ (Lean: `New.Grading.agreeingTranslates`). If a class is not in $\mathcal{D}$, its representative does not survive for $d = 0$, by [Theorem](/decl/New.Grading.exists_agreesWithStringMap/). The complement of $\mathcal{D}$ is stable under $R(E)$, by [Proposition](/decl/New.Grading.agreesWithStringMap_mul_iff/). By the vanishing theorem, only the classes in $\mathcal{D}$ contribute to the period (Lean: `New.Grading.tsum_agreeingTranslates`).

**Proposition (The translates of $\mathcal{C}$).** Let $W$ be equivariant. There is a bijection

$$e \colon \big(G'(E) / R'(E)\big) \times \mathcal{C} \to \mathcal{D}$$

such that $k_{e(q, x)}(h, r) = k_x(\gamma_q^{-1} h, r)$ for all $q$, $x$, $h$ and $r$, where $\gamma_q$ is the chosen representative of the coset $q$.

Lean: `New.Grading.exists_equiv_agreeingTranslates`, with `New.exists_equiv_quotient_prod_block` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* For $d = 0$ every rational $\delta \in G'(E)$ acts on the classes, since no weight is lowered. A rational $\delta$ keeps a class of $\mathcal{C}$ in $\mathcal{C}$ if and only if $\delta \in R'(E)$, by [Proposition](/decl/New.Grading.agreesWithStringMap_mul_iff/). So the translates of $\mathcal{C}$ are blocks, and $(q, x) \mapsto \gamma_q x$ is a bijection onto $\mathcal{D}$. The formula for the terms is the substitution law. $\square$

**Lemma (One translate gives one value).** Let $W$ be equivariant. Then for every $h$,

$$\sum_{x \in \mathcal{C}} \int_{[R]} k_x(h, r)\, d\mu_R(r) = W'(h).$$

Lean: `New.Grading.tsum_integral_classTerm_agreeingClasses` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* Integrate term by term. The sum over $\mathcal{C}$ of the constant terms for $d = 0$ is a Fourier coefficient that does not depend on the weights, as long as $d \leq \max(\operatorname{grade}', 0)$ (Lean: `New.Grading.tsum_constTerm_agreesWithStringMap`). So the sum may be computed again for the weights $d = \operatorname{grade}'$ of $Y'$, over the classes modulo $\Lambda_{\operatorname{grade}'}$ that agree with $T$. Among these, a class that survives is the class of $T$, by [Theorem](/decl/New.Grading.hasDegreeGe_of_survives/). The group $R(E)$ fixes the class of $T$, by [Lemma](/decl/New.Grading.hasDegreeGe_zero_mul_stringMap_mul_sub/), and it keeps the set of agreeing classes. So the set of the other agreeing classes is stable under $R(E)$, and its integral vanishes by the vanishing theorem. The term of the class of $T$ integrates to $W'(h)$. $\square$

**Theorem (The period as a sum of unfolded values).** Let $W$ be equivariant. For every $h \in G'$,

$$\int_{[R]} W(r)\, \theta(r, h)\, d\mu_R(r) = \sum_{q \in G'(E) / R'(E)} W'(\gamma_q^{-1} h),$$

where the sum converges, and $\gamma_q$ is the chosen representative of $q$.

Lean: `New.Grading.hasSum_unfoldStep` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* The left side is the sum of the integrals of the terms over $\mathcal{D}$. Transport the sum along the bijection $e$ and sum first over $x \in \mathcal{C}$. For fixed $q$ the inner sum is $W'(\gamma_q^{-1} h)$, by the last lemma applied at $\gamma_q^{-1}h$. $\square$

Since $q \mapsto \gamma_q^{-1}$ is a bijection onto $R'(E) \backslash G'(E)$, the right side is the sum $\sum_{\gamma \in R'(E) \backslash G'(E)} W'(\gamma h)$.

### The main theorem

Recall that a function $y$ on $G'$ is automorphic if it is continuous, left invariant under $G'(E)$, and right invariant under an open subgroup of the finite points (Lean: `New.Space.IsAutomorphic`). It is rapidly decreasing if, for every $B \in \mathbb{N}$, there is $C$ with $|y(h)|\, \mathrm{ht}(h)^B \leq C$ for all $h$ (Lean: `New.Space.IsRapid`). Here $\mathrm{ht}(h)$ is the height of [reduction theory](/chapter/reduction-theory/): the inverse of the first minimum of the lattice moved by $h$, cut off at $1$. Write $[G'] = G'(E) \backslash G'$ with its invariant measure, and $R'(E) \backslash G'$ with the invariant measure of the same Haar measure.

**Theorem (One step of unfolding).** Let $W$ be equivariant, and let $y$ be automorphic and rapidly decreasing on $G'$. Then:

1. the function $h \mapsto W'(h) y(h)$ is integrable on $R'(E) \backslash G'$;
2. the period of $W$ against the theta lift of $y$ unfolds:

$$\int_{[R]} W(r) \int_{[G']} \theta(r, h)\, y(h)\, dh\, d\mu_R(r) = \int_{R'(E) \backslash G'} W'(h)\, y(h)\, dh .$$

Lean: `New.Grading.integral_besselGroup_unfold` (Lib/Weil/Periods/Unfolding.lean).

*Proof.* There are four steps.

*Step 1: a uniform bound.* For each $h$ there is a rational $\delta \in G'(E)$ with $\|\omega(1, \delta h)\| \leq 2^B \mathrm{ht}(h)^B$, for a fixed $B$. This is the growth bound of the theta kernel after reduction (Lean: `New.ThetaKernel.eventually_exists_norm_omega_le_mul_height_pow`). The decay of $y$ absorbs this growth. So there is a constant $c$ such that $\sum_{x \in S} |k_x(h, r)\, y(h)| \leq c$ for all $h$, $r$ and every set $S$ of classes (Lean: `New.Grading.exists_tsum_enorm_classTerm_mul_le`).

*Step 2: exchange of the integrals.* By Step 1, the function $(h, r) \mapsto W(r)\theta(r, h)y(h)$ is bounded on $[G'] \times [R]$, and both measures are finite. Fubini's theorem gives

$$\int_{[R]} W(r) \int_{[G']} \theta(r, h)\, y(h)\, dh\, d\mu_R(r) = \int_{[G']} \Big(\int_{[R]} W(r)\theta(r, h)\, d\mu_R(r)\Big) y(h)\, dh.$$

*Step 3: the sum over cosets.* By the previous theorem the inner integral is $\sum_q W'(\gamma_q^{-1} h)$. The terms $W'(\gamma_q^{-1} h)y(h)$ are permuted by left translation by $G'(E)$, because $y$ is automorphic and $W'$ is invariant under $R'(E)$.

*Step 4: unfolding.* By Step 1 and the last bound of the lemma on the translates, $\sum_q |W'(\gamma_q^{-1} h)\, y(h)| \leq c\, \mu_R([R])$ for every $h$ (Lean: `New.Grading.exists_tsum_enorm_unfoldStep_mul_le`). So the integral over $[G']$ of the sum of the absolute values is finite, since $[G']$ has finite volume. The unfolding of a sum over $G'(E)/R'(E)$ then applies (Lean: `New.integral_tsum_orbit_of_lt_top_or_integrable`). It gives the integrability (1), and it turns the integral over $[G']$ of the sum into the integral over $R'(E) \backslash G'$ of the term at the trivial coset, which is $W'(h)y(h)$. $\square$

**Remark (Formalization).** The integrability in (1) is a conclusion of the theorem, not a hypothesis. This matters, because the integral of a function that is not integrable is $0$ in Lean. The identity in (2) is an identity of true integrals. The source proves that the integrand of the iterated integral is integrable for the product measure. The theorem has no hypothesis on the constants $c$ of the two gradings. The iteration is in [seesaw identity, part 1](/chapter/seesaw-identity-1/), which starts from a source function and applies the step once at each string length.

### The unfolded function is equivariant

**Theorem (Equivariance of the unfolded function).** Let $W$ be equivariant, and suppose that the gradings $Y$ and $Y'$ have the same constant $c$. Then, for every $h \in G'$, the function $\gamma \mapsto W'(\gamma h)$ on $R'$ is equivariant for $Y'$.

Lean: `New.Grading.isEquivariant_unfoldStep` (Lib/Weil/Periods/ConstantTerm.lean).

*Proof.* Continuity and invariance under $R'(E)$ are the properties of $W'$ above. Let $u \in R'$ with $u - 1$ of degree $\geq 2$ for the grades of $Y'$. Since $T$ lowers grades by at most $1$, the map $uT - T$ has degree $\geq 1$. By the substitution law with $\delta = u$, and the change of the point,

$$\mathrm{CT}(g, u h) = \beta(T, u^{-1}T)^{\pm 1}\, \mathrm{CT}(g, h),$$

a phase that does not depend on $g$ and $h$. The source computes it as $\psi\big(\tfrac{\jmath}{2}\operatorname{tr}(T T^\dagger u)\big)$. For equal constants, $T T^\dagger = \mathfrak{e}'$ by [Proposition](/decl/New.Grading.formAdjoint_stringMap_mul_stringMap/). So the phase is $\psi_{U'}(u)$, the generic character of $Y'$. Integrate against $W(r)$: the phase comes out of the integral, and $W'(u \gamma h) = \psi_{U'}(u) W'(\gamma h)$. $\square$

**Remark (Formalization).** The hypothesis that the constants are equal is used only in the identity $T T^\dagger = \mathfrak{e}'$. This theorem does not say that $W'$ is a source function of an automorphic form on $U(X')$, even when $s - 1$ is odd. The iteration in [seesaw identity, part 1](/chapter/seesaw-identity-1/) proves such an identification separately, after an even number of steps, from [Proposition](/decl/New.Grading.IsEquivariant.eq_sourceFn/) and [Theorem](/decl/New.Grading.integral_besselMeasure_eq_of_mean/).
