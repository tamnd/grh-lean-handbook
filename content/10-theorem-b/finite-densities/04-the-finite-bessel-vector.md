---
title: The finite Bessel vector
lean:
  - New/Spanning/Frames/BesselVector.lean
decls:
  - New.Floors.IntegralPlace.extendedBesselChar
  - New.Floors.IntegralPlace.extendedBesselChar_eq
  - New.Floors.IntegralPlace.extendedBesselChar_besselU_mul
  - New.Floors.IntegralPlace.extendedBesselChar_mul_of_mem_unitaryLevel
  - New.Floors.IntegralPlace.continuous_extendedBesselChar
  - New.Floors.PlaceData.IntermediateGroup
  - New.Floors.PlaceData.IntermediateGroup.Cosets
  - New.Floors.PlaceData.unipotentMass
  - New.Floors.PlaceData.massIntegral
  - New.Floors.PlaceData.IntermediateGroup.massRatio
  - New.Floors.PlaceData.IntermediateGroup.besselVector
  - New.Floors.PlaceData.exists_mem_congruenceSubgroup_of_inner_ne_zero
  - New.Floors.PlaceData.IntermediateGroup.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq
  - New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_congruenceSubgroup_integral_sq
  - New.Floors.IntegralPlace.IsLargeLatticeData.isCut_besselVector
  - New.Floors.IntegralPlace.IsLargeLatticeData.unipotentMass_mul_inner_besselVector
  - New.Floors.IntegralPlace.IsLargeLatticeData.card_cosets_mul_groupMeasure
  - New.Floors.IntegralPlace.IsLargeLatticeData.enorm_sq_besselVector_mul_unipotentMass
  - New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_enorm_sq_besselVector
  - New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_inner_besselVector_sq_mul_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.pairingNormSq_mul_le_massRatio
  - New.Floors.IntegralPlace.IsLargeLatticeData.enorm_integral_extendedBesselChar_eq_enorm_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The finite Bessel vector

The densities of [local frames](/chapter/local-frames/#densities-as-integrals-over-two-frames) are defined for any cut Bessel function $W$. At a finite place the argument needs one specific $W$, built from a subgroup $Z$ with $K(g) \le Z \le K$. This section constructs it and computes its pointwise norm, its $L^2$ norm on $\mathsf{U}\backslash\mathsf{G}$, and the $L^2$ norm of its pairing. Each computation reduces, by the unfolding theorem of the last section, to a count of cosets of $K(g)$.

Throughout, $F$ is a place datum with modulus $g = $ `F.levelUnit`, $K(g) = $ `F.congruenceSubgroup`, $K = K(1)$, $\psi$ is the character of the place and $\sigma = $ `New.simpleRootSum` is the sum of the entries just above the diagonal of the frame block. From the second subsection on, $F$ is a large lattice datum.

### The model case of the Bessel vector

Let $\varrho = 1$ and $Z = K$. The Bessel character $u \mapsto \psi(\sigma(u)/g)$ of $\mathsf{U}$ is trivial on $\mathsf{U}\cap K(g)$, because $\sigma(u)/g$ is integral there and $R$ is self-dual. So the character extends to a function on $\mathsf{U}K(g)$ that is right invariant under $K(g)$, and it is extended by $0$ to $\mathsf{G}$. The function $\chi_g$ is not invariant under $K$, so one takes all its right translates by representatives $c$ of $K(g)\backslash K$. The vector $W(y) = (\chi_g(yc^{-1}))_c$ is then a Bessel function with values in $\mathbb{C}^{[K:K(g)]}$. Each point $y$ meets at most one coset in each coordinate, and the norm of $W(y)$ counts the cosets that $y$ meets.

### The extended character

**Definition (Extended Bessel character).** For a unit $g$ and $z \in \mathsf{G}$,

$$\chi_g(z) = \begin{cases}\psi\bigl(g^{-1}\sigma(u)\bigr) & \text{if } u^{-1}z \in K(g) \text{ for some } u \in \mathsf{U},\\ 0 & \text{otherwise.}\end{cases}$$

Lean: `New.Floors.IntegralPlace.extendedBesselChar` (New/Spanning/Frames/BesselVector.lean).

**Remark (Formalization).** In the first case the source uses the element `h.choose` given by the axiom of choice. The next lemma shows that the value does not depend on the choice, so the definition agrees with the textbook one.

**Lemma (Independence of the representative).** If $u \in \mathsf{U}$ and $u^{-1}y \in K(g)$, then $\chi_g(y) = \psi(g^{-1}\sigma(u))$.

Lean: `New.Floors.IntegralPlace.extendedBesselChar_eq` (New/Spanning/Frames/BesselVector.lean).

*Proof.* Let $v$ be the chosen element. Then $v^{-1}u = (v^{-1}y)(u^{-1}y)^{-1} \in K(g) \cap \mathsf{U}$. An element of $K(g)$ in $\mathsf{U}$ has $g^{-1}\sigma(v^{-1}u) \in R$. The integers are self-dual for $\psi$, so $\psi$ is $1$ on $R$. The map $\sigma$ is additive on the partial unitriangular group, so $\sigma(u) = \sigma(v) + \sigma(v^{-1}u)$, and $\psi(g^{-1}\sigma(u)) = \psi(g^{-1}\sigma(v))$. $\square$

**Lemma (Laws of the extended character).** For all $y \in \mathsf{G}$:

1. $|\chi_g(y)| \le 1$, and $\chi_g(y) = 0$ unless $y \in \mathsf{U}K(g)$.
2. $\chi_g(uy) = \psi(g^{-1}\sigma(u))\chi_g(y)$ for $u \in \mathsf{U}$.
3. $\chi_g(yk) = \chi_g(y)$ for $k \in K(g)$.
4. $\chi_g$ is continuous.

Lean: `New.Floors.IntegralPlace.extendedBesselChar_besselU_mul`, `New.Floors.IntegralPlace.extendedBesselChar_mul_of_mem_unitaryLevel`, `New.Floors.IntegralPlace.continuous_extendedBesselChar` (New/Spanning/Frames/BesselVector.lean).

*Proof.* (1) The values of $\psi$ have modulus $1$; the support statement is the definition. (2) If $v^{-1}y \in K(g)$ with $v \in \mathsf{U}$, then $(uv)^{-1}uy \in K(g)$, and $\sigma(uv) = \sigma(u) + \sigma(v)$; apply the lemma before. If no such $v$ exists for $y$, none exists for $uy$, and both sides are $0$. The source proves this for $u$ in the larger Bessel group $\mathsf{S}$, which normalises $\mathsf{U}$; for $u \in \mathsf{U}$ the extra factor is $1$. (3) The condition $u^{-1}yk \in K(g)$ is the condition $u^{-1}y \in K(g)$. (4) By (3), $\chi_g$ is constant on the cosets of the open subgroup $K(g)$, so it is locally constant. $\square$

### Intermediate groups and the vector

**Definition (Intermediate group, cosets, masses).** An intermediate group is a subgroup $Z$ of $\mathsf{G}$ with $K(g) \le Z \le K$ (`New.Floors.PlaceData.IntermediateGroup`, the interval `Set.Icc`). Its cosets are the classes of $Z$ under $a \sim b \iff ab^{-1} \in K(g)$, that is the right cosets $K(g)a$ (`New.Floors.PlaceData.IntermediateGroup.Cosets`). They are finite in number, because $K(g)$ is open and $K$ is compact. Write

$$\mathrm{fl} = \prod_{l<\varrho}\mathrm{fl}_l(g), \qquad \varkappa(Z) = \int_{\mathsf{G}}\Bigl|\int_Z\chi_g(yxy^{-1})\,d\mathsf{M}(y)\Bigr|^2 d\mathsf{M}(x), \qquad \mathrm{mr}(Z) = \frac{\mathsf{M}(Z)\,\mathsf{M}(K(g))}{\mathrm{fl}^2}.$$

Lean: `New.Floors.PlaceData.IntermediateGroup`, `New.Floors.PlaceData.IntermediateGroup.Cosets`, `New.Floors.PlaceData.unipotentMass`, `New.Floors.PlaceData.massIntegral`, `New.Floors.PlaceData.IntermediateGroup.massRatio` (New/Spanning/Frames/BesselVector.lean).

The number $\mathrm{fl}$ is positive and finite. The number $\varkappa(Z)$ is the mass integral: it is the quantity that the [main term](/chapter/main-term/) bounds from below. The mass integral is defined for any subgroup $Z$; the integrals are taken in $[0, \infty]$ and the inner Bochner integral is $0$ if it does not converge, but for an intermediate group $Z$ the integrand is bounded and $Z$ has finite mass, so no junk value occurs.

**Definition (Finite Bessel vector).** For an intermediate group $Z$ and $y \in \mathsf{G}$,

$$W_Z(y) = \bigl(\chi_g(y\,c^{-1})\bigr)_{c}\ \in\ \mathbb{C}^{\mathrm{Cosets}(Z)},$$

where $c$ runs over the cosets and the point $c$ in $\chi_g(yc^{-1})$ is a chosen representative of the coset, with the standard inner product.

Lean: `New.Floors.PlaceData.IntermediateGroup.besselVector` (New/Spanning/Frames/BesselVector.lean).

**Remark (Formalization).** The representative is `c.out`, chosen by `Quotient.out`. A different choice $kc$ with $k \in K(g)$ changes the coordinate to $\chi_g(yc^{-1}k^{-1}) = \chi_g(yc^{-1})$ by law (3), so $W_Z$ does not depend on the choice. The proofs below do not use this fact; they work with the fixed representatives.

**Lemma (Two facts on cosets).** Let $Z$ be an intermediate group.

1. If $\langle W_Z(x), W_Z(y)\rangle \ne 0$, then there are $u, v \in \mathsf{U}$ with $ux \in K$ and $(ux)^{-1}(vy) \in K(g)$.
2. For $y \in Z$ there is exactly one coset $d$ with $y\,c^{-1} \in K(g)$ if and only if $c = d$.

Lean: `New.Floors.PlaceData.exists_mem_congruenceSubgroup_of_inner_ne_zero`, `New.Floors.PlaceData.IntermediateGroup.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq` (New/Spanning/Frames/BesselVector.lean).

*Proof.* (1) Some coset $c$ gives a nonzero term, so $\chi_g(xc^{-1}) \ne 0$ and $\chi_g(yc^{-1}) \ne 0$. By law (1) there are $u, v \in \mathsf{U}$ with $u^{-1}xc^{-1} \in K(g)$ and $v^{-1}yc^{-1} \in K(g)$. The representative $c$ lies in $K$, so $u^{-1}x \in K(g)c \subseteq K$. The quotient $(u^{-1}x)^{-1}(v^{-1}y)$ is $c^{-1}k c$ for some $k \in K(g)$, and $K(g)$ is normal in $K$. Rename $u^{-1}, v^{-1}$ as $u, v$. (2) Take $d$ the coset of $y$; then $c = d$ if and only if $y\,c^{-1} \in K(g)$, by the definition of the relation. $\square$

### The vector is a cut Bessel function

From now on $F$ is a large lattice datum ([the lattice datum](/chapter/finite-densities/#the-lattice-datum)). Then the box is $K$, so the conditions of a cut function are conditions on $K$.

**Theorem (The finite Bessel vector is cut).** For a large lattice datum and an intermediate group $Z$, $W_Z$ is a cut Bessel function in the sense of [local frames](/chapter/local-frames/#densities-as-integrals-over-two-frames): it is strongly measurable with $\|W_Z(y)\| \le \sqrt{\#\mathrm{Cosets}(Z)}$; $W_Z(uy) = \psi(g^{-1}\sigma(u))W_Z(y)$ for $u \in \mathsf{U}$; and $W_Z(y) \ne 0$ implies $uy \in K$ for some $u \in \mathsf{U}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.isCut_besselVector` (New/Spanning/Frames/BesselVector.lean).

*Proof.* Each coordinate has modulus at most $1$, which gives the bound. Measurability follows from continuity. The law under $\mathsf{U}$ is law (2) in each coordinate. If $W_Z(y) \ne 0$, then $\langle W_Z(y), W_Z(y)\rangle \ne 0$ and fact (1) of the lemma before gives $u \in \mathsf{U}$ with $uy \in K$. $\square$

The inner product is the coordinatewise $\sum_c \overline{a_c}\,b_c$; the source uses Mathlib's convention, conjugate linear in the first slot.

### The pairing as an integral over the unipotent group

**Theorem (Pairing of two translates).** For $x, y \in \mathsf{G}$,

$$\mathrm{fl}\cdot\langle W_Z(y), W_Z(yx)\rangle = \int \mathbf{1}_Z(uy)\,\chi_g\bigl(uyx(uy)^{-1}\bigr)\,d\eta_{<\varrho+2}(u).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.unipotentMass_mul_inner_besselVector` (New/Spanning/Frames/BesselVector.lean).

*Proof.* The measure $\eta_{<\varrho+2}$ is carried by $\mathsf{U}$, so it is enough to compute the integrand for $u \in \mathsf{U}$. For a coset $c$ let $S_c = \{u : u\,y\,c^{-1} \in K(g)\}$ and $a_c = \overline{W_Z(y)_c}\,W_Z(yx)_c$. Claim: for $u \in \mathsf{U}$ the integrand equals $\sum_c a_c\mathbf{1}_{S_c}(u)$.

If $uy \notin Z$, then $u$ lies in no $S_c$, since $u y c^{-1} \in K(g) \le Z$ and $c \in Z$ would give $uy \in Z$; both sides are $0$. If $uy \in Z$, fact (2) gives exactly one coset $d$ with $u \in S_d$. For this $d$, the lemma on independence gives $W_Z(y)_d = \chi_g(yd^{-1}) = \psi(g^{-1}\sigma(u^{-1}))$, since $u\cdot yd^{-1} \in K(g)$. By laws (3) and (2),

$$\begin{aligned}W_Z(yx)_d &= \chi_g(yxd^{-1}) = \chi_g\bigl(yx(uy)^{-1}\cdot u y d^{-1}\bigr) = \chi_g\bigl(u^{-1}\cdot uyx(uy)^{-1}\bigr)\\ &= \psi\bigl(g^{-1}\sigma(u^{-1})\bigr)\chi_g\bigl(uyx(uy)^{-1}\bigr).\end{aligned}$$

The two characters cancel in $a_d$, because $|\psi| = 1$. This proves the claim.

Integrate the sum term by term. The unfolding theorem of [the last section](/chapter/finite-densities/#masses-at-the-standard-level), applied with $\theta$ the unit mass at $1$, gives

$$\eta_{<\varrho+2}(S_c) = \mathrm{fl}\cdot\mathbf{1}\bigl[\text{some } u \in \mathsf{U} \text{ has } u\,y\,c^{-1} \in K(g)\bigr],$$

which is finite. If $W_Z(y)_c = 0$, the term $a_c$ is $0$. Otherwise law (1) gives $u \in \mathsf{U}$ with $u^{-1}yc^{-1} \in K(g)$, so the indicator is $1$ and the term is $\mathrm{fl}\cdot a_c$. The sum of these terms is $\mathrm{fl}\cdot\langle W_Z(y), W_Z(yx)\rangle$. $\square$

### Norms

**Theorem (Coset count).** $\#\mathrm{Cosets}(Z)\cdot\mathsf{M}(K(g)) = \mathsf{M}(Z)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.card_cosets_mul_groupMeasure` (New/Spanning/Frames/BesselVector.lean).

*Proof.* The number of right cosets is the relative index $[Z : K(g)]$. The group $Z$ is compact, as a closed subgroup of $K$, and $K(g)$ is open. For a left invariant measure the mass of a compact group is the index times the mass of an open subgroup of finite index. $\square$

**Theorem (Pointwise norm).** For $y \in \mathsf{G}$,

$$\|W_Z(y)\|^2\cdot\mathrm{fl} = \eta_{<\varrho+2}\bigl(\{u : uy \in Z\}\bigr) \le 1.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_sq_besselVector_mul_unipotentMass`, `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_sq_besselVector_mul_le_one` (New/Spanning/Frames/BesselVector.lean).

*Proof.* Put $x = 1$ in the pairing theorem. Then $\chi_g(uy(uy)^{-1}) = \chi_g(1) = 1$, so the integrand is $\mathbf{1}_Z(uy)$. For the bound, $Z \le K$, and the unfolding theorem at level $1$ gives $\eta_{<\varrho+2}(\{u : uy \in K\}) \le \prod_l \mathrm{fl}_l(1)\cdot 1 = 1$, since the unit mass is a probability measure and $|1| = 1$. $\square$

**Theorem (L² norm of the vector).** $\mathrm{fl}\cdot\int\|W_Z\|^2\,d\mu_{\ge 0} = \mathsf{M}(Z)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_enorm_sq_besselVector` (New/Spanning/Frames/BesselVector.lean).

*Proof.* Recall that $\mathsf{M} = \eta_{<\varrho+2}\ast\mu_{\ge 0}$ ([local frames](/chapter/local-frames/#place-data-floors-and-gauges)). Integrate the pointwise norm against $\mu_{\ge 0}$:

$$\int\eta_{<\varrho+2}(\{u : uy \in Z\})\,d\mu_{\ge 0}(y) = (\eta_{<\varrho+2}\ast\mu_{\ge 0})(Z) = \mathsf{M}(Z). \qquad\square$$

By the coset count, the right side is $\#\mathrm{Cosets}(Z)\cdot\mathsf{M}(K(g))$: each coordinate contributes the mass of one coset.

**Theorem (Pairing in one variable).** For $x \in \mathsf{G}$,

$$\Bigl(\int|\langle W_Z(x), W_Z(y)\rangle|^2\,d\mu_{\ge 0}(y)\Bigr)\cdot\mathrm{fl}\cdot\mathrm{fl} \le \|W_Z(x)\|^2\cdot\mathsf{M}(K(g)).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_inner_besselVector_sq_mul_le` (New/Spanning/Frames/BesselVector.lean).

*Proof.* If $W_Z(x) = 0$ there is nothing to prove. Otherwise the cut property gives $u \in \mathsf{U}$ with $ux \in K$. Let $S = \{y : v\,y(ux)^{-1} \in K(g) \text{ for some } v \in \mathsf{U}\}$.

Step 1: the mass of $S$. The measure $\mathsf{M}$ is right invariant (`New.Floors.PlaceData.isMulRightInvariant_groupMeasure`, New/Spanning/Frames/Levels.lean), so $\mathsf{M}(K(g)) = \mathsf{M}(\{z : z(ux)^{-1} \in K(g)\})$. The unfolding theorem with $c = (ux)^{-1}$ gives $\mathsf{M}(K(g)) = \mathrm{fl}\cdot\mu_{\ge 0}(S)$.

Step 2: the pairing vanishes off $S$. If $\langle W_Z(x), W_Z(y)\rangle \ne 0$, fact (1) gives $v, w \in \mathsf{U}$ with $vx \in K$ and $(vx)^{-1}(wy) \in K(g)$. Conjugate by $ux \in K$, which normalises $K(g)$: $(ux)\bigl((vx)^{-1}wy\bigr)(ux)^{-1} = uv^{-1}w\cdot y\,(ux)^{-1} \in K(g)$. Since $uv^{-1}w \in \mathsf{U}$, this gives $y \in S$.

Step 3: on $S$, the Cauchy-Schwarz inequality and the pointwise norm give

$$|\langle W_Z(x), W_Z(y)\rangle|^2\,\mathrm{fl} \le \|W_Z(x)\|^2\,\|W_Z(y)\|^2\,\mathrm{fl} \le \|W_Z(x)\|^2.$$

Integrate over $y$ and multiply by $\mathrm{fl}$: the left side is at most $\|W_Z(x)\|^2\,\mu_{\ge 0}(S)\,\mathrm{fl} = \|W_Z(x)\|^2\,\mathsf{M}(K(g))$. $\square$

**Theorem (Pairing norm).** $\mathrm{pn}(W_Z)\cdot\mathrm{fl} \le \mathrm{mr}(Z)$, where $\mathrm{pn}(W) = \iint|\langle W(x), W(y)\rangle|^2\,d\mu_{\ge 0}(y)\,d\mu_{\ge 0}(x)$ is the pairing norm of [local frames](/chapter/local-frames/#densities-as-integrals-over-two-frames).

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.pairingNormSq_mul_le_massRatio` (New/Spanning/Frames/BesselVector.lean).

*Proof.* Integrate the theorem before over $x$: $\mathrm{pn}(W_Z)\,\mathrm{fl}^2 \le \mathsf{M}(K(g))\int\|W_Z\|^2\,d\mu_{\ge 0}$. Multiply by $\mathrm{fl}$ and use the $L^2$ norm: $\mathrm{pn}(W_Z)\,\mathrm{fl}^3 \le \mathsf{M}(Z)\,\mathsf{M}(K(g))$. The number $\mathsf{M}(K(g))$ is finite since $K(g) \le K$ is compact, and $\mathrm{fl}^2$ is positive and finite, so one may divide by $\mathrm{fl}^2$. $\square$

### The mass integral as a correlation

**Theorem (Inner integral as a correlation).** For $x \in \mathsf{G}$,

$$\Bigl|\int_Z\chi_g(yxy^{-1})\,d\mathsf{M}(y)\Bigr| = \Bigl|\int\langle W_Z(z), W_Z(zx)\rangle\,d\mu_{\ge 0}(z)\Bigr|\cdot\mathrm{fl}.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_integral_extendedBesselChar_eq_enorm_mul` (New/Spanning/Frames/BesselVector.lean).

In the source the integral on the right is `F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 x`, the correlation from floor $0$ of the kernel $(y, y') \mapsto \langle W_Z(y), W_Z(y')\rangle$ at $(1, x)$ ([local frames](/chapter/local-frames/#place-data-floors-and-gauges)).

*Proof.* Let $f = \mathbf{1}_Z\cdot(z \mapsto \chi_g(zxz^{-1}))$. It is bounded by $1$, continuous on the open set $Z$, and $Z$ has finite mass, so $f$ is integrable. Write $\mathsf{M} = \eta_{<\varrho+2}\ast\mu_{\ge 0}$, unfold the convolution and swap the integrals by Fubini:

$$\int_Z\chi_g(yxy^{-1})\,d\mathsf{M} = \int\!\!\int f(uy)\,d\eta_{<\varrho+2}(u)\,d\mu_{\ge 0}(y) = \int\mathrm{fl}\,\langle W_Z(y), W_Z(yx)\rangle\,d\mu_{\ge 0}(y),$$

by the pairing theorem. Take absolute values. $\square$

**Theorem (Mass integral on K(g)).** $\int_{K(g)}\bigl|\int_Z\chi_g(yxy^{-1})\,d\mathsf{M}(y)\bigr|^2 d\mathsf{M}(x) = \mathsf{M}(Z)^2\,\mathsf{M}(K(g))$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_congruenceSubgroup_integral_sq` (New/Spanning/Frames/BesselVector.lean).

*Proof.* For $x \in K(g)$ and $y \in Z \le K$, $yxy^{-1} \in K(g)$, so $\chi_g(yxy^{-1}) = \psi(g^{-1}\sigma(1)) = 1$ by the lemma on independence with $u = 1$. The inner integral is $\mathsf{M}(Z)$, which is finite, and the outer integral of the constant $\mathsf{M}(Z)^2$ over $K(g)$ is $\mathsf{M}(Z)^2\,\mathsf{M}(K(g))$. $\square$

This is the main term of the mass integral: the points $x$ near the identity contribute exactly $\mathsf{M}(Z)^2\mathsf{M}(K(g))$. The section [Shells, decay and mass](/chapter/finite-densities/#shells-decay-and-mass) shows that the points $x \notin K(g)$ contribute little.

**Example.** Let $Z = K(g)$. There is one coset, $W_Z(y) = \chi_g(y)$ up to the representative, $\mathsf{M}(Z) = \mathsf{M}(K(g))$ and $\mathrm{mr}(Z) = \mathsf{M}(K(g))^2/\mathrm{fl}^2$. The pointwise norm says that $\mathrm{fl}\cdot|\chi_g(y)|^2$ is the $\eta_{<\varrho+2}$ mass of the $u$ with $uy \in K(g)$: either $0$ or $\mathrm{fl}$, in agreement with $|\chi_g(y)| \in \{0, 1\}$.
