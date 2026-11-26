---
title: The inner product formula
lean:
  - Lib/SiegelWeil/RallisInner/Doubling.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
  - Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean
decls:
  - New.SiegelWeil.measurePreserving_quotMeasure_unfold
  - New.SiegelWeil.inner_product_formula
  - New.SiegelWeil.vacuumCoeff
  - New.SiegelWeil.norm_vacuumCoeff
  - New.SiegelWeil.weilMatrixCoeff_mul
  - New.SiegelWeil.IsSharp
  - New.SiegelWeil.IsSharp.isOpen_level
  - New.SiegelWeil.IsSharp.mass_ne_zero
  - New.SiegelWeil.IsSharp.weilMatrixCoeff_integrated_mul
  - New.SiegelWeil.IsSharp.isUnramifiedOn
  - New.SiegelWeil.cosetRep
  - New.SiegelWeil.rallisSeries
  - New.SiegelWeil.IsSharp.hasSum_integral_weilMatrixCoeff_mul
  - New.SiegelWeil.IsSharp.petersson_lift_eq_integral
  - New.SiegelWeil.IsSharpFn
  - New.SiegelWeil.IsSharpFn.isSharp
  - New.SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The inner product formula

This section integrates the doubling identity of [Section 2](/chapter/rallis-inner-product/#doubling) against two functions on $[U(S)]$. The result is the inner product formula as an adelic integral. The section then defines sharp data and splits the adelic integral into a real integral, a constant at the level and a series over the unramified places.

### The textbook form

Let $\pi$ be a cuspidal automorphic representation of $U(S)$, and let $\Theta_\phi(y)$ be the theta lift of a form $y$ in $\pi$ by a datum $\phi$. In the classical form, due to Rallis, the Petersson product of two lifts is
$$\langle \Theta_{\phi'}(y'), \Theta_\phi(y)\rangle = c \int_{U(S)(\mathbb{A})} \langle \phi', \omega(g)\phi \rangle\, \langle y', \pi(g) y\rangle\, dg,$$
with a constant $c$ that depends on the measures. For a factorizable datum and form, the integral is a product of local integrals. Almost all of them are unramified, and their product is a partial $L$-value of $\pi$ divided by a product of partial zeta values. The source cites S. Rallis, *L-functions and the oscillator representation*, Lecture Notes in Math. 1245 (1987), and J.-S. Li, Crelle 428 (1992), for this formula. It gives no theorem numbers for them. The source form below keeps the adelic integral. It does not factor the integral into local integrals and does not use an $L$-function of $\pi$.

### The adelic formula

The proof unfolds a sum over the rational points against one of the two integrals over $[U(S)]$. The next lemma is the change of variables.

**Lemma.** The map $((g', g), \gamma) \mapsto (g', g'^{-1} \gamma g)$ carries the product measure on $[U(S)] \times [U(S)] \times U(S)(E)$, with counting measure on the last factor, to the product measure on $[U(S)] \times U(S)(\mathbb{A})$.

Lean: `New.SiegelWeil.measurePreserving_quotMeasure_unfold` (Lib/SiegelWeil/RallisInner/Doubling.lean).

The forms of the source are the *rapid functions* `S.rapidFunctions`. These are automorphic functions $y$ on $U(S)(\mathbb{A})$ such that $|y(g)|\operatorname{ht}(g)^B$ is bounded for every $B$.

**Theorem (Inner product formula).** Let $2n < m$, let $f$ be a clean datum and $f'$ any datum, with $f' = f$ by default. Let $y$, $y'$ be rapid functions on $U(S)(\mathbb{A})$. Put
$$k(g) = \langle f', \omega(g, 1) f\rangle\; \langle y', R(g) y\rangle_{S},$$
where $R$ is right translation and $\langle\,,\rangle_S$ is the Petersson product. Then $k$ is integrable on $U(S)(\mathbb{A})$, and
$$\langle \Theta_{f'}(y'), \Theta_f(y)\rangle_T = \operatorname{vol}([U(T)]) \int_{U(S)(\mathbb{A})} k(g)\, dg.$$

Lean: `New.SiegelWeil.inner_product_formula` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* Write the left side as an integral over $[U(T)] \times [U(S)] \times [U(S)]$ of $\overline{\theta(\omega(g', x) f')\, y'(g')}\, \theta(\omega(g, x) f)\, y(g)$. The second lemma on bounds in [Section 2](/chapter/rallis-inner-product/#doubling) bounds the inner integral over $x$ by $C\operatorname{ht}(g')^l \operatorname{ht}(g)^l$. The rapid decay of $y$ and $y'$ beats these powers. So Fubini's theorem applies, and the integral over $x$ can be done first. The doubling identity turns it into $\operatorname{vol}([U(T)])$ times $\sum_\gamma \langle f', \omega(g'^{-1}\gamma g) f\rangle$. The change of variables of the lemma unfolds the sum over $\gamma$ with the integral over $g$. The result is the integral of $\langle f', \omega(h) f\rangle\, \overline{y'(g')}\, y(g'h)$ over $g' \in [U(S)]$ and $h \in U(S)(\mathbb{A})$. The integral over $g'$ is the Petersson product $\langle y', R(h) y\rangle_S$. $\square$

**Remark (Formalization).** The forms are rapidly decreasing, not cuspidal, and they need not be eigenforms. The formula holds for any rapid functions. The theorem gives the integrability of $k$ as a separate conclusion, so the right side is not a junk value.

### The coefficient of the vacuum

At the places where the datum is the vacuum, its matrix coefficient is a character times a power of a multiplier. The multiplier `New.finMultiplier g` of a finite point $g$ satisfies $|{\rm finMultiplier}(g)|^2 = [gL : L \cap gL]$, where $L = \hat{\mathcal{O}}^n$ is the standard lattice.

**Definition.** For $M \in \mathbb{N}$, a character $b$ of $[U(1)]$ and a finite point $g$ of $U(S)$, the *vacuum coefficient* is
$$\operatorname{mc}(g) = \big(b(\det g)\, \operatorname{finMultiplier}(g)^M\big)^{-1}.$$
Its modulus is $|\operatorname{finMultiplier}(g)|^{-M} = [gL : L \cap gL]^{-M/2}$.

Lean: `New.SiegelWeil.vacuumCoeff`, `New.SiegelWeil.norm_vacuumCoeff` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

**Lemma.** Let $f$ be a vacuum above a set $A$ of places. Let $\gamma$ be a finite point supported on $A$ and its conjugate, and let $g$ be a point whose finite part is integral at $A$. Then
$$\langle f, \omega(\gamma g) f\rangle = \operatorname{mc}(\gamma)\, \langle f, \omega(g) f\rangle,$$
with $M = m$.

Lean: `New.SiegelWeil.weilMatrixCoeff_mul` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* The vector $u = \omega(g, 1) f$ is again a vacuum above $A$, since $g$ is integral at $A$. The projection onto the vacua above $A$ sends $\omega(\gamma, 1) u$ to $\operatorname{mc}(\gamma)\, u$. The character $b(\det\gamma)^{-1}$ comes from the twist, and the power of the multiplier comes from the action of $\gamma$ on $\operatorname{Hom}(S, T)$, which is $m$ copies of its action on $S$. The projection is self adjoint, and it fixes $f$. $\square$

### Sharp data

A sharp datum makes the part of the integral at the level a constant. The real part of the datum is a vector $v$ of the Fock space, and the finite part is a datum $F$. The full datum is $v \otimes F = $ `New.Space.integrated (S.hom T) v F`.

**Definition.** Let $S_0$ be a set of finite places, $J$ a subgroup of the finite points of $U(S)$, and $c \in \mathbb{C}$. A finite datum $F$ is *sharp* for $J$ off $S_0$, with mass $c$, if the following six conditions hold. Here $K_0$ is the group of integral finite points.

1. $\langle F, F\rangle \neq 0$.
2. $F$ lies in the finite part, the span of the finite translates of the vacuum.
3. For every Fock vector $v$ and every set $A$ disjoint from $S_0$, the datum $v \otimes F$ is a vacuum above $A$.
4. For every finite point $g$ integral off $S_0$, $\langle F, \omega(g) F\rangle$ is $\langle F, F\rangle$ if $g \in J \cap K_0$, and $0$ otherwise.
5. $\langle F, F\rangle / [K_0 : J \cap K_0] = c$.
6. For every Fock vector $v$, the datum $v \otimes F$ is clean.

Lean: `New.SiegelWeil.IsSharp` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Lemma.** Let $F$ be sharp for $J$ off $S_0$ with mass $c$. Then $J$ is open and $c \neq 0$. If $b$ has a weight and a tame part, then $b \circ \det$ is trivial on the integral points supported on the places off $S_0$ and their conjugates.

Lean: `New.SiegelWeil.IsSharp.isOpen_level`, `New.SiegelWeil.IsSharp.mass_ne_zero`, `New.SiegelWeil.IsSharp.isUnramifiedOn` (Lib/SiegelWeil/RallisInner/SharpData.lean).

*Proof.* The matrix coefficient is continuous and is $\langle F, F\rangle \neq 0$ at $1$. By condition 4 it vanishes on $K_0$ outside $J$. So a neighbourhood of $1$ lies in $J$, and $J$ is open. As $K_0$ is compact, the index of $J \cap K_0$ is finite, so $c \neq 0$. For the last claim, compute the coefficient of the vacuum times $F$ at an integral point $k$ supported off $S_0$ in two ways, as $k \cdot 1$ and as $1 \cdot k$. The two results differ by the factor $b(\det k)^{-1}$, which must therefore be $1$. $\square$

**Theorem.** Let $F$ be sharp for $J$ off $S_0$, let $b$ have weight $\gamma'$, let $v$ be a Fock vector and $\phi = v \otimes F$. Let $x$ be a real point, $u$ a finite point supported on the places off $S_0$ and their conjugates, and $g$ a finite point integral off $S_0$. Then
$$\langle \phi, \omega(x u g)\phi\rangle = \langle v, \Omega(x) v\rangle\; \operatorname{mc}(u)\; \langle F, F\rangle\, \mathbf{1}_{J \cap K_0}(g),$$
where $\Omega(x)$ is the real Weil representation `New.realPairWeil γ γ' (x, 1)`, for any $\gamma$.

Lean: `New.SiegelWeil.IsSharp.weilMatrixCoeff_integrated_mul` (Lib/SiegelWeil/RallisInner/SharpData.lean).

### The Rallis series

Every finite point $h$ factors as $h = u g$ with $u$ supported on the places of a set $A$ and their conjugates, and $g$ integral at $A$. The cosets of the group `New.localLevel n A` of points integral at $A$ have representatives of this form.

**Definition.** For a coset $q$ of `localLevel n A`, `cosetRep q` is the component above $A$ and its conjugate of a chosen element of $q$. It represents $q$ and is supported on $A$ and its conjugate.

Lean: `New.SiegelWeil.cosetRep` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

**Definition.** For $M \in \mathbb{N}$, a character $b$, a set $A$ of places and a function $y$ on $U(S)(\mathbb{A})$, the *Rallis series* is
$$\mathcal{R}_A y(g) = \sum_{q} \operatorname{mc}(r_q)\; y(g\, r_q),$$
where $q$ runs over the cosets of `localLevel n A` and $r_q = $ `cosetRep q`.

Lean: `New.SiegelWeil.rallisSeries` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

**Remark (Formalization).** The series is a `tsum`. If the terms are not summable, the value is the junk value $0$. The representative `cosetRep q` uses `Quotient.out`, a choice. Section 4 proves that the terms are absolutely summable for $M = m > 2n$, so the value is the sum there.

**Lemma.** Let $F$ be sharp for $J$ off $S_0$ with mass $c$, let $v$ be a Fock vector and $x$ a real point, and let $P$ be a right $J$-invariant function on the finite points. If $g \mapsto \langle \phi, \omega(x g)\phi\rangle P(g)$ is integrable, its integral over the finite points is the sum over the cosets $q$ of the points integral off $S_0$ of
$$c\, \langle v, \Omega(x) v\rangle\, \operatorname{mc}(r_q)\, P(r_q).$$

Lean: `New.SiegelWeil.IsSharp.hasSum_integral_weilMatrixCoeff_mul` (Lib/SiegelWeil/RallisInner/SharpData.lean).

*Proof.* Cut the integral into the cosets $r_q\, \texttt{localLevel}$. On each coset the theorem above gives the integrand as $\langle v, \Omega(x) v\rangle\, \operatorname{mc}(r_q)$ times $\langle F, F\rangle \mathbf{1}_{J \cap K_0}$ times $P(r_q)$, by the $J$-invariance of $P$. The Haar measure gives $K_0$ volume $1$, so the integral of $\langle F, F\rangle \mathbf{1}_{J\cap K_0}$ is $\langle F, F \rangle / [K_0 : J\cap K_0] = c$. $\square$

**Theorem (Inner product formula for sharp data).** Let $2n < m$, let $F$ be sharp for $J$ off $S_0$ with mass $c$, let $b$ have weight $\gamma'$, and let $v$ be a Fock vector. Let $y$, $y'$ be rapid functions with $y$ fixed by $J$, and let $z = \mathcal{R}_{S_0^c} y$ with $M = m$. Then the function
$$x \mapsto \langle v, \Omega(x) v\rangle\; \langle y', R(x) z\rangle_S$$
on the real points of $U(S)$ is integrable, and
$$\langle \Theta_{v\otimes F}(y'), \Theta_{v\otimes F}(y)\rangle_T = \operatorname{vol}([U(T)])\; c \int_{U(S)(\mathbb{R})} \langle v, \Omega(x) v\rangle\; \langle y', R(x) z\rangle_S\, dx.$$

Lean: `New.SiegelWeil.IsSharp.petersson_lift_eq_integral` (Lib/SiegelWeil/RallisInner/SharpData.lean).

*Proof.* Condition 6 makes $v \otimes F$ clean, so the inner product formula applies. Its adelic integral is first integrated over the finite points, with $P(g) = \langle y', R(x g) y\rangle_S$. The lemma turns that integral into $c$ times a sum over cosets, and the sum is $\langle y', R(x) z\rangle_S$. $\square$

So the formula has three parts: the real integral, the mass $c$ at the level, and the Rallis series over the places off $S_0$.

### A source of sharp data

The source builds sharp data from functions on matrices modulo an ideal. Let $\mathfrak{m}$ be a modulus, with residue ring $\mathcal{O}/\mathfrak{m}$. The datum `New.vacuumDatum S T 𝔪 Ψ` is the function $\Psi$ at the places of $\mathfrak{m}$ and the vacuum elsewhere.

**Definition.** A function $\Psi \neq 0$ on the $m \times n$ matrices over $\mathcal{O}/\mathfrak{m}$ is *sharp* for a group $J$ if the principal level $J(\mathfrak{m})$ lies in $J$, $J \subseteq K_0$, $J$ fixes the datum $\Psi \otimes \mathrm{vac}$, and there is a matrix $A$ such that $A x$ is the reduction of a point of $J$ whenever $\Psi(x) \neq 0$.

Lean: `New.SiegelWeil.IsSharpFn` (Lib/SiegelWeil/RallisInner/SharpData.lean).

**Proposition.** Let $\Psi$ be sharp for $J$. Suppose that all signs of $S$ agree or that $\mathfrak{m} \neq (1)$. Then $\Psi \otimes \mathrm{vac}$ is sharp for $J$ off the places of $\mathfrak{m}\bar{\mathfrak{m}}$, with mass
$$c = \frac{\sum_x |\Psi(x)|^2}{|\mathcal{O}/\mathfrak{m}|^{mn}\; [K_0 : J \cap K_0]}.$$
For the principal level $J = J(\mathfrak{m})$ and a function $F$ supported on $\{x : Ax = 1\}$, the index is $|GL_n(\mathcal{O}/\mathfrak{m})|$.

Lean: `New.SiegelWeil.IsSharpFn.isSharp`, `New.SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one` (Lib/SiegelWeil/RallisInner/SharpData.lean).

The hypothesis on the signs or on $\mathfrak{m}$ serves only for condition 6. If $\mathfrak{m} \neq (1)$, the support of $\Psi$ consists of primitive matrices at a place of $\mathfrak{m}$, and these have left inverses, as case (b) of the clean condition asks.

**Remark (Formalization).** The mass $c$ in these results is explicit, but the volume $\operatorname{vol}([U(T)])$ and the real integral are not computed. The theorems need `IsSharp` as a hypothesis. For the data of the source it comes from `IsSharpFn.isSharp`. Whether every caller supplies it is part of the open finding F-084.
