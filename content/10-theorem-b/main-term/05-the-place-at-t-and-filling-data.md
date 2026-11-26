---
title: The place at T and filling data
lean:
  - New/Spanning/MainTerm/FillingLevel.lean
decls:
  - New.Filling.IsIntegralOff
  - New.Filling.cosetAmplitude
  - New.Filling.boundedNonzeroIntegers
  - New.Filling.finite_boundedNonzeroIntegers
  - New.Filling.entrySet
  - New.Filling.toPlaces
  - New.Filling.IsFillingData
  - New.Filling.exists_places_integralOff
  - New.Filling.exists_isIntegralOff_toPlaces_eq
  - New.Filling.mem_unitaryLevel_iff
  - New.Filling.mem_latticeStabilizer_iff
  - New.Filling.exists_integralPlace
  - New.Filling.isMulLeftInvariant_haar_inv
  - New.Filling.charOnPlaces_add_star
  - New.Filling.exists_isFillingData
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The place at T and filling data

The class sums are sums over rational points of $G(E)$. The local bounds of [the finite places](/chapter/finite-densities/) are statements at one finite place, or at a finite product of finite places. This section chooses a finite set $T$ of finite places that holds all the data that is not integral. Outside $T$ every relevant element is integral, so the places outside $T$ contribute only the condition "integral". At $T$ the product of the completions is one finite place in the sense of [the lattice datum](/chapter/finite-densities/#the-lattice-datum), and this section builds a lattice datum on it.

In this section $T$ is a finite set of finite places of $E$ that is stable under conjugation. $\operatorname{LocProd}(T) = \prod_{w \in T} E_w$ is the product of the completions, $\mathcal O$ is its ring of integers, and $\mathbb A_f$ is the ring of finite adeles. An adele $a$ is *integral off $T$* if $a_w$ is integral for every $w \notin T$. The ring of $T$-integers of $E$ is the set of $t \in E$ that are integral off $T$.

### Orbit sums and the set of entries

**Definition (Integral off $T$).** An element $x$ of the finite adelic unitary group is *integral off $T$* if the entries of $x$ and of $x^{-1}$ are integral off $T$.

Lean: `New.Filling.IsIntegralOff` (New/Spanning/MainTerm/FillingLevel.lean).

The amplitude sums of [Poincaré series and unfolding](/chapter/poincare-series/) add the amplitudes of the terms $\gamma$ over a block $(c, s, c')$. The terms are taken up to the left and right action of the rational unipotent group $\mathsf U(E)$. The coset amplitude collects one double coset.

**Definition (Coset amplitude).** For a side (full or cut), classes $c, c'$, a reduction $s$ and $\gamma \in G(E)$,
$$\operatorname{cosetAmplitude}(c, s, c')(\gamma) = \sum_{(u, u') \in \mathsf U(E)^2} \mathbf 1\bigl[u\gamma u'^{-1} \text{ lies over } (c, s, c')\bigr]\, A(c, c')(u \gamma u'^{-1}),$$
where $A(c, c')$ is the amplitude of the Bessel function named by the side. The sum is the Lean `tsum`; it is $0$ if the family is not summable.

Lean: `New.Filling.cosetAmplitude` (New/Spanning/MainTerm/FillingLevel.lean).

The entries of the Weyl elements that occur are quotients of leading minors. A leading minor of a term with a nonzero cut amplitude is a nonzero integer of bounded size ([Section 6](/chapter/main-term/#kloosterman-sums-and-unfolding)).

**Definition (Bounded integers and entries).** $\operatorname{boundedNonzeroIntegers}$ is the set of nonzero integers $\delta$ of $E$ with $|\Phi_v\delta|^2 \leq b^{270n^2}$ at every infinite place $v$. The set $\mathcal T$ of *entries* (`entrySet`) is the set of units $t \in E^\times$ with $t = \delta/\delta'$ for two elements $\delta, \delta'$ of $\operatorname{boundedNonzeroIntegers}$.

Lean: `New.Filling.boundedNonzeroIntegers`, `New.Filling.entrySet` (New/Spanning/MainTerm/FillingLevel.lean).

**Lemma.** The set $\operatorname{boundedNonzeroIntegers}$ is finite. So $\mathcal T$ is finite.

Lean: `New.Filling.finite_boundedNonzeroIntegers` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* An integer of $E$ whose images under all complex embeddings have absolute value at most $R$ is a root of a monic integer polynomial of degree $[E : \mathbb Q]$ with coefficients bounded in terms of $R$. There are finitely many such polynomials. The infinite places give all the embeddings up to conjugation, and conjugate embeddings have the same absolute value. The set $\mathcal T$ is the image of a product of two finite sets under $(\delta, \delta') \mapsto \delta/\delta'$, so it is finite. $\square$

**Definition (Projection to $T$).** $\operatorname{toPlaces}$ is the homomorphism from the finite adelic unitary group of the lattice basis to the unitary group over $\operatorname{LocProd}(T)$ that takes the components at $T$ of the entries.

Lean: `New.Filling.toPlaces` (New/Spanning/MainTerm/FillingLevel.lean).

### The choice of $T$

**Theorem (A set of places).** For a finite set $T_0$ of nonzero elements of $E$ there is a finite set $T$ of finite places, stable under conjugation, such that: each $t \in T_0$ and its inverse are $T$-integers; the inverse of the level $M$ is integral off $T$; the lattice basis and its inverse are integral off $T$; and $N^{-1}$ is a $T$-integer.

Lean: `New.Filling.exists_places_integralOff` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* A finite adele $a$ is integral at all places outside a finite set, by the definition of the restricted product. So $a$ is integral off $T$ for all $T$ that contain this set; this holds eventually along the finite sets ordered by inclusion. The conditions ask finitely many adeles to be integral off $T$: the elements of $T_0$ and their inverses, $M^{-1}$, the entries of the lattice basis and of its inverse, and $N^{-1}$. A finite intersection of eventual conditions is eventual. Every $T$ lies in $T \cup \bar T$, which is stable under conjugation, so stable sets occur arbitrarily far out. Take a stable $T$ far enough out. $\square$

The next two results compare the adelic group with the group at $T$.

**Theorem (Lifts).** Every $y$ in the unitary group over $\operatorname{LocProd}(T)$ is $\operatorname{toPlaces}(x)$ for some $x$ that is integral off $T$. If $y$ lies in the unipotent group $\mathsf U$, then $x$ can be taken in $\mathsf U$; if $y$ lies in the floor group $H$, then $x$ can be taken in $H$. One $x$ does all three.

Lean: `New.Filling.exists_isIntegralOff_toPlaces_eq` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* Let $\varphi$ extend each matrix entry by zero outside $T$. It is additive and multiplicative, but it does not keep $1$. Put $z = y - 1$ and $x = 1 + \varphi(z)$. The condition $y^* J y = J$ reads $z^* J z + z^* J + J z = 0$. The Gram matrix $J$ of the lattice basis has entries in $E$, and $\varphi(Jz) = J\varphi(z)$ since $J$ acts entrywise. So $\varphi$ keeps this identity, and $x$ is unitary. The same construction applied to $y^{-1}$ gives the inverse of $x$, since $\varphi(z)\varphi(z') = \varphi(zz')$. Off $T$, $x$ and $x^{-1}$ are the identity, so they are integral. The groups $\mathsf U$ and $H$ are defined by conditions on $y - 1$ that are linear and entrywise with coefficients in $E$, so $\varphi$ keeps them. $\square$

**Theorem (Levels split at $T$).** Let $u$ be a finite idele with $u^{-1}$ integral off $T$. Then $x$ lies in the unitary level of $u$ over $\hat{\mathcal O}$ if and only if $x$ is integral off $T$ and $\operatorname{toPlaces}(x)$ lies in the unitary level of $u$ at $T$ over $\mathcal O$.

Lean: `New.Filling.mem_unitaryLevel_iff` (New/Spanning/MainTerm/FillingLevel.lean).

Here the unitary level of $u$ over a ring $R$ is the set of $x$ with $x, x^{-1}$ integral over $R$ and $u^{-1}(x - 1)$ integral over $R$ ([congruence subgroups](/chapter/finite-densities/#the-lattice-datum)).

*Proof.* An adele is in $\hat{\mathcal O}$ if and only if its components at $T$ are in $\mathcal O$ and it is integral off $T$. Apply this to each entry of $x$, of $x^{-1}$ and of $u^{-1}(x - 1)$. The conditions at $T$ give the level of $u$ at $T$. The conditions off $T$ for $x$ and $x^{-1}$ say that $x$ is integral off $T$. The last condition off $T$ follows from these: $x - 1$ is integral off $T$, and so is $u^{-1}$. $\square$

**Corollary (The lattice stabilizer).** $x$ lies in the stabilizer $K$ of the lattice if and only if $x$ is integral off $T$ and $\operatorname{toPlaces}(x)$ is integral at $T$.

Lean: `New.Filling.mem_latticeStabilizer_iff` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* The stabilizer is the unitary level of $u = 1$. Apply the theorem with $u = 1$. $\square$

### The finite place at $T$

**Definition (Character at $T$).** $\operatorname{charOnPlaces}(T)(x) = \psi_f(-\varpi^{-1}\,\tilde x)$, where $\tilde x$ extends $x$ by zero, $\psi_f$ is the standard character of the finite adeles and $\varpi$ is the generator of the different in the data $S$ ([Section 3](/chapter/main-term/#frequencies-and-poisson-summation)).

**Lemma (Traces).** $\operatorname{charOnPlaces}(T)(x + \bar x) = 1$.

Lean: `New.Filling.charOnPlaces_add_star` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* The element $\varpi$ is skew, so $-\varpi^{-1}\bar{\tilde x} = -\overline{(-\varpi^{-1}\tilde x)}$. The character $\psi_f$ takes the same value at conjugate adeles. So the value at $\bar x$ is the inverse of the value at $x$, and their product is $1$. $\square$

**Theorem (The place at $T$).** There is a structure of a finite place on $\operatorname{LocProd}(T)$ whose additive character is $\operatorname{charOnPlaces}(T)$.

Lean: `New.Filling.exists_integralPlace` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* The integers are $\mathcal O$ and the measure is the Haar measure of mass $1$ on $\mathcal O$. The modulus of a unit $x$ is $\prod_{w \in T}|x_w|$, the inverse of its index. The ring has a skew unit $i$ with $i^2 = -1$ and an integral $\tau$ with $\tau + \bar\tau = 1$. The map $(a, b) \mapsto \tau i a + b$ on pairs of skew elements is onto, and the preimage of $\mathcal O$ is a product of two copies of the integral skew elements. This gives a Haar measure on the skew elements of mass $1$ on the integral ones. The integers are self-dual: $a \in \mathcal O$ if and only if the character is trivial on $\mathcal O a$. By extension by zero this is the self-duality of $\hat{\mathcal O}$ for $x \mapsto \psi_f(-\varpi^{-1}x)$. A Plancherel kernel is the indicator of $\mathcal O$, which is its own transform by self-duality. $\square$

**Theorem (Unimodularity).** For any structure of a finite place on $\operatorname{LocProd}(T)$, the inverse of a left Haar measure on the unitary group of the lattice basis is left invariant.

Lean: `New.Filling.isMulLeftInvariant_haar_inv` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* The Gram matrix of the lattice basis is unimodular, so it has an orthonormal basis $k$ over $\hat{\mathcal O}$. Conjugation by $k$ identifies the adelic unitary group with the standard group $G_f$, whose Haar measure is invariant on both sides. By the corollary on the stabilizer, the projection to $T$ maps the points integral off $T$ onto the group at $T$, and the lifts are given by the theorem on lifts. The image of the bi-invariant measure, restricted to the points integral off $T$, is a left Haar measure at $T$ whose inverse is left invariant. Haar measures differ by a positive constant. $\square$

This proves field 3 of a [large lattice datum](/chapter/finite-densities/#the-lattice-datum), which that chapter keeps as a hypothesis.

**Definition (Filling data).** Place data $F$ on $\operatorname{LocProd}(T)$, for the Gram matrix of the lattice basis, with $3\varrho + 6$ further hyperbolic pairs and an orthonormal part of size $k - (6\varrho + 13)$, are *filling data* if $F$ is a large lattice datum, the character of the place is $\operatorname{charOnPlaces}(T)$, and the level unit of $F$ is the component of $M$ at $T$.

Lean: `New.Filling.IsFillingData` (New/Spanning/MainTerm/FillingLevel.lean).

**Theorem (Filling data exist).** For every conjugation-stable finite set $T$ there are a finite place on $\operatorname{LocProd}(T)$ and place data $F$ that are filling data.

Lean: `New.Filling.exists_isFillingData` (New/Spanning/MainTerm/FillingLevel.lean).

*Proof.* Take the place of the theorem above. Since $1000(2\varrho + 2) \leq k$, $k = (k - (6\varrho + 13)) + 2(3\varrho + 6) + 1$ holds in $\mathbb N$. [Lattice data exist](/chapter/finite-densities/#the-lattice-datum) with level unit $M$ at $T$. Field 1 of a large datum: the ideal zeta value at $T$ is at most the global value, and the global value to the power $n$ is at most $1 + 2^{-n}$ by the sizes of [the data](/chapter/data-and-sizes/); the bounds $3\varrho + 5 < 9n$ and $53n \leq k - (6\varrho + 13)$ follow from $1000(2\varrho+2) \leq k$. Field 2 is the lemma on traces. Field 3 is unimodularity. $\square$

**Remark (Formalization).** In the source, `IsFillingData` is a class that extends `IsLargeLatticeData`. Each theorem of the following sections takes an arbitrary instance. The main theorem obtains one by this theorem, so no hypothesis remains.
