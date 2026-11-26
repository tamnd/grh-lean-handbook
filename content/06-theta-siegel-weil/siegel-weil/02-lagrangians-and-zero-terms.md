---
title: Lagrangians and zero terms
lean:
  - Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean
  - Lib/Weil/DualPair/MixedModel.lean
decls:
  - New.SiegelWeil.CompleteSplitting
  - New.SiegelWeil.splitWeil
  - New.SiegelWeil.Lagrangian
  - New.SiegelWeil.mixedValue
  - New.SiegelWeil.CompleteSplitting.lagrangian
  - New.SiegelWeil.Lagrangian.exists_completeSplitting
  - New.SiegelWeil.Lagrangian.chosenSplitting
  - New.SiegelWeil.Lagrangian.zeroTerm
  - New.SiegelWeil.zeroTerm_lagrangian_eq_theta
  - New.SiegelWeil.isometrySplitting
  - New.SiegelWeil.zeroTerm_isometrySplitting
  - New.SiegelWeil.exists_lagrangian_equiv_containing
  - New.SiegelWeil.mixedValue_splitWeil_levi
  - New.SiegelWeil.mixedValue_splitWeil
  - New.SiegelWeil.hasSum_mixedValue_theta_splitWeil
  - New.SiegelWeil.norm_zeroTerm_parabolic_mul
  - New.SiegelWeil.norm_zeroTerm_vacElem_pos
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lagrangians and zero terms

This section defines the two sides of the Siegel-Weil formula. The left side needs the Weil representation of the pair $(S, T)$ and the theta functional. The right side needs the Lagrangians of $S$ and the zero term of each Lagrangian. The zero term is the term of the Eisenstein series. The section proves that the zero term depends only on the Lagrangian, and it computes how the zero term changes under the parabolic subgroup and under the rational points.

### The pair and its representation

Fix a CM field $E$ with Weil data, as in [Chapter 1](/chapter/weil-representation/). Let $S$ be a hermitian space with a point, of rank $n$ and signs $s$, and let $T$ be one of rank $m$ and signs $t$. Write $G_S$ and $G_T$ for their adelic unitary groups. The space $\mathrm{Hom}(S, T)$ is a hermitian space of rank $mn$, and $\mathcal{S}(\mathrm{Hom}(S, T))$ is its space of integrable coefficients against the vacuum. The representation [`New.pairWeil`](/decl/New.pairWeil/) of $G_S \times G_T$ on this space sends $(g, h)$ to $a(\det h)\, b(\det g)^{-1}\, \omega(x \mapsto h x g^{-1})$, for two characters $a$ and $b$ of the norm one ideles.

**Definition (The split Weil representation).** The representation $\omega$ of this chapter is `pairWeil` with $b = 1$ and $a = \upsilon_1^{\lfloor n/2 \rfloor}$, where $\upsilon_1$ is the splitting character $\upsilon$ restricted to the norm one ideles. In $\omega(g, h)$ the element $g$ is in $G_S$ and $h$ is in $G_T$.

Lean: `New.SiegelWeil.splitWeil`, `New.WeilData.upsilonU1` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/Defs.lean).

The twist by $\upsilon_1^{\lfloor n/2 \rfloor}$ makes $G_T$ act on the slices by substitution alone. The theorem on the Levi action below shows this.

**Definition (Complete splitting).** A complete splitting of $S$ into $p$ hyperbolic planes is a [splitting](/decl/New.Space.Splitting/) of $S$ over the space of rank zero with $p$ columns. It consists of two isotropic frames $l$ and $k$, each an $n \times p$ matrix over $E$, with $l^* J k = 1$, so that $S = l E^p \oplus k E^p$. The count of the basis gives $n = 2p$.

Lean: `New.SiegelWeil.CompleteSplitting` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Definition (Lagrangian).** A Lagrangian of $S$ is a subspace $L$ of $E^n$ such that $y \in L$ if and only if $x^* J y = 0$ for every $x \in L$. For a complete splitting $P$, the span of the columns of $P.k$ is a Lagrangian, written $L_P$.

Lean: `New.SiegelWeil.Lagrangian`, `New.SiegelWeil.CompleteSplitting.lagrangian` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Definition (Values in the Schrödinger model).** Let $P$ be a complete splitting of $S$ with $p$ columns. It induces a splitting of $\mathrm{Hom}(S, T)$ over $\mathrm{Hom}(0, T) = 0$ with $mp$ columns. For an adelic $m \times p$ matrix $x$, the value of $f$ at $x$ is
$$f[x] = \theta_0\big(f[x]_P\big) \in \mathbb{C},$$
where $f[x]_P$ is the slice of $f$ at $x$ for the induced splitting and $\theta_0$ is the theta functional of the space of rank zero, which reads a vector as a number. The map $f \mapsto f[x]$ is a bounded functional on $\mathcal{S}(\mathrm{Hom}(S, T))$.

Lean: `New.SiegelWeil.mixedValue`, `New.Space.Splitting.homSource`, `New.Space.Splitting.homSlice` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean).

When $T$ is the standard definite space, the function $x \mapsto f[x]$ plays the part of a Schwartz-Bruhat function on $\mathbb{A}^{m \times p}$ in the Schrödinger model. The source calls it the Schrödinger function of $f$. The source does not state an isomorphism with a space of functions, and the argument needs only the values.

### Lagrangians come from splittings

**Theorem (Every Lagrangian is split).** For every Lagrangian $L$ of $S$ there are a natural number $r$ and a complete splitting $P$ of $S$ into $r$ hyperbolic planes with $L_P = L$.

Lean: `New.SiegelWeil.Lagrangian.exists_completeSplitting` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Choose a basis $k$ of $L$. It has a left inverse, and it is isotropic: each column of $k$ is in $L$, so it is orthogonal to every column of $k$. The splitting theorem `New.Space.exists_splitting` extends $k$ to a splitting $S = (lE^r \oplus kE^r) \perp V$ with a complementary space $V$ of rank $d$. Suppose that $d > 0$. The embedding $\iota$ of $V$ is orthogonal to $k$, and so its columns are orthogonal to $L$. Since $L$ is its own orthogonal, the columns of $\iota$ lie in $L$, and $\iota = k c$ for a matrix $c$. Then the Gram matrix of $V$ is $\iota^* J \iota = \iota^* J k c = 0$, since $\iota$ is orthogonal to $k$. This contradicts that the Gram matrix of a space is invertible. So $d = 0$, and the splitting is complete. $\square$

**Definition (The chosen splitting and the zero term).** For each Lagrangian $L$ the source chooses one pair $(r, P_L)$ from the theorem above. The zero term along $L$ is the functional
$$\mathrm{ev}_L(f) = f[0] \quad \text{in the Schrödinger model of } P_L.$$
By `New.Space.Splitting.zeroTerm_apply` of [Chapter 1](/chapter/weil-representation/), $\mathrm{ev}_L(f)$ is the mean of $\theta(\varrho(z) f)$ over the maps $z : S \to T$ that vanish on $L$, adelic modulo rational.

Lean: `New.SiegelWeil.Lagrangian.chosenSplitting`, `New.SiegelWeil.Lagrangian.completeSplitting`, `New.SiegelWeil.Lagrangian.numPlanes`, `New.SiegelWeil.Lagrangian.zeroTerm` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (The zero term depends on the Lagrangian only).** Let $P$ be a complete splitting of $S$. For every $f$,
$$\mathrm{ev}_{L_P}(f) = \theta_0\big(\mathrm{ev}_{P}(f)\big),$$
where $\mathrm{ev}_P$ is the zero term of the splitting of $\mathrm{Hom}(S, T)$ induced by $P$.

Lean: `New.SiegelWeil.zeroTerm_lagrangian_eq_theta`, `New.Space.Splitting.zeroTerm_homSource_congr` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean).

*Proof.* Let $Q = P_{L_P}$ be the chosen splitting of $L_P$. The columns of $P.k$ lie in the span of $Q.k$, so $P.k = Q.k\, c$ for a matrix $c$. Since $Q.k$ is isotropic, $Q.k^* J P.k = Q.k^* J Q.k\, c = 0$. The complements of $P$ and $Q$ are the space of rank zero, so their embeddings are equal. The zero term of a splitting of $\mathrm{Hom}(S, T)$ depends only on its frame $k$ up to these two conditions, by `zeroTerm_homSource_congr`. So the zero terms of $P$ and $Q$ agree, and the left side is by definition the zero term of $Q$. $\square$

**Remark (Formalization).** The splitting $P_L$ is chosen by `Nonempty.some`. The theorem above shows that the zero term does not depend on the choice. The number $r$ of planes is determined by $L$, since $n = 2r$.

### The action of the rational points

A rational isometry $\gamma \in U(S)(E)$ gives a splitting of $S$ with no planes, whose complement is $S$ itself, embedded by $\gamma$. Call it $D_\gamma$.

**Theorem (Rational isometries).** For $\gamma \in U(S)(E)$ and every $f$, the zero term of the splitting of $\mathrm{Hom}(S, T)$ induced by $D_\gamma$ is $f \mapsto \omega(\gamma^{-1}, 1) f$. For a complete splitting $P$, the Lagrangian of the composite splitting $D_\gamma \circ P$, which is $\gamma L_P$, has
$$\mathrm{ev}_{\gamma L_P}(f) = \mathrm{ev}_{L_P}\big(\omega(\gamma^{-1}, 1) f\big).$$

Lean: `New.SiegelWeil.isometrySplitting`, `New.SiegelWeil.zeroTerm_isometrySplitting`, `New.SiegelWeil.zeroTerm_lagrangian_isometrySplitting_comp` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* A rational point acts on a vector, read as a function, by a change of variables. This is the corollary of Weil's invariance in [Chapter 1](/chapter/weil-representation/). The zero term of a splitting with no planes is a mean over a single point, so it is this change of variables. The second claim follows from the first and the rule that the zero term of a composite splitting is the composite of the zero terms. $\square$

The rational group acts on the Lagrangians, and the sum of all zero terms is invariant under this action. Section 5 uses this in the proof of the invariance of the difference of the two sides.

### Splitting off a part

The induction on the rank uses one more structure. Let $D_1$ be a splitting $S = (lE^r \oplus kE^r) \perp S_1$, with isotropic frame $D_1.k$. The Lagrangians of $S$ that contain the columns of $D_1.k$ correspond to the Lagrangians of $S_1$.

**Theorem (Lagrangians through a frame).** Let $D_1$ be a splitting of $S$ over $S_1$. There is a bijection $\sigma$ from the Lagrangians of $S_1$ to the Lagrangians of $S$ that contain the columns of $D_1.k$, such that
$$\mathrm{ev}_{\sigma(L)}(f) = \mathrm{ev}_L\big(\mathrm{ev}_{D_1}(f)\big)$$
for every Lagrangian $L$ of $S_1$ and every $f$. Here $\mathrm{ev}_{D_1}$ is the zero term $\mathcal{S}(\mathrm{Hom}(S, T)) \to \mathcal{S}(\mathrm{Hom}(S_1, T))$ along the splitting of $\mathrm{Hom}(S, T)$ induced by $D_1$.

Lean: `New.SiegelWeil.exists_lagrangian_equiv_containing`, `New.Space.Splitting.zeroTerm_homSource_comp`, `New.Space.Splitting.comp` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean; Lib/Weil/MixedModel/IsotropicSplitting.lean).

*Proof.* Send a Lagrangian $L_1$ of $S_1$ to the Lagrangian of the composite splitting $D_1 \circ P_{L_1}$. Its elements are the vectors $D_1.k\, a + \iota w$ with $w \in L_1$, so it contains the columns of $D_1.k$. In the other direction, send a Lagrangian $L$ that contains $D_1.k$ to its preimage under $\iota$. This preimage is a Lagrangian of $S_1$: a vector $y$ of $S_1$ is orthogonal to the preimage if and only if $\iota y$ is orthogonal to $L$, because $L$ is spanned by its intersection with $\iota S_1$ and the columns of $D_1.k$, which are orthogonal to $\iota S_1$. The two maps are inverse to each other, by the description of the elements. For the zero terms, the zero term of a composite splitting is taken in two stages, by `zeroTerm_homSource_comp`. $\square$

### The Levi subgroup and the substitution law

For a complete splitting $P$ and $a \in \mathrm{GL}_p(\mathbb{A})$, the Levi element $P.\mathrm{levi}(a, 1)$ acts by $k \mapsto ka$ and $l \mapsto l (a^*)^{-1}$. The following is the Levi law of [Chapter 1](/chapter/weil-representation/), read in the values $f[x]$.

**Theorem (The Levi law for the pair).** Let $P$ be a complete splitting of $S$, let $a \in \mathrm{GL}_p(\mathbb{A})$, $h \in G_T$ and $x$ an adelic $m \times p$ matrix. For every $f$,
$$\big(\omega(P.\mathrm{levi}(a, 1), h) f\big)[x] = \chi(\det a)^{-1} \sqrt{|\det a|}^{\,m}\, f[h^{-1} x a],$$
where $\chi$ is the unitary character `New.AutChar.spaceChar 1 m` of the ideles and $|\cdot|$ is the idele norm. In particular $(\omega(1, h) f)[x] = f[h^{-1} x]$.

Lean: `New.SiegelWeil.mixedValue_splitWeil_levi`, `New.SiegelWeil.mixedValue_splitWeil`, `New.AutChar.spaceChar` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* The complement of $P$ has rank zero, so $h$ acts on its space of vectors as the identity. The slice law for the Levi element on $\mathrm{Hom}(S, T)$, `New.Space.Splitting.homSlice_levi`, gives the factor and the substitution. The character $\upsilon_1^{\lfloor n/2 \rfloor}$ of $\det h$ in $\omega$ cancels the character that $h$ gives on the slices, since $\lfloor n/2 \rfloor = p$. $\square$

**Theorem (Theta in the Schrödinger model).** For every $h \in G_T$ and every $f$, the family $\xi \mapsto f[h^{-1}\, x_T^{-1} \xi]$, indexed by the rational $m \times p$ matrices $\xi$, is summable with sum $\theta(\omega(1, h) f)$. Here $x_T$ is the point of $T$, which puts $\xi$ in standard coordinates.

Lean: `New.SiegelWeil.hasSum_mixedValue_theta_splitWeil` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is the theorem on the theta of the slices from [Chapter 1](/chapter/weil-representation/), for the induced splitting of $\mathrm{Hom}(S, T)$, together with the substitution law. $\square$

This is the classical formula $\theta(g, h; \varphi) = \sum_\xi (\omega(g, h)\varphi)(\xi)$ of Section 1, now a theorem in the source.

### The size of the zero terms

Two facts on the norms of zero terms enter the proof of the formula. The first says how the parabolic subgroup scales the zero term. The second says that the zero term of a translate of the vacuum is never zero.

**Theorem (The parabolic subgroup scales the zero term).** Let $P$ be a complete splitting of $S$ with frame $k$. Let $g \in G_S$ and $a \in \mathrm{GL}_p(\mathbb{A})$ with $g k = k a$ in adelic coordinates. Then for all $g' \in G_S$ and all $f$,
$$\big\|\mathrm{ev}_{L_P}\big(\omega(g g', 1) f\big)\big\| = \sqrt{|\det a|}^{\,m}\, \big\|\mathrm{ev}_{L_P}\big(\omega(g', 1) f\big)\big\|.$$

Lean: `New.SiegelWeil.norm_zeroTerm_parabolic_mul`, `New.Space.Splitting.ActsOnFrame` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* By the rule for elements that keep the frame, `New.Space.Splitting.homSource_zeroTerm_pairWeil`, the zero term of $\omega(g, 1)\varphi$ is $\chi(\det a)^{-1}\sqrt{|\det a|}^{\,m}$ times the zero term of $\varphi$. The block of $g$ on the complement is $1$, since the complement has rank zero. Apply this to $\varphi = \omega(g', 1) f$. The character has norm $1$. $\square$

**Theorem (The vacuum has nonzero zero terms).** Let $P$ be a complete splitting of $S$ and $v$ the vacuum vector of $\mathrm{Hom}(S, T)$. For every $g \in G_S$,
$$0 < \big\|\mathrm{ev}_{L_P}\big(\omega(g, 1) v\big)\big\|.$$

Lean: `New.SiegelWeil.norm_zeroTerm_vacElem_pos`, `New.Space.Splitting.exists_slice_omega_vacElem_of_isEmpty` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Up to a character, the zero term is the zero term of $\omega(g')v$ for the induced splitting of $\mathrm{Hom}(S, T)$, for an element $g'$ of the group of $\mathrm{Hom}(S, T)$. For a splitting with complement of rank zero, every slice of $\omega(g')v$ is a nonzero constant $c$ times a character times a Gaussian, times the vacuum of the space of rank zero. At the slice $0$ the character and the Gaussian are $1$, and the vacuum of the space of rank zero has value $1$ at $0$. So the zero term is $c \neq 0$. $\square$

### A model case: the hyperbolic plane

**Example (The Lagrangians of the hyperbolic plane).** Let $S$ be the hyperbolic plane with basis $l, k$, where $l$ and $k$ are isotropic and $l^* J k = 1$. A Lagrangian is an isotropic line. Consider the line of $l + c k$ for $c \in E$. Its vector has
$$(l + ck)^* J (l + ck) = c\, l^* J k + \bar c\, k^* J l = c + \bar c.$$
So the line is isotropic if and only if $\bar c = -c$. Let $\jmath$ be the purely imaginary element of the Weil data, so $\bar \jmath = -\jmath$. Then $\bar c = -c$ if and only if $c = \jmath^{-1}\beta$ with $\beta \in E^+$, because $\jmath c$ is then fixed by the conjugation. A line that is not of this form has no component on $l$, so it is the line of $k$. The Lagrangians are thus the line of $k$ and the lines of $l + \jmath^{-1}\beta k$, $\beta \in E^+$, and these lines are distinct. In the classical language, $P(E)\backslash U(1,1)(E)$ is the projective line over $E^+$, and the point at infinity is the line of $k$. Section 6 proves this in the source and computes each zero term.
