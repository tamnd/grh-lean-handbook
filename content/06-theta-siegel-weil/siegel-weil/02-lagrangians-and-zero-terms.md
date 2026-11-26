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

This section defines the two sides of the formula: the Weil representation of the pair $(S, T)$ and the zero term of each Lagrangian of $S$. It proves that the zero term depends only on the Lagrangian, and it computes how the zero term changes under the parabolic subgroup and under the rational points.

### The pair and its representation

Fix a CM field $E$ with Weil data, as in [Chapter 1](/chapter/weil-representation/). Let $S$ be a hermitian space with a point, of rank $n$ and signs $s$, and let $T$ be one of rank $m$ and signs $t$. Write $G_S$ and $G_T$ for their adelic unitary groups. The space $\mathrm{Hom}(S, T)$ is a hermitian space of rank $mn$, and $\mathcal{S}(\mathrm{Hom}(S, T))$ is its space of integrable coefficients against the vacuum. The representation [`New.pairWeil`](/decl/New.pairWeil/) of $G_S \times G_T$ on this space sends $(g, h)$ to $a(\det h)\, b(\det g)^{-1}\, \omega(x \mapsto h x g^{-1})$, for two characters $a$ and $b$ of the norm one ideles.

**Definition (The split Weil representation).** The representation $\omega$ of this chapter is `pairWeil` with $b = 1$ and $a = \upsilon_1^{\lfloor n/2 \rfloor}$, where $\upsilon_1$ is the splitting character $\upsilon$ restricted to the norm one ideles. In $\omega(g, h)$ the element $g$ is in $G_S$ and $h$ is in $G_T$.

Lean: `New.SiegelWeil.splitWeil`, `New.WeilData.upsilonU1` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/Defs.lean).

**Definition (Complete splitting).** A complete splitting of $S$ into $p$ hyperbolic planes is a [splitting](/decl/New.Space.Splitting/) of $S$ over the space of rank zero with $p$ columns. It consists of two isotropic frames $l$ and $k$, each an $n \times p$ matrix over $E$, with $l^* J k = 1$, so that $S = l E^p \oplus k E^p$. The count of the basis gives $n = 2p$.

Lean: `New.SiegelWeil.CompleteSplitting` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Definition (Lagrangian).** A Lagrangian of $S$ is a subspace $L$ of $E^n$ such that $y \in L$ if and only if $x^* J y = 0$ for every $x \in L$. For a complete splitting $P$, the span of the columns of $P.k$ is a Lagrangian, written $L_P$.

Lean: `New.SiegelWeil.Lagrangian`, `New.SiegelWeil.CompleteSplitting.lagrangian` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Definition (Values in the Schrödinger model).** Let $P$ be a complete splitting of $S$ with $p$ columns. It induces a splitting of $\mathrm{Hom}(S, T)$ over $\mathrm{Hom}(0, T) = 0$ with $mp$ columns. For an adelic $m \times p$ matrix $x$, the value of $f$ at $x$ is
$$f[x] = \theta_0\big(f[x]_P\big) \in \mathbb{C},$$
where $f[x]_P$ is the slice of $f$ at $x$ for the induced splitting and $\theta_0$ is the theta functional of the space of rank zero, which reads a vector as a number. The map $f \mapsto f[x]$ is a bounded functional on $\mathcal{S}(\mathrm{Hom}(S, T))$.

Lean: `New.SiegelWeil.mixedValue`, `New.Space.Splitting.homSource`, `New.Space.Splitting.homSlice` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean).

### Lagrangians come from splittings

**Theorem (Every Lagrangian is split).** For every Lagrangian $L$ of $S$ there are a natural number $r$ and a complete splitting $P$ of $S$ into $r$ hyperbolic planes with $L_P = L$.

Lean: `New.SiegelWeil.Lagrangian.exists_completeSplitting` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* A basis $k$ of $L$ is isotropic, so the splitting theorem `New.Space.exists_splitting` extends it to $S = (lE^r \oplus kE^r) \perp V$. The embedding of $V$ is orthogonal to $k$, so its columns lie in $L^\perp = L$ and are multiples of $k$. Then the Gram matrix of $V$ is $0$, which contradicts its invertibility unless $V = 0$. $\square$

**Definition (The chosen splitting and the zero term).** For each Lagrangian $L$ the source chooses one pair $(r, P_L)$ from the theorem above. The zero term along $L$ is the functional
$$\mathrm{ev}_L(f) = f[0] \quad \text{in the Schrödinger model of } P_L.$$
By `New.Space.Splitting.zeroTerm_apply` of [Chapter 1](/chapter/weil-representation/), $\mathrm{ev}_L(f)$ is the mean of $\theta(\varrho(z) f)$ over the maps $z : S \to T$ that vanish on $L$, adelic modulo rational.

Lean: `New.SiegelWeil.Lagrangian.chosenSplitting`, `New.SiegelWeil.Lagrangian.completeSplitting`, `New.SiegelWeil.Lagrangian.numPlanes`, `New.SiegelWeil.Lagrangian.zeroTerm` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (The zero term depends on the Lagrangian only).** Let $P$ be a complete splitting of $S$. For every $f$,
$$\mathrm{ev}_{L_P}(f) = \theta_0\big(\mathrm{ev}_{P}(f)\big),$$
where $\mathrm{ev}_P$ is the zero term of the splitting of $\mathrm{Hom}(S, T)$ induced by $P$.

Lean: `New.SiegelWeil.zeroTerm_lagrangian_eq_theta`, `New.Space.Splitting.zeroTerm_homSource_congr` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean).

*Proof.* Let $Q$ be the chosen splitting of $L_P$. Then $P.k = Q.k\, c$ for a matrix $c$ and $Q.k^* J P.k = 0$, and both complements have rank zero. By `zeroTerm_homSource_congr` the zero term of a splitting of $\mathrm{Hom}(S, T)$ depends only on these data, so the zero terms of $P$ and $Q$ agree. $\square$

**Remark (Formalization).** The splitting $P_L$ is chosen by `Nonempty.some`. The theorem above shows that the zero term does not depend on the choice. The number $r$ of planes is determined by $L$, since $n = 2r$.

### The action of the rational points

A rational isometry $\gamma \in U(S)(E)$ gives a splitting of $S$ with no planes, whose complement is $S$ itself, embedded by $\gamma$. Call it $D_\gamma$.

**Theorem (Rational isometries).** For $\gamma \in U(S)(E)$ and every $f$, the zero term of the splitting of $\mathrm{Hom}(S, T)$ induced by $D_\gamma$ is $f \mapsto \omega(\gamma^{-1}, 1) f$. For a complete splitting $P$, the Lagrangian of the composite splitting $D_\gamma \circ P$, which is $\gamma L_P$, has
$$\mathrm{ev}_{\gamma L_P}(f) = \mathrm{ev}_{L_P}\big(\omega(\gamma^{-1}, 1) f\big).$$

Lean: `New.SiegelWeil.isometrySplitting`, `New.SiegelWeil.zeroTerm_isometrySplitting`, `New.SiegelWeil.zeroTerm_lagrangian_isometrySplitting_comp` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* The zero term of a splitting with no planes is a mean over one point, so it is the change of variables of the corollary of Weil's invariance in [Chapter 1](/chapter/weil-representation/). The second claim follows, since the zero term of a composite splitting is the composite of the zero terms. $\square$

### Splitting off a part

The induction on the rank splits off a frame. Let $D_1$ be a splitting $S = (lE^r \oplus kE^r) \perp S_1$.

**Theorem (Lagrangians through a frame).** Let $D_1$ be a splitting of $S$ over $S_1$. There is a bijection $\sigma$ from the Lagrangians of $S_1$ to the Lagrangians of $S$ that contain the columns of $D_1.k$, such that
$$\mathrm{ev}_{\sigma(L)}(f) = \mathrm{ev}_L\big(\mathrm{ev}_{D_1}(f)\big)$$
for every Lagrangian $L$ of $S_1$ and every $f$. Here $\mathrm{ev}_{D_1}$ is the zero term $\mathcal{S}(\mathrm{Hom}(S, T)) \to \mathcal{S}(\mathrm{Hom}(S_1, T))$ along the splitting of $\mathrm{Hom}(S, T)$ induced by $D_1$.

Lean: `New.SiegelWeil.exists_lagrangian_equiv_containing`, `New.Space.Splitting.zeroTerm_homSource_comp`, `New.Space.Splitting.comp` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/DualPair/MixedModel.lean; Lib/Weil/MixedModel/IsotropicSplitting.lean).

*Proof.* Send $L_1$ to the Lagrangian of the composite splitting $D_1 \circ P_{L_1}$, whose elements are $D_1.k\, a + \iota w$ with $w \in L_1$. The inverse sends $L$ to its preimage under $\iota$, which is a Lagrangian of $S_1$ because $L$ is spanned by $L \cap \iota S_1$ and the columns of $D_1.k$. The identity of the zero terms is `zeroTerm_homSource_comp`: the zero term of a composite splitting is taken in two stages. $\square$

### The Levi subgroup and the substitution law

For a complete splitting $P$ and $a \in \mathrm{GL}_p(\mathbb{A})$, the Levi element $P.\mathrm{levi}(a, 1)$ acts by $k \mapsto ka$ and $l \mapsto l (a^*)^{-1}$.

**Theorem (The Levi law for the pair).** Let $P$ be a complete splitting of $S$, let $a \in \mathrm{GL}_p(\mathbb{A})$, $h \in G_T$ and $x$ an adelic $m \times p$ matrix. For every $f$,
$$\big(\omega(P.\mathrm{levi}(a, 1), h) f\big)[x] = \chi(\det a)^{-1} \sqrt{|\det a|}^{\,m}\, f[h^{-1} x a],$$
where $\chi$ is the unitary character `New.AutChar.spaceChar 1 m` of the ideles and $|\cdot|$ is the idele norm. In particular $(\omega(1, h) f)[x] = f[h^{-1} x]$.

Lean: `New.SiegelWeil.mixedValue_splitWeil_levi`, `New.SiegelWeil.mixedValue_splitWeil`, `New.AutChar.spaceChar` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is the slice law `New.Space.Splitting.homSlice_levi` for the Levi element, since the complement of $P$ has rank zero. The character $\upsilon_1^{\lfloor n/2 \rfloor}$ of $\det h$ in $\omega$ cancels the character that $h$ gives on the slices, since $\lfloor n/2 \rfloor = p$. This is why $\omega$ carries this twist. $\square$

**Theorem (Theta in the Schrödinger model).** For every $h \in G_T$ and every $f$, the family $\xi \mapsto f[h^{-1}\, x_T^{-1} \xi]$, indexed by the rational $m \times p$ matrices $\xi$, is summable with sum $\theta(\omega(1, h) f)$. Here $x_T$ is the point of $T$, which puts $\xi$ in standard coordinates.

Lean: `New.SiegelWeil.hasSum_mixedValue_theta_splitWeil` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is the theorem on the theta of the slices from [Chapter 1](/chapter/weil-representation/), for the induced splitting of $\mathrm{Hom}(S, T)$, together with the substitution law. $\square$

### The size of the zero terms

**Theorem (The parabolic subgroup scales the zero term).** Let $P$ be a complete splitting of $S$ with frame $k$. Let $g \in G_S$ and $a \in \mathrm{GL}_p(\mathbb{A})$ with $g k = k a$ in adelic coordinates. Then for all $g' \in G_S$ and all $f$,
$$\big\|\mathrm{ev}_{L_P}\big(\omega(g g', 1) f\big)\big\| = \sqrt{|\det a|}^{\,m}\, \big\|\mathrm{ev}_{L_P}\big(\omega(g', 1) f\big)\big\|.$$

Lean: `New.SiegelWeil.norm_zeroTerm_parabolic_mul`, `New.Space.Splitting.ActsOnFrame` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* This is the rule `New.Space.Splitting.homSource_zeroTerm_pairWeil` for elements that keep the frame, applied to $\omega(g', 1) f$; the character $\chi(\det a)^{-1}$ that it gives has norm $1$. $\square$

**Theorem (The vacuum has nonzero zero terms).** Let $P$ be a complete splitting of $S$ and $v$ the vacuum vector of $\mathrm{Hom}(S, T)$. For every $g \in G_S$,
$$0 < \big\|\mathrm{ev}_{L_P}\big(\omega(g, 1) v\big)\big\|.$$

Lean: `New.SiegelWeil.norm_zeroTerm_vacElem_pos`, `New.Space.Splitting.exists_slice_omega_vacElem_of_isEmpty` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Up to a character, every slice of a translate of the vacuum for a splitting with complement of rank zero is a nonzero constant $c$ times a character times a Gaussian. At the slice $0$ this is $c \neq 0$. $\square$

**Example (The Lagrangians of the hyperbolic plane).** Let $S$ be the hyperbolic plane with isotropic basis $l, k$ and $l^* J k = 1$. The line of $l + ck$ is isotropic if and only if $c + \bar c = 0$, that is $c = \jmath^{-1}\beta$ with $\beta \in E^+$, where $\jmath$ is the purely imaginary element of the Weil data. So the Lagrangians are the line of $k$ and the lines of $l + \jmath^{-1}\beta k$, $\beta \in E^+$. Classically, $P(E)\backslash U(1,1)(E)$ is the projective line over $E^+$, with the line of $k$ at infinity. Section 6 computes the zero terms.
