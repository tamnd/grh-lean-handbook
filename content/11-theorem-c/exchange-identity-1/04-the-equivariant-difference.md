---
title: The equivariant difference
lean:
  - Lib/ClassField/HeckeCharacter/SplitTameCharacters.lean
  - Lib/Weil/DualPair/ThetaIntegrals.lean
  - Lib/SiegelWeil/SingularForms/CentreCoefficients.lean
  - New/Determinant/Exchange/EquivariantDifference.lean
decls:
  - New.Exchange.localChar
  - New.Exchange.SplitTameChar.semilocalChar
  - New.Exchange.thetaLarge
  - New.Exchange.thetaSmall
  - New.Exchange.IsEquivariantLift
  - New.Exchange.ReadsAt.pairWeil_localDatum_of_mem_supportedOn
  - New.Exchange.pairWeil_inv_localDatum
  - New.Exchange.thetaLarge_translate_mul
  - New.Exchange.thetaSmall_translate_mul
  - New.Exchange.thetaLarge_mul_of_mem_stdLevel
  - New.Exchange.thetaSmall_mul_of_mem_stdLevel
  - New.Exchange.exists_linear_thetaSmall
  - New.Exchange.exists_linear_thetaLarge
  - New.Exchange.exists_isEquivariantLift_eq_thetaLarge_sub_smul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The equivariant difference

This section writes the difference of the two sides of the exchange identity as one linear map $\mathcal{D}$ of the small datum $\Psi$. The map $\mathcal{D}$ has three laws: its values are automorphic forms, it is equivariant under the group at the ramified places, and it is invariant under the integral points elsewhere. A map with these laws is an *equivariant lift*. The main input is the theorem of Section 3.

### The setting

Let $E$ be a CM field with Weil data, as in [the Weil representation](/chapter/weil-representation/), and let $\upsilon$ be its splitting character. Let $\mathfrak{c}$ be a split tame character of weight $\mu$: a character $\nu$ of $[U(1)]$, tamely ramified exactly at a nonempty finite set $S$ of places, with $S$ disjoint from its conjugate $\bar S$. See [characters and twists](/chapter/fields-places-twists/). Write $F = \prod_{w \in S} E_w$, a semilocal field.

**Definition.** For a Hecke character $\xi$ of $E$ and an integer $k$, the character $\chi_{\xi, k}$ of $F$ is $t \mapsto \xi(t)\, |t|^{k/2}$ on the invertible $t$, with $t$ read as an idele supported on $S$, and $0$ on the other elements. The character $\chi_{\mathfrak{c}} = \chi_{\nu_E, 0}$, where $\nu_E(t) = \nu(t / \bar t)$ is the base change of $\nu$, is the *semilocal character* of $\mathfrak{c}$.

Lean: `New.Exchange.localChar`, `New.Exchange.SplitTameChar.semilocalChar` (Lib/ClassField/HeckeCharacter/SplitTameCharacters.lean).

On the units of $O$ the factor $|t|^{k/2}$ is $1$. So $\chi_{\nu_E, k}$ and $\chi_{\mathfrak{c}}$ agree on $GL_n(O)$ determinants, for every $k$. Both are tame, because $\nu$ is tamely ramified at $S$.

Let $W$ be a hermitian space of rank $n$ and $V$, $V'$ hermitian spaces of ranks $a$ and $b$, with $n = a + b$ through a bijection $\sigma \colon b \sqcup a \to n$, and $n$ even. At a split place $w \in S$, the group $U(W)(E_v)$ is $GL_n(E_w)$ and $U(V)(E_v)$ is $GL_a(E_w)$. Write $g_S$ for the component at $S$ of a point $g$.

**Definition.** For a Schwartz vector $v$ of the real Fock space of $\operatorname{Hom}(W, V)$ and a function $\Phi$ of $a \times n$ matrices over $F$, the *large side* $\Theta_{\mathrm{large}}(v, \Phi)$ is the function on $U(W)(\mathbb{A})$ that integrates over $[U(V)]$ the theta kernel of the datum with $v$ at the infinite places, $\Phi$ at $S$, and the vacuum at the other finite places. Both characters of the Weil representation are $\nu^{-1} \upsilon^{n/2}$, restricted to the norm-one ideles.

For a Schwartz vector $v'$ of the Fock space of $\operatorname{Hom}(W, V')$ and a function $\Psi$ of $n \times b$ matrices over $F$, the *small side* $\Theta_{\mathrm{small}}(v', \Psi)$ is the theta integral over $[U(V')]$ of the datum with $v'$ at the infinite places, $y \mapsto \Psi(y^{\mathsf{T}})$ at the conjugate places $\bar S$, and the vacuum elsewhere. Its characters are $\nu\, \upsilon^{n/2}$ and $\upsilon^{a}$.

Lean: `New.Exchange.thetaLarge` (Lib/Weil/DualPair/ThetaIntegrals.lean), `New.Exchange.thetaSmall` (New/Determinant/Exchange/EquivariantDifference.lean).

The large datum is read at $S$ and the small datum at $\bar S$. At a split place the two components $E_w$ and $E_{\bar w}$ of $E_v$ play the roles of the rows and of the columns of a matrix; this is why $\Psi$ is transposed.

**Definition.** Let $X$ be a hermitian space of rank $m$, and $M$ a space of functions of $m \times b$ matrices over $F$. A linear map $\mathcal{D}$ from these functions to functions on $U(X)(\mathbb{A})$ is an *equivariant lift* on $M$ if:

1. every $\Psi \in M$ is locally constant with compact support in the matrices with a left inverse;
2. for $\Psi \in M$, $\mathcal{D}\Psi$ is continuous and left invariant under $U(X)(E)$;
3. for $\Psi \in M$ and a finite point $g$ supported on $S \cup \bar S$, the function $\Psi_g(y) = \Psi(g_S\, y)$ lies in $M$ and
$$\mathcal{D}\Psi_g(x\, g) = \frac{\mathcal{D}\Psi(x)}{\chi_{\upsilon, 1}(\det g_S)^{b}};$$
4. for $\Psi \in M$, $\mathcal{D}\Psi$ is right invariant under the integral points of level one that are $1$ at $S$.

Lean: `New.Exchange.IsEquivariantLift` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

### The action at the ramified places

The Weil representation acts on the datum at $S$ by matrix multiplication. This is the formula of the mixed model at a split place.

**Lemma.** Let $\pi$ read the components at a set $A$ of places disjoint from its conjugate. Let $\varphi$ be locally constant with compact support, and let $g \in U(W)$ and $h \in U(V)$ be finite points supported on $A \cup \bar A$. Then $(g, h)$ moves the datum $(v, \varphi)$ to the datum $(v, x \mapsto \varphi(h_A^{-1}\, x\, g_A))$, times
$$\frac{\chi_W(\det h_A)}{\chi_V(\det g_A)} \cdot \frac{|\det g_A|^{a/2}}{|\det h_A|^{n/2}},$$
where $\chi_W$ and $\chi_V$ are the characters of the Weil representation.

Lean: `New.Exchange.ReadsAt.pairWeil_localDatum_of_mem_supportedOn` (New/Determinant/Exchange/EquivariantDifference.lean).

The proof is the formula of the Weil representation of [Volume 6](/chapter/weil-representation/) in the model that is split at $A$, with the factor of each place collected into the determinants.

**Lemma.** Let $k \in U(V)$ be finite and supported on $S \cup \bar S$. For $\Phi$ locally constant with compact support in the $x$ with $x^{\mathsf{T}}$ left invertible,
$$k^{-1} \cdot (v, \Phi) = \chi_{\nu_E, n}(\det k_S) \cdot \bigl(v,\ x \mapsto \Phi(k_S\, x)\bigr)$$
in the Weil representation of the large side.

Lean: `New.Exchange.pairWeil_inv_localDatum` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* Apply the previous lemma with $g = 1$ and $h = k^{-1}$. The function becomes $x \mapsto \Phi(k_S\, x)$, and the scalar is $\chi_W(\det k_S)^{-1}\, |\det k_S|^{n/2}$, where $\chi_W$ is the character $\nu^{-1}\upsilon^{n/2}$ of rank $n$, read as a character of the determinant at $S$. As $n$ is even, this character is $\nu_E^{-1}$ at $S$, so the scalar is $\nu_E(\det k_S)\, |\det k_S|^{n/2} = \chi_{\nu_E, n}(\det k_S)$. $\square$

### Translation laws of the two sides

Write $\chi = \chi_{\nu_E, n}$ for the rest of the section.

**Lemma.** Let $(\Phi, \Psi)$ be a same-section pair for $\chi$ and $\sigma$, and let $g \in U(W)$ be finite and supported on $S \cup \bar S$. Then
$$\Theta_{\mathrm{large}}\bigl(v,\ \chi(\det g_S^{-1})\, \Phi(\,\cdot\, g_S^{-1})\bigr)(x\, g) = \frac{\Theta_{\mathrm{large}}(v, \Phi)(x)}{\chi_{\upsilon, 1}(\det g_S)^{b}}.$$
If $y \mapsto \Psi(g_S\, y)$ is locally constant with compact support in the left invertible matrices, then
$$\Theta_{\mathrm{small}}\bigl(v',\ \Psi(g_S\, \cdot\,)\bigr)(x\, g) = \frac{\Theta_{\mathrm{small}}(v', \Psi)(x)}{\chi_{\upsilon, 1}(\det g_S)^{b}}.$$

Lean: `New.Exchange.thetaLarge_translate_mul`, `New.Exchange.thetaSmall_translate_mul` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* The theta integral at $x g$ is the theta integral at $x$ of the datum moved by $(g, 1)$. By the lemma on the action, $(g, 1)$ turns $\Phi(\cdot\, g_S^{-1})$ back into $\Phi$, times the scalar $\chi_V(\det g_S)^{-1} |\det g_S|^{a/2}$ with $\chi_V = \nu_E^{-1} \upsilon^{b}$ at $S$. Multiply by $\chi(\det g_S^{-1}) = \nu_E(\det g_S)^{-1} |\det g_S|^{-n/2}$. The powers of $\nu_E$ cancel, and $a - n = -b$, so the product is $\upsilon(\det g_S)^{-b} |\det g_S|^{-b/2} = \chi_{\upsilon, 1}(\det g_S)^{-b}$. For the small side, the datum is read at $\bar S$, where the component of $g$ is the conjugate inverse transpose of $g_S$. The lemma on the action gives the scalar $\chi_{V'}(\det \bar d^{-1})^{-1} |\det \bar d^{-1}|^{b/2}$ with $d = \det g_S$ and $\chi_{V'} = \upsilon^{b}$ of rank $b$. With $\upsilon(\bar t) = \upsilon(t)^{-1}$ this is again $\chi_{\upsilon, 1}(d)^{-b}$. $\square$

**Lemma.** Let $k$ be an integral point of level one of $U(W)$ that is $1$ at $S$. For $\Phi$ and $\Psi$ locally constant with compact support,
$$\Theta_{\mathrm{large}}(v, \Phi)(x k) = \Theta_{\mathrm{large}}(v, \Phi)(x), \qquad \Theta_{\mathrm{small}}(v', \Psi)(x k) = \Theta_{\mathrm{small}}(v', \Psi)(x).$$

Lean: `New.Exchange.thetaLarge_mul_of_mem_stdLevel`, `New.Exchange.thetaSmall_mul_of_mem_stdLevel` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* Off $S \cup \bar S$ the datum is the vacuum, which the integral points of level one fix, and the characters are unramified there. At $S$ and $\bar S$ the point $k$ is $1$. $\square$

### The large side depends only on the small datum

**Lemma.** For a Schwartz vector $v'$ there is a linear map $T'$ with $T'(\Psi) = \Theta_{\mathrm{small}}(v', \Psi)$ for every $\Psi$ that is locally constant with compact support in the left invertible matrices.

Lean: `New.Exchange.exists_linear_thetaSmall` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* The theta integral is linear on the data whose theta kernel has polynomial growth on $U(W)$, uniformly on $U(V')$. A Schwartz vector at the infinite places and a locally constant datum with compact support at $\bar S$ give such a datum. $\square$

**Theorem.** For a Schwartz vector $v$ there is a linear map $T$ with $T(\Psi) = \Theta_{\mathrm{large}}(v, \Phi)$ for every same-section pair $(\Phi, \Psi)$ for $\chi = \chi_{\nu_E, n}$ and $\sigma$.

Lean: `New.Exchange.exists_linear_thetaLarge` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* Let $\Lambda$ be the linear map that agrees with the theta integral on data of polynomial growth, composed with the linear map $\Phi \mapsto (v, \Phi)$. We check the hypothesis of the theorem of Section 3 on equivariant functionals. Let $h \in GL_a(F)$. At a split place every element of $GL_a(E_w)$ is the component of a point of $U(V)$, so $h = k_S$ for a finite $k \in U(V)$ supported on $S \cup \bar S$. The theta integral is an integral over $[U(V)]$ with an invariant measure, so it does not change if the datum is moved by $(1, k^{-1})$. By the lemma on $k^{-1}$,
$$\Lambda(\Phi) = \Lambda\bigl(k^{-1} \cdot (v, \Phi)\bigr) = \chi(\det h)\, \Lambda\bigl(x \mapsto \Phi(h x)\bigr).$$
This is the hypothesis. The theorem of Section 3 gives $T$ with $T(\Psi) = \Lambda(\Phi)$ for every same-section pair, and $\Lambda(\Phi) = \Theta_{\mathrm{large}}(v, \Phi)$, because $\Phi$ is locally constant with compact support. $\square$

### The difference is an equivariant lift

**Theorem (The equivariant difference).** Let $n$ be even, let $v$ and $v'$ be Schwartz vectors, and let $c \in \mathbb{C}$. There are a space $M$ of functions of $n \times b$ matrices over $F$ and a linear map $\mathcal{D}$ such that:

1. $\mathcal{D}$ is an equivariant lift on $M$;
2. for every locally constant $\Psi$ and every $\Phi$ matched with $\Psi$ for the semilocal character $\chi_{\mathfrak{c}}$ over $O$, we have $\Psi \in M$ and
$$\mathcal{D}\Psi = \Theta_{\mathrm{large}}(v, \Phi) - c\, \Theta_{\mathrm{small}}(v', \Psi).$$

Lean: `New.Exchange.exists_isEquivariantLift_eq_thetaLarge_sub_smul` (New/Determinant/Exchange/EquivariantDifference.lean).

*Proof.* Let $M$ be the space of second members $\Psi$ of same-section pairs $(\Phi, \Psi)$ for $\chi = \chi_{\nu_E, n}$ and $\sigma$, and put $\mathcal{D} = T - c\, T'$. For a same-section pair, $\mathcal{D}\Psi = \Theta_{\mathrm{large}}(v, \Phi) - c\, \Theta_{\mathrm{small}}(v', \Psi)$ by the two lemmas above. We check the laws.

Law 1. The second member of a same-section pair is in $\mathcal{S}$ of the left invertible matrices, by definition.

Law 2. Each theta integral of a datum of polynomial growth is continuous and left invariant under the rational points. So is the difference.

Law 3. Let $g$ be supported on $S \cup \bar S$. By the translation proposition of Section 3, applied with $g_S^{-1}$, the pair $(\chi(\det g_S^{-1})\Phi(\cdot\, g_S^{-1}),\ \Psi(g_S\, \cdot))$ is a same-section pair. So $\Psi_g = \Psi(g_S\, \cdot) \in M$, and $\mathcal{D}\Psi_g$ is the difference of the two translated sides. The two translation laws divide both sides by the same factor $\chi_{\upsilon, 1}(\det g_S)^{b}$.

Law 4. Both sides are invariant under the integral points that are $1$ at $S$.

Matched pairs. Let $\Phi$ and $\Psi$ be matched for $\chi_{\mathfrak{c}}$ over $O$, with $\Psi$ locally constant. For $k \in GL_n(O)$, $\chi(\det k) = \chi_{\mathfrak{c}}(\det k)$, because $|\det k| = 1$. So $\Phi$ and $\Psi$ are matched for $\chi$ too. The character $\chi$ is tame, so the theorem of Section 3 makes $(\Phi, \Psi)$ a same-section pair for $\chi$. Hence $\Psi \in M$, and $\mathcal{D}\Psi$ is the difference of the two sides. $\square$

The theorem hides $\Phi$. The value $\mathcal{D}\Psi$ is defined for every $\Psi \in M$, and the large side enters only through the same-section pairs. Section 5 needs exactly this: it moves $\Psi$ by the group at $S$ and by limits, and it never has to move a matched $\Phi$ along.

**Remark (Formalization).** The space $M$ and the maps $T$, $T'$ come from existence statements. Off the data of polynomial growth the linear map $\Lambda$ is a chosen extension, and its values there are not used. The equivariance factor $\chi_{\upsilon, 1}(\det g_S)^{-b}$ depends only on the rank $b$ of $V'$, and not on $\mathfrak{c}$.
