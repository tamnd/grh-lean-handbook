---
title: The level N
lean:
  - New/UpperBound/Divisibility/SetupAtLevel.lean
decls:
  - New.Data.nonInducedPlaces
  - New.Data.star_inducedPlace_mem_nonInducedPlaces
  - New.Data.natCast_mem_of_mem_nonInducedPlaces
  - New.Data.isSplitLevel_nonInducedPlaces
  - New.Data.diagPoint
  - New.Data.diagPointN
  - New.Data.dualPointN
  - New.Data.conjEmbedGL
  - New.Data.formRepAtN
  - New.Data.map_adeleExtension_diagPoint
  - New.Data.directDatum_ne_zero_iff
  - New.Data.directDatum_conj_ne_zero_iff
  - New.Data.atPlaces_conj_mem_mirabolic
  - New.Data.mem_levelX_of_mem_mirabolic
  - New.Data.mem_ramified_of_mem_ramifiedSourceForms
  - New.Data.conjEmbedGL_mem_supportedOn
  - New.Data.conjEmbedGL_mem_levelX
  - New.Data.upOperator_mem_sourceForm
  - New.Data.upIntegralForms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The level N

At the prime $p = N$ the lifts of the chain are glued at the level, and the lift laws of [the objects of the upper bound](/chapter/upper-bound-objects/) undo the gluing. Those laws are stated for an abstract split level $P$ and an abstract representation of $\mathrm{GL}_{n \sqcup \ast}(E_P)$. This section supplies the concrete objects: the split level $\Sigma_N$, the points $\delta_j$ that change the standard lattice to the lattice $L_j$, and the representation of $\mathrm{GL}(E_{\Sigma_N})$ on forms. It then proves that the level $K_j$ is the mirabolic group read in a basis of $L_j$, and it defines the module $\mathcal A'$ whose colength Section 3 bounds.

Throughout this section and the next two, $p = N$ and $\iota_N : \mathbb C \to \mathbb C_N$ is the fixed embedding. Recall that $N \equiv 1$ modulo the cyclotomic conductor ([the data and their sizes](/chapter/data-and-sizes/)). So $N$ splits completely in $E$, and the Frobenius at $N$ is trivial ([the field E at the primes](/chapter/field-at-primes/)). Write $\pi$ for the integer of $K$ with $\pi\bar\pi = N$, and $\Pi_N$ for the set of primes of $E$ that divide $\pi$.

### The places above N

For $\tau \in \Phi$, let $w_\tau$ be the prime of $E$ induced by $\iota_N \circ \tau$ ([marked primes and the valuation of a chain](/chapter/chain-valuation/)).

**Definition (The places $\Sigma_N$).** $\Sigma_N = \{\bar w_\tau : \tau \in \Phi\}$, the set of conjugates of the induced places.

Lean: `New.Data.nonInducedPlaces` (New/UpperBound/Divisibility/SetupAtLevel.lean).

**Lemma.** For each $\tau \in \Phi$, $\bar w_\tau \in \Sigma_N$. Each place of $\Sigma_N$ lies above $N$.

Lean: `New.Data.star_inducedPlace_mem_nonInducedPlaces` (New/UpperBound/Divisibility/SetupAtLevel.lean).

Lean: `New.Data.natCast_mem_of_mem_nonInducedPlaces` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* The first claim is the definition. The place $w_\tau$ lies above $N$, so its conjugate does too. $\square$

**Proposition ($\Sigma_N$ is a split level).** The set $\Sigma_N$ is a split level for $N$ in the sense of [lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n): no place of $\Sigma_N$ has its conjugate in $\Sigma_N$; each $w \in \Sigma_N$ has residue field with $N$ elements and $v_w(N) = 1$; and the places above $N$ are exactly those of $\Sigma_N$ and their conjugates.

Lean: `New.Data.isSplitLevel_nonInducedPlaces` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* The group $\Phi$ acts on the places above $N$, and $w_{\sigma\tau} = \sigma \cdot w_\tau$. So the places $w_\tau$ form one orbit of $\Phi$. A conjugate pair in one orbit would mean $\sigma \cdot w = \bar w$ for some $\sigma \in \Phi$. For a prime above $p$ this needs $(\sigma, -1)$ to be a power of the Frobenius at $p$. At $N$ the Frobenius is trivial, as $N \equiv 1$ modulo the conductor. So $\sigma\cdot w_\tau \ne \bar w_\tau$ for all $\sigma$, $\tau$, and the conjugates $\bar w_\tau$ do not meet the orbit. This is the first claim. As the Frobenius is trivial, each residue field has $N$ elements, and $N$ is unramified in $E$. So $v_w(N) = 1$. Every place above $N$ is $\sigma \cdot w_1$ or its conjugate for some $\sigma \in \Phi$, by the decomposition of primes in $E$ ([the field E at the primes](/chapter/field-at-primes/)). This gives the last claim. $\square$

The choice of the conjugates, not the induced places, matters at Section 4: the embedding $\iota_N \circ \tau$ reads an adele through its component at $\bar w_\tau$ (see the lemma on the image of $\delta$ below).

### The points $\delta_j$

Index the basis of $X_j$ by $n_j \sqcup \{\ast\}$, with last basis vector $e_\ast$. Let $\mathrm{diag}_S(N)$ be the matrix at $\Sigma_N$ that is $\mathrm{diag}(1, \dots, 1, N)$ at the places of $\Sigma_N$ in a set $S$ and $1$ at the other places of $\Sigma_N$.

**Definition (Diagonal points).**

1. $\delta_j(S)$ is the finite adelic point of the unitary group of $X_j$ that is supported above $N$ with component $\mathrm{diag}_S(N)$ at $\Sigma_N$.
2. $\delta_j = \delta_j(\Pi_N)$.
3. $\delta_j^\vee = \delta_j\,\delta_j(\Sigma_N)^{-1}$.

Lean: `New.Data.diagPoint`, `New.Data.diagPointN`, `New.Data.dualPointN` (New/UpperBound/Divisibility/SetupAtLevel.lean).

A point of the unitary group supported above $N$ is fixed by its components at $\Sigma_N$, since the component at $\bar w$ is the conjugate inverse transpose of the component at $w$. The point $\delta_j$ takes the standard lattice to $L_j$, the lattice of integral vectors with last coordinate divisible by $\pi$. The point $\delta_j^\vee$ takes it to the dual lattice $L_j^\vee$.

**Definition (Matrices read in a basis of $L_j$).** For $a \in \mathrm{GL}_{X_j}(E_{\Sigma_N})$ put $c_j(a) = \delta_j\,\epsilon(a)\,\delta_j^{-1}$, where $\epsilon(a)$ is the unitary point supported above $N$ with component $a$ at $\Sigma_N$. Let $\rho_j$ be the representation of $\mathrm{GL}_{X_j}(E_{\Sigma_N})$ on the forms on $X_j$ by right translation by $c_j(a)$.

Lean: `New.Data.conjEmbedGL`, `New.Data.formRepAtN` (New/UpperBound/Divisibility/SetupAtLevel.lean).

So $\rho_j$ is the representation $\pi$ of the lift laws, with $P = \Sigma_N$. The operator $\mathrm{Up}$ of the lift laws, built from $\rho_0$, is the operator $\mathrm{Up}$ of this chapter. It is a sum of right translates with roots of unity as coefficients.

**Lemma (The image of a diagonal point).** For $\tau \in \Phi$, the map $\mathrm{GL}(\mathbb A_{E,f}) \to \mathrm{GL}(\mathbb C_N)$ induced by the weight embedding $\iota_N \circ \tau$ sends $\delta_j(S)$ to the diagonal matrix with entries $1$ at the indices of $n_j$, and last entry $N$ if $\bar w_\tau \in S$ and $1$ otherwise.

Lean: `New.Data.map_adeleExtension_diagPoint` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* The embedding factors through the completion of $E$ at the place it defines. This place is $\bar w_\tau$, which lies in $\Sigma_N$. The component of $\delta_j(S)$ there is $\mathrm{diag}(1, \dots, 1, N)$ if $\bar w_\tau \in S$ and $1$ otherwise. $\square$

### The level is mirabolic in the basis of $L_j$

Recall the level $K_j$ of [source forms](/chapter/upper-bound-objects/): the points of the chosen integral subgroup whose last row is that of $1$ modulo $\pi$. The mirabolic group of the lift laws is the group of integral invertible matrices with last column $e_\ast$ modulo $N$. The *direct datum* is the indicator of this condition on matrices at $\Sigma_N$.

**Lemma (The direct datum).** The direct datum is nonzero at a matrix $M$ at $\Sigma_N$ if and only if, at each $w \in \Sigma_N$, all entries of $M$ are integral and $v_w(M_{b\ast} - [b = \ast]) \ge 1$ for each index $b$.

Lean: `New.Data.directDatum_ne_zero_iff` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* This unfolds the definition, with $v_w(N) = 1$. $\square$

**Lemma (Conjugation by $\delta_j$).** Let $k$ be a finite adelic point of the unitary group of $X_j$. The direct datum is nonzero at the component of $\delta_j^{-1}k\delta_j$ at $\Sigma_N$ if and only if, for each $w \in \Sigma_N$:

1. $k$ is integral at $w$;
2. if $\bar w \mid \pi$, the last row of $k^{-1}$ at $\bar w$ is $e_\ast^{T}$ modulo $\bar w$;
3. if $w \mid \pi$, the last row of $k$ at $w$ is $e_\ast^{T}$ modulo $w$.

Lean: `New.Data.directDatum_conj_ne_zero_iff` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* Let $t_b = N$ if $b = \ast$ and $w \mid \pi$, and $t_b = 1$ otherwise. The entry $(b, c)$ of $\delta_j^{-1}k\delta_j$ at $w$ is $t_b^{-1}k_{bc}t_c$. The last row of $k^{-1}$ at $\bar w$ is the conjugate of the last column of $k$ at $w$, because $k$ is unitary. If $w \nmid \pi$, then $t = 1$, the condition of the direct datum is integrality and the last column condition at $w$, and the second item expresses that last column condition. If $w \mid \pi$, then $\bar w \nmid \pi$ and the second item is empty. The conjugated matrix has entries $k_{ab}$ on the upper block, $N^{-1}k_{\ast b}$ on the last row, $Nk_{a\ast}$ on the last column, and $k_{\ast\ast}$ at the corner. Its integrality and its congruence on the last column are, entry by entry, the integrality of $k$ and the congruence of the last row of $k$ modulo $w$. $\square$

**Theorem (The level in the basis of $L_j$).**

1. For $k \in K_j$, the component of $\delta_j^{-1}k\delta_j$ at $\Sigma_N$ is mirabolic.
2. Let $g$ be supported on $\Sigma_N$ and its conjugates, and let the component of $\delta_j^{-1}g\delta_j$ at $\Sigma_N$ be mirabolic. Then $g \in K_j$.
3. For every $a$, $c_j(a)$ is supported on $\Sigma_N$ and its conjugates. If $a$ is mirabolic, $c_j(a) \in K_j$.

Lean: `New.Data.atPlaces_conj_mem_mirabolic` (New/UpperBound/Divisibility/SetupAtLevel.lean).

Lean: `New.Data.mem_levelX_of_mem_mirabolic` (New/UpperBound/Divisibility/SetupAtLevel.lean).

Lean: `New.Data.conjEmbedGL_mem_supportedOn`, `New.Data.conjEmbedGL_mem_levelX` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* A matrix $a$ is mirabolic exactly if the direct datum is nonzero at $a$ and at $a^{-1}$. For part 1, apply the lemma on conjugation to $k$ and to $k^{-1}$. Both are integral at each $w \in \Sigma_N$, as $k$ lies in the integral subgroup. The last rows of $k$ and $k^{-1}$ are $e_\ast^T$ modulo each prime dividing $\pi$, by the definition of $K_j$. For part 2, the lemma applied to $g$ and $g^{-1}$ gives integrality of $g$ and $g^{-1}$ at $\Sigma_N$, so $g$ is integral at all places, as it is $1$ away from $N$. So $g$ lies in the chosen integral subgroup. The lemma also gives the last row of $g$ modulo each $w \mid \pi$. For part 3, $\delta_j$ and $\epsilon(a)$ are supported above $N$, and part 2 applies to $c_j(a)$. $\square$

**Proposition ($\mathrm{Up}$ keeps source forms).** If $\varphi$ is a source form on $X_0$, so is $\mathrm{Up}\,\varphi$.

Lean: `New.Data.upOperator_mem_sourceForm` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* Let $k \in K_0$ and let $a$ be the component of $\delta_0^{-1}k\delta_0$ at $\Sigma_N$. By part 1 of the theorem, $a$ is mirabolic, and $c_0(a) \in K_0$ by part 3. Put $b = c_0(a)^{-1}k$. Then $b \in K_0$ and $b$ is $1$ at $\Sigma_N$, hence at all places above $N$. A point trivial above $N$ commutes with every point supported above $N$, so right translation by $b$ commutes with $\mathrm{Up}$. As $b$ fixes $\varphi$, it fixes $\mathrm{Up}\,\varphi$. The vector $\varphi$ is fixed by $\rho_0(a')$ for every mirabolic $a'$, by part 3. So $\mathrm{Up}\,\varphi$ is fixed by the mirabolic group, by the lemma on $\mathrm{Up}$ of [lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n). Hence $k = c_0(a)\,b$ fixes $\mathrm{Up}\,\varphi$. $\square$

### Ramified forms

A source form $\varphi$ is *ramified* if, at each $u \mid \pi$, the sum of its right translates by $z_u^i$, $0 \le i < N-1$, is $0$. Here $z_u$ is a chosen integral scalar, $1$ away from $u$ and $\bar u$, whose component at $u$ generates the units of the residue field. This definition and the fact that a ramified $\varphi$ has the form $\psi - z_u\psi$ for a source form $\psi$ are in [short columns and the gain](/chapter/short-columns-gain/) (`New.Data.ramifiedSourceForms`, `New.Data.exists_eq_sub_scalingGenerator`).

**Lemma (Ramified source forms are ramified vectors).** If $\varphi$ is a ramified source form, then $\varphi$ is a ramified vector of $\rho_0$ in the sense of the lift laws.

Lean: `New.Data.mem_ramified_of_mem_ramifiedSourceForms` (New/UpperBound/Divisibility/SetupAtLevel.lean).

*Proof.* Let $w \in \Sigma_N$. One of $w$ and $\bar w$ is a prime $u \mid \pi$, by the split level property. Write $\varphi = \psi - z_u\psi$. The scalar $z_u$ is an integral unit at $w$ and is $1$ modulo $N$ at the other places of $\Sigma_N$. A scalar matrix commutes with $\delta_0$, so $z_u = c_0(x)$ for the scalar $x$ with the components of $z_u$. Hence $\varphi$ lies in the range of $1 - \rho_0(x)$. $\square$

### The module $\mathcal A'$

Write $\mathcal A_\iota$, $\mathcal A^L$ and $\mathcal A^\vee$ for the $\mathcal O_\iota$-modules of source forms integral at the points $1$, $\delta_0$ and $\delta_0^\vee$. Integral at $d$ means $\mathrm{GaugeLe}(d, 1, \varphi)$, so $\mathcal A^L$ is the module of source forms with values integral for $L_0$.

**Definition ($\mathcal A'$).** $\mathcal A'$ is the $\mathcal O_\iota$-module of forms $\varphi$ on $X_0$ such that $\mathrm{Up}^{\varrho+1}\varphi \in \mathcal A^L$.

Lean: `New.Data.upIntegralForms` (New/UpperBound/Divisibility/SetupAtLevel.lean).

Here $\varrho + 1 = m/2$, the number of glued pairs. The module $\mathcal A'$ does not depend on the twist.

**Remark (Formalization).** The module $\mathcal A'$ is a submodule of all forms on $X_0$, not of the source forms. The forms in $\mathcal A'$ need not be source forms; only $\mathrm{Up}^{\varrho+1}\varphi$ is. Section 7 intersects it with $\mathcal A_\iota$ and with the ramified forms, so the difference does not matter. The scalars of all these modules are the ring $\mathcal O_\iota$ of complex numbers that $\iota_N$ sends to $N$-adic integers. The set $\Sigma_N$ is registered as a split level by an instance, so the lift laws apply to it without a further hypothesis.
