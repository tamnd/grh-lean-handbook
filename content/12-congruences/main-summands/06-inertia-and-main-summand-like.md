---
title: Inertia above the level and main summand like
lean:
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean
decls:
  - New.Selmer.IsMainSummandLike
  - New.Selmer.IsMainSummandLike.eventually_span_eq_top_and_exists_eq_smul_one
  - New.Selmer.norm_pow_sub_pow_eq_one
  - New.Selmer.ellVal_det_sub_one_le_card_mul
  - New.Selmer.not_q₂_dvd_mul_pow_mul
  - New.Selmer.IsInertiaSpectrum
  - New.Selmer.IsInertiaSpectrum.of_conjPlace
  - New.Selmer.exists_isInertiaSpectrum_chosenPlace
  - New.Selmer.exists_inertiaGroup_isInertiaSpectrum
  - New.Selmer.IsRepOfType.exists_map_pow_eq_one_and_ellVal_det_le
  - New.Selmer.IsCommonRootPower
  - New.Selmer.IsLiftSetting.exists_isCommonRootPower_of_isPrimitivePolynomial
  - New.Selmer.IsLiftSetting.exists_isCommonRootPower_of_eq_X_sub_one
  - New.Selmer.IsLiftSetting.exists_isCommonRootPower
  - New.Selmer.IsRepOfType.exists_inertia_isRoot_charpoly
  - New.Selmer.eventually_span_eq_top_and_exists_scalar_of_tame_pair
  - New.Selmer.IsRepOfType.isMainSummandLike
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Inertia above the level and main summand like

This section defines the condition "like a main summand" and proves that a representation of the type of a lift setting, of rank $\#r$ and empty level, satisfies it when its weights are those of a main summand. All the work is at the places above $M = p_0 p_1$. There the inertia acts through roots of unity of controlled order. These roots give three things: a bound on $v_\ell \det(R\gamma - 1)$, a tame pair that generates all matrices, and a scalar of large order.

### The condition

**Definition (Like a main summand).** A representation $R$ of rank $\#n$ is *like a main summand* with twist $1 - t$ and jumps $J$ if:

1. $R$ is conjugate self-dual of twist $1 - t$, empty level and jumps $J$;
2. $(\#n, t, J)$ are main summand weights ([weights, signs and b-places](/chapter/main-summands/#weights-signs-and-b-places));
3. at every $A$ over a place $v \mid M$ prime to $\ell$, there are $\gamma$ in inertia, equal to the tame generator if $v$ is chosen, and $N$ a unit at $A$, such that $R(s^N) = 1$ for $s$ in inertia, and $v_\ell \det(R\gamma - 1)$ and $v_\ell \det(R(\gamma^c)^{-1} - 1)$ are at most $\#n \cdot v_\ell(N_{\mathrm{ch}})$;
4. for all large coefficient rings $\mathcal{O}$, the image of every lattice $u$ in $R$ spans all matrices over $\mathcal{O}$;
5. for all large $\mathcal{O}$ and every lattice $u$, some $g$ with $\varepsilon(g) = p_i^{\#n}$ for some $i$ has $u(g)$ scalar;
6. some $\gamma$ in inertia above $M$, off $\ell$, acts by a scalar $y$ with $|y^{\ell^a j} - 1| = 1$ for all $a$ and $1 \leq j \leq 4\#n + 2$.

Here $N_{\mathrm{ch}}$ is the chosen group order of [cocycles, relations and Selmer lengths](/chapter/main-summands/#cocycles-relations-and-selmer-lengths).

Lean: `New.Selmer.IsMainSummandLike`, `New.Selmer.IsMainSummandLike.eventually_span_eq_top_and_exists_eq_smul_one` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

The second name packs 4 and 5 into one eventual statement. Its proof is the conjunction of the two filters.

**Remark (Formalization).** A coefficient ring is a finite extension of $\mathbb{Z}_\ell$ in $\bar{\mathbb{Q}}_\ell$, and "for all large" is the filter of the order by inclusion. So 4 and 5 hold for every ring that contains some fixed ring.

### Three lemmas on roots of unity

**Lemma.** Let $x \in \bar{\mathbb{Q}}_\ell$ be a root of unity. If $(x^a)^{\ell^u} \neq (x^b)^{\ell^u}$ for all $u$, then $|x^a - x^b| = 1$.

Lean: `New.Selmer.norm_pow_sub_pow_eq_one` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* Write the order of $x$ as $\ell^u k$ with $\ell \nmid k$. Then $(x^a)^{\ell^u}$ and $(x^b)^{\ell^u}$ are distinct $k$-th roots of unity. Their difference divides $k$ in the integers, so it has norm at least $|k| = 1$. It is a multiple of $x^a - x^b$ in the integers, so $|x^a - x^b| \geq 1$. Both are integers, so equality holds. $\square$

**Lemma.** Let $Z$ be a matrix of size $\#r$ killed by $\prod_{y \in \mu}(X - y)$, where each $y \in \mu$ is not $1$ and has $y^{p_i^d - 1} = 1$ for some $1 \leq d \leq D.r$. Then $v_\ell \det(Z - 1) \leq \#r \cdot v_\ell(N_{\mathrm{ch}})$.

Lean: `New.Selmer.ellVal_det_sub_one_le_card_mul` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* Each eigenvalue $x$ of $Z$ is a root of the killing polynomial, so $x \in \mu$. Since $x \neq 1$ and $x^{p_i^d - 1} = 1$, the integer $p_i^d - 1$ is a multiple of $x - 1$, so $v_\ell(x - 1) \leq v_\ell(p_i^d - 1)$. The number $p_i^d - 1$ divides the order of $\mathrm{GL}_d$ over the residue field, so $v_\ell(p_i^d - 1) \leq v_\ell(N_{\mathrm{ch}})$. The determinant $\det(Z - 1)$ is the product of the $x - 1$ over the $\#r$ eigenvalues. $\square$

**Lemma.** Let $1 \leq j \leq m$, $1 \leq t \leq 4D.r + 2$ and $b \in \mathbb{N}$. Then $q_2$ does not divide $j \ell^b t$, where $q_2$ is the order of $\chi_M$ at the chosen places.

Lean: `New.Selmer.not_q₂_dvd_mul_pow_mul` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* One of $2$ and $5$ is a prime $p \neq \ell$, and $p$ divides $18480$, which divides $q_0$. So $p^{s}$ divides $q_2$, with $s$ the tower exponent. If $q_2$ divides $j\ell^b t$, then $p^s$ divides $jt$, since $p \neq \ell$. But $0 < jt \leq m(4D.r + 2) < 2^s \leq p^s$ by the size bounds of the data. $\square$

### The inertia spectrum

**Definition (Inertia spectrum).** Let $l \in \{0, 1\}$, $A$ a place, $t \in \mathbb{N}$ and $s$ in the Galois group. A multiset $\mu$ is an *inertia spectrum* of $s$ at $A$ in rank $\#m$ if it has $\#r + t$ members, each $y \in \mu$ has $y^{p_l^{(\#r)!} - 1} = 1$ and $y^{p_l^d - 1} = 1$ for some $1 \leq d \leq D.r$, and for every $R$ of rank $\#m$ of type $(V, c^{\mathrm{sc}} (X-1)^t)$, the polynomial $\prod_{y \in \mu}(X - y)$ kills $s$ at $A$ and $(s^c)^{-1}$ at the conjugate place $\bar A$.

Lean: `New.Selmer.IsInertiaSpectrum`, `New.Selmer.IsInertiaSpectrum.of_conjPlace` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

The second name says that a spectrum of $(s^c)^{-1}$ at $\bar A$ is a spectrum of $s$ at $A$. This holds because the two clauses swap, and $s \mapsto (s^c)^{-1}$ is an involution.

**Lemma (Spectrum at a chosen place).** Let $(V, c)$ be a lift setting, let $w_i$ divide $p_l$, and let $A$ lie over $w_i$. Every $s$ in inertia at $A$ has an inertia spectrum $\mu$. If $t = 0$ and $s$ is the tame generator, then $1 \notin \mu$.

Lean: `New.Selmer.exists_isInertiaSpectrum_chosenPlace` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* The scaled type polynomial $c_i^{\mathrm{sc}}$ is a label of degree $\#r$, and the residue field has order $q = p_l$. Let $y$ be the tame exponent of $s$ at level $(\#r)!$, prime to $q^{(\#r)!} - 1$ for the tame generator. Let $\mu$ be the images $\iota(T^y(x))$ of the roots $x$ of $c_i^{\mathrm{sc}} (X-1)^t$. There are $\#r + t$ of them. Each root lies in a field of degree $d \leq \#r \leq D.r$ over the residue field, so $x^{q^d - 1} = 1$, and $d$ divides $(\#r)!$. The kill at $A$ is the label condition of $R$. The kill at $\bar A$ is the label condition at the conjugate place, from conjugate self-duality. If $t = 0$ and $s$ is the tame generator, $y$ is prime to the order of each $x$, so $T^y(x) = 1$ forces $x = 1$. But $1$ is not a root of $c_i^{\mathrm{sc}}$. $\square$

**Lemma (Spectrum above the level).** Let $v \mid p_l$ and let $A$ lie over $v$. There is $\gamma$ in inertia at $A$, the tame generator if $v$ is chosen, such that every $s$ in inertia has a spectrum $\mu$, with $1 \notin \mu$ if $t = 0$ and $s = \gamma$.

Lean: `New.Selmer.exists_inertiaGroup_isInertiaSpectrum` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* If $v$ is chosen, this is the lemma before. If not, $\bar v$ is chosen and $\bar A$ lies over $\bar v$. Take $\gamma = (\gamma_{\bar A}^c)^{-1}$ for the tame generator $\gamma_{\bar A}$ of $\bar A$. Apply the lemma at $\bar A$ to $(s^c)^{-1}$ and use the conjugate place lemma. $\square$

**Theorem (Ramification above the level).** Let $(V, c)$ be a lift setting and $R$ of rank $\#r$, of type $(V, c^{\mathrm{sc}})$ and empty level. Then condition 3 of the definition holds for $R$ with $\#n = \#r$.

Lean: `New.Selmer.IsRepOfType.exists_map_pow_eq_one_and_ellVal_det_le` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* Take $\gamma$ from the lemma above with $t = 0$, and $N = p_l^{(\#r)!} - 1$, a unit at $A$. For $s$ in inertia, $R$ is of finite type at $A$, so $R(s)$ has finite order and is diagonalizable. The polynomial of the spectrum kills $R(s)$, so each eigenvalue lies in the spectrum and is an $N$-th root of unity. So $R(s)^N = 1$. The spectrum of $\gamma$ does not contain $1$, so the lemma on determinants bounds $v_\ell \det(R\gamma - 1)$. The same holds for $(\gamma^c)^{-1}$ through the clause at $\bar A$ and the conjugate place. $\square$

### The common root power

**Definition (Common root power).** Let $q$ be the order of the residue field at $w_i$. An element $y$ is a *common root power* for $(i, j, e)$ if every root $\xi$ of $c_i^{\mathrm{sc}}$ has $\xi^e = y$ and $\xi^{q^{\#r}} = \xi$, the powers $(\xi^{q^a})^{\ell^u}$ for $a < \#r$ are distinct for each $u$, and $y^x = 1$ implies $q_2 \mid jx$.

Lean: `New.Selmer.IsCommonRootPower` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

**Lemma (Common root powers exist).** Let $(V, c)$ be a lift setting with $V.\mathrm{tamePart} = \chi_M^j\vartheta.\mathrm{tamePart}$. If $c_i$ is primitive with $\#r = D.r$, or $c_i = X - 1$ with $\#r = 1$, then a common root power exists.

Lean: `New.Selmer.IsLiftSetting.exists_isCommonRootPower_of_isPrimitivePolynomial`, `New.Selmer.IsLiftSetting.exists_isCommonRootPower_of_eq_X_sub_one`, `New.Selmer.IsLiftSetting.exists_isCommonRootPower` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* *Primitive case.* The scaling factor is a root of unity of order dividing $q_2$, and $q_2^2$ divides $q - 1$. So the scaled polynomial stays primitive. Let $y$ be the product of its roots. It is a primitive $(q - 1)$-th root of unity, and each root $\xi$ has $\xi^e = y$ for one $e$. The roots lie in $\mathbb{F}_{q^{\#r}}$. The conjugates $\xi^{q^a}$ stay distinct after an $\ell^u$-th power, since $\xi$ has order $q^{\#r} - 1$ and $9 \mid q - 1$. If $y^x = 1$, then $q - 1 \mid x$, so $q_2 \mid x$. *Case $X - 1$.* The only root is the name $z$ of $\omega^{-j}$, where $\omega$ has order $q_2$. Take $e = 1$ and $y = z$. Then $z^q = z$, and $z^x = 1$ forces $q_2 \mid jx$. The third name joins the two cases. $\square$

### The tame pair and the main result

**Lemma (A tame eigenvalue).** Let $(V, c)$ be a lift setting and $R$ of type $(V, c^{\mathrm{sc}})$, of rank $\#r$ and empty level. Let $A$ lie over $w_i$ and not over $\ell$. There are $s$ in inertia at $A$ and an injective map $\tau = \iota \circ T$ such that every polynomial that vanishes at the $\tau(\eta)$, $\eta$ a root of $c_i^{\mathrm{sc}}$, kills $R(s)$, and some $\tau(\xi)$ is an eigenvalue of $R(s)$ of finite order.

Lean: `New.Selmer.IsRepOfType.exists_inertia_isRoot_charpoly` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* Take $s$ of tame exponent $1$. The label condition gives the kill. Each eigenvalue of $R(s)$ is a root of the killing polynomial, so it is some $\tau(\xi)$. A root of unity of the residue field maps to a root of unity. $\square$

**Lemma (Tame pair).** Let $A$ over $w \mid p_l$ not be over $\ell$, let $R$ of rank $\#r$ be of finite type at $A$ with $R(s^N) = 1$ on inertia, $N$ a unit. Let $s$ in inertia have $R(s^{q^{\#r}}) = R(s)$ and an eigenvalue $\zeta$ of finite order with $|\zeta^{q^a} - \zeta^{q^b}| = 1$ for $a \neq b < \#r$. Then conditions 4 and 5 hold for $R$.

Lean: `New.Selmer.eventually_span_eq_top_and_exists_scalar_of_tame_pair` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* On tame inertia a Frobenius $\varphi$ raises $R(s)$ to its $q$-th power by conjugation. So $R(s)$ has the eigenvalues $\zeta^{q^a}$, $a < \#r$, distinct modulo the maximal ideal. Take $\mathcal{O}$ with $\zeta \in \mathcal{O}$. The eigenlines of $u(s)$ modulo the maximal ideal are permuted cyclically by $u(\varphi)$. So $u(s)$ and $u(\varphi)$ span all matrices, and $u(\varphi^{\#r})$ preserves each eigenline and commutes with them, hence is scalar. Its cyclotomic character is $q^{\#r} = p_l^{\#r}$. $\square$

**Theorem (Representations of a type are like main summands).** Let $(V, c)$ be a lift setting for $\vartheta$, and $R$ of rank $\#r$, of type $(V, c^{\mathrm{sc}})$ with twist $1 - k$, jumps $J$ and empty level. If $(\#r, k, J)$ are main summand weights, then $R$ is like a main summand with twist $1 - k$ and jumps $J$.

Lean: `New.Selmer.IsRepOfType.isMainSummandLike` (New/Congruences/GaloisRepresentations/RowsAndColumnsFromLabels.lean).

*Proof.* Conditions 1 and 2 are the hypotheses. Condition 3 is the theorem on ramification. By condition 5 of a lift setting, take a chosen place $w = w_i$ above some $p_l \neq \ell$ whose label is primitive or $X - 1$. Take $j$ with $V.\mathrm{tamePart} = \chi_M^j\vartheta.\mathrm{tamePart}$, and a common root power $y$ with exponent $e$. Take $s$, $\tau$, $\xi$ from the lemma on a tame eigenvalue. Since $\xi^{q^{\#r}} = \xi$ for each root, $X^{q^{\#r}} - X$ kills $R(s)$, so $R(s^{q^{\#r}}) = R(s)$. The distinct powers and the first root lemma give $|\tau\xi^{q^a} - \tau\xi^{q^b}| = 1$. The tame pair lemma gives 4 and 5. For 6, $X^e - \tau(y)$ kills $R(s)$, so $R(s^e) = \tau(y)$ is scalar. If $(\tau y)^{\ell^{a+u} t} = 1$ for some $u$, then $q_2 \mid j\ell^{a+u}t$, against the lemma on $q_2$, since $t \leq 4\#r + 2 \leq 4D.r + 2$. So the first root lemma gives $|\tau(y)^{\ell^a t} - 1| = 1$. $\square$
