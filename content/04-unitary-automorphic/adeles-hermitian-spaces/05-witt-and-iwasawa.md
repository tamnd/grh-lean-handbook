---
title: Witt's theorem and the Iwasawa decomposition in the source
lean:
  - Lib/Adelic/Witt/WittTheorem.lean
  - Lib/Adelic/Unitary/RationalPoints.lean
  - Lib/Adelic/Witt/IwasawaDecomposition.lean
  - Lib/Weil/MixedModel/IsotropicSplitting.lean
decls:
  - New.quasiReflection
  - New.witt_of_quasiReflection_mem
  - New.witt
  - New.Space.witt
  - New.exists_isUnit_sub_star
  - New.exists_orthonormal_Ô
  - New.exists_unit_star_mul_self_eq
  - New.witt_Ô
  - New.maxCompact
  - New.hyperbolicSpace
  - New.Space.Splitting
  - New.Space.exists_splitting
  - New.Space.Splitting.levi
  - New.Space.Splitting.radicalElement
  - New.Space.Splitting.iwasawa
  - New.Space.Splitting.exists_eq_radicalElement_mul_levi_mul_isAdapted
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Witt's theorem and the Iwasawa decomposition in the source

This section gives the forms of Witt's theorem that the source proves, over a field and over the integral finite adeles, and the Iwasawa decomposition that it deduces from them. Section 3 gave the classical statements. Here the hypotheses are those of the Lean statements.

### Witt's theorem over a field

Let $R$ be a field with an involution $a \mapsto \bar a$. Let $J \in M_n(R)$ be hermitian and invertible, with form $h(u, v) = u^* J v$, and let $U(J)$ be the group of $g$ with $g^* J g = J$.

**Definition (Quasi-reflection).** Let $v \in R^n$ and let $\sigma \in R^\times$ with $\sigma + \bar\sigma = h(v, v)$. The *quasi-reflection* along $v$ with parameter $\sigma$ is the map $x \mapsto x - \sigma^{-1} h(v, x)\, v$. It is in $U(J)$.

Lean: `New.quasiReflection`, `New.quasiReflection_mulVec` (Lib/Adelic/Witt/WittTheorem.lean).

When $h(v, v) \neq 0$ and the characteristic is not $2$, one can take $\sigma = h(v, v)/2$, and the map is the reflection along $v$. The parameter $\sigma$ allows isotropic $v$ too. Then $\sigma$ must be a nonzero element with $\bar\sigma = -\sigma$.

**Theorem (Witt, by quasi-reflections).** Suppose that $R$ has an element $z$ with $z - \bar z \neq 0$. Let $X$, $Y$ be $n \times k$ matrices over $R$ with left inverses and with $X^* J X = Y^* J Y$. Let $H$ be a subgroup of $U(J)$ that contains every quasi-reflection. Then $gX = Y$ for some $g \in H$. In particular $gX = Y$ for some $g \in U(J)$.

Lean: `New.witt_of_quasiReflection_mem`, `New.witt` (Lib/Adelic/Witt/WittTheorem.lean).

*Proof.* Induction on a set $s$ of columns that are already matched by some $g \in H$. Let $j$ be a new column, and write $x = gX_j$ and $y = Y_j$. Then $h(x, x) = h(y, y)$, and $x$ and $y$ have the same products with the matched columns $Y_i$, $i \in s$. If $h(y, y - x) \neq 0$, put $\sigma = h(y, y - x)$. A short computation gives $\sigma + \bar\sigma = h(x - y, x - y)$, and the quasi-reflection along $x - y$ with parameter $\sigma$ sends $x$ to $y$ and fixes the matched columns. If $h(y, y - x) = 0$, first apply a quasi-reflection along a vector $\bar u$ such that $u^\top J$ kills the matched columns but neither $x$ nor $y$. The left inverses give two candidates for $u$, and one of them or their sum serves. The element $z$ gives a parameter $\sigma$ for this vector. After this step the first case applies. $\square$

**Remark (Formalization).** The classical theorem of Section 3 is about isometries between subspaces. The source states it for frames: a frame is a matrix with a left inverse, and the theorem moves one frame to another. Two frames with the same Gram matrix give an isometry between their spans, and conversely. The hypothesis on $z$ says that the involution is not the identity, since $R$ is a field. The proof is that of the classical theorem by reflections, adapted to the case where the vector $x - y$ is isotropic.

**Theorem (Witt for a space).** Let $V = (J, x)$ be a space over a CM field $E$ with a CM type. Let $X$, $Y$ be $n \times m$ matrices over $E$ with left inverses and $X^* J X = Y^* J Y$. Then $gX = Y$ for some $g \in U(J)(E)$.

Lean: `New.Space.witt` (Lib/Adelic/Unitary/RationalPoints.lean), `New.exists_isUnit_sub_star` (Lib/Adelic/Unitary/Defs.lean).

*Proof.* A CM field has an element $z$ with $z - \bar z \neq 0$, since conjugation is not the identity on $E$. The matrix $J$ is hermitian and invertible by Section 4. Apply the previous theorem. $\square$

So Witt's theorem over $E$ needs no condition on roots of unity. The source also has the element $y$ of Section 4 with $y - \bar y = i$, but it uses that element only where $z - \bar z$ must be a unit at the finite places.

### Witt's theorem over the integral finite adeles

The local theory over $\hat{\mathcal{O}}_E$ needs the standing condition in an essential way. It gives an element $z \in \hat{\mathcal{O}}_E$ with $z - \bar z$ a unit at every finite place, namely $y$ with $y - \bar y = i$.

**Theorem (Orthonormal bases over $\hat{\mathcal{O}}_E$).** Let $E$ be a CM field with the standing condition. Let $b \in M_n(\mathbb{A}_{E,f})$ be hermitian and in $\mathrm{GL}_n(\hat{\mathcal{O}}_E)$. Then $k^* b k = 1$ for some $k \in \mathrm{GL}_n(\hat{\mathcal{O}}_E)$.

Lean: `New.exists_orthonormal_Ô` (Lib/Adelic/Witt/WittTheorem.lean).

**Corollary (Units are norms).** Let $E$ be as above. A finite adele $u$ with $\bar u = u$ that is a unit at every finite place is $\bar c c$ for a unit $c$ of $\hat{\mathcal{O}}_E$.

Lean: `New.exists_unit_star_mul_self_eq` (Lib/Adelic/Witt/WittTheorem.lean).

*Proof.* Apply the theorem to the $1 \times 1$ matrix $u$. This gives a unit $k$ with $\bar k u k = 1$. Put $c = k^{-1}$. $\square$

These are the adelic forms, at all finite places at once, of two local facts in the unramified case: a unimodular hermitian lattice has an orthonormal basis, and a unit fixed by conjugation is a norm of a unit (Jacobowitz, Amer. J. Math. 84 (1962)). At a split place both facts hold for any field, since $E_w \times E_{\bar w}$ with the exchange involution has every fixed unit as a norm. The Lean proof works over the profinite ring $\hat{\mathcal{O}}_E$ directly. It finds an orthonormal frame modulo each finite place by the element $z$, and lifts it.

**Theorem (Witt over $\hat{\mathcal{O}}_E$).** Let $E$ be a CM field with the standing condition. Let $X$, $Y$ be $n \times k$ matrices over $\mathbb{A}_{E,f}$ that are primitive over $\hat{\mathcal{O}}_E$, that is, they and some left inverses have entries in $\hat{\mathcal{O}}_E$. If $X^* X = Y^* Y$, then $gX = Y$ for some $g \in K_0$.

Lean: `New.witt_Ô`, `New.IsPrimitiveMatrix` (Lib/Adelic/Witt/WittTheorem.lean).

*Proof.* Over $\hat{\mathcal{O}}_E$ there is an invertible matrix $a$ with $aX = Y$ and $a^* Y = X$. A first candidate has both properties, and a correction term that kills $X$, with an adjoint that kills $Y$, makes it invertible at every finite place by a Smith form argument. Then $a^* a$ is hermitian and invertible over $\hat{\mathcal{O}}_E$, and it fixes $X$. The orthonormal frame $T$ of $a^* a$ can be taken congruent to $1$ modulo $a^* a - 1$, so $T$ fixes $X$ too. The matrix $g = aT$ is unitary, integral and sends $X$ to $Y$. $\square$

**Remark (Formalization).** The theorem is for the standard form $1$ only. This is sufficient for the source: the point $x$ of a space moves its form to the identity at every finite place, so Witt over $\hat{\mathcal{O}}_E$ for the identity form gives Witt for the base lattice of every space. The theorem does not cover lattices that are not unimodular. The source has no theorem for them.

### The Iwasawa decomposition of the source

**Definition (Maximal compact subgroup).** The subgroup $K_\infty K_0$ of $G$ is the product of the groups $U(\mathrm{diag}(s)) \cap U(1)$ at the infinite places and of $K_0$.

Lean: `New.maxCompact` (Lib/Adelic/Witt/IwasawaDecomposition.lean).

At an infinite place, $U(\mathrm{diag}(s)) \cap U(1)$ is $U(p) \times U(q)$ for the numbers $p$ and $q$ of signs $+1$ and $-1$. This is a maximal compact subgroup of $U(p, q)$. The Lean name does not assert that $K_\infty K_0$ is maximal, and the argument uses only that it is compact and that the decomposition below holds.

**Definition (Hyperbolic space).** For a finite set $p$, the *hyperbolic space* of rank $2|p|$ has the Gram matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ in blocks, signs $+1$ on the first copy of $p$ and $-1$ on the second, and a point given by explicit matrices at the infinite and the finite places.

Lean: `New.hyperbolicSpace` (Lib/Weil/MixedModel/IsotropicSplitting.lean).

The finite part of the point uses the chosen unit $\epsilon$ with $\bar\epsilon\epsilon = -1$ of Section 4 and a chosen integral adele of trace $1$. A different choice gives another point of the same matrix.

**Definition (Splitting).** Let $V$ and $V_0$ be spaces and $p$ a finite set. A *splitting* of $V$ over $V_0$ consists of $n \times p$ matrices $k$, $l$ and an $n \times n_0$ matrix $\iota$ over $E$, with
$$k^* J k = 0, \quad l^* J l = 0, \quad l^* J k = 1, \quad \iota^* J \iota = J_0, \quad \iota^* J k = 0, \quad \iota^* J l = 0,$$
and $|n| = |n_0| + 2|p|$.

Lean: `New.Space.Splitting` (Lib/Weil/MixedModel/IsotropicSplitting.lean).

This is a Witt decomposition $V = (lE^p \oplus kE^p) \perp \iota V_0$ in the sense of Section 3, given by frames. The frame $k$ spans a totally isotropic subspace, and its stabilizer is a parabolic subgroup.

**Theorem (Existence of splittings).** Let $E$ carry Weil data, in particular the standing condition. Let $V$ be a space and let $k$ be an $n \times p$ matrix over $E$ with a left inverse and $k^* J k = 0$. Then there are a space $V_0$ and a splitting $D$ of $V$ over $V_0$ with $D.k = k$.

Lean: `New.Space.exists_splitting` (Lib/Adelic/Witt/IwasawaDecomposition.lean).

*Proof.* At an infinite place the columns of $x^{-1}k$ span an isotropic subspace for $\mathrm{diag}(s)$, so each sign occurs at least $|p|$ times in $s$. So $V$ has the signs of the sum of a hyperbolic space of rank $2|p|$ and a standard space with the remaining signs. By Landherr's theorem in the form of Section 6, $V$ is congruent over $E$ to this sum. The sum has an evident splitting, which carries over. Its frame $k'$ has the same Gram matrix $0$ as $k$, so Witt's theorem for a space gives $g$ with $gk' = k$. $\square$

**Definition (Levi and radical elements).** Let $D$ be a splitting of $V$ over $V_0$. The *Levi homomorphism* sends $(m, g_0) \in \mathrm{GL}_p(\mathbb{A}_E) \times G(V_0)$ to the element of $G$ that sends $k$ to $km$, $\iota$ to $\iota g_0$, and $l$ to $l (m^*)^{-1}$, in the coordinates of the point. The *radical element* with adelic parameters $c$ and $b$ fixes $k$, sends $\iota$ to $\iota + k c^* \varepsilon_0$, and sends $l$ to $l - \iota c - k(\tfrac{1}{2} j^{-1}(b + b^*) + \tfrac12 c^* \varepsilon_0 c)$. Here $\varepsilon_0$ is the standard form of $V_0$ and $j$ is the purely imaginary element of the Weil data.

Lean: `New.Space.Splitting.levi`, `New.Space.Splitting.radicalElement` (Lib/Weil/MixedModel/IsotropicSplitting.lean).

**Theorem (Iwasawa decomposition).** Let $D$ be a splitting of $V$ over $V_0$, let $g \in G$, and let $\mathrm{wt}$ be a weight function on $p$. Then there is $\kappa \in K_\infty K_0$ such that $g\kappa$ acts on the frame $k$ by a matrix $b \in \mathrm{GL}_p(\mathbb{A}_E)$ that is block triangular for $\mathrm{wt}$, and
$$g\kappa = D.\mathrm{radicalElement}(c, z) \cdot D.\mathrm{levi}(b, u)$$
for some adelic matrices $c$, $z$ and some $u \in G(V_0)$.

Lean: `New.Space.Splitting.iwasawa`, `New.Space.Splitting.exists_mem_maxCompact_actsOnFrame` (Lib/Adelic/Witt/IwasawaDecomposition.lean).

*Proof.* At each infinite place, take an orthonormal frame adapted to the flag of the weights by Gram-Schmidt, and compare it with the image of $k$ by Witt's theorem inside $U(p) \times U(q)$. At the finite places, take frames that are integral and primitive over $\hat{\mathcal{O}}_E$, and compare them by Witt over $\hat{\mathcal{O}}_E$. Gluing the components gives $\kappa$ with $g\kappa k = kb$. An element that stabilizes the span of $k$ is a radical element times a Levi element. $\square$

**Theorem (Decomposition with an adapted factor).** Let $D$ be a splitting and $g \in G$. Then
$$g = D.\mathrm{radicalElement}(c, b) \cdot D.\mathrm{levi}(a, g_0) \cdot h$$
with $h$ adapted to $D$: the matrix $h^{-1}(l, k, \iota)$, in the coordinates of the point, is orthonormal at every infinite place and integral at the finite places.

Lean: `New.Space.Splitting.exists_eq_radicalElement_mul_levi_mul_isAdapted`, `New.Space.Splitting.IsAdapted` (Lib/Adelic/Witt/IwasawaDecomposition.lean, Lib/Weil/MixedModel/IsotropicSplitting.lean).

**Remark (Formalization).** The classical decomposition $G = P K$ of Section 3 (Tits, PSPM 33 part 1, 3.3.2 and 3.8.1, at the finite places) uses a good maximal compact subgroup at each place. The source proves the decomposition only for the parabolic subgroups that come from a splitting of a space, and only for the compact subgroup $K_\infty K_0$. At a finite place $K_0$ is the stabilizer of a unimodular lattice. Under the standing condition every finite place is unramified by Section 4, so this lattice gives a hyperspecial subgroup, and the decomposition at that place is the classical one. The source proves the decomposition from Witt's theorem and Gram-Schmidt, and does not use Tits. The radical element uses the element $j$ of the Weil data, so the decomposition needs Weil data, which is more than the standing condition.

**Remark (Formalization).** The weight function $\mathrm{wt}$ fixes a flag inside the span of $k$. With $\mathrm{wt} = 0$ the matrix $b$ is any element of $\mathrm{GL}_p(\mathbb{A}_E)$, and the theorem is the decomposition for the maximal parabolic subgroup of $k$. The proof of the second theorem uses the case $\mathrm{wt} = 0$ twice: once for $g$, and once for an adapted element.
