---
title: A model case
lean:
  - Lib/Adelic/Hecke/Basic.lean
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
decls:
  - New.classAut
  - New.classSum
  - New.Variety.classAut_eq_bot
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A model case: forms on a finite set of classes

This section treats the simplest lattice of automorphic forms: forms with scalar values on a definite unitary group. The target lattice of Section 4 has the same shape, with vector values and with a family of maps in place of one.

### Classes and their stabilisers

Let $E$ be a CM field with maximal totally real subfield $E^+$, and let $U_n$ be the unitary group over $E^+$ of the standard hermitian form $\sum_i x_i \bar x_i$ on $E^n$. This form is definite at every infinite place, so the real points of $U_n$ form a compact group. Let $G_f = U_n(\mathbb{A}_{E^+,f})$ be the group of finite adelic points, let $\Gamma = U_n(E^+)$ be the group of rational points, and let $K \subset G_f$ be an open compact subgroup. The double coset space $\Gamma \backslash G_f / K$ is finite.

**Definition (Stabiliser of a class).** Let $G$ be a group with subgroups $\Gamma$ and $K$, and let $g \in G$. The stabiliser of the class of $g$ is $\Gamma_g = \Gamma \cap g K g^{-1}$.

Lean: `New.classAut` (Lib/Adelic/Hecke/Basic.lean).

The group $\Gamma_g$ is the stabiliser of the coset $gK$ under the left action of $\Gamma$. Its order depends only on the double coset $\Gamma g K$. In the definite case, $\Gamma_g$ is the intersection of a discrete group with a compact group, so it is finite.

**Definition (Class sum).** Let $\Gamma, K$ be subgroups of $G$ with finitely many double cosets, and let $f$ be a function on $G$ with values in a rational vector space. The class sum of $f$ is
$$\sum_{c \in \Gamma \backslash G / K} \frac{f(g_c)}{\# \Gamma_{g_c}},$$
where $g_c$ is a chosen representative of $c$.

Lean: `New.classSum` (Lib/Adelic/Hecke/Basic.lean).

If $f$ is left invariant under $\Gamma$ and right invariant under $K$, the class sum does not depend on the choice of the representatives.

### Forms with scalar values

Let $\chi : K \to \mathbb{C}^\times$ be a character of finite order. A form of level $K$ and character $\chi$ with scalar values is a function $\varphi : G_f \to \mathbb{C}$ with $\varphi(\gamma g k) = \chi(k)\varphi(g)$ for all $\gamma \in \Gamma$, $g \in G_f$ and $k \in K$. Such a form is determined by its values at the representatives $g_c$. If $\chi$ is not trivial on some $g_c^{-1}\Gamma_{g_c} g_c$, the value at $g_c$ is $0$. The inner product is the class sum
$$\langle \varphi, \varphi' \rangle = \sum_c \frac{\overline{\varphi(g_c)}\, \varphi'(g_c)}{\# \Gamma_{g_c}}.$$
The function $g \mapsto \overline{\varphi(g)}\varphi'(g)$ is left $\Gamma$-invariant and right $K$-invariant, since $|\chi(k)| = 1$. So the sum is well defined. It is positive definite.

A form is *integral at* $\iota$ if all its values lie in $\mathcal{O}_\iota$. Let $\varphi$ be integral at $\bar\iota$ and $\varphi'$ integral at $\iota$. Then $\iota(\overline{\varphi(g)}) = \bar\iota(\varphi(g))$ and $\iota(\varphi'(g))$ are integral, so each numerator of the class sum is integral at $\iota$. So $A \langle \varphi, \varphi' \rangle$ is integral at $\iota$ for every integer $A$ that is divisible by all the orders $\#\Gamma_{g_c}$.

**Example.** Suppose that one class $c$ has $\#\Gamma_{g_c} = 2$, and that $\chi$ is trivial. Let $\delta_c$ be the form with value $1$ on the class $c$ and $0$ on the others. It is integral at every $\iota$. Its squared norm is $\langle \delta_c, \delta_c \rangle = 1/2$, which is not integral at the $\iota$ above $2$. So in this case the integral forms are not an integral lattice for the inner product at $\ell = 2$. The cure is to make the level small enough that every stabiliser is trivial.

### Trivial stabilisers

The standard way to make the stabilisers trivial is a congruence condition.

**Lemma (Minkowski's lemma for definite unitary groups).** Let $E$ be a CM field with at least two infinite places. Let $w_i$ be distinct finite places of $E$, finitely many, such that
$$(2n)^{[E:\mathbb{Q}]} < \prod_i q_{w_i},$$
where $q_w$ is the norm of $w$. Let $K$ be a subgroup of $G_f$ whose elements are integral and reduce to $1$ modulo every $w_i$. Then for every $g \in G_f$ the stabiliser $\Gamma \cap g K g^{-1}$ of the coset $gK$ in the rational points of the unitary group of the standard form is trivial.

Lean: `New.Variety.classAut_eq_bot` (Lib/Shimura/HeckeTower/HeckeData.lean).

*Proof.* Let $\gamma \in \Gamma \cap g K g^{-1}$, and put $k = g^{-1}\gamma g \in K$. The trace $t = \operatorname{tr}(\gamma - 1) = \operatorname{tr}\gamma - n$ lies in $E$, since $\gamma$ is rational. It equals $\operatorname{tr}(k - 1)$, and $k$ is integral at every finite place, so $t$ is an algebraic integer of $E$. The matrix $k$ reduces to $1$ modulo each $w_i$, so $t$ lies in every $w_i$, and so in their product. Under each complex embedding $\tau$ of $E$ the matrix $\tau(\gamma)$ is unitary, so its diagonal entries have absolute value at most $1$, and $|\tau(t)| \leq 2n$. If $t \neq 0$, the absolute norm of $t$ is a positive integer at most $(2n)^{[E:\mathbb{Q}]}$, and it is divisible by $\prod_i q_{w_i}$. This contradicts the hypothesis. So $\operatorname{tr}\gamma = n$. Fix one embedding $\tau$ and write $A = \tau(\gamma) - 1$. Since $\tau(\gamma)^*\tau(\gamma) = 1$ and $\operatorname{tr}\tau(\gamma) = n$,
$$\operatorname{tr}(A^* A) = \operatorname{tr}(\tau(\gamma)^*\tau(\gamma)) - \overline{\operatorname{tr}\tau(\gamma)} - \operatorname{tr}\tau(\gamma) + n = n - n - n + n = 0.$$
So $A = 0$ and $\gamma = 1$. $\square$

**Remark (Formalization).** The proof does not use that $\gamma$ has finite order. The source states the last step for any matrix that preserves a positive definite form $H$, with $\operatorname{tr}(H^{-1}A^*HA)$ in place of $\operatorname{tr}(A^*A)$. The hypothesis of at least two infinite places is part of the statement. The data of this book have $f \geq x^{11}$ infinite places ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)), so the hypothesis holds.

With trivial stabilisers all weights are $1$, and the inner product of integral forms is integral at every $\iota$. The coordinates $\varphi \mapsto (\varphi(g_c))_c$ identify the forms of trivial character with $\mathbb{C}^C$, where $C$ is the set of classes, and the Gram matrix in these coordinates is the identity.

### Vector values

The forms of the target lattice take values in a representation $W$ of $\prod_\tau \mathrm{GL}_n(\mathbb{C})$ with a standard basis and a Gram matrix $G_W$ with integer entries. A form is integral at $\iota$ if for every $g$ the vector $g^{-1} \cdot \iota(\varphi(g))$ has integral coordinates. Section 4 shows that the pairing of integral values is still integral. With trivial stabilisers, the values at the representatives are coordinates, and the Gram matrix is the block matrix $1 \otimes G_W$, one block for each class.
