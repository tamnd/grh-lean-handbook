---
title: Existence and Chebotarev
lean:
  - Lib/ClassField/Global/ExistenceTheorem.lean
  - Lib/ClassField/Global/Chebotarev.lean
decls:
  - New.idelesPowAt
  - New.exists_kummer_chars
  - New.QZChar.apply_eq_zero_of_artinMap_eq_one
  - New.exists_comp_artinMap_of_ker_le
  - New.exists_comp_artinMap
  - New.OddPart.IsUnramifiedTorsionHom
  - New.OddPart.exists_detecting_points_hom
  - New.chebotarev
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Existence and Chebotarev

This section treats the two results of the chapter that the rest of the proof uses most: the existence theorem, in the form of a factorisation through the Artin map, and Chebotarev's theorem, in the form of an existence statement for Frobenius elements. It also treats a finite detection lemma for unramified homomorphisms, which is a corollary of the existence theory.

Fix a number field $K$ embedded in $\Omega$ and a group $\Gamma$ with `IsProGalois Γ K Ω`, as in Section 3.

### The textbook existence theorem

Section 2 states the textbook existence theorem. With reciprocity it says that every continuous character of $C_K$ of finite order is $\chi \circ \theta_K$ for a unique character $\chi$ of the Galois group. The source states this form, for finite ideles and for totally complex $K$. Then $K^\times_+ = K^\times$, and the Proposition of Section 2 says that the kernel of the Artin map on finite ideles is the closure of $K^\times$.

### Kummer theory

For a set $S$ of finite places and $n \in \mathbb{N}$, `idelesPowAt S n` is the group of finite ideles whose component at every $v \in S$ is an $n$-th power in $K_v^\times$.
Lean: `New.idelesPowAt` (Lib/ClassField/Global/ExistenceTheorem.lean).

**Lemma (Kummer characters).** Suppose that $\Gamma$ fixes the $n$-th roots of unity in $\Omega$, and let $\zeta$ be the root of unity of order $n$ that the source fixes. There is an additive map $\kappa$ from the $\Gamma$-invariant units of $\Omega$ to the characters $\Gamma \to \mathbb{Z}/n$ with these properties.
1. If $a^n = x$, then $\zeta^{\kappa(x)(g)} = g(a)/a$ for all $g \in \Gamma$.
2. Let $K$ be totally complex, and let $S$ be a finite set of finite places that contains the places over $n$, such that the principal ideles and the ideles that are units off $S$ generate all finite ideles. If a finite idele $a$ has $\kappa(u)(\operatorname{artinMap}(a)) = 0$ for every $S$-unit $u$, then $a$ is a principal idele times an idele that is an $n$-th power at each place of $S$ and a unit off $S$.

Lean: `New.exists_kummer_chars` (Lib/ClassField/Global/ExistenceTheorem.lean).

Part 1 is the textbook Kummer pairing, with $\kappa(x)$ the Kummer character of an $n$-th root of $x$. Part 2 is the global step. Let $E$ be the $S$-units and $G_0$ the group in the conclusion. Each $\kappa(u) \circ \operatorname{artinMap}$ kills $G_0$, by reciprocity. So $u \mapsto \kappa(u) \circ \operatorname{artinMap}$ embeds $E/E^n$ into the characters of the quotient by $G_0$, and the bound $[(\mathbb{A}_{K,f})^\times : G_0] \leq [E : E^n]$ (`New.index_sup_idelesPowAt_le`) shows that it is onto.

**Lemma (Characters killed by n).** Suppose that $\Gamma$ fixes the $n$-th roots of unity, and that $K$ is totally complex. Let $\psi$ be a continuous character of $(\mathbb{A}_{K,f})^\times$ with values in $\mathbb{Q}/\mathbb{Z}$, with $\psi(x) = 0$ for $x \in K^\times$ and $n \psi = 0$. If $\operatorname{artinMap}(a) = 1$, then $\psi(a) = 0$.
Lean: `New.QZChar.apply_eq_zero_of_artinMap_eq_one` (Lib/ClassField/Global/ExistenceTheorem.lean).

*Proof.* Take $S$ large: it contains the places over $n$ and the places where $\psi$ is ramified, and it satisfies the generation condition. The character $\psi$ kills the ideles that are $n$-th powers at $S$ and units off $S$, place by place: at $v \in S$ because $n \psi = 0$, and off $S$ because $\psi$ is unramified there. It also kills $K^\times$. Since $\operatorname{artinMap}(a) = 1$, every Kummer character kills the Artin symbol of $a$. By part 2 of the previous lemma, $a$ lies in the group that $\psi$ kills. $\square$

### The existence theorem

**Lemma (Factorisation).** Let $C$ be a topological group, and let $\theta : (\mathbb{A}_{K,f})^\times \to C$ be a continuous homomorphism whose kernel contains the kernel of $\operatorname{artinMap}$. Then there is a continuous homomorphism $\mu : \Gamma \to C$ such that $\mu(g) = \theta(x)$ whenever the class of $g$ in $\Gamma^{\mathrm{ab}}$ is $\operatorname{artinMap}(x)$.
Lean: `New.exists_comp_artinMap_of_ker_le` (Lib/ClassField/Global/ExistenceTheorem.lean).

*Proof.* The map $\operatorname{artinMap}$ is surjective (Section 7), so $\theta$ factors through it as a homomorphism on $\Gamma^{\mathrm{ab}}$. The finite ideles are $\sigma$-compact and $\operatorname{artinMap}$ is a continuous surjective homomorphism, so by an open mapping theorem it is an open map, hence a quotient map. So the factor is continuous. Compose with $\Gamma \to \Gamma^{\mathrm{ab}}$. $\square$

**Theorem (Existence, totally complex fields).** Let $K$ be totally complex, and let $C$ be a topological group in which points are closed. Let $\theta : (\mathbb{A}_{K,f})^\times \to C$ be a continuous homomorphism with $\theta(x) = 1$ for all $x \in K^\times$. Then there is a continuous homomorphism $\mu : \Gamma \to C$ such that $\mu(g) = \theta(x)$ whenever the class of $g$ in $\Gamma^{\mathrm{ab}}$ is $\operatorname{artinMap}(x)$.
Lean: `New.exists_comp_artinMap` (Lib/ClassField/Global/ExistenceTheorem.lean).

*Proof.* By the factorisation lemma it suffices that $\theta(a) = 1$ when $\operatorname{artinMap}(a) = 1$. The kernel of $\theta$ is closed, since $C$ is $T_1$. Continuous characters with values in $\mathbb{Q}/\mathbb{Z}$ separate a closed subgroup of the finite ideles from a point outside it. So it suffices that each continuous character $\psi$ that vanishes on $K^\times$ vanishes at $a$. The kernel of $\psi$ is open and contains $K^\times$, so it has finite index $n$ (`New.finiteIndex_idele_subgroup_of_isOpen`, Section 3), and $n \psi = 0$. Now induct on the index $d$ of the subgroup of $\Gamma$ that fixes the $n$-th roots of unity. If $d = 1$, the lemma on characters killed by $n$ applies. If $d > 1$, a nonzero character of $\operatorname{Gal}(K(\mu_n)/K)$ cuts out a cyclic extension $L$ of $K$ inside $K(\mu_n)$, over which the index is smaller. By the norm group theorem of Section 7, $a$ is a principal idele times a norm $N_{L/K}(y)$. By induction, $\psi \circ N_{L/K}$ kills the kernel of the Artin map of $L$, so it factors through $\operatorname{Gal}(\Omega/L)$. A study of commutators then gives $\psi(N_{L/K}(y)) = 0$. $\square$

**Remark (Formalization).** The source proves existence only for totally complex $K$. The textbook theorem holds for every number field, and in the finite idele form it reads: a continuous $\theta$ that is trivial on the totally positive elements factors through the Artin map. In the source, the hypothesis enters through the Kummer step, part 2 of the Kummer lemma. There each Kummer character must kill the principal ideles, and the source gets this from `New.abelianLift_artinMap_principalIdele_eq_one`, for characters that kill the complex conjugations. The index bound `New.index_sup_idelesPowAt_le` is also stated for totally complex $K$ only. The applications in Section 1 are over totally complex fields, for example the CM fields of the chapter [CM fields and places](/chapter/cm-fields/).

### Detecting points

The next result is a finite form of the existence theorem. It bounds unramified homomorphisms of $\Gamma$ by the class number.

**Definition (Unramified torsion homomorphism).** Let $S$ be a set of finite places, $m \in \mathbb{N}$, and $B$ an additive group. A map $x : \Gamma \to B$ is an *unramified torsion homomorphism* if it is locally constant, $x(gh) = x(g) + x(h)$, $m \cdot x(g) = 0$ for all $g$, and $x$ vanishes on the inertia group of `placeOver v` for every finite $v \notin S$.
Lean: `New.OddPart.IsUnramifiedTorsionHom` (Lib/ClassField/Global/ExistenceTheorem.lean).

**Theorem (Detecting points).** Let $K$ be totally complex, $S$ a set of finite places and $m \in \mathbb{N}$, such that `idelesPowAt S m` has finite index. Then there are a finite type $\iota$, points $p_i \in \Gamma$ and integers $n_i \geq 2$ for $i \in \iota$, with these properties.
1. The product $\prod_i n_i$ divides $h_K \cdot [(\mathbb{A}_{K,f})^\times : \texttt{idelesPowAt}\ S\ m]$, with $h_K$ the class number.
2. Every unramified torsion homomorphism $x$ has $n_i \cdot x(p_i) = 0$ for all $i$, and $x = 0$ if $x(p_i) = 0$ for all $i$.

Lean: `New.OddPart.exists_detecting_points_hom` (Lib/ClassField/Global/ExistenceTheorem.lean).

*Proof.* Let $A$ be the group generated by the principal ideles and the ideles that are $m$-th powers at $S$ and units off $S$, and let $H = \operatorname{artinMap}(A)$. A count with the class group shows that $[\Gamma^{\mathrm{ab}} : H]$ divides $h_K \cdot [(\mathbb{A}_{K,f})^\times : \texttt{idelesPowAt}\ S\ m]$. So $\Gamma^{\mathrm{ab}}/H$ is finite, and it is a product of cyclic groups of orders $n_i \geq 2$. Let $p_i$ lift a generator of factor $i$. For every homomorphism $f : B \to \mathbb{Q}/\mathbb{Z}$, the character $f \circ x$ kills $H$: by reciprocity (Section 7), since $K$ has no complex conjugations, $f \circ x$ is killed by $m$, and it is unramified off $S$. So $f \circ x$ factors through $\Gamma^{\mathrm{ab}}/H$, and it is determined by its values at the $p_i$. The maps $f$ separate the points of $B$. $\square$

### Chebotarev's theorem

The textbook theorem is the density statement of Section 2. The source proves an existence form for the absolute Galois group.

**Theorem (Chebotarev, existence form).** Let $W$ be a nonempty open subset of $\operatorname{Gal}(\Omega/K)$, and let $S$ be a finite set of finite places of $K$. Then there are a finite place $v \notin S$ such that $q_v$ is a prime number, and a place $A$ of $\Omega$ over $v$, with these properties.
1. Some arithmetic Frobenius $\sigma$ at $A$ for $q_v$ lies in $W$.
2. Every arithmetic Frobenius $\tau$ at $A$ for $q_v$ lies in $W$.

Lean: `New.chebotarev` (Lib/ClassField/Global/Chebotarev.lean).

*Proof.* Take $g \in W$ and an open normal subgroup $U$ with $gU \subseteq W$. Let $H = \langle g \rangle U$ and let $L$ be the fixed field of $H$. Then $H/U$ is a quotient of $\langle g \rangle$, so it is cyclic, and $U$ is the kernel of a character $\chi$ of $H$. By surjectivity (Section 7), some finite idele $a$ of $L$ has $\operatorname{artinMap}_H(a) = g$. The kernel of $\chi \circ \operatorname{artinMap}_H$ is open, and it contains the totally positive elements and the norms from the field cut out by $\chi$. By part (b) of the second inequality (Section 5), $\varpi_w a$ lies in this kernel for infinitely many places $w$ of $L$ with $q_w$ prime. Almost all of them lie over a place of $K$ outside $S$ at which all inertia groups lie in $U$. Take one such $w$ and let $v$ be the place of $K$ below it. Since $q_w$ is prime and is a power of $q_v$, the residue degree is $1$ and $q_v = q_w$. The symbol of $\varpi_w$ is the inverse of a Frobenius $\sigma$, by the geometric convention. So $\chi(\sigma) = \chi(g)$, and $g^{-1} \sigma \in U$, so $\sigma \in gU \subseteq W$. Any other Frobenius at $A$ differs from $\sigma$ by an element of the inertia group, which lies in $U$. So it also lies in $gU \subseteq W$. $\square$

**Remark (Formalization).** The theorem gives no density. It gives one place, and so, by enlarging $S$, infinitely many. It gives places of degree one over $\mathbb{Q}$, since $q_v$ is prime. In $\operatorname{Gal}(\Omega/K)$ the inertia groups are never trivial, so a Frobenius at $A$ is defined only up to inertia. Part 2 says that the whole coset lies in $W$. So a user of the theorem may take any Frobenius at $A$. The source does not state the textbook density, and its proof does not use the nonvanishing of $L$-functions of nonabelian characters. The proof is Deuring's reduction to a cyclic extension (Milne, *Class Field Theory*, VIII 7.4, as the source cites).
