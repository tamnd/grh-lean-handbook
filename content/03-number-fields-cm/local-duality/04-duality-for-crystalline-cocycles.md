---
title: Duality for crystalline cocycles
lean:
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/ClassField/LocalDuality/CrystallineDuality.lean
decls:
  - New.Period.crysCocycles
  - New.Period.IsPotentiallyCrystalline
  - New.Selmer.exists_perfect_pairing
  - New.Period.IsPotentiallyCrystalline.index_mul_index_dual
  - New.Period.IsPotentiallyCrystalline.exists_twist_jump_pos
  - New.Period.IsPotentiallyCrystalline.cup_mem_B2_of_jump_pos
  - New.Period.IsPotentiallyCrystalline.card_pairingAnnihilator_mul_card_dvd
  - New.Period.IsCupOrthogonal
  - New.Period.IsPotentiallyCrystalline.relIndex_dvd_of_orthogonal
  - New.Lift.cupOrthogonal
  - New.Lift.dualDefect
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Duality for crystalline cocycles

The divisibility of the last section takes a maximal orthogonal pair as a hypothesis. The source supplies this pair in one case: the reductions modulo $\ell^m$ of the crystalline cocycles of a potentially crystalline lattice and of its dual. This section gives the classical statement, the Bloch-Kato orthogonality, and then the three statements of the source.

### The textbook form

Let $K$ be a finite extension of $\mathbb{Q}_\ell$ of degree $n$, and let $V$ be a de Rham representation of $G_K$ of dimension $d$ over $\mathbb{Q}_\ell$. Bloch and Kato define $H^1_f(K, V)$ as the kernel of $H^1(K, V) \to H^1(K, B_{\mathrm{cris}} \otimes V)$. For a lattice $T \subset V$, $H^1_f(K, T)$ is the preimage of $H^1_f(K, V)$. The classical facts are the following (Bloch and Kato, "L-functions and Tamagawa numbers of motives", in *The Grothendieck Festschrift*, Volume I, Birkhäuser, 1990, §3).

1. *Dimension.* $\dim H^1_f(K, V) = \dim H^0(K, V) + \dim D_{\mathrm{dR}}(V)/\mathrm{Fil}^0$.
2. *Orthogonality.* Under local Tate duality $H^1(K, V) \times H^1(K, V^*(1)) \to \mathbb{Q}_\ell$, the subspaces $H^1_f(K, V)$ and $H^1_f(K, V^*(1))$ are exact annihilators of each other.

The dimensions of $D_{\mathrm{dR}}/\mathrm{Fil}^0$ for $V$ and for $V^*(1)$ add up to $nd$, because the Hodge-Tate weights of $V^*(1)$ are the weights of $V$ moved by $u \mapsto -u-1$, with the sign convention in use. With $\dim B^1(V) = d - \dim H^0(K, V)$, the spaces $Z^1_f$ of crystalline cocycles satisfy

$$\dim Z^1_f(K, V) + \dim Z^1_f(K, V^*(1)) = (2 + n)\, d.$$

This is the cocycle form of the count. It is the analogue in characteristic $0$ of the exponent $2 + d$ of the last section, with the degree $n$ in place of $d$.

### The objects of the source

The source works with a profinite group $\Gamma$ and a map $\Gamma \to G_{\mathbb{Q}_\ell}$ (the structure `OverGp Γ ℓ`, with map `toGp`). The degree $n$ above is the index of the image of `toGp`.

**Definition (Crystalline cocycles).** For a representation $\rho$ of $\Gamma$ on a module $T$, `crysCocycles ρ` is the submodule of the functions $c : \Gamma \to T$ that become coboundaries in $B_{\max} \otimes T$: there is $y \in B_{\max} \otimes T$ with $1 \otimes c(g) = (j(g) \otimes \rho(g))\, y - y$ for all $g$.

Lean: `New.Period.crysCocycles` (Lib/PadicHodge/Crystalline/Basic.lean).

This is the analogue of $Z^1_f$ above for the lattice $T$, defined with $B_{\max}$ in place of $B_{\mathrm{cris}}$. Both rings are in use in the literature, and they define the same crystalline representations.

**Definition (Potentially crystalline).** `IsPotentiallyCrystalline ρ` says that the elements of $B_{\max} \otimes T$ fixed by $j(g) \otimes \rho(g)$ for all $g$ near $1$ span $B_{\max} \otimes T$ over $B_{\max}$.

Lean: `New.Period.IsPotentiallyCrystalline` (Lib/PadicHodge/Crystalline/Basic.lean).

This section uses these notions only through the statements below.

**Lemma (A perfect pairing of lattices).** Let $R$ be a ring that is finite over $\mathbb{Z}_\ell$ in the sense of the class `PadicIntegerRing`, and let $L$ be a lattice over $R$. There is a $\mathbb{Z}_\ell$-linear form $f$ on $R$ such that $(\varphi, x) \mapsto f(\varphi(x))$ is a perfect pairing over $\mathbb{Z}_\ell$ between the $R$-dual of $L$ and $L$.

Lean: `New.Selmer.exists_perfect_pairing` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

This is the only "perfect pairing" in the folder. It is a statement of linear algebra about lattices. It is not local Tate duality.

### The exact count

**Theorem (Sizes of crystalline cocycles).** Let $L$ and $L'$ be potentially crystalline lattices over $\mathbb{Z}_\ell$, and let $b : L' \cong \mathrm{Hom}(L, \mathbb{Z}_\ell)$ satisfy $b(g x, g y) = \chi(g)\, b(x, y)$, where $\chi$ is the cyclotomic character. Let $d$ be the rank of $L$ and $n$ the index of the image of `toGp`. Then for every $m$,

$$[Z_f(L) : \ell^m Z_f(L)] \cdot [Z_f(L') : \ell^m Z_f(L')] = \bigl((\ell^m)^d\bigr)^{2+n}.$$

Lean: `New.Period.IsPotentiallyCrystalline.index_mul_index_dual` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

*Proof.* The source's proof uses two facts. First, the Hodge-Tate jumps of $L'$ are the numbers $-u-1$ for the jumps $u$ of $L$. So the numbers of negative jumps of the two lattices add up to $d$. Second, the rank formula for crystalline cocycles, `crysCocycles.finrank_eq`, expresses the rank of $Z_f$ through the negative jumps. So the two ranks add up to $2d + nd$. For a free module of rank $s$, the index of $\ell^m$ times it is $(\ell^m)^s$. $\square$

The docstring of the source says that the classical route to this count is Bloch-Kato duality together with the Euler characteristic formula, and that neither is used. The theorem states only the product of the two indices. It does not state that the two groups annihilate each other.

### The divisibility for reductions

**Theorem (Local duality for potentially crystalline lattices).** Let `toGp` be an open embedding of $\Gamma$ into $G_{\mathbb{Q}_\ell}$, and let $L, L'$ and $b$ be as above. Let $q : L \to V$ present $V = L/\ell^m L$ as a finite $\Gamma$-module, and let $r$ identify $L'/\ell^m L'$ with the Cartier dual of $V$ through the reduction of $b$. For every group $Y$ of cocycles in $Z^1(V^\vee)$, with annihilator $Y^\perp$ under the cup product,

$$\#Y^\perp \cdot \#Y \;\Big|\; \#V^{2+n}.$$

Lean: `New.Period.IsPotentiallyCrystalline.card_pairingAnnihilator_mul_card_dvd` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

The statement writes $\#V^{2+n}$ as $((\ell^m)^d)^{2+n}$. It also takes an instance `IsLocalGalois` for the fixed field of the image of `toGp`. This instance follows from the open embedding.

*Proof.* The source's proof has four steps.

1. An open normal subgroup $Q$ fixes $V$. Take an open subgroup $U$ whose image in $\Gamma/Q$ is a Sylow $\ell$-subgroup. Its index is prime to $\ell$, so prime to $\#V$, and every element of $U$ acts on $V$ with $\ell$-power order.
2. Replace $L$ and $L'$ by Tate twists with the same reductions, such that all Hodge-Tate jumps of the twist of $L'$ over $U$ are positive (`New.Period.IsPotentiallyCrystalline.exists_twist_jump_pos`).
3. Over $U$, the reductions $Z$ and $Z'$ of the crystalline cocycles of the twists are orthogonal. The cup product of two crystalline cocycles is a 2-coboundary when the jumps are positive (`New.Period.IsPotentiallyCrystalline.cup_mem_B2_of_jump_pos`).
4. The sizes satisfy $\#Z \cdot \#Z' = \#V^{2+n}$, by the exact count above. By the inequality of local duality over $U$ (`New.card_mul_card_le_of_orthogonal`), no orthogonal pair over $U$ is larger. This is the hypothesis `h_max`. Then `New.DiscreteModule.local_duality_card_dvd` gives the divisibility over $\Gamma$. $\square$

So in this case the source does prove the maximal pair that the divisibility needs. It proves it from the inequality and from the exact count of crystalline cocycles. Neither of these is a perfect duality.

The two lemmas of steps 2 and 3 are the following.

**Lemma (Twists with positive jumps).** Under the hypotheses above, there are potentially crystalline actions $\sigma, \sigma'$ of $\Gamma$ on $L, L'$ for which $b$ satisfies the same twisted identity and $q$ is still equivariant, such that every Hodge-Tate jump of $\sigma'$ restricted to $U$ with nonzero multiplicity is positive.

Lean: `New.Period.IsPotentiallyCrystalline.exists_twist_jump_pos` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

**Lemma (Cup products of crystalline cocycles).** If the jumps are positive in the sense of the previous lemma, then the cup product, through $b$ modulo $\ell^m$, of the reduction of a crystalline cocycle of $L$ and a crystalline cocycle of $L'$ is a 2-coboundary.

Lean: `New.Period.IsPotentiallyCrystalline.cup_mem_B2_of_jump_pos` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

### One divisibility of Bloch-Kato

**Definition (Cup orthogonal).** For a reduction $q : L \to V$ and a group $H$ of maps $\Gamma \to L'$, a map $s : \Gamma \to V$ is *cup orthogonal* to $H$ if $s$ is a continuous cocycle and some lift $a$ of $s$ to $L$ has cup product with every $c \in H$, through $b$ modulo $\ell^m$, in $B^2$.

Lean: `New.Period.IsCupOrthogonal` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

**Theorem (One divisibility in Bloch-Kato duality).** Let `toGp` be an open embedding, and let $L, L', b, q$ be as above. Let $A$ be the image under $q$ of $Z_f(L)$. Let $H$ be a group of maps $\Gamma \to L'$ and $S$ a group of maps $\Gamma \to V$. If every element of $A$ and every element of $S$ is cup orthogonal to $H$, then

$$[S : S \cap A] \;\Big|\; [Z_f(L') : H \cap Z_f(L')].$$

Lean: `New.Period.IsPotentiallyCrystalline.relIndex_dvd_of_orthogonal` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

The classical reading is as follows. If $H$ is large in $Z_f(L')$, then few cocycles orthogonal to $H$ lie outside the crystalline ones. In the limit where $H = Z_f(L')$, the right side is $1$, and every cocycle orthogonal to all crystalline cocycles of $L'$ is crystalline. This is one inclusion of the exact orthogonality in fact 2, for the reductions modulo $\ell^m$.

The file also defines, for later volumes, classes of lattices (`New.Lift.InClass`), the functions whose cup products with all crystalline cocycles of a class are coboundaries, and the defect between these and the crystalline cocycles.

**Definition (Cup orthogonal functions).** For a property $\mathcal{Q}$ of lattices and a lattice $L$, `cupOrthogonal 𝒬 L` is the set of functions $\Gamma \to L$ whose cup products with the crystalline cocycles of the lattices with $\mathcal{Q}$ are coboundaries.

Lean: `New.Lift.cupOrthogonal` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

**Definition (Dual defect).** `dualDefect 𝒬 L` is the length of the crystalline cocycles of $L$ modulo those in `cupOrthogonal 𝒬 L`.

Lean: `New.Lift.dualDefect` (Lib/ClassField/LocalDuality/CrystallineDuality.lean).

**Remark (Formalization).** The source proves an exact count of crystalline cocycles from Hodge-Tate jumps and a rank formula, not from Bloch-Kato duality. It then combines this count with the inequality of local duality to produce the maximal pair `h_max` over an open subgroup of index prime to $\ell$. The conclusion is a divisibility over $\Gamma$, and one divisibility of indices in the place of the Bloch-Kato orthogonality. The source does not prove that $H^1_f(V)$ and $H^1_f(V^*(1))$ are exact annihilators. The cited sources in the file are Serre, *Galois Cohomology*, II.5.2 and II.5.7, and Milne, *ADT*, I.2.3 and I.2.8.
