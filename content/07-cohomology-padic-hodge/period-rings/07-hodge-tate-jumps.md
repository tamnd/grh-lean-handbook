---
title: Hodge-Tate jumps
lean:
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/PadicHodge/Crystalline/HodgeTateForms.lean
  - Lib/PadicHodge/Crystalline/HodgeTateJumps.lean
decls:
  - New.HasHodgeTateWeight
  - New.Period.hodgeTateMaps
  - New.Period.jump
  - New.Period.HasJumps
  - New.Period.hodgeTateMaps.mem_span_same_weight
  - New.Period.finite_hodgeTateMaps
  - New.Period.hasJumps_of_basis
  - New.Period.hodgeMatrix
  - New.Period.IsHodgeTateFrame
  - New.Period.exists_isHodgeFrame
  - New.Period.IsPotentiallyCrystalline.exists_isHodgeTateFrame
  - New.Period.IsPotentiallyCrystalline.exists_hasJumps
  - New.Period.hasJumps_of_cyclotomicGp_zpow
  - New.Period.jump_twist_cyclotomicGp
  - New.Period.jump_eq_of_pairing
  - New.Period.exists_jump_bound
  - New.Period.exists_jump_of_jointly_injective
  - New.Period.IsPotentiallyCrystalline.sum_jump_eq_jump_overZp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hodge-Tate jumps

This section defines the Hodge-Tate weights, which the source calls *jumps*, and proves that a potentially crystalline representation of rank $d$ has $d$ jumps with multiplicity at each embedding. It computes the jumps of twists, duals, subobjects and restrictions of scalars. The source cites O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), Section 6.3.

### The classical notion

Let $V$ be a finite-dimensional continuous $\mathbb{Q}_p$-representation of $G_K$, and let $\mathbb{C}_p(i)$ be $\mathbb{C}_p$ with $g$ acting by $\chi(g)^i g$. The representation $V$ is *Hodge-Tate* if $\mathbb{C}_p \otimes_{\mathbb{Q}_p} V$ is a finite direct sum of the $\mathbb{C}_p(i)$, as a semilinear representation. The multiplicity of $\mathbb{C}_p(i)$ is $\dim_K (\mathbb{C}_p(-i) \otimes V)^{G_K}$, which is well defined by the theorem of Tate. The integers $i$ that occur are the Hodge-Tate weights, with two sign conventions in the literature.

### Forms of weight u

The source does not decompose $\mathbb{C}_p \otimes V$. It counts linear forms. Let $R$ be a $\mathbb{Z}_p$-algebra, $T$ an $R$-module with an action $\rho$ of $\Gamma$, and $\gamma : R \to \mathbb{C}_p$ a $\mathbb{Z}_p$-algebra map.

**Definition (Forms of weight u, jumps).** For $u \in \mathbb{Z}$, $H_u(\rho, \gamma)$ is the $\overline{\mathbb{Q}}_p$-vector space of $\gamma$-semilinear maps $f : T \to \mathbb{C}_p$ such that, for every $x \in T$,
$$f(\rho(g)x) = \chi(g)^{-u}\, j(g)\bigl(f(x)\bigr) \quad \text{for all } g \text{ near } 1.$$
The *multiplicity of the jump* $u$ is $\mathrm{jump}(\rho, \gamma, u) = \dim_{\overline{\mathbb{Q}}_p} H_u(\rho, \gamma)$. A multiset $J$ of integers *lists the jumps* of $\rho$ at $\gamma$ if $\mathrm{jump}(\rho, \gamma, u)$ is the multiplicity of $u$ in $J$ for every $u$.

Lean: `New.Period.hodgeTateMaps` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.jump`, `New.Period.HasJumps`.

The space is a $\overline{\mathbb{Q}}_p$-space and not a $\mathbb{C}_p$-space: $cf$ has weight $u$ only if $c$ is fixed near $1$. The condition "near $1$" makes the notion a potential one.

The source also has a pointwise notion. An element $y \in \mathbb{C}_p \otimes_{\mathbb{Z}_p} T$ *has Hodge-Tate weight* $u$ if $(j(g) \otimes \rho(g))\,y = \chi(g)^{-u} y$ for all $g \in \Gamma$.

Lean: `New.HasHodgeTateWeight` (Lib/PadicHodge/Crystalline/Basic.lean).

This notion is used in the files `PadicComparison/HodgeTate/PeriodMap.lean` and `Shimura/Eigenspace.lean` of the source, for classes in étale cohomology. The jumps of this section are defined through $H_u$ only.

**Example.** Let $T = \mathbb{Z}_p(1)$ and $R = \mathbb{Z}_p$. A linear map $T \to \mathbb{C}_p$ is $f_y(x) = xy$, and the condition reads $\chi(g)^{1+u} g(y) = y$ for $g$ near $1$. For $u = -1$, $y \in \overline{\mathbb{Q}}_p$ by Ax-Sen-Tate, so $H_{-1}$ has dimension $1$. For $u \neq -1$, $y = 0$ by Tate. So $\mathbb{Z}_p(1)$ has the single jump $-1$.

**Remark (Formalization).** Three points of the definition need care.

1. *Sign.* The weight $u$ enters as $\chi^{-u}$, and the space consists of forms on $T$, not of vectors in $\mathbb{C}_p \otimes T$. With these two choices, $\mathbb{Z}_p(1)$ has the jump $-1$, as the example shows, and $\chi^c$ has the jump $-c$ (`hasJumps_of_cyclotomicGp_zpow` below gives the multiset with $-c$ repeated). A reader who compares with a text in which $\mathbb{Q}_p(1)$ has weight $1$ must change the sign.
2. *Junk value.* `New.Period.jump` is `Module.finrank`, which is $0$ for an infinite-dimensional space. So a jump of multiplicity $0$ can mean "no form" or "infinitely many independent forms". For $T$ finite over $R$, the instance `New.Period.finite_hodgeTateMaps` below shows that the space is finite-dimensional, and then the value is the true dimension. Every theorem below that counts jumps has $T$ finite.
3. *No continuity.* The forms are not required to be continuous, and $\rho$ is not required to be continuous. For $T$ finite over $R$ this has no effect on the count, since the theorems below find the forms explicitly.

### Finiteness

**Theorem (Same weight).** Let $T$ be finite over $R$. Let $f_i \in H_{k_i}(\rho, \gamma)$ for a family of forms, and let $\phi \in H_u(\rho, \gamma)$ lie in the $\mathbb{C}_p$-span of the $f_i$. Then $\phi$ lies in the $\overline{\mathbb{Q}}_p$-span of the $f_i$ with $k_i = u$.

Lean: `New.Period.hodgeTateMaps.mem_span_same_weight` (Lib/PadicHodge/Crystalline/HodgeTateForms.lean).

*Proof.* Choose a $\mathbb{C}_p$-linearly independent subfamily $f_{a(1)}, \ldots, f_{a(r)}$ with the same span, and write $\phi = \sum_i c_i f_{a(i)}$. Evaluate $\phi$ at $\rho(g)x$ for $g$ near $1$ in two ways, once with the weight $u$ of $\phi$ and once with the weights $k_{a(i)}$ of the $f_{a(i)}$. Since $\rho(g)$ is onto and the $f_{a(i)}$ are independent, the coefficients agree:
$$\chi(g)^{k_{a(i)} - u}\, g(c_i) = c_i \quad \text{for } g \text{ near } 1.$$
If $k_{a(i)} = u$, then $c_i$ is fixed near $1$, so $c_i \in \overline{\mathbb{Q}}_p$ by Ax-Sen-Tate. If $k_{a(i)} \neq u$, then $c_i = 0$ by Tate's theorem on twists. $\square$

**Theorem (Finiteness).** If $T$ is finite over $R$, then $H_u(\rho, \gamma)$ is finite-dimensional over $\overline{\mathbb{Q}}_p$ for every $u$.

Lean: `New.Period.finite_hodgeTateMaps` (Lib/PadicHodge/Crystalline/HodgeTateForms.lean).

*Proof.* The $\gamma$-semilinear maps $T \to \mathbb{C}_p$ form a finite-dimensional $\mathbb{C}_p$-space, so finitely many elements of $H_u$ span the same $\mathbb{C}_p$-space. By the previous theorem, they span $H_u$ over $\overline{\mathbb{Q}}_p$. $\square$

**Theorem (Jumps from a basis).** Let $T$ be finite over $R$. If a $\mathbb{C}_p$-basis $(b_i)_{i \in \iota}$ of the $\gamma$-semilinear maps $T \to \mathbb{C}_p$ has $b_i \in H_{u_i}$ for each $i$, then the multiset $\{u_i\}$ lists the jumps of $\rho$ at $\gamma$.

Lean: `New.Period.hasJumps_of_basis` (Lib/PadicHodge/Crystalline/HodgeTateForms.lean).

The proof is the theorem on same weights: $H_v$ is the $\overline{\mathbb{Q}}_p$-span of the $b_i$ with $u_i = v$, and these are independent.

### Hodge frames

The existence of jumps for a potentially crystalline representation is the statement that potentially crystalline implies Hodge-Tate. The source proves it with matrices over $B_{\mathrm{dR}}$.

**Definition (Hodge matrix, Hodge-Tate frame).** Let $\iota$ be a finite set.

1. For a matrix $W$ over $B_{\mathrm{dR}}^+$ and $k : \iota \to \mathbb{Z}$, the *Hodge matrix* is $W \cdot \mathrm{diag}(t^{k_i})$, a matrix over $B_{\mathrm{dR}}$.
2. For matrices $N$ and $P$ over $\mathbb{C}_p$ and $g \in G_p$, the matrix $P$ is a *Hodge-Tate frame* of weights $k$ for $N$ at $g$ if $N \cdot g(P_j) = \chi(g)^{-k_j} P_j$ for every column $P_j$ of $P$.

Lean: `New.Period.hodgeMatrix` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.IsHodgeTateFrame`.

**Theorem (Hodge frames over B_dR).** Let $\mathrm{nearOne} \leq F$, and let $N(g)$ be matrices over a ring $A$ that maps compatibly to $\overline{\mathbb{Q}}_p$ and to $B_{\mathrm{dR}}$. Let $U$ be an invertible matrix over $B_{\mathrm{dR}}$ with $N(g) \cdot j(g)(U) = U$ for $F$-almost all $g$. Then there is a matrix $Y$ of determinant $1$ over $\overline{\mathbb{Q}}_p$ such that $U Y = W \cdot \mathrm{diag}(t^{k_i})$ with $W$ invertible over $B_{\mathrm{dR}}^+$ and $k : \iota \to \mathbb{Z}$, and $Y$ has integral entries, is fixed near $1$, and has the further properties that the source collects in `IsHodgeFrame`.

Lean: `New.Period.exists_isHodgeFrame` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.IsHodgeFrame`.

The proof is a minimality argument. Among the factorizations $UY = W \cdot \mathrm{diag}(t^{k_i})$, which exist by `exists_eq_hodgeMatrix`, take one with $\det W$ minimal for divisibility. If $W$ is not invertible, the elimination theorem of Section 3 (`le_of_hodgeTate_stable`) gives an algebraic fixed vector $a$ in the kernel of $\theta(W)$ with some $a_i = 1$. Then $Wa = tV$, and changing column $i$ and $k_i$ divides $\det W$ by $t$, which contradicts minimality. Classically this is the existence of a basis adapted to the filtration (Brinon-Conrad, Section 6.3).

**Theorem (Hodge-Tate frames).** Let $R$ be algebraic over $\mathbb{Z}_p$, let $e$ be a finite $R$-basis of $T$, let $\rho$ be potentially crystalline, and let $\gamma : R \to \mathbb{C}_p$. There are an invertible matrix $P$ over $\mathbb{C}_p$ and $k : \iota \to \mathbb{Z}$ with:

1. near $1$, $P$ is a Hodge-Tate frame of weights $k$ for the matrix of $\rho(g)$ in $e$, read through $\gamma$;
2. the multiset $\{k_i\}$ lists the jumps of $\rho$ at $\gamma$;
3. the semilinear forms whose values on $e$ are the rows of $P^{-1}$ form a $\mathbb{C}_p$-basis, the $i$-th of weight $k_i$.

Lean: `New.Period.IsPotentiallyCrystalline.exists_isHodgeTateFrame` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.IsPotentiallyCrystalline.top_le_span_fixed`, `New.Period.hasJumps_of_rows`.

*Proof.* The fixed periods of $\rho$ map to vectors in $B_{\mathrm{dR}}^\iota$ fixed near $1$ that span: this is "potentially crystalline implies potentially de Rham" in coordinates. Choose an invertible matrix $U$ of them, take its Hodge frame $UY = W \cdot \mathrm{diag}(t^{k_i})$, and put $P = \theta(W)$. Reduction modulo $t$ gives the frame property, and the theorem on jumps from a basis gives 2. $\square$

**Theorem (Number of jumps).** Let $R$ be algebraic over $\mathbb{Z}_p$, let $T$ be finite and free over $R$, and let $\rho$ be potentially crystalline. Then for every $\gamma : R \to \mathbb{C}_p$ there is a multiset $J$ with $|J| = \operatorname{rank}_R T$ that lists the jumps of $\rho$ at $\gamma$.

Lean: `New.Period.IsPotentiallyCrystalline.exists_hasJumps` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean).

Classically, this says that a potentially crystalline representation is Hodge-Tate, with $\dim V$ weights counted with multiplicity.

**Remark (Formalization).** The hypothesis "algebraic over $\mathbb{Z}_p$" covers $R = \mathbb{Z}_p$, finite extensions $E$ of $\mathbb{Q}_p$, their rings of integers, and $\overline{\mathbb{Q}}_p$. It is used to factor $\gamma$ through $\overline{\mathbb{Q}}_p$. The jumps are defined for each $\gamma$ separately. For $R = E$, there are $[E : \mathbb{Q}_p]$ maps $\gamma$, and each has its own multiset.

### Operations on jumps

**Theorem (Twists and characters).** Let $c \in \mathbb{Z}$.

1. If $\rho'(g) = \chi(g)^c\rho(g)$, then $\mathrm{jump}(\rho', \gamma, u - c) = \mathrm{jump}(\rho, \gamma, u)$ for all $u$.
2. If $R$ is algebraic over $\mathbb{Z}_p$, $T$ is finite and free over $R$, and $\rho(g)x = \chi(g)^c x$ for all $g$ and $x$, then the jumps of $\rho$ at $\gamma$ are $-c$ with multiplicity $\operatorname{rank}_R T$.

Lean: `New.Period.jump_twist_cyclotomicGp` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.hasJumps_of_cyclotomicGp_zpow`, `New.Period.jump_twist_of_period`.

The first claim needs no hypotheses: multiplication of a form by $\chi(g)^c$ is built into the condition. The source proves a more general rule (`jump_twist_of_period`): if $\rho' = a\rho$ for scalars $a(g) \in R$, and a nonzero $y \in \mathbb{C}_p$ satisfies $\gamma(a(g))\,y = \chi(g)^{-v} g(y)$ near $1$, then $f \mapsto yf$ maps $H_u(\rho)$ onto $H_{u+v}(\rho')$.

**Theorem (Duals).** Let $R$ be algebraic over $\mathbb{Z}_p$, $T$ finite and free over $R$ and $\rho$ potentially crystalline. Let $b : T' \cong \mathrm{Hom}_R(T, R)$ with $b(\sigma(g)x)(\rho(g)y) = \chi(g)^c\,b(x)(y)$. Then $\mathrm{jump}(\sigma, \gamma, u) = \mathrm{jump}(\rho, \gamma, -u-c)$.

Lean: `New.Period.jump_eq_of_pairing` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean).

The proof uses the Hodge-Tate frame $P$ of $\rho$ and the transpose of $P$ as a frame for the dual basis.

**Theorem (Bounds).** If $T$ is finite over $R$, there is $a \geq 0$ such that every jump $k$ of $\rho$ at $\gamma$ with nonzero multiplicity satisfies $-a \leq k \leq a$. The multiplicity of $u$ is $0$ exactly when $H_u = 0$.

Lean: `New.Period.exists_jump_bound` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.jump_eq_zero_iff`.

The bound needs no potential crystallinity: forms of distinct weights are independent over $\mathbb{C}_p$.

**Theorem (Subobjects).** Let $R$ be a domain algebraic over $\mathbb{Z}_p$, let $T$ be finite and free, and let $f_i : T \to S_i$ be finitely many equivariant $R$-linear maps that are jointly injective, with each $S_i$ finite, free and potentially crystalline. If $u$ is a jump of $T$ at $\gamma$, then $u$ is a jump of some $S_i$ at $\gamma$.

Lean: `New.Period.exists_jump_of_jointly_injective` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean).

This is a weak form of the additivity of Hodge-Tate weights in exact sequences. It has no multiplicities. Section 8 uses it for the trivial representation inside $T$: if $T$ has a nonzero invariant vector, then $0$ is a jump of $T$.

**Theorem (Restriction of scalars).** Let $R$ be a domain that is finite and free over $\mathbb{Z}_p$, let $T$ be finite and free over $R$, and let $\rho$ be potentially crystalline. Write $\rho_{\mathbb{Z}_p}$ for $\rho$ viewed as a representation over $\mathbb{Z}_p$. Then
$$\sum_{\gamma : R \to \mathbb{C}_p} \mathrm{jump}(\rho, \gamma, u) = \mathrm{jump}(\rho_{\mathbb{Z}_p}, \mathrm{incl}, u) \quad \text{for every } u,$$
where $\gamma$ runs over the $\mathbb{Z}_p$-algebra maps and $\mathrm{incl} : \mathbb{Z}_p \to \mathbb{C}_p$ is the inclusion. The source also proves a bound for forms on which an element $\zeta \in R$ acts by a given scalar.

Lean: `New.Period.IsPotentiallyCrystalline.sum_jump_eq_jump_overZp` (Lib/PadicHodge/Crystalline/HodgeTateJumps.lean), `New.Period.card_algHom_eq_finrank`, `New.Period.overZp`.

The number of maps $\gamma$ is $\operatorname{rank}_{\mathbb{Z}_p} R$ (`card_algHom_eq_finrank`). This theorem converts the rank formula of Section 8, stated for $\rho_{\mathbb{Z}_p}$, to jumps at the embeddings of $R$.

**Example.** For $T = O_E(1)$, with $E$ of degree $r$ over $\mathbb{Q}_p$, each of the $r$ maps $\gamma$ has the jumps $\{-1\}$, and over $\mathbb{Z}_p$, $T \cong \mathbb{Z}_p(1)^r$ has the jump $-1$ with multiplicity $r$.
