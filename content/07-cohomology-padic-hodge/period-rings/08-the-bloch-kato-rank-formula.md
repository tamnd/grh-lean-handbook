---
title: The Bloch-Kato rank formula
lean:
  - Lib/PadicHodge/BlochKato.lean
  - Lib/PadicHodge/Characters.lean
decls:
  - New.Period.crysCocycles.comp_mem
  - New.Period.crysCocycles.coboundary_mem
  - New.Period.crysCocycles.apply_mul
  - New.Period.crysCocycles.mem_of_smul_mem
  - New.Period.crysCocycles.eventually_eq_pow_smul
  - New.Period.IsPotentiallyCrystalline.comp_mem_Z1
  - New.Period.IsPotentiallyCrystalline.ker_reducedCocycle
  - New.Period.extensionRep
  - New.Period.isAdmissible_extensionRep
  - New.Period.jump_extensionRep_le
  - New.Period.IsPotentiallyCrystalline.exists_hodge_basis
  - New.Period.crysCocycles.finrank_eq
  - New.Period.crysCocycles.fg
  - New.Period.IsPotentiallyCrystalline.exists_coboundary_eq_smul
  - New.Period.crysCocycles.apply_eq_zero_of_cyclotomicGp
  - New.Period.exists_unramified_period
  - New.Period.exists_period_of_character
  - New.Period.isPotentiallyCrystalline_of_unramified_char
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Bloch-Kato rank formula

This section computes the rank of the module $Z_f(T)$ of crystalline cocycles of Section 5, for a lattice $T$ in a potentially crystalline representation. This is the number that Volume 12 needs to bound Selmer groups. The section also proves that $Z_f(T)$ behaves well under reduction modulo $p^m$, and it ends with the potentially unramified characters, which the source treats in the file `Characters`. The source cites S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Proposition 3.8 and Corollary 3.8.4, and J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay summer school notes (2009), Proposition 2.8 and Theorem 2.1.

### The classical formula

Let $V$ be a finite-dimensional de Rham representation of $G_K$. Bloch and Kato prove
$$\dim_{\mathbb{Q}_p} H^1_f(K, V) = \dim_{\mathbb{Q}_p} H^0(K, V) + \dim_{\mathbb{Q}_p} D_{\mathrm{dR}}(V)/\mathrm{Fil}^0 D_{\mathrm{dR}}(V).$$
The source does not work with classes. It counts cocycles. The two counts are related as follows. The cocycles $Z_f$ contain the coboundaries $B^1 = \{g \mapsto gx - x\}$, and $Z_f/B^1 = H^1_f$. The map $x \mapsto (g \mapsto gx - x)$ has kernel $H^0$, so $\dim B^1 = \dim V - \dim H^0$. So
$$\dim Z_f = \dim V + \dim_{\mathbb{Q}_p} D_{\mathrm{dR}}(V)/\mathrm{Fil}^0.$$
The term $H^0$ cancels. The last term is $[K : \mathbb{Q}_p]$ times the number of Hodge-Tate weights of $V$ on the side where $\mathbb{Q}_p(1)$ lies, counted with multiplicity. In the convention of Section 7, $\mathbb{Z}_p(1)$ has the jump $-1$, so this is the number of negative jumps.

### Crystalline cocycles

The setting of this section is: $T$ is a finite free $\mathbb{Z}_p$-module, also an $R$-module, with an $R$-linear action $\rho$ of $\Gamma$, and $j : \Gamma \to G_p$ has open image of index $n$. The definition of $Z_f(\rho)$ is in Section 5: $c \in Z_f(\rho)$ if $1 \otimes c(g) = (j(g) \otimes \rho(g))y - y$ for one $y \in B_{\max} \otimes T$ and all $g$.

**Theorem (Basic properties).**

1. If $f : T \to T'$ is $\mathbb{Z}_p$-linear and equivariant, then $f \circ c \in Z_f(\sigma)$ for $c \in Z_f(\rho)$.
2. For $x \in T$, the coboundary $g \mapsto \rho(g)x - x$ is in $Z_f(\rho)$.
3. If $T$ is free over $\mathbb{Z}_p$, every $c \in Z_f(\rho)$ satisfies $c(gh) = c(g) + \rho(g)c(h)$.
4. If $a \in \mathbb{Z}_p$ is nonzero and $a c \in Z_f(\rho)$, then $c \in Z_f(\rho)$.

Lean: `New.Period.crysCocycles.comp_mem` (Lib/PadicHodge/BlochKato.lean), `New.Period.crysCocycles.coboundary_mem`, `New.Period.crysCocycles.apply_mul`, `New.Period.crysCocycles.mem_of_smul_mem`.

*Proof.* For 1, apply $1 \otimes f$ to the witness $y$. For 2, the witness is $1 \otimes x$. For 3, $gh\,y - y = (gy - y) + g(hy - y)$, and $x \mapsto 1 \otimes x$ is injective for $T$ free. For 4, $a$ is a unit of $B_{\max}$ fixed by $G_p$, so $a^{-1}y$ is a witness for $c$. $\square$

Claim 4 says that $Z_f(\rho)$ is saturated in the module of all maps $\Gamma \to T$.

**Remark (Formalization).** The definition of $Z_f$ does not ask that $c$ is continuous, and $\Gamma$ has no topology in it. The next theorem shows that, for a potentially crystalline $\rho$, a crystalline cocycle is automatically continuous in the sense that matters.

**Theorem (Continuity).** Let $\rho$ be potentially crystalline and $c \in Z_f(\rho)$. For every $m$, $c(g) \in p^mT$ for all $g$ near $1$. If $\Gamma$ is a topological group and $j$ is an open embedding, and $q : T \to V$ is an equivariant additive map onto a discrete $\Gamma$-module with kernel $p^mT$, then $q \circ c$ is a continuous cocycle. The kernel of $c \mapsto q \circ c$ on $Z_f(\rho)$ is $p^m Z_f(\rho)$.

Lean: `New.Period.crysCocycles.eventually_eq_pow_smul` (Lib/PadicHodge/BlochKato.lean), `New.Period.IsPotentiallyCrystalline.comp_mem_Z1`, `New.Period.IsPotentiallyCrystalline.reducedCocycle`, `New.Period.IsPotentiallyCrystalline.ker_reducedCocycle`.

The statement on the kernel is saturation again: if $q \circ c = 0$, then $c = p^m b$ for a map $b$, and $b \in Z_f(\rho)$ by claim 4. These results connect $Z_f$ with the Galois cohomology of finite modules that Volume 3 uses in [local duality and the Greenberg-Wiles count](/chapter/local-duality/). The source also proves that the reductions are stable under corestriction (`New.Period.IsPotentiallyCrystalline.holdsCorestrictions`), which that count needs.

### Extensions

A crystalline cocycle gives an extension. Let $C$ be an $R$-module and $a : C \to Z_f(\rho)$ an $R$-linear map. On $T \times C$, put $g(y, c) = (\rho(g)y + a(c)(g),\, c)$.

**Theorem (Extensions are admissible).** If $\rho$ is admissible along $F$, then so is the extension $T \times C$. If $T$ is finite over $R$ and $u \neq 0$, the jump $u$ of the extension has multiplicity at most that of $T$.

Lean: `New.Period.extensionRep` (Lib/PadicHodge/BlochKato.lean), `New.Period.isAdmissible_extensionRep`, `New.Period.jump_extensionRep_le`.

*Proof.* The vector $(0, c)$ satisfies $g(1 \otimes (0, c)) - 1 \otimes (0, c) = 1 \otimes (a(c)(g), 0) = g(y_c, 0) - (y_c, 0)$ for the witness $y_c$ of $a(c)$. So $1 \otimes (0, c) - (y_c, 0)$ is fixed by all $g$, and $1 \otimes (0, c)$ is in the span of fixed periods and the image of $B_{\max} \otimes T$. For the jumps, a form of weight $u \neq 0$ on $T \times C$ that vanishes on $T$ is a form on the trivial module $C$, and is $0$ by Tate's theorem. So restriction to $T$ is injective. $\square$

### Hodge coordinates

The proof of the rank formula needs coordinates in which the filtration is diagonal.

**Theorem (Hodge basis).** Let $\rho$ be potentially crystalline and $e$ a $\mathbb{Z}_p$-basis of $T$, indexed by $\iota$. There are $k : \iota \to \mathbb{Z}$ and a $\mathbb{Z}_p$-linear automorphism $N$ of $B_{\mathrm{dR}}^\iota$ with:

1. the multiset $\{k_i\}$ lists the jumps of $\rho_{\mathbb{Z}_p}$ at the inclusion $\mathbb{Z}_p \to \mathbb{C}_p$;
2. $N$ carries the action of $g$ on $B_{\mathrm{dR}}^\iota$, by the matrix of $\rho(g)$ in $e$ and $j(g)$ on the entries, to the action of $j(g)$ on the entries;
3. a vector $b$ is $N$ of a vector over $B_{\mathrm{dR}}^+$ if and only if $b_i \in \mathrm{Fil}^{-k_i} B_{\mathrm{dR}} = t^{-k_i}B_{\mathrm{dR}}^+$ for each $i$;
4. there is an invertible $W$ over $B_{\mathrm{dR}}^+$ with $\rho(g) \cdot j(g)\bigl(W\,\mathrm{diag}(t^{k_i})\bigr) = W\,\mathrm{diag}(t^{k_i})$ for all $g$.

Lean: `New.Period.IsPotentiallyCrystalline.exists_hodge_basis` (Lib/PadicHodge/BlochKato.lean).

The docstring calls this "a case of the existence of bases adapted to the Hodge filtration (Brinon-Conrad 6.3.7)". The proof uses Galois descent from the field fixed by an open subgroup to turn the periods fixed near $1$ into an invertible matrix $U$ of periods fixed by all of $\Gamma$. Its Hodge form $W\,\mathrm{diag}(t^{k_i})$, with $W$ invertible over $B_{\mathrm{dR}}^+$, is again invariant, and $N$ is the inverse of multiplication by it.

### The rank formula

**Theorem (Bloch-Kato rank formula).** Let $T$ be finite and free over $\mathbb{Z}_p$, let $\rho$ be potentially crystalline, and let $J$ list the jumps of $\rho_{\mathbb{Z}_p}$ at the inclusion $\mathbb{Z}_p \to \mathbb{C}_p$. Then $Z_f(\rho)$ is a finitely generated $\mathbb{Z}_p$-module and
$$\operatorname{rank}_{\mathbb{Z}_p} Z_f(\rho) = \operatorname{rank}_{\mathbb{Z}_p} T + [G_p : j(\Gamma)] \cdot \#\{u \in J : u < 0\},$$
where the count is with multiplicity.

Lean: `New.Period.crysCocycles.finrank_eq` (Lib/PadicHodge/BlochKato.lean).

*Proof.* Take a basis $e$ of $T$ indexed by $\iota$, with $|\iota| = d$, and the Hodge coordinates $(k, N)$. Let $K$ be the field of elements of $\overline{\mathbb{Q}}_p$ fixed by $j(\Gamma)$; it has degree $n = [G_p : j(\Gamma)]$ over $\mathbb{Q}_p$. Write $D$ for the coboundary map $y \mapsto (g \mapsto gy - y)$ on $B_{\max}^\iota$, with $\Gamma$ acting through $e$. Let $P \subset B_{\mathrm{dR}}^\iota$ be $N$ of the vectors over $B_{\mathrm{dR}}^+$, so $P = \prod_i t^{-k_i}B_{\mathrm{dR}}^+$ by 3.

Compare two $\mathbb{Z}_p$-modules of vectors $y \in B_{\max}^\iota$.

- $A$ is the set of $y$ such that $Dy$ has values in $\mathbb{Z}_p^\iota$, that is, $Dy$ comes from a map $\Gamma \to T$.
- $B$ is the set of $y$ such that $\varphi(y) - y$ is fixed by $\Gamma$ and $N(y)$ lies in $K^\iota + P$.

*Rank of $A$.* The map $D$ sends $A$ onto $Z_f(\rho)$, read in coordinates, with kernel $\ker D$. So $\operatorname{rank} A = \operatorname{rank} Z_f(\rho) + \operatorname{rank} \ker D$ (`rank_comap_coboundary_eq`).

*Rank of $B$.* Consider $\Phi(y) = (\varphi(y) - y,\ N(y) \bmod P)$ from $B_{\max}^\iota$ to $B_{\max}^\iota \times B_{\mathrm{dR}}^\iota/P$. By the fundamental exact sequence of Section 4, $\Phi$ is onto, with kernel $\mathbb{Q}_p^\iota$. The set $B$ is the preimage of $\ker D \times (K^\iota + P)/P$. For $k_i \geq 0$, the coordinate $i$ of $K^\iota$ lies in $t^{-k_i}B_{\mathrm{dR}}^+$, so it vanishes modulo $P$. For $k_i < 0$, it meets $t^{-k_i}B_{\mathrm{dR}}^+$ only in $0$. So $(K^\iota + P)/P \cong K^{d^-}$, with $d^-$ the number of negative $k_i$. This gives
$$\operatorname{rank} B = \operatorname{rank} \ker D + n\, d^- + d$$
(`rank_comap_frob_sub_prod_eq`), since $K$ has rank $n$ over $\mathbb{Z}_p$ and $\mathbb{Q}_p^\iota$ has rank $d$.

*$A \subseteq B$.* If $Dy$ has values in $\mathbb{Z}_p^\iota$, then $\varphi$ fixes $Dy$, and $D$ commutes with $\varphi$, so $D(\varphi(y) - y) = 0$. The vector $N(y)$ satisfies $g N(y) - N(y) = N(Dy(g)) \in P$, since $Dy(g)$ has entries in $\mathbb{Z}_p \subset B_{\mathrm{dR}}^+$. By the theorem on the invariants of $B_{\mathrm{dR}}$ in Section 4, applied with $S$ the coordinate $t^{-k_i}B_{\mathrm{dR}}^+$, each coordinate of $N(y)$ is in $K$ modulo $P$.

*$B/A$ is torsion.* Let $y \in B$, and write $N(y) = w + N(x)$ with $w \in K^\iota$ and $x$ over $B_{\mathrm{dR}}^+$. The entries of $Dy$ are fixed by $\varphi$, and in $B_{\mathrm{dR}}$ they are the coboundary of $x$. They also lie in $B_{\mathrm{dR}}^+$, so they are $p$-adic numbers by the fundamental exact sequence. Their denominators are bounded (`exists_pow_mul_coboundary_integral`), so one power $p^s$ makes all of them integral (`exists_padicInt_eq_pow_smul_of_frobEnd_eq`). So $p^s y \in A$.

So $A$ and $B$ have the same rank. The module $\ker D$ embeds in $K^\iota$, so its rank is finite and cancels: $\operatorname{rank} Z_f(\rho) = d + n d^-$. Finally, $Z_f(\rho)$ is a torsion-free submodule of a separated module with finite rank, and this gives finite generation (`crysCocycles.finite_and_finrank_eq_of_rank_eq`). $\square$

**Remark (Formalization).** Four points separate this theorem from the classical one.

1. It is stated on cocycles, not on $H^1_f$. The classical form follows by the computation at the start of the section, but the source does not state it.
2. The jumps are those of $\rho_{\mathbb{Z}_p}$ at the one map $\mathbb{Z}_p \to \mathbb{C}_p$, not of $\rho$ at the embeddings of $R$. For $R$ a domain finite and free over $\mathbb{Z}_p$, the restriction theorem of Section 7 converts one to the other.
3. The factor $n$ is the index $[G_p : j(\Gamma)]$, which is $[K : \mathbb{Q}_p]$ for $\Gamma = G_K$. It is finite since $j(\Gamma)$ is open in the compact group $G_p$, so the formula has no junk value from an infinite index.
4. The crystalline condition uses $B_{\max}$ (F-056). The rank is for $B_{\max}$-crystalline cocycles. The classical $H^1_f$ uses $B_{\mathrm{cris}}$.

**Theorem (Finite generation over R).** If $T$ is finite and free over $\mathbb{Z}_p$ and $\rho$ is potentially crystalline, then $Z_f(\rho)$ is finitely generated over $R$.

Lean: `New.Period.crysCocycles.fg` (Lib/PadicHodge/BlochKato.lean).

**Example.** Let $\Gamma = G_p$ with $j$ the identity, so $n = 1$.

1. $T = \mathbb{Z}_p$ with the trivial action. The only jump is $0$, so $\operatorname{rank} Z_f = 1$. The coboundaries are $0$. The crystalline cocycles are homomorphisms $G_p \to \mathbb{Z}_p$, and the formula says that they form a module of rank $1$. Classically, $H^1_f(\mathbb{Q}_p, \mathbb{Q}_p)$ is the line of unramified homomorphisms.
2. $T = \mathbb{Z}_p(1)$. The jump is $-1$, so $\operatorname{rank} Z_f = 1 + 1 = 2$. The coboundaries $g \mapsto (\chi(g) - 1)x$ have rank $1$, and the quotient has rank $1$. Classically, $H^1_f(\mathbb{Q}_p, \mathbb{Q}_p(1))$ is $\mathbb{Z}_p^\times \otimes \mathbb{Q}_p$ under the Kummer map, of dimension $1$.
3. $T = \mathbb{Z}_p(-1)$. The jump is $1$, so $\operatorname{rank} Z_f = 1$, and every crystalline cocycle is a coboundary up to torsion. Classically, $H^1_f(\mathbb{Q}_p, \mathbb{Q}_p(-1)) = 0$.

### Two consequences

**Theorem (Positive jumps).** Let $\rho$ be potentially crystalline and suppose every jump of $\rho_{\mathbb{Z}_p}$ with nonzero multiplicity is positive. Then for every $c \in Z_f(\rho)$ there are a nonzero $t \in \mathbb{Z}_p$ and $x \in T$ with $\rho(g)x - x = t\, c(g)$ for all $g$.

Lean: `New.Period.IsPotentiallyCrystalline.exists_coboundary_eq_smul` (Lib/PadicHodge/BlochKato.lean).

*Proof.* There are no negative jumps, so $\operatorname{rank} Z_f = d$. A nonzero invariant $x$ would embed the trivial representation in $T$, and $0$ would be a jump of $T$ by the subobject theorem of Section 7, which the hypothesis excludes. So the coboundary map $T \to Z_f$ is injective, its image has rank $d$, and the quotient is torsion. $\square$

**Theorem (Twists of the trivial representation).** Let $\Gamma$ act on $T$ by $\chi^{-a}$ with $a \geq 0$, and let $c \in Z_f(\rho)$. If $\rho(s) = 1$, and $j(s)$ is in inertia in the case $a = 0$, then $c(s) = 0$.

Lean: `New.Period.crysCocycles.apply_eq_zero_of_cyclotomicGp` (Lib/PadicHodge/BlochKato.lean).

*Proof.* For $a > 0$, every jump is $a > 0$, so the theorem on positive jumps gives $t \neq 0$ and $x$ with $\rho(g)x - x = t\,c(g)$. At $g = s$ the left side is $0$, and $T$ is torsion free, so $c(s) = 0$. For $a = 0$, it is enough to show $l(c(s)) = 0$ for every linear form $l : T \to \mathbb{Z}_p$. By claim 1 of the basic properties, $l \circ c$ is a crystalline cocycle of the trivial representation, so $l(c(g)) = j(g)y - y$ for some $y \in B_{\max}$. The element $\varphi(y) - y$ is fixed by $\Gamma$, so by the theorem on fixed fractions of Section 5, $p^n(\varphi(y) - y)$ is a Witt vector $w$ over a finite field, and $w = \varphi(x) - x$ for some $x \in A_{\inf}$ by Section 2. The element $y$ is invariant modulo $B_{\mathrm{dR}}^+$, so $y = z + b$ with $z \in B_{\mathrm{dR}}^+$ and $b$ algebraic. Then $p^n y - x$ is fixed by $\varphi$, and the fundamental exact sequence makes it a $p$-adic number $r$. Since $j(s)$ fixes $r$, it moves $x$ by $p^n l(c(s))$. The element $j(s)$ is in inertia, so its action on $x$ is trivial after reduction to the Witt vectors of the residue field. So $p^n l(c(s)) = 0$. $\square$

The docstring calls the theorem "a consequence, on cocycles, of the Bloch-Kato computation of $H^1_f$ of Tate twists".

### Potentially unramified characters

The local conditions of Volume 12 are also applied to characters. The source proves the needed facts only for characters that are unramified on an open subgroup.

**Theorem (Lang's equation in rank one).** Let $T$ be a finite free $\mathbb{Z}_p$-algebra and $a \in T$ with $(1 - a)^e \in pT$ for some $e$. Then $A_{\inf} \otimes_{\mathbb{Z}_p} T$ has a unit $y$ such that every element of `FrobGal` maps $y$ into $(1 \otimes T)\,y$, and for every Weil pair $(s, k)$, $\varphi^k(s(y)) = y$ and $s(y) = (1 \otimes a^k)\,y$.

Lean: `New.Period.exists_unramified_period` (Lib/PadicHodge/Characters.lean).

*Proof.* Put $\alpha = 1 \otimes a$. Solve $\alpha\varphi(x) - x = 1$ by successive approximation modulo powers of $1 - \alpha$. Modulo $1 - \alpha$ the equation is $\varphi(x) - x = 1$, which has a solution by the Artin-Schreier-Witt proposition of Section 2. Since $(1-\alpha)^e \in (p)$ and $A_{\inf} \otimes T$ is $p$-adically complete, the approximations converge. Put $y = (1 - \alpha)x + 1$, which is a unit because $1 - \alpha$ is in the Jacobson radical, and satisfies $\alpha\varphi(y) = y$. Every $m \in$ `FrobGal` fixes $\alpha$ and commutes with $\varphi$, so $m(y)$ solves the same equation, and $m(y)/y$ is fixed by $\varphi$, so lies in $T$. For a Weil pair, $\varphi^k \circ s$ acts trivially on the Witt vectors of the residue field, so the factor is $1$. Then $\varphi^k(s(y)) = y$ and $\alpha^k \varphi^k(y) = y$ give $s(y) = \alpha^k y$. $\square$

**Theorem (Potentially unramified characters).** Let $\Gamma$ be a topological group, $j$ an open embedding, and $\nu : \Gamma \to \overline{\mathbb{Q}}_p^\times$ a continuous character with $\nu(g) = 1$ for all $g$ near $1$ with $j(g)$ in inertia. Let $T$ be a commutative $\overline{\mathbb{Q}}_p$-algebra and $\rho(g)x = \nu(g)x$. Then:

1. $\rho$ is potentially crystalline;
2. $\rho$ has the jumps of the trivial action on $T$;
3. for every Weil pair $(j(s), k)$, the polynomial $X - \nu(s)$ kills $(s, k)$ on $\rho$.

Lean: `New.Period.isPotentiallyCrystalline_of_unramified_char` (Lib/PadicHodge/Characters.lean), `New.Period.IsPotentiallyCrystalline.of_unramified_char`, `New.Period.jump_eq_jump_one_of_unramified_char`, `New.Period.isKilledBy_X_sub_C_of_unramified_char`, `New.Period.exists_period_of_character`.

*Proof.* Choose an open subgroup $U$ on which $\nu$ is trivial on inertia and $|1 - \nu| < 1$, a Frobenius $\phi \in U$ of some degree $f$, and an $f$-th root $a$ of $\nu(\phi)$ with $|1 - a| < 1$. The value $a$ lies in the ring of integers $O$ of a finite Galois extension of $\mathbb{Q}_p$, and $(1-a)^e \in pO$ for some $e$. Lang's equation gives a unit $y \in A_{\inf} \otimes O$. The identity $j(g)(y) = (1 \otimes \nu(g)^{-1})\,y$ holds on the elements $\phi^k i$ with $i$ in inertia, which are dense near $1$, and it is closed, so it holds near $1$ (`exists_period_of_character`). Then $(1 \otimes x)\,y$ is fixed near $1$ for every $x \in T$, and these elements span $B_{\max} \otimes T$ because $y$ is a unit. This gives 1. On these elements $\beta_{s,k}$ is multiplication by $\nu(s)$, since $\varphi^k(s(y)) = y$, which gives 3. Claim 2 follows from the same period, mapped to $\mathbb{C}_p$. $\square$

**Remark (Formalization).** The theorem covers only characters that are unramified on an open subgroup, so of finite order on inertia. The module $T$ is a commutative $\overline{\mathbb{Q}}_p$-algebra, and the coefficients act through $\overline{\mathbb{Q}}_p$. The docstring calls the result "a case of the fact that potentially unramified characters are potentially crystalline of weight 0 (Caruso)". The file gives no further reference. The header of `Lib/PadicHodge/PeriodRings/DeRhamPeriods.lean` names X. Caruso, *An introduction to p-adic period rings* (2019), Section 3, and this is probably the work meant.
