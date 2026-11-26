---
title: The theorems of Ax and Tate
lean:
  - Lib/PadicHodge/PeriodRings/AxTheorem.lean
  - Lib/PadicHodge/TateSen.lean
decls:
  - New.Period.pow_le_norm_aeval
  - New.Period.ax_mem_closure_fixedField
  - New.Period.exists_algebraic_of_fixed_near_one
  - New.Period.exists_norm_normalizedTrace_le
  - New.Period.eq_zero_of_smul_eq_cyclotomicGp_zpow_smul
  - New.Period.tate_eq_zero_of_cyclotomicGp_twist
  - New.Period.le_of_echelon
  - New.Period.le_of_hodgeTate_stable
  - New.Period.forall_smul_eq_iff_mem_localFieldOf
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The theorems of Ax and Tate

Statements about the Galois invariants of a period ring reduce to statements about $\mathbb{C}_p$ and its cyclotomic twists. The theorem of Ax says that an element of $\mathbb{C}_p$ fixed by an open subgroup of $G_p$ is algebraic. The theorem of Tate says that no nonzero element of $\mathbb{C}_p$ transforms by a nonzero power of $\chi$. Together they give Ax-Sen-Tate and a principle of elimination.

### The theorem of Ax

**Theorem (Ax-Sen-Tate).** Let $J$ be a closed subgroup of $G_p$, and let $L \subseteq \overline{\mathbb{Q}}_p$ be its fixed field. The elements of $\mathbb{C}_p$ fixed by $J$ are the elements of the closure of $L$ in $\mathbb{C}_p$. In particular, if $J$ is open, then $L$ is a finite extension of $\mathbb{Q}_p$ and $\mathbb{C}_p^J = L$.

Lean: `New.Period.ax_mem_closure_fixedField` (Lib/PadicHodge/PeriodRings/AxTheorem.lean), for the main inclusion; `New.Period.forall_smul_eq_iff_mem_localFieldOf` (Lib/PadicHodge/TateSen.lean), for open $J$.

The main inclusion is the theorem of J. Ax, *Zeros of polynomials over local fields: the Galois action*, J. Algebra 15 (1970). The source also cites the proofs in the notes of Fontaine and Ouyang, Sections 3.3 to 3.5.

**Theorem (Ax).** Let $J$ be a subgroup of $G_p$ and let $x \in \mathbb{C}_p$ with $gx = x$ for every $g \in J$. Then $x$ lies in the closure in $\mathbb{C}_p$ of the image of the fixed field of $J$ in $\overline{\mathbb{Q}}_p$.

Lean: `New.Period.ax_mem_closure_fixedField` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

The proof uses one estimate on polynomials.

**Lemma.** Let $K$ be an algebraically closed field and $L$ a normed field over $K$. Let $f \in K[X]$ have leading coefficient $a$, let $x \in L$ and $r \geq 0$, and assume that $\|x - w\| \geq r$ for every root $w$ of $f$. Then $\|f(x)\| \geq \|a\|\, r^{\deg f}$.

Lean: `New.Period.pow_le_norm_aeval` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

*Proof.* Write $f = a\prod_w (X - w)$ over the roots with multiplicity, and bound each factor below by $r$. $\square$

*Proof of the theorem of Ax.* Assume the contrary. Then there is $\varepsilon > 0$ with $\|x - y\| \geq \varepsilon$ for every algebraic $y$ fixed by $J$. The source defines radii $r_k \geq \varepsilon/16$ with $r_0 = \varepsilon$ and $r_{k+1}^{2^k} = 2^{-(k+1)} r_k^{2^k}$, and proves by induction on $k$: if a finite set $S \subset \overline{\mathbb{Q}}_p$ with at most $2^k$ points is stable under $J$, then $\|x - z\| \geq r_k$ for every $z \in S$. For the step, let $T$ be the points $t \in S$ with $\|x - t\| = \|x - z\|$, and put $f = \sum_{t \in T} (X - t)^{2^k}$. Its coefficients are fixed by $J$, so its roots satisfy the bound $r_k$. The lemma gives $\|f(x)\| \geq 2^{-(k+1)} r_k^{2^k} = r_{k+1}^{2^k}$, and the ultrametric inequality gives $\|f(x)\| \leq \|x - z\|^{2^k}$. To finish, take $z$ algebraic with $\|x - z\| < \varepsilon/16$ and $S$ the conjugates of $z$. $\square$

The source proves only the case where $\sup_{g\in J} \|gx - x\| = 0$. It does not give the constant of Ax for the distance to the fixed field.

**Corollary.** If $x \in \mathbb{C}_p$ is fixed by every $g$ in a neighbourhood of $1$ in $G_p$, then $x$ lies in $\overline{\mathbb{Q}}_p$.

Lean: `New.Period.exists_algebraic_of_fixed_near_one` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

*Proof.* A neighbourhood of $1$ in the Krull topology contains the subgroup $\mathrm{Gal}(\overline{\mathbb{Q}}_p/E)$ for a finite extension $E$ of $\mathbb{Q}_p$. By the theorem of Ax, $x$ lies in the closure of $E$. A finite dimensional subspace of a normed space over the complete field $\mathbb{Q}_p$ is closed, so $x \in E$. $\square$

**Remark (Formalization).** The text writes $x \in \overline{\mathbb{Q}}_p$ for an element of $\mathbb{C}_p$ in the image of $\overline{\mathbb{Q}}_p$. In Lean, $\mathbb{C}_p$ is the completion of $\overline{\mathbb{Q}}_p$ (`PadicAlgCl p`), and the corollary gives `∃ y, x = coe' y`. The docstring of `Lib/PadicHodge/TateSen.lean` records that Ax's theorem comes "without the constant". So the source does not have the quantitative form that some proofs of the Sen theory use. No later file needs it.

### The normalized trace

**Proposition (Tate).** There is a constant $C$, depending only on $p$, such that every $z$ in $\mathbb{Q}_p(\mu_{p^\infty})$ has $|\mathrm{Tr}(z)| \leq C|z|$, where $\mathrm{Tr}$ is the normalized trace to $\mathbb{Q}_p$.

This is in J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966), Springer (1967), Section 3.

Lean: `New.Period.exists_norm_normalizedTrace_le` (Lib/PadicHodge/TateSen.lean).

The normalized trace of $z$ is $[E:\mathbb{Q}_p]^{-1}\mathrm{Tr}_{E/\mathbb{Q}_p}(z)$ for any finite extension $E$ that contains $z$. It does not depend on $E$.

*Proof.* The source first bounds the normalized trace of every root of unity of $p$-power order by a constant $C$. For $z \in \mathbb{Q}_p(\zeta)$ with $\zeta$ primitive of order $p^{n+1}$, write $z = \sum_{i<e} a_i \pi^i$ with $\pi = \zeta - 1$ and $e = \varphi(p^{n+1})$. The nonzero terms have distinct norms, so each has norm at most $\|z\|$, and the binomial theorem bounds $|\mathrm{Tr}(\pi^i)|$ by $C$. This gives the constant $Cp$. $\square$

### The theorem of Tate

**Theorem (Tate).** For every open subgroup $U$ of $G_p$ and every integer $n \neq 0$, $H^0(U, \mathbb{C}_p(n)) = 0$.

Lean: `New.Period.tate_eq_zero_of_cyclotomicGp_twist` (Lib/PadicHodge/TateSen.lean).

This is in Tate, *p-divisible groups*, Section 3.

The source proves it in two steps. The first step is the case $U = G_p$.

**Theorem.** Let $y \in \mathbb{C}_p$ and $n \neq 0$, and assume $gy = \chi(g)^n y$ for every $g \in G_p$. Then $y = 0$.

Lean: `New.Period.eq_zero_of_smul_eq_cyclotomicGp_zpow_smul` (Lib/PadicHodge/TateSen.lean).

*Proof.* Let $H = \ker\chi$. For algebraic $w$ fixed by $H$, $1 - (\gamma w - w)$ has normalized trace $1$, so $1 \leq C\,\|1 - (\gamma w - w)\|$, and by Ax this holds for every $z \in \mathbb{C}_p^H$. If $y \neq 0$, it is enough, by Ax again, to show $1 \leq C\,\|1 - yw\|$ for algebraic $w$ fixed by $H$, since $w = y^{-1}$ gives a contradiction. For this, take $\delta$ in inertia fixing $w$ with $a = \chi(\delta)^n \neq 1$, and $z = (a-1)^{-1} yw$, so that $\delta z - z = yw$. $\square$

The second step passes to open subgroups by Galois descent.

**Theorem.** Let $x \in \mathbb{C}_p$ and let $u \neq v$ be integers. Assume that $\chi(g)^u\, gx = \chi(g)^v x$ for every $g$ in a neighbourhood of $1$ in $G_p$. Then $x = 0$.

Lean: `New.Period.tate_eq_zero_of_cyclotomicGp_twist` (Lib/PadicHodge/TateSen.lean).

*Proof.* On an open subgroup $U$, $x$ is fixed by the twisted action $g \ast y = \chi(g)^{u - v} gy$. Galois descent writes $x$ as a $\overline{\mathbb{Q}}_p$-combination of elements fixed by all of $G_p$ for this action, and each of them is $0$ by the first step. $\square$

**Remark (Formalization).** The source states and proves Tate's theorem for $H^0$ only, as the docstring of `Lib/PadicHodge/TateSen.lean` says. The textbook form also contains $H^1(G_K, \mathbb{C}_p(n)) = 0$ for $n \neq 0$, and $H^1(G_K, \mathbb{C}_p)$ of dimension $1$ over $K$. No file of the period rings uses these. The hypothesis "for every $g$ in a neighbourhood of $1$" is a filter condition, `∀ᶠ g in nhds 1`. It is the form in which the later files apply the theorem, to a representation of a group $\Gamma$ with $j : \Gamma \to G_p$ of open image.

### Ax-Sen-Tate for a group over G_p

**Theorem.** Let $j : \Gamma \to G_p$ have open image, and let $K$ be the fixed field of $j(\Gamma)$ in $\overline{\mathbb{Q}}_p$. An element $x \in \mathbb{C}_p$ is fixed by every $j(g)$ if and only if $x \in K$.

Lean: `New.Period.forall_smul_eq_iff_mem_localFieldOf` (Lib/PadicHodge/TateSen.lean), `New.Period.localFieldOf`, `New.Period.OverGp`.

*Proof.* The image $j(\Gamma)$ is an open subgroup, so it is a neighbourhood of $1$. The corollary to the theorem of Ax gives that $x$ is algebraic, and then $x \in K$ by definition. The converse is clear. $\square$

The class `New.Period.OverGp` packages $j$ (`toGp`) with the fact that its range is open. The filter `New.Period.nearOne` on $\Gamma$ is the pull-back along $j$ of the neighbourhoods of $1$, and its image under $j$ is the filter of neighbourhoods of $1$ (`New.Period.nhds_one_le_map_nearOne`).

### Elimination

Sections 5 and 6 need to find, in a subspace $W$ of $\mathbb{C}_p^d$ that is stable under a twisted Galois action, enough vectors that are algebraic and Galois-fixed. The source does this with an elimination on supports.

**Lemma (Elimination).** Let $A$ be a commutative ring and $b$ a basis of an $A$-module $V$, with coordinates $b_i$. Let $W, W'$ be submodules of $V$. Assume the following for every nonzero $v \in W$ such that every $y \in W$ with support inside the support of $v$ is proportional to $v$, in the sense $b_k(v)\,y = b_k(y)\,v$ for all $k$: there is $u \in W \cap W'$ with support inside the support of $v$ and with some coordinate equal to $1$. Then $W \subseteq W'$.

Lean: `New.Period.le_of_echelon` (Lib/PadicHodge/TateSen.lean).

*Proof.* By induction on the support. If $y$ has support inside that of $w$ and $b_k(w) \neq 0$, then $b_k(y)w - b_k(w)y$ has strictly smaller support. This gives, first, a vector $u$ as in the hypothesis for every nonzero $w \in W$, without the proportionality condition. Then subtract $b_k(w)u$ from $w$ to lower the support of $w$. $\square$

**Theorem (Hodge-Tate elimination).** Let $\iota$ be finite and $u : \iota \to \mathbb{Z}$. Let $F$ be a filter on $G_p$ finer than the neighbourhoods of $1$. Let $W$ be a $\mathbb{C}_p$-subspace of $\mathbb{C}_p^\iota$ such that, for each $a \in W$, the vector $(\chi(g)^{u_i}\, g a_i)_i$ lies in $W$ for $g$ eventually along $F$. Let $W'$ be a subspace that contains each $a \in W \cap \overline{\mathbb{Q}}_p^\iota$ for which some $k$ has: $\|a_i\| \leq 1$ for all $i$; $a_i = 0$ whenever $u_i \neq u_k$; $a_k = 1$; and each $a_i$ is fixed by $g$ eventually along $F$. Then $W \subseteq W'$.

Lean: `New.Period.le_of_hodgeTate_stable` (Lib/PadicHodge/TateSen.lean).

*Proof.* Apply the elimination lemma to the standard basis, and scale the vector $v$ it gives so that a coordinate $w_k$ of largest norm is $1$. The twisted conjugate of $w$ lies in $W$ with support inside that of $w$, so it is proportional to $w$, and the factor at $k$ gives $\chi(g)^{u_i} g w_i = \chi(g)^{u_k} w_i$ for $g$ along $F$. If $u_i \neq u_k$, Tate's theorem gives $w_i = 0$. If $u_i = u_k$, the corollary to the theorem of Ax gives $w_i \in \overline{\mathbb{Q}}_p$. $\square$

**Example.** Take $u = (0, 1)$ and $W$ the line of $(1, c)$. The twisted conjugate $(1, \chi(g)\, gc)$ lies in $W$ only if $\chi(g)\,gc = c$, and Tate's theorem gives $c = 0$. So the theorem finds the generator $(1, 0)$.
