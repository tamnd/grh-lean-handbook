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

The period rings of this chapter are rings of functions of a sort on $\mathbb{C}_p$ and its tilt. Each statement about the Galois invariants of a period ring reduces, in the end, to a statement about the Galois invariants of $\mathbb{C}_p$ and of its cyclotomic twists. This section proves the two such statements that the source uses. The first is the theorem of Ax: an element of $\mathbb{C}_p$ that is fixed by an open subgroup of $G_p$ is algebraic. The second is the theorem of Tate: no nonzero element of $\mathbb{C}_p$ transforms by a nonzero power of the cyclotomic character. Together they give the theorem of Ax-Sen-Tate, and a principle of elimination that the source uses to find algebraic, Galois-fixed vectors in a subspace of $\mathbb{C}_p^d$.

### The theorem of Ax

**Theorem (Ax-Sen-Tate).** Let $J$ be a closed subgroup of $G_p$, and let $L \subseteq \overline{\mathbb{Q}}_p$ be its fixed field. The elements of $\mathbb{C}_p$ fixed by $J$ are the elements of the closure of $L$ in $\mathbb{C}_p$. In particular, if $J$ is open, then $L$ is a finite extension of $\mathbb{Q}_p$ and $\mathbb{C}_p^J = L$.

The main inclusion is the theorem of J. Ax, *Zeros of polynomials over local fields: the Galois action*, J. Algebra 15 (1970). The source also cites the proofs in the notes of Fontaine and Ouyang, Sections 3.3 to 3.5.

The source proves the main inclusion for every subgroup $J$, closed or not.

**Theorem (Ax).** Let $J$ be a subgroup of $G_p$ and let $x \in \mathbb{C}_p$ with $gx = x$ for every $g \in J$. Then $x$ lies in the closure in $\mathbb{C}_p$ of the image of the fixed field of $J$ in $\overline{\mathbb{Q}}_p$.

Lean: `New.Period.ax_mem_closure_fixedField` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

The proof uses one estimate on polynomials.

**Lemma.** Let $K$ be an algebraically closed field and $L$ a normed field over $K$. Let $f \in K[X]$ have leading coefficient $a$, let $x \in L$ and $r \geq 0$, and assume that $\|x - w\| \geq r$ for every root $w$ of $f$. Then $\|f(x)\| \geq \|a\|\, r^{\deg f}$.

Lean: `New.Period.pow_le_norm_aeval` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

*Proof.* Write $f = a\prod_w (X - w)$ over the roots with multiplicity, and bound each factor below by $r$. $\square$

*Proof of the theorem of Ax.* Assume the contrary. Then there is $\varepsilon > 0$ such that $\|x - y\| \geq \varepsilon$ for every $y \in \overline{\mathbb{Q}}_p$ fixed by $J$. Define radii
$$r_k = \frac{\varepsilon}{16}\, 2^{(2k+4)/2^k}, \qquad k \geq 0.$$
Then $r_0 = \varepsilon$, $r_k \geq \varepsilon/16$ for all $k$, and $r_{k+1}^{2^k} = 2^{-(k+1)} r_k^{2^k}$. Both sides of the last identity are $(\varepsilon/16)^{2^k} 2^{k+3}$.

*Claim.* Let $S$ be a finite subset of $\overline{\mathbb{Q}}_p$ with at most $2^k$ points that is stable under $J$. Then $\|x - z\| \geq r_k$ for every $z \in S$.

For $k = 0$, $S$ has one point, which is fixed by $J$, and the hypothesis gives the bound. For the step from $k$ to $k+1$, let $z \in S$ and let $T$ be the set of points $t \in S$ with $\|x - t\| = \|x - z\|$. The set $T$ is stable under $J$, because $J$ fixes $x$ and acts by isometries. Put
$$f = \sum_{t \in T} (X - t)^{2^k}.$$
Then $f$ has degree $2^k$ and leading coefficient the integer $\#T$, and its coefficients are fixed by $J$. So the set of roots of $f$ is stable under $J$ and has at most $2^k$ points. By the induction hypothesis, every root lies at distance at least $r_k$ from $x$. The integer $\#T$ is at most $2^{k+1}$, so $|\#T|_p \geq 2^{-(k+1)}$. The lemma gives $\|f(x)\| \geq 2^{-(k+1)} r_k^{2^k} = r_{k+1}^{2^k}$. On the other hand, every term $(x - t)^{2^k}$ of $f(x)$ has norm $\|x - z\|^{2^k}$, so $\|f(x)\| \leq \|x - z\|^{2^k}$ by the ultrametric inequality. Thus $\|x - z\| \geq r_{k+1}$.

To finish, choose $z \in \overline{\mathbb{Q}}_p$ with $\|x - z\| < \varepsilon/16$. The roots of the minimal polynomial of $z$ over $\mathbb{Q}_p$ form a finite set that is stable under $J$ and contains $z$. The claim gives $\|x - z\| \geq r_k \geq \varepsilon/16$ for a suitable $k$, which is a contradiction. $\square$

The proof does not use the closedness of $J$, and it does not give the constant of Ax. In the classical statement, the distance from $x$ to the fixed field is bounded by a constant multiple of $\sup_{g\in J} \|gx - x\|$. The source proves only the case where the supremum is $0$. The lemmas on the radii are private to the file.

**Corollary.** If $x \in \mathbb{C}_p$ is fixed by every $g$ in a neighbourhood of $1$ in $G_p$, then $x$ lies in $\overline{\mathbb{Q}}_p$.

Lean: `New.Period.exists_algebraic_of_fixed_near_one` (Lib/PadicHodge/PeriodRings/AxTheorem.lean).

*Proof.* A neighbourhood of $1$ in the Krull topology contains the subgroup $\mathrm{Gal}(\overline{\mathbb{Q}}_p/E)$ for a finite extension $E$ of $\mathbb{Q}_p$. By the theorem of Ax, $x$ lies in the closure of $E$. A finite dimensional subspace of a normed space over the complete field $\mathbb{Q}_p$ is closed, so $x \in E$. $\square$

**Remark (Formalization).** The text writes $x \in \overline{\mathbb{Q}}_p$ for an element of $\mathbb{C}_p$ in the image of $\overline{\mathbb{Q}}_p$. In Lean, $\mathbb{C}_p$ is the completion of $\overline{\mathbb{Q}}_p$ (`PadicAlgCl p`), and the corollary gives `∃ y, x = coe' y`. The docstring of `Lib/PadicHodge/TateSen.lean` records that Ax's theorem comes "without the constant". So the source does not have the quantitative form that some proofs of the Sen theory use. No later file needs it.

### The normalized trace

**Proposition (Tate).** There is a constant $C$, depending only on $p$, such that every $z$ in $\mathbb{Q}_p(\mu_{p^\infty})$ has $|\mathrm{Tr}(z)| \leq C|z|$, where $\mathrm{Tr}$ is the normalized trace to $\mathbb{Q}_p$.

This is in J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966), Springer (1967), Section 3.

Lean: `New.Period.exists_norm_normalizedTrace_le` (Lib/PadicHodge/TateSen.lean).

The normalized trace of $z$ is $[E:\mathbb{Q}_p]^{-1}\mathrm{Tr}_{E/\mathbb{Q}_p}(z)$ for any finite extension $E$ that contains $z$. It does not depend on $E$. In Lean, $\mathbb{Q}_p(\mu_{p^\infty})$ is the fixed field in $\overline{\mathbb{Q}}_p$ of the kernel of $\chi$.

*Proof.* A private lemma of the file first bounds the normalized trace of every root of unity of $p$-power order by a constant $C$. Let $z \in \mathbb{Q}_p(\mu_{p^\infty})$. The source uses compactness to find a primitive root of unity $\zeta$ of order $p^{n+1}$ such that $z \in \mathbb{Q}_p(\zeta)$. Put $\pi = \zeta - 1$ and $e = \varphi(p^{n+1})$. Then $\|\pi\|^e = |p|$, and $z = \sum_{i<e} a_i \pi^i$ with $a_i \in \mathbb{Q}_p$. The norms of the nonzero terms are distinct, since their exponents in $\|\pi\|$ differ modulo $e$. So each term has norm at most $\|z\|$. By the binomial theorem, $\pi^i$ is an integer combination of powers of $\zeta$, so $|\mathrm{Tr}(\pi^i)| \leq C$. Hence $|\mathrm{Tr}(a_i\pi^i)| \leq |a_i|\,C \leq C p\,\|a_i\pi^i\| \leq Cp\,\|z\|$, because $\|\pi\|^i \geq \|\pi\|^e = p^{-1}$. The constant of the proposition is $Cp$. $\square$

### The theorem of Tate

**Theorem (Tate).** For every open subgroup $U$ of $G_p$ and every integer $n \neq 0$, $H^0(U, \mathbb{C}_p(n)) = 0$.

This is in Tate, *p-divisible groups*, Section 3.

The source proves it in two steps. The first step is the case $U = G_p$.

**Theorem.** Let $y \in \mathbb{C}_p$ and $n \neq 0$, and assume $gy = \chi(g)^n y$ for every $g \in G_p$. Then $y = 0$.

Lean: `New.Period.eq_zero_of_smul_eq_cyclotomicGp_zpow_smul` (Lib/PadicHodge/TateSen.lean).

*Proof.* Let $H = \ker\chi$ and let $C$ be the constant of the proposition. Fix $\gamma \in G_p$. For every algebraic $w$ fixed by $H$, the element $1 - (\gamma w - w)$ is fixed by $H$, because $H$ is normal, and its normalized trace is $1$. The proposition gives $1 \leq C\,\|1 - (\gamma w - w)\|$. The theorem of Ax extends this inequality to every $z \in \mathbb{C}_p$ fixed by $H$, because the set of $z$ that satisfy it is closed:
$$1 \leq C\,\|1 - (\gamma z - z)\| \quad \text{for all } z \in \mathbb{C}_p^H. \qquad (*)$$

Assume $y \neq 0$. Then $y^{-1}$ is fixed by $H$. It is enough to show $1 \leq C\,\|1 - yw\|$ for every algebraic $w$ fixed by $H$. By the theorem of Ax this inequality then holds at $w = y^{-1}$, where the right side is $0$, which is a contradiction.

So let $w$ be algebraic and fixed by $H$. The source chooses $\gamma_0$ in the inertia group with $\chi(\gamma_0) = p + 1$. The stabilizer of $w$ is open, so some power $\delta = \gamma_0^N$ with $N \geq 1$ fixes $w$. The number $a = \chi(\delta)^n = (p+1)^{Nn}$ is not $1$. Put $z = (a-1)^{-1} yw$. Then $z$ is fixed by $H$, and
$$\delta z - z = (a - 1)^{-1}(a\,yw - yw) = yw.$$
Now $(*)$ with $\gamma = \delta$ gives $1 \leq C\,\|1 - yw\|$. $\square$

The second step passes to open subgroups by Galois descent.

**Theorem.** Let $x \in \mathbb{C}_p$ and let $u \neq v$ be integers. Assume that $\chi(g)^u\, gx = \chi(g)^v x$ for every $g$ in a neighbourhood of $1$ in $G_p$. Then $x = 0$.

Lean: `New.Period.tate_eq_zero_of_cyclotomicGp_twist` (Lib/PadicHodge/TateSen.lean).

*Proof.* Choose an open subgroup $U$ on which the relation holds. Let $G_p$ act on $\mathbb{C}_p$ by $g \ast y = \chi(g)^{u - v} gy$. This action is semilinear over $\overline{\mathbb{Q}}_p$, and $x$ is fixed by $U$. By Galois descent for the finite extension cut out by $U$, $x$ is a $\overline{\mathbb{Q}}_p$-linear combination of elements fixed by all of $G_p$ for the twisted action. Each such element $y$ satisfies $gy = \chi(g)^{v-u} y$ for all $g$, so it is $0$ by the first step. $\square$

**Remark (Formalization).** The source states and proves Tate's theorem for $H^0$ only, as the docstring of `Lib/PadicHodge/TateSen.lean` says. The textbook form also contains $H^1(G_K, \mathbb{C}_p(n)) = 0$ for $n \neq 0$, and $H^1(G_K, \mathbb{C}_p)$ of dimension $1$ over $K$. No file of the period rings uses these. The hypothesis "for every $g$ in a neighbourhood of $1$" is a filter condition, `∀ᶠ g in nhds 1`. It is the form in which the later files apply the theorem, to a representation of a group $\Gamma$ with $j : \Gamma \to G_p$ of open image.

### Ax-Sen-Tate for a group over G_p

**Theorem.** Let $j : \Gamma \to G_p$ have open image, and let $K$ be the fixed field of $j(\Gamma)$ in $\overline{\mathbb{Q}}_p$. An element $x \in \mathbb{C}_p$ is fixed by every $j(g)$ if and only if $x \in K$.

Lean: `New.Period.forall_smul_eq_iff_mem_localFieldOf` (Lib/PadicHodge/TateSen.lean), `New.Period.localFieldOf`, `New.Period.OverGp`.

*Proof.* The image $j(\Gamma)$ is an open subgroup, so it is a neighbourhood of $1$. The corollary to the theorem of Ax gives that $x$ is algebraic, and then $x \in K$ by definition. The converse is clear. $\square$

The class `New.Period.OverGp` packages the homomorphism $j$ (`toGp`) with the fact that its range is open. The filter `New.Period.nearOne` on $\Gamma$ is the pull-back along $j$ of the neighbourhoods of $1$. Since the image is open, its image under $j$ is the filter of neighbourhoods of $1$ (`New.Period.nhds_one_le_map_nearOne`). This is how a statement "for $g$ near $1$ in $\Gamma$" becomes a statement on $G_p$, without a topology on $\Gamma$.

### Elimination

Sections 5 and 6 need to find, in a subspace $W$ of $\mathbb{C}_p^d$ that is stable under a twisted Galois action, enough vectors that are algebraic and Galois-fixed. The source does this with an elimination on supports.

**Lemma (Elimination).** Let $A$ be a commutative ring and $b$ a basis of an $A$-module $V$, with coordinates $b_i$. Let $W, W'$ be submodules of $V$. Assume the following for every nonzero $v \in W$ such that every $y \in W$ with support inside the support of $v$ is proportional to $v$, in the sense $b_k(v)\,y = b_k(y)\,v$ for all $k$: there is $u \in W \cap W'$ with support inside the support of $v$ and with some coordinate equal to $1$. Then $W \subseteq W'$.

Lean: `New.Period.le_of_echelon` (Lib/PadicHodge/TateSen.lean).

*Proof.* By induction on the support. If $y$ has support inside that of $w$ and $b_k(w) \neq 0$, then $b_k(y)w - b_k(w)y$ has strictly smaller support. This gives, first, a vector $u$ as in the hypothesis for every nonzero $w \in W$, without the proportionality condition. Then subtract $b_k(w)u$ from $w$ to lower the support of $w$. $\square$

**Theorem (Hodge-Tate elimination).** Let $\iota$ be finite and $u : \iota \to \mathbb{Z}$. Let $F$ be a filter on $G_p$ finer than the neighbourhoods of $1$. Let $W$ be a $\mathbb{C}_p$-subspace of $\mathbb{C}_p^\iota$ such that, for each $a \in W$, the vector $(\chi(g)^{u_i}\, g a_i)_i$ lies in $W$ for $g$ eventually along $F$. Let $W'$ be a subspace that contains each $a \in W \cap \overline{\mathbb{Q}}_p^\iota$ for which some $k$ has: $\|a_i\| \leq 1$ for all $i$; $a_i = 0$ whenever $u_i \neq u_k$; $a_k = 1$; and each $a_i$ is fixed by $g$ eventually along $F$. Then $W \subseteq W'$.

Lean: `New.Period.le_of_hodgeTate_stable` (Lib/PadicHodge/TateSen.lean).

*Proof.* Apply the elimination lemma to the standard basis. Let $v$ be as there, and divide $v$ by a coordinate $v_k$ of largest norm, to get $w$ with $w_k = 1$ and $\|w_i\| \leq 1$. The twisted conjugate of $w$ lies in $W$ and has support inside that of $w$, so it is proportional to $w$. Reading the factor at the coordinate $k$ gives $\chi(g)^{u_i} g w_i = \chi(g)^{u_k} w_i$ for $g$ along $F$. If $u_i \neq u_k$, the theorem of Tate gives $w_i = 0$. If $u_i = u_k$, then $w_i$ is fixed by $g$ near $1$, and the corollary to the theorem of Ax gives $w_i \in \overline{\mathbb{Q}}_p$. So $w$ is a vector as in the hypothesis on $W'$. $\square$

This is the step where the source uses Tate and Ax together.

**Example.** Take $\iota = \{1, 2\}$, $u = (0, 1)$ and $W$ the line spanned by $(1, c)$ for some $c \in \mathbb{C}_p$. The twisted conjugate of $(1, c)$ is $(1, \chi(g)\, gc)$. It lies in $W$ only if $\chi(g)\,gc = c$. For $g$ near $1$, Tate's theorem with $u = 1$, $v = 0$ then gives $c = 0$. So a stable line in $\mathbb{C}_p \oplus \mathbb{C}_p(1)$ lies in one of the two factors, and the theorem finds the algebraic generator $(1, 0)$ of $W$.
