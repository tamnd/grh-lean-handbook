---
title: Block averages, Mackey's formula and the adjunction
lean:
  - Lib/LocalGL/Green/HallAlgebra.lean
  - Lib/General/Groups/CharacterTheory.lean
decls:
  - New.Hall.blockAverage
  - New.Hall.IsCuspidal
  - New.Hall.rankInner
  - New.Hall.skew
  - New.Hall.blockAverage_mul
  - New.Hall.rankInner_mul_eq_sum_skew
  - New.Hall.rankInner_mul_eq_rankInner_skew
  - New.Hall.rankInner_mul_of_isCuspidal
  - New.Hall.skew_of_isCuspidal
  - New.Hall.skew_mul
  - New.classInner_evalGL_prod
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Block averages, Mackey's formula and the adjunction

Parabolic induction has an adjoint: the mean over a unipotent radical, which is Harish-Chandra restriction. This section defines it on the ring $\mathcal{H}(k)$ as a block average, proves Mackey's formula for the block average of a product, and proves the adjunction with the inner products of the groups $\mathrm{GL}_n(k)$. The section ends with the consequence that Section 5 uses most: a cuspidal function acts on $\mathcal{H}(k)$ by a derivation.

### Block averages and cuspidal functions

Let $a$ be an endomorphism of $V$ and $b$ an endomorphism of $W$. For a linear map $x : W \to V$, the *block map* $g_{a,b,x}$ is the endomorphism $(w, v) \mapsto (bw, xw + av)$ of $W \times V$. The subspace $0 \times V$ is stable. The restriction to it is $a$, and the map on the quotient $W$ is $b$. In a basis adapted to $0 \times V$, the matrix of $g_{a,b,x}$ is block triangular with diagonal blocks $a$ and $b$ and corner block $x$.

**Definition (Block average, cuspidal).** For $F \in \mathcal{H}(k)$ and classes $a, b$, the *block average* is
$$\delta F(a, b) = \frac{1}{|\mathrm{Hom}(W, V)|} \sum_{x \in \mathrm{Hom}(W, V)} F([g_{a,b,x}]),$$
for any endomorphisms in the classes $a$ and $b$. The function $F$ is *cuspidal* if $\delta F(a, b) = 0$ whenever $\dim a \neq 0$ and $\dim b \neq 0$.

Lean: `New.Hall.blockAverage`, `New.Hall.IsCuspidal`, `New.blockTriangularEnd`, `New.Hall.blockAverage_simClassOf` (Lib/LocalGL/Green/HallAlgebra.lean).

The block average does not depend on the chosen endomorphisms: an isomorphism of $V$ and one of $W$ change $x$ by a bijection of $\mathrm{Hom}(W, V)$. For each class $a$, the function $b \mapsto \delta F(a, b)$ is an element of $\mathcal{H}(k)$, which this chapter writes $\delta F(a, \cdot)$.

For invertible $a$ and $b$, the block maps $g_{a,b,x}$ form the coset $(b, a) U$ of the unipotent radical $U$ of a parabolic subgroup, and $\delta F(a, b)$ is the mean of $F$ over this coset. This is the value at $(a, b)$ of the Harish-Chandra restriction of $F$ to the Levi subgroup. So the definition agrees with the classical notion of a cuspidal class function on $\mathrm{GL}_n(k)$ (see Springer, Sém. Bourbaki 441, Section 1, which the source cites).

**Lemma (A block of dimension $0$).** If $\dim o = 0$, then $\delta F(o, a) = F(a)$ and $\delta F(a, o) = F(a)$ for every class $a$.

Lean: `New.Hall.blockAverage_of_dim_eq_zero` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* There is one map $x$, the zero map, and the block map is $a$ on $W \times 0$ or on $0 \times V$. $\square$

### Mackey's formula

**Theorem (Mackey's formula).** Let $a$ be an endomorphism of $V$ and $b$ an endomorphism of $W$. For $F, H \in \mathcal{H}(k)$,
$$\delta(F * H)([a], [b]) = \sum_{A} \bigl(\delta F([a|_A], \cdot) * \delta H([a|_{V/A}], \cdot)\bigr)([b]),$$
where $A$ runs over the $a$-stable subspaces of $V$.

Lean: `New.Hall.blockAverage_mul` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* By the definition of the product, the right side is the sum over the $a$-stable $A \leq V$ and the $b$-stable $B \leq W$ of $\delta F([a|_A], [b|_B]) \, \delta H([a|_{V/A}], [b|_{W/B}])$. The left side is the mean over $x$ of a sum over the $g_x$-stable subspaces $U$ of $W \times V$, with $g_x = g_{a,b,x}$. Sort these $U$ by $A = \{v : (0, v) \in U\}$ and by the image $B$ of $U$ in $W$. Both are stable. For fixed $A$ and $B$, the subspaces $U$ are the graphs $U_s = \{(w, v) : w \in B, \ v + A = s(w)\}$ of the linear maps $s : B \to V/A$. Write $\pi : V \to V/A$ and $\bar a = a|_{V/A}$. The subspace $U_s$ is $g_x$-stable exactly when
$$\pi \circ x|_B = s \circ b|_B - \bar a \circ s. \tag{1}$$
Let $S$ be the set of pairs $(x, s)$ that satisfy (1). For each $s$, condition (1) fixes $\pi \circ x|_B$, so $S$ has exactly $|\mathrm{Hom}(W, V)|$ elements. Fix a lift $\tilde s : B \to V$ of $s$. In the coordinates $(w, \alpha) \mapsto (w, \tilde s(w) + \alpha)$ on $U_s \cong B \times A$, the restriction $g_x|_{U_s}$ is the block map with blocks $a|_A$ and $b|_B$ and corner $y_1 = x|_B + a \tilde s - \tilde s b$, which takes values in $A$ by (1). The quotient $(W \times V)/U_s$ contains $(0 \times V + U_s)/U_s \cong V/A$ with the map $\bar a$, and the quotient by this subspace is $W/B$ with the map $b|_{W/B}$. So the map induced by $g_x$ is a block map with blocks $\bar a$ and $b|_{W/B}$ and a corner $y_2 : W/B \to V/A$. The map $(x, s) \mapsto (y_1, y_2)$ is affine on $S$, and it is onto $\mathrm{Hom}(B, A) \times \mathrm{Hom}(W/B, V/A)$: the values of $x$ on $B$ inside $A$ give every $y_1$, and the values of $\pi \circ x$ on a complement of $B$ give every $y_2$. So all its fibres have the same size. Thus the mean over $x$ of the terms with these $A$ and $B$ is the product of the two block averages. $\square$

### Inner products and the adjunction

**Definition (Inner products).** For a finite group $G$ and functions $f, h : G \to \mathbb{C}$, put $\langle f, h \rangle_G = |G|^{-1} \sum_{g} \overline{f(g)} h(g)$. For $F, H \in \mathcal{H}(k)$ and $n \geq 0$, put
$$\langle F, H \rangle_n = \frac{1}{|\mathrm{GL}_n(k)|} \sum_{g \in \mathrm{GL}_n(k)} \overline{F([g])} \, H([g]).$$
For $d \geq 0$ and $f, F \in \mathcal{H}(k)$, the *skew* of $F$ by $f$ in rank $d$ is the element $\partial^d_f F$ of $\mathcal{H}(k)$ with
$$\partial^d_f F(a) = \langle f, \delta F(a, \cdot) \rangle_d = \frac{1}{|\mathrm{GL}_d(k)|} \sum_{b \in \mathrm{GL}_d(k)} \overline{f([b])} \, \delta F(a, [b]).$$

Lean: `New.Hall.rankInner`, `New.Hall.skew`, `New.classInner`, `New.finMean`, `New.Hall.classInner_evalGL` (Lib/LocalGL/Green/HallAlgebra.lean, Lib/General/Groups/CharacterTheory.lean).

For a finite set $I$ with $n$ elements, $\langle F|_{\mathrm{GL}_I}, H|_{\mathrm{GL}_I} \rangle_{\mathrm{GL}_I(k)} = \langle F, H \rangle_n$. For $n = 0$ the group is trivial and $\langle F, H \rangle_0 = \overline{F(o)} H(o)$, where $o$ is the class of dimension $0$. In particular $\langle \mathbb{1}, H \rangle_0 = H(o)$.

**Theorem (Adjunction).** For $A, B, X \in \mathcal{H}(k)$ and $n \geq 0$,
$$\langle A * B, X \rangle_n = \sum_{p + q = n} \langle A, \partial^q_B X \rangle_p.$$

Lean: `New.Hall.rankInner_mul_eq_sum_skew` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* Let $G = \mathrm{GL}_n(k)$ and $V = k^n$. By the definition of the product,
$$|G| \, \langle A * B, X \rangle_n = \sum_{g \in G} \sum_{W} \overline{A([g|_W])} \, \overline{B([g|_{V/W}])} \, X([g]),$$
where $W$ runs over the $g$-stable subspaces. Exchange the sums. For each $p$, the group $G$ permutes the subspaces of dimension $p$ transitively. Let $W_0$ be one of them and $P$ its stabilizer, so there are $|G|/|P|$ of them. The pairs $(g, W)$ with $\dim W = p$ contribute $(|G|/|P|) \sum_{g \in P} \overline{A([g|_{W_0}])} \, \overline{B([g|_{V/W_0}])} \, X([g])$. The group $P$ is the set of block maps $g_{a,b,x}$ with $a \in \mathrm{GL}(W_0)$, $b \in \mathrm{GL}(V/W_0)$ and $x$ arbitrary, after a choice of complement. So the mean over $P$ is the mean over $a \in \mathrm{GL}_p(k)$ of $\overline{A([a])}$ times the mean over $b \in \mathrm{GL}_q(k)$ of $\overline{B([b])} \, \delta X([a], [b])$. This is $\langle A, \partial^q_B X \rangle_p$. $\square$

**Corollary (Adjunction in one degree).** Let $f \in \mathcal{H}(k)$ vanish on the classes of dimension different from $d$. Then for all $H, F$ and $n$, $\langle f * H, F \rangle_{d+n} = \langle H, \partial^d_f F \rangle_n$.

Lean: `New.Hall.rankInner_mul_eq_rankInner_skew` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* Write $f * H = H * f$ and apply [the adjunction](/decl/New.Hall.rankInner_mul_eq_sum_skew/) with $A = H$ and $B = f$. For $q \neq d$ the function $f$ vanishes on $\mathrm{GL}_q(k)$, so $\partial^q_f F = 0$. $\square$

### Cuspidal functions act by derivations

**Theorem (Leibniz rule for the pairing).** Let $c \in \mathcal{H}(k)$ be cuspidal and $d \neq 0$. For all $F, H \in \mathcal{H}(k)$,
$$\langle c, F * H \rangle_d = \langle c, F \rangle_d \, \langle \mathbb{1}, H \rangle_0 + \langle \mathbb{1}, F \rangle_0 \, \langle c, H \rangle_d.$$

Lean: `New.Hall.rankInner_mul_of_isCuspidal` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* The left side is the conjugate of $\langle F * H, c \rangle_d = \sum_{p+q=d} \langle F, \partial^q_H c \rangle_p$, by [the adjunction](/decl/New.Hall.rankInner_mul_eq_sum_skew/). The term of $(p, q)$ involves $\delta c(a, b)$ with $\dim a = p$ and $\dim b = q$. Since $c$ is cuspidal, it vanishes unless $p = 0$ or $q = 0$. As $d \neq 0$, the two remaining terms $(d, 0)$ and $(0, d)$ are distinct. By the lemma on a block of dimension $0$, $\partial^0_H c = \overline{H(o)} \, c$ and $\partial^d_H c(o) = \langle H, c \rangle_d$. So the two terms are $\overline{H(o)} \langle F, c \rangle_d$ and $\overline{F(o)} \langle H, c \rangle_d$. Take conjugates and use $\langle \mathbb{1}, H \rangle_0 = H(o)$. $\square$

**Corollary (Skew of a cuspidal function).** Let $c$ be cuspidal and $d \neq 0$. For every $f \in \mathcal{H}(k)$, $\partial^d_f c = \langle f, c \rangle_d \cdot 1$.

Lean: `New.Hall.skew_of_isCuspidal` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* At the class $o$ of dimension $0$, $\delta c(o, \cdot) = c$, so $\partial^d_f c(o) = \langle f, c \rangle_d$. At a class $a$ with $\dim a \neq 0$, $\delta c(a, b) = 0$ for every $b$ of dimension $d \neq 0$, so $\partial^d_f c(a) = 0 = 1(a)$. $\square$

**Theorem (Skew by a cuspidal function is a derivation).** Let $c$ be cuspidal and $d \neq 0$. For all $F, H \in \mathcal{H}(k)$,
$$\partial^d_c (F * H) = (\partial^d_c F) * H + F * (\partial^d_c H).$$

Lean: `New.Hall.skew_mul` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* Evaluate at an endomorphism $g$ of $V$. By [Mackey's formula](/decl/New.Hall.blockAverage_mul/), $\delta(F * H)([g], \cdot)$ is the sum over the $g$-stable $W$ of $\delta F([g|_W], \cdot) * \delta H([g|_{V/W}], \cdot)$. Apply $\langle c, \cdot \rangle_d$ to each term and use [the Leibniz rule](/decl/New.Hall.rankInner_mul_of_isCuspidal/). The term of $W$ becomes $\partial^d_c F([g|_W]) \, H([g|_{V/W}]) + F([g|_W]) \, \partial^d_c H([g|_{V/W}])$, since $\delta F([g|_W], o) = F([g|_W])$. The sum over $W$ of this is the right side at $[g]$. $\square$

The source attributes this rule to Zelevinsky's structure of a positive self-adjoint Hopf algebra on the class functions of the groups $\mathrm{GL}_n(k)$. The source proves only the Leibniz rule and does not set up the Hopf algebra.

### Frobenius reciprocity

The last result of the section unfolds a product of several factors into a mean over a parabolic subgroup. Let $n$ be a finite set with a map $\lambda : n \to \iota$ to a finite totally ordered set of levels. The *parabolic subgroup* $P_\lambda \subset \mathrm{GL}_n(k)$ is the group of invertible matrices that are block upper triangular for $\lambda$, and $g \mapsto g_i$ is the projection onto the diagonal block of level $i$.

**Theorem (Frobenius reciprocity).** Let $s$ be a finite set of levels that contains $\lambda(n)$, let $F_i \in \mathcal{H}(k)$ for $i \in s$, let $n_i$ be the number of indices of level $i$, and let $Y$ be a class function on $\mathrm{GL}_n(k)$. Then
$$\Bigl\langle \Bigl(\prod_{i \in s} [F_i]_{n_i}\Bigr)\Big|_{\mathrm{GL}_n}, \, Y \Bigr\rangle_{\mathrm{GL}_n(k)} = \Bigl\langle g \mapsto \prod_{i \in s} F_i([g_i]), \ Y|_{P_\lambda} \Bigr\rangle_{P_\lambda}.$$

Lean: `New.classInner_evalGL_prod`, `New.parabolic`, `New.blockHom`, `New.exists_eq_evalGL` (Lib/LocalGL/Green/HallAlgebra.lean, Lib/General/Groups/BesselGroups.lean).

*Proof.* Every class function $Y$ is the restriction of some $X \in \mathcal{H}(k)$. Use induction on the number of levels. Split off the largest level $i$ with $n_i \neq 0$ and apply [the adjunction in one degree](/decl/New.Hall.rankInner_mul_eq_rankInner_skew/) with $f = [F_i]_{n_i}$. The skew $\partial^{n_i}_f X$ is the mean over the last diagonal block and over the corner blocks of that level. The inductive hypothesis, applied to the remaining levels and to the restriction of this skew, gives the mean over the remaining blocks. Together these means are the mean over $P_\lambda$, since $P_\lambda$ is the product of its Levi subgroup and its unipotent radical. $\square$

The formula is the classical statement that $\prod_i [F_i]_{n_i}$ is induced from the inflation of $\otimes_i F_i$ to $P_\lambda$. Section 6 uses it to induce characters of semidirect products from parabolic subgroups.
