---
title: Floors and the Bessel subgroup
lean:
  - Lib/DiscreteSeries/Bruhat/FloorGroups.lean
  - Lib/DiscreteSeries/Bessel/Basic.lean
decls:
  - New.Shape
  - New.Shape.Form.splitGram
  - New.Shape.Form.frameGram
  - New.Shape.Form.besselU
  - New.Shape.Form.besselU0
  - New.Shape.Form.floorGroup
  - New.Shape.Form.unipotentBelow
  - New.Shape.Form.partialUnitriangularGroup
  - New.Shape.Form.besselS
  - New.Filling.mem_besselS_iff_frameImage
  - New.besselS_le_normalizer_besselU
  - New.exists_eq_toBesselH
  - New.simpleRootSum
  - New.simpleRootSum_mul
  - New.div_mem_unitaryLevel_of_besselU_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Floors and the Bessel subgroup

This section fixes the hermitian space, its basis, the levels and floors, and the groups of the chapter. It proves that the Bessel subgroup $S$ normalises its unipotent part $\mathsf U$, that the sum of the simple root entries is an additive character of $S$, and that the definite factor $H$ of $S$ is a compact unitary group $U(k)$. The last result controls the factor $H$ of an element of $\mathsf U H$ in a congruence subgroup.

### The space and its basis

Let $A$ be a commutative ring with an involution $a \mapsto \bar a$. For a square matrix $J$ over $A$, the unitary group is $U(J) = \{ g \in GL_n(A) : g^* J g = J \}$, where $g^* = \bar g^{\mathsf T}$. The form is $h(x, y) = x^* J y$.

**Definition.** A *shape* $\mathfrak s$ is a number $\varrho \ge 0$, a finite set $\kappa$, and an element $k_0 \in \kappa$. Put $k = |\kappa|$, $n = \varrho + 1$ and $r = 2\varrho + k + 1$. The basis of the space is
$$e_0, \dots, e_{\varrho - 1}, \quad x_i \ (i \in \kappa), \quad z, \quad e^*_0, \dots, e^*_{\varrho - 1}.$$
The *middle block* is spanned by the $x_i$ and $z$. The *frame* is $f = (f_0, \dots, f_\varrho) = (e_0, \dots, e_{\varrho - 1}, z)$.

Lean: `New.Shape` (Lib/General/Groups/BesselGroups.lean).

A middle form $T$ is a matrix on the middle block. The main example is $T = \operatorname{diag}(1, \dots, 1, -N)$, with $1$ at each $x_i$ and $-N$ at $z$. The source writes it as `New.Shape.middleGram`.

**Definition.** The *split form* of $T$ is the Gram matrix $J_T$ with $h(e_a, e^*_b) = \delta_{ab}$, with $T$ on the middle block, and with all other products of basis vectors zero. Its unitary group is written $G_T = U(J_T)$.

Lean: `New.Shape.Form.splitGram` (Lib/General/Groups/BesselGroups.lean).

So the space is $\varrho$ hyperbolic planes $\langle e_a, e^*_a \rangle$ plus the middle block. Over $\mathbb C$ with $N = 1$ the form has signature $(\varrho + k, \varrho + 1)$, and the source writes $G_1$ and $J_1$ for this group and its form.

**Definition.** For $\gamma \in G_T$ the *frame matrix* is the $(\varrho + 1) \times (\varrho + 1)$ matrix
$$Z(\gamma)_{jl} = h(f_j, \gamma f_l), \qquad 0 \le j, l \le \varrho.$$
For $0 \le l \le \varrho + 1$, $\delta_l(\gamma)$ is its leading principal minor of order $l$, with $\delta_0 = 1$.

Lean: `New.Shape.Form.frameGram` (Lib/General/Groups/BesselGroups.lean).

Since $h(e_a, y)$ is the coefficient of $e^*_a$ in $y$, the first $\varrho$ rows of $Z(\gamma)$ read the coefficients of $\gamma f_l$ at $e^*_0, \dots, e^*_{\varrho - 1}$. For $T = \operatorname{diag}(1_\kappa, -N)$, $h(z, y)$ is $-N$ times the coefficient of $z$ in $y$.

### Levels and floors

The *level* of a basis vector is $a$ at $e_a$, $\varrho$ on the middle block, and $2\varrho - a$ at $e^*_a$. So the levels increase along the order $e_0, e_1, \dots, e_{\varrho - 1}$, middle block, $e^*_{\varrho - 1}, \dots, e^*_0$. The *floor* is $a$ at both $e_a$ and $e^*_a$, $\varrho$ at $z$ and $\varrho + 1$ at each $x_i$. The floor of the frame vector $f_b$ is $b$.

A matrix $g$ is *unitriangular* for a function $\lambda$ on the indices if $g_{ij} = \delta_{ij}$ whenever $\lambda(j) \le \lambda(i)$. So $g$ is block upper triangular for $\lambda$, with identity blocks on the diagonal.

**Definition.** The *Bessel unipotent group* $\mathsf U$ is the group of $u \in G_T$ that are unitriangular for the level. Its subgroup $\mathsf U^0 = \mathsf U \cap \operatorname{Fix}(f)$ consists of the $u \in \mathsf U$ with $u f_b = f_b$ for each $b$.

Lean: `New.Shape.Form.besselU`, `New.Shape.Form.besselU0` (Lib/General/Groups/BesselGroups.lean).

An element $u \in \mathsf U$ acts as the identity on the middle block modulo $\langle e_0, \dots, e_{\varrho - 1} \rangle$. It sends $e_a$ into $e_a + \langle e_0, \dots, e_{a-1} \rangle$. So $\mathsf U$ is the unipotent radical of the parabolic subgroup that fixes the isotropic flag $\langle e_0 \rangle \subset \langle e_0, e_1 \rangle \subset \cdots \subset \langle e_0, \dots, e_{\varrho - 1}\rangle$.

**Definition.** For $l \ge 0$:

1. $H_l$ is the group of $g \in G_T$ that fix every basis vector of floor below $l$.
2. $\mathcal N_{<l}$ is the group of $g \in G_T$ that are unitriangular for the function equal to the level on the floors below $l$ and to $\varrho$ on the other floors.
3. $\mathcal N_l = H_l \cap \mathcal N_{<l+1}$.
4. $Q_l$ is the group of $g \in G_T$ with $g_{ij} = \delta_{ij}$ at every entry where $\operatorname{level}(j) \le \operatorname{level}(i)$ and the column $j$ has floor and level below $l$. If $l > n$, the condition is required at every entry with $\operatorname{level}(j) \le \operatorname{level}(i)$.

Lean: `New.Shape.Form.floorGroup`, `New.Shape.Form.unipotentBelow`, `New.Floors.FloorGroups.floorUnipotent`, `New.Shape.Form.partialUnitriangularGroup` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

The groups $H_l$ decrease. $H_0 = G_T$, and $H_l$ is trivial for $l \ge \varrho + 2$ (Lean: `New.Floors.FloorGroups.floorGroup_zero`, `New.Floors.FloorGroups.floorGroup_eq_bot`). An element of $H_l$ also agrees with $1$ in the rows of the pairs of floor below $l$, since it preserves the form. So $H_\varrho$ is the unitary group of the middle block. The groups $\mathcal N_{<l}$ increase, and $\mathcal N_{<l} = \mathsf U$ for $l \ge \varrho$ (Lean: `New.Floors.FloorGroups.unipotentBelow_eq_besselU`). The groups $Q_l$ decrease, and $Q_{\varrho + 2} = \mathsf U$ (Lean: `New.Floors.FloorGroups.partialUnitriangularGroup_add_two_eq_besselU`). An element of $Q_l$ is unitriangular on the first $l$ frame vectors: for $b < l$, $g f_b \in f_b + \langle e_0, \dots, e_{b-1} \rangle$.

**Definition.** The *Bessel subgroup* is $S = Q_{\varrho + 1}$. Its *definite factor* is $H = H_{\varrho + 1}$, the fixer of all basis vectors except the $x_i$.

Lean: `New.Shape.Form.besselS`, `New.Shape.Form.besselH` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

The frame vectors are exactly the basis vectors with floor and level at most $\varrho$. So the definition says this.

**Lemma.** An element $s \in G_T$ lies in $S$ if and only if, for every frame vector $f_a$ and every basis index $i$ with $a \le \operatorname{level}(i)$, the coefficient of $s f_a$ at $i$ equals that of $f_a$. Equivalently, $s f_a - f_a$ lies in $\langle e_0, \dots, e_{a-1} \rangle$ for every $a \le \varrho$.

Lean: `New.Filling.mem_besselS_iff_frameImage` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

*Proof.* The basis indices of floor and level below $\varrho + 1$ are the $e_a$ and $z$, that is the frame vectors, and the level of $f_a$ is $a$. So the condition that defines $Q_{\varrho+1}$ is the condition of the lemma. The indices of level below $a$ are $e_0, \dots, e_{a-1}$. $\square$

In the language of Gan, Gross and Prasad (Astérisque 346 (2012), §12), $S = \mathsf U \rtimes H$ is the Bessel subgroup attached to the subspace $\langle x_i \rangle$ of odd codimension $2\varrho + 1$. The source proves the decomposition $S = \mathsf U H$ with the Heisenberg groups of the next section: [Lemma](/decl/New.mem_besselS/).

### The Bessel subgroup normalises $\mathsf U$

**Proposition.** $S$ normalises $\mathsf U$.

Lean: `New.besselS_le_normalizer_besselU` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

*Proof.* For $m \ge 0$ let $F_m$ be the span of the basis vectors of level at most $m$. An isometry $u$ lies in $\mathsf U$ if and only if $(u - 1) F_m \subset F_{m-1}$ for every $m$. So it is enough to prove that every $s \in S$ preserves each $F_m$. Then $s^{-1}$ also preserves each $F_m$, and $(s u s^{-1} - 1) F_m = s (u - 1) s^{-1} F_m \subset s F_{m-1} = F_{m-1}$.

For $m < \varrho$, $F_m = \langle e_0, \dots, e_m \rangle$, and $s e_a \in e_a + F_{a-1}$ by the lemma. For $m \ge \varrho$, the vectors orthogonal to $F_m$ are spanned by the $e_a$ with $e^*_a \notin F_m$, that is with $2\varrho - a > m$. So $F_m^\perp = F_{2\varrho - m - 1}$, a space of the first kind. The form is nondegenerate, so $F_m = (F_{2\varrho - m - 1})^\perp$. The isometry $s$ preserves $F_{2\varrho - m - 1}$, so it preserves its orthogonal complement. $\square$

The source proves the same statement entry by entry: $s$ is block upper triangular for the level, and conjugation by a block triangular matrix keeps the unitriangular group (Lean: `New.conj_mem_unitriangular`).

### The definite factor is a compact unitary group

Let $\iota : U(1_\kappa) \to G_T$ extend a unitary $\kappa \times \kappa$ matrix by the identity on the other basis vectors. Its image lies in $H$ (Lean: `New.toBesselH`, `New.toBesselH_mem`).

**Lemma.** Let $T = \operatorname{diag}(1_\kappa, -N)$ with $N$ a unit of $A$. Every $h \in H$ equals $\iota(m)$ for some $m \in U(1_\kappa)$.

Lean: `New.exists_eq_toBesselH` (Lib/DiscreteSeries/Bessel/Basic.lean).

*Proof.* The columns of $h$ outside $\kappa$ are those of $1$, and its rows of the hyperbolic pairs are those of $1$. So $h$ differs from $1$ only in the columns $x_a$, at the rows $x_b$ and $z$. Read $h^* J_T h = J_T$ at the entry $(z, x_a)$: it gives $-N \cdot \overline{h_{z z}} h_{z x_a} = 0$ with $h_{zz} = 1$, so $h_{z x_a} = 0$ since $N$ is a unit. Read it at $(x_a, x_b)$: the block $m = (h_{x_a x_b})$ satisfies $m^* m = 1$. $\square$

With [Lemma](/decl/New.mem_besselS/) of the next section this gives the form used in Theorem B: if $A$ has an element $\tau$ with $\tau + \bar\tau = 1$, $J_T$ is hermitian and invertible and $N$ is a unit, every $s \in S$ is $u \cdot \iota(m)$ with $u \in \mathsf U$ and $m \in U(1_\kappa)$ (Lean: `New.exists_besselU_mul_toBesselH`). Over $\mathbb C$ the group $H$ is $U(k)$, and the source writes $\mathrm{embedH}$ for $\iota$ (Lean: `New.RealPlace.embedH`).

### The character of $S$

**Definition.** For $s \in G_T$ the *simple root sum* is
$$\sigma(s) = \sum_{a < \varrho} s_{f_a, f_{a+1}},$$
the sum of the entries of $s$ just above the diagonal of its block on the frame. Over $\mathbb C$ put $\operatorname{wave}(c) = \exp(c - \bar c)$, a character of $(\mathbb C, +)$ of absolute value one.

Lean: `New.simpleRootSum` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean), `New.wave` (Lib/General/Groups/BesselGroups.lean).

Note that $c - \bar c = 2i \operatorname{Im} c$. So $\operatorname{wave}(c) = e^{2 i \operatorname{Im} c}$.

**Proposition.** For $h, u \in S$, $\sigma(hu) = \sigma(h) + \sigma(u)$. For $h \in H$, $\sigma(h) = 0$.

Lean: `New.simpleRootSum_mul`, `New.simpleRootSum_eq_zero_of_mem_besselH` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

*Proof.* Put $x = f_a$ and $y = f_{a+1}$. Then $(hu)_{xy} = \sum_m h_{xm} u_{my}$. By the lemma on $S$, $u_{my} = \delta_{my}$ unless $m$ has level below that of $y$, that is unless $m = e_c$ with $c \le a$. For such $m$ the column $m$ of $h$ is a frame column, and $h_{xm} = \delta_{xm}$ since the level of $x$ is at least that of $m$. So only $m = y$ and $m = x$ contribute, and $(hu)_{xy} = h_{xy} u_{yy} + h_{xx} u_{xy} = h_{xy} + u_{xy}$. Sum over $a$. For $h \in H$ the frame columns of $h$ are those of $1$, so every entry $h_{f_a f_{a+1}}$ is $0$. $\square$

So $s \mapsto \operatorname{wave}(\sigma(s))$ is a character of $S$, trivial on $H$. On $\mathsf U$ it reads the coefficient of $e_a$ in $u e_{a+1}$ for $a < \varrho - 1$, and that of $e_{\varrho - 1}$ in $u z$.

### Congruence subgroups

Let $Q \subset A$ be a subring and $g$ a unit of $A$. The congruence subgroup $K(g)$ of $G_T$ consists of the $k \in G_T$ with $k \in GL_r(Q)$ and $g^{-1}(k - 1)$ integral over $Q$ (Lean: `New.unitaryLevel`). For $k \in K(g)$, $g^{-1} \sigma(k) \in Q$, since each off-diagonal entry of $k - 1$ is divisible by $g$ (Lean: `New.inv_mul_simpleRootSum_mem`).

**Proposition.** Let $h, h' \in H$, $u, u' \in \mathsf U$ and $y \in G_T$. If $u h y \in K(g)$ and $u' h' y \in K(g)$, then $h' h^{-1} \in K(g)$.

Lean: `New.div_mem_unitaryLevel_of_besselU_mul` (Lib/DiscreteSeries/Bruhat/FloorGroups.lean).

So the $h \in H$ with $h y \in \mathsf U K(g)$ lie in one coset $(H \cap K(g)) h_0$.

*Proof.* First let $u \in \mathsf U$ and $h \in H$ with $u h \in K(g)$. We show $h \in K(g)$. The matrix $h$ differs from $1$ only in the block $\kappa \times \kappa$. For $i, j \in \kappa$, $(uh)_{ij} = \sum_m u_{im} h_{mj}$. Here $u_{im} = \delta_{im}$ unless $m$ has level above $\varrho$, that is $m = e^*_a$, and $h_{e^*_a, j} = 0$. So $(uh)_{ij} = h_{ij}$. Each entry of $h$ is an entry of $uh$ or of $1$. This gives the integrality of $h$ and the congruence of $h - 1$. For $h^{-1}$, write $(uh)^{-1} = (h^{-1} u^{-1} h) h^{-1}$, where $h^{-1} u^{-1} h \in \mathsf U$ by the Proposition on the normaliser. The same argument shows that each entry of $h^{-1}$ is an entry of $(uh)^{-1}$ or of $1$. So $h \in K(g)$ (Lean: `New.mem_unitaryLevel_of_besselU_mul`).

Now put $d = h' h^{-1} \in H$. Then
$$(u' h' y)(u h y)^{-1} = u' \, (d u^{-1} d^{-1}) \, d,$$
and $u' d u^{-1} d^{-1} \in \mathsf U$ since $H \subset S$ normalises $\mathsf U$. The left side lies in $K(g)$. Apply the first step. $\square$

**Remark (Formalization).** The source states the last proposition with $h' / h = h' h^{-1}$, in the notation of groups. The congruence subgroup is defined by the two conditions $k \in GL_r(Q)$ and $g^{-1}(k - 1) \in M_r(Q)$. Nothing requires $Q$ to be a ring of integers or $g$ to lie in $Q$.
