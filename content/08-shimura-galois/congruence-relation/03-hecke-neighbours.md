---
title: The relation on points
lean:
  - Lib/General/Combinatorics.lean
  - Lib/Shimura/IntegralModel/TowerExistence.lean
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/Shimura/CongruenceRelation/HeckeNeighbours.lean
  - Lib/Shimura/CongruenceRelation/KernelReduction.lean
decls:
  - New.q_binomial_submodule
  - New.Variety.cancels_moebius_of_factorsThrough_sup
  - New.Variety.IsSafe
  - New.Variety.invHeckeIsogeny
  - New.Variety.heckeSum
  - New.Variety.Model
  - New.Variety.UniversalFamily.GraphClosure.congruenceRelation
  - New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup
  - New.Variety.exists_residue_torsion_emb
  - New.Variety.frobeniusTwist
  - New.Variety.IsTwistedReduction
  - New.Variety.IsTwistedReduction.exists_comp_eq_smul
  - New.Variety.cartier
  - New.Variety.ker_factors_of_torsionPoint
  - New.Variety.exists_isLieLine
  - New.Variety.exists_param_pow_card_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The relation on points

This section proves the relation on points that Section 2 needs, for the Hecke legs of the model. The proof has two parts. The first part is combinatorics over a finite field: the coefficients $(-1)^r q^{\binom{r}{2}}$ cancel along any map that depends only on $A + W$, for a fixed nonzero subspace $W$. The second part is geometry: at each point of the special fibre, the Frobenius twisted Hecke neighbour of $A$ depends only on $A + W$, for some $W \neq 0$. The second part is the only place where abelian varieties enter.

Throughout, $k$ is a finite field with $q$ elements, $n \geq 1$, and $A, B, U, W$ denote subspaces of $k^n$. For a subspace $A$ write $r(A) = \dim A$ and
$$\mu(A) = (-1)^{r(A)} q^{\binom{r(A)}{2}}.$$

### The q-binomial theorem over subspaces

**Theorem (q-binomial theorem).** For every subspace $W$ of $k^n$ and every $X \in \mathbb{C}$,
$$\sum_{U \leq W} (-X)^{\dim U} q^{\binom{\dim U}{2}} = \prod_{l = 0}^{\dim W - 1} \left(1 - q^l X\right).$$

Lean: `New.q_binomial_submodule` (Lib/General/Combinatorics.lean).

The textbook form is a sum over $r$ with the Gaussian binomial coefficient $\binom{d}{r}_q$, the number of $r$-dimensional subspaces of $k^d$: $\sum_r \binom{d}{r}_q (-X)^r q^{\binom{r}{2}} = \prod_{l < d}(1 - q^l X)$. The source cites Macdonald for it. The form over subspaces avoids the Gaussian coefficients.

*Proof.* Induction along a maximal chain $0 = W_0 < W_1 < \cdots < W_d = W$, with $\dim W_j = j$. For $W = 0$ both sides are $1$. Let $H < W$ be a hyperplane of $W$, with $\dim H = d$ and $\dim W = d + 1$, and assume the formula for $H$. Write $c_r = (-X)^r q^{\binom{r}{2}}$, so that $c_{r + 1} = -X q^r c_r$.

A subspace $U \leq W$ either lies in $H$, or does not. In the second case $U' = U \cap H$ has dimension $\dim U - 1$, and $U = U' + k v$ for any $v \in U \setminus H$. Fix $U' \leq H$ of dimension $r$. The subspaces $U \leq W$ with $U \cap H = U'$ and $U \not\leq H$ correspond to the lines of $W / U'$ that do not lie in $H / U'$. Their number is
$$\frac{q^{d + 1 - r} - q^{d - r}}{q - 1} = q^{d - r}.$$
So
$$\sum_{U \leq W} c_{\dim U} = \sum_{U' \leq H} \left(c_r + q^{d - r} c_{r + 1}\right) = \sum_{U' \leq H} \left(1 - q^d X\right) c_r = (1 - q^d X) \sum_{U' \leq H} c_{\dim U'},$$
where $r = \dim U'$ in each term. The induction hypothesis finishes the proof. $\square$

**Remark (Formalization).** The Lean proof counts pairs $(U, v)$ with $v \in U \setminus H$ in two ways, in place of the count of lines. The sum on the left is `heckePolyCoeff X U` summed over $U \leq W$, and the product is `SiegelWeil.qPochhammer q (dim W) X`. The same coefficients $(-1)^j q^{\binom{j}{2}}$ appear in the Hecke polynomial of Section 1, and at $X = 1$ they are the coefficients $\mu$ of the next proposition.

### Möbius cancellation

**Proposition (Möbius cancellation).** Let $W \neq 0$ be a subspace of $k^n$, and let $v$ be a map from the subspaces of $k^n$ to a set $V$ such that $v(A)$ depends only on $A + W$. Then the coefficients $\mu(A)$ cancel along $v$:
$$\sum_{A \leq k^n} (-1)^{\dim A} q^{\binom{\dim A}{2}} [v(A)] = 0.$$

Lean: `New.Variety.cancels_moebius_of_factorsThrough_sup` (Lib/Shimura/IntegralModel/TowerExistence.lean).

In the source, $k$ is the residue field of a finite place $w$ of a number field and $q$ is the norm of $w$.

*Proof.* By the lemma on factoring of Section 2, it is enough to treat $v(A) = A + W$. For a subspace $B$ let
$$F(B) = \sum_{A \,:\, A + W = B} \mu(A).$$
The coefficient of $[B]$ in $\sum_A \mu(A) [A + W]$ is $F(B)$. So it is enough to show $F(B) = 0$ for all $B$.

Sum $F$ over the subspaces below a fixed $B$:
$$\sum_{B' \leq B} F(B') = \sum_{A \,:\, A + W \leq B} \mu(A).$$
If $W \not\leq B$, no $A$ has $A + W \leq B$, and the sum is $0$. If $W \leq B$, the condition $A + W \leq B$ is $A \leq B$, and the sum is the left side of the q-binomial theorem for $B$ at $X = 1$. It equals $\prod_{l < \dim B}(1 - q^l)$. Here $\dim B \geq \dim W \geq 1$, so the factor $l = 0$ occurs, and it is $1 - q^0 = 0$. So
$$\sum_{B' \leq B} F(B') = 0 \quad \text{for every } B.$$
The lattice of subspaces is finite. Möbius inversion on it (or induction on $\dim B$) gives $F(B) = 0$ for every $B$. $\square$

**Example ($n = 1$).** The subspaces are $0$ and $k$, with $\mu(0) = 1$ and $\mu(k) = -1$. The only $W \neq 0$ is $k$, and $0 + k = k + k$. So the hypothesis says $v(0) = v(k)$, and the conclusion is $[v(0)] - [v(k)] = 0$.

**Example ($n = 2$).** The subspaces are $0$, the $q + 1$ lines and $k^2$, with $\mu = 1$, $-1$ and $q$. Take $W = L_0$, a line. Then $A + L_0 = L_0$ for $A \in \{0, L_0\}$, and $A + L_0 = k^2$ for the other $q$ lines and for $k^2$. So $v$ takes at most two values, $v(0) = v(L_0)$ and $v(L) = v(k^2)$ for $L \neq L_0$. The two classes have total coefficients $1 - 1 = 0$ and $-q + q = 0$. The relation on points is
$$[v(0)] - [v(L_0)] - \sum_{L \neq L_0} [v(L)] + q\,[v(k^2)] = 0.$$
This is the shape of the classical relation for modular curves. The line $L_0$ plays the part of the kernel of Frobenius, and the coefficient $q$ of $k^2$ is cancelled by $q$ lines with the same image.

### The Hecke legs at a split place

Let $E$ be a CM field that contains $K_0 = \mathbb{Q}(\sqrt{-d_0})$, and let $\mathfrak{N}$ be a level in $\mathcal{O}_E$.

**Definition (Safe place).** A finite place $w$ of $E$ is *safe* for $\mathfrak{N}$ if the place $u$ of $K_0$ below $w$ is split and prime to the discriminant, and $\mathfrak{N}$ lies neither in $w$ nor in any place above $\bar u$.

Lean: `New.Variety.IsSafe` (Lib/Shimura/HeckeTower/HeckeData.lean).

In Lean, the condition on $u$ is that $u$ contains some element $(1 + \sqrt{-d_0})/2 - b$, $b \in \mathbb{Z}$, coprime to its conjugate. The type `SafePlace 𝔑` collects the safe places.

Let $w$ be a split place, that is $\bar w \neq w$, with residue field $k_w$ of order $q$. For a subspace $U$ of $k_w^n$ of dimension $r$, the source fixes a matrix in the double coset of $\operatorname{diag}(\varpi 1_r, 1_{n - r})$ in $\mathrm{GL}_n(E_w)$ whose reduction modulo $w$ has kernel $U$.

**Definition (Hecke element of a subspace).** The element $g_U$ of $\mathrm{GL}_n(\mathbb{A}_{E, f})$ is the product of a central scalar, the conjugate of $N(\varpi_w)^{-r}$ with $N$ the norm from $E$ to $K_0$, and the image at $w$ of the transpose of the chosen matrix of $U$. The element $\tau_{w, j}$ of the group ring is $\sum_{\dim U = j} [g_U]$.

Lean: `New.Variety.invHeckeIsogeny` and `New.Variety.heckeSum` (Lib/Shimura/HeckeTower/HeckeData.lean).

The model of [the integral model](/chapter/integral-model/) has, at each level $i$, legs $p_g : W_i \to Z$ for the cosets $g$ in a set $s_i$. Write $u_A = p_{g_A}$. The relation on points is one field of the structure [Model](/decl/New.Variety.Model/).

**Definition (The congruence field of a model).** Let $w$ be a split safe place with $q = p^f$, let $i$ be a level with $g_A \in s_i$ for all $A$, and let $\mathfrak{p} \subseteq R$ contain the image of $w$. Then the family $(u_A)_A$ satisfies the congruence relation modulo $\mathfrak{p}$, with coefficients $\mu(A) = (-1)^{r(A)} q^{\binom{r(A)}{2}}$ and exponents $(n - r(A)) f$.

Lean: field `congruence` of `New.Variety.Model` ([Model.lean, line 145](lean:Lib/Shimura/HeckeTower/Model.lean#L145)).

Unwound, for every point $x$ of the cover in characteristic $p$ over $\mathfrak{p}$,
$$\sum_{A \leq k_w^n} (-1)^{r(A)} q^{\binom{r(A)}{2}} \left[\operatorname{Frob}^{(n - r(A)) f}(u_A(x))\right] = 0,$$
where $\operatorname{Frob}$ is the $p$-power Frobenius of the field of $x$. So $\operatorname{Frob}^{(n - r) f}$ is the $q^{n - r}$-power map.

The model is built in [the integral model](/chapter/integral-model/), and the field is proved there from the next lemma. The covers of the model are closures of graphs of Hecke translations. Write $C$ for such a closure.

**Lemma.** In the setting of the construction of the model, let $w$ be a split place that is safe for the level and good for the PEL datum, with $q = l^f$. Let $\mathfrak{p}$ contain the image of $w$. Let maps $u_A$ from $C$ to the base send the complex point of each $a$ to the complex point of the translate $a \cdot g_A$. Then $(u_A)_A$ satisfies the congruence relation modulo $\mathfrak{p}$ with coefficients $\mu(A)$ and exponents $(n - r(A)) f$.

Lean: `New.Variety.UniversalFamily.GraphClosure.congruenceRelation` (Lib/Shimura/IntegralModel/TowerExistence.lean).

*Proof.* Let $x$ be a point of $C$ with values in a field $k$ of characteristic $l$, over $\mathfrak{p}$. It comes from the residue field of a point $z$ of $C$. The point $z$ is the centre of an arc: a valuation ring $V$ of $\mathbb{C}$, and a $V$-point $\alpha$ of $C$ whose generic point is the complex point of some $b$. The maps $u_A$ send $\alpha$ to the $V$-points of the Hecke neighbours $b \cdot g_A$. The geometric step below, applied to the residue field of $V$, gives $W \neq 0$ such that the Frobenius twisted reductions of these $V$-points depend only on $A + W$. Here the exponents match: $l^{(n - r(A)) f} = q^{n - r(A)}$. Möbius cancellation gives the relation at the residue field of $V$. Frobenius commutes with the field embeddings between the residue field of $z$, the residue field of $V$ and $k$, and $\operatorname{Spec}$ of a field embedding is an epimorphism. So the relation descends from the residue field of $V$ to the residue field of $z$ and goes up to $k$. $\square$

### The geometric step

The geometric step is the analogue of the classical fact that the $p + 1$ quotients of an ordinary elliptic curve reduce to two Frobenius twists. The source states it in a form that needs no ordinary locus. The textbook forms are in Wedhorn, *Congruence relations on some Shimura varieties*, J. reine angew. Math. 524 (2000), 43 to 71, and in Harris and Taylor (2001), Chapter III.4. The source says that its method follows Katz and Mazur, *Arithmetic moduli of elliptic curves* (1985), Chapter 13.

**Theorem (Pointwise step).** Let $U$ be a universal family of PEL type over $R$ for the CM field $E \supseteq K_0$, with $\beta = (1 + \sqrt{-d_0})/2$ the element of the PEL datum. Let $V$ be a valuation subring of $\mathbb{C}$, and let $s$ be a $V$-point of level one with moduli point $z$. Let $\pi : V \to k$ be onto an algebraically closed field of characteristic $l$, and let $x_0$ be the reduction of the object under $s$ along $\pi$. Let $w$ be a split finite place equal to the kernel of $\mathcal{O}_E \to k$, good for the PEL datum and safe for the level, with $q = |k_w|$. For each subspace $A \leq k_w^n$ let $m(A) \in \mathbb{N}$ with $l^{m(A)} = q^{n - \dim A}$, and let $\alpha(A)$ be a $V$-point of level one of the Hecke neighbour $z \cdot g_A$. Then there is $W \neq 0$ such that
$$A \longmapsto \alpha(A) \circ \operatorname{Spec}\left(\operatorname{Frob}^{m(A)} \circ \pi\right)$$
depends only on $A + W$.

Lean: `New.Variety.UniversalFamily.exists_ne_bot_factorsThrough_sup` ([HeckeNeighbours.lean, line 950](lean:Lib/Shimura/CongruenceRelation/HeckeNeighbours.lean#L950)).

The idea is as follows. Each Hecke neighbour comes with an isogeny $\psi_A$ from the abelian variety $y$ of $z$ to the abelian variety $y'_A$ of $z \cdot g_A$. Its kernel on torsion has $w$-part $A$, and its degree is a power of $q$. Reduce modulo $\pi$ and twist by Frobenius. The twisted reduction $g_A$ of $\psi_A$ has the same degree $q^n$ for every $A$: a factor $q^{\dim A}$ from $\psi_A$ and $q^{n - \dim A}$ from Frobenius. Now one nonzero $w$-torsion section $t$ reduces to $0$. Adding $t$ to $A$ changes the kernel of $\psi_A$ only by a section that the reduction does not see. So the kernels of $g_A$ and $g_{A'}$ agree when $A + kt = A' + kt$, and rigidity makes the targets equal. So $W = kt$.

*Proof.* The proof uses the following steps. Each is a lemma of the two files.

1. The $w$-torsion of $(\mathbb{A}_{E, f}/\hat{\mathcal{O}}_E)^n$ is a copy $\sigma(k_w^n)$ of $k_w^n$, and an integral matrix kills $\sigma(v)$ exactly when its reduction modulo $w$ kills $v$ (`New.Variety.exists_residue_torsion_emb`).
2. The neighbour $z \cdot g_A$ gives an isogeny $\psi_A : y \to y'_A$ over $V$ with multiplier $q^{\dim A}$, acting on torsion by $g_A^{-1}$. The torsion sections in its kernel have $w$-part $\sigma(A)$, and $l^{m(\bot)}$ kills all of them. Goodness of $w$ gives $b \in \mathbb{Z}$ with $\beta - b \in w$ coprime to its conjugate, and safety makes the part of the kernel killed by a power of $\beta - b$ into $w$-torsion.
3. A nonzero $w$-torsion vector $t$ has a section that reduces to $0$ over $k$ (`New.Variety.exists_param_pow_card_eq_zero`). This is the source of $W$. The proof finds the line of tangent vectors on which $\mathcal{O}_E$ acts through $\mathcal{O}_E \to k$ (`New.Variety.exists_isLieLine`), a function that detects it, and a parameter whose powers are local equations for the torsion sections. It uses the theorem of Cartier that the points in characteristic $0$ of a finite flat group scheme are dense in it (`New.Variety.cartier`), and the density of torsion sections in kernels of isogenies (`New.Variety.ker_factors_of_torsionPoint`).
4. Each $\psi_B$ reduces to an isogeny $g_B$ from $x_0$ to the reduction $x_B$ of $y'_B$ twisted by $\operatorname{Frob}^{m(B)}$, and $g_B$ has multiplier $l^{m(B)} q^{\dim B} = l^{m(\bot)} = q^n$.
5. Let $W = k_w t$. If $A + W = A' + W$, the weighted counts of torsion sections through each point agree: $l^{m(A)} N_A(a) = l^{m(A')} N_{A'}(a)$, where $N_A(a)$ is the number of sections of $\sigma(A)$ through the $k$-point $a$. The reason is that $\sigma(t)$ reduces to $0$, so the sections of $\sigma(A + W)$ through a point are the sections of $\sigma(A)$ through it, each counted $|W|$ times over.
6. Equal weighted counts make each of $g_A$ and $g_{A'}$ factor through the other up to a power of $\bar\beta - b$ (`New.Variety.IsTwistedReduction.exists_comp_eq_smul`). Rigidity of the objects of the family then makes $x_A = x_{A'}$, compatibly with the maps to the family.
7. The two points agree on the base and on each section. So they are equal. $\square$

The twist needs a precise form, since the reduction of $y'_A$ along $\operatorname{Frob}^{m} \circ \pi$ and along $\pi$ are objects over different maps.

**Definition (Frobenius twist; twisted reduction).** For $\pi : V \to k$ and a $k$-scheme $T$, the absolute Frobenius $t \mapsto t^{l^f}$ of $T$ is a map over $V$ from $T$ with the structure $\operatorname{Frob}^f \circ \pi$ to $T$ with the structure $\pi$. A map $g : x_0 \to x$ between reductions is the *twisted reduction* of $\psi : y \to y'$ if on points it is Frobenius followed by $\psi$, it is $\mathcal{O}_E$-linear, and it sends the reduction of each section $a$ of $y$ to the reduction of $\psi(a)$.

Lean: `New.Variety.frobeniusTwist` and `New.Variety.IsTwistedReduction` (Lib/Shimura/CongruenceRelation/HeckeNeighbours.lean).

**Remark (Formalization).** The pointwise step uses no ordinary locus, no Dieudonné theory and no Serre-Tate theory. It works with torsion sections, their reductions and a count of sections through a point. Rigidity enters through the level structure of the family, not through a moduli problem: the source proves no moduli property for its family (see [the integral model](/chapter/integral-model/)). The choice of $W$ depends on the point; the Möbius cancellation needs only that some $W \neq 0$ exists at each point. The proof uses `choose` for the isogenies $\psi_A$, the reductions $x_B$ and the embedding $\sigma$. The statement does not depend on these choices.
