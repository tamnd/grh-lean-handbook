---
title: The colength of one scaled Hecke operator
lean:
  - New/UpperBound/Divisibility/HeckeEdges.lean
  - New/UpperBound/Divisibility/MarkOperator.lean
decls:
  - New.Columns.valuationRingAt
  - New.Columns.localGL
  - New.Columns.localGL_mem_localIntGL_iff
  - New.Columns.atPlace_embFin
  - New.Columns.latticeGL
  - New.Columns.latticeGL_apply
  - New.Columns.localGL_mem_localIntGL_iff_mem_range
  - New.Columns.localGL_latticeGL_mem_localIntGL
  - New.Columns.blockScaling
  - New.Columns.coe_blockScaling
  - New.Columns.coe_blockScaling_inv
  - New.Columns.blockScaling_mem_basicDoubleCoset
  - New.Columns.mem_parahoric_twoBlock_iff
  - New.Columns.conj_blockScaling_mem_localIntGL_iff
  - New.Columns.conj_mem_localIntGL_of_transposeGL_mem_parahoric
  - New.Columns.edgeStep
  - New.Columns.natCast_mem_of_valuation_eq
  - New.Columns.edgeStep_mem_basicDoubleCoset
  - New.Columns.edgeStep_inv_mul_mem_localIntGL_iff
  - New.Columns.exists_edgeStep_eq
  - New.Columns.ClassEdges
  - New.Columns.HeckeEdges
  - New.Columns.atPlace_mem_localIntGL_of_isLevel
  - New.Columns.nonempty_heckeEdges
  - New.Columns.HeckeEdges.embFin_rationalPart
  - New.Columns.HeckeEdges.rationalPart_eq
  - New.Columns.HeckeEdges.localGL_rationalPart_mem_localIntGL
  - New.Columns.HeckeEdges.eq_of_origin_eq_of_mem_parahoric
  - New.Columns.HeckeEdges.heckeSplit_apply_rep
  - New.Columns.smul_transpose_map_eq_letterMatrix
  - New.Columns.kroneckerPi_symPowMatrix_eq_letterRep
  - New.Columns.exists_schur_eq_symPowMatrix
  - New.Columns.exists_weylIndex_equiv
  - New.Columns.exists_schur_eq_map
  - New.Columns.weightRep_column_apply
  - New.Columns.sourceFormOfValues
  - New.Columns.sourceFormOfValues_apply_rep
  - New.Columns.range_sourceFormOfValues
  - New.Columns.isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle
  - New.Data.isLargeDegree_of_le_card
  - New.Data.three_mul_divisorConstant_le
  - New.Data.exists_orbit_of_mem_aPlaces
  - New.Data.embeddingToward
  - New.Data.placeOfEmb_embeddingToward
  - New.Data.embeddingToward_mem_embValRing
  - New.Data.letterEmbedding
  - New.Data.coe_letterEmbedding
  - New.Data.not_isUnit_natCast_embValRing
  - New.Data.dvd_letterEmbedding_sub_pow
  - New.Data.IsExceptional.card_residueField
  - New.Data.IsMarked.exists_frobeniusCycle
  - New.Data.IsMarked.isOntoUpToColength_scaledHeckeOperator
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The colength of one scaled Hecke operator

Section 5 moved the scaled Hecke operators $Y_{\mathfrak l} = p^{A_{\mathfrak l}}T_{\mathfrak l,r}$ through the chain. So the divisibility holds on the image of their product. This section shows that the image of one $Y_{\mathfrak l}$ is large. The bound comes from the theorem on elementary divisors of [elementary divisors of a Hecke operator](/chapter/elementary-divisors/). The work here is to write $Y_{\mathfrak l}$ in the coordinates of that theorem.

Recall that $\mathrm{IsOntoUpToColength}(p, M, j, y, c)$ says: $y(M) \subseteq M$, and there is a natural number $i \le c$ with $\mathrm{ColengthDvd}(M, y(M) + p^jM, p^i)$ ([colength](/chapter/twisted-lattices/)). Write $\dim = \dim_{\mathbb C}$ of the space of source forms, and $r = r_p$.

### The theorem on elementary divisors

A *Frobenius cycle* with $N$ letters on a local ring $W$, with values in a ring $O$, is: a prime $p$, an exponent $e$ with $P = p^e \ge 5$, ring maps $\iota_s : W \to O$ for $s \in \mathbb Z/N$, a parity for each letter that alternates, a square root of $p$ in $O$, the congruence $\iota_{s+1}(x) \equiv \iota_s(x)^P \pmod p$, and $\#(W/\mathfrak m_W) = q = P^N$. The size conditions $\mathrm{IsLargeDegree}(k, n, r, \theta)$ are $0 < r$, $2r \le k$, $0 < \theta \le 1$, $n^4 \le q$ and $(Nk\log q/\theta)^5P^{3r} \le n$. The divisor constant is $c_{\mathrm{div}} = Nn(P^{-2r} + r^2/(kP))$.

Edge coordinates on finite sets $X$ and $H$ give, for each edge $(x, b)$ with $b$ a coset of the parahoric subgroup $P_r \subseteq \mathrm{GL}_k(W)$ with blocks $r$ and $k - r$: an origin $o(x,b) \in X$, a basis change $g(x,b) \in \mathrm{GL}_k(W)$, a matrix $h(b)$ with $h(b)^{-1} \in b$, and a transition $m(x,b) \in \mathrm{GL}_H(O)$. An edge must be determined by its origin and the coset of $g^{\mathsf T}$ modulo $P_r$. For a bijection $J : I \cong \mathrm{Exp} \times H$, where $\mathrm{Exp}$ indexes the monomials of degree $n$ in each letter, the edge Hecke operator is

$$(AF)(x) = \sum_b \big((\varrho(g(x,b))\,p^{\mathrm{depth}}\,\varrho(h(b)))^{\mathsf T} \otimes m(x,b)\big)\,F(o(x,b)).$$

Here $\varrho$ is the action on monomials, and $p^{\mathrm{depth}}$ multiplies a monomial by $p$ to its degree in the deep variables.

**Theorem (Elementary divisors).** Let $O$ be a valuation domain of characteristic $0$, let $p$ not be a unit of $O$, and let $\mathrm{IsLargeDegree}(k, n, r, \theta)$ hold. Let $f : (X \to I \to O) \to M$ be $O$-linear and $Y \circ f = f \circ A$. Then for every $j$, $\mathrm{IsOntoUpToColength}(p, f(\cdot), j, Y, (3c_{\mathrm{div}} + \theta j)\,|X|\,|I|)$.

Lean: `New.FrobeniusCycle.elementary_divisors` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean). The proof is in [elementary divisors of a Hecke operator](/chapter/elementary-divisors/), an earlier chapter.

### Hecke edges

Fix a marked set $\Lambda$ and $\mathfrak l \in \Lambda$. Let $W$ be the valuation ring of $\mathfrak l$ in $E$ and $X$ the set of classes $\Gamma\backslash G_f/K_0$. By [the marked sets](/chapter/chain-valuation/), $\mathfrak l$ is split, $p$ is a uniformizer at $\mathfrak l$, and $K_0$ is maximal at $\mathfrak l$. By [the freeness of $K_0$](/decl/New.Data.classAut_levelX_zero_eq_bot/), $\Gamma$ acts freely on the classes. Let $d = \mathrm{diag}(p, \dots, p, 1, \dots, 1)$ with $r$ entries $p$.

**Definition (Hecke edges).** Hecke edges at $\mathfrak l$ are: a numbering of $X_0$; representatives $\rho(x)$ of the classes, integral above $p$; and for each edge $e = (x, b)$ an origin $o(e) \in X$, a rational point $\gamma_e \in \Gamma$, an element $u_e \in K_0$ and a basis change $g_e \in \mathrm{GL}_k(W)$, such that

$$\rho(x)\,\delta(x,b) = \gamma_e\,\rho(o(e))\,u_e, \qquad \gamma_e^{-1} = g_e\,d^{-1}\beta_b^{-1}.$$

Here $\beta_b$ is the chosen representative of $b$, and $\delta(x,b)$ is the point with component $\rho(x)_{\mathfrak l}^{-1}\beta_b d$ at $\mathfrak l$, with the matching component at $\bar{\mathfrak l}$.

Lean: `New.Columns.HeckeEdges`, `New.Columns.edgeStep` (New/UpperBound/Divisibility/HeckeEdges.lean).

**Lemma.** If $p \in \mathfrak l$, Hecke edges exist.

Lean: `New.Columns.nonempty_heckeEdges` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* Representatives integral above $p$ exist. The point $\rho(x)\delta(x,b)$ lies in some class $y$, so it is $\gamma\rho(y)u$. At $\mathfrak l$ the point $\gamma^{-1}\beta_bd$ is $\rho(y)_{\mathfrak l}u_{\mathfrak l}$, which is integral. So $\gamma^{-1}\beta_b d = g$ lies in $\mathrm{GL}_k(W)$, and $\gamma^{-1} = gd^{-1}\beta_b^{-1}$. $\square$

**Lemma (Edges are free).** Let $p$ be a uniformizer at $\mathfrak l$, $K_0$ maximal at $\mathfrak l$, and the action free. If $o(e) = o(e')$ and $g_e^{\mathsf T}(g_{e'}^{\mathsf T})^{-1} \in P_r$, then $e = e'$.

Lean: `New.Columns.HeckeEdges.eq_of_origin_eq_of_mem_parahoric` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* Let $e = (x, b)$, $e' = (x', b')$ and $\eta = \gamma_e\gamma_{e'}^{-1}$. At $\mathfrak l$, $\eta = \beta_b\,(dg_e^{-1}g_{e'}d^{-1})\,\beta_{b'}^{-1}$. The hypothesis on the transposes makes $dg_e^{-1}g_{e'}d^{-1}$ integral (`New.Columns.conj_mem_localIntGL_of_transposeGL_mem_parahoric`). So $\eta\rho(x') \in \rho(x)K_0$. Thus $x = x'$, and $\eta = 1$ by freeness. Then $d^{-1}\beta_b^{-1}\beta_{b'}d = g_e^{-1}g_{e'}$ is integral, so $\beta_b^{-1}\beta_{b'} \in P_r$ (`New.Columns.conj_blockScaling_mem_localIntGL_iff`) and $b = b'$. $\square$

**Lemma (The Hecke operator as a sum over edges).** Let $p$ be a uniformizer at $\mathfrak l$, $r < k$, $K_0$ maximal at $\mathfrak l$, and $\varphi$ fixed by $K_0$. Then

$$(T_{\mathfrak l,r}\varphi)(\rho(x)) = \sum_b \gamma_{(x,b)} \cdot \varphi(\rho(o(x,b))).$$

Lean: `New.Columns.HeckeEdges.heckeSplit_apply_rep`, `New.Columns.exists_edgeStep_eq`, `New.Columns.edgeStep_mem_basicDoubleCoset` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* The matrix $d$ lies in the double coset of $T_{\mathfrak l,r}$. Every coset of that double coset is the coset of $\delta(x, b)$ for some $\beta$, and $\delta(x,b)$ and $\delta(x,b')$ give the same coset if and only if $b = b'$. So $(T_{\mathfrak l,r}\varphi)(\rho(x)) = \sum_b\varphi(\rho(x)\delta(x,b))$, and $\varphi(\gamma_e\rho(o(e))u_e) = \gamma_e\cdot\varphi(\rho(o(e)))$. $\square$

### The weight in the coordinates of the edges

Let $Q$ be the set of a-places $\sigma$ with $w_\sigma \in \{\mathfrak l, \bar{\mathfrak l}\}$, numbered by $t : \mathbb Z/N \cong Q$. At an a-place the weight is one row of length $a$, so its Weyl module is $\mathrm{Sym}^a$ of the standard module.

**Lemma (Splitting the weight space).** There is a bijection $J$ of the basis index $I$ of the Weyl module with $\mathrm{Exp} \times H$, where $H$ indexes the Weyl module at the places outside $Q$, such that $(\prod_s c_s)^a$ times the Schur matrix of a family $z$ is the Schur matrix of $z$ outside $Q$, tensored with $\bigotimes_s\mathrm{Sym}^a(c_s z_{t(s)}^{\mathsf T})^{\mathsf T}$.

Lean: `New.Columns.exists_weylIndex_equiv`, `New.Columns.exists_schur_eq_symPowMatrix` (New/UpperBound/Divisibility/HeckeEdges.lean).

**Lemma (Letters).** Let $T$ be a Frobenius cycle on $W$ with prime $p$, and let $\iota_s = \phi_s$ on even letters and $\phi_s \circ c$ on odd letters. Let $\gamma^{-1} = g\,d^{-1}\beta$ with $g, \beta \in \mathrm{GL}_k(W)$. Then $\bigotimes_s \mathrm{Sym}^a\big(p^{[s\text{ even}]}\,(\phi_s\circ c)(\gamma)^{\mathsf T}\big) = \varrho(g)\,p^{\mathrm{depth}}\,\varrho(\beta)$.

Lean: `New.Columns.kroneckerPi_symPowMatrix_eq_letterRep`, `New.Columns.smul_transpose_map_eq_letterMatrix` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* For one letter, $p^{[s \text{ even}]}(\phi_s\circ c)(\gamma)^{\mathsf T}$ is the letter matrix of $g$, times the diagonal matrix with $p$ at the deep variables, times the letter matrix of $\beta$. Symmetric powers and tensor products are multiplicative. $\square$

**Lemma (Integral outside $Q$).** Let $S$ be a set of places, and let $\gamma$ be integral at $\bar w_\tau$ for each a-place $\tau \in S$. Then the Schur matrix of $\gamma$ on the factor at $S$, with $\gamma$ embedded by $\Phi_\tau\circ c$, is invertible over $\mathcal O_\iota$.

Lean: `New.Columns.exists_schur_eq_map` (New/UpperBound/Divisibility/HeckeEdges.lean).

**Lemma (Integral forms are integral values).** Let the $\rho(x)$ be integral above $p$. The map that sends $F : X \to I \to \mathcal O_\iota$ to the source form with value $F(x)$ at $\rho(x)$ has image $\mathcal A_\iota$.

Lean: `New.Columns.range_sourceFormOfValues`, `New.Columns.sourceFormOfValues` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* The gauge of a source form at $\eta\rho(x)u$ equals its gauge at $\rho(x)$. At an integral point the gauge is at most $1$ if and only if all coordinates lie in $\mathcal O_\iota$. $\square$

### The bound for a matched cycle

**Theorem.** Let $\mathfrak l \in \Lambda$ and let $T$ be a Frobenius cycle on $W$ with values in $\mathcal O_\iota$, with prime $p$ not a unit. Let $t : \mathbb Z/N \cong Q$, let $\iota_s = \Phi_{t(s)}$ on even letters and $\Phi_{t(s)}\circ c$ on odd letters, let $A_{\mathfrak l} = a\,\#\{s \text{ even}\}$, and let $\mathrm{IsLargeDegree}(k, a, r, \theta)$ hold. Then for every $j_0$,

$$\mathrm{IsOntoUpToColength}\big(p, \mathcal A_\iota, j_0, Y_{\mathfrak l}, (3c_{\mathrm{div}} + \theta j_0)\dim\big).$$

Lean: `New.Columns.isOntoUpToColength_scaledHeckeOperator_of_frobeniusCycle`, `New.Columns.HeckeEdges.localGL_rationalPart_mem_localIntGL` (New/UpperBound/Divisibility/HeckeEdges.lean).

*Proof.* Take Hecke edges. For an a-place $\tau \notin Q$, the prime $\bar w_\tau$ is neither $\mathfrak l$ nor $\bar{\mathfrak l}$, and $\gamma_e$ is integral there: at such a place $\delta = 1$, so $\gamma_e = \rho(x)\,u_e^{-1}\rho(o(e))^{-1}$ is a product of integral matrices. By the last lemma but one, the Schur matrix of $\gamma_e$ outside $Q$ is an invertible matrix $m_e$ over $\mathcal O_\iota$. The edge coordinates are $o$, $g$, $h(b) = \beta_b^{-1}$ and $m$. The edges are free by the lemma above. Since $p^{A_{\mathfrak l}} = \prod_s (p^{[s\text{ even}]})^a$, the splitting and the lemma on letters give, entry by entry, that $p^{A_{\mathfrak l}}$ times the Schur matrix of $\gamma_e$ is the term of $e$ in $A$. With $f$ the map of the last lemma, the sum over edges gives $Y_{\mathfrak l}\circ f = f\circ A$. The action is free, so $\dim = |X|\,|I|$, and $f$ has image $\mathcal A_\iota$. Apply the theorem on elementary divisors. $\square$

### The Frobenius cycle of a marked prime

**Lemma (The orbit).** Let $\chi_K(p) = -1$, let $o_0$ be odd, let $\tau$ be an a-place, and let $N$ be the order of $[-p]^{o_0}$. There is an injective $t : \mathbb Z/N \to \Phi$ with $t(s+1) = [-p^{o_0}]\,t(s)$ whose image is the set of a-places $\sigma$ with $w_\sigma \in \{w_\tau, \bar w_\tau\}$.

Lean: `New.Data.exists_orbit_of_mem_aPlaces` (New/UpperBound/Divisibility/MarkOperator.lean).

*Proof.* Put $t(s) = [-p]^{o_0 s}\tau$. By [the induced primes](/chapter/chain-valuation/), $w_\sigma \in \{w_\tau, \bar w_\tau\}$ if and only if $\sigma = [-p]^i\tau$. Such a $\sigma$ is an a-place if and only if $o_0 \mid i$, because the a-places are the places of class $1$ modulo $q_0$, and $o_0$ is the order of $[-p]$ modulo $q_0$. $\square$

For $\sigma$ with $w_\sigma \in \{\mathfrak l, \bar{\mathfrak l}\}$, let $\iota_\sigma = \Phi_\sigma$ if $w_\sigma = \mathfrak l$ and $\Phi_\sigma\circ c$ otherwise. It maps $W$ into $\mathcal O_\iota$.

Lean: `New.Data.embeddingToward`, `New.Data.letterEmbedding`, `New.Data.embeddingToward_mem_embValRing` (New/UpperBound/Divisibility/MarkOperator.lean).

**Lemma (Frobenius congruence for letters).** Let $\chi_K(p) = -1$, $\mathfrak l$ split, $e$ odd, $\sigma' = [-p^e]\sigma$, and let $\sigma, \sigma'$ induce $\mathfrak l$ or $\bar{\mathfrak l}$. Then $p \mid \iota_{\sigma'}(x) - \iota_\sigma(x)^{p^e}$ in $\mathcal O_\iota$ for every $x \in W$.

Lean: `New.Data.dvd_letterEmbedding_sub_pow` (New/UpperBound/Divisibility/MarkOperator.lean).

*Proof.* Reduce modulo $p$. A ring map from $W$ is fixed by its values on $\mathcal O_E$, since $W$ is a localization. Let $g$ be the automorphism named by $-p^e$. By [the Frobenius congruence](/decl/New.Parameters.natCast_dvd_pow_sub_galOfPlaceInt_star/), $g(y) \equiv \bar y^{p^e} \pmod p$. Since $w_{\sigma'} = \bar w_\sigma$, exactly one of $\iota_\sigma$, $\iota_{\sigma'}$ has the conjugation, and $\iota_{\sigma'}(\bar y) = \iota_\sigma(g(y))$. So modulo $p$, $\iota_{\sigma'}(\bar y) \equiv \iota_\sigma(\bar y)^{p^e}$. $\square$

**Theorem (The Frobenius cycle).** Let $\Lambda$ be marked, $\mathfrak l \in \Lambda$, $o = o_0N$, $t(s+1) = [-p^{o_0}]t(s)$, and let each $t(s)$ induce $\mathfrak l$ or $\bar{\mathfrak l}$. There is a Frobenius cycle $T$ on $W$ with values in $\mathcal O_\iota$, prime $p$ and exponent $o_0$, with $s$ even if and only if $w_{t(s)} = \mathfrak l$, and $\iota_s = \iota_{t(s)}$.

Lean: `New.Data.IsMarked.exists_frobeniusCycle`, `New.Data.IsExceptional.card_residueField` (New/UpperBound/Divisibility/MarkOperator.lean).

*Proof.* The congruence is the last lemma but one with $e = o_0$. Multiplication by $[-p^{o_0}]$ exchanges $\mathfrak l$ and $\bar{\mathfrak l}$, so parities alternate. $P = p^{o_0} \ge p \ge 13$. Since $p$ is exceptional, the residue field of $\mathfrak l$ has $p^o = p^{o_0N} = P^N$ elements, by the norm of $\mathfrak l$ in [the exceptional primes](/decl/New.Data.IsExceptional.q_eq_pow_orderOf/). A square root of $p$ in $\mathbb C$ lies in $\mathcal O_\iota$. $\square$

### The sizes and the mark operator

**Lemma (Sizes).** Let $T$ have $N$ letters, $13 \le p < x_1$, $0 < e \le r$, $N \le \#\Phi$ and $m \le eN$. Then $\mathrm{IsLargeDegree}(k, a, r, 1/(m^2f))$. If $N = 2\ell$, then $3c_{\mathrm{div}} \le 12a\ell/(mp)$.

Lean: `New.Data.isLargeDegree_of_le_card`, `New.Data.three_mul_divisorConstant_le` (New/UpperBound/Divisibility/MarkOperator.lean).

*Proof.* The first part uses the bounds on the numerical parameters of [the objects of the upper bound](/chapter/upper-bound-objects/): $a^4 \le \exp(m) \le 3^m \le p^{eN} = q$, and $\log q \le eN\log x_1$ and $P^{3r} \le x_1^{3l_0^2} \le \sqrt b$ give the last condition. For the second part, $mp \le p^rp^r \le P^{2r}$, and $r^2m \le k$ gives $r^2/(kP) \le 1/(mp)$. So $3c_{\mathrm{div}} \le 3\cdot 2\ell a\cdot 2/(mp)$. $\square$

**Theorem (The mark operator).** Let $\Lambda$ be marked, $\mathfrak l \in \Lambda$ and $j_0 \in \mathbb N$. Then

$$\mathrm{IsOntoUpToColength}\Big(p, \mathcal A_\iota, j_0, Y_{\mathfrak l}, \Big(\frac{12A_{\mathfrak l}}{mp} + \frac{j_0}{m^2f}\Big)\dim\Big).$$

Lean: `New.Data.IsMarked.isOntoUpToColength_scaledHeckeOperator` (New/UpperBound/Divisibility/MarkOperator.lean).

*Proof.* The prime $p$ is not a unit of $\mathcal O_\iota$, since $|\iota_p p|_p < 1$ (`New.Data.not_isUnit_natCast_embValRing`). Take an a-place $\tau$ with $w_\tau = \mathfrak l$, the orbit $t$ of $\tau$, and its Frobenius cycle $T$. The even letters are the a-places inducing $\mathfrak l$, so $A_{\mathfrak l} = a\,\#\{s \text{ even}\}$, and the number of even letters is $\ell = N/2$. By [the exceptional orbits](/decl/New.Data.IsExceptional.hasExceptionalOrbits/), $o_0$ is odd, $o_0 \le r$, and $m \mid o$, so $m \le o_0N$. The lemma on sizes gives $\mathrm{IsLargeDegree}$ with $\theta = 1/(m^2f)$ and $3c_{\mathrm{div}} \le 12A_{\mathfrak l}/(mp)$. Apply the theorem for a matched cycle. $\square$

**Remark (Formalization).** The Hecke edges, the numbering and the matrices $m_e$ come from `Nonempty` and `choose`. The bound does not depend on them. The divisions in the bound are divisions of real numbers, and the exponent $i$ is a natural number at most the real bound.
