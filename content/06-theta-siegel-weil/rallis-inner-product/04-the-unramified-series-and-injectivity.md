---
title: The unramified series and injectivity
lean:
  - Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean
  - Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
decls:
  - New.SiegelWeil.IsUnramifiedOn
  - New.FinPlace.four_le_q
  - New.SiegelWeil.stepWeight
  - New.SiegelWeil.stepWeight_le_of_isSplit
  - New.SiegelWeil.stepWeight_le
  - New.SiegelWeil.tsum_stepWeight_conjClosure_singleton_le
  - New.SiegelWeil.summable_stepWeight
  - New.SiegelWeil.tsum_ofReal_norm_vacuumCoeff_le
  - New.SiegelWeil.induction_on_stepWeight
  - New.SiegelWeil.summable_norm_vacuumCoeff
  - New.SiegelWeil.exists_form_eq_rallisSeries
  - New.SiegelWeil.rallisSeries_union
  - New.SiegelWeil.eq_zero_of_rallisSeries_eq_zero
  - New.SiegelWeil.exists_petersson_formLift_eq_rallisSeries
  - New.SiegelWeil.cosetTerm
  - New.SiegelWeil.rallis_inner_product_cosetTerm
  - New.SiegelWeil.vacuumSum
  - New.SiegelWeil.rallisSeries_const
  - New.placeSign
  - New.vacuumSum_pair
  - New.vacuumSum_eq_L_div_eulerProd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The unramified series and injectivity

The inner product formula for sharp data of [Section 3](/chapter/rallis-inner-product/#the-inner-product-formula) has three parts. This section studies the third part, the Rallis series $\mathcal{R}_A$ over the places of a set $A$. It proves that the coefficients are absolutely summable for $2n < m$, that the series is injective, and that the theta lift is injective. In rank one it evaluates the sum of the coefficients as an $L$-value.

### Unramified characters

**Definition.** A character $b$ of $[U(1)]$ is *unramified on* a set $A$ of places, for rank $n$, if $b(\det k) = 1$ for every integral finite point $k$ of $U(S)$ that is supported on $A$ and its conjugate.

Lean: `New.SiegelWeil.IsUnramifiedOn` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

On such points the vacuum coefficient is $1$. For a sharp datum, $b$ is unramified on the places off $S_0$ by the lemma on sharp data in Section 3.

### Counting lattices by neighbours

The modulus of the vacuum coefficient at a coset is a power of an index of lattices. The source bounds the sum of these powers by a count of lattices. A lattice other than the standard lattice $L$ can be brought nearer to $L$ by a *step* at a place $w$. A step is a line in the $n$-space over the residue field at $w$ together with a class of neighbours. This is the neighbour method of Kneser, as in M. Greenberg and J. Voight, *Lattice methods for algebraic modular forms on classical groups* (2014), Section 5, which the source cites.

**Definition.** For $M \in \mathbb{N}$ and a finite place $w$ with residue field of order $q_w$, the *step weight* is
$$s_w = \#\{\text{steps at } w\}\cdot q_w^{-M/2}.$$

Lean: `New.SiegelWeil.stepWeight` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

**Lemma.** Let $2n < M$. Then $s_w \le 1/(q_w - 1)$ for every finite place $w$, and $s_w \le 1/((q_w - 1)\sqrt{q_w})$ if $w$ is split. The weights $s_w$ are summable over all finite places.

Lean: `New.SiegelWeil.stepWeight_le`, `New.SiegelWeil.stepWeight_le_of_isSplit`, `New.SiegelWeil.summable_stepWeight` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

The number of lines in $\mathbb{F}_{q}^n$ is at most $q^n/(q - 1)$, and $q^{n} q^{-M/2} \le q^{-1/2}$ for $M > 2n$. So $s_w$ is at most the number of neighbour classes at $w$ divided by $(q_w - 1)\sqrt{q_w}$. There is at most one class at a split place. At any place there are at most $\sqrt{q_w}$ classes; the source proves this with the root of unity of order $5040$ in the Weil data. For summability, the weight is $O(q_w^{-3/2})$ at a split place. At a place that is not split it is $O(1/q_w)$, and then $q_w$ is at least the square of its least prime factor.

To make the sum over one place small, the source needs $q_w \ge 4$.

**Lemma.** Let $E$ be a CM field with a primitive root of unity of order $5040$. Then $q_w \ge 4$ for every finite place $w$ of $E$.

Lean: `New.FinPlace.four_le_q` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

*Proof.* The field $E$ contains a primitive cube root of unity and a primitive fourth root of unity, as $3$ and $4$ divide $5040$. So $1 + X + X^2$ and $1 + X^2$ have roots in the integers of $E$, hence in every residue field. The first polynomial has no root in $\mathbb{F}_2$, and the second has no root in $\mathbb{F}_3$. So no residue field is $\mathbb{F}_2$ or $\mathbb{F}_3$, and $q_w \ge 4$. $\square$

**Lemma.** Let $2n < M$. For every finite place $w$, the sum of $s_u$ over $u \in \{w, \bar w\}$ is at most $1/3$.

Lean: `New.SiegelWeil.tsum_stepWeight_conjClosure_singleton_le` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

*Proof.* If $w = \bar w$, then $s_w \le 1/(q_w - 1) \le 1/3$ as $q_w \ge 4$. If $w \neq \bar w$, both places are split. Then $(q - 1)\sqrt{q} \ge 3 \cdot 2 = 6$, so each weight is at most $1/6$, and the sum is at most $1/3$. $\square$

**Lemma.** If the weights $s_w$ over the places of $A$ and their conjugates add up to at most $1/3$, then the moduli of the vacuum coefficients at the coset representatives of `localLevel n A` add up to at most $3/2$.

Lean: `New.SiegelWeil.tsum_ofReal_norm_vacuumCoeff_le` (Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean).

The proof descends along the index $[L : L \cap \gamma^{-1} L] = |\operatorname{finMultiplier}(\gamma)|^2$. A coset other than the trivial one is brought nearer to the trivial coset by a step. With $\varrho \le 1/3$ the sum of the weights, the nontrivial cosets contribute at most $\varrho + \varrho^2 + \cdots \le 1/2$, and the total is at most $3/2$.

**Lemma (Induction over sets of places).** Let $2n < M$, and let $P$ be a property of sets of finite places. Suppose that $P(A)$ holds whenever the weights over $A$ and its conjugate add up to at most $1/3$. Suppose also that $P(A_1)$ and $P(A_2)$ imply $P(A_1 \cup A_2)$ whenever $A_2$ is disjoint from $A_1$ and its conjugate. Then $P(A)$ holds for every set $A$, finite or infinite.

Lean: `New.SiegelWeil.induction_on_stepWeight` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

*Proof.* As the weights are summable, there is a finite set $T$ of places off which the weights add up to at most $1/3$. The part of $A$ off $T$ has $P$. The places of $T$ are split off one pair $\{w, \bar w\}$ at a time, and each pair has $P$ by the last lemma but one. $\square$

### Summability and injectivity

**Theorem.** Let $2n < m$. For every character $b$ and every set $A$ of finite places, the moduli of the vacuum coefficients $\operatorname{mc}(r_q)$, with $M = m$, are summable over the cosets $q$ of `localLevel n A`.

Lean: `New.SiegelWeil.summable_norm_vacuumCoeff` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

So for $2n < m$ and bounded $y$ the Rallis series is an absolutely convergent sum, and the junk value of Section 3 does not occur. The series converges uniformly, it is continuous, and it keeps automorphy.

**Theorem.** Let $2n < m$, let $b$ be unramified on $A$, and let $J$ be a group with $K_0 \cap \operatorname{supp}(A) \subseteq J \subseteq$ `localLevel n A`, where $\operatorname{supp}(A)$ is the group of points supported on $A$ and its conjugate. If $y$ is a form of type $e$ with level $J$, then $\mathcal{R}_A y$ is again a form of type $e$ with level $J$.

Lean: `New.SiegelWeil.exists_form_eq_rallisSeries` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

**Lemma.** Let $2n < m$, let $A_2$ be disjoint from $A_1$ and its conjugate, let $b$ be unramified on $A_1 \cup A_2$, and let $y$ be bounded and fixed by the integral points supported on $A_1 \cup A_2$ and its conjugate. Then $\mathcal{R}_{A_1 \cup A_2}\, y = \mathcal{R}_{A_1}(\mathcal{R}_{A_2}\, y)$.

Lean: `New.SiegelWeil.rallisSeries_union` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

**Theorem (Injectivity of the series).** Let $2n < m$, let $b$ be unramified on $A$, and let $y$ be a bounded function fixed by the integral points supported on $A$ and its conjugate. If $\mathcal{R}_A y = 0$, then $y = 0$.

Lean: `New.SiegelWeil.eq_zero_of_rallisSeries_eq_zero` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

*Proof.* Use the induction over sets of places. If the weights over $A$ add up to at most $1/3$, the trivial coset contributes $y$ itself, and the other cosets contribute at most $(3/2 - 1)\sup|y| = \tfrac12 \sup |y|$ in absolute value. So $\sup|y| \le \sup|\mathcal{R}_A y| + \tfrac12\sup|y|$, and $\mathcal{R}_A y = 0$ forces $y = 0$. For a union, the series at $A_1 \cup A_2$ is the series at $A_1$ of the series at $A_2$. Injectivity at $A_1$ gives $\mathcal{R}_{A_2} y = 0$, and injectivity at $A_2$ gives $y = 0$. $\square$

The series is a perturbation of the identity at each place, and the perturbations are uniformly small. No $L$-function is used.

### Injectivity of the theta lift

Let $\gamma$, $\gamma'$ be weights and $e$, $e'$ types of forms on $U(S)$ and $U(T)$. A Fock vector $v$ is an *edge* from $e$ to $e'$ for the real Weil representation if it satisfies the conditions `New.IsEdge` of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). One condition is that the real zeta integral
$$Z = \int_{U(S)(\mathbb{R})} \langle v, \Omega(x) v\rangle\, \frac{\overline{e(x)}}{e(1)}\, dx$$
is not $0$. The lift of forms `New.formLift` sends forms of type $e$ to forms of type $e'$.

**Theorem (Rallis inner product formula and injectivity).** Let $v$ be an edge from $e$ to $e'$ for the weights $\gamma$, $\gamma'$, and let $2n < m$. There is a constant $C \neq 0$ with the following property. Let $a$, $b$ be characters of weights $\gamma$, $\gamma'$, let $F$ be sharp for $J$ off $S_0$ with mass $c$, and let $L$ be the lift of forms by $v \otimes F$. Let $y$ be a form of type $e$ with level $J$. Then $L y = 0$ implies $y = 0$, and for every form $y'$ of type $e$,
$$\langle L y', L y\rangle_T = C\, c\, \langle y', \mathcal{R}_{S_0^c}\, y\rangle_S.$$

Lean: `New.SiegelWeil.exists_petersson_formLift_eq_rallisSeries` (Lib/SiegelWeil/RallisInner/SharpData.lean).

*Proof.* Take $C = \operatorname{vol}([U(T)])\, Z$. It is not zero, because $Z \neq 0$ for an edge. On forms of type $e$, a real translate scales the Petersson product by $\overline{e(x)}/e(1)$. So the real integral of the formula for sharp data is $Z\, \langle y', z\rangle_S$, with $z = \mathcal{R}_{S_0^c} y$. Here $z$ is a form of type $e$, by the theorem on forms above. This gives the identity. If $L y = 0$, take $y' = z$. Then $C c \langle z, z\rangle_S = 0$, and $C \neq 0$, $c \neq 0$ give $z = 0$. Injectivity of the series gives $y = 0$. $\square$

The constant $C$ does not depend on $a$, $b$, $F$, $J$ or $S_0$. It depends only on the spaces and the real data.

**Remark (Formalization).** The constant $C$ comes from an existence statement. The source does not compute $\operatorname{vol}([U(T)])$ or $Z$. Only $C \neq 0$ is used. In the classical form of the non-vanishing theorem, the lift of a cuspidal $\pi$ is nonzero when an $L$-value of $\pi$ is not zero. Here no $L$-value appears. The unramified part is the operator $\mathcal{R}_{S_0^c}$, and its injectivity replaces the non-vanishing of the $L$-value. The source cites S. Rallis, *Injectivity properties of liftings associated to Weil representations*, Compositio Math. 52 (1984), and J.-S. Li, *Non-vanishing theorems for the cohomology of certain arithmetic quotients*, Crelle 428 (1992), for this kind of result. Its version is proved for unitary groups with $m > 2n$ and for sharp data.

The series can also be written as a sum over cosets.

**Definition.** For forms $y'$, $y$ of type $e$ and a coset $q$ of `localLevel n A`, the *coset term* is $\operatorname{mc}(r_q)\, \langle y', R(r_q) y\rangle_S$.

Lean: `New.SiegelWeil.cosetTerm` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Corollary.** Under the hypotheses of the theorem, there is $A \neq 0$ such that $L$ is injective on forms of level $J$, and $\langle L y', L y\rangle_T$ is the absolutely convergent sum over the cosets $q$ of `localLevel n S₀ᶜ` of $A\, c$ times the coset term of $q$.

Lean: `New.SiegelWeil.rallis_inner_product_cosetTerm` (Lib/SiegelWeil/RallisInner/SharpData.lean).

### The sum of the coefficients in rank one

For a constant function the series is the constant times the sum of the coefficients.

**Definition.** The *vacuum sum* is $\operatorname{vs}_A = \sum_q \operatorname{mc}(r_q)$, over the cosets $q$ of `localLevel n A`. It has the junk value $0$ if the terms are not summable.

Lean: `New.SiegelWeil.vacuumSum`, `New.SiegelWeil.rallisSeries_const` (Lib/SiegelWeil/UnramifiedSeries/RallisSeries.lean).

In rank one, $S$ is a line and $U(S) = U(1)$. Let $\upsilon$ be the splitting character on $U(1)$. The source fixes a sign at each finite place.

**Definition.** Fix a well order on the finite places. The *place sign* $\varepsilon_w$ is $-1$ if $w$ comes before $\bar w$, and $1$ otherwise. So $\varepsilon_w = 1$ if $w = \bar w$, and for a split pair $\{w, \bar w\}$ one sign is $-1$ and the other is $1$.

Lean: `New.placeSign` (Lib/SiegelWeil/RallisInner/SharpData.lean).

**Lemma.** Let $\nu$ have weight $l$ and tame part $\psi$, with $\psi$ trivial at $w$ and $\bar w$, and let $k > 1$. In rank one, the vacuum sum at $\{w, \bar w\}$ for $M = 2k$ and the character $\nu\upsilon^k$ is
$$\prod_{u \in \{w, \bar w\}} \frac{1 - \varepsilon_u\, q_u^{-k}}{1 - \tilde\nu(\varpi_u)^{-1}\, q_u^{-k}},$$
where $\tilde\nu$ is the base change of $\nu$ and $\varpi_u$ is a uniformizer at $u$.

Lean: `New.vacuumSum_pair` (Lib/SiegelWeil/RallisInner/SharpData.lean).

**Theorem.** Let $\nu$ have weight $l$ and tame part $\psi$, trivial off a set $S$ of places. Let $D = S \cup \bar S$, let $T$ have rank $m = 2k$ with $k > 1$, and let $n = 1$. Then
$$\operatorname{vs}_{D^c} = \frac{L^D(k, \nu^{-1})}{\prod_{w \notin D} (1 - \varepsilon_w q_w^{-k})^{-1}},$$
where $L^D$ is the $L$-function of the base change of $\nu^{-1}$ without the factors at $D$, and the vacuum sum is taken for $M = m$ and the character $\nu\upsilon^k$.

Lean: `New.vacuumSum_eq_L_div_eulerProd` (Lib/SiegelWeil/RallisInner/SharpData.lean).

The proof writes both sides as products over the pairs $\{w, \bar w\}$ off $D$ and compares the factors with the lemma.

**Example.** Suppose that $E/F$ is unramified at the places off $D$. Let $v$ be a place of $F$ below a place $w \notin D$, with residue order $N v$.

- If $v$ splits as $w \bar w$, then $q_w = q_{\bar w} = Nv$, and the two signs are $-1$ and $1$. The numerator factors give $(1 + Nv^{-k})(1 - Nv^{-k}) = 1 - Nv^{-2k}$.
- If $v$ is inert, then $w = \bar w$, $\varepsilon_w = 1$ and $q_w = Nv^2$. The factor is $1 - Nv^{-2k}$.

So the denominator is $\zeta_F^{D}(2k)$, the zeta function of $F$ without the places below $D$, at $2k$. The theorem reads $\operatorname{vs}_{D^c} = L^D(k, \nu^{-1}) / \zeta^D_F(2k)$. This is the shape of the classical unramified computation: an $L$-value over a product of zeta values.

**Remark (Formalization).** This evaluation is only in rank one and only for $k > 1$. For $n > 1$ the source keeps the unramified part as the series $\mathcal{R}_{S_0^c}$ and does not identify it with an $L$-value. The norm formula that combines this computation with the inner product formula is `New.LValueData.inner_trivialLift_self_eq_L`, outside this volume. The source cites G. Shimura, Ann. of Math. 102 (1975), T. Yang, J. reine angew. Math. 485 (1997), Harris, Li and Skinner (2005), and Finis, Ann. of Math. 163 (2006), for critical Hecke $L$-values as norms of theta lifts from $U(1)$. It gives no theorem numbers for them.
