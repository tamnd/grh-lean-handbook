---
title: Theorem B, enough forms
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
decls:
  - New.Data.enough_forms
  - New.IsSpread
  - New.IsSpread.exists_few_le_finrank_iSup_range
  - New.IsNearIsometry
  - New.isSpread_of_second_moment
  - New.Data.isSpread_goodPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theorem B, enough forms

Theorem C needs a family that spans almost all of the target, and the source is much smaller than the target. Theorem B says that few translates of $\mathfrak{p}(\mathrm{src})$ are enough: their images span all of the target except a share $4/b^2$, and the number of translates is at most $5\log(1 + 2b^2)$ times the ratio of the dimensions. The proof is linear algebra on top of one analytic fact, a second moment bound for the Poincaré map.

### The statement of Theorem B

**Theorem (Theorem B, enough forms).** The target has dimension $d_T > 0$, and there is a finite set $t \subseteq \bar G$ with

$$\#t \cdot \dim\mathrm{src} \leq 5\, d_T \log(1 + 2b^2)$$

such that the images $s\mathfrak{p}(\mathrm{src})$, $s \in t$, span a subspace of dimension at least $(1 - 4/b^2)\, d_T$.

Lean: `New.Data.enough_forms` (New/Reduction/ShortAndEnough.lean).

The theorem has two parts, and they are used in different places. The bound on $\#t$ multiplies the index bound of Theorem A (b). The bound on the dimension is the hypothesis $n \geq (1 - 4/b^2) d_T$ of Theorem C. The positivity $d_T > 0$ lets the main inequality divide by $d_T$. Theorem B is a statement about ranges, and the scalars $c_B$ and $c_{ss}^{-1}$ in $\mathfrak{p}$ do not change ranges.

### A model case: random subspaces

Let $W$ have dimension $d$, and let $V_1, V_2, \dots$ be subspaces of dimension $v$ in general position. Then $\dim(V_1 + \dots + V_j) = \min(jv, d)$, and $\lceil d/v \rceil$ of them span $W$. Translates of one subspace by a group are not in general position, so the right notion is an average one. Suppose that for every subspace $F$ of $W$ of dimension $\alpha d$, some translate $V_s$ meets $F$ in at most $((1 + \alpha)/2)\, v$ dimensions. Then the greedy choice adds at least $((1 - \alpha)/2)\, v$ new dimensions at each step. The missing share $1 - \alpha$ then decays like $(1 - v/(2d))^j$, and the cover needs about $(2d/v)\log(1/\eta)$ translates to leave a share $\eta$. This is the shape of Theorem B, with $\eta = 2/b^2$.

### Spread and the greedy cover

**Definition (Spread).** Let $V$ and $W$ be finite-dimensional complex spaces, and let $B_s : V \to W$ be linear maps indexed by a set. The maps *spread with the error* $\eta$ if for every subspace $F$ of $W$, with $\alpha = \dim F/\dim W$, there is an index $s$ with

$$\dim B_s^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \eta\Bigr)\dim V.$$

Lean: `New.IsSpread` (New/Spanning/SecondMoment/FewTranslates.lean).

**Remark (Formalization).** The share $\alpha$ is a quotient in $\mathbb{R}$, so it is $0$ if $\dim W = 0$, by the convention $x/0 = 0$. The theorems below assume $\dim W > 0$.

**Theorem (Few maps span almost everything).** Let $V$ and $W$ be finite-dimensional with $V \neq 0$ and $\dim W > 0$. Let $0 < \varepsilon < 1/16$, and let the maps $B_s$ spread with the error $3\varepsilon/2$. Then there is a finite set $t$ of indices with

$$\#t \cdot \dim V \leq \tfrac{5}{2}\bigl(1 + \log(1/(16\varepsilon))\bigr)\dim W \quad\text{and}\quad (1 - 16\varepsilon)\dim W \leq \dim \sum_{s \in t} B_s(V).$$

Lean: `New.IsSpread.exists_few_le_finrank_iSup_range` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Choose the maps greedily. Let $F$ be the span of the images chosen so far, with share $\alpha$, and suppose that $1 - \alpha > 16\varepsilon$. Spread gives $s$ with $\dim B_s^{-1}(F) \leq ((1 + \alpha)/2 + 3\varepsilon/2)\dim V$. Since $\dim(F + B_s V) - \dim F = \dim V - \dim B_s^{-1}(F)$, the step adds at least $((1 - \alpha)/2 - 3\varepsilon/2)\dim V$ dimensions. As $\varepsilon < (1 - \alpha)/16$, this is at least $(1/2 - 3/32)(1 - \alpha)\dim V \geq \frac{2}{5}(1 - \alpha)\dim V$. So each step multiplies the codimension of $F$ by at most $1 - \rho \leq e^{-\rho}$, with the rate $\rho = 2\dim V/(5\dim W)$. After $L$ steps the codimension is at most $\max(16\varepsilon, e^{-L\rho})\dim W$. Take $L = \lceil \log(1/(16\varepsilon))/\rho \rceil$. The first step shows $\rho \leq 1$, so $L \dim V \leq \frac{5}{2}\log(1/(16\varepsilon))\dim W + \dim V \leq \frac{5}{2}(1 + \log(1/(16\varepsilon)))\dim W$. $\square$

### Spread from a second moment

The spread of the Poincaré maps comes from two numbers: how close the projected map is to an isometry, and how much its translates overlap on average. For a linear map $A$ between finite-dimensional inner product spaces, $\|A\|$ denotes the Hilbert-Schmidt norm, and $\mathrm{pr}_U$ is the orthogonal projection onto $U$.

**Definition (Near isometry in mean square).** A linear map $A : S \to T$ is a *near isometry with the error* $\varepsilon$ if $\|A\,\mathrm{pr}_U\|^2 \geq \dim U - \varepsilon\dim S$ for every subspace $U$ of $S$.

Lean: `New.IsNearIsometry` (New/Spanning/SecondMoment/FewTranslates.lean).

**Theorem (One translate).** Let a finite group $\Gamma$ act unitarily on $T$ by $\rho$, and let $\mathrm{pr}_0$ be the orthogonal projection onto a subspace $T_0$ with $\mathrm{pr}_0\,\rho(s) = \rho(s)\,\mathrm{pr}_0$ for all $s$. Let $B : S \to T$ be linear and $\varepsilon \geq 0$. Suppose that $\mathrm{pr}_0 B$ is a near isometry with the error $\varepsilon$, and that

$$\dim T_0 \cdot \sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \leq \#\Gamma\,(1 + \varepsilon)(\dim S)^2.$$

Then the maps $\mathrm{pr}_0\,\rho(s)\,B : S \to T_0$ spread with the error $3\varepsilon/2$.

Lean: `New.isSpread_of_second_moment` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $W \subseteq T_0$ have dimension $\alpha\dim T_0$. By the Cauchy-Schwarz inequality for the Hilbert-Schmidt product, $(\sum_s \|\mathrm{pr}_W\rho(s)B\|^2)^2 \leq \dim W \cdot \#\Gamma\sum_s\|B^*\rho(s)B\|^2 \leq \#\Gamma^2\alpha(1 + \varepsilon)(\dim S)^2$. So some $s$ has $\|\mathrm{pr}_W\rho(s)B\|^2 \leq \sqrt{\alpha(1 + \varepsilon)}\dim S$. Let $U$ be the preimage of $W$ under $\mathrm{pr}_0\rho(s)B$. The map $\mathrm{pr}_0\rho(s)B\,\mathrm{pr}_U$ has image in $W$, and $\rho(s)$ is unitary and commutes with $\mathrm{pr}_0$. So the near isometry gives $\dim U - \varepsilon\dim S \leq \|\mathrm{pr}_W\rho(s)B\|^2$. Hence $\dim U \leq (\sqrt{\alpha(1 + \varepsilon)} + \varepsilon)\dim S \leq ((1 + \alpha)/2 + 3\varepsilon/2)\dim S$, by $\sqrt{uv} \leq (u + v)/2$. $\square$

### The Poincaré maps spread

**Theorem (The good Poincaré maps spread).** The good Poincaré maps $\#\bar G\cdot e_0\,s\,\mathcal{P}$, from all source forms to the target, $s \in \bar G$, spread with the error $\frac{3}{2}(8b^2)^{-1}$.

Lean: `New.Data.isSpread_goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

The proof applies the theorem on one translate with $\varepsilon = (8b^2)^{-1}$ to the Poincaré map $P$ scaled by $(\mathrm{vol}\,J\cdot\nu)^{-1/2}$, where $J$ is the principal level and $\nu$ the covolume of its unipotent points. Volume 10 supplies three facts.

1. *Bad types are rare.* The projection $e_0$ is a product of two central idempotents, one for each level prime, and the coefficient at $1$ of the complement of each has real part at most $b^{-8}/2$ (`New.Data.bad_types_rare`).
2. *Near isometry.* The map $e_0 P$ is a near isometry with the error $5b^{-4}$ (`New.Data.isNearIsometry_e₀_comp_scaledPoincare`).
3. *Second moment.* $\sum_{s\in\bar G}\|P^*sP\|^2 \leq (1 + 9b^{-4})\, D_X^2/(\deg\cdot\mathrm{mass}_r)$, where $\deg$ is the product of the formal degrees at the infinite places and $\mathrm{mass}_r$ is the mass of the genus of the standard lattice of rank $r$ (`New.Data.sum_hilbertSchmidtNorm_scaledPoincare_sq_le`). With $d_T \leq \#\bar G\cdot\deg\cdot\mathrm{mass}_r$ (`New.Data.targetDim_le_card_mul_besselDegree_mul_mass`), this gives the hypothesis of the theorem on one translate.

The sizes give $5b^{-4} \leq (8b^2)^{-1}$ and $9b^{-4} \leq (8b^2)^{-1}$.

### The proof of Theorem B

*Proof.* The target is not zero (`New.Data.finrank_targetForms_ne_zero`), so $d_T > 0$. Apply the theorem on few maps to the good Poincaré maps, with $V$ the space of all source forms, $W$ the target and $\varepsilon = (8b^2)^{-1}$, which is less than $1/16$. It gives $t$ with $\#t\cdot D_X \leq \frac{5}{2}(1 + \log(b^2/2))\, d_T$ and images of dimension at least $(1 - 2/b^2)d_T$, since $16\varepsilon = 2/b^2$. The factor is at most $5\log(1 + 2b^2)$, as $b^2/2 \leq 1 + 2b^2$ and $1 \leq \log(1 + 2b^2)$ (`New.Data.five_halves_mul_one_add_log_le`). Since $\dim\mathrm{src} \leq D_X$, the first bound of the theorem follows.

For the second bound, pass from all source forms to $\mathrm{src}$. For each $s$, the image of $\mathrm{src}$ has codimension at most $D_X - \dim\mathrm{src}$ in the image of all source forms. So the span of the images $s\mathfrak{p}(\mathrm{src})$, $s \in t$, loses at most $\#t(D_X - \dim\mathrm{src})$ dimensions. The ramified forms have codimension at most $f/(N - 1)\cdot D_X$, and $f/(N - 1) \leq b^{-8}$, because $f \leq b$ and $b^9 + 1 \leq N$. So the loss is at most $b^{-8}\cdot\#t D_X \leq b^{-8}\cdot 5\log(1 + 2b^2)\, d_T \leq (2/b^2)\, d_T$. The span has dimension at least $(1 - 2/b^2 - 2/b^2)d_T = (1 - 4/b^2)d_T$. $\square$

### What Theorem B costs

Theorem B costs nothing in size. The factor $5\log(1 + 2b^2)$ multiplies the index cost of Theorem A (b), and the missing share $4/b^2$ is filled in Theorem C at a cost of at most $d_T b$.

### The plan in Volume 10

Volume 10 proves the analytic facts, with an overview in [Theorem B and its plan](/chapter/theorem-b-plan/) and the assembly in [the proof of Theorem B](/chapter/proof-of-theorem-b/). [Few translates suffice](/chapter/few-translates/) is the linear algebra of this section. [Equal multiplicities by the trace formula](/chapter/equal-multiplicities/) gives the dimension $d_T$ and the count by the mass. [Bessel functions at a real place](/chapter/bessel-real-place/) and [Poincaré series and unfolding](/chapter/poincare-series/) build the map $P$ and unfold $P^*sP$. [Moments of the Poincaré map](/chapter/moments/) reduces the second moment to a sum of terms. [The anatomy of a term](/chapter/anatomy-of-a-term/), [the remaining terms](/chapter/remaining-terms/) and [the main term](/chapter/main-term/) bound them, and [local densities at the real places](/chapter/real-densities/) and [at the finite places](/chapter/finite-densities/) compute the main term. The hard part is the error $9b^{-4}$: the second moment must equal its main term up to a relative error far below $b^{-2}$, uniformly in the huge rank $r$.
