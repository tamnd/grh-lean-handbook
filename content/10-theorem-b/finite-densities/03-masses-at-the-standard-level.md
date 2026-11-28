---
title: Masses at the standard level
lean:
  - New/Spanning/Frames/StandardLevel.lean
  - New/Spanning/Frames/FiniteDepth.lean
decls:
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_mul_heisenbergElem_mem_unitaryLevel_iff
  - New.Floors.IntegralPlace.IsLargeLatticeData.heisenbergMeasure_eq_floorModulus
  - New.Floors.IntegralPlace.IsLargeLatticeData.ascConv_unitaryLevel
  - New.Floors.IntegralPlace.IsLargeLatticeData.ascConv_mconv_unitaryLevel_coset
  - New.Floors.IntegralPlace.IsLargeLatticeData.groupMeasure_boxSet_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.mul_le_mconv_boxSet
  - New.Floors.IntegralPlace.IsLargeLatticeData.volume_intUnits_le_weylLaw_boxSet
  - New.Floors.IntegralPlace.IsLargeLatticeData.le_partialGroupMeasure_boxSet
  - New.Floors.IntegralPlace.IsLargeLatticeData.isHaarMeasure_groupMeasure
  - New.Floors.IntegralPlace.IsLargeLatticeData.inv_two_pow_le_groupMeasure
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Masses at the standard level

The main term is a mass minus an error, so the masses of the congruence subgroups must be known exactly, and that of $K$ up to a factor near $1$. This section computes the Heisenberg mass of $K(g)$, unfolds the group measure over a coset of $K(g)$, and bounds $\mathsf{M}(K)$ from both sides. Throughout, $F$ is a large lattice datum and $g$ is a unit with $g \in R$ and $\bar g = g$.

### The model case of the masses

Let $\varrho = 1$, so there is one Heisenberg group, of floor $0$. Its elements are pairs $(v, \beta)$, with $v$ a vector of the $r_0 = k + 1$ basis vectors of floor above $0$ and $\beta$ skew. The chart is a group isomorphism up to the term $\tau h(v, v)$, and the Heisenberg measure $\eta_0$ is the image of $dv\,d\beta$. The condition that some $u \in \mathsf{U}$ moves the point into $K(g)$ is the condition that $g^{-1}v$ and $g^{-1}\beta$ are integral. So the mass is $|g|^{r_0}$ from $v$ times the skew volume of $gR$, which is $|g|^{1/2}$ because the skew elements are a line over the fixed field. The general case is the same computation on each floor.

### One Heisenberg group

For $a < \varrho$ let $r_a = k + 1 + 2(\varrho - a - 1)$, the rank of the vector part of the Heisenberg group of floor $a$, and let

$$\mathrm{fl}_a(g) = |g|^{r_a}\cdot|g|^{1/2}$$

(`F.floorModulus a g`, [local frames](/chapter/local-frames/#depth)).

**Lemma (Heisenberg points of level g).** Let $a < \varrho$ and let $S$ be a subgroup of $U_{<a}$, the unipotent group of the floors below $a$. For a point $(v, \beta)$ of the Heisenberg group of floor $a$, some $u \in S$ moves it into $K(g)$ if and only if every entry of $g^{-1}v$ and also $g^{-1}\beta$ are integral.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_mul_heisenbergElem_mem_unitaryLevel_iff` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* Write the extension of $v$ by zero as $gw$; then $g^{-1}v$ is integral if and only if $w$ is. If $u\cdot(v, \beta) \in K(g)$ with $u \in S$, a lemma on the gauge of scale $1$ (`New.Floors.Size.mem_vecsOfSize_and_mem_ofSize_of_heisenbergElem`) reads the column of $e^*_a$: it gives that $w$ is integral and that $g^{-1}\beta - \tau g\,h(w, w)$ is integral, where $\tau$ is the fixed element with $\tau + \bar\tau = 1$. Since $J$ is unimodular and $w$ is integral, $h(w, w) \in R$, so $\tau g\,h(w, w) \in R$ and $g^{-1}\beta$ is integral. Conversely take $u = 1$. With $e = e_a$, the Eichler map minus $1$, divided by $g$, is $(w - se)h(e, \cdot) - e\,h(w, \cdot)$ with $s$ integral, and this matrix is integral because $J$ is unimodular. $\square$

**Theorem (Heisenberg mass of a congruence subgroup).** For $a < \varrho$ and a subgroup $S \le U_{<a}$,

$$\eta_a\bigl(\{y : uy \in K(g) \text{ for some } u \in S\}\bigr) = \mathrm{fl}_a(g).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.heisenbergMeasure_eq_floorModulus` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The measure $\eta_a$ is the image of $dv\,d\beta$ under the Heisenberg chart. By the lemma, the preimage of the set is the box $(gR)^{r_a}\times\{\beta : g^{-1}\beta \in R\}$. Each of the $r_a$ coordinates gives $\mathrm{vol}(gR) = |g|$. The skew measure gives the skew elements in $gR$ the mass $|g|^{1/2}$ (`New.Floors.IntegralPlace.skewMeasure_setOf_mul_mem`), because $\bar g = g$. The product is $\mathrm{fl}_a(g)$. $\square$

**Theorem (Mass of K(g) below floor j).** For $j \le \varrho$,

$$\eta_{<j}(K(g)) = \prod_{l < j}\mathrm{fl}_l(g),$$

where $\eta_{<j}$ is the ascending convolution of $\eta_0, \dots, \eta_{j-1}$ (`ascConv heisenbergMeasure j`).

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.ascConv_unitaryLevel` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* By induction on $j$; for $j = 0$ both sides are $1$. The unfolding theorem at a finite place ([Siegel-Weil](/chapter/siegel-weil/#local-densities-at-a-finite-place), `New.Floors.IntegralPlace.ascConv_mconv_unfolding`) says $(\eta_{<j}\ast\theta)(K(g)c^{-1}) = \eta_{<j}(K(g))\cdot\theta(U_{<j}K(g)c^{-1})$ for every s-finite $\theta$. Apply it with $\theta = \eta_j$ and $c = 1$. The last factor is $\mathrm{fl}_j(g)$ by the theorem before, with $S = U_{<j}$. $\square$

**Theorem (Unfolding over all floors).** For every s-finite $\theta$ and every $c \in \mathsf{G}$,

$$(\eta_{<\varrho+2}\ast\theta)\bigl(\{y : yc \in K(g)\}\bigr) = \Bigl(\prod_{l < \varrho}\mathrm{fl}_l(g)\Bigr)\cdot\theta\bigl(\{y : u\,yc \in K(g) \text{ for some } u \in \mathsf{U}\}\bigr).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.ascConv_mconv_unitaryLevel_coset` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The Heisenberg measures of the two top floors are the unit mass at $1$, so $\eta_{<\varrho+2} = \eta_{<\varrho}$. The unfolding theorem gives the product of $\eta_{<\varrho}(K(g))$ and $\theta(U_{<\varrho}K(g)c^{-1})$. The first factor is the theorem before, and $U_{<\varrho} = \mathsf{U}$. $\square$

The product $\prod_{l<\varrho}\mathrm{fl}_l(g)$ appears in every mass of the next section, where it is called the unipotent mass.

### Upper bound for the mass of K

**Theorem (Upper bound for the mass of K).** $\mathsf{M}(K) \le 1 + 2^{-n}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.groupMeasure_boxSet_le` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* Step 1: each floor has mass at most $\zeta = \zeta_R(m)$ on the near points, in the sense `FloorMassLe l ζ 1` of [local frames](/chapter/local-frames/#place-data-floors-and-gauges). For the gauge of scale $1$ every size is $R$, of volume $1$. On floor $l$ solve the quadric in a block: the block kernel of the last section gives mass at most $\zeta|1|^{-(2m+3)} = \zeta$ to the integral points of each fibre, and the other coordinates are free in $R$, of volume $1$. The lemma `New.Floors.Gauge.floorMassLe_one_of_le` turns this into `FloorMassLe l ζ 1`.

Step 2: unfold at the level $1$. The theorem on unfolding over all floors with $g = 1$ and $c = 1$ gives $\mathsf{M}(K) \le \mu_{\ge 0}(\{y : y \text{ near at } \varrho + 2\})$, since $\mathrm{fl}_l(1) = 1$ and $\mathsf{U}K$ is the set of points near at $\varrho + 2$.

Step 3: the lemma on the mass of the near points ([local frames](/chapter/local-frames/#place-data-floors-and-gauges)) bounds this by $\zeta^n$, and field 1 of a large lattice datum gives $\zeta^n \le 1 + 2^{-n}$. $\square$

### Lower bound for the mass of K

**Lemma (Boxes in convolutions).** For measures $\sigma$ and $\theta$ with $\theta$ s-finite, $\sigma(K)\,\theta(K) \le (\sigma\ast\theta)(K)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.mul_le_mconv_boxSet` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* $K$ is a group, so $K\cdot K \subseteq K$, and the convolution of the restrictions to $K$ is carried by $K$. $\square$

**Lemma (Weyl elements of units).** For every floor $l$, $\lambda_l(K) \ge \mathrm{vol}(R^\times)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.volume_intUnits_le_weylLaw_boxSet` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The measure $\lambda_l$ is the image of $|c|^{d}\,dc$, $d = r_l$, under $c \mapsto w_l(c)^{-1}$. For a unit $u$ of $R$, the Weyl element $w_l(u)$ is an integral isometry with integral inverse, so it lies in $K$. On $R^\times$ the density $|u|^d$ equals $1$. So $\lambda_l(K) \ge \int_{R^\times}|c|^d\,dc \ge \mathrm{vol}(R^\times)$. $\square$

**Theorem (Lower bound on the partial measures).** For $l + i = \varrho$,

$$\mathrm{vol}(R^\times)^{i+1} \le \mathfrak{m}_{l,\,i+2}(K),$$

where $\mathfrak{m}_{l,\,i+2}$ is the convolution of the floor measures of the $i + 2$ floors from $l$ on (`F.partialGroupMeasure l (i + 2)`).

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.le_partialGroupMeasure_boxSet` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* By induction on $i$, from the top. For $i = 0$, $l = \varrho$ and $\mathfrak{m}_{\varrho, 2} = \eta_H\ast\theta_{\varrho}$. The lattice datum gives $\eta_H(K) = 1$ and $\theta_\varrho(K) \ge \mathrm{vol}(R^\times)$, and the lemma on boxes concludes. For the step, $\eta_l(K) = \mathrm{fl}_l(1) = 1$ by the Heisenberg mass with $g = 1$ and $S$ trivial. So

$$\mathrm{vol}(R^\times)^{i+2} \le \mathfrak{m}_{l+1,\,i+2}(K)\cdot\eta_l(K)\cdot\lambda_l(K)\cdot\eta_l(K),$$

by the induction hypothesis and the lemma on Weyl elements. Three uses of the lemma on boxes bound the right side by the mass of $\mathfrak{m}_{l+1,\,i+2}\ast(\eta_l\ast(\lambda_l\ast\eta_l))$, which is $\mathfrak{m}_{l,\,i+3}(K)$. $\square$

**Theorem (Lower bound for the mass of K).** Let $B \ge 2$ and let the non-units of $R$ have volume at most $B^{-1}$. Then $2^{-n} \le \mathsf{M}(K)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.inv_two_pow_le_groupMeasure` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* $\mathrm{vol}(R^\times) \ge \mathrm{vol}(R) - \mathrm{vol}(R \setminus R^\times) \ge 1 - B^{-1} \ge 1/2$. The theorem before with $l = 0$ and $i = \varrho$ gives $\mathsf{M}(K) \ge \mathrm{vol}(R^\times)^{\varrho+1} \ge 2^{-n}$. $\square$

**Example.** For one finite place with residue field of $q$ elements, the non-units are the maximal ideal, of volume $q^{-1}$. So $B = q$ works, and $\mathsf{M}(K) \ge (1 - q^{-1})^n$. For a finite set of places the non-units are the elements that are non-units at some place, of volume at most $\sum_v q_v^{-1}$; the hypothesis asks this sum to be at most $1/2$.

**Remark.** The two bounds give $2^{-n} \le \mathsf{M}(K) \le 1 + 2^{-n}$. The upper bound uses the ideal zeta value and holds for every large lattice datum. The lower bound needs the hypothesis on the non-units, which is why it is a separate theorem. Both are used: the upper bound in the main term, the lower bound in [the chapter on moments](/chapter/moments/).

### The group measure is a Haar measure

**Theorem (Haar measure).** For a large lattice datum, $\mathsf{M}$ is a Haar measure on $\mathsf{G}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.isHaarMeasure_groupMeasure` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* $\mathsf{M}$ is right invariant ([local frames](/chapter/local-frames/#place-data-floors-and-gauges)). Field 3 of a large lattice datum gives a Haar measure $\nu$ that is right invariant, so $\mathsf{M} = d\cdot\nu$ for some $d \in [0, \infty]$ by uniqueness of right invariant measures. Then $d \neq 0$ because $\mathsf{M} \neq 0$. And $d \neq \infty$: $\nu(K) > 0$ since $K$ is open and contains $1$, and $\mathsf{M}(K) \le 1 + 2^{-n}$ is finite. A positive finite multiple of a Haar measure is a Haar measure. $\square$

**Remark (Formalization).** The source proves the theorem as an instance. So every lemma of the library on Haar measures applies to $\mathsf{M}$ at a large lattice datum without a further argument. The finiteness of $d$ is the only place where the upper bound for $\mathsf{M}(K)$ is used in this file.
