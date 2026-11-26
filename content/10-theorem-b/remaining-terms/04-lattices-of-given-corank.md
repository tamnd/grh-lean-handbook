---
title: Lattices of given corank
lean:
  - New/Spanning/RemainingTerms/LatticesOfCorank.lean
decls:
  - New.Filling.sum_classes_le_of_sum_translates_le
  - New.Filling.inv_mul_mem_of_inverseRowsCongruent
  - New.Filling.RowVanishesModPiN
  - New.Filling.discWeightIfRowVanishes
  - New.Filling.LatticeStabilizerCoset
  - New.Filling.map_le_and_rowVanishesModPiN_of_out_eq
  - New.Filling.tsum_discriminant_inv_le_of_out_eq
  - New.Filling.exists_mk_out_eq_embFin_mul
  - New.Filling.encard_le_of_vecMul_mem_smul
  - New.Filling.encard_rowVanishesModPiN_le
  - New.Filling.exists_saturatedLattice_encard_rowVanishesModPiN_le
  - New.Filling.mul_inv_pow_le_of_mul_le
  - New.Filling.exists_sum_discWeightIfRowVanishes_le
  - New.Filling.tsum_index_saturatedLattice_le
  - New.Filling.sum_tsum_discWeightIfRowVanishes_le
  - New.Filling.mul_rootDiscr_pow_le_tailScale_pow_div
  - New.Filling.sum_discriminant_inv_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lattices of given corank

The size of a term below the top cell is controlled by the discriminant of a lattice in $X_0$: the lattice that the link vectors of the term generate ([link vectors and the splitting](/chapter/remaining-terms/#link-vectors-and-the-splitting)). To sum the sizes, the chapter needs a bound for the sum of $(\operatorname{disc}L)^{-k}$ over all lattices $L$ of given rank in the lattice $\Lambda_c \cap X_0$ of a class, summed over the classes. This section proves that bound.

The idea is an average. The lattice of a class $c$ is a unimodular lattice $u\hat{\mathcal{O}}^\kappa$ cut down by one linear condition: a linear form must vanish modulo $\bar\pi$. A lattice $L$ of corank $l$ lies in the lattice of the class only if the form vanishes on $L$ modulo $\bar\pi$. As $u$ is fixed and the form moves over its $N^{kf}$ or so possible values, the form vanishes on $L$ for only about $N^{lf}$ of them. So on average over the classes, the weight of $L$ is cut down by $N^{-(k-l)f}$, and then the sum over the lattices of a unimodular lattice is bounded by Siegel's lemma.

Throughout, $\bar\pi$ is the finite idele with $\pi\bar\pi = N$, the lattice $\Lambda_c \cap X_0$ consists of the vectors $v$ with $g^{-1}v$ integral and with entry $k_0$ divisible by $\bar\pi$, for the chosen representative $g$ of $c$, and $\operatorname{disc}$ is the discriminant in rank $r$ of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/). $H = \operatorname{discriminantBound} = b^{n^3f}$.

### An average over the classes

**Lemma (Averaging over the classes).** Let $A$ be finite and nonempty, with a map $a$ into the finite adelic unitary group of $X_0$. Let $F \geq 0$ be a function on the classes and $B \geq 0$. If $\sum_{\varphi \in A}F([u\,a(\varphi)]) \leq \#A\cdot B$ for every $u$, then $\sum_cF(c) \leq \#\mathrm{Classes}\cdot B$.

Lean: `New.Filling.sum_classes_le_of_sum_translates_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Each $F(c)$ is a term of one of the sums, so it is finite. Put $\delta(g) = B - F([g])$. It is invariant on the left under the rational points and on the right under the level, so it is a smooth automorphic function. The hypothesis says that $\sum_\varphi\delta(g\,a(\varphi)) \geq 0$ for every $g$. The class integral of a nonnegative function is nonnegative, and the class integral is invariant under right translation. So $\#A$ times the integral of $\delta$ is at least $0$. As the level fixes $\delta$, the integral of $\delta$ is $\sum_c(B - F(c))$. So $\sum_cF(c) \leq \#\mathrm{Classes}\cdot B$. $\square$

The average is taken over the cosets of a subgroup of the integral unitary group.

**Definition.** $\mathrm{Cos}$ (`LatticeStabilizerCoset`) is the quotient of the integral unitary group of $X_0$ by its subgroup of matrices whose row $k_0$ is congruent to that of $1$ modulo $\bar\pi$. For $u$ in the finite adelic unitary group and $y$ integral, the form of $y$ is the row $k_0$ of $y^{-1}u^{-1}$. It vanishes on $L$ modulo $\bar\pi$ (`RowVanishesModPiN`) if its values on $L$ lie in $\hat{\mathcal{O}}\bar\pi$. The weight $w_{u,y,r}(L)$ (`discWeightIfRowVanishes`) is $(\operatorname{disc}_rL)^{-k}$ if the form of $y$ vanishes on $L$ modulo $\bar\pi$, and $0$ otherwise.

Lean: `New.Filling.LatticeStabilizerCoset`, `New.Filling.RowVanishesModPiN`, `New.Filling.discWeightIfRowVanishes` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

**Lemma (Congruent rows give one coset).** If the rows $k_0$ of $y^{-1}$ and $y'^{-1}$ are congruent modulo $\bar\pi$, then $y$ and $y'$ have the same image in $\mathrm{Cos}$.

Lean: `New.Filling.inv_mul_mem_of_inverseRowsCongruent` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Row $k_0$ of $y^{-1}y'$ is row $k_0$ of $y^{-1}$ times $y'$. Row $k_0$ of $y'^{-1}y'$ is that of $1$. Their difference is the difference of the rows times the integral matrix $y'$, so it is divisible by $\bar\pi$. $\square$

**Lemma (Representatives of translates).** For $u$ and $\varphi \in \mathrm{Cos}$ there are a rational $\eta$ and an integral $y$ in the coset $\varphi$ such that the chosen representative of the class of $u\,\varphi^{\mathrm{out}}$ is $\eta\,u\,y$.

Lean: `New.Filling.exists_mk_out_eq_embFin_mul` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* The chosen representative is $\eta\,u\,\varphi^{\mathrm{out}}g$ with $\eta$ rational and $g$ in the level. The level is the preimage of $K(M)$, so $g$ lies in the subgroup that defines $\mathrm{Cos}$. Put $y = \varphi^{\mathrm{out}}g$. $\square$

**Lemma (From the class to a unimodular lattice).** Let the chosen representative of $c$ be $\eta u y$. The sum of $(\operatorname{disc}_rL)^{-k}$ over the lattices $L \subset \Lambda_c \cap X_0$ of rank $r$ with $\operatorname{disc}_rL \leq H$ is at most the sum of $w_{u,y,r}(L)$ over the lattices $L \subset u\hat{\mathcal{O}}^\kappa$ of rank $r$ with $\operatorname{disc}_rL \leq H$.

Lean: `New.Filling.tsum_discriminant_inv_le_of_out_eq` (New/Spanning/RemainingTerms/LatticesOfCorank.lean), with `New.Filling.map_le_and_rowVanishesModPiN_of_out_eq`.

*Proof.* For $L \subset \Lambda_c \cap X_0$ and $v \in L$, the vector $y^{-1}u^{-1}\eta^{-1}v$ is integral with entry $k_0$ divisible by $\bar\pi$. So $\eta^{-1}L \subset u\hat{\mathcal{O}}^\kappa$, and the form of $y$ vanishes on $\eta^{-1}L$ modulo $\bar\pi$. The map $L \mapsto \eta^{-1}L$ is injective, and as $\eta$ is a rational isometry it keeps the rank and the discriminant. $\square$

### Few forms vanish on a lattice

**Lemma (Few forms vanish on a sublattice).** Let $m$ be a basis of a primitive sublattice of rank $r$ and corank $l$ of $\hat{\mathcal{O}}^\pi$, let $A$ be an integral invertible matrix, and let $d$ be an integral idele. Let $Y_a$, for $a$ in a set $B$, be integral forms that are pairwise incongruent modulo $d$ and whose values on the lattice with basis $mA$ are divisible by $d$. Then $\#B \leq [\det A]\,[d]^l$, where $[\cdot]$ is the generalized index.

Lean: `New.Filling.encard_le_of_vecMul_mem_smul` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Extend $m$ to an integral basis $U$ of $\hat{\mathcal{O}}^\pi$ with integral inverse. Write the values of $Y_a$ on $mA$ as $dW_a$, with $W_a$ integral. The class of $W_a$ modulo the row lattice of $A$ has $[\det A]$ possible values, and it fixes the values of $Y_a$ on $m$ modulo $d$. The values of $Y_a$ on the other $l$ columns of $U$ have $[d]^l$ classes modulo $d$. If two forms agree in both classes, they agree modulo $d$ on all of $U$, so they are congruent modulo $d$ and hence equal. $\square$

**Lemma (Few cosets kill a lattice).** Let $y_\varphi$ lie in the coset $\varphi$ for each $\varphi \in \mathrm{Cos}$. Let $L \subset u\hat{\mathcal{O}}^\kappa$ be a lattice of rank $r$ and corank $l$. There is a subspace $V$ of dimension $r$ such that $L$ has a finite index $i$ in the lattice $\Lambda_V$ of the adelic points of $V$ in $u\hat{\mathcal{O}}^\kappa$, $\operatorname{disc}_rL = i\operatorname{disc}\Lambda_V$, and the form of $y_\varphi$ vanishes on $L$ modulo $\bar\pi$ for at most $i(N^f)^l$ of the $\varphi$.

Lean: `New.Filling.exists_saturatedLattice_encard_rowVanishesModPiN_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean), with `New.Filling.encard_rowVanishesModPiN_le`.

*Proof.* $L$ has a basis $mA$, where $m$ is a basis of $\Lambda_V$ and $A$ is integral; then $i = [\det A]$ and $\operatorname{disc}_rL = \operatorname{disc}\Lambda_V\cdot[\det A]$. Apply the previous lemma to the rows $k_0$ of $y_\varphi^{-1}$, with $d = \bar\pi$, whose index is $N^f$. Two of these rows that are congruent modulo $\bar\pi$ belong to the same coset, by the lemma on congruent rows. $\square$

**Lemma (Exponents).** Let $d, i \geq 1$ with $di \leq H$, and $r \leq k$. Then for every $\mu$, $i(di)^{-k} \leq H^{\mu+2}d^{-k-1}i^{-r-\mu}$.

Lean: `New.Filling.mul_inv_pow_le_of_mul_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Write $i(di)^{-k} = i(di)^{\mu+1}\cdot d^{-(k+\mu+1)}i^{-(k+\mu+1)}$. Bound $i$ and $di$ by $H$, $d^{-(k+\mu+1)}$ by $d^{-(k+1)}$ and $i^{-(k+\mu+1)}$ by $i^{-(r+\mu)}$. $\square$

**Lemma (One lattice, all cosets).** In the situation above, with $L$ of discriminant at most $H$, for every $\mu$,

$$\sum_{\varphi}w_{u,y_\varphi,r}(L) \leq (N^f)^lH^{\mu+2}\cdot\operatorname{disc}(\Lambda_V)^{-k-1}\cdot i^{-r-\mu}.$$

Lean: `New.Filling.exists_sum_discWeightIfRowVanishes_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* The sum is the number of $\varphi$ whose form vanishes on $L$, at most $i(N^f)^l$, times $(di)^{-k}$ with $d = \operatorname{disc}\Lambda_V \geq 1$. Apply the lemma on exponents. $\square$

### The sum over a unimodular lattice

**Lemma (Sublattices of finite index).** For every subspace $V$, the sum of $[\Lambda_V : M]^{-\dim V - 2\varrho - 4}$ over the sublattices $M$ of finite index in $\Lambda_V$ is at most $2^k$.

Lean: `New.Filling.tsum_index_saturatedLattice_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* By [the bound for sublattices of a lattice](/decl/New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le/) the sum is at most $\zeta_{\hat{\mathcal{O}}}(2\varrho + 4)^{\dim V}$, where $\zeta_{\hat{\mathcal{O}}}(\mu)$ is the sum of $[\hat{\mathcal{O}} : I]^{-\mu}$ over the ideals of finite index. A standing bound on the degree of $E$ and [the bound for powers of the zeta sum](/decl/New.idealZeta_intAdeles_pow_le/) of [the chapter on the Siegel-Weil formula](/chapter/siegel-weil/) give $\zeta_{\hat{\mathcal{O}}}(2\varrho + 4)^{\varrho+1} \leq 2$, so $\zeta_{\hat{\mathcal{O}}}(2\varrho + 4) \leq 2$. And $\dim V \leq k$. $\square$

**Lemma (All lattices and all cosets).** Let $r + l = k$. Then

$$\sum_{\varphi \in \mathrm{Cos}}\ \sum_{L}w_{u,y_\varphi,r}(L) \leq (N^f)^lH^{2\varrho+6}\cdot(200fk\operatorname{rd}_E)^{f(k+1)l}\cdot 2^k,$$

where $L$ runs over the lattices of rank $r$ in $u\hat{\mathcal{O}}^\kappa$ with $\operatorname{disc}_rL \leq H$, and $\operatorname{rd}_E$ is the root discriminant.

Lean: `New.Filling.sum_tsum_discWeightIfRowVanishes_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Exchange the sums. For each $L$ choose $V$ as in the lemma on one lattice, with $\mu = 2\varrho + 4$. The map $L \mapsto (V, L)$ is injective, so the sum is at most

$$(N^f)^lH^{2\varrho+6}\sum_{V \text{ of codim } l}\operatorname{disc}(\Lambda_V)^{-k-1}\sum_{M}[\Lambda_V : M]^{-\dim V - 2\varrho - 4}.$$

The inner sum is at most $2^k$. The sum over $V$ is at most $(200fk\operatorname{rd}_E)^{f(k+1)l}$ by [the theorem on the height zeta function](/decl/New.Filling.tsum_sublatticeDiscriminant_inv_le/), a consequence of Siegel's lemma in [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/). $\square$

**Lemma (The constants).** For every $l$,

$$(N^f)^lH^{2\varrho+6}(200fk\operatorname{rd}_E)^{f(k+1)l}2^k \leq \tau^{l+1}/b^f.$$

Lean: `New.Filling.mul_rootDiscr_pow_le_tailScale_pow_div` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* Split the left side as $b^{-f}\cdot X\cdot Y^l$ with $X = b^fH^{2\varrho+6}2^k$ and $Y = N^f(200fk\operatorname{rd}_E)^{f(k+1)}$. Since $2^k \leq b^k \leq b^f$ (by the standing hypothesis $k \leq f$), $X \leq b^{(n^3(2\varrho+6)+2)f} \leq \tau$ by the bound $n^3(2\varrho + 6) + 2 \leq 10^5n^9$. For $Y$, compare the $1000$th powers: $N^{1000} \leq b^{60000n}$ and $(200fk\operatorname{rd}_E)^{1000} \leq b^{k+1}$ by the standing hypotheses, so $Y^{1000} \leq b^{(60000n + k + 1)f} \leq b^{250kf} = \tau^{1000}$, as $1000(2\varrho+2) \leq k$. $\square$

**Theorem (Lattices of given corank).** Let $S$ be admissible and $r + l = k$. Then

$$\sum_{c}\ \sum_{L}(\operatorname{disc}_rL)^{-k} \leq \frac{\#\mathrm{Classes}}{N^{kf}}\,\tau^{l+1},$$

where $L$ runs over the lattices of rank $r$ in $\Lambda_c \cap X_0$ with $\operatorname{disc}_rL \leq b^{n^3f}$.

Lean: `New.Filling.sum_discriminant_inv_le` (New/Spanning/RemainingTerms/LatticesOfCorank.lean).

*Proof.* By the standing hypothesis `le_relIndex`, $\#\mathrm{Cos} \geq (N^k/b)^f > 0$; in particular $\mathrm{Cos}$ is finite. Apply the averaging lemma with $A = \mathrm{Cos}$, $a(\varphi) = \varphi^{\mathrm{out}}$ and $B = \tau^{l+1}/N^{kf}$. Fix $u$, and choose $\eta_\varphi, y_\varphi$ by the lemma on representatives of translates. By the lemma from the class to a unimodular lattice, the sum over $\varphi$ of the inner sums for the classes $[u\,\varphi^{\mathrm{out}}]$ is at most the double sum of the weights. This is at most $\tau^{l+1}/b^f$ by the last two lemmas. Finally

$$\frac{\tau^{l+1}}{b^f} = \Big(\frac{N^k}{b}\Big)^f\frac{\tau^{l+1}}{N^{kf}} \leq \#\mathrm{Cos}\cdot\frac{\tau^{l+1}}{N^{kf}}. \qquad \square$$

**Remark (Formalization).** The sums are in $[0, \infty]$, so the theorem asserts in particular that the double sum is finite. The index in `le_relIndex` is a relative index of subgroups, which is $0$ if it is infinite; the hypothesis $(N^k/b)^f \leq$ index with a positive left side excludes that case, and the proof uses this to make $\mathrm{Cos}$ a finite type. The elements $\eta_\varphi$, $y_\varphi$ and the subspaces $V$ are chosen with `choose`; the bounds do not depend on the choices.

**Example.** Let $l = 0$, so that $L$ has full rank $k$. Then the bound is $\#\mathrm{Classes}\cdot\tau/N^{kf}$. Without the average, a single unimodular lattice $u\hat{\mathcal{O}}^\kappa$ contains itself, of discriminant $1$, so the weight of one class could be as large as $1$. The condition modulo $\bar\pi$ removes this: only a proportion of about $N^{-kf}$ of the forms vanish on a full lattice of index prime to $N$. The factor $\tau^{l+1}$ pays for the number of lattices and for the constants of Siegel's lemma; it is small against the gains of [the gain](/chapter/remaining-terms/#the-gain).
