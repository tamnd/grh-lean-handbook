---
title: From sides to lattices
lean:
  - New/Congruences/Lifting/CupOrthogonalityBounds.lean
decls:
  - New.Lift.KummerChart.letterJumps
  - New.Lift.KummerChart.universalSide
  - New.Lift.KummerChart.mem_letterJumps
  - New.Lift.KummerChart.fitsWindows_letterJumps
  - New.Lift.KummerChart.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary
  - New.Lift.KummerChart.sum_card_algHom_le_finrank
  - New.Lift.length_quotient_mul_length_residueField
  - New.Lift.InClass.sum_jump_le_finrank
  - New.Lift.KummerChart.sum_jumpMultiplicity_le
  - New.Lift.FitsWindows.neg_add_sub_one_le
  - New.Lift.FitsWindows.neg_add_le_of_opposite
  - New.Lift.FitsWindows.le_add_add
  - New.Lift.KummerChart.le_of_mem_jumpSet_tateDualSide
  - New.Lift.KummerChart.crysCocycles_le_cupOrthogonal_of_no_small_neg_jump
  - New.Lift.KummerChart.dualDefect_le_of_few_low_weights
  - New.Lift.KummerChart.dualDefect_eq_zero_and_dualDefect_le
  - New.Lift.KummerChart.hasCupExponent_any_pattern
  - New.Lift.KummerChart.hasCupExponent_sparse_thick
  - New.Lift.IsTameType
  - New.Lift.lcm_pow_sub_one_le
  - New.Lift.exists_tameChart_e_eq_lcm
  - New.Lift.TameChart.differentBound_le_one
  - New.Lift.KummerChart.linearFrob_comp_subtype
  - New.Lift.TameChart.linearFrob_eq_one
  - New.Lift.TameChart.inClass_of_pow_sub_one
  - New.Lift.noMultipleNear_of_add_lt
  - New.Lift.hasCupExponent_of_isTameType
status: drafted
drafted_by: writer@claude-opus-5-5
---
## From sides to lattices

This section passes from sides to Galois lattices and states the four outputs. The lattice notions are from [duality for crystalline cocycles](/chapter/local-duality/#duality-for-crystalline-cocycles): for a class $\mathcal{Q}$ of lattices, $L^{\perp\mathcal{Q}}$ (cupOrthogonal) is the module of the $c : \Gamma \to L$ whose cup product with every crystalline cocycle of every $Y$ in $\mathcal{Q}$, under every pairing, is a coboundary; the *defect* is $\ell_O(Z_f(L) / (Z_f(L) \cap L^{\perp\mathcal{Q}}))$, a value in $\mathbb{N} \cup \{\infty\}$; and $L$ *has cup exponent* $e$ if $p^e Z_f(L) \subseteq L^{\perp\mathcal{Q}}$. The class $\mathrm{InClass}(F, K, U)$ collects the lattices whose periods fixed on a set of the filter $F$ span, whose Hodge-Tate jumps at each embedding $g$ lie in $U(g)$, and on which each polynomial allowed by $K(s)$ kills $s$, for $s$ in inertia.

### The universal side

**Definition.** Let $k$ be a Kummer chart and $\zeta \in O$ a root with $\zeta^{p^f - 1} = 1$. The *jump set* of $U$ at the letter $i$ is $\{0\} \cup \bigcup_gU(g)$, over the embeddings $g$ with $g(\zeta) = \theta(\omega(i))$, where $\omega(i)$ is the Teichmüller lift of $i$. For $L$ in $\mathrm{InClass}(F, \bot, U)$, with $F$ finer than the subgroup of the chart, the *universal side* of $L$ is the side with the lattice $L$, these jump sets, and the parameter lattice $Z_f(L)$ of all crystalline cocycles, with the trivial action and the identity as cocycle map.

Lean: `New.Lift.KummerChart.letterJumps`, `New.Lift.KummerChart.universalSide`, `New.Lift.KummerChart.mem_letterJumps`, `New.Lift.KummerChart.fitsWindows_letterJumps` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

If every $U(g)$ fits the windows $(\eta, \varepsilon, b, W)$, so does every jump set, since $0 \in [-\eta, \eta]$.

**Lemma (From sides to lattices).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be an open embedding, let $\mathcal{Q} \subseteq \mathrm{InClass}(F, \bot, U)$ and $L \in \mathrm{InClass}(F, \bot, U')$. Let $x \in Z_f(L)$. If for all $Y$ in $\mathcal{Q}$, all pairings $P$ of their universal sides and all $c \in Z_f(Y)$, $(c, x)$ is a scaled cup coboundary with exponent $e$, then $p^ex \in L^{\perp\mathcal{Q}}$.

Lean: `New.Lift.KummerChart.pow_smul_mem_cupOrthogonal_of_isScaledCupCoboundary` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* A pairing of $Y$ and $L$ into $\mathbb{Z}/p^m(1)$ is a pairing of the universal sides. A scaled cup coboundary with exponent $e$ says that the cup product of $c$ and $p^ex$ is a coboundary ([the sides](/chapter/exponent-lattices/#pairing-sides-and-the-pairing-lemma)). This is the condition that defines $L^{\perp\mathcal{Q}}$. $\square$

### Counting

**Lemma (Counting).**

1. An embedding $g$ satisfies $g(\zeta) = \theta(\omega(i))$ for at most one letter $i$, so the numbers $d_i$ of such $g$ add up to at most $\mathrm{rank}_{\mathbb{Z}_p}O$.
2. $\ell_O(O/p) \cdot [k_O : \mathbb{F}_p] = \mathrm{rank}_{\mathbb{Z}_p}O$.
3. For $L$ in a class and any finite $J$, the jumps of $L$ at $g$ in $J$, with multiplicity, number at most $\mathrm{rank}_OL$.
4. If at each $g$ at most $n$ jumps of $L$ lie in $J$, then at most $d_i n$ jumps of the universal side at $i$ lie in $J$.
5. If $v$ fits $(\eta, -\varepsilon, b, W)$, $v'$ fits $(\eta, \varepsilon, b, W)$ and $\eta \leq b$, then $-(v + v') - 1 \leq b + W + \eta$, and in all cases $-(v + v') \leq b + W + 2\eta$. Any bound $B \geq 0$ for these numbers bounds the jumps of the Tate dual side.

Lean: `New.Lift.KummerChart.sum_card_algHom_le_finrank`, `New.Lift.length_quotient_mul_length_residueField`, `New.Lift.InClass.sum_jump_le_finrank`, `New.Lift.KummerChart.sum_jumpMultiplicity_le`, `New.Lift.FitsWindows.neg_add_sub_one_le`, `New.Lift.FitsWindows.neg_add_le_of_opposite`, `New.Lift.FitsWindows.le_add_add`, `New.Lift.KummerChart.le_of_mem_jumpSet_tateDualSide` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* (1) For $i \neq i'$, $\theta(\omega(i)) \neq \theta(\omega(i'))$, so the sets of $g$ are disjoint. (2) $O$ is free over $\mathbb{Z}_p$ of rank $e_Of_O$, and $\ell_O(O/p) = e_O$. (3) The jumps at $g$ with multiplicity number $\mathrm{rank}_OL$ in all. (4) The multiplicity at $i$ is the sum over the $d_i$ embeddings above $i$. (5) The windows have opposite signs, so $v$ and $v'$ are not both below $-\eta$; if one is, the other is at most $\eta$ and the far one at most $b + W$ in absolute value. The jumps of the dual side are $0$ and the $-(v + v') - 1$. $\square$

### The defect

**Theorem (No small negative jump).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be an open embedding, the chart unramified and $p \geq 5$. At each letter let $b_i + W + \eta \leq (p-3)a$, $6(a + \eta + W) < b_i$ and $\mathrm{NoMultipleNear}(p, 6(a+\eta+W), b_i)$. Let $L$ be crystalline with jumps in $U'$, and let the jump sets of $U$ and $U'$ fit $(\eta, -\varepsilon_i, b_i, W)$ and $(\eta, \varepsilon_i, b_i, W)$. If no element of any $U(g)$ or $U'(g)$ lies in $[-a, 0)$, or every $U'(g)$ lies in $[-\eta, 0]$, then $Z_f(L) \subseteq L^{\perp\mathcal{Q}}$ for $\mathcal{Q}$ the crystalline lattices with jumps in $U$.

Lean: `New.Lift.KummerChart.crysCocycles_le_cupOrthogonal_of_no_small_neg_jump` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* By the last lemma, with $e = 0$, it suffices to show the relation with exponent $0$ for the universal sides. All jumps of the two sides are at most $b_i + W + \eta$ since they fit the windows. The same holds for the Tate dual side by part 5 of the counting lemma, as $\eta \leq b_i$. This is at most $(p-3)a$, so by the unramified killer ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)) $E^a$ kills the three cokernels: $\kappa = 0$. The two cases pass from the embeddings to the letters, since $0 \notin [-a, 0)$. On an unramified chart $d = 0$. The [theorem on deep points](/chapter/cup-products/#deep-points) gives the exponent $3(0 + (8n+4) \cdot 0) = 0$. $\square$

**Theorem (Few low jumps for lattices).** In the setting of the last theorem, let $\eta \geq 1$, and let $L$ have at most $m$ jumps in $[-\eta, \eta]$ at each embedding. Then
$$\mathrm{dualDefect} \leq 11f\bigl(m(a+1) + \mathrm{rank}_OL \cdot (W+1)\bigr) \cdot \ell_O(O/p).$$

Lean: `New.Lift.KummerChart.dualDefect_le_of_few_low_weights` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* Multiply both sides by $[k_O : \mathbb{F}_p]$; by part 2 of the counting lemma it suffices to bound the length over $\mathbb{Z}_p$ by $11f(m(a+1) + \mathrm{rank}_OL(W+1))\,\mathrm{rank}_{\mathbb{Z}_p}O$. Let $S$ be the universal side of $L$. By parts 3 and 4, (H4) of [few low jumps](/chapter/cup-products/#few-low-jumps) holds with $n_i = fd_im$ and $r_i = fd_i\,\mathrm{rank}_OL$. The theorem on few low jumps, with the roles of the two sides as there, gives $V \subseteq Z_f(L)$ of colength at most $11\sum_i(fd_im(a+1) + fd_i\,\mathrm{rank}_OL(W+1))$, with exponent $0$ for every $Y$. By the lemma from sides to lattices, $V \subseteq L^{\perp\mathcal{Q}}$. So the defect is at most the colength of $V$, and $\sum_id_i \leq \mathrm{rank}_{\mathbb{Z}_p}O$ by part 1. $\square$

**Theorem (The defect at generic primes).** In the setting of the theorem on no small negative jump, with $\eta \geq 1$:

- (a) if no $U(g)$ or $U'(g)$ meets $[-a, 0)$, or every $U'(g)$ lies in $[-\eta, 0]$, then $\mathrm{dualDefect}(\mathcal{Q}, L) = 0$;
- (b) for every $m$, if $L$ has at most $m$ jumps in $[-\eta, \eta]$ at each embedding, then $\mathrm{dualDefect}(\mathcal{Q}, L) \leq 11f(m(a+1) + \mathrm{rank}_OL\,(W+1))\,\ell_O(O/p)$.

Lean: `New.Lift.KummerChart.dualDefect_eq_zero_and_dualDefect_le` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* The defect is $0$ exactly when $Z_f(L) \subseteq L^{\perp\mathcal{Q}}$. Use the last two theorems. $\square$

### Explicit exponents

**Theorem (Any pattern for lattices).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be an open embedding, the chart unramified, $p \geq 7$, $\eta \geq 1$ and $V + 4\eta \leq M$. Let $L$ be crystalline with jumps in $U'$, and at each letter let the jump sets of $U$ and $U'$ fit $(\eta, \mp\varepsilon_i, \beta_i, V)$, with $\beta_i = b$ at the b-letters and $\beta_i = G$ at the others, and $0 < G \leq b$. If $b < Kp^2$, $2G < Kp$ and $M \leq K$, then $L$ has cup exponent $10^4(K + \lfloor\log_p(2(b+M))\rfloor)$ for the crystalline lattices with jumps in $U$.

Lean: `New.Lift.KummerChart.hasCupExponent_any_pattern` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* Apply the lemma from sides to lattices to the universal sides, with the [theorem on any pattern](/chapter/cup-products/#cuts-and-exponent-bounds) for $W = M$. $\square$

**Theorem (Sparse thick letters for lattices).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be an open embedding and $\eta \geq 1$. Let $L$ be crystalline with jumps in $U'$, and at each letter let the jump sets of $U$ and $U'$ fit $(\eta, \mp\varepsilon_i, \beta_i, V)$, with $\beta_i = b$ at the b-letters and $\beta_i = G$ at the others, and $G + V \leq \eta$. Let $J \geq 1$, and let no three b-letters $i$, $i^{p^s}$, $i^{p^{s+t}}$ occur with $1 \leq s, t \leq J$. Assume that either the chart is unramified, $p \geq 7$ and $10p^J\eta \leq b$, or $\varepsilon$ is constant and $8e \leq p^{J+1}$. Let $2e(b + 5\eta) \leq p^{J+1}\delta$ and $20(J + 1 + d)\eta + \lfloor\log_p(2(b + 5\eta))\rfloor \leq M$, where $e$ is the ramification index of the chart and $d$ is $0$ if $e = 1$ and $v_p(e) + 1$ if not. Then $L$ has cup exponent $10^3(\delta + (J+1)M)$ for the crystalline lattices with jumps in $U$.

Lean: `New.Lift.KummerChart.hasCupExponent_sparse_thick` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* Apply the lemma from sides to lattices with the [theorem on sparse thick letters](/chapter/cup-products/#cuts-and-exponent-bounds), with $X = M$. $\square$

### Tame types

**Definition.** A relation $K$ on polynomials is a *tame type* of sizes $(r, N)$ if $K$ holds for $X^e - 1$, with $e = \mathrm{lcm}_{1 \leq j \leq r}(p^j - 1)$, and for some monic $q \in \mathbb{Z}_p[X]$ of degree at most $N$.

Lean: `New.Lift.IsTameType` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

**Lemma (Tame descent).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be a surjective open embedding.

1. $\mathrm{lcm}_{1 \leq j \leq r}(q^j - 1) \leq q^{r^2}$ for $q > 1$.
2. If $r < p$, there is a [tame chart](/chapter/exponent-lattices/#tame-charts) with $e = \mathrm{lcm}_{1 \leq j \leq r}(p^j - 1)$, and $d \leq 1$ for every tame chart.
3. Restriction to the subgroup of a chart does not change the operator of $s$ on the periods.
4. If $X^e - 1$ kills the inertia operators on the periods of a potentially crystalline $Y$, then those of the inertia elements in the subgroup of the tame chart are $1$.
5. If $K(s)$ allows $X^e - 1$ for every $s$ in inertia, then $\mathrm{InClass}(F, K, U)$ lies in the class of the lattices crystalline over the subgroup with jumps in $U$.
6. If $b + n < q$, then $\mathrm{NoMultipleNear}(q, n, b)$.

Lean: `New.Lift.lcm_pow_sub_one_le`, `New.Lift.exists_tameChart_e_eq_lcm`, `New.Lift.TameChart.differentBound_le_one`, `New.Lift.KummerChart.linearFrob_comp_subtype`, `New.Lift.TameChart.linearFrob_eq_one`, `New.Lift.TameChart.inClass_of_pow_sub_one`, `New.Lift.noMultipleNear_of_add_lt` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* (1) The lcm divides the product, which is less than $q^{1 + \cdots + r} \leq q^{r^2}$. (2) The [existence of tame charts](/chapter/exponent-lattices/#tame-charts) gives a chart for every $e$ prime to $p$, and $e$ is prime to $p$. As $p \nmid e$, $d = 0$ or $1$. (3) The periods of the restriction are the same module, with the same action. (4) On inertia $s \mapsto \beta(s)$ is a homomorphism with open kernel, and $\beta(s)^e = 1$. By tame inertia theory it is trivial on the stabiliser of the root $\varpi^{1/e}$, which contains the inertia elements of the subgroup. (5) By 3 and 4 inertia of the subgroup acts trivially on the periods, and a potentially crystalline lattice with this property is crystalline over the subgroup. (6) A nonzero multiple of $q$ has absolute value at least $q > b + n$. $\square$

**Theorem (Tame types).** Let $\Gamma \to G_{\mathbb{Q}_p}$ be a surjective open embedding. For each $s$ in inertia let $K(s)$ be a tame type of sizes $(r, N)$. Let $L$ lie in $\mathrm{InClass}(F, s \mapsto K(s^{-1}), U')$, and let every $U(g)$ fit $(\eta, -\varepsilon, b, W)$ and every $U'(g)$ fit $(\eta, \varepsilon, b, W)$. If
$$p > b + 6(W + \eta) + r^2(N+1)^2 + 2,$$
then $L$ has cup exponent $3r^2(N+1)^2 + 150(\eta + W + 1)$ for $\mathrm{InClass}(F, K, U)$.

Lean: `New.Lift.hasCupExponent_of_isTameType` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

*Proof.* $r < p$, so part 2 gives a tame chart with $e = \mathrm{lcm}(p^j - 1) \leq p^{r^2}$. By part 5 both $\mathrm{InClass}(F, K, U)$ and $L$ become crystalline over its subgroup. Take $\zeta = 1$; then every embedding lies over the letter $1$. Apply the lemma from sides to lattices. Fix $Y$ and a pairing. The type gives monic $q$ and $q'$ of degree at most $N$ that kill the tame generator on $Y$ and on $L$; the Tate dual of $Y \otimes L$ has a monic killer $q''$ of degree at most $N^2$ ([tame charts](/chapter/exponent-lattices/#tame-charts)). All jumps of the three sides are at most $n = b + 6(W + \eta)$, by part 5 of the counting lemma for the dual side. Let $\kappa = r^2(N+1)^2$. Then $r^2(\deg + 1) \leq \kappa$ for the three killers, and $n + \kappa + 2 < p$, so the tame killer gives $p^\kappa$ for the three cokernels, with $a = 0$. Part 6 gives $\mathrm{NoMultipleNear}(p, 6(\eta + W), b)$. No jump lies in $[0, 0) = \emptyset$. The theorem on deep points gives the exponent $3(\kappa + (8 \cdot 6(\eta + W) + 4)d) \leq 3\kappa + 150(\eta + W + 1)$, since $d \leq 1$. $\square$

**Remark (Formalization).** The defect has values in $\mathbb{N} \cup \{\infty\}$; the bounds show it is finite. For a tame chart the source takes $\zeta = 1$, so all embeddings lie over one letter and the jump sets do not separate them. The constant $d$ is $0$ exactly for $e = 1$.

## Exercises

**Exercise 1.** In the model case $f = 1$, $L = \mathbb{Z}_p$ with the jump $0$ only, compute the bound of part (b) of the defect theorem with $m = 1$ and $W = 0$.

*Hint.* $11(a + 1 + 1) \cdot 1 = 11(a + 2)$, as $\ell(\mathbb{Z}_p/p) = 1$.

**Exercise 2.** Show that the bound $b + W + \eta$ of part 5 of the counting lemma is never attained, and find the largest value of $-(v + v') - 1$.

*Hint.* At most one of $v$, $v'$ is below $-\eta$. Take $v = -(b + W)$ and $v' = -\eta$: the value is $b + W + \eta - 1$.

**Exercise 3.** Let $p = 11$, $\eta = 1$, $W = 0$, $a = 2$. Find all $b$ with $b + W + \eta \leq (p-3)a$ and $6(a + \eta + W) < b$.

*Hint.* There is none: $b \leq 15$ and $b > 18$. In general the two conditions ask $6a + 7 \leq b \leq 8a - 1$, so $a \geq 4$, and $a = 4$ gives only $b = 31$.

## Notes and references

Kisin modules are due to M. Kisin, *Crystalline representations and F-crystals*, Progr. Math. 253 (2006). The source cites A. Iovita and A. Marmora, *Continuity of the finite Bloch-Kato cohomology* (2015), J. Nekovář, *Compatibility of arithmetic and algebraic local constants II* (2018), and P. Čoupek, E. Gazaki and A. Marmora, *Exactness of Breuil-Kisin functors* (2026), among others.

The status. The six files of the chapter have full proofs in the source, with no `sorry` and no axiom. The conditions are explicit hypotheses. No file of the chapter imports a file of a later chapter of Volume 12.

Finding F-088 says that the unramified killer needs $p \geq 5$. In this chapter it enters only through the unramified killing cuts, the long gap, the few low jumps theorems ($p \geq 5$) and the theorem on any pattern ($p \geq 7$). The sparse theorem with a constant sign has no bound on $p$, and the tame theorem needs $p > b + 6(W + \eta) + r^2(N+1)^2 + 2$, so $p \geq 3$. So $p = 2$ is covered only by the sparse theorem with a constant sign, and $p = 3$ only by it and by small tame cases. The finding stays open.

The notes and the plan have small errors. The plan of the volume lists cup products as the ninth chapter and gives it all of the Lifting folder; the volume file puts it eighth and splits the folder with [exponent lattices](/chapter/exponent-lattices/). Research note f-congr gives about 7,000 words for all of Lifting. Finding F-104 records that preprints of 2026 are cited.

The chapter reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
