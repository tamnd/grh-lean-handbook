---
title: The size of the algebraic part
lean:
  - New/OneLift/HeckeValues/AlgebraicPartSize.lean
decls:
  - New.Data.CriticalPair.sqrt_weylNormSq_pointKernel_le
  - New.Data.CriticalPair.normSqAt_trivialLift_le
  - New.Data.CriticalPair.chosenGroupOrder_mul_denomBound_sq_le
  - New.Data.CriticalPair.norm_map_integralAlgebraicPart_le
  - New.Parameters.exists_eq_star_map_star_and_placePerm_eq
  - New.Data.CriticalPair.norm_trivialLift_sq_eq_mul_inner
  - New.Data.CriticalPair.exists_norm_map_inner_trivialLift_eq_mul
  - New.Data.exists_log_norm_inner_trivialLift_eq
  - New.Data.CriticalPair.exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize
  - New.Data.exists_hasEmptyRow
  - New.Data.CriticalPair.HasEmptyRow.hasLiftRank
  - New.Data.CriticalPair.IsMainPair.negWeight_sub_z_mem_Icc
  - New.Data.heightLe_norm_trivialLift_sq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The size of the algebraic part

The previous section bounds the $\ell$-adic sizes of the algebraic part. This section bounds its archimedean sizes, that is, the absolute values $|\sigma(\cdot)|$ for the automorphisms $\sigma$ of $\mathbb{C}$. There are two results. For a flat pair (`HasEmptyRow`: $c_\tau = z$ at every $\tau$), every conjugate of $n_L L^{\mathrm{alg}}(1)$ is at most $\exp(x^{34})$, by a direct bound on the kernel values. For a main pair, the family $\iota \mapsto \|\varphi_1\|^2$ has height at most $\mathrm{denominatorBudget} - \sum_\tau\mathrm{jetSize}(\kappa_\tau)$. The second result uses the Galois law of [Galois conjugates of the lift](/chapter/character-lifts/#galois-conjugates-of-the-lift) to compare the pair with a flat pair of the same rank.

Here $x$ is the length of the prime sum, $f$ the number of infinite places $\tau \in \Phi$ of $E$, $M = $ `D.M`, $\Omega = $ `P.bigOmega D.towerExp` the period of the tower, and

$$\mathrm{jetSize}(i) = \log i! + i\log(M/\Omega),$$

the size of a derivative of order $i$ ([the data and its sizes](/chapter/data-and-sizes/)). All sizes of the data are those of Volume 1. The phrase "by the sizes of the data" refers to the inequalities that `D.le_of_hasLogBound` gives.

### Flat pairs: a direct bound

**Lemma (One kernel value).** Let $p$ be flat on $n$ and $\sigma \in \mathrm{Aut}(\mathbb{C})$. For all $u \in U(1)(\mathbb{A}_f)$ and $g \in G_f$,

$$\big\|\sigma\circ\kappa^{\mathrm{pt}}_1(u, g)\big\| \leq C = (M^f)^{\#n}\exp\big(c_P(q_1\#n + 1)^2 + f\cdot\#n\cdot\log 4\big),$$

with $c_P = $ `P.constantBound`, $q_1 = $ `P.q₁ D.towerExp`, and the norm the square root of the Weyl norm.

Lean: `New.Data.CriticalPair.sqrt_weylNormSq_pointKernel_le` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* For a flat pair the weight has no boxes (`columnCount = 0`), so the test vector is $1$ with Weyl norm $1$. The datum is the indicator of the block, a function modulo an ideal whose residue ring has $M^f$ elements, with values $0$ and $1$, so every conjugate of a value has norm at most $1$. Such a datum is a vacuum combination (`isAdmissibleCombination_vacuumDatum`). The general bound for the jets of a vacuum combination (`sqrt_weylNormSq_schurJet_le_of_isVacuumCombination`, [theta kernels and gauges](/chapter/theta-kernels-gauges/)) gives the number of residues times `jetSizeBound`. With no boxes, `jetSizeBound` is the exponential factor of $C$. $\square$

**Lemma (Conjugate norms of the lift).** Let `h_rank : p.HasLiftRank n`, $\varphi = \varphi_1$, and assume that every $\sigma$-conjugate of every kernel value has norm at most $C$. Then

$$\|\varphi\|_\sigma^2 \leq e^{x^{30}}\big(e^{x^{30}}C\big)^2.$$

Lean: `New.Data.CriticalPair.normSqAt_trivialLift_le` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* The class numbers of $U(1)$ at the chosen level and of $U(n)$ at the level of $\varphi$ are both at most $e^{x^{30}}$ (`card_stdClasses_le_exp`); for $U(n)$ the level contains the principal level of $\pi_M\pi_N$. With no twist places there is one family of units. So by the finite sum of Section 4, $\|\sigma\circ\varphi(g)\| \leq e^{x^{30}}C$. The conjugate norm is a class sum of $\|\sigma\circ\varphi(g)\|^2/\#\mathrm{Aut}$, so it is at most the class number times the square of this bound (`classSum_le_card_mul_sq`). $\square$

**Lemma (The integer factor).** For a flat pair, $\mathrm{chosenGroupOrder}\cdot n_\nu^2 \leq e^{x^{33}}$.

Lean: `New.Data.CriticalPair.chosenGroupOrder_mul_denomBound_sq_le` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* With no boxes, $n_\nu = M^{4fz}$. So the logarithm is $\log\mathrm{chosenGroupOrder} + 8fz\log M$, which is at most $x^{33}$ by the sizes of the data. $\square$

**Theorem (Flat pairs).** For a flat pair $p$ on $n$ and every $\sigma \in \mathrm{Aut}(\mathbb{C})$,

$$\big|\sigma\big(n_L L^{\mathrm{alg}}(1)\big)\big| \leq e^{x^{34}}.$$

Lean: `New.Data.CriticalPair.norm_map_integralAlgebraicPart_le` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* With no twist, $n_L L^{\mathrm{alg}}(1) = \mathrm{chosenGroupOrder}\cdot n_\nu^2\cdot\langle\varphi, \varphi\rangle$. By Cauchy-Schwarz for the conjugate pairing (`norm_map_inner_le`), $|\sigma\langle\varphi, \varphi\rangle| \leq \|\varphi\|_\sigma^2$. Insert the two lemmas, with $C$ from the first lemma. The logarithm of the product $e^{x^{33}}\cdot e^{x^{30}}(e^{x^{30}}C)^2$ is at most $x^{34}$ by the sizes of the data. $\square$

**Remark (Formalization).** The exponent $34$ is a bound that the source chooses to fit its sizes. The register of findings lists it as F-095, open: it is not known whether the original argument has this bound, or how much room it leaves. The same finding concerns the range $[\kappa_\tau, \kappa_\tau + x^{42}]$ of the jet degrees of a main pair, proved below.

### The Galois law for the squared norm

**Lemma (Conjugating by complex conjugation).** For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ there is $\sigma' \in \mathrm{Gal}(\mathbb{C}/K)$ with $\sigma'(x) = \overline{\sigma(\bar x)}$ for all $x$ and with the same permutation `placePerm s` of the infinite places of $E$.

Lean: `New.Parameters.exists_eq_star_map_star_and_placePerm_eq` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* Conjugation commutes with $K$ as a set, so $\sigma' = \mathrm{conj}\circ\sigma\circ\mathrm{conj}$ fixes $K$. On the embedding $\Phi(1)$ of $E$ the two maps agree, because the conjugate of an embedding in the CM type is the conjugate embedding and $\sigma$ permutes the places (`apply_Phi_eq_Phi_placePerm`). The permutation is read off from this embedding. $\square$

**Lemma (Scales).** Let $A = \mathrm{jetScale}^J\varphi_X$ with $X = $ `lValueData H ϑ` and $J = $ `p.rowLengthSum`. Then

$$\|\varphi_\vartheta\|^2 = |\mathrm{vacuumScale}^{\#n}|^2\cdot M^J\cdot\langle A, A\rangle.$$

Lean: `New.Data.CriticalPair.norm_trivialLift_sq_eq_mul_inner` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* $\varphi_\vartheta = \mathrm{vacuumScale}^{\#n}\,\bar\pi_M^{\,J}\cdot A$, and $|\bar\pi_M|^2 = M$ (`norm_map_star_piMBar_sq`). $\square$

**Theorem (Conjugates of the squared norm).** Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. There is $a > 0$ such that for every pair $p$ with `H : p.HasLiftRank n` there are lift data $Y$ on the places of the trivial twist, with row lengths $\ell^Y_{e\tau} = c_\tau - z$ for $e = $ `placePerm σ`, and

$$|\sigma\langle A, A\rangle| = \big(\sqrt\Omega\big)^{-2J}\cdot a\cdot|\langle\varphi_Y, \varphi_Y\rangle|.$$

Lean: `New.Data.CriticalPair.exists_norm_map_inner_trivialLift_eq_mul` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* Step 1 (the constants). Take $\sigma'$ from the previous lemma. Apply the Galois law `map_trivialLift` of [Galois conjugates of the lift](/chapter/character-lifts/#galois-conjugates-of-the-lift) to $\sigma$ and to $\sigma'$, on the places of the trivial twist (no twist places). It gives $t, c, u$ and $t', c', u'$ with $|t| = |t'| = \Omega^{-1/2}$ and $c, c' \neq 0$. These do not depend on $p$. Put $a = |c'|\,|c|$.

Step 2 (the conjugate character). The character $\mu_X = \nu$ has a weight, so there is a character $\nu^\sigma$ with the permuted weight and $\nu^\sigma(v) = \sigma(\nu(v))$ at the finite points (`HasWeight.exists_conj`). Then also $\nu^\sigma(v) = \sigma'(\nu(v))$ there, since the values lie on the circle. Let $Y$ be the data with the places of $X$, the row lengths permuted by $e$, the character $\nu^\sigma$ and the tame part $\sigma\circ\psi$.

Step 3 (the two laws). The Galois law gives, for every $h$ and index $i$,

$$\sigma(A(h)_i) = t^J c\,\nu_{V,Y}(u)\,\frac{\sigma\Delta}{\Delta}(h')\,\varphi_Y(h)_{i\circ e^{-1}},$$

and the same for $\overline{\sigma(\overline{A(h)_i})}$ with $t'$, $c'$, $u'$ and $\sigma'$.

Step 4 (the multipliers cancel). $\frac{\sigma\Delta}{\Delta}(h')\cdot\overline{\frac{\sigma'\Delta}{\Delta}(h')} = 1$ (`map_finMultiplier_mul_conj`). By the lemma `map_inner_self_eq` on conjugates of class sums, $\sigma\langle A, A\rangle$ is $\overline{t'^J c'\nu_{V,Y}(u')}\cdot t^Jc\,\nu_{V,Y}(u)\cdot\langle\varphi_Y, \varphi_Y\rangle$. Take absolute values. The character values have absolute value $1$. $\square$

**Lemma (The size of a squared norm).** Let $S$ be level places with no twist places. There is $c \in \mathbb{R}$ such that for all data $Y$ on $S$ with $\#n = 2k$ and $k \geq 2$: $\langle\varphi_Y, \varphi_Y\rangle \neq 0$, and there is $r$ with $-4f \leq r$, with $r \leq 4f$ if all row lengths are $0$, and

$$\log|\langle\varphi_Y, \varphi_Y\rangle| = c + r + \sum_\tau\log(\ell^Y_\tau)!.$$

Lean: `New.Data.exists_log_norm_inner_trivialLift_eq` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* By the norm formula `inner_trivialLift_self_eq_L` of [the norm of the lift](/chapter/character-lifts/#the-norm-of-the-lift), $\langle\varphi_Y, \varphi_Y\rangle = C_0\cdot u_S\cdot\prod_\tau\ell_\tau!\cdot d\cdot L$ with $C_0 \neq 0$ and $u_S = \prod_{w\in M}(q_w - 1)$ depending on $n$ and $S$ only, $d$ the dimension of the weight, and $L = L^S(k, \mu^{-1})$. With no twist places, $N(Q) = 1$. Take $c = \log|C_0| + \log u_S$ and $r = \log d + \log|L|$. The Euler product at $k \geq 2$ satisfies $|\log|L|| \leq 4f$ and $L \neq 0$ (`eulerProd_ne_zero_and_abs_log_norm_le`). Since $d \geq 1$, $r \geq -4f$. If all row lengths are $0$, the weight is trivial, $d = 1$, and $r \leq 4f$. $\square$

**Theorem (Conjugates of the norm of the lift).** Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. There is $c$ such that for every pair $p$ with `HasLiftRank n` there is $r$ with $-4f \leq r$, with $r \leq 4f$ if $p$ is flat, and

$$\log\big|\sigma\big(\|\varphi_1\|^2\big)\big| = c + r + \sum_\tau\mathrm{jetSize}(c_\tau - z).$$

Lean: `New.Data.CriticalPair.exists_log_norm_map_norm_sq_trivialLift_eq_add_sum_jetSize` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* By the lemma on scales and the theorem on conjugates, $|\sigma\|\varphi_1\|^2| = v\cdot M^J\cdot\Omega^{-J}\cdot a\cdot|\langle\varphi_Y, \varphi_Y\rangle|$, with $v = |\sigma|\mathrm{vacuumScale}^{\#n}|^2| > 0$. Apply the previous lemma to $Y$, with $c_1$ for $S$ the places of the trivial twist. Put $c = \log v + \log a + c_1$. The row lengths of $Y$ are those of $X$ permuted, so $\sum_\tau\log(\ell^Y_\tau)! = \sum_\tau\log(c_\tau - z)!$, and $J\log(M/\Omega) + \sum_\tau\log(c_\tau - z)! = \sum_\tau\mathrm{jetSize}(c_\tau - z)$. If $p$ is flat, all row lengths of $Y$ are $0$. $\square$

### Flat pairs and main pairs

**Lemma (Flat pairs exist).** Let $4 \leq \#n \leq t$ with $\#n$ even, and let $\chi = (\mu, \psi)$ be a character of weight $0$ with tame part trivial off the chosen places. Then some critical pair $p = (\nu, z)$ is flat on $n$, has tame part $\psi$, and $\nu\upsilon^{\#n/2} = \mu$.

Lean: `New.Data.exists_hasEmptyRow` (New/OneLift/HeckeValues/AlgebraicPartSize.lean), `New.Data.CriticalPair.HasEmptyRow.hasLiftRank` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* Write $\#n = 2z$. Take $\nu = \mu\upsilon^{-z}$ and $c_\tau = z$. Then $\nu$ has weight $-z$ and tame part $\psi$. The bounds $1 \leq z \leq t$ hold since $4 \leq 2z \leq t$, and $z \leq 4b$ by the sizes of the data. The second name records that a flat pair has lift rank, which is part of the definition. $\square$

**Lemma (Jet degrees of a main pair).** Let $p$ be a main pair for $j$. For every $\tau$, $c_\tau - z \in [\kappa_\tau, \kappa_\tau + x^{42}]$, with $\kappa = $ `D.weight`.

Lean: `New.Data.CriticalPair.IsMainPair.negWeight_sub_z_mem_Icc` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* A main pair has $z \leq r$, $c_\tau \leq w_j(\tau)$ and $w_j(\tau) + r \leq c_\tau + t$ ([critical pairs and the ratio](/chapter/twists-critical-pairs/#critical-pairs-and-the-ratio)). The weight of the $j$-th lift satisfies $\kappa_\tau + t \leq w_j(\tau)$ (`k_add_t_add_one_le_halfGap`) and $w_j(\tau) \leq \kappa_\tau + x^{42}$ (`liftWeight_le_weight_add`). So $c_\tau - z \geq w_j - t \geq \kappa_\tau$, and $c_\tau - z \leq w_j \leq \kappa_\tau + x^{42}$. $\square$

**Theorem (Height of the untwisted norm).** Let $p$ be a main pair for $j$. The constant family $\iota \mapsto \|\varphi_1\|^2$ has height at most

$$\mathrm{denominatorBudget} - \sum_\tau\mathrm{jetSize}(\kappa_\tau).$$

Lean: `New.Data.heightLe_norm_trivialLift_sq` (New/OneLift/HeckeValues/AlgebraicPartSize.lean).

*Proof.* Step 1 (a flat pair). $\#\mathrm{RankOneIndex}(z) = 2z$ with $2 \leq z \leq r$, so $4 \leq 2z \leq t = 5r$. By the lemma on flat pairs with $\chi = 1$ there is a flat pair $q$ on the same index set.

Step 2 (the multiplier). Put $H = n_L(q)L^{\mathrm{alg}}_q(1)/\|\varphi_{p,1}\|^2 = \mathrm{chosenGroupOrder}\cdot n_\nu(q)^2\cdot\|\varphi_{q,1}\|^2/\|\varphi_{p,1}\|^2$. It is nonzero, since both lifts are nonzero ([the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part)).

Step 3 (archimedean bound). Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, and take $c$ from the theorem on conjugates for $\sigma$ and this index set. For $q$ it gives $r_0 \leq 4f$ and the sum $0$; for $p$ it gives $r \geq -4f$ and $\sum_\tau\mathrm{jetSize}(c_\tau - z)$. The constant $c$ cancels in $\log|\sigma H|$:

$$\log|\sigma H| = \log\big(\mathrm{chosenGroupOrder}\,n_\nu(q)^2\big) + r_0 - r - \sum_\tau\mathrm{jetSize}(c_\tau - z).$$

By the lemma on the integer factor, the first term is at most $x^{33}$. `jetSize` is increasing (`jetSize_le_add`), and $c_\tau - z \geq \kappa_\tau$ by the lemma on jet degrees. So $\log|\sigma H| \leq x^{33} + 8f - \sum_\tau\mathrm{jetSize}(\kappa_\tau)$, and $x^{33} + 8f \leq \mathrm{denominatorBudget}$ by the sizes of the data. An arbitrary $\sigma \in \mathrm{Aut}(\mathbb{C})$ has the same absolute values as some $\sigma'$ over $K$ (`exists_algEquiv_norm_eq`), since $K$ is imaginary quadratic.

Step 4 (primes). $H\cdot\|\varphi_{p,1}\|^2 = n_L(q)L^{\mathrm{alg}}_q(1)$, which has $|\iota(\cdot)| \leq 1 = e^0$ for every $\iota$ by the corollary of Section 4.

Step 5. Apply the multiplier criterion `HeightLe.of_mul_le` of [twisted lattices](/chapter/twisted-lattices/), with $\alpha = \mathrm{denominatorBudget} - \sum_\tau\mathrm{jetSize}(\kappa_\tau)$ and $e = 0$. $\square$

The proof does not bound $\|\varphi_{p,1}\|^2$ by itself. Its conjugates contain the unknown constant $c$ of the Galois law. The comparison with a flat pair of the same rank and the same places removes $c$, and the flat pair has integral and explicitly bounded algebraic part. The cost is the term $\sum_\tau\mathrm{jetSize}(c_\tau - z)$, which enters with a minus sign: large derivatives make $\|\varphi_{p,1}\|^2$ large, and so its inverse small.

**Remark (Formalization).** The constants $a$ and $c$ come from existence statements, and the theorem on the height does not use their values. The flat pair $q$ is obtained by `obtain` from an existence statement, so it is not explicit either. The theorem asks only that $p$ be a main pair; it uses only $2 \leq z \leq r$ and the lemma on jet degrees.
