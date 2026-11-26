---
title: A test form with small pairing
lean:
  - New/OneLift/HeckeValues/TwistedValueHeights.lean
decls:
  - New.rationalU1_sup_integralU1_le_comap
  - New.exists_norm_le_norm_twisted_classSum
  - New.Data.exists_mul_eq_norm_map_le_norm_map_mul
  - New.Data.pointForm_mem_integralForms
  - New.Data.CriticalPair.trivialLiftClassSum
  - New.Data.CriticalPair.trivialLiftClassSum_mem
  - New.Data.CriticalPair.smul_apply_trivialLiftClassSum
  - New.Data.CriticalPair.kernelForm_eq_modKernelStdSpace_of_hasEmptyRow
  - New.Data.twistRow
  - New.Data.testColumn
  - New.Data.testColumn_injective
  - New.Data.inner_pointForm_kernelForm
  - New.Data.isTestForm_trivialLiftClassSum_pointForm
  - New.Data.exists_isTestForm_inner_kernelForm_eq
  - New.Data.modKernel_div_apply
  - New.Data.norm_map_mul_le_iff_le_div
  - New.Data.exists_root_prod_integralAlgebraicPart
  - New.Data.exists_isTestForm_le_norm_inner_trivialLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A test form with small pairing

Let $p$ be a main pair for $j$, with point $z$, and let $\vartheta$ be a twist with $\ell$ prime to $\mathrm{Nm}\,Q$. Let $\varphi = \varphi_\vartheta$ be the lift of $\nu\vartheta$ to $U(2z)$. This section builds a test form $\Xi$ on $U(2z)$ at $\ell$ whose pairing $\langle\Xi, \varphi\rangle$ has a small $\ell$-adic valuation. A test form is integral above $\ell$ and orthogonal to the false lifts ([point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms)). The bound is

$$|\iota(c_0\,\rho)|\cdot\ell^{-F(\ell)} \leq |\iota\langle\Xi, \varphi\rangle|,$$

with a constant $c_0 \neq 0$ independent of $\ell$ and $\vartheta$, $\rho = \mathrm{ratio}(q_2, \vartheta)$ for a flat pair $q_2$ on four indices, and $F(\ell) = $ `D.localPrimeSumTotal ℓ` the exponent of $\ell$ that is forced on derivatives of order $\kappa$.

The idea is a seesaw. Split the $2z$ indices into four blocks of sizes $12$, $4$, $4$ and $2z - 20$. On the first block put a derivative that is not too divisible; such a derivative exists by the sharpness of the divisibility. On the other three blocks put lifts of flat pairs. The pairing of $\varphi$ with the resulting form factors as a product of four theta kernels. The last three are algebraic parts of flat pairs, and their sizes are known from the previous section.

This section uses three results of later chapters of this volume. We state each once.

**Theorem (Sharpness; forward).** Let $l_\tau \in [\kappa_\tau, \kappa_\tau + x^{42}]$ for every $\tau$. There is $t \neq 0$ with $|\sigma t| \leq \exp(fmb/k)$ for all $\sigma$, such that for every modulus $\mathfrak{m} = (\pi_M)$, every prime $\ell$ and every $\iota$ there are an exponent $\gamma$ on $\Phi \times 12$ of degree $l_\tau$ at each $\tau$ and a class $y_0 \in \mathfrak{m}$-residues$^{12}$ with
$$\ell^{-F(\ell)} \leq \Big|\iota\Big(\mathrm{vacuumScale}^{12}\,t^{-1}\prod_\tau l_\tau!\cdot\mathrm{coeff}_\gamma\,\mathrm{twelveTaylor}(\mathbf{1}_{y_0})\Big)\Big|.$$

Lean: `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` (New/Derivatives/Sharpness/BoundAttained.lean), proved in [the divisibility is sharp](/chapter/sharpness/).

**Theorem (Periods of false lifts; forward).** Under the hypotheses listed in the source (the level contains the chosen places and the twist places, the tame part is nontrivial at the twist places, $\Xi$ is killed by the hyperplane sums, by the descent and by a Hecke polynomial at a split place, and $2\#r + 2\#N + 3 < \#n$), the class sum over $h$ of the periods of $\Xi$ against point forms at $(h_1, h)x$ with kernel vectors in the second block is $0$. For $W$ a line with nontrivial tame part at the chosen places, every form in the image of the mean over $\prod_w GL_1(k_w)$ is killed by the hyperplane sums.

Lean: `New.Rows.stdClassSum_period_eq_zero`, `New.Rows.hyperplaneSum_apply_eq_zero_of_rank_one` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean), proved in [false lifts](/chapter/false-lifts/).

The third forward result is used in the next section.

### Two averaging lemmas

**Lemma (Rational and integral units).** Let $\Gamma \supseteq U(1)(K)$ and let $K'$ contain the principal level at the places $w_i \in S$. Then the finite part of a rational norm-one adele, or of an integral one congruent to $1$ at $S$, lies in $\Gamma K'$.

Lean: `New.rationalU1_sup_integralU1_le_comap` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* A rational point is a $1\times 1$ rational matrix, so it lies in $\Gamma$. An integral unit congruent to $1$ at $S$ lies in the standard level, and its reductions at the $w_i$ are $1$, so it lies in the principal level. $\square$

**Lemma (Twisted means).** Let $\Gamma$, $K'$ be as above, with $\Gamma\backslash U(1)(\mathbb{A}_f)/K'$ finite and all stabilizers trivial. Let $\iota : \mathbb{C} \to \mathbb{C}_\ell$ and $s : U(1)(\mathbb{A}_f) \to \mathbb{C}$. There are a translation $z$ and a tame character $\chi$ of weight $0$, trivial off $S$, with
$$|\iota(s(1))| \leq \Big|\iota\Big(\frac{\sum_{[g]}\chi(\det gz)\,s(gz)}{\sum_{[g]}1}\Big)\Big|.$$

Lean: `New.exists_norm_le_norm_twisted_classSum` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The group is commutative, so the double cosets are the cosets of $\Gamma K'$, and a class sum is a sum over the finite group $A = U(1)(\mathbb{A}_f)/\Gamma K'$. By the previous lemma every character $\psi$ of $A$ comes from a tame character $\chi_\psi$ trivial off $S$ (`exists_mem_tameChars`). Take $z$ inverse to the representative of the trivial class. By orthogonality of the characters of $A$, the terms for all $\psi$ sum to $s(1)$. The norm $|\iota(\cdot)|$ is ultrametric, so some term has norm at least $|\iota(s(1))|$. $\square$

**Lemma (Multiplicative pigeonhole).** Let $G$ be a finite group, $\iota$ a ring map to a normed field, and $V^{\#G} = \prod_{\chi\in G}a(\chi)b(\chi)$. For every $\psi$ there are $\phi\chi = \psi$ with $|\iota V| \leq |\iota(a(\phi)b(\chi))|$.

Lean: `New.Data.exists_mul_eq_norm_map_le_norm_map_mul` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Take $\chi$ with $|\iota(a(\psi/\chi)b(\chi))|$ largest. Since $\chi \mapsto \psi/\chi$ permutes $G$, $|\iota V|^{\#G} = \prod_\chi|\iota(a(\psi/\chi)b(\chi))|$, which is at most the largest factor to the power $\#G$. $\square$

**Lemma (A mean of flat values).** Let $q_1(\chi)$ and $q_3(\chi)$ be flat on $n$ and on four indices, for each tame character $\chi$ trivial off the chosen places. There is $L \neq 0$ with $L^{\#G} = \prod_\chi n_L L^{\mathrm{alg}}_{q_3(\chi)}(1)\cdot n_L L^{\mathrm{alg}}_{q_1(\chi)}(1)$ and $|\sigma L| \leq \exp(x^{34})^2$ for all $\sigma$.

Lean: `New.Data.exists_root_prod_integralAlgebraicPart` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* $\mathbb{C}$ is algebraically closed, so a root $L$ exists, and $L \neq 0$ since all factors are nonzero. For $\sigma$, the pigeonhole lemma with $\psi = 1$ gives $|\sigma L| \leq |\sigma(\cdot)\,\sigma(\cdot)|$ for two flat values, and each is at most $e^{x^{34}}$ by the theorem on flat pairs of the previous section. $\square$

### Class sums against flat lifts

Let $q$ be flat on $\mathrm{Fin}\,m$, $\vartheta$ a tame character, $\Xi_q = \varphi_{q,\vartheta}$, $d = n_\nu(q)$ and $X$ lift data.

**Definition (Class sum against a flat lift).** For $F : U(m)(\mathbb{A}_f) \to$ forms for $X$,
$$\mathrm{trivialLiftClassSum}(F) = \mathrm{chosenGroupOrder}\cdot\sum_{[h]}\frac{d}{\mathrm{Nm}\,Q^{m-1}}\,\langle 1, d\,\Xi_q(h)\rangle\cdot F(h),$$
a class sum over $U(m)$ at the level of the lift, with $\langle\,,\rangle$ the pairing `gramForm`.

Lean: `New.Data.CriticalPair.trivialLiftClassSum` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

**Lemma (Integrality).** Let $\ell$ be prime to $\mathrm{Nm}\,Q$. If all $F(h)$ lie in an $\mathcal{O}_{\mathbb{C}_\ell}$-module $N$, so does the class sum.

Lean: `New.Data.CriticalPair.trivialLiftClassSum_mem` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* `chosenGroupOrder` is divisible by the orders of the stabilizers (`card_classAut_dvd_chosenGroupOrder`), so it suffices that each summand lies in $N$. $d/\mathrm{Nm}\,Q^{m-1}$ is $\ell$-integral. In jet degree $0$ the vector $1$ has gauge $1$, and $d\,\Xi_q$ is integral by Section 4, so $\langle 1, d\Xi_q(h)\rangle$ is integral. $\square$

**Lemma (Pairing a class sum).** Let $L$ be conjugate-linear with $L(F(h)) = B\,A\,\kappa_q(g, h)_i$ for all $h$ and coordinates $i$, where $\kappa_q$ is the kernel of the lift data of $\nu_q\vartheta$. Then
$$\Big(\sum_{[u]\in U(1)}1\Big)\,\mathrm{vacuumScale}^m\cdot L(\mathrm{trivialLiftClassSum}(F)) = B\cdot n_L L^{\mathrm{alg}}_q(\vartheta)\cdot A.$$

Lean: `New.Data.CriticalPair.smul_apply_trivialLiftClassSum` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The operators of the central action fix the lift (Section 2), so $\langle\kappa_q(kg), \Xi\rangle = \langle\kappa_q(g), \Xi\rangle$ for all $k$. By adjointness, $\|\Xi\|^2$ is the class sum over $U(1)$ of the conjugate of $\langle\kappa_q(g), \Xi\rangle$. Both sides then unfold to the same double class sum of double sums over coordinates, term by term by the hypothesis. $\square$

**Lemma (Flat kernels).** For $q$ flat on $\mathrm{Fin}\,m$ and every multiple $\mathfrak{m}$ of `levelModulus 2`, each coordinate of the kernel at $(g, h)$ is the theta kernel `modKernelStdSpace` with polynomial $1$, character $\nu\vartheta\upsilon^z$, and the function `residueBlockDatum` read modulo $\mathfrak{m}$.

Lean: `New.Data.CriticalPair.kernelForm_eq_modKernelStdSpace_of_hasEmptyRow` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The row lengths are $0$, so the kernel is the kernel of degree $0$ (`kernelForm_of_rowLength_eq_zero`), and `modKernel_factor` passes to $\mathfrak{m}$. $\square$

### The seesaw

Write $\mathrm{RankOneIndex}(z) = (12 \sqcup (4 \sqcup 4)) \sqcup (2z - 20)$.

**Definition (Twist row and test column).** `twistRow z` is a chosen row of the second block. For a chosen place $i$ and $x_0$ a column of $12$ residues modulo the product of the chosen places, `testColumn` is the column with $x_0$ on the first block and a standard basis vector on each of the other three blocks.

Lean: `New.Data.twistRow`, `New.Data.testColumn`, `New.Data.testColumn_injective` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

The column is injective since its last block is a basis vector.

**Lemma (Integral point forms).** If $v$ has gauge at most $1$ at $h$, the point form with vector $v$ at $h$ is integral at every $\ell$-adic place.

Lean: `New.Data.pointForm_mem_integralForms` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The form is supported on the class of $hk$ with $k$ integral, and $k$ keeps the gauge (`weylGauge_deltaForm_le`, `weylGauge_mul_of_mem_integralAbove`). $\square$

**Theorem (Seesaw at one point).** Let $q_2, q_3, q$ be flat on the last three blocks, $q_2$ at $\vartheta$ and the others at $1$. Let $c$ be an integer vector with Fock polynomial $a\cdot x^\alpha$ in the first block, and let $\chi\cdot\chi_{q_2}\chi_{q_3}\chi_q = \chi_X$ for the characters $\nu\upsilon^z$ of the lift data. Then the pairing of $\kappa_X(g)$ with the point form at $\mathrm{diag}(1, h_2, h_3, h_1)$, datum `testColumn`, row `twistRow` and vector $c$ is
$$a\cdot\mathrm{modKernel}_\chi(\mathbf{1}_{x_0}, x^\alpha)(1, g)\cdot\kappa_{q_2}(g, h_2)_{i_2}\,\kappa_{q_3}(g, h_3)_{i_3}\,\kappa_q(g, h_1)_{i_1}.$$

Lean: `New.Data.inner_pointForm_kernelForm` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Read all four data modulo $\mathfrak{m} = $ `levelModulus 2` of $X$. The datum of the point form is the product of the data of the four blocks: the indicator of $x_0$ on the first, and on the others the tame parts at the twist places, which are trivial at the chosen places and, for the untwisted blocks, trivial everywhere. The pairing with the kernel is the descent of the point form (`normalizedDescent_pointForm`), a kernel `modKernel` with this datum and the polynomial $a\,x^\alpha$. By the lemma on flat kernels the last three factors are kernels `modKernelStdSpace`. The kernel of a block sum is the product of the kernels of the blocks (`modKernelStdSpace_block`), the characters multiply by hypothesis. $\square$

**Theorem (The class sum is a test form).** Let $c$ be fixed by the representation of weight `columnCount` at every $g$ whose columns in the first block are those of the identity. Then for all $h_2, h_3$ the class sum `trivialLiftClassSum` over $h_1$, against the untwisted lift of $q$, of these point forms is a test form at $\ell$.

Lean: `New.Data.isTestForm_trivialLiftClassSum_pointForm` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Integrality: the point is $1$ on the first block, so it fixes $c$, and the integer vector has gauge $1$; apply the lemma on integral point forms and the lemma on integrality. Orthogonality: let $y$ be in the image of the mean over the residue units, killed by the descent and by a Hecke polynomial at a split place $w$. Expand the lift of $q$ over $U(1)$ and exchange the two class sums. The inner sums are periods of $y$ against point forms whose kernel vectors live in the last block, of size $2z - 20$. Since $z > m \geq 10000$, $2\cdot 1 + 2\cdot 20 + 3 < 2z$. The tame part of $p$ is nontrivial at the twist places of $\vartheta$ and at the chosen places, since $p$ is ramified. So the forward theorem on periods of false lifts applies, with the second statement to give the hyperplane sums. Its remaining hypotheses are checked in the source: equivariance holds since $g$ fixes $c$ and weight $0$ is trivial; in weight $0$ every coordinate of the kernel is the same theta constant; and an element of the level fixes the unit column at the chosen places, hence both data. So every period is $0$. $\square$

**Theorem (Seesaw factorisation).** Let $\ell$ be prime to $\mathrm{Nm}\,Q$, let $\alpha$ have degree $\ell^X_\tau$ at each $\tau$, and let the characters multiply as above. There is a test form $\Xi$ at $\ell$ with, for every $g \in U(1)(\mathbb{A}_f)$,
$$\langle\Xi, \kappa_X(g)\rangle\cdot N^3\,\mathrm{vacuumScale}^{2z-12} = \frac{\prod_\tau\ell^X_\tau!}{\alpha!}\,\Lambda\cdot\mathrm{modKernel}_\chi(\mathbf{1}_{x_0}, x^\alpha)(1, g),$$
with $\Lambda = n_LL^{\mathrm{alg}}_q(1)\,n_LL^{\mathrm{alg}}_{q_3}(1)\,n_LL^{\mathrm{alg}}_{q_2}(\vartheta)$ and $N$ the class number of $U(1)$ at the chosen level.

Lean: `New.Data.exists_isTestForm_inner_kernelForm_eq` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* The theorem on monomial vectors of [one exchange and the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data) gives an integer vector $c$ with Fock polynomial $\frac{\prod\ell_\tau!}{\alpha!}x^\alpha$, fixed as required. Take $\Xi$ the triple class sum, over $h_2$ against $q_2$ at $\vartheta$, $h_3$ against $q_3$, and $h_1$ against $q$, of the point forms. By the previous theorem and the lemma on integrality (twice), $\Xi$ is a test form. Apply the lemma on pairing a class sum three times, with the seesaw at one point as the hypothesis. $\square$

### The pairing with the lift

**Lemma (Dividing a character).** $\mathrm{modKernel}_{a, b/\psi}(g, h) = \psi(\det g)\,\mathrm{modKernel}_{a,b}(g, h)$.

Lean: `New.Data.modKernel_div_apply` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

**Lemma (Moving a factor).** For $\rho \neq 0$: $|\iota(V\rho)|\,a \leq |\iota y|$ if and only if $|\iota V|\,a \leq |\iota(y/\rho)|$.

Lean: `New.Data.norm_map_mul_le_iff_le_div` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

Both are direct computations.

**Theorem (A form with small pairing).** Let $p$ be a main pair for $j$ and $q_2$ flat on four indices. There is $c_0 \neq 0$ with $|\sigma c_0| \leq \exp(fmb/k + 3x^{34})$ for all $\sigma$, such that for every prime $\ell$, every $\iota$ and every twist $\vartheta$ with $\ell$ prime to $\mathrm{Nm}\,Q$ some test form $\Xi$ at $\ell$ has
$$|\iota(c_0\cdot\mathrm{ratio}(q_2, \vartheta))|\cdot\ell^{-F(\ell)} \leq |\iota\langle\Xi, \varphi_\vartheta\rangle|.$$

Lean: `New.Data.exists_isTestForm_le_norm_inner_trivialLift` (New/OneLift/HeckeValues/TwistedValueHeights.lean).

*Proof.* Step 1 (constants). For each tame character $\chi$ take flat pairs $q_1(\chi)$ on $2z - 20$ indices and $q_3(\chi)$ on four indices with character $\chi$ (Section 5). The degrees $l_\tau = c_\tau - z$ lie in $[\kappa_\tau, \kappa_\tau + x^{42}]$ (Section 5), so sharpness gives $t$. Take $L$ from the lemma on a mean of flat values and $L_2 = n_LL^{\mathrm{alg}}_{q_2}(1)$. Put $c_0 = t L_2 L$. Its conjugates are at most $e^{fmb/k}\cdot e^{x^{34}}\cdot e^{2x^{34}}$.

Step 2 (the first block). Fix $\ell$, $\iota$, $\vartheta$. Put $\chi_0 = \chi_X/\chi_{q_2}$. Sharpness at $\ell$ gives $\alpha$ and $x_0$. Let $s(g) = \mathrm{modKernel}_{\chi_0}(\mathbf{1}_{x_0}, x^\alpha)(1, g)$. By the sharpness bound, $\ell^{-F(\ell)} \leq |\iota c|\,|\iota s(1)|$ with $c = \mathrm{vacuumScale}^{12}t^{-1}\prod_\tau l_\tau!\,(\bar\pi_M\,\mathrm{jetScale})^{|\alpha|}/\alpha!$.

Step 3 (averaging). The lemma on twisted means gives $z'$ and $\psi$ with $|\iota s(1)| \leq |\iota A|$, $A$ the twisted mean of $s$. The pigeonhole lemma gives $\psi = \psi_3\psi_1$ with $|\iota L| \leq |\iota W|$, $W = n_LL^{\mathrm{alg}}_{q_3(\psi_3)}(1)\,n_LL^{\mathrm{alg}}_{q_1(\psi_1)}(1)$.

Step 4 (the test form). Apply the seesaw factorisation with $\chi = \chi_0/\psi$, $q = q_1(\psi_1)$, $q_3 = q_3(\psi_3)$. The characters multiply correctly because $\psi = \psi_3\psi_1$. By the lemma on dividing a character, the kernel there is $\psi(\det g)\,s(g)$.

Step 5 (the identity). The lift is a class sum of translated kernels (`trivialLift_eq_stdClassSum_translate`), so the pairing $\langle\Xi, \varphi_X\rangle$ is a class sum of the factorisation over $g$. With $|\alpha| = J$ the scalars of $c$ and of $\varphi_\vartheta$ match, and $\mathrm{ratio}(q_2, \vartheta) = n_LL^{\mathrm{alg}}_{q_2}(\vartheta)/L_2$ (`ratio_eq_integralAlgebraicPart_div`, [the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part)). The factor $t$ cancels. The result is
$$tL_2W\cdot cA = N^2\,\langle\Xi, \varphi_\vartheta\rangle/\mathrm{ratio}(q_2, \vartheta).$$

Step 6. The ratio is nonzero, so by the lemma on moving a factor it suffices that $|\iota c_0|\,\ell^{-F(\ell)} \leq |\iota(\langle\Xi,\varphi\rangle/\rho)|$. Chain the bounds of Steps 2 and 3 and the identity. The integer $N^2$ has $|\iota N^2| \leq 1$. $\square$

**Remark (Formalization).** The pairs $q_1$ and $q_3$ are obtained by `choose`, one for each tame character, and only their properties are used. The bound $\exp(x^{34})$ enters $c_0$ three times; see F-095 in Section 5. Two small lemmas on chosen places, `TameChar.tamePart_eq_one_of_isChosen` and `isChosen_levelPlaces_chosenPlace`, live in the file New/Congruences/GaloisRepresentations/SelmerHypotheses.lean of Volume 12, which this file imports. The ratio $\rho$ is nonzero by `ratio_ne_zero`, which the source proves from the nonvanishing `HasWeight.L_ne_zero` (F-120).
