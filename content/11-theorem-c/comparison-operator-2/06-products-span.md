---
title: Products span
lean:
  - New/OneLift/ComparisonOperator/ProductsSpan.lean
decls:
  - New.Data.thetaKernelPairing
  - New.Data.isAdelicHol_star_goodForms
  - New.Data.integral_mul_sum_choiceFn_eq_zero
  - New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Products span

This section proves that a good form $F$ on $W_j$ that is orthogonal to all products $\mathsf{F}_i\,\Theta(\zeta)$ is zero. With the approximation of [the last section](/chapter/comparison-operator-2/#approximation-near-a-peak), only two steps remain. Step 2 turns the orthogonality into a vanishing integral over the real group. Step 4 is the isolation estimate of [the first part](/chapter/comparison-operator-1/#isolation).

Background in one line each. A *good form* on $W_j$ is a form of principal level $\varpi^2$ at the chosen places, of discrete series type, in the image of the idempotent $e_0$ ([single theta lifts](/chapter/single-theta-lifts/#the-lift-and-its-adjoint)). The space $V^\circ$ is definite, with index set $\mathrm{SecondFactorIndex}$: the $r$ indices of $W_j$ and $t - 9m - 1 - r$ further ones. Its classes at level $\varpi^2$ are $\mathrm{SecondFactorClasses}$. The weight $u$ = `New.Data.conjHolomorphicWeight` is the weight of $\bar F$, and $u^\circ$ = `New.Data.kernelWeight` is the weight of the kernel $\theta^\circ$ on $W_j$ ([the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)). Both are $K$-dominant with gap $300n_*$, and the entries of $u$ have modulus at most $5b$ (`New.Data.hasHolGap_conjHolomorphicWeight`, `New.Data.abs_conjHolomorphicWeight_le`).

### The pairing

**Definition (The pairing with $\theta^\circ$).** Let $\zeta$ assign to each class $c$ of $U(V^\circ)$ a vector of the Weyl module of the diagrams $\mu^-$, with the column counts $k^-$ of the untwisted descent pair. Then
$$\Theta(\zeta)(g) = \sum_c \theta^{W_j, V^\circ}\bigl(\mathbf{1}_{\iota}, P_{\overline{\zeta(c)}}\bigr)(g, c),$$
where the kernel has characters $\beta_{W}$ (the character of the descent pair on $W_j$) and $\upsilon^{m/2 - j}$, modulus $\varpi^2$, datum the indicator of the inclusion $\iota$ of $W_j$ in $V^\circ$ modulo $\varpi^2$, and polynomial the letter polynomial of $\overline{\zeta(c)}$ in the variables of the negative basis vectors of $W_j$. The pairing is conjugate linear in $\zeta$.

Lean: `New.Data.thetaKernelPairing` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

### The conjugate of a good form is holomorphic

**Lemma (Holomorphy).** For a good form $F$ and every adelic $g$, the function $h \mapsto \overline{F(g h)}$ on the real group of $W_j$ is holomorphic of weight $u$ for the order $o_W$ = `New.Data.orderW`.

Lean: `New.Data.isAdelicHol_star_goodForms` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Let $L$ be the single lift at the trivial twist. It is injective ([injectivity and the norm](/chapter/single-theta-lifts/#injectivity-and-the-norm-of-one-lift), `New.Data.singleLift_injective`). So $L^*L$ is injective on a finite dimensional space, hence onto, and $F = L^*Ly$ for some $y$. By [the lift and its adjoint](/chapter/single-theta-lifts/#the-lift-and-its-adjoint) (`New.Data.coe_adjoint_singleLift`), $L^*$ is the normalized descent, so $F$ is the normalized descent of $Ly$. Its conjugate is a finite combination of theta kernels $\theta(\cdot, P_\xi)$, where $P_\xi$ is the Fock polynomial of a vector $\xi$ of the Weyl module.

The descent pair fits the parameters, so it has joint harmonics ([existence of joint harmonics](/chapter/local-theta/#existence-of-joint-harmonics), `New.IsMatch.exists_isJointHarmonic`). The polynomial of the highest vector is a product of joint harmonics, hence lies in the holomorphic data of weight $u$ (`New.Rows.prod_mem_holomorphicData`). By the equivariance of the Fock map (`New.DescentPair.realPairWeil_fockPoly`), the polynomial of every vector lies in the holomorphic data too (`New.Rows.mem_holomorphicData_of_highestVector`, [HolomorphicData.lean](lean:Lib/Weil/DualPair/HolomorphicData.lean#L176)). A kernel with a polynomial in the holomorphic data is holomorphic in the real variable ([HolomorphicData.lean](lean:Lib/Weil/DualPair/HolomorphicData.lean#L206), `New.Rows.isAdelicHol_pairTheta`). A finite sum of holomorphic functions of weight $u$ is holomorphic of weight $u$. $\square$

### Step 2: orthogonality on the real group

**Proposition (Step 2).** Let $F$ be a good form such that $\int_{[U(W_j)]} F\,\mathsf{F}_i\,\Theta(\zeta) = 0$ for every choice $i$ and every $\zeta$. Let $m_{u^\circ}$ be integrable. Then for all numbers $c_i$ and every adelic $g$,
$$\int_{U(W_j)_\infty} F(g h)\Bigl(\sum_i c_i\,\mathsf{F}_i(g h)\Bigr)m_{u^\circ}(h)\,dh = 0.$$

Lean: `New.Data.integral_mul_sum_choiceFn_eq_zero` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Each $F\mathsf{F}_i$ is rapidly decreasing of level $\varpi^2$ by [the third exchange](/chapter/comparison-operator-2/#the-third-exchange) (`New.Data.mul_choiceFn_mem_rapidOfLevel`), so the same holds for $\psi = F\sum_i c_i\mathsf{F}_i$.

We have $2\,\mathrm{rank}\,W_j = 2r < t - 9m - 1 = \mathrm{rank}\,V^\circ$, as $t = 5r$ and $100m + 9 < k \leq r$. Let $Q_p$ run over the basis of the Weyl module, written as polynomials in the negative letters. The highest vector is in the holomorphic data of weight $u^\circ$ (`New.Rows.letterPoly_highestVector_mem_holomorphicData`, [neighbours and reproduction](/chapter/siegel-weil/)), and the translates of a polynomial of the module are combinations of the $Q_p$ (`New.realPairWeil_fockLetters`). So the reproducing formula on $(W_j, V^\circ)$ (`New.Rows.reproducing_formula_modKernel`, same chapter) gives numbers $a_p$ with
$$\int\psi(g h)\,m_{u^\circ}(h)\,dh = \sum_p a_p\int_{[U(W_j)]}\psi\,K_p,$$
where $p = (c, q)$ is a class $c$ of $U(V^\circ)$ and a basis index $q$, and $K_p$ is the kernel of $(W_j, V^\circ)$ at the class $c$ with polynomial $Q_q$. It suffices that each $\int\psi K_p$ is $0$.

The basis polynomial $Q_q$ is $P_v$ for some vector $v$, since the map from vectors to polynomials is onto the module (`New.range_toPoly`). Let $\zeta$ be $\bar v$ at the class $c$ and $0$ elsewhere. Then $\Theta(\zeta) = K_p$, as the conjugate of $\bar v$ is $v$. Each $F\mathsf{F}_iK_p$ is rapidly decreasing (`New.Rows.mul_modKernel_mem_rapidOfLevel`), so the integral is linear:
$$\int\psi K_p = \sum_i c_i\int F\,\mathsf{F}_i\,\Theta(\zeta) = 0. \qquad\square$$

**Remark (Formalization).** Before this lemma the file has `seal Finset.sum in`. It stops Lean from unfolding finite sums during definitional checks. It changes only the speed of elaboration, not the statement.

### Step 4: the proof

**Theorem (Products span).** Let $F$ be a good form on $W_j$ with $\int F\,\mathsf{F}_i\,\Theta(\zeta) = 0$ for every choice $i$ and every $\zeta$. Then $F = 0$.

Lean: `New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

*Proof.* Take $\mathsf{F}^0$, its bound $C$ and the approximations from [the approximation theorem](/chapter/comparison-operator-2/#approximation-near-a-peak). It suffices to show $\bar F = 0$. Suppose not.

The form $\bar F$ is rapidly decreasing of level $M\sqrt{-d}$, since $F$ is of level $\varpi^2$, $\varpi\bar\varpi = M$, and conjugation keeps the level (`New.Rows.star_mem_rapidOfLevel`). So $\bar F$ has a peak $g$. At every peak $x$ of $\bar F$, [peaks away from the cusp](/chapter/discrete-series/#the-holomorphic-case-the-cusp-kernel-and-the-character-wave) gives $\lambda_1(x) \geq (5b\cdot b^{23})^{-1/2}$, with $A = 5b$ and $A' = b^{23}$: the gap of $u$ is at least $300n_* \geq 1$, the entries are at most $5b$, $\bar F$ is holomorphic of weight $u$ by the lemma on holomorphy, and the imaginary part of the level is at most $b^{23}$ by the data.

So at every peak $x$ the approximation theorem gives numbers $c_i$ such that $K = \sum_i c_i\mathsf{F}_i(x\,\cdot)$ satisfies $|K(h) - \mathsf{F}^0(h)| \leq \delta|h|^{6n_*}$ with $\delta = 2b^{-19n_*}|\mathsf{F}^0(1)|$. The function $K$ is holomorphic of weight $u - u^\circ$ (`New.Data.isAdelicHol_choiceFn`). By Step 2, with $m_{u^\circ}$ integrable by [isolation](/chapter/comparison-operator-1/#isolation),
$$\int\overline{\bar F(x h)}\,K(h)\,m_{u^\circ}(h)\,dh = \int F(xh)K(h)m_{u^\circ}(h)\,dh = 0.$$
The isolation theorem ([isolation](/chapter/comparison-operator-1/#isolation), `New.Data.norm_apply_one_le_of_forall_isPeak`) now gives
$$|\mathsf{F}^0(1)| \leq (4B + 1)\cdot 2B^{-19}|\mathsf{F}^0(1)|,\qquad B = b^{n_*}.$$
The data give $b > 10$, so $B > 10$. Then $(4B + 1)\cdot 2 < B^2 \leq B^{19}$, so $(4B+1)\cdot 2B^{-19} < 1$. As $|\mathsf{F}^0(1)| > 0$, this is a contradiction. $\square$

### Example: the numbers at the end

**Example (How much room the contradiction has).** Take $B = b^{n_*}$ with $b = 11$ and $n_* = 1$, which is far below the true sizes. Then $(4B + 1)\cdot 2 = 90$ and $B^{19} = 11^{19} \approx 6.1\cdot 10^{19}$. So the factor is about $1.5\cdot 10^{-18}$. In the true data $n_* = 2ft^3$ is of size $10^{20}$ or more, and the factor $2(4B+1)B^{-19}$ is about $8B^{-18}$. The approximation theorem has a loss of $b^{n_*}$ from the integral of $|h|^{6n_*}$ against $m_{u'}$. The isolation estimate has a second loss of $4b^{n_*}$. The gain $b^{-20n_*}$ from sparse sums pays for both with much room.

**Example (Why the good form must be conjugated).** The isolation theorem is about a function $F'$ holomorphic of weight $u$ and the integral of $\overline{F'}Km_{u'}$. Our hypothesis is about $\int FKm_{u^\circ}$. So we apply the theorem to $F' = \bar F$. Its weight is the weight of the conjugate, $u$ = `New.Data.conjHolomorphicWeight`, and this is why the lemma on holomorphy is stated for $\bar F$ and not for $F$.
