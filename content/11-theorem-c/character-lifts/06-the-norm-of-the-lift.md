---
title: The norm of the lift
lean:
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
decls:
  - New.Data.CriticalPair.HasLiftRank
  - New.Data.CriticalPair.HasEmptyRow
  - New.Data.CriticalPair.rowLengthSum
  - New.Data.CriticalPair.denomBound
  - New.Data.CriticalPair.lValueData
  - New.Data.CriticalPair.trivialLift
  - New.Data.CriticalPair.algPart
  - New.Data.CriticalPair.integralAlgebraicPart
  - New.LValueData.index_rangeParabolic_incl
  - New.LValueData.index_stabilizer_inclMatrix_col
  - New.fockPairing_rename_rename
  - New.LValueData.fockPairing_fockPoly_highestVector
  - New.natCard_GL_unit_resField
  - New.LValueData.stdLevelIndex_chosenLevel
  - New.LValueData.relIndex_descentResidueLevel
  - New.LValueData.blockMeanSquare
  - New.LValueData.blockMass_eq_blockMeanSquare_div
  - New.LValueData.isSharp_blockDatum
  - New.LValueData.blockMeanSquare_mul_relIndex_mul_prod_eq_pow
  - New.LValueData.integral_fockInner_realPairWeil
  - New.LValueData.inner_thetaLift_constForm_self
  - New.eulerProd_placeSign_ne_zero
  - New.LValueData.eulerProd_indicator_placeSign
  - New.LValueData.inner_trivialLift_self_eq_L
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The norm of the lift

This section computes $\langle\varphi_X, \varphi_X\rangle$ when the rank is even, $N = 2k$ with $k \geq 2$. The answer is a product of a nonzero constant $C$, simple factors at the chosen places, the hook number and the dimension of the weight, the partial value $L(k, \mu^{-1})$, and $N(Q)^{N-1}$. The proof is a chain of exact identities: the lift of $1$ (Section 4), the comparison with the Petersson product (Section 2), the Rallis inner product formula, and the evaluation of the vacuum sum as an Euler product. The local factors at the places of $X$ are counted in three ways, and their product is $N(Q)^{N-1}$.

### The pair and its lift

The previous chapter [twists, critical pairs and regular families](/chapter/twists-critical-pairs/) defines a critical pair $p = (\nu, z)$, with $\nu$ of weight $-c$, and a tame character $\vartheta$ with a set $Q$ of places. The definitions that turn the pair into lift data are in the file of this section. We list them.

**Definition (Lift rank).** `p.HasLiftRank n` says $\#n = 2z$ and $2 \leq z$. `p.HasEmptyRow n` says in addition $c_\tau = z$ at every infinite place $\tau$.

Lean: `New.Data.CriticalPair.HasLiftRank` (New/OneLift/HeckeValues/CharacterLiftNorm.lean), `New.Data.CriticalPair.HasEmptyRow` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

**Definition (Row length sum and denominator).** The row length sum is $j = \sum_\tau (c_\tau - z)$, the total order of the derivatives. The denominator is $n_\nu = M^{4fz}\,(Md)^j$, with $M = $ `D.M`, $f = $ `D.f` the number of infinite places and $d = $ `P.d`.

Lean: `New.Data.CriticalPair.rowLengthSum` (New/OneLift/HeckeValues/CharacterLiftNorm.lean), `New.Data.CriticalPair.denomBound` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

**Definition (Lift data of a pair).** Under `HasLiftRank`, the data `lValueData H ϑ` have the level places of $\vartheta$ (the chosen places and $Q$), row lengths $c_\tau - z$, the character $\nu\vartheta$ and the tame part of $\nu$ times that of $\vartheta$.

Lean: `New.Data.CriticalPair.lValueData` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

The weight of $\nu\vartheta$ is $-c_\tau = -((c_\tau - z) + z)$, and $z = \lfloor N/2 \rfloor$, so the condition on the weight in `LValueData` holds.

**Definition (Scaled lift and algebraic part).** The scaled lift is

$$\varphi = \mathrm{vacuumScale}^{N}\,\big(\bar\pi\cdot\mathrm{jetScale}\big)^{j}\cdot\varphi_X, \qquad X = \mathrm{lValueData}(H, \vartheta),$$

with $\pi = $ `D.piMBar`. The algebraic part is $L^{\mathrm{alg}}(z, \nu\vartheta) = \|\varphi\|^2 / N(Q)^{N-1}$, and the integral algebraic part is $n_L\, L^{\mathrm{alg}}$ with $n_L = $ `chosenGroupOrder` $\cdot\, n_\nu^2$.

Lean: `New.Data.CriticalPair.trivialLift` (New/OneLift/HeckeValues/CharacterLiftNorm.lean), `New.Data.CriticalPair.algPart` (New/OneLift/HeckeValues/CharacterLiftNorm.lean), `New.Data.CriticalPair.integralAlgebraicPart` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

Since $N = 2z$, the exponent $N - 1$ is the exponent $2z - 1$ of the definition in the previous chapter. The two scales are chosen so that the values of $\varphi$ have the denominator $n_\nu$. The chapter [Hecke values of character lifts](/chapter/hecke-values/) works with these values.

**Remark (Formalization).** `HasLiftRank` asks $2 \leq z$. The norm formula below needs exactly this: $k = z \geq 2$, so that the Euler product at $k$ converges and the Rallis formula applies in rank $N > 2$. Other files of the source put stronger bounds on $z$. These stronger bounds are not used here.

### Indices at the level

Let $w$ be a place of $X$ with residue field $k_w$ of $q$ elements, and let $i_0$ be the index of the line.

**Lemma (Two indices in GL).** (1) The subgroup `rangeParabolic` of $\mathrm{GL}_n(k_w)$, the stabilizer of the span of the basis vectors other than $e_{i_0}$, has index $\sum_{j=0}^{N-1} q^j$. (2) The stabilizer of the column $e_{i_0}$ has index $q^N - 1$.

Lean: `New.LValueData.index_rangeParabolic_incl` (New/OneLift/HeckeValues/CharacterLiftNorm.lean), `New.LValueData.index_stabilizer_inclMatrix_col` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* (1) The inverse transpose maps the stabilizer of a hyperplane to the stabilizer of a line (`index_rangeParabolic`). The orbit of a line is the set of all lines, and there are $(q^N - 1)/(q - 1) = \sum_{j<N} q^j$ of them (`index_stabilizer_line`). (2) The orbit of a nonzero vector is the set of nonzero vectors, and there are $q^N - 1$ of them. $\square$

**Lemma (Units of GL of a line).** $\#\mathrm{GL}_1(k_w) = \#k_w^\times$.

Lean: `New.natCard_GL_unit_resField` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* A $1 \times 1$ matrix is invertible exactly when its entry is a unit. $\square$

**Lemma (Index of the chosen level).** $[K_0(U(1)) : K_M] = \prod_{w \in M} (q_w - 1)$.

Lean: `New.LValueData.stdLevelIndex_chosenLevel` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The chosen level is the kernel of the reduction to $\prod_{w \in M}\mathrm{GL}_1(k_w)$, which is onto. Its index is the order of this product (`relIndex_levelOf`), and each factor has $q_w - 1$ elements. $\square$

**Lemma (Index of the level of V).** The level $K = $ `levelOf (descentResidueLevel)` of the forms on $V$ has index

$$[K_0 : K] = \prod_{w \in M} (q_w^N - 1)\cdot \prod_{w \in Q} \sum_{j=0}^{N-1} q_w^j.$$

Lean: `New.LValueData.relIndex_descentResidueLevel` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The group `descentResidueLevel` is the product, over the places of $X$, of the stabilizer of $e_{i_0}$ at a chosen place and of the stabilizer of the hyperplane at a twist place. The index of a product is the product of the indices (`index_pi_univ`). Apply the lemma on two indices. $\square$

### The block datum

**Definition (Mean square).** $\mathrm{BMS}_X = \prod_{w \in M} q_w^{-N}\cdot\prod_{w \in Q}\dfrac{q_w - 1}{q_w}$.

Lean: `New.LValueData.blockMeanSquare` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

This is the proportion of columns modulo the places in the support of the block function $\Psi$. At a chosen place the reduction must be $e_{i_0}$, one column out of $q^N$. At a twist place the entry in the row $i_0$ must be a unit, and then $|\psi_w|^2 = 1$.

**Lemma (Mass of the block datum).** The mass `blockMass` of the descent pair is $\mathrm{BMS}_X / [K_0(U(1)) : K_M]$.

Lean: `New.LValueData.blockMass_eq_blockMeanSquare_div` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* By definition the mass is the sum of $|\Psi|^2$ over the columns, divided by the number of columns and by $\prod_{w \in M} \#\mathrm{GL}_1(k_w)$. The sum is $\prod_{w \in Q} (q_w - 1)\, q_w^{N-1}$, and the number of columns is $\prod_{w} q_w^N$. Use $(q-1)/q = (q-1)q^{N-1}/q^N$ and the index of the chosen level. $\square$

**Lemma (The block datum is sharp).** The block datum $f_0$ is sharp for $\omega$ with character $\nu_V$, off the set $S_0$ of the places of $X$ and their conjugates, at the level $K_M$, with mass $\mathrm{BMS}_X / [K_0(U(1)) : K_M]$.

Lean: `New.LValueData.isSharp_blockDatum` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The previous chapter proves that the block datum of any descent pair is sharp with mass `blockMass` (`DescentPair.isSharp_blockDatum`). The places of the level modulus are the places of $X$. Use the lemma on the mass. $\square$

The notion of a sharp datum is in [the Rallis inner product formula](/chapter/rallis-inner-product/) of Volume 6.

**Lemma (Local factors).**

$$\mathrm{BMS}_X\cdot[K_0 : K]\cdot\prod_{w \in M \cup Q}\big(1 - q_w^{-N}\big)^{-1} = N(Q)^{N-1}, \qquad N(Q) = \prod_{w \in Q} q_w.$$

Lean: `New.LValueData.blockMeanSquare_mul_relIndex_mul_prod_eq_pow` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Compute place by place. At a chosen place the factor is $q^{-N}(q^N - 1)(1 - q^{-N})^{-1} = 1$. At a twist place it is

$$\frac{q-1}{q}\cdot\sum_{j<N} q^j\cdot\frac{q^N}{q^N - 1} = \frac{q^N - 1}{q}\cdot\frac{q^N}{q^N - 1} = q^{N-1},$$

since $(q - 1)\sum_{j<N}q^j = q^N - 1$ (`mul_geom_sum`). The numbers $q^N - 1$ are nonzero since $q \geq 2$ and $N \geq 1$. $\square$

### The real integral

**Lemma (Fock pairing and renaming).** The Fock pairing $\langle P, Q\rangle = P(\partial)Q(0)$ does not change if the variables of $P$ and $Q$ are renamed along an injective map.

Lean: `New.fockPairing_rename_rename` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The pairing is a jet, and jets commute with injective renaming (`jet_rename`). $\square$

**Lemma (Fock norm of the highest vector).** Let $v^+$ be the highest vector of the weight on $V$. Then $\langle\overline{\mathrm{fockPoly}(v^+)}, \mathrm{fockPoly}(v^+)\rangle$ is the hook number of the weight.

Lean: `New.LValueData.fockPairing_fockPoly_highestVector` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* For the polynomials `toPoly`, the Fock pairing is the hook number times the Gram form (`fockPairing_toPoly_toPoly`). The Gram form of $v^+$ with itself is $1$. By Section 4, `toPoly` is the Fock polynomial with its variables renamed injectively. Use the previous lemma. $\square$

**Lemma (Real integral).** Let $v$ be the Fock vector of `fockPoly(v⁺)`. Then

$$\int_{U(1)(\mathbb{R})}\langle v, \omega_\infty(x, 1)v\rangle\,dx\cdot\langle 1, 1\rangle_{\mathrm{Pet}} = \mathrm{hook}(\kappa)\cdot\mathrm{vol}[U(1)].$$

Lean: `New.LValueData.integral_fockInner_realPairWeil` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The weight of the line is $-\ell_\tau$, and the real Weil action $\omega_\infty(x, 1)$ with this twist fixes $v$ (`realPairWeil_schurCoeffPoly`). So the integrand is the Fock norm of $v$, which is the hook number by the previous lemma. The measure on $U(1)(\mathbb{R})$ has mass $1$. The Petersson product of $1$ with itself is the volume of $[U(1)]$. $\square$

### The Rallis inner product formula for the constant one

**Theorem (Norm of the theta lift of one).** If $N > 2$, then

$$\langle\Theta_W 1, \Theta_W 1\rangle = \frac{\mathrm{vol}[U(1)]\,\mathrm{vol}[U(N)]}{[K_0(U(1)) : K_M]}\cdot d_\kappa\cdot\mathrm{hook}(\kappa)\cdot[K_0 : K]\cdot\mathrm{BMS}_X\cdot\sigma,$$

where $\sigma = $ `vacuumSum Unit N ν_V S₀ᶜ` is the sum of the coefficients of the vacuum off $S_0$.

Lean: `New.LValueData.inner_thetaLift_constForm_self` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Step 1. Let $\theta_1 = \mathrm{lift}(\mathrm{fockDatum}(v^+), 1)$. By the previous chapter, $\theta_1$ is the function attached to $\Theta_W 1$ (`ofAlgForm_thetaLift`).

Step 2. The block datum is sharp with mass $\mathrm{BMS}_X / [K_0(U(1)) : K_M]$, and $1$ is a rapidly decreasing function on $U(1)$. So the Rallis inner product formula for sharp data (`IsSharp.petersson_lift_eq_integral`) gives

$$\langle\theta_1, \theta_1\rangle_{\mathrm{Pet}} = \mathrm{vol}[U(N)]\,\frac{\mathrm{BMS}_X}{[K_0(U(1)):K_M]}\int_{U(1)(\mathbb{R})}\langle v, \omega_\infty(x,1)v\rangle\,\big\langle 1, R(1)(\cdot\, x)\big\rangle_{\mathrm{Pet}}\,dx,$$

with $R$ the Rallis series of the vacuum.

Step 3. Translations fix $1$, so its Rallis series is the constant $\sigma$ (`rallisSeries_const`). The inner integral is $\langle 1, 1\rangle_{\mathrm{Pet}}\,\sigma$, and the real integral is $\mathrm{hook}(\kappa)\,\mathrm{vol}[U(1)]\,\sigma$ by the lemma on the real integral.

Step 4. By the Petersson comparison of Section 2 at the level $K$, $\langle\Theta_W 1, \Theta_W 1\rangle = [K_0:K]\, d_\kappa\,\langle\theta_1, \theta_1\rangle_{\mathrm{Pet}}$. Multiply. $\square$

### The Euler product

Let `placeSign` give $1$ at a place fixed by complex conjugation and the two signs $\pm 1$ to the two places of a split pair. The Euler product of a sign function $s$ at $k$ is $\prod_w (1 - s(w)\,q_w^{-k})^{-1}$. When $E/F$ is unramified at the finite places, the Euler product of `placeSign` at $k$ is $\zeta_F(2k)$.

**Lemma (Nonvanishing).** For $k > 1$, the Euler product of `placeSign` at $k$ is not $0$.

Lean: `New.eulerProd_placeSign_ne_zero` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* The signs have absolute value at most $1$, and the product converges absolutely for $k > 1$. So it is the exponential of a convergent series (`eulerProd_eq_exp_neg_tsum_log_of_norm_le_one`), and an exponential is never $0$. $\square$

**Lemma (Removing the places of X).** If $2k = N$ and $k > 1$, then the Euler product of the signs set to $0$ on $S_0$ is

$$\mathrm{eulerProd}(\mathbf{1}_{S_0^c}\,\mathrm{placeSign}, k) = \mathrm{eulerProd}(\mathrm{placeSign}, k)\cdot\prod_{w \in M\cup Q}\big(1 - q_w^{-N}\big).$$

Lean: `New.LValueData.eulerProd_indicator_placeSign` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Removing the factors at a finite set $S$ multiplies the product by $\prod_{w\in S}(1 - s(w)q_w^{-k})$ (`eulerProd_erase`). The places of $X$ are split and distinct from their conjugates, so $S_0$ is the disjoint union of the pairs $\{w, \bar w\}$. A pair has the signs $1$ and $-1$ and the same norm, and contributes $(1 - q^{-k})(1 + q^{-k}) = 1 - q^{-2k} = 1 - q^{-N}$ (`placeSign_factor_mul`). $\square$

### The norm formula

**Theorem (Norm of the lift of a character).** Let $N = 2k$ with $k > 1$. Put

$$C = \frac{\mathrm{vol}[U(N)]\,\mathrm{vol}[U(1)]}{\mathrm{eulerProd}(\mathrm{placeSign}, k)}.$$

Then $C \neq 0$ and

$$\langle\varphi_X, \varphi_X\rangle = C\cdot\prod_{w\in M}(q_w - 1)\cdot\mathrm{hook}(\kappa)\cdot d_\kappa\cdot L^{S_0}(k, \mu^{-1})\cdot N(Q)^{N-1},$$

where $L^{S_0}(s, \mu^{-1})$ is the $L$-function of $x \mapsto \mu(x/\bar x)^{-1}$ without the factors at $S_0$ (`X.u1Char⁻¹.L X.places`), and $\mathrm{hook}(\kappa) = \prod_\tau \ell_\tau!$ by Section 3.

Lean: `New.LValueData.inner_trivialLift_self_eq_L` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Step 1. The volumes are positive (`measureReal_univ_ne_zero`), and the Euler product is not $0$. So $C \neq 0$.

Step 2. The vacuum sum is a partial $L$-value (`vacuumSum_eq_L_div_eulerProd`, from [the Rallis inner product formula](/chapter/rallis-inner-product/)): with $\nu_V = \mu\,\upsilon^{k}$,

$$\sigma = \frac{L^{S_0}(k, \mu^{-1})}{\mathrm{eulerProd}(\mathbf{1}_{S_0^c}\,\mathrm{placeSign}, k)} = \frac{L^{S_0}(k, \mu^{-1})}{\mathrm{eulerProd}(\mathrm{placeSign}, k)}\cdot\prod_{w\in M\cup Q}\big(1 - q_w^{-N}\big)^{-1},$$

by the lemma on removing the places.

Step 3. By Section 4, $\varphi_X = [K_0(U(1)):K_M]\,\Theta_W 1$, and the index is real. So $\langle\varphi_X, \varphi_X\rangle = [K_0(U(1)):K_M]^2\,\langle\Theta_W 1, \Theta_W 1\rangle$. Insert the theorem on the norm of $\Theta_W 1$ (here $N = 2k > 2$) and Step 2. One power of the index cancels.

Step 4. The local factors $\mathrm{BMS}_X\,[K_0:K]\,\prod(1 - q_w^{-N})^{-1}$ are $N(Q)^{N-1}$. The remaining index is $\prod_{w\in M}(q_w - 1)$. $\square$

In the model case of Section 1 all products are empty and $\mathrm{hook}(\kappa) = d_\kappa = 1$. The theorem gives $\langle\varphi_X, \varphi_X\rangle = C\,L(k, \mu^{-1})$.
