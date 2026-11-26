---
title: The third exchange
lean:
  - New/OneLift/ComparisonOperator/ThreeExchanges.lean
decls:
  - New.Data.enlargedSpace
  - New.Data.enlargedPoint
  - New.Data.signOrder
  - New.Data.signs_eq_blockSigns_signOrder
  - New.Data.invariantTraceChar
  - New.Data.invariantTraceChar_mul
  - New.Data.twistedChiMod
  - New.Data.thirdExchangeKernel
  - New.Data.thirdExchangeLeftSide
  - New.Data.firstFactorChar_mul_upsilonU1_pow
  - New.Data.isTameFor_twistedChiMPow_mul_carrierChar
  - New.Data.matchedPoly_constantRows
  - New.Data.integral_carrierForm_mul_eq_card_mul_choiceFn
  - New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn
  - New.Data.productDatum
  - New.Data.stdClassSum_thirdExchangeKernel_productDatum
  - New.Data.stdClassSum_thirdExchangeKernel_eq_productDatum
  - New.Data.thirdExchangeLeftSide_eq_kernelClassSum
  - New.Data.goodForms_mem_rapidOfLevel
  - New.Data.polyVector_letterPoly_mem_holomorphicData
  - New.Data.exists_choiceFn_eq_mul_kernelClassSum
  - New.Data.mul_choiceFn_mem_rapidOfLevel
  - New.Data.isAdelicHol_choiceFn
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The third exchange

The third exchange equates a double class sum of kernels with $\mathsf{F}_i$, up to a number $c_\vartheta$ with $|c_\vartheta|^2 = C/\Gamma_j(\vartheta)$. The double sum is then rewritten as a theta series on $U(W_j)$. Last, we show that $\mathsf{F}_i$ is holomorphic and that $F\,\mathsf{F}_i$ has level $\varpi^2$ for a good form $F$.

Background in one line each, all from [the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data) unless said otherwise. $\varpi$ is the product of the chosen places, and the twist modulus $\varpi^2Q$ adds the places $Q$ of $\vartheta$. $V''$ is the standard definite space on the index set `FirstFactorIndex j`. $\chi' = \chi^j\vartheta$ is `twistedChiMPow`. $\nu''$ = `firstFactorChar` is the character of the $j$-th lift times a power of $\upsilon$. The character `carrierChar j` has trivial tame part and does not depend on $\vartheta$ (`New.Data.carrierChar_hasWeight`). A choice $i$ has a matrix $\Lambda$ modulo $\varpi^2$, a class $h^\flat$ of $U(W^\flat)$ and lists of short rows. $\psi_\Lambda$ = `traceChar Λ` is the additive character $x \mapsto \psi(\mathrm{tr}\,\Lambda x)$. The function $\mathsf{F}_i$ = `choiceFn j i` is the integral of $\varphi^\circ$ against the kernel of $S$ and $W' = W_j \oplus I_j^- \oplus I_{3m-j} \oplus W^\flat$ with datum $\psi_\Lambda$. The theta series `kernelClassSum` and the vectors `leftSideSeries` are in [the first part](/chapter/comparison-operator-1/#descent-of-product-forms) and [its Section 7](/chapter/comparison-operator-1/#line-coordinates).

### The spaces and the data

**Definition (The enlarged space and point).** The space $W' = ((W_j \oplus (I_j^- \oplus I_{2m + (m-j)})) \oplus W^\flat)$ has $W^\flat$ the standard definite space on the $6m + 1$ indices `FlatIndex`. Its basis is indexed by `FirstFactorIndex j`, like that of $V''$, with the signs `padSigns j` on the first three summands and $1$ on $W^\flat$. For a choice $i$ and $g$ in the group of $W_j$, the point $(g, 1, 1, h^\flat)$ of $U(W')$ has $h^\flat$ the class representative of $i$.

Lean: `New.Data.enlargedSpace`, `New.Data.enlargedPoint` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Definition (The sign order).** The bijection `signOrder j` lists the basis of $W = I_{3m} \oplus W'$ in two blocks: first the positive vectors (the first `posRank j` vectors of $W_j$, numbered by `rowIndexOfNumber`, and the added positive indices), then the $m$ negative vectors (from `negIndex j`).

Lean: `New.Data.signOrder` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Lemma (The signs are block signs).** The signs of $W$, which are $1$ on $I_{3m}$, `padSigns j` on the first three summands of $W'$ and $1$ on $W^\flat$, are $1$ on the first block and $-1$ on the second block of `signOrder j`.

Lean: `New.Data.signs_eq_blockSigns_signOrder` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Check each kind of index. The first `posRank j` vectors of $W_j$ have sign $1$ by the definition of `signsW`. The added indices have sign $1$. The negative vectors are those of $I_j^-$ and the later vectors of $W_j$, and `negIndex` lists exactly these. $\square$

**Definition (The invariant trace character).** For $\Lambda$ modulo $\varpi^2$ and $x$ modulo $\varpi^2Q$,
$$\psi^{\mathrm{inv}}_\Lambda(x) = \sum_{\gamma \in GL_{3m}(O/\varpi^2)} \psi_\Lambda(\bar x\gamma),$$
where $\bar x$ is $x$ read modulo $\varpi^2$. The character $\chi'_{\mathrm{mod}}$ = `twistedChiMod` of the residue ring modulo $\varpi^2Q$ is the one that the tame part of $\chi'$ induces.

Lean: `New.Data.invariantTraceChar`, `New.Data.twistedChiMod` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Lemma.** $\psi^{\mathrm{inv}}_\Lambda(x\gamma) = \psi^{\mathrm{inv}}_\Lambda(x)$ for every invertible $\gamma$ modulo $\varpi^2Q$.

Lean: `New.Data.invariantTraceChar_mul` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Substitute $\gamma' = \bar\gamma\gamma'$ in the sum over $GL_{3m}(O/\varpi^2)$. This is a bijection. $\square$

**Definition (The kernel and the left side).** The kernel of the third exchange at $(h', h)$ is the kernel of $(W, V'')$ with characters $\chi'\cdot$`carrierChar j` and $\nu''$, modulus $\varpi^2Q$, a datum $\Psi$, and the polynomial `stackedDetProd` of the constant rows of $i$, read through `posEquiv j` and moved to the rows of $W$ by `signOrder j`. The point is $((1, h'), (g, 1, 1, h^\flat))$ in $U(W)$ and $h$ in $U(V'')$. The *left side* is
$$\mathrm{LS}_\vartheta(i, g) = \mathrm{cs}_{h'}\Bigl(\mathsf{a}(\chi', h')\,\mathrm{cs}_h\bigl(K_\vartheta(i, g, \Psi_\Lambda)(h', h)\bigr)\Bigr),\quad \Psi_\Lambda(x', x'') = \chi'_{\mathrm{mod}}(\det x'')\,\psi^{\mathrm{inv}}_\Lambda(x''^{-1}x').$$

Lean: `New.Data.thirdExchangeKernel`, `New.Data.thirdExchangeLeftSide` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Lemma (Characters).** (a) $\nu''\upsilon^m = \chi'\cdot\mathrm{carrierChar}_j$. (b) $\chi'\cdot\mathrm{carrierChar}_j$ is tame for $\varpi^2Q$ with the character $\chi'_{\mathrm{mod}}$, of weight $m - \#\mathrm{DetIndex}(j, \tau)$ at $\tau$.

Lean: `New.Data.firstFactorChar_mul_upsilonU1_pow`, `New.Data.isTameFor_twistedChiMPow_mul_carrierChar` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* (a) Write all four characters as products of $\chi$, $\vartheta$, $\mu_j^0$ and powers of $\upsilon$, and compare the exponents. (b) $\chi'$ is tame of weight $0$ for $\varpi^2Q$ ([tameness of twisted characters](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)). `carrierChar j` has trivial tame part and weight $m + e_j - w_j(\tau)$, with $e_j$ = `firstFactorCharExp j`. The count $\#\mathrm{DetIndex}(j, \tau) + e_j = w_j(\tau)$ turns this into $m - \#\mathrm{DetIndex}(j, \tau)$. A product of a tame character and one with trivial tame part is tame with the same character. $\square$

Three more identities, private in the source, match the exchanges with the pairs of [Section 2](/chapter/comparison-operator-2/#the-three-pairs-and-the-hecke-product). With $n = j + \lfloor(t - 11m - 1)/2\rfloor$:
$$\frac{\mathrm{carrierChar}_j^{-1}}{\chi'}\,\upsilon^{3m + z_*} = \frac{\vartheta^{-1}}{\nu_*},\qquad \chi'^{-1}\upsilon^m = \frac{\vartheta^{-1}}{\nu_1},\qquad \chi'\upsilon^{m/2} = \frac{\vartheta}{\nu_{-1}}.$$
Each is a comparison of exponents.

**Lemma (The matched polynomial of the constant rows).** For the constant rows of a row choice, the polynomial `matchedPoly` of the exchange identity, for the identity on the $3m$ columns and `signOrder j` on the rows, is `paddedMinorProd j` in the rows of $W_j$ and the padding, times the determinants `pairedDetProd` that pair the variables of the rows of $W^\flat$ with the short rows $i.\mathrm{rows}(\tau, k)$ read at $\tau$.

Lean: `New.Data.matchedPoly_constantRows` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* The constant rows are either basis vectors of $W_j$ and the padding, or short rows. Expand `matchedPoly` as a product over places and over the blocks. A determinant of basis rows times the variables is a minor of the variables in those rows. A determinant of short rows times the variables is a factor of `pairedDetProd`. The exponents agree by a count of indices. $\square$

### The exchange

**Lemma (Translates of the datum).** For a choice $i$ and every $g$,
$$\int_{[U(S)]}\varphi^\circ(x)\,\theta^{S, W'}_{\upsilon^m, \mathrm{carrierChar}_j}\bigl[\psi^{\mathrm{inv}}_\Lambda, P_i\bigr]\bigl(x, (g, 1, 1, h^\flat)\bigr)\,dx = \#GL_{3m}(O/\varpi^2)\;\mathsf{F}_i(g),$$
where $P_i$ is the polynomial of the previous lemma.

Lean: `New.Data.integral_carrierForm_mul_eq_card_mul_choiceFn` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* By [Section 3](/chapter/comparison-operator-2/#the-carrier), applied to the tame character $\chi'$ of weight $0$, $\varphi^\circ$ is in $\mathrm{rapidOfLevel}(S, 1)$. Level $1$ with the trivial modulus means that $\varphi^\circ$ is invariant under all of `stdLevel`. `carrierChar j` has trivial tame part. So the lemma on translates ([one exchange](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)) applies with $\mathfrak{m}' = \varpi^2Q \subseteq \varpi^2$: the integral with the sum of translates of $\psi_\Lambda$ is $\#GL_{3m}$ times the integral with $\psi_\Lambda$, which is $\mathsf{F}_i(g)$. $\square$

**Theorem (The three exchanges).** There are $C \in \mathbb{C}$ and $c : \mathrm{Twist} \to \mathbb{C}$ such that, for every twist $\vartheta$, $|c_\vartheta|^2 = C/\Gamma_j(\vartheta)$ and $c_\vartheta\,\mathrm{LS}_\vartheta(i, g) = \mathsf{F}_i(g)$ for all $i$ and $g$.

Lean: `New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Step 1 (ranks). $\#V'' = 3m + 2z_*$, by counting the indices, and so $2m + 2 \leq \#(I_{3m} \sqcup V'')$.

Step 2 (the exchange). Apply the explicit exchange identity to $W = I_{3m} \oplus W'$, $V = V''$, $V' = S$, with `posEquiv j`, `signOrder j`, the block signs lemma, Step 1, and the rows `DetIndex j`. By `choose`, this gives a constant $C_3$ and, for each character tame of the right weight, a number $c_3$ with $|c_3|^2 = C_3/L_*(\ldots)$ and the identity (b) for all matched pairs. We use it for $\chi'\cdot\mathrm{carrierChar}_j$, which is tame by the lemma on characters.

Step 3 (the carrier). By `choose` on the carrier identity, get $C_{12}$ and, for the tame $\chi'$ of weight $0$, the number $c_{12}$ with $c_{12}\,\mathrm{cs}(\mathsf{a}\,\theta) = \varphi^\circ$.

Step 4 (the constants). Let $N = \#GL_{3m}(O/\varpi^2)$. Put $C = C_3C_{12}/N^2$ and $c_\vartheta = c_3c_{12}/N$. Then $|c_\vartheta|^2$ is $C$ divided by three $L_*$ factors. The places of $\varpi^2Q$ are the chosen places and $Q$. The three character identities above turn the three characters into $(\nu_*\vartheta)^{-1}$, $(\nu_1\vartheta)^{-1}$ and $(\nu_{-1}\vartheta^{-1})^{-1}$, at the points $z_*$, $m$ and $m/2$. This is the definition of $\Gamma_j(\vartheta)$.

Step 5 (the identity). As $N \neq 0$, it is enough to show $c_3c_{12}\,\mathrm{LS}_\vartheta(i, g) = N\,\mathsf{F}_i(g)$. By the lemma on translates, the right side is the integral of $\varphi^\circ$ against the kernel with $\psi^{\mathrm{inv}}_\Lambda$. Apply the one exchange theorem with $E^b = I_{3m}$, $W' = W'$, the carrier identity of Step 3 as the class sum identity, and the invariance of $\psi^{\mathrm{inv}}_\Lambda$. Its hypothesis is Step 2 for each matched pair, once we rewrite its polynomial by the lemma on the matched polynomial and its character by $\nu'' = \chi'\,\mathrm{carrierChar}_j\,\upsilon^{-m}$. $\square$

**Remark (Formalization).** The number $C$ comes from `choose` and may be $0$. Nothing here bounds it below. [Section 8](/chapter/comparison-operator-2/#integrality-false-lifts-and-the-seesaw) proves that the twist factor built from $c_\vartheta$ is not $0$, by a separate argument.

### The left side is a theta series

**Definition (The product datum).** For rows $w$ modulo $\varpi^2$ and $x = (x'\;x'')$ with $x''$ square,
$$\Psi^\times_{w,\Lambda}(x) = \mathrm{col}_w(x''|_{W_j})\cdot\begin{cases}\psi^{\mathrm{inv}}_\Lambda(x') & \text{if the columns of } x'' \text{ off } W_j \text{ are those of } 1,\\ 0 & \text{otherwise,}\end{cases}$$
where $\mathrm{col}_w$ = `columnDatum` is the datum of [the row stabilizer theorem](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data).

Lean: `New.Data.productDatum` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

**Lemma (The class sum of the product datum).** For all $w$, $i$, $g$ and $h$, the class sum over $h'$ of $\mathsf{a}(\chi', h')$ times the third kernel with datum $\Psi^\times_{w,\Lambda}$ is the kernel of $(W_j, V'')$ at $(g, h)$ with characters `charW` of the descent pair and $\nu''$, datum $\mathrm{col}_w$ and polynomial `letterPoly` of the vector `leftSideSeries` $(\vartheta, j, i, h)$.

Lean: `New.Data.stdClassSum_thirdExchangeKernel_productDatum` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Expand the vector `leftSideSeries` in its coordinates. The right side becomes a sum of kernels, one per coordinate, each on the index set of $W_j \oplus I_j^- \oplus W^{\mathrm{add}}$. On the left, expand $\mathsf{a}$ and use the seesaw `modKernel_sum_left` backwards to join the kernel of $(I_m, I_{3m})$ with the third kernel. Relabel by `regroupEquiv j` with `modKernel_reindex`. Then compare argument by argument. The spaces agree entry by entry. For the characters, $W_j$ has $m - j$ negative signs and $\upsilon^m = \upsilon^{m-j}\upsilon^j$. The data agree by the definition of $\Psi^\times$. The polynomials agree by `renameRowsCols_stackedDetProd_eq_sum`, which writes the stacked determinants as the sum over the coordinates of `paddedMinorProd`. The points agree entry by entry. $\square$

**Lemma (Passing to the row stabilizer).** Let $u\,w = \Lambda$. For all $g$ and $h'$, the class sum at `stdLevel` of the third kernel with datum $\Psi_\Lambda$ equals the class sum at `rowFixingLevel` (the level of the matrices that are $1$ off $W_j$ and fix $w$) of the third kernel with datum $\Psi^\times_{w,\Lambda}$.

Lean: `New.Data.stdClassSum_thirdExchangeKernel_eq_productDatum` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Apply the row stabilizer theorem with the tame character of the lemma on characters. Two hypotheses remain. First, $\psi^{\mathrm{inv}}_\Lambda(Ax) = \psi^{\mathrm{inv}}_\Lambda(x)$ for $A$ in the row stabilizer of $w$: $\mathrm{tr}(\Lambda A x\gamma) = \mathrm{tr}(uwAx\gamma) = \mathrm{tr}(uwx\gamma)$, as $wA = w$. Second, the real group of $V''$ fixes the polynomial. This is `realPairWeil_stackedDetProd`, after the block signs lemma. $\square$

**Theorem (The left side is a theta series).** If $u\,w = \Lambda$, then $\mathrm{LS}_\vartheta(i, g)$ = `kernelClassSum` $(\text{descentPair}\,\vartheta\,j, \nu'', w, \text{leftSideSeries}\,\vartheta\,j\,i)(g)$.

Lean: `New.Data.thirdExchangeLeftSide_eq_kernelClassSum` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Apply the last lemma inside the left side, swap the two finite class sums, and apply the lemma on the product datum. The result is the definition of `kernelClassSum`. $\square$

### Level and holomorphy of $\mathsf{F}_i$

Background in one line. A good form on $W_j$ is a form of principal level at the chosen places in the image of $e_0$ ([single theta lifts](/chapter/single-theta-lifts/)); $u$ = `conjHolomorphicWeight j` is the weight of conjugates of good forms and $u^\circ$ = `kernelWeight j` that of $\theta^\circ$.

**Lemma.** If $\varpi \mid a$, a good form on $W_j$ lies in $\mathrm{rapidOfLevel}(W_j, a)$.

Lean: `New.Data.goodForms_mem_rapidOfLevel` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* A good form has the chosen level, and $K(a) \subseteq$ the chosen level when $\varpi \mid a$. It is a cusp form for a cuspidal type, so it decays rapidly. $\square$

**Lemma (Holomorphic letters).** For every vector $\xi$ of the Weyl module of weight $\mu^+$ = `colsPlus`, the Fock vector of `letterPoly` $\xi$ lies in $\mathrm{holomorphicData}$ for the order `orderW j`, of weight $u - u^\circ$.

Lean: `New.Data.polyVector_letterPoly_mem_holomorphicData` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* The definite group acts on these polynomials by linear substitution, which matches the Weyl representation. So it is enough that the highest vector is holomorphic (`mem_holomorphicData_of_highestVector`). That holds by `letterPoly_highestVector_mem_holomorphicData`, as the parameters fit the descent pair and are injective. Also $u = (u - u^\circ) + u^\circ$ by `conjHolomorphicWeight_eq_add_kernelWeight`. $\square$

**Corollary.** (a) $\mathsf{F}_i = c\,\cdot$ `kernelClassSum` at $\vartheta = 1$ and $w = \Lambda$, for some $c$. (b) $F\,\mathsf{F}_i \in \mathrm{rapidOfLevel}(W_j, \varpi^2)$ for every good form $F$. (c) $\mathsf{F}_i$ is adelic holomorphic for `orderW j` of weight $u - u^\circ$.

Lean: `New.Data.exists_choiceFn_eq_mul_kernelClassSum`, `New.Data.mul_choiceFn_mem_rapidOfLevel`, `New.Data.isAdelicHol_choiceFn` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* (a) Take $c = c_1$ from the theorem of the three exchanges, and $u = 1$, so $1\cdot\Lambda = \Lambda$. (b) By (a), $\mathsf{F}_i$ is a finite sum of kernels with data modulo $\varpi^2$ whose tame parts are trivial off the modulus. The product of such a kernel with a form of level $\varpi^2$ that decays rapidly has level $\varpi^2$ and decays rapidly (`mul_modKernel_mem_rapidOfLevel`). (c) By (a), each kernel is holomorphic by the lemma on holomorphic letters and `isAdelicHol_pairTheta`. $\square$
