---
title: The kernels of a square
lean:
  - New/Determinant/Exchange/OneSquare.lean
decls:
  - New.Exchange.pairWeil_modDatum_single_mul_left
  - New.Exchange.pairWeil_modDatum_single_mul_right
  - New.Exchange.hasLeftInv_transpose_of_areMatched
  - New.Exchange.hasLeftInv_of_areMatched
  - New.Exchange.IsTameFor.exists_inv_rankTwist_inv
  - New.Exchange.integral_integral_sum_eq
  - New.Exchange.exists_integrable_kernel_bound
  - New.Exchange.exists_eq_mul_of_forall_polyVector
  - New.Exchange.modKernel_single_sum_left
  - New.Exchange.modKernel_single_sum_right
  - New.Exchange.upIntegrand
  - New.Exchange.downIntegrand
  - New.Exchange.exists_upIntegrand_bound
  - New.Exchange.integrable_upIntegrand
  - New.Exchange.exists_norm_integral_upIntegrand_sub_le
  - New.Exchange.integrable_downIntegrand
  - New.Exchange.integral_upIntegrand
  - New.Exchange.integral_downIntegrand
  - New.Exchange.integral_sum_upIntegrand_eq_mul
  - New.Exchange.pairTransposedLift_comp_pairLift_mul
  - New.Exchange.pairLift_comp_pairTransposedLift_mul
  - New.Exchange.integral_transposedLift_mul_transposedLift
  - New.Exchange.integral_integral_sum_downIntegrand
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The kernels of a square

This section collects the analytic and algebraic lemmas that Section 5 needs. All of them are in the file [OneSquare.lean](lean:New/Determinant/Exchange/OneSquare.lean#L50). We write $\theta^{S,T}_{a,b}(\varphi)(g, h)$ for the theta kernel `pairTheta S T a b φ` of the pair $(S, T)$, twisted by $a(\det h)\, b(\det g)^{-1}$. We write $\varphi^{S,T}_\Psi(v)$ for the datum `modDatum S T 𝔪 Ψ v`: the Fock vector $v$ at the infinite places, $\Psi$ at the places of $\mathfrak{m}$, the vacuum elsewhere. For a matrix $x$ we write $\delta_x$ for its indicator function, and we call $\varphi_{\delta_x}(v)$ the *point datum* at $x$.

### Background

We use these results. Each is one line here.

1. The lift $\mathcal{L}(a, b, P, \Psi)$ and the transposed lift $\mathcal{L}^{\mathsf{T}}(a, b, P, \Psi)$ are the chosen linear maps `formLift` for the kernel $\theta^{S,T}_{a,b}$ and its swap, with the datum $\varphi_\Psi(v_P)$ of the Fock vector $v_P$ of $P$ ([Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L189)). See [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows).
2. `IsPairEdge a b e e' P` says that all $a_i$ have one weight, all $b_i$ have one weight, and $(e, e', v_P)$ is an edge ([Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L207)). Then each datum $\varphi_\Psi(v_P)$ is an arrow $e \to e'$ and, for the swapped kernel, an arrow $\bar e' \to \bar e$ (`IsPairEdge.isArrow`, [line 261](lean:Lib/Weil/Seesaw.lean#L261); `IsPairEdge.isArrow_swap`, [line 294](lean:Lib/Weil/Seesaw.lean#L294)).
3. For integral points $k$, $k'$ with $x = k'^{-1} y k$ modulo $\mathfrak{m}$, the Weil representation at $(k, k')$ sends $\varphi_{\delta_x}(v)$ to $a(\det k')\, b(\det k)^{-1}\varphi_{\delta_y}(v)$ (`pairWeil_modDatum_single`, [Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L106)).
4. If $\varphi$ is an arrow and $\omega(k, k')\varphi = c\varphi'$, then the translate by $k'$ of the lift by $\varphi$ of $y$ is $c$ times the lift by $\varphi'$ of the translate of $y$ by $k$ (`formRep_formLift_of_eq_smul`, [Lift.lean](lean:Lib/Weil/Lift.lean#L942)).
5. If $\varphi$ is an arrow $e \to e'$ and, for the swapped kernel, an arrow $\varepsilon' \to \varepsilon$, then $\int_{[T]} z \cdot \mathcal{L}_\varphi y = \int_{[S]} y \cdot \mathcal{L}^{\mathsf{T}}_\varphi z$ (`integral_mul_formLift_swap`, [Lift.lean](lean:Lib/Weil/Lift.lean#L950)).
6. The kernel of $(S \oplus V, T)$ for $aa'$, $b$, the product of $\Psi$ and $\Psi'$ on the column blocks and the product $PP'$, at $(g \oplus g', h)$, is the product of the kernels of $(S, T)$ and $(V, T)$. The same holds for row blocks (`New.modKernel_sum_left`, `New.modKernel_sum_right`, [the pair and its kernel](/chapter/theta-lifts-seesaw/#the-pair-and-its-kernel)).
7. Twisting: the kernel for $a\mu$, $b\mu'$ is $\mu(\det h)/\mu'(\det g)$ times the kernel for $a$, $b$ (`New.modKernel_twist`, [KernelLaws.lean](lean:Lib/Weil/DualPair/KernelLaws.lean#L126)).
8. Decay: if $\Psi$ lives on left invertible matrices and $\mathfrak{m}$ has a place, then $\|\theta(\varphi_\Psi(v))(g, h)\|\, \mathrm{ht}_S(g)^M \leq C\, m_N(v)\, \mathrm{ht}_T(h)^B$. If $\Psi$ lives on matrices whose transpose has a left inverse, the roles of $g$ and $h$ change. Here $m_N(v) = \int (1 + \|z\|)^N |v(z)|\, dz$ is the moment `fockMoment` (`New.pairTheta_modDatum_decay`, `New.pairTheta_modDatum_decay_of_rightInv`, [growth and adjointness](/chapter/theta-lifts-seesaw/#growth-convergence-and-adjointness)).
9. The datum is linear in $\Psi$: $\varphi_\Psi(v) = \sum_x \Psi(x)\varphi_{\delta_x}(v)$ (`modDatum_eq_sum`, [KernelDecay.lean](lean:Lib/Weil/DualPair/KernelDecay.lean#L527)). The height of $g \oplus h$ is at most $\mathrm{ht}(g)\,\mathrm{ht}(h)$ ([line 519](lean:Lib/Weil/DualPair/KernelDecay.lean#L519)).
10. For a vector $v$ with all moments finite (a *Schwartz vector*), there are polynomials $P_m$ with $m_N(v - v_{P_m}) \to 0$ for every $N$ (`New.Fock.exists_tendsto_fockMoment`, [the Fock model](/chapter/weil-representation/#the-fock-model-at-a-real-place)).
11. $\nu$ is tame for $(\mathfrak{m}, \mu, \chi)$ if $\mathfrak{m}$ has a place, $\nu$ has weight $\mu$ and a tame part $\psi$ with $\psi_w \neq 1$ exactly for $w \mid \mathfrak{m}$, and $\chi = \prod_{w \mid \mathfrak{m}} \psi_w$. Then $\nu(\det k) = \chi(\det k \bmod \mathfrak{m})$ for integral $k$. The condition is stable under $\nu \mapsto \nu^{-1}$ (with $\chi^{-1}$) and under products with characters of trivial tame part ([TameModulus.lean](lean:Lib/ClassField/HeckeCharacter/TameModulus.lean#L325)).

For $g \in GL_{n'}(O_E/\mathfrak{m})$ let $\operatorname{liftMod}(g)$ be the chosen integral point with residue $g$ ([TameModulus.lean](lean:Lib/ClassField/HeckeCharacter/TameModulus.lean#L253)).

### Point data and characters

**Lemma.** Let $S$, $T$ be spaces, $\alpha$, $\beta$ characters, $g \in GL_{n'}(O_E/\mathfrak{m})$, $x$ a matrix and $v$ a Fock vector. Put $k = \operatorname{liftMod}(g)$. Let $k^{-1}$ act in the finite part of $U(T)$. It sends $\varphi_{\delta_{gx}}(v)$ to $\alpha^{-1}(\det k)\,\varphi_{\delta_x}(v)$. For $g \in GL_n$ and $k = \operatorname{liftMod}(g)$ acting in the finite part of $U(S)$, it sends $\varphi_{\delta_{yg}}(v)$ to $\beta^{-1}(\det k)\,\varphi_{\delta_y}(v)$.

Lean: `New.Exchange.pairWeil_modDatum_single_mul_left`, `New.Exchange.pairWeil_modDatum_single_mul_right` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Apply background item 3 with $(k, k') = (1, k^{-1})$ and the matrices $gx$ and $x$. The condition is $gx = k\, x$ modulo $\mathfrak{m}$, true since $k$ has residue $g$. The character is $\alpha(\det k^{-1}) = \alpha^{-1}(\det k)$. The second case is the same with $(k, 1)$. $\square$

**Lemma.** Let $\Psi$, $\Psi'$ be matched for $\chi$ over the whole ring, with $\sigma$. If $\Psi(x) \neq 0$, then $x^{\mathsf{T}}$ has a left inverse. If $\Psi'(y) \neq 0$, then $y$ has a left inverse.

Lean: `New.Exchange.hasLeftInv_transpose_of_areMatched`, `New.Exchange.hasLeftInv_of_areMatched` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* By the support condition of [matched functions](/chapter/exchange-identity-1/#matched-functions), $x$ is the last row block of $k^{-1}$ for an invertible $k$. The rows of an invertible matrix are independent, so $x^{\mathsf{T}}$ has a left inverse. In the same way $y$ is the first column block of $k$, and the first row block of $k^{-1}$ is a left inverse of it. $\square$

**Lemma.** If $\nu$ is tame for $(\mathfrak{m}, \mu, \chi)$, then for every finite type $N$ there is $\mu'$ such that $\operatorname{rankTwist}(\nu^{-1}, N)^{-1}$ is tame for $(\mathfrak{m}, \mu', \chi)$.

Lean: `New.Exchange.IsTameFor.exists_inv_rankTwist_inv` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* $\nu^{-1}$ is tame with $\chi^{-1}$. The power $\upsilon^{|N|/2}$ has trivial tame part, so $\operatorname{rankTwist}(\nu^{-1}, N)$ is tame with $\chi^{-1}$. Invert again to get $\chi$. $\square$

### Integration lemmas

**Lemma.** Let $F_i$ be functions on $([U_1] \times [U_2]) \times [A]$ and $c_i$ numbers, for $i$ in a finite set. Assume that each $F_i$ with $c_i \neq 0$ is integrable with integral $r_i$. Then $\int_{U_1 \times U_2} \int_A \sum_i c_i F_i = \sum_i c_i r_i$.

Lean: `New.Exchange.integral_integral_sum_eq` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Each $c_i F_i$ is integrable: it is $0$ if $c_i = 0$. So the sum is integrable. Fubini turns the iterated integral into one integral, and the integral of a finite sum is the sum of the integrals. A term with $c_i = 0$ gives $0 = c_i r_i$. $\square$

**Lemma.** Let $\varphi_1$, $\varphi_2$ be rapidly decreasing functions on $[U_1]$, $[U_2]$, and $\nu_0$ a character. Let $K_v(g, h)$ be continuous in $(g, h)$ for each Fock vector $v$, with $\|K_v(g, h)\| \leq C\, m_N(v)\, \mathrm{ht}(g)^B$ whenever $m_N(v)$ is finite. Then there are $N'$ and $C'$ such that, for $m_{N'}(v)$ finite, the function $F((g_1, g_2), h) = \varphi_1(g_1)\varphi_2(g_2)\nu_0(\det g_2) K_v(g_1 \oplus g_2, h)$ is integrable and bounded by $C' m_{N'}(v)$.

Lean: `New.Exchange.exists_integrable_kernel_bound` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Take $N' = N$. Rapid decay gives $D$, $D'$ with $\|\varphi_1\|\,\mathrm{ht}^B \leq D$ and $\|\varphi_2\|\,\mathrm{ht}^B \leq D'$. The character has modulus $1$, and $\mathrm{ht}(g_1 \oplus g_2) \leq \mathrm{ht}(g_1)\,\mathrm{ht}(g_2)$. So $\|F\| \leq |C|\,|D|\,D'\, m_N(v)$. A bounded continuous function on a space of finite measure is integrable. $\square$

**Lemma.** Let $\Lambda_j$ be functions of a Fock vector, for $j \in J$, and $\rho_j$ numbers. Assume that each $\Lambda_j$ is Lipschitz for one moment: $\|\Lambda_j(v) - \Lambda_j(w)\| \leq D\, m_N(w - v)$ when the three moments are finite. Assume that for every polynomial $P$ there is $r$ with $\Lambda_j(v_P) = r\rho_j$ for all $j$. Then for every Schwartz vector $x$ there is $\kappa$ with $\Lambda_j(x) = \kappa\rho_j$ for all $j$.

Lean: `New.Exchange.exists_eq_mul_of_forall_polyVector` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Take $P_m$ from background item 10. For each $j$ the Lipschitz bound gives $\Lambda_j(v_{P_m}) \to \Lambda_j(x)$. So the functions $j \mapsto \Lambda_j(v_{P_m})$ tend to $j \mapsto \Lambda_j(x)$ pointwise. Each lies in the line $\mathbb{C}\rho$. A finite dimensional subspace is closed, so the limit lies in it. $\square$

The index set $J$ may be infinite. Only the line $\mathbb{C}\rho$ must be finite dimensional.

### The kernels multiply

Fix spaces $A'$, $A$, $U_1$, $U_2$ and a character $\nu_0$.

**Lemma.** Let $b_2\nu_0 = b_1$. For a matrix $x$ with column blocks $x_1$, $x_2$ and polynomials $P_1$, $P_2$, read in the variables of the two column blocks,
$$\nu_0(\det g_2)\,\theta^{U_1 \oplus U_2, A}_{a_1a_2, b_1}[\delta_x, P_1P_2](g_1 \oplus g_2, h) = \theta^{U_1, A}_{a_1, b_1}[\delta_{x_1}, P_1](g_1, h)\,\theta^{U_2, A}_{a_2, b_2}[\delta_{x_2}, P_2](g_2, h).$$
If $b_1\nu_0 = b_2$, then for $y$ with row blocks $y_1$, $y_2$,
$$\nu_0(\det g_2)\,\theta^{A', U_1 \oplus U_2}_{b_1, a_1a_2}[\delta_y, P_1P_2](h, g_1 \oplus g_2) = \theta^{A', U_1}_{b_1, a_1}[\delta_{y_1}, P_1](h, g_1)\,\theta^{A', U_2}_{b_2, a_2}[\delta_{y_2}, P_2](h, g_2).$$

Lean: `New.Exchange.modKernel_single_sum_left`, `New.Exchange.modKernel_single_sum_right` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* $\delta_x(z) = \delta_{x_1}(z_1)\delta_{x_2}(z_2)$. Background item 6 splits the left kernel into the product of the kernels for $(U_1, A)$ with $a_1, b_1$ and $(U_2, A)$ with $a_2, b_1$. By item 7 with $\mu = 1$, $\mu' = \nu_0$, the kernel for $a_2, b_2\nu_0$ is $\nu_0(\det g_2)^{-1}$ times the kernel for $a_2, b_2$. The second claim is the same: in $(A', U_2)$ the group of $U_2$ is on the right, so item 7 with $\mu = \nu_0$ gives $\theta_{b_1\nu_0, a_2} = \nu_0(\det g_2)\,\theta_{b_1, a_2}$. $\square$

**Definition.** For functions $f_1$, $f_2$, a matrix $x$ modulo $\mathfrak{m}$, characters $\gamma$, $b$ and a Fock vector $w$, put
$$\mathrm{up}(x, w)((g_1, g_2), h) = f_1(g_1) f_2(g_2)\,\nu_0(\det g_2)\,\theta^{U_1 \oplus U_2, A}_{\gamma, b}(\varphi_{\delta_x}(w))(g_1 \oplus g_2, h),$$
$$\mathrm{down}(y, w)((g_1, g_2), h) = f_1(g_1) f_2(g_2)\,\nu_0(\det g_2)\,\theta^{A', U_1 \oplus U_2}_{b, \gamma}(\varphi_{\delta_y}(w))(h, g_1 \oplus g_2).$$

Lean: `New.Exchange.upIntegrand`, `New.Exchange.downIntegrand` (New/Determinant/Exchange/OneSquare.lean).

The theta kernel is linear in the datum, so $\mathrm{up}(x, v + w) = \mathrm{up}(x, v) + \mathrm{up}(x, w)$ and the same for differences (`upIntegrand_add`, `upIntegrand_sub`).

**Lemma.** Let $\mathfrak{m}$ have a place, $f_1$, $f_2$ be of rapid decay, and $x^{\mathsf{T}}$ have a left inverse. There are $N$ and $D$ such that, for $m_N(w)$ finite, $\mathrm{up}(x, w)$ is integrable and bounded by $D\, m_N(w)$. So $\mathrm{up}(x, w)$ is integrable for every Schwartz vector $w$. There are $N$ and $D$ such that $\|\int \mathrm{up}(x, v) - \int \mathrm{up}(x, v')\| \leq D\, m_N(v' - v)$ whenever the three moments are finite. If $y$ has a left inverse, then $\mathrm{down}(y, w)$ is integrable for every Schwartz vector $w$.

Lean: `New.Exchange.exists_upIntegrand_bound`, `New.Exchange.integrable_upIntegrand`, `New.Exchange.exists_norm_integral_upIntegrand_sub_le`, `New.Exchange.integrable_downIntegrand` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* $\delta_x$ lives on $\{x\}$, and $x^{\mathsf{T}}$ has a left inverse. Background item 8 with $M = 0$ bounds the kernel by $C\, m_N(w)\,\mathrm{ht}(g_1 \oplus g_2)^B$. The previous integrability lemma gives the first claim. The second follows since all moments of $w$ are finite. For the third, the difference of the integrals is the integral of $\mathrm{up}(x, v' - v)$, by linearity. Its norm is at most $D\, m_N(v' - v)$ times the finite total measure. For the last claim, use the first decay bound of item 8 for $\delta_y$, with the roles of the spaces exchanged. $\square$

**Lemma.** Let $b_2\nu_0 = b_1$. Take the point datum at $x$ with the vector $v_{P_1P_2}$ and the characters $a_1a_2$, $b_1$. If $\mathrm{up}(x, v_{P_1P_2})$ is integrable, then
$$\int \mathrm{up}(x, v_{P_1P_2}) = \int_{[A]} \mathrm{lift}_{U_1 \to A}(a_1, b_1, P_1, \delta_{x_1}) f_1 \cdot \mathrm{lift}_{U_2 \to A}(a_2, b_2, P_2, \delta_{x_2}) f_2.$$
If $b_1\nu_0 = b_2$ and $\mathrm{down}(y, v_{P_1P_2})$ is integrable, its integral is the integral over $[A']$ of the product of the transposed lifts of $f_1$ and $f_2$ for $(A', U_1)$ with $b_1, a_1, \delta_{y_1}$ and $(A', U_2)$ with $b_2, a_2, \delta_{y_2}$.

Lean: `New.Exchange.integral_upIntegrand`, `New.Exchange.integral_downIntegrand` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Fubini puts the integral over $A$ outside. For fixed $h$, the inner integrand is $f_1(g_1)f_2(g_2)$ times the product of two kernels, by the kernel product lemma. So it is a product of a function of $g_1$ and a function of $g_2$. The integral of such a product over $[U_1] \times [U_2]$ is the product of the integrals, and these are the two lifts at $h$. The second claim is the same. $\square$

Here `lift` is the integral itself, not the chosen map `formLift`.

**Lemma.** Fix $g = (g_1, g_2)$. Assume that the theta integral over $[A]$ of $\theta^{U_1 \oplus U_2, A}_{a, b_0}(\varphi_\Psi(w))$ at $g_1 \oplus g_2$ is $c$ times $\int_{[A']} \theta^{A', U_1 \oplus U_2}_{b_0', a}(\varphi_{\Psi'}(v))(k, g_1 \oplus g_2)\, dk$. Then
$$\int_{[A]} \sum_x \Psi(x)\,\mathrm{up}(x, w)(g, k)\, dk = c \int_{[A']} \sum_y \Psi'(y)\,\mathrm{down}(y, v)(g, k)\, dk.$$

Lean: `New.Exchange.integral_sum_upIntegrand_eq_mul` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* By item 9 both data are sums of point data. The factor $f_1(g_1)f_2(g_2)\nu_0(\det g_2)$ does not depend on $k$, so it leaves both integrals. What remains is the hypothesis. $\square$

### Equivariance along a path

**Lemma.** Let $(U_1, A)$ be an edge $e_1 \to e$ for $(a_1, b_1, P_1)$ and $(U_2, A)$ an edge $\bar e_2 \to \bar e$ for $(a_2, b_2, P_2)$. Let $(a_1(i)a_2(i))^{-1}$ be tame for $(\mathfrak{m}, \mu, \chi)$. For $g \in GL_{n'}(O_E/\mathfrak{m})$,
$$\mathcal{L}^{\mathsf{T}}(\delta_{(gx)_2}) \circ \mathcal{L}(\delta_{(gx)_1}) = \chi(\det g)\,\mathcal{L}^{\mathsf{T}}(\delta_{x_2}) \circ \mathcal{L}(\delta_{x_1}).$$
Dually, let $(A', U_1)$ be an edge $\bar e' \to \bar e_1$ for $(b_1', a_1', P_1')$ and $(A', U_2)$ an edge $e' \to e_2$ for $(b_2', a_2', P_2')$, with $(a_1'(i)a_2'(i))^{-1}$ tame for $(\mathfrak{m}, \mu, \chi)$. Then for $g \in GL_n(O_E/\mathfrak{m})$ the map $\mathcal{L}(\delta_{(yg)_2}) \circ \mathcal{L}^{\mathsf{T}}(\delta_{(yg)_1})$ is $\chi(\det g)$ times the map for $y$.

Lean: `New.Exchange.pairTransposedLift_comp_pairLift_mul`, `New.Exchange.pairLift_comp_pairTransposedLift_mul` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* Fix a form $f$, put $k = \operatorname{liftMod}(g)$ and let $F$ be the lift of $f$ with $\delta_{gx_1}$. The column blocks of $gx$ are $gx_1$ and $gx_2$. By the point data lemma and item 4, the translate of $F$ by $k^{-1}$ is $a_1^{-1}(\det k)$ times the lift of $f$ with $\delta_{x_1}$. The transposed lift with $\delta_{gx_2}$ is an arrow for the swapped kernel. The point data lemma and item 4, with $k^{-1}$ in the group of $A$, give: the transposed lift of $F$ with $\delta_{gx_2}$ is $a_2^{-1}(\det k)$ times the transposed lift, with $\delta_{x_2}$, of the translate of $F$. Combine the two. The factor is $a_2^{-1}(\det k)\,a_1^{-1}(\det k)$, which is $\chi(\det g)$ by item 11. The second claim is the same, with $k$ in the group of $A'$ and the right action. $\square$

**Lemma.** In the dual setting, for $\Psi_1$, $\Psi_2$ and forms $f_1$ of type $e_1$ and $f_2$ of type $\bar e_2$,
$$\int_{[A']} \mathrm{lift}^{\mathsf{T}}(\Psi_1) f_1 \cdot \mathrm{lift}^{\mathsf{T}}(\Psi_2) f_2 = \int_{[U_2]} f_2 \cdot \mathcal{L}(\Psi_2)\big(\mathcal{L}^{\mathsf{T}}(\Psi_1) f_1\big).$$
Let $b_1'(i)\nu_0 = b_2'(i)$, let $\mathfrak{m}$ have a place, let $\Psi'$ vanish off the left invertible matrices, and let $f_1$, $f_2$ be rapidly decreasing. Then
$$\int_{U_1 \times U_2}\int_{A'} \sum_y \Psi'(y)\,\mathrm{down}(y, v_{P_1'P_2'}) = \sum_y \Psi'(y) \int_{[U_2]} f_2 \cdot \mathcal{L}(\delta_{y_2})\big(\mathcal{L}^{\mathsf{T}}(\delta_{y_1}) f_1\big).$$

Lean: `New.Exchange.integral_transposedLift_mul_transposedLift`, `New.Exchange.integral_integral_sum_downIntegrand` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* For the first claim, the datum for $(A', U_2)$ is an arrow $e' \to e_2$ and, swapped, an arrow $\bar e_2 \to \bar e'$. Item 5 moves the transposed lift of $f_2$ to a lift on the other side. The integrals `lift` equal the chosen maps on these arrows. For the second claim, $v_{P_1'P_2'}$ is a Schwartz vector, and each $\mathrm{down}(y, v)$ with $\Psi'(y) \neq 0$ is integrable by the integrability lemma. The integration lemma for sums, then the down integral lemma, then the first claim give the result. $\square$
