---
title: Archimedean bounds for jets
lean:
  - New/UpperBound/Kernels/JetConjugatesAndBounds.lean
decls:
  - New.HasConjugateGrowth
  - New.integral_exp_neg_inv_mul_normalizedVolume
  - New.norm_integral_normalizedVolume_le
  - New.norm_realVac
  - New.Parameters.jet_jetSeries_mul
  - New.Parameters.map_jet_eq_integral
  - New.Parameters.norm_jet_translate_le
  - New.Parameters.IsVacuumCombination
  - New.Parameters.isVacuumCombination_of_isAdmissibleCombination
  - New.Parameters.isVacuumCombination_finHeisenbergOp
  - New.Parameters.jetSizeBound
  - New.Parameters.jetSizeBound_eq
  - New.Parameters.norm_map_pairChar
  - New.Parameters.norm_jet_le_of_isVacuumCombination
  - New.sqrt_prod_pow_le_exp
  - New.schurGrowthExponent
  - New.FitsRanks.sum_diagramWeight_eq_boxes
  - New.Parameters.hasConjugateGrowth_schurCoeffPoly
  - New.Parameters.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Archimedean bounds for jets

A jet is a derivative at one point. Derivatives of holomorphic functions are bounded by Cauchy's estimate in terms of values on a circle. In the Fock model the right form of Cauchy's estimate is an integral: a jet is the integral of the function against a conjugated polynomial and a Gaussian. This section uses that formula for the datum $LF$ of Section 2, whose values Section 3 bounds. The result is a bound for $|\sigma(\text{jet})|$, for all automorphisms $\sigma$ of $\mathbb{C}$, first along one polynomial and then for the whole Schur jet matrix in the Gram norm.

### Model case (jets)

Let $G$ be an entire function of one variable with $|G(y)| \le M e^{|y|^2/2}$. Write $dA$ for Lebesgue measure on $\mathbb{C}$. The monomials are orthogonal for the Gaussian weight: $\int_{\mathbb{C}} \bar y^k y^m e^{-|y|^2}\,dA/\pi = k!\,\delta_{km}$. So, expanding $G = \sum_m a_m y^m$,
$$G^{(k)}(0) = k!\,a_k = \int_{\mathbb{C}} \bar y^{\,k}\,G(y)\,e^{-|y|^2}\,\frac{dA}{\pi}.$$
This is the reproducing formula of the Bargmann-Fock space. It gives
$$|G^{(k)}(0)| \le M\int_{\mathbb{C}} |y|^k e^{-|y|^2/2}\,\frac{dA}{\pi} = M\,2^{k/2+1}\,\Gamma\bigl(\tfrac k2 + 1\bigr).$$
The growth is about $\sqrt{k!}\,2^{k/2}$, not $k!$. This $\sqrt{k!}$ is the source of the $\tfrac12\log l!$ terms in the exponent $\mathrm{schurGrowthExponent}$ below.

The general case has two more features. The polynomial $\bar y^k$ is replaced by any polynomial $Q$, and the bound must hold for $\sigma(Q(\cdot))$ with $\sigma$ not continuous. One condition on $Q$ handles both. The Gaussian $e^{-|y|^2/2}$ is split as $e^{-L|y|^2/(2L+2)}e^{-|y|^2/(2L+2)}$: the first factor absorbs the growth of $Q$, and the second is integrated.

### Gaussian integrals

Let $\iota$ be a finite set, and let $\nu_\iota$ be Lebesgue measure on $\mathbb{C}^\iota$ divided by $\pi^{|\iota|}$. Recall from [the Weil representation](/chapter/weil-representation/) the real vacuum $\mathrm{realVac}(y) = \exp(-\bar y\cdot y/2)$ on $\mathbb{C}^\iota$.

**Lemma (Gaussian integral).** For $a > 0$,
$$\int_{\mathbb{C}^\iota} \exp\Bigl(-a^{-1}\sum_i |y_i|^2\Bigr)\,d\nu_\iota(y) = a^{|\iota|}.$$

Lean: `New.integral_exp_neg_inv_mul_normalizedVolume` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The integral of $e^{-|y|^2/a}$ over $\mathbb{C} = \mathbb{R}^2$ is $\pi a$. Take the product over $\iota$ and divide by $\pi^{|\iota|}$. $\square$

**Corollary (Bounded integrands).** Let $a > 0$, and let $f$ be a function on $\mathbb{C}^\iota$ with $|f(y)| \le C\exp(-a^{-1}\sum_i|y_i|^2)$ for all $y$. Then $\bigl|\int f\,d\nu_\iota\bigr| \le C a^{|\iota|}$.

Lean: `New.norm_integral_normalizedVolume_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The Gaussian is integrable, since its integral is not $0$. So the bound is the integral of the bound. $\square$

**Remark (Formalization).** In the source a non-integrable function has integral $0$. So the corollary needs no integrability hypothesis: the hypothesis forces $C \ge 0$.

**Lemma (The real vacuum).** $|\mathrm{realVac}(y)| = \exp(-\sum_i |y_i|^2/2)$.

Lean: `New.norm_realVac` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* $\bar y \cdot y = \sum_i |y_i|^2$ is real, and $|e^z| = e^{\mathrm{Re}\,z}$. $\square$

### Jets as integrals

In this section $V$ is the space $\mathrm{Hom}(V_n, V_{n'})$ of the standard spaces, with all signs $+1$ and index set $n' \times n$. Its variables are $X_{\tau, j, i}$. Recall that $\partial_Q G$ is $Q(\partial)G$ at $0$, for a polynomial $Q$ and a power series $G$, as in [Weyl modules](/chapter/weyl-modules/).

**Lemma (Moving the scale).** For $c, a \in \mathbb{C}$, a polynomial $Q$ and a datum $F$,
$$\partial_Q\bigl(J_{ca}F\bigr) = \partial_{Q(cX)}\bigl(J_a F\bigr).$$

Lean: `New.Parameters.jet_jetSeries_mul` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* By [the integral vacuum and tight frames](/chapter/integral-vacuum/), $\partial_Q(J_s F)$ is $\theta$ of $F$ paired with the polynomial $Q(sX)$, that is, with $X_i$ replaced by $sX_i$. The polynomials $Q((ca)X)$ and $(Q(cX))(aX)$ are equal: check it on monomials. $\square$

Recall from [the Weil representation](/chapter/weil-representation/) the map $\mathrm{realVec}$: it takes $y \in \mathbb{C}^{\Phi \times n'\times n}$ to the adelic vector with finite part $0$ whose coordinate at $\tau$ is $y_\tau$ scaled by $(2\pi\,\mathrm{Im}\,\tau(j))^{-1/2}$. The theta functional of an integrated datum is $\int v(y)\,F(\mathrm{realVec}\,y)\,d\nu(y)$.

**Lemma (Conjugate jets as integrals).** Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, and let $F, F'$ be data with $\mathrm{IsJetConjugate}(\sigma, \pi_\sigma, t_0, t, F, F')$. Then for every polynomial $Q$,
$$\sigma\bigl(\partial_Q J_{t_0}F\bigr) = \int Q^\sigma_\pi\bigl(t\bar y\bigr)\,\mathrm{realVac}(y)\,F'(\mathrm{realVec}\,y)\,d\nu(y),$$
where $Q^\sigma_\pi$ is $Q$ with $\sigma$ applied to the coefficients and the variable $X_{\tau, j, i}$ renamed to $X_{\pi_\sigma\tau, j, i}$.

Lean: `New.Parameters.map_jet_eq_integral` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* A ring map commutes with jets: $\sigma(\partial_Q G) = \partial_{Q^\sigma}(\sigma G)$. By hypothesis $\sigma(J_{t_0}F) = \mathrm{rename}_{\pi_\sigma^{-1}}(J_tF')$. Renaming the variables of the series and of the polynomial together does not change the jet, so
$$\sigma\bigl(\partial_Q J_{t_0}F\bigr) = \partial_{Q^\sigma_\pi}\bigl(J_tF'\bigr).$$
By [the integral vacuum and tight frames](/chapter/integral-vacuum/), $\partial_P(J_tF')$ is the theta functional of $F'$ integrated against the Fock vector of $P(tX)$, and in the Fock model the Fock vector of a polynomial $P$ is $y \mapsto P(\bar y)\,\mathrm{realVac}(y)$. The formula for $\theta$ of an integrated datum gives the integral. $\square$

### Conjugate growth

**Definition (Conjugate growth).** Let $\sigma : \mathbb{C} \to \mathbb{C}$ be a map, $Q$ a polynomial in variables indexed by a finite set $\iota$, $T$ real, $L \in \mathbb{N}$, and $w, A$ real. Then $Q$ has *conjugate growth* $(T, L, w, A)$ under $\sigma$ if for all $z \in \mathbb{C}^\iota$ and all real $R$,
$$\sum_i |\sigma(z_i)|^2 \le T\,(2L + 2)\,R \implies |\sigma(Q(z))| \le A\exp(w + LR).$$

Lean: `New.HasConjugateGrowth` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

For an automorphism $\sigma$ and $Q$ homogeneous of degree $L$, put $\sigma(z) = \sqrt T y$. The condition then says that $T^{L/2}|Q^\sigma(y)|\exp(-L|y|^2/(2L+2)) \le A e^w$ for all $y$. 

**Example.** Let $\iota$ be one point, $Q = X^L$ with $L \ge 1$, and $T = 1$. If $|\sigma z|^2 \le (2L+2)R$, then $|\sigma(z^L)| = |\sigma z|^L \le ((2L+2)R)^{L/2}$. Put $x = (2L+2)R$. For $x > 0$ the function $\log x - x/(L+1)$ has its maximum $\log(L+1) - 1$ at $x = L + 1$. So $\tfrac L2\log x \le LR + \tfrac L2\log\frac{L+1}{e}$. For $R \le 0$ the hypothesis forces $z = 0$, and $\sigma(z^L) = 0$. So $X^L$ has conjugate growth $(1, L, \tfrac L2\log\frac{L+1}{e}, 1)$ under every automorphism. The term $\tfrac L2 \log L$ is the $\tfrac12\log L!$ of the model case, up to $O(L)$.

### One translate

**Theorem (Cauchy's estimate for one translate).** Let $V = \mathrm{Hom}(V_n, V_{n'})$ be as above, $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, $c \in \mathbb{C}$, $Q$ a polynomial, $L \in \mathbb{N}$, and $w, A, T$ real with $A \ge 0$, $|\sigma(c)|^2/\Omega_E \le T$, and $Q$ of conjugate growth $(T, L, w, A)$ under $\sigma$. Then for every finite adelic vector $x$ and every finite unitary $g$ of $V$,
$$\Bigl|\sigma\bigl(\partial_Q J_{c t_0}\,\varrho(\mathrm{fin}(x))\,\omega(1,g)\,\theta^\circ\bigr)\Bigr| \le \exp\bigl(C_P\,(q_1 |n'||n| + 1)^2 + w\bigr)\,(2L+2)^{f|n'||n|}\,A.$$

Lean: `New.Parameters.norm_jet_translate_le` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Let $F$ be the datum $\varrho(\mathrm{fin}(x))\,\omega(1,g)\,\theta^\circ$. It lies in $V^{\mathrm{fin}}$. Write $M = C_P(q_1|n'||n|+1)^2$ and $N(y) = \sum_i |y_i|^2$. Take a jet conjugation $L_\sigma$ for $(\sigma, t, b)$ on $V$ by the existence theorem of Section 2. By the lemma on moving the scale and the lemma on conjugate jets, applied with $F' = L_\sigma F$,
$$\sigma\bigl(\partial_Q J_{ct_0}F\bigr) = \int Q'(t\bar y)\,\mathrm{realVac}(y)\,(L_\sigma F)(\mathrm{realVec}\,y)\,d\nu(y),$$
with $Q' = (Q(cX))^\sigma_\pi$. Fix $y$ and put $z = c\,\sigma^{-1}(t\bar y\circ e)$, where $e$ is the permutation $(\tau, j, i)\mapsto(\pi_\sigma\tau, j, i)$ and $\sigma^{-1}$ acts on each coordinate. Then $Q'(t\bar y) = \sigma(Q(z))$, as one checks on monomials, and
$$\sum_i |\sigma(z_i)|^2 = |\sigma(c)|^2\,|t|^2\,N(y) = \frac{|\sigma c|^2}{\Omega_E}\,N(y) \le T\,N(y) = T(2L+2)\frac{N(y)}{2L+2},$$
because $|t|^2 = \Omega_E^{-1}$ and $e$ is a permutation. Conjugate growth with $R = N(y)/(2L+2)$ gives $|\sigma(Q(z))| \le A\exp(w + LN(y)/(2L+2))$. The real vacuum has modulus $e^{-N(y)/2}$, and $|(L_\sigma F)(\mathrm{realVec}\,y)| \le e^M$ by the theorem on values of the conjugated vacuum, applied to the space $V$ of rank $|n'||n|$. So the integrand is at most
$$A\,e^{M+w}\exp\Bigl(\frac{LN}{2L+2} - \frac N2\Bigr) = A\,e^{M+w}\exp\Bigl(-\frac{N}{2L+2}\Bigr).$$
The corollary on bounded integrands with $a = 2L+2$ and $|\iota| = f|n'||n|$ gives the claim. $\square$

The jets are taken at $ct_0$, and only $|\sigma(c)|^2/\Omega_E$ enters, as the variance of the Gaussian seen by $Q$.

### Vacuum combinations

The data of the argument are not single translates. They are finite combinations whose coefficients have controlled conjugates.

**Definition (Vacuum combination).** Let $V$ be a space over $E$ and $B$ real. A datum $f$ is a *vacuum combination of size $B$* if there is a finitely supported function $r$ on finite adelic vectors with
$$f = \sum_{x} r(x)\,\varrho^\pm(x)\,\theta^\circ \qquad\text{and}\qquad \sum_x |\tau(r(x))| \le B \text{ for every ring automorphism } \tau \text{ of } \mathbb{C}.$$
Here $\varrho^\pm(x)$ is the normalized finite Heisenberg operator $\mathrm{finHeisenbergOp}(x)$: $\varrho(\mathrm{fin}(x))$ times the root of unity $\mathrm{semichar}(x)$.

Lean: `New.Parameters.IsVacuumCombination` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

**Lemma (Admissible combinations).** An admissible combination of the translates $\varrho^\pm(x)\theta^\circ$, in the sense of [the seesaw identity, part 1](/chapter/seesaw-identity-1/), with support in a set $A$, denominator $d$ away from $q$, the size condition switched on and size $B$, is a vacuum combination of size $B$. A single translate $\varrho^\pm(x)\,\theta^\circ$ is a vacuum combination of size $1$.

Lean: `New.Parameters.isVacuumCombination_of_isAdmissibleCombination`, `New.Parameters.isVacuumCombination_finHeisenbergOp` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* For the first claim keep the coefficients and the expansion and forget the support and integrality conditions. For the second take $r$ the function that is $1$ at $x$ and $0$ elsewhere. $\square$

**Definition (The jet size factor).** For $B$ real, $L\in\mathbb{N}$ and $w$ real,
$$\mathrm{jetSizeBound}(n, n', B, L, w) = B\exp\Bigl(C_P\,(q_1|n'||n|+1)^2 + f|n'||n|\log(2L+2) + w\Bigr).$$

Lean: `New.Parameters.jetSizeBound` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

**Lemma (Closed form).** $\mathrm{jetSizeBound}(n, n', B, L, w) = B\,\exp\bigl(C_P(q_1|n'||n|+1)^2 + w\bigr)\,(2L+2)^{f|n'||n|}$.

Lean: `New.Parameters.jetSizeBound_eq` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* $\exp(k\log(2L+2)) = (2L+2)^k$, since $2L + 2 > 0$. $\square$

The data are moved by the Weil representation $\omega_{a,b}$ of the dual pair of [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), twisted by two automorphic characters $a$ and $b$ of the norm one ideles. At finite points $g$ of $\mathrm{U}(V_n)$ and $h$ of $\mathrm{U}(V_{n'})$ it acts by the value $\chi_{a,b}(g,h) = a(\det h)\,b(\det g)^{-1}$ of the pair character times $\omega(1, k)$, where $k$ is the finite unitary operator $z \mapsto h z g^{-1}$ on $V$.

**Lemma (The pair character has modulus one).** Let $a$ and $b$ be automorphic characters with weights $e_a$, $e_b$ and tame parts. Then for $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and finite unitary points $g$ and $h$, $|\sigma(\chi_{a,b}(g, h))| = 1$.

Lean: `New.Parameters.norm_map_pairChar` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The determinants are norm one ideles with archimedean part $1$. For a character with a weight, $|\tau(\mu(u))| = 1$ at such $u$ for every ring map $\tau$, as in the proof for the multiplier ratio. $\square$

**Theorem (Size of jets).** Let $f$ be a vacuum combination of size $B$ on $V = \mathrm{Hom}(V_n, V_{n'})$. Let $a$, $b$ be automorphic characters with weights, $g$ and $h$ finite unitary points of ranks $n$ and $n'$, and $\sigma$ any ring automorphism of $\mathbb{C}$. Let $c$, $Q$, $L$, $w$, $A$, $T$ be as in Cauchy's estimate for one translate, now for this $\sigma$: $A \ge 0$, $|\sigma(c)|^2/\Omega_E \le T$, and $Q$ of conjugate growth $(T, L, w, A)$ under $\sigma$. Then
$$\Bigl|\sigma\bigl(\partial_Q\,J_{ct_0}\,\omega_{a,b}((1,g),(1,h))\,f\bigr)\Bigr| \le \mathrm{jetSizeBound}(n, n', B, L, w)\cdot A.$$

Lean: `New.Parameters.norm_jet_le_of_isVacuumCombination` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* *Reduction to $\sigma$ over $K$.* By [the integral vacuum and tight frames](/chapter/integral-vacuum/), there is $\sigma' \in \mathrm{Gal}(\mathbb{C}/K)$ with $|\sigma(z)| = |\sigma'(z)|$ for all $z \in \mathbb{C}$. Then $|\sigma'(c)|^2/\Omega_E \le T$, and $Q$ has conjugate growth $(T, L, w, A)$ under $\sigma'$, since the condition sees $\sigma$ only through absolute values.

*One term.* Let $x$ be a finite adelic vector. The Weil operator of $(g, h)$ maps $\varrho^\pm(x)\,\theta^\circ$ to $\chi_{a,b}(g,h)\,\varrho^\pm(kx)\,\omega(1,k)\,\theta^\circ$, by the law $\omega(k)\varrho^\pm(x) = \varrho^\pm(kx)\omega(k)$. The operator $\varrho^\pm(kx)$ is $\zeta\,\varrho(\mathrm{fin}(kx))$ for a root of unity $\zeta$. So the jet of this term is $\chi_{a,b}(g,h)\,\zeta$ times a jet of $\varrho(\mathrm{fin}(kx))\,\omega(1,k)\,\theta^\circ$. Its $\sigma$-image has the absolute value of its $\sigma'$-image. The number $\sigma'(\chi_{a,b}(g,h)\zeta)$ has modulus one, by the lemma on the pair character and since $\sigma'(\zeta)$ is a root of unity. Cauchy's estimate for one translate, for $\sigma'$, bounds the rest by $C\,A$, with $C = \exp(C_P(q_1|n'||n|+1)^2 + w)(2L+2)^{f|n'||n|}$.

*The sum.* The jet is $\sigma$-semilinear in the datum. So the $\sigma$-image of the jet of $\omega_{a,b}(g, h) f$ is $\sum_x \sigma(r(x))\,\sigma(\text{jet of the term at } x)$, and its modulus is at most $\sum_x |\sigma(r(x))|\,CA \le B\,C\,A$. By the closed form, $BC = \mathrm{jetSizeBound}(n, n', B, L, w)$. $\square$

**Remark (Formalization).** The theorem holds for every ring automorphism of $\mathbb{C}$, and the hypothesis on $r$ is for every ring automorphism too. The reduction to $\mathrm{Gal}(\mathbb{C}/K)$ is by absolute values only. It does not say that $\sigma(\text{jet}) = \sigma'(\text{jet})$, which is false in general. It says only that the two have the same modulus. The size $B$ of a vacuum combination is a real number. If $B < 0$, no $r$ exists, since a sum of absolute values is at least $0$, and the theorem is vacuous.

### Schur jets

Recall from [Weyl modules](/chapter/weyl-modules/) the Schur matrix $S_\kappa(z)$ of a weight $\kappa$, for a family $z = (z_\tau)$ of $n'\times n$ matrices, with rows indexed by the Weyl basis of rank $n'$ and columns by the Weyl basis of rank $n$, and the Gram norm $\|\xi\|_\kappa = \sqrt{\mathrm{weylNormSq}(\xi)}$. The *Schur jet matrix* $\mathrm{schurJet}_\kappa(G)$ of a power series $G$ has the entry $\partial_{S_\kappa(X)_{i'i}}G$ at $(i', i)$. For a covector $y$ and a vector $\xi$, $Q_{y,\xi} = y^T S_\kappa(X)\,\xi$ is the *Schur coefficient polynomial*. Then $y\cdot\mathrm{schurJet}_\kappa(G)\,\xi = \partial_{Q_{y,\xi}}G$, and $Q_{y,\xi}(z) = y^TS_\kappa(z)\xi$ for a lift weight. A weight $\kappa$ is a *lift weight* from $n$ to $n'$ with exponents $e_b$, $e$ if $\kappa$ fits the ranks, $|n| < |n'|$ and $e(\tau) = e_b(\tau) + \kappa(\tau, |n|)$, as in [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/).

The bound for $S_\kappa$ is the norm bound of [Weyl modules](/chapter/weyl-modules/), [`New.weylNormSq_schur_le`](/decl/New.weylNormSq_schur_le/). In one line: if $\kappa$ fits the ranks, there are $\rho_\tau(i) \ge 0$ for $i < |n|$ with $\sum_i \rho_\tau(i) \le \sum_{j, i}|z_{\tau, j, i}|^2$ for each $\tau$ and $\|S_\kappa(z)\eta\|_\kappa^2 \le \prod_{\tau, i}\rho_\tau(i)^{l(\tau, i)}\,\|\eta\|_\kappa^2$ for all $\eta$, where $l(\tau, i)$ is the length of row $i$ at $\tau$ of the diagram of the columns of height below $|n'|$, the diagram weight.

**Lemma (Row lengths and boxes).** If $\kappa$ fits the ranks $|n|$ and $|n'|$, then
$$\sum_{\tau \in \Phi}\sum_{i < |n|} l(\tau, i) = \mathrm{boxes}(\kappa, |n'|).$$

Lean: `New.FitsRanks.sum_diagramWeight_eq_boxes` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Fix $\tau$. The length $l(\tau, i)$ is $\sum_{i < k < |n'|}\kappa(\tau, k)$. Exchange the sums: a column of height $k < |n'|$ is counted once for each $i < |n|$ with $i < k$. If $k \le |n|$ there are $k$ such $i$. If $|n| < k < |n'|$, then $\kappa(\tau, k) = 0$ because $\kappa$ fits the ranks. So the sum is $\sum_{k<|n'|}k\,\kappa(\tau, k)$. Sum over $\tau$. $\square$

**Lemma (A monomial bound).** Let $\Phi$ be finite, $I$ a finite set of natural numbers, $\rho_\tau(i) \ge 0$, $l(\tau, i) \in \mathbb{N}$, and $L > 0$, $u$, $R$ real with $\sum_{\tau, i}\rho_\tau(i) \le e^u(2L+2)R$. Then
$$\sqrt{\prod_{\tau, i}\rho_\tau(i)^{l(\tau, i)}} \le \exp\Bigl(\frac12\sum_{\tau, i}\Bigl(\frac{l(\tau,i)}{L} + \log l(\tau,i)! + l(\tau,i)\,u\Bigr) + LR\Bigr).$$

Lean: `New.sqrt_prod_pow_le_exp` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* For $x \ge 0$, $l\in\mathbb{N}$ and real $v$, $x^l \le \exp(\log l! + lv + xe^{-v})$: this is $t^l/l! \le e^t$ at $t = xe^{-v}$. Take $v = u + 1/L$ and multiply over $(\tau, i)$:
$$\prod\rho^{l} \le \exp\Bigl(\sum\bigl(\log l! + l u + l/L\bigr) + S e^{-u-1/L}\Bigr), \qquad S = \sum\rho.$$
Since $e^{1/L} \ge 1 + 1/L = (L+1)/L$,
$$S e^{-u-1/L} \le \frac{e^u(2L+2)R}{e^u(L+1)/L} = 2LR.$$
Take square roots. $\square$

**Definition (Schur growth exponent).** For index sets $n$, $n'$, a weight $\kappa$, $L \in \mathbb{N}$ and real $u$,
$$\mathrm{schurGrowthExponent}(n, n', \kappa, L, u) = \frac12\sum_{\tau\in\Phi}\sum_{i<|n|}\Bigl(\frac{l(\tau, i)}{L} + \log l(\tau, i)! + l(\tau, i)\,u\Bigr).$$

Lean: `New.schurGrowthExponent` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

By the lemma on row lengths, the terms $l/L$ and $lu$ sum to $\mathrm{boxes}(\kappa, |n'|)(1/L + u)/2$ when $\kappa$ fits the ranks.

**Proposition (Growth of Schur coefficients).** Let $\kappa$ be a lift weight from $n$ to $n'$, $\sigma$ a ring automorphism of $\mathbb{C}$, and $y$ a covector with $|\sigma(y\cdot\eta)| \le \|\sigma\circ\eta\|_\kappa$ for all $\eta$. Then for every vector $\xi$, every positive integer $L$ and every real $u$, the polynomial $Q_{y,\xi}$ has conjugate growth
$$\bigl(e^u,\ L,\ \mathrm{schurGrowthExponent}(n, n', \kappa, L, u),\ \|\sigma\circ\xi\|_\kappa\bigr)$$
under $\sigma$.

Lean: `New.Parameters.hasConjugateGrowth_schurCoeffPoly` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* Let $z$ and $R$ satisfy $\sum|\sigma(z_i)|^2 \le e^u(2L+2)R$. Let $Z_\tau$ be the matrix of the $z_{\tau, j, i}$, and $Z^\sigma_\tau$ the matrix of the $\sigma(z_{\tau, j, i})$. The Schur matrix has integer polynomial entries, so $\sigma(S_\kappa(Z)\xi) = S_\kappa(Z^\sigma)\,(\sigma\circ\xi)$. By the hypothesis on $y$,
$$|\sigma(Q_{y,\xi}(z))| = |\sigma(y\cdot S_\kappa(Z)\xi)| \le \|S_\kappa(Z^\sigma)(\sigma\circ\xi)\|_\kappa.$$
The norm bound for $S_\kappa$ at $Z^\sigma$ gives $\rho$ with $\sum_{\tau, i}\rho_\tau(i) \le \sum|\sigma(z_i)|^2 \le e^u(2L+2)R$ and
$$\|S_\kappa(Z^\sigma)(\sigma\circ\xi)\|_\kappa \le \sqrt{\textstyle\prod\rho^l}\,\|\sigma\circ\xi\|_\kappa.$$
The monomial bound gives $\sqrt{\prod\rho^l} \le \exp(\mathrm{schurGrowthExponent}(n, n', \kappa, L, u) + LR)$. $\square$

**Theorem (Size of Schur jets).** Let $f$ be a vacuum combination of size $B$ on $V = \mathrm{Hom}(V_n, V_{n'})$, let $a$, $b$ be automorphic characters with weights $e_a$, $e_b$, let $g$, $h$ be finite unitary points, $\sigma$ a ring automorphism of $\mathbb{C}$, $c \in \mathbb{C}$, $L$ a positive integer, and $\kappa$ a lift weight from $n$ to $n'$ with exponents $e_b$, $e$. Put $G = J_{ct_0}\,\omega_{a,b}((1,g),(1,h))\,f$ and $u = \log(|\sigma(c)|^2/\Omega_E)$. Then for every vector $\xi$,
$$\bigl\|\sigma\circ\bigl(\mathrm{schurJet}_\kappa(G)\,\xi\bigr)\bigr\|_\kappa \le \mathrm{jetSizeBound}\bigl(n, n', B, L, \mathrm{schurGrowthExponent}(n, n', \kappa, L, u)\bigr)\cdot\|\sigma\circ\xi\|_\kappa.$$

Lean: `New.Parameters.sqrt_weylNormSq_schurJet_le_of_isVacuumCombination` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* By duality for the Gram norm, from [Weyl modules](/chapter/weyl-modules/): it is enough to show $|\sigma(y\cdot v)| \le C$ for $v = \mathrm{schurJet}_\kappa(G)\xi$, the right side $C$, and every covector $y$ with $|\sigma(y\cdot\eta)| \le \|\sigma\circ\eta\|_\kappa$ for all $\eta$. For such $y$, $y\cdot v = \partial_{Q_{y,\xi}}G$. The proposition gives conjugate growth $(e^u, L, \mathrm{schurGrowthExponent}, \|\sigma\circ\xi\|_\kappa)$, and $|\sigma(c)|^2/\Omega_E \le e^{u}$. The theorem on the size of jets with $T = e^u$ and $A = \|\sigma\circ\xi\|_\kappa \ge 0$ gives the bound. $\square$

**Remark (Formalization).** If $\sigma(c) = 0$, then $u = \log 0$, which is $0$ in the source, and $T = e^0 = 1 \ge 0 = |\sigma c|^2/\Omega_E$. So the theorem still holds, with a weaker bound than the true one. In the argument $c \ne 0$. The step $|\sigma(c)|^2/\Omega_E \le e^{\log(|\sigma c|^2/\Omega_E)}$ is an inequality, not an equality, for this reason.

**Example.** Let $\kappa$ have all columns of height $1$ at one place $\tau_0$, $k$ of them, and $|n| = 1 < |n'|$. Row $0$ at $\tau_0$ counts the columns of height $h$ with $0 < h < |n'|$, so $l(\tau_0, 0) = k$, and $\mathrm{boxes}(\kappa, |n'|) = k$. The exponent is $\frac12(k/L + \log k! + ku)$. Take $L = k$. The bound is $B\,e^{C_P(q_1|n'|+1)^2}(2k+2)^{f|n'|}\,e^{1/2}\sqrt{k!}\,(|\sigma c|^2/\Omega_E)^{k/2}$ times $\|\sigma\circ\xi\|_\kappa$. Up to the constant and the factor $(2k+2)^{f|n'|}$ this is the bound $\sqrt{k!}\,T^{k/2}$ of the model case.
