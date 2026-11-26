---
title: One exchange and the exchange data
lean:
  - New/OneLift/ComparisonOperator/OneExchange.lean
  - New/OneLift/ComparisonOperator/ExchangeData.lean
  - New/OneLift/ComparisonOperator/DeterminantProducts.lean
decls:
  - New.Rows.rowStabilizer
  - New.Rows.columnDatum
  - New.Rows.columnDatum_mul_ite_eq_ite_mem_rowStabilizer
  - New.Rows.isRapid_modKernel
  - New.Rows.areMatched_det_mul
  - New.Rows.integrable_and_mul_stdClassSum_eq_integral_mul
  - New.Rows.mul_stdClassSum_eq_integral_mul_modKernel
  - New.Rows.integral_mul_modKernel_sum_translates
  - New.Rows.stdClassSum_tower
  - New.Rows.fixesLeft_modKernelStdSpace
  - New.Rows.stdClassSum_rowStabilizer_eq
  - New.Rows.carrierForm
  - New.Rows.carrierCoeff
  - New.Data.choiceFn
  - New.Data.isTameFor_of_hasWeight
  - New.Data.isTameFor_twistedChiMPow
  - New.Rows.exists_int_weylRep_invariant_fockPoly_eq_smul_monomial
  - New.exists_det_fromCols_eq_mul_det
  - New.Rows.twoSidedSubst_stackedDetProd
  - New.Rows.twoSidedSubst_firstColsCoord
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One exchange and the exchange data

The comparison operator of the later chapters applies the exchange identity three times. This section gives the tools for one application. They are a factorization when $W = E^b \oplus W'$, a reduction of class sums to row stabilizers, and the data of the three exchanges. In this section $E^b$ is the standard definite space, $\mathrm{cs}_K(f)$ is the class sum of $f$ at the level $K$ (the sum over the classes of the definite group, each weighted by the inverse of its number of automorphisms), and $K_0$ is the stabilizer of the standard lattice. The kernel $\theta^{S,T}_{\alpha,\beta}(\Psi, P)$ is the theta kernel of the pair $(S, T)$ with the datum $\Psi$ modulo $\mathfrak{m}$ and the Fock vector of the polynomial $P$.

### One exchange

**Lemma (Rapid decay).** If $\mathfrak{m} \neq (1)$ and $\Psi$ vanishes off the matrices with a left inverse, the kernel $g \mapsto \theta^{S,V}(\Psi, P)(g, h)$ has rapid decay on $[U(S)]$.

Lean: `New.Rows.isRapid_modKernel` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* This is the decay bound of the theta kernel for such data in [theta lifts and seesaws](/chapter/theta-lifts-seesaw/#growth-convergence-and-adjointness), applied to the Fock vector of $P$, whose moments are all finite. $\square$

**Lemma.** Let $\Psi'$ on $n \times b$ matrices modulo $\mathfrak{m}$ satisfy $\Psi'(y\gamma) = \Psi'(y)$ for $\gamma \in GL_b(O_E/\mathfrak{m})$. Then $\Phi(x', x'') = \chi(\det x'')\,\Psi'(x''^{-1}x')$ and $\Psi(y', y'') = \chi(\det y')\,\Psi'(y'')$ are matched for $\chi^{-1}$.

Lean: `New.Rows.areMatched_det_mul` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* The block pair of [the first part](/chapter/exchange-identity-1/#matched-functions) is matched for $\chi^{-1}$. Its first function is $\Phi$. Its second is $\chi(\det y')\,\Psi'(-y''y'^{-1})$ where $y'$ is invertible, and $0$ elsewhere. By the invariance under $-y'^{-1}$ this is $\Psi$. Where $y'$ is singular, $\chi(\det y') = 0$. $\square$

**Theorem (One exchange).** Let $W = E^b \oplus W'$. Suppose that for all matched $\Phi$, $\Psi$ for $\chi^{-1}$,
$$c\,\mathrm{cs}_{K_0}(K\Phi) = \int_{[U(V')]} \theta^{V', W}_{a, \beta\beta'}(\Psi, P)(x, ((1, h'), g))\,dx,$$
where $P$ is a polynomial in the variables of $W'$. Let $\Psi'$ be as in the lemma. Then the product $\theta^{V', E^b}_{a,\beta}(\chi\circ\det, 1)(x, h')\,\theta^{V', W'}_{a,\beta'}(\Psi', P)(x, g)$ is integrable, and its integral is $c\,\mathrm{cs}_{K_0}(K\Phi)$ for $\Phi(x', x'') = \chi(\det x'')\Psi'(x''^{-1}x')$. Summing over the classes $h'$ of $U(E^b)$: if $c_0\,\mathrm{cs}(h' \mapsto \mathrm{coef}(h')\,\theta^{V', E^b}(x, h')) = F(x)$, then
$$c\,c_0\,\mathrm{cs}\bigl(h' \mapsto \mathrm{coef}(h')\,\mathrm{cs}_{K_0}(K\Phi\,h')\bigr) = \int_{[U(V')]} F(x)\,\theta^{V',W'}_{a,\beta'}(\Psi', P)(x, g)\,dx.$$

Lean: `New.Rows.integrable_and_mul_stdClassSum_eq_integral_mul`, `New.Rows.mul_stdClassSum_eq_integral_mul_modKernel` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* The function matched with $\Phi$ is the product $\Psi(y', y'') = \chi(\det y')\,\Psi'(y'')$. A product datum on $E^b \oplus W'$ gives the product of the two kernels, as the Weil representation of a sum is the tensor product. So the integrand of the hypothesis is the product in the claim. Where $\Psi \neq 0$, $y'$ is invertible, so $y$ has a left inverse. By rapid decay the kernel is integrable. For the sum over classes: the class sum is finite, so it commutes with the integral, and each term is the first claim times $c_0\,\mathrm{coef}(h')$. $\square$

### Translates and the tower of class sums

**Lemma (Translates).** Let $F$ be automorphic, of rapid decay and right invariant under $K_0$, and let $\beta'$ have trivial tame part. For $\mathfrak{m}' \subseteq \mathfrak{m}$,
$$\int F\,\theta^{V',W'}_{a,\beta'}\Bigl(\sum_{\gamma \in GL_b(O_E/\mathfrak{m})}\psi(\bar y\gamma), P\Bigr) = |GL_b(O_E/\mathfrak{m})|\int F\,\theta^{V',W'}_{a,\beta'}(\psi, P).$$

Lean: `New.Rows.integral_mul_modKernel_sum_translates` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* The kernel is linear in the datum, and reading a datum modulo $\mathfrak{m}$ through $\mathfrak{m}'$ does not change the kernel. Let $k \in K_0$ lift $\gamma$. Right translation of the kernel by $k$ replaces $\psi$ by $\psi(\cdot\,\gamma)$ times $\beta'(\det k)$, and $\beta'(\det k) = 1$ as the tame part is trivial. $F$ is invariant under $k$. The integrand is automorphic, continuous and of rapid decay, so its integral over $[U(V')]$ is invariant under right translation. So each term is the integral for $\psi$. $\square$

**Lemma (Tower).** Let $H \leq GL_b(O_E/\mathfrak{m})$, and $K_H$ the elements of $K_0$ that reduce into $H$. Let $f_0$ be left invariant under the rational points and right invariant under $K_H$, and $f(h) = \sum_{q \in GL_b/H} f_0(h\,\tilde q)$ with lifts $\tilde q \in K_0$. If $f$ is right invariant under $K_0$, then $\mathrm{cs}_{K_H}(f_0) = \mathrm{cs}_{K_0}(f)$.

Lean: `New.Rows.stdClassSum_tower` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* A class sum at level $K$ is the integral over the class space divided by the volume of $K$. Integrate $f$: it is the sum of $[GL_b : H]$ integrals of translates of $f_0$, all equal. The index of $K_H$ in $K_0$ is $[GL_b : H]$, which cancels. $\square$

**Theorem (Row stabilizers).** Let $\varphi \colon O_E/\mathfrak{m} \to S$ be a ring map, $w$ a $c \times b$ matrix over $S$, $e \colon r \hookrightarrow b$, and $H$ the group of the invertible $A$ with the columns of $1$ off $e$ and $w\,\varphi(A) = w$. Let $F$ be left invariant under $H$, let $\alpha$ be tame for $(\mathfrak{m}, \gamma, \chi)$, and let the Fock vector of $P$ be fixed by the real group of $E^b$. Then the class sum at level $K_0$ of the kernel of $(W, E^b)$ with datum $\chi(\det x'')F(x''^{-1}x')$ equals the class sum at level $K_H$ of the kernel with datum
$$\Phi_0(x', x'') = \mathrm{col}(x''_e)\cdot\begin{cases}F(x') & x'' \text{ has the columns of } 1 \text{ off } e,\\ 0 & \text{otherwise},\end{cases}$$
where $\mathrm{col}(\sigma) = \chi(\det \sigma_{e,\cdot})$ if $w\varphi(\sigma) = w\,\iota_e$ and $0$ otherwise.

Lean: `New.Rows.rowStabilizer`, `New.Rows.columnDatum`, `New.Rows.columnDatum_mul_ite_eq_ite_mem_rowStabilizer`, `New.Rows.fixesLeft_modKernelStdSpace`, `New.Rows.stdClassSum_rowStabilizer_eq` (New/OneLift/ComparisonOperator/OneExchange.lean).

*Proof.* Step 1. $\Phi_0(x) = \Phi(x)$ if $x'' \in H$ and $0$ otherwise. Write $z = 1 + u\iota_e^T$ when $z$ has the columns of $1$ off $e$. Then $\det z_{e,e\text{-cols}} = \det z$ and both conditions on $w$ say $w\varphi(u) = 0$. So $\mathrm{col}(z_e) = \chi(\det z)$ if $w\varphi(z) = w$. If $z \in H$, $F(z^{-1}x') = F(x')$. If $z$ satisfies both conditions but is not invertible, $\chi(\det z) = 0$.

Step 2. The kernel, as a function of $h$, is left invariant under the rational points. A rational $\delta$ moves $h$ to $\delta h$. The invariance of the kernel cancels $\delta$ and leaves its real part, which acts on $P$ by a substitution times a power of $\det\delta$. By hypothesis that action fixes $P$.

Step 3. Right translation by $k \in K_0$ with reduction $A$ replaces the datum $\Psi$ by $\chi(\det A)\,\Psi(A^{-1}\cdot)$, as $\alpha$ is tame. This fixes $\Phi$, as $\chi(\det A^{-1}x'') = \chi(\det A)^{-1}\chi(\det x'')$. For $A \in H$ it fixes $\Phi_0$, by Step 1.

Step 4. $\Phi = \sum_{q \in GL_b/H} \chi(\det q)\,\Phi_0(q^{-1}\cdot)$: an invertible $x''$ lies in exactly one coset, and at a singular $x''$ all terms are $0$. With Steps 2 and 3, the tower lemma applies. $\square$

### The exchange data

The source fixes the objects of the three exchanges in one file. They are definitions, and later chapters use them. We list the ones that the later chapters name.

1. The *carrier* $\varphi^\circ$ is the theta lift of the constant $1$ from $U(I_m^-)$ to the group of the space $S$ of signature $(2m, m)$. Its kernel has trivial modulus, finite datum $1$, characters $\upsilon^m$ and $1$, and the polynomial $\prod_\tau \det(y^-_\tau)^{2m}$, where $y^-_\tau$ is the $m \times m$ block of the rows of sign $-1$.
2. The *coefficients* $\mathsf{a}(h)c(\det h)$ are the class sums over $U(I_m)$ of the kernel with characters $c$ and $1$ and all data trivial.
3. The function $\mathsf{F}_i$ on $U(W_j)$, for a choice $i$, is the integral over $[U(S)]$ of $\varphi^\circ$ times the kernel of $(S, W_j \oplus I_j^- \oplus I_{3m-j} \oplus I_{6m+1})$. Its finite datum is the additive character of a matrix $\Lambda$ modulo $\varpi^2$. Its polynomial is a fixed product of minors times a product of determinants that pairs short rows of a class of $U(I_{6m+1})$ with the variables.

Lean: `New.Rows.carrierForm`, `New.Rows.carrierCoeff`, `New.Data.choiceFn` (New/OneLift/ComparisonOperator/ExchangeData.lean).

**Lemma (Tameness of twisted characters).** Let $\vartheta$ be a twist with tame part non-trivial exactly on $Q$, and $c \neq 0$. If $\nu$ has weight $\gamma$ and tame part $\psi\,\vartheta$, with $\psi$ non-trivial exactly at the chosen places, then $\nu$ is tame for $(\varpi^c Q, \gamma)$ with the character of its tame part. In particular $\chi^j\vartheta$ is tame of weight $0$.

Lean: `New.Data.isTameFor_of_hasWeight`, `New.Data.isTameFor_twistedChiMPow` (New/OneLift/ComparisonOperator/ExchangeData.lean).

*Proof.* The places of the modulus are the chosen places and those of $Q$. These two sets are disjoint, since the norms of the places of $Q$ avoid the chosen primes. So $\psi\vartheta$ is non-trivial at $w$ exactly if $w$ is chosen or in $Q$. For $\chi^j\vartheta$, the tame part of $\chi^j$ is non-trivial exactly at the chosen places for $1 \leq j \leq m$. $\square$

**Theorem (Monomial vectors).** Let $X$ be lift data from $U(1)$ to a definite group, with row lengths $\ell_\tau$, and let $\alpha$ be an exponent on $r$ rows, placed by $e$, of degree $\ell_\tau$ at each $\tau$. There is an integer vector $v$ whose Fock polynomial is $\prod_\tau \ell_\tau!/\alpha!$ times the monomial $x^\alpha$ in the rows $e$. The vector is fixed by every $g$ whose columns $e$ are those of $1$.

Lean: `New.Rows.exists_int_weylRep_invariant_fockPoly_eq_smul_monomial` (New/OneLift/ComparisonOperator/ExchangeData.lean).

*Proof.* Let $v$ list the coefficients of $x^\alpha$ in the basis of products of minors. The monomial lies in column $0$, so it is semi-invariant of the weight of the lift. Pairing with the basis by the Fock form gives the polynomial of $v$ as the hook number times $x^\alpha/\alpha!$, and the hook number is $\prod_\tau \ell_\tau!$ here. If $g$ fixes the columns $e$, the substitution by $g^T$ fixes $x^\alpha$. The adjoint of the substitution acts on the basis by the Schur matrix, so the Schur matrix fixes $v$. $\square$

### Products of determinants

**Lemma.** (a) For a matrix $Z$ there are $Y$ and $\gamma$ with $\det(X \mid Z) = \gamma\det(YX)$ for all $X$. (b) Under $x_\tau \mapsto c_\tau^T x_\tau g_\tau^T$, the product of the determinants of $M_{\tau k}g_\tau^T$ stacked over $x_\tau$ goes to $\prod_\tau (\det c_\tau\det g_\tau)^{|\iota_\tau|}$ times the product for $M_{\tau k}$. (c) If this substitution with $g = \mathrm{diag}(1, g_\tau)$ sends $F'$ to $sF$, the coordinates in the first $p$ columns satisfy $\sum_{l'}\mathrm{schur}(c)_{ll'}\,\mathrm{coord}_{l'}(F') \mapsto s\,\mathrm{coord}_l(F)$.

Lean: `New.exists_det_fromCols_eq_mul_det`, `New.Rows.twoSidedSubst_stackedDetProd`, `New.Rows.twoSidedSubst_firstColsCoord` (New/OneLift/ComparisonOperator/DeterminantProducts.lean).

*Proof.* (a) Choose an invertible $(U_1 \mid U_2)$ with $U_1^*Z = 0$ and put $Y = U_1^*$. Then $(U_1 \mid U_2)^*(X \mid Z)$ is block triangular with diagonal blocks $U_1^*X$ and $U_2^*Z$. (b) One factor at a time: after the substitution the stacked matrix is $\mathrm{diag}(1, c_\tau)^T$ times the stacked matrix of $M_{\tau k}$ times $g_\tau^T$. (c) Under the splitting into the first columns and the rest, the substitution acts by $x \mapsto c^Tx$ on the first columns and by the substitution with $(c, g)$ on the coefficients. The adjoint of $x \mapsto c^Tx$ for the Fock form is $x \mapsto cx$, which acts on the basis of products of minors by the Schur matrix. $\square$

**Remark (Formalization).** The row stabilizer is defined as the intersection of a stabilizer for left multiplication and a stabilizer for right multiplication through the opposite group. The second condition $w\varphi(A) = w$ is a right action. The short rows in the exchange data are chosen with `Exists.choose` from the existence of short bases. No statement in this chapter depends on that choice.
