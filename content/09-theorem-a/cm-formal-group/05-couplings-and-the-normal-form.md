---
title: Couplings and the normal form
lean:
  - New/Derivatives/Divisibility/NormalForm.lean
decls:
  - New.coupling
  - New.couplingSum
  - New.HasNormalForm
  - New.rescale_coupling
  - New.HasNormalForm.exists_subst_eq_mul_expSubst
  - New.HasNormalForm.of_dvd_sub
  - New.HasNormalForm.rescale
  - New.HasNormalForm.exists_of_norm_eq
  - New.dvd_coeff_subst_couplingSum
  - New.HasNormalForm.norm_coeff_subst_le_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Couplings and the normal form

Section 4 wrote $\theta(\varpi z)$ as an integral series times $\exp(c_\varpi\Xi)$, with $\Xi$ a sum of the monomials $(z^{p^e}z)^{p^j}$ modulo $\pi_p$. This section sets up the same shape in many variables. The monomial $z^{p^e}z$ becomes a coupling $\Gamma_e$, which pairs each variable with the variable of a partner. A series with this shape has the *normal form*. The section proves the formal properties of the normal form: it is stable under substitution and scaling, it is enough to know the exponent modulo $\pi_p$, and it gives integrality in low degrees when the couplings are divisible.

Nothing in this section uses theta functions or the field $E$. The partners are given by an arbitrary rule. Section 6 supplies the rule $\tau \mapsto u(-p^e)\tau$ and proves that theta products have the normal form. The [next chapter](/chapter/normal-forms/) uses the integrality theorem at the end of this section.

### The setting

Fix a prime $p$ and two finite sets $\Phi$ and $c$. The elements $\tau$ of $\Phi$ are called places. The variables are $z_x$ for $x = (\tau, i) \in \Phi \times c$. A *partner rule* is a map $\mathrm{pr} : \mathbb{N} \times \Phi \to \Phi$, written $(e, \tau) \mapsto \mathrm{pr}_e(\tau)$. For $x = (\tau, i)$ we write $x'_e = (\mathrm{pr}_e(\tau), i)$. Fix also a set $S \subseteq \mathbb{N}$ of exponents. Series over $\mathfrak{o}$ are integral, and we read them over $\mathbb{C}_p$ when needed.

### Couplings

**Definition (Coupling, coupling sum, normal form).**

1. The *coupling* of exponent $e$ is the polynomial
$$\Gamma_e = \sum_{x \in \Phi \times c} z_x^{\,p^e}\, z_{x'_e}$$
with coefficients in $\mathfrak{o}$.
2. For numbers $\lambda_{ej} \in \mathfrak{o}$ ($e, j \in \mathbb{N}$), the *coupling sum* is
$$\Xi_{S,\lambda} = \sum_{e \in S}\sum_{j \ge 0}\lambda_{ej}\,\Gamma_e^{\,p^j}.$$
3. Let $\varpi \in \mathbb{C}_p$ and let $F$ be a power series over $\mathbb{C}_p$ in the variables $z_x$. Then $F$ *has the normal form* for $(S, \mathrm{pr}, \varpi, \lambda)$ if there is an integral series $W$ with
$$F(\varpi z) = W\,\exp\bigl(c_\varpi\,\Xi_{S,\lambda}\bigr), \qquad c_\varpi = \varpi^{p+1}/p.$$

Lean: `New.coupling`, `New.couplingSum`, `New.HasNormalForm` (New/Derivatives/Divisibility/NormalForm.lean).

Here $F(\varpi z)$ means $F$ with every $z_x$ replaced by $\varpi z_x$.

**Example.** Let $\Phi$ and $c$ have one element each, so there is one variable $z$, and let the partner rule be the identity. Then $\Gamma_e = z^{p^e}z$, and the coupling sum is $\sum_{e \in S}\sum_j\lambda_{ej}(z^{p^e}z)^{p^j}$. With $S = I_p^\circ$, item 4 of the [theorem on one curve](/decl/New.CMLattice.exists_exponent_tsum/) says that $\Xi \equiv \Xi_{S,\lambda}$ modulo $\pi_p$. The proposition on the exponent modulo $\pi$ below then gives the normal form for $\theta$ in one variable.

**Example.** Let $\Phi = \{\tau_1, \tau_2\}$ with the rule that swaps $\tau_1$ and $\tau_2$ for every $e$, and let $c$ have one element. Write $a = z_{\tau_1}$ and $b = z_{\tau_2}$. Then $\Gamma_e = a^{p^e}b + b^{p^e}a$. For $e = 0$ this is $2ab$. For the identity rule it would be $a^{p^e+1} + b^{p^e+1}$. The rule decides which products appear. In Section 6 it is the rule that couples a place with its conjugate partner.

**Lemma (Homogeneity and convergence).**

1. For $\alpha \in \mathfrak{o}$, $\Gamma_e(\alpha z) = \alpha^{p^e+1}\,\Gamma_e$. So $\Gamma_e$ has order at least $p^e + 1$.
2. The family $\lambda_{ej}\Gamma_e^{\,p^j}$ over $(e, j) \in S \times \mathbb{N}$ is summable, and its sum $\Xi_{S,\lambda}$ has the constant term $0$.
3. $\Xi_{S,\lambda}(\alpha z) = \Xi_{S,\lambda'}$ with $\lambda'_{ej} = \alpha^{(p^e+1)p^j}\lambda_{ej}$.
4. If the series $Z_x$ have the constant term $0$, then $\Gamma_e(Z) = \sum_x Z_x^{p^e}Z_{x'_e}$, and $\Xi_{S,\lambda}(Z) = \sum_{e \in S}\sum_j\lambda_{ej}\,\Gamma_e(Z)^{p^j}$ as a convergent sum.

Lean: `New.rescale_coupling` (New/Derivatives/Divisibility/NormalForm.lean), with `New.le_order_coupling`, `New.hasSum_couplingSum`, `New.constantCoeff_couplingSum`, `New.rescale_couplingSum`, `New.subst_coupling` and `New.hasSum_subst_couplingSum`.

*Proof.* (1) Each term $z_x^{p^e}z_{x'_e}$ is a monomial of degree $p^e + 1$. (2) The term $(e, j)$ has order at least $(p^e + 1)p^j$. For each degree $D$, only finitely many pairs $(e, j)$ have $(p^e + 1)p^j \le D$. So in each degree the sum is finite. (3) Apply (1) term by term, using (4). (4) Substitution is a continuous ring map on series without constant term, so it commutes with the convergent sum. $\square$

**Remark (Formalization).** The coupling sum is an infinite sum `tsum` over the subtype $S \times \mathbb{N}$, in the topology of coefficientwise convergence. By item 2 the family is summable. So the junk value $0$ of `tsum` for a family that is not summable does not occur, and $\Xi_{S,\lambda}$ is the true sum. The numbers $\lambda_{ej}$ are given for all $e \in \mathbb{N}$, as a function `l : ℕ → ℕ → valRingCp p`. Only the values with $e \in S$ matter.

### Substitution and the exponent modulo a prime

**Proposition (Substitution).** Let $F$ have the normal form for $(S, \mathrm{pr}, \varpi, \lambda)$, and let $Z_x$ be integral series in any set of variables, with the constant term $0$. Then there is an integral series $W'$ with
$$F(\varpi Z) = W'\,\exp\bigl(c_\varpi\,\Xi_{S,\lambda}(Z)\bigr).$$

Lean: `New.HasNormalForm.exists_subst_eq_mul_expSubst` (New/Derivatives/Divisibility/NormalForm.lean), with `New.subst_expSubst`.

*Proof.* Substitute $Z$ into $F(\varpi z) = W\exp(c_\varpi\Xi_{S,\lambda})$. The substitution commutes with the exponential, since $\Xi_{S,\lambda}$ has no constant term. Take $W' = W(Z)$, which is integral. $\square$

**Proposition (Exponent modulo $\pi$).** Let $\pi \in \mathfrak{o}$ with $|c_\varpi\pi| \le p^{-1/(p-1)}$. Let $W$ and $\Xi$ be integral series with $\Xi(0) = 0$ and $\Xi \equiv \Xi_{S,\lambda}$ modulo $\pi$. If $F(\varpi z) = W\exp(c_\varpi\Xi)$, then $F$ has the normal form for $(S, \mathrm{pr}, \varpi, \lambda)$.

Lean: `New.HasNormalForm.of_dvd_sub` (New/Derivatives/Divisibility/NormalForm.lean), with `New.norm_coeff_expSubst_smul_le_one`.

*Proof.* Put $G = \Xi - \Xi_{S,\lambda}$. Then $G(0) = 0$, and $G = \pi G_0$ with $G_0$ integral. So $c_\varpi G = (c_\varpi\pi)G_0$ has coefficients of norm at most $p^{-1/(p-1)}$. By the [exponential bound](/decl/New.norm_coeff_expSubst_le_one/) of Volume 7, $V = \exp(c_\varpi G)$ is integral. Then $\exp(c_\varpi\Xi) = V\exp(c_\varpi\Xi_{S,\lambda})$, and $F(\varpi z) = (WV)\exp(c_\varpi\Xi_{S,\lambda})$. $\square$

The condition on $\pi$ is the reason why the exponent must be known modulo $\pi_p$ and not modulo a smaller ideal. For $|\varpi| = p^{-\rho_p}$ and $\pi = \pi_p$ we get $v(c_\varpi\pi_p) = (p+1)\rho_p - 1 + v(\pi_p)$. For inert $p$ this is $1/(p-1) - 1 + 1 = 1/(p-1)$. For $p = d$ it is $(p+1)/(2p-2) - 1/2 = 1/(p-1)$. In both cases the condition holds with equality. The scale $\varpi$ is as large as the method allows.

### Scaling and the choice of the scale

**Proposition (Scaling).** Let $F$ have the normal form for $(S, \mathrm{pr}, \varpi, \lambda)$.

1. For $\alpha \in \mathfrak{o}$, the series $F(\alpha z)$ has the normal form for $(S, \mathrm{pr}, \varpi, \lambda')$ with $\lambda'_{ej} = \alpha^{(p^e+1)p^j}\lambda_{ej}$.
2. If $\varpi \ne 0$ and $|\varpi'| = |\varpi|$, then $F$ has the normal form for $(S, \mathrm{pr}, \varpi', \lambda'')$ for some numbers $\lambda''_{ej} \in \mathfrak{o}$.

Lean: `New.HasNormalForm.rescale`, `New.HasNormalForm.exists_of_norm_eq` (New/Derivatives/Divisibility/NormalForm.lean).

*Proof.* (1) We have $F(\alpha\varpi z) = W(\alpha z)\exp(c_\varpi\Xi_{S,\lambda}(\alpha z))$ by the proposition on substitution, and $\Xi_{S,\lambda}(\alpha z) = \Xi_{S,\lambda'}$ by item 3 of the lemma. (2) Put $\alpha = \varpi'/\varpi$ and $\beta = \varpi/\varpi'$. Both are units of $\mathfrak{o}$. By (1), $F(\varpi' z) = F(\alpha\varpi z)$ is $W_1\exp(c_\varpi\Xi_{S,\lambda'})$. Now $c_\varpi = c_{\varpi'}\beta^{p+1}$, so $c_\varpi\Xi_{S,\lambda'} = c_{\varpi'}\Xi_{S,\lambda''}$ with $\lambda''_{ej} = \beta^{p+1}\lambda'_{ej}$. $\square$

So the normal form depends on $\varpi$ only through $|\varpi|$, at the cost of new numbers $\lambda_{ej}$. The proof gives $\lambda''_{ej}$ as a unit times $\lambda_{ej}$, since $\alpha$ and $\beta$ are units. The lemma states only that some $\lambda''$ exists, so a later use cannot read off that a unit $\lambda_{ej}$ stays a unit.

### Integrality in low degrees

The main use of the normal form is a criterion for the integrality of $F(\varpi Z)$ in the degrees up to a bound $B$.

**Lemma (Divisibility of the coupling sum).** Let $Z_x$ be integral series with the constant term $0$, let $\pi \in \mathfrak{o}$, and let $B \in \mathbb{N}$. Assume that $\pi$ divides $\Gamma_e(Z)$ for every $e \in S$ with $e \le \log_p B$. Then $\pi$ divides every coefficient of $\Xi_{S,\lambda}(Z)$ of degree at most $B$.

Lean: `New.dvd_coeff_subst_couplingSum` (New/Derivatives/Divisibility/NormalForm.lean), with `New.le_order_subst_coupling_pow`.

*Proof.* By item 4 of the lemma, the coefficient is a convergent sum of the coefficients of $\lambda_{ej}\Gamma_e(Z)^{p^j}$. If $e \le \log_p B$, then $\pi$ divides $\Gamma_e(Z)$ and its powers. If $e > \log_p B$, then $p^e > B$, and $\Gamma_e(Z)^{p^j}$ has order at least $p^e + 1 > B$, since each $Z_x$ has order at least $1$. So its coefficient of degree at most $B$ is $0$. A convergent sum of multiples of $\pi$ in $\mathfrak{o}$ is a multiple of $\pi$, since $\pi\mathfrak{o}$ is closed. $\square$

Here $\log_p B$ is the integer part of the logarithm, `Nat.log p B`. Only the couplings with $p^e \le B$ enter.

**Theorem (Integrality from the normal form).** Let $F$ have the normal form for $(S, \mathrm{pr}, \varpi, \lambda)$. Let $\pi \in \mathfrak{o}$ with $|c_\varpi\pi| \le p^{-1/(p-1)}$. Let $Z_x$ be integral series with the constant term $0$, and let $B \in \mathbb{N}$ such that $\pi$ divides $\Gamma_e(Z)$ for every $e \in S$ with $e \le \log_p B$. Then every coefficient of $F(\varpi Z)$ of degree at most $B$ has norm at most $1$.

Lean: `New.HasNormalForm.norm_coeff_subst_le_one` (New/Derivatives/Divisibility/NormalForm.lean).

*Proof.* By the proposition on substitution, $F(\varpi Z) = W'\exp(c_\varpi\Xi')$ with $W'$ integral and $\Xi' = \Xi_{S,\lambda}(Z)$. By the last lemma, $\pi$ divides the coefficients of $\Xi'$ of degree at most $B$. So the coefficients of $c_\varpi\Xi'$ of degree at most $B$ have norm at most $p^{-1/(p-1)}$, and the [exponential bound](/decl/New.norm_coeff_expSubst_le_one/) gives that $\exp(c_\varpi\Xi')$ is integral in these degrees. A coefficient of degree $m \le B$ of a product involves only coefficients of degree at most $m$ of the factors. $\square$

**Example.** Let $p = 3$ and $B = 20$. Then $\log_3 20 = 2$. For $S$ the set of odd numbers, only $\Gamma_1$ must be divisible by $\pi$. The coupling $\Gamma_3$ has degree $28 > 20$, and it does not enter. For $S = \mathbb{N}$, the set at $p = d$, the coupling $\Gamma_0 = \sum_x z_xz_{x'_0}$ also enters for every $B \ge 1$. It is quadratic.

The theorem turns a question on $p$-adic integrality of a theta series into a question on the divisibility of finitely many polynomials $\Gamma_e(Z)$. In the [next chapter](/chapter/normal-forms/) the series $Z_x$ come from the jets of a chain of theta lifts, and the divisibility of $\Gamma_e(Z)$ is a congruence between the places $\tau$ and their partners.

### Derivatives of the coupling sum

The file also computes the derivatives of $\Xi_{S,\lambda}$ modulo $p$. For $e > 0$, $\partial(G^{p^e})/\partial z_y$ is divisible by $p$. So, modulo $p$, only the linear factor $z_{x'_e}$ of $\Gamma_e$ contributes, and only the terms with $j = 0$. If $0 \notin S$, this gives
$$\frac{\partial\Xi_{S,\lambda}}{\partial z_y} \equiv \sum_{e \in S}\lambda_{e0}\sum_{x : x'_e = y} z_x^{\,p^e} \pmod{p}.$$

**Remark (Formalization).** The congruence above is `New.dvd_pderiv_couplingSum_sub`, with `New.partnerPowerSum` for the inner sum and the residue forms `New.residue_coeff_pderiv_couplingSum_eq`, `New.residue_coeff_pderiv_couplingSum` and `New.exists_eq_single_of_residue_coeff_pderiv_ne_zero`. The module docstring says that they are needed only for the sharpness of the divisibility bound, not for the bound itself. Sharpness is not part of Volume 9, so the handbook does not state them as results here. The hypothesis $0 \notin S$ excludes the ramified prime, where $I_p^\circ$ contains $0$. The definitions of this section use the classes `Fintype` on $\Phi$ and $c$; the derivative part also uses `DecidableEq`. The predicate `New.HasNormalForm` is a proposition with an existential quantifier over $W$. The numbers $\lambda_{ej}$ are part of the data, and the normal form does not determine them.
