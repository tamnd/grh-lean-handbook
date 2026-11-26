---
title: Couplings at an inert prime
lean:
  - New/Derivatives/Sharpness/Couplings.lean
decls:
  - New.IsCouplingFamily
  - New.powerDegree
  - New.partnerDegree
  - New.degree_partnerDegree
  - New.exists_pderiv_mul_eq_smul
  - New.exists_jet_mul_prod_X
  - New.pairExponent
  - New.couplingSubst
  - New.IsCouplingFamily.isLowestTerm_pderiv_couplingSum
  - New.IsCouplingFamily.norm_coeff_powerDegree
  - New.IsCouplingFamily.norm_coeff_pairExponent
  - New.CMLattice.norm_pow_div_of_inert
  - New.CMLattice.one_lt_norm_pow_div_of_inert
  - New.CMLattice.exists_prod_rescale_rescale_thetaProd_eq
  - New.CMLattice.leastValLE_partnerDegree_of_isCouplingFamily
  - New.CMLattice.leastValLE_six_of_isCouplingFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Couplings at an inert prime

At an inert prime the rate $\gamma_p$ alone does not reach the forced divisibility $S_p$. The extra divisibility comes from the couplings $z_\tau^{p^e}z_{\tau^+}$ in the normal form of the theta product. This section shows that a product of couplings has a coefficient with negative valuation. The reason is a scalar $\kappa$ with $|\kappa| > 1$ in front of the couplings.

### The scalar

In this section the variables are $z_\tau$, one for each element $\tau$ of a finite set $\Phi$. (In Lean they are indexed by $\Phi \times \mathrm{Unit}$.) A partner rule $\mathrm{pr}(e, \tau)$ is given. For integral $l_{a,b}$ the coupling sum is
$$\Xi = \sum_{a \text{ odd}}\sum_{b \geq 0}l_{a,b}\,\Gamma_a^{p^b}, \qquad \Gamma_a = \sum_\tau z_\tau^{p^a}z_{\mathrm{pr}(a,\tau)}$$
(`New.couplingSum`). The series $F$ has the *normal form* if $F(\varpi z) = W\exp(\kappa\Xi)$ with $W$ integral and $\kappa = \varpi^{p+1}/p$ (`New.HasNormalForm`). Both are in [couplings and the normal form](/chapter/cm-formal-group/#couplings-and-the-normal-form). At an inert prime the exponents $a$ run over the odd numbers (`New.partnerExponents_of_inert`).

**Lemma (The scalar).** Let $p$ be inert in $K$ and $|\varpi| = p^{-\rho_p}$. Then $|\varpi^{p+1}/p| = p^{1 - 1/(p-1)}$. If also $p > 2$, then $|\varpi^{p+1}/p| > 1$.

Lean: `New.CMLattice.norm_pow_div_of_inert`, `New.CMLattice.one_lt_norm_pow_div_of_inert` (New/Derivatives/Sharpness/Couplings.lean), with `New.CMLattice.varpiValuation_mul_add_one_of_inert`.

*Proof.* At an inert prime $\rho_p = 1/(p^2-1)$, so $\rho_p(p+1) = 1/(p-1)$. Hence $|\varpi^{p+1}/p| = p^{-1/(p-1)}\cdot p$. For $p > 2$, $1/(p-1) < 1$, so the exponent $1 - 1/(p-1)$ is positive. $\square$

### Families of couplings

**Definition (Coupling family).** Let $\Phi_0 \subseteq \Phi$ and $e : \Phi \to \mathbb{N}$. Write $\tau^+ = \mathrm{pr}(e(\tau), \tau)$. The pair $(\Phi_0, e)$ is a *coupling family* if

1. $e(\tau)$ is odd for every $\tau \in \Phi_0$;
2. for $\tau, \tau_1 \in \Phi_0$ and odd $e' \leq e(\tau)$, $\mathrm{pr}(e', \tau_1) = \tau^+$ implies $\tau_1 = \tau$ and $e' = e(\tau)$.

Lean: `New.IsCouplingFamily` (New/Derivatives/Sharpness/Couplings.lean).

So among the couplings of places of $\Phi_0$ with the partner $\tau^+$, the coupling $z_\tau^{p^{e(\tau)}}z_{\tau^+}$ has the lowest degree, and it is the only one of that degree.

**Definition (The two degrees).** For $j : \Phi \to \mathbb{N}$, the degree of $\prod_{\tau \in \Phi_0}(z_\tau^{p^{e(\tau)}}z_{\tau^+})^{j(\tau)}$ splits into two parts:
$$\nu' = \sum_{\tau \in \Phi_0}p^{e(\tau)}j(\tau)\,\mathbf{1}_\tau, \qquad \nu'' = \sum_{\tau \in \Phi_0}j(\tau)\,\mathbf{1}_{\tau^+}.$$
So $|\nu'| = \sum_\tau p^{e(\tau)}j(\tau)$ and $|\nu''| = |j| = \sum_{\tau \in \Phi_0}j(\tau)$.

Lean: `New.powerDegree`, `New.partnerDegree`, `New.degree_partnerDegree` (New/Derivatives/Sharpness/Couplings.lean), with `New.degree_powerDegree`.

**Lemma (The lowest term of a derivative).** Let $(\Phi_0, e)$ be a coupling family and $\tau \in \Phi_0$. Reduce $\partial\Xi/\partial z_{\tau^+}$ modulo the maximal ideal and put $z_{\tau_1} = 0$ for $\tau_1 \notin \Phi_0$. The result has lowest term $\bar l_{e(\tau),0}\,z_\tau^{p^{e(\tau)}}$ for the total degree.

Lean: `New.IsCouplingFamily.isLowestTerm_pderiv_couplingSum` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Two facts from [couplings and the normal form](/chapter/cm-formal-group/#couplings-and-the-normal-form) describe $\partial\Xi/\partial z_{\tau^+}$ modulo the maximal ideal. Its coefficient at $z_\tau^{p^{e(\tau)}}$ is $\bar l_{e(\tau),0}$ (`New.residue_coeff_pderiv_couplingSum`). Every other monomial with a nonzero residue is $z_{\tau_1}^{p^a}$ with $a$ odd and $\mathrm{pr}(a, \tau_1) = \tau^+$ (`New.exists_eq_single_of_residue_coeff_pderiv_ne_zero`). Let such a monomial have degree $p^a \leq p^{e(\tau)}$. Then $a \leq e(\tau)$. If $\tau_1 \notin \Phi_0$, the term is killed. If $\tau_1 \in \Phi_0$, condition (2) gives $\tau_1 = \tau$ and $a = e(\tau)$. $\square$

**Lemma (A unit coefficient).** Let $(\Phi_0, e)$ be a coupling family and let $l_{a,0}$ be a unit for odd $a$. If $g$ is integral with $g \equiv \prod_{\tau \in \Phi_0}(\partial\Xi/\partial z_{\tau^+})^{j(\tau)}$ modulo the maximal ideal, and $U$ is integral with constant term $1$, then $|\mathrm{coeff}_{\nu'}(gU)| = 1$.

Lean: `New.IsCouplingFamily.norm_coeff_powerDegree` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Reduce modulo the maximal ideal and put $z_{\tau_1} = 0$ for $\tau_1 \notin \Phi_0$. Neither step changes the coefficient at $\nu'$, which lives on $\Phi_0$, up to reduction. By the last lemma and the product rule for lowest terms, the reduction of $g$ has lowest term $c\,z^{\nu'}$ with $c = \prod_\tau\bar l_{e(\tau),0}^{j(\tau)} \neq 0$. The reduction of $U$ has lowest term $1$. So the reduced coefficient of $gU$ at $\nu'$ is $c \neq 0$. An integer of $\mathbb{C}_p$ with nonzero residue is a unit. $\square$

### Derivatives bring down the scalar

**Lemma (One derivative).** Let $|\kappa| > 1$ and $\partial$ a derivative in one variable. If $\partial G = (\kappa A + B)G$ with $A$, $B$ integral, then for integral $g$ there is an integral $g'$ with $\partial(gG) = \kappa\,g'G$ and $g' \equiv gA$ modulo the maximal ideal.

Lean: `New.exists_pderiv_mul_eq_smul` (New/Derivatives/Sharpness/Couplings.lean), with `New.exists_pderiv_mul_expSubst`.

*Proof.* Put $g' = gA + \kappa^{-1}(\partial g + gB)$. Then $\kappa g'G = \kappa gAG + (\partial g)G + gBG = \partial(gG)$. As $|\kappa^{-1}| < 1$, $g' \equiv gA$. $\square$

For $F = W\exp(\kappa\Xi)$ with $W$ a unit, $\partial F = (\kappa\,\partial\Xi + \partial W/W)F$, and $\partial W/W$ is integral. So the lemma applies to $F$ with $A = \partial\Xi$.

**Lemma (Many derivatives).** If $\partial_{t_i}G = (\kappa A_i + B_i)G$ with $A_i$, $B_i$ integral, for $i$ in a finite set $T$, then there is an integral $g \equiv \prod_{i \in T}A_i$ with $(\prod_{i \in T}\partial_{t_i})\,f(\partial)G\,(0) = \kappa^{|T|}f(\partial)(gG)(0)$ for every polynomial $f$.

Lean: `New.exists_jet_mul_prod_X` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Induction on $T$, applying the last lemma once for each element. $\square$

### The two copies

**Definition (Coupling substitution).** For $\delta$ on $n + 1$ copies, substitute $z_0 = \delta_0z' + z''$ and $z_c = \delta_cz'$ for $c \neq 0$, in two new copies $z'$, $z''$ of the variables. The exponent of $z'^{\nu'}z''^{\nu''}$ is written $(\nu', \nu'')$.

Lean: `New.couplingSubst`, `New.pairExponent` (New/Derivatives/Sharpness/Couplings.lean).

**Theorem (The coefficient along couplings).** Let $(\Phi_0, e)$ be a coupling family, let $l_{a,0}$ be a unit for odd $a$, let $|\kappa| > 1$ and $F = W\exp(\kappa\Xi)$ with $W$ an integral unit. Let $\delta_0 = 1$, and let $\prod_cF(\delta_cz) = U$ be integral with constant term $1$. Put $G = F(z' + z'')\prod_{c \neq 0}F(\delta_cz')$. Then
$$|\nu''!|\cdot|\mathrm{coeff}_{(\nu', \nu'')}G| = |\kappa|^{|j|}.$$

Lean: `New.IsCouplingFamily.norm_coeff_pairExponent` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Only the first factor of $G$ involves $z''$. So $\partial_{z''_x}G = (\kappa\,\partial_x\Xi + B)(z' + z'')\,G$ with $B$ integral. Differentiate $j(\tau)$ times in $z''_{\tau^+}$ for each $\tau \in \Phi_0$. That is $|j|$ derivatives, and together they are $\partial^{\nu''}$ in $z''$. The lemma on many derivatives gives an integral $g$ with
$$\partial_{z'}^{\nu'}\partial_{z''}^{\nu''}G(0) = \kappa^{|j|}\,\partial_{z'}^{\nu'}(gG)(0), \qquad g(z', 0) \equiv \prod_{\tau \in \Phi_0}(\partial\Xi/\partial z_{\tau^+})^{j(\tau)}(z').$$
At $z'' = 0$, $G(z', 0) = \prod_cF(\delta_cz') = U(z')$. The right side depends only on $gG$ at $z'' = 0$, and equals $\kappa^{|j|}\nu'!\,\mathrm{coeff}_{\nu'}(g(z', 0)U)$. By the unit coefficient lemma this coefficient has norm $1$. The left side is $\nu'!\,\nu''!\,\mathrm{coeff}_{(\nu', \nu'')}G$. Divide by $\nu'! \neq 0$ and take norms. $\square$

### Six copies of the theta product

**Lemma (Six integral scalings after the scale).** Let the forms $\mu_j$ be integral and $|\varpi| \leq p^{-\rho_p}$. There are $\delta_c$, $c < 6$, with $\delta_0 = 1$ and $|\delta_c| \leq 1$, such that $\prod_c\Theta(\delta_c\varpi z)$ is an integral series $U$ with constant term $1$.

Lean: `New.CMLattice.exists_prod_rescale_rescale_thetaProd_eq` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Take $\delta$ from [the six scalings lemma](/decl/New.CMLattice.exists_scaledThetaProd_mem_mul_eq_one/). The product $\prod_c\Theta(\delta_cz)$ lies in $\mathfrak{o}[[y(\mu z)]]$ and has constant term $1$. By [the scaling lemma](/decl/New.CMLattice.rescale_mem_range_seriesToCp_of_mem_multiSeriesRing/) it stays integral after $z \mapsto \varpi z$. $\square$

**Theorem (Couplings on six copies, the exact bound).** Let $p > 2$ be inert, let the forms $\mu_j$ be integral, $|\varpi| = p^{-\rho_p}$, $l_{a,0}$ a unit for odd $a$, and let $\Theta$ have the normal form with these $\varpi$, $l$ and the partner rule $\mathrm{pr}$. Let $(\Phi_0, e)$ be a coupling family and $\nu = \nu' + \nu''$. Then
$$\mathrm{val}_6(\nu) \leq \frac{|j|}{p-1} - |j| - \rho_p|\nu| - v(\nu''!).$$

Lean: `New.CMLattice.leastValLE_partnerDegree_of_isCouplingFamily` (New/Derivatives/Sharpness/Couplings.lean), with `New.CMLattice.isUnit_of_rescale_thetaProd_eq` and `New.coeff_prod_copySubst_rescale`.

*Proof.* Write $\Theta(\varpi z) = W\exp(\kappa\Xi)$ with $\kappa = \varpi^{p+1}/p$. The constant term of $W$ is $\Theta(0) = 1$, so $W$ is a unit. By the scalar lemma, $|\kappa| = p^{1 - 1/(p-1)} > 1$. Take $\delta$ and $U$ from the last lemma. Apply the coefficient theorem to $F = \Theta(\varpi z)$. Scaling by $\varpi$ multiplies the coefficient at $(\nu', \nu'')$ by $\varpi^{|\nu|}$. With $|\nu''!| = p^{-v(\nu''!)}$ this gives
$$|\mathrm{coeff}_{(\nu', \nu'')}\textstyle\prod_c\Theta(\text{coupling substitution})| = p^{(1 - 1/(p-1))|j| + \rho_p|\nu| + v(\nu''!)}.$$
The coupling substitution has integral coefficients, because $|\delta_c| \leq 1$. [The substitution lemma](/decl/New.CMLattice.leastValLE_of_copySubst/) with $H_c = 1$ gives the bound, since the copies of $(\nu', \nu'')$ add up to $\nu$. $\square$

**Theorem (Couplings on six copies).** Under the same hypotheses,
$$\mathrm{val}_6(\nu) \leq -|j| \qquad\text{and}\qquad \mathrm{val}_6(\nu) \leq \gamma_p|\nu| - |j| - v(\nu'!) - v(\nu''!).$$

Lean: `New.CMLattice.leastValLE_six_of_isCouplingFamily` (New/Derivatives/Sharpness/Couplings.lean).

*Proof.* Both follow from the exact bound by monotony. For the first, $|\nu'| = \sum_\tau p^{e(\tau)}j(\tau) \geq p|j|$ since $e(\tau) \geq 1$. So $|\nu| \geq (p+1)|j|$ and $\rho_p|\nu| \geq \rho_p(p+1)|j| = |j|/(p-1)$. Also $v(\nu''!) \geq 0$. For the second, Legendre's bound gives $v(\nu'!) \leq |\nu'|/(p-1)$. With $|\nu| = |\nu'| + |j|$ and $\gamma_p = 1/(p-1) - \rho_p$,
$$\gamma_p|\nu| - |j| - v(\nu'!) \geq \frac{|\nu'| + |j|}{p-1} - \rho_p|\nu| - |j| - \frac{|\nu'|}{p-1} = \frac{|j|}{p-1} - |j| - \rho_p|\nu|.$$
Subtract $v(\nu''!)$ from both sides. $\square$

**Remark (Formalization).** The Lean proof of the last theorem is preceded by `seal Finset.sum Finset.prod Finset.univ in`. The source comment says that this keeps definitional checks from unfolding the finite sums. It does not change the statement.

The first bound serves the inert primes $p > k$, where six further copies carry valuation $0$. The second bound serves the primes $p \leq k$, where six further copies carry the rate $\gamma_p$. Section 6 uses both.
