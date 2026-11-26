---
title: Least valuations on copies
lean:
  - New/Derivatives/Sharpness/LeastValuation.lean
decls:
  - New.IsLowestTerm
  - New.IsLowestTerm.mul
  - New.copySubst
  - New.norm_coeff_copySubst_le
  - New.padicInt_sum_four_squares
  - New.CMLattice.LeastValLE
  - New.CMLattice.LeastValLE.mono
  - New.CMLattice.leastValLE_zero
  - New.CMLattice.LeastValLE.add
  - New.CMLattice.leastValLE_of_copySubst
  - New.CMLattice.leastValLE_of_rescale
  - New.CMLattice.LeastValLE.exists_monomial
  - New.CMLattice.prod_rescale_theta_mem
  - New.CMLattice.scaledThetaProd
  - New.CMLattice.exists_scaledThetaProd_mem_mul_eq_one
  - New.CMLattice.leastValLE_of_unit_coefficients
  - New.CMLattice.leastValLE_zero_of_span
  - New.CMLattice.rescale_mem_range_seriesToCp_of_mem_multiSeriesRing
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Least valuations on copies

This section moves from one variable to many. The variables are $z_x$, for $x$ in a finite set $X$. A family of linear forms $\mu_jz = \sum_x\mu_j(x)z_x$, for $j \in J$, is fixed, together with multiplicities $m_j$. The theta product is
$$\Theta = \prod_{j \in J}\theta(\mu_jz)^{m_j}$$
(`New.CMLattice.thetaProd`, from [resolutions, partners and theta products](/chapter/cm-formal-group/#resolutions-partners-and-theta-products)). The ring $\mathfrak{o}[[y(\mu z)]]$ is the ring of series $G(y(\mu_jz))_j$ with $G$ over $\mathfrak{o}$ (`New.CMLattice.multiSeriesRing`, from [integrality and the formal group](/chapter/cm-elliptic-curves/#integrality-and-the-formal-group)).

The section defines a relation $\mathrm{val}_n(\nu) \leq r$ and proves the two bounds on six copies that the later sections use.

### Lowest terms

**Definition (Lowest term).** Let $w : X \to \mathbb{N}$ be weights. The series $f$ has *lowest term* $c\,z^m$ for $w$ if every coefficient of $f$ of weight at most $w(m)$ equals the coefficient of the monomial $c\,z^m$. The value $c = 0$ is allowed.

Lean: `New.IsLowestTerm` (New/Derivatives/Sharpness/LeastValuation.lean).

**Lemma (Lowest term of a product).** If $f$ has lowest term $c\,z^D$ and $g$ has lowest term $d\,z^{D'}$, then $fg$ has lowest term $cd\,z^{D + D'}$. The same holds for finite products and powers.

Lean: `New.IsLowestTerm.mul` (New/Derivatives/Sharpness/LeastValuation.lean), with `New.IsLowestTerm.prod` and `New.IsLowestTerm.pow`.

*Proof.* Let $e$ have weight at most $w(D + D')$. The coefficient of $fg$ at $e$ is $\sum_{a + b = e}f_ag_b$. If $w(a) < w(D)$, then $f_a = 0$, since $a \neq D$. If $w(a) > w(D)$, then $w(b) < w(D')$, so $g_b = 0$. If $w(a) = w(D)$ and $a \neq D$, then $f_a = 0$. So only $a = D$ remains, and then $b = e - D$ has $w(b) \leq w(D')$. Its value $g_b$ is $d$ if $b = D'$ and $0$ otherwise. The coefficient is $cd$ if $e = D + D'$ and $0$ otherwise. Products and powers follow by induction. $\square$

### Copies

**Definition (Substitution of copies).** Let $K$ be a finite set and $a : K \to R$. For a series $F$ in the variables $z_x$, the series $F(\sum_ka_kz_k)$ in the variables $z_{(x,k)}$ substitutes $\sum_ka_kz_{(x,k)}$ for $z_x$.

Lean: `New.copySubst` (New/Derivatives/Sharpness/LeastValuation.lean).

For an exponent $\gamma$ on $X \times K$, let $\bar\gamma$ be the exponent on $X$ with $\bar\gamma(x) = \sum_k\gamma(x, k)$. It adds up the copies of each variable.

**Lemma (Integral substitutions do not raise coefficients).** If $|a_k| \leq 1$ for all $k$, then $|\mathrm{coeff}_\gamma F(\sum_ka_kz_k)| \leq |\mathrm{coeff}_{\bar\gamma}F|$.

Lean: `New.norm_coeff_copySubst_le` (New/Derivatives/Sharpness/LeastValuation.lean), with `New.coeff_copySubst`.

*Proof.* Only the monomials of $F$ of degree $\bar\gamma$ contribute to the coefficient at $\gamma$. Expanding $\prod_x(\sum_ka_kz_{(x,k)})^{\bar\gamma(x)}$ gives
$$\mathrm{coeff}_\gamma F\Bigl(\sum_ka_kz_k\Bigr) = \prod_{(x,k)}a_k^{\gamma(x,k)}\cdot\prod_x\binom{\bar\gamma(x)}{\gamma(x, \cdot)}\cdot\mathrm{coeff}_{\bar\gamma}F.$$
The multinomial coefficients are integers, so they have norm at most $1$. The factors $a_k$ have norm at most $1$. $\square$

**Lemma (Four squares).** Every $x \in \mathbb{Z}_p$ is a sum $\sum_{i<4}a_i^2$ of four squares in $\mathbb{Z}_p$.

Lean: `New.padicInt_sum_four_squares` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Every natural number is a sum of four squares, by Lagrange's theorem. The map $a \mapsto \sum_ia_i^2$ on $\mathbb{Z}_p^4$ is continuous and $\mathbb{Z}_p^4$ is compact, so its range is closed. The range contains the naturals, which are dense in $\mathbb{Z}_p$. So it is all of $\mathbb{Z}_p$. $\square$

### The relation

**Definition (Least valuation).** Let $n \in \mathbb{N}$, $\nu$ an exponent on $X$ and $r \in \mathbb{R}$. The relation $\mathrm{val}_n(\nu) \leq r$ holds if there are $H_c \in \mathfrak{o}[[y(\mu z)]]$ and exponents $\alpha_c$, for $c < n$, with $\sum_c\alpha_c = \nu$ and
$$p^{-r} \leq \prod_{c < n}|\mathrm{coeff}_{\alpha_c}(H_c\Theta)|.$$
The right side is the norm of the coefficient at $\prod_cz_c^{\alpha_c}$ of the product $\prod_c(H_c\Theta)(z_c)$ over $n$ copies $z_c$ of the variables.

Lean: `New.CMLattice.LeastValLE` (New/Derivatives/Sharpness/LeastValuation.lean).

**Remark (Formalization).** The source defines no least valuation as a number. `LeastValLE` is a relation in $r$. So no infimum, no junk value and no question of attainment arises. The name of the section reflects the intended reading: the least valuation of the degree-$\nu$ coefficients is at most $r$.

**Lemma (Rules).**

1. If $\mathrm{val}_n(\nu) \leq r$ and $r \leq r'$, then $\mathrm{val}_n(\nu) \leq r'$.
2. $\mathrm{val}_n(0) \leq 0$ for every $n$.
3. If $\mathrm{val}_n(\nu) \leq r$ and $\mathrm{val}_{n'}(\nu') \leq r'$, then $\mathrm{val}_{n+n'}(\nu + \nu') \leq r + r'$.

Lean: `New.CMLattice.LeastValLE.mono`, `New.CMLattice.leastValLE_zero`, `New.CMLattice.LeastValLE.add` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* (1) $p^{-r'} \leq p^{-r}$ as $p \geq 1$. (2) Take all $H_c = 1$ and $\alpha_c = 0$. The constant term of $\Theta$ is $1$, since $\theta(0) = 1$. (3) Put the two families side by side. The product of the two bounds is the bound for the joined family, since $p^{-(r + r')} = p^{-r}p^{-r'}$. $\square$

**Lemma (Substitution).** Let $A_{c,k}$, for $c < n$ and $k \in K$, have $|A_{c,k}| \leq 1$, and let $H_c \in \mathfrak{o}[[y(\mu z)]]$. If the coefficient at $\gamma$ of $\prod_c(H_c\Theta)(\sum_kA_{c,k}z_k)$ has valuation at most $r$, then $\mathrm{val}_n(\bar\gamma) \leq r$.

Lean: `New.CMLattice.leastValLE_of_copySubst` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* The coefficient of the product is the sum, over the splittings $\gamma = \sum_c\beta_c$, of $\prod_c\mathrm{coeff}_{\beta_c}(H_c\Theta)(\sum_kA_{c,k}z_k)$. The sum is not empty, since its norm is at least $p^{-r} > 0$. By the ultrametric inequality some term $\beta$ has norm at least $p^{-r}$. By the last lemma each factor has norm at most $|\mathrm{coeff}_{\bar\beta_c}(H_c\Theta)|$. Take the same $H_c$ and $\alpha_c = \bar\beta_c$. Then $\sum_c\alpha_c = \bar\gamma$. $\square$

**Corollary (Scaling).** Let $|\delta_c| \leq 1$ and $H_c \in \mathfrak{o}[[y(\mu z)]]$ for $c < n$. If the coefficient at $\nu$ of $\prod_c(H_c\Theta)(\delta_cz)$ has valuation at most $r$, then $\mathrm{val}_n(\nu) \leq r$.

Lean: `New.CMLattice.leastValLE_of_rescale` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Apply the substitution lemma with one new copy, $K = \{\ast\}$ and $A_{c,\ast} = \delta_c$. The new copy is identified with $z$, and then $\bar\gamma = \nu$. $\square$

**Lemma (Monomials suffice).** If $\mathrm{val}_n(\nu) \leq r$, then there are exponents $\alpha_c$ on $X$ and $e_c$ on $J$, for $c < n$, with $\sum_c\alpha_c = \nu$, $|e_c| \leq |\nu|$ and
$$p^{-r} \leq \prod_c\Bigl|\mathrm{coeff}_{\alpha_c}\Bigl(\prod_jy(\mu_jz)^{e_c(j)}\,\Theta\Bigr)\Bigr|.$$

Lean: `New.CMLattice.LeastValLE.exists_monomial` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Let $H_c$, $\alpha_c$ witness the relation. For each exponent $\beta$, [the largest monomial lemma](/decl/New.exists_monomial_max_norm_coeff/) for the series $y(\mu_jz)$ and $s = \Theta$ gives $e(\beta)$ with $|e(\beta)| \leq |\beta|$. Its monomial, times $\Theta$, has a coefficient at $\beta$ at least as large as that of every $G(y(\mu z))\Theta$. Put $e_c = e(\alpha_c)$. Then $|e_c| \leq |\alpha_c| \leq |\nu|$. Each $H_c$ is some $G(y(\mu z))$, so each factor does not decrease. $\square$

**Remark (Formalization).** The map $\beta \mapsto e(\beta)$ comes from `choose`. So the monomials are not explicit, and only the bound $|e_c| \leq |\nu|$ on them is known. Section 7 needs exactly this bound.

### Six copies of theta

**Lemma (Products of scaled theta).** Let $\delta_c \in \mathbb{Z}_p$, for $c < n$, with $\sum_c\delta_c^2 = 0$. Then $\prod_c\theta(\delta_cz) \in \mathfrak{o}[[y]]$.

Lean: `New.CMLattice.prod_rescale_theta_mem` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Write $\theta = \exp(-g)$ with $g$ the series $-\log\theta$ (`New.CMLattice.negLogTheta`). As $\sum_c\delta_c^2 = 0$,
$$\prod_c\theta(\delta_cz) = \exp\Bigl(-\sum_cg(\delta_cz)\Bigr) = \prod_c\exp\bigl(\delta_c^2g(z) - g(\delta_cz)\bigr).$$
For an integer $a$ of $K$, $\exp(a\bar a\,g(z) - g(az)) = \theta(az)/\theta(z)^{a\bar a}$ is in $\mathfrak{o}[[y]]$. The same holds for every pair $(\delta, s)$ in the closure of the pairs $(a, a\bar a)$ (`New.CMLattice.expSubst_sub_rescale_mem`, with `New.normPairClosure`). The pair $(\delta, \delta^2)$ is in this closure for $\delta \in \mathbb{Z}_p$: the pairs $(k, k^2)$ with $k \in \mathbb{N}$ are of the form $(a, a\bar a)$, and the map $\delta \mapsto (\delta, \delta^2)$ is continuous on $\mathbb{Z}_p$, in which $\mathbb{N}$ is dense. So each factor is in $\mathfrak{o}[[y]]$. $\square$

**Definition (Scaled theta product).** For $\delta : \{0, \dots, n-1\} \to \mathbb{Z}_p$, the scaled theta product is $\prod_c\Theta(\delta_cz)$.

Lean: `New.CMLattice.scaledThetaProd` (New/Derivatives/Sharpness/LeastValuation.lean), with `New.CMLattice.scaledThetaProd_eq_prod_subst`.

With $u(z) = \prod_c\theta(\delta_cz)$, the scaled theta product equals $\prod_ju(\mu_jz)^{m_j}$. One only exchanges the products over $c$ and $j$.

**Lemma (Six scalings).** There is $\delta : \{0, \dots, 5\} \to \mathbb{Z}_p$ with $\delta_0 = 1$ such that $\prod_c\Theta(\delta_cz)$ lies in $\mathfrak{o}[[y(\mu z)]]$, has an inverse $V$ in $\mathfrak{o}[[y(\mu z)]]$, and has constant term $1$.

Lean: `New.CMLattice.exists_scaledThetaProd_mem_mul_eq_one` (New/Derivatives/Sharpness/LeastValuation.lean), with `New.CMLattice.scaledThetaProd_mem` and `New.CMLattice.exists_scaledThetaProd_mul_eq_one`.

*Proof.* By the four squares lemma, $-1 = \sum_{i<4}a_i^2$ in $\mathbb{Z}_p$. Put $\delta = (1, a_0, a_1, a_2, a_3, 0)$. Then $\sum_c\delta_c^2 = 0$. By the last lemma $u = \prod_c\theta(\delta_cz) \in \mathfrak{o}[[y]]$, and $u(0) = 1$. A series of $\mathfrak{o}[[y]]$ with unit constant term has an inverse $v$ in $\mathfrak{o}[[y]]$, because $y$ generates the ring (`New.CMLattice.isSeriesGenerator_translatedY`). Substitute $\mu_jz$ for $z$. Then $\prod_ju(\mu_jz)^{m_j}$ and $\prod_jv(\mu_jz)^{m_j}$ lie in $\mathfrak{o}[[y(\mu z)]]$, and their product is $1$. $\square$

**Remark (Formalization).** The sixth entry is $\delta_5 = 0$. Its factor $\Theta(0 \cdot z)$ is the constant $1$. Five copies would do for this lemma. The source keeps six so that the later lemmas all have six copies.

### The two bounds on six copies

For an exponent $\nu$ on $X$ we write $v(\nu!) = \sum_xv(\nu(x)!)$ and $|\nu| = \sum_x\nu(x)$.

**Theorem (The rate on six copies).** If one form $\mu_{i_0}$ has $|\mu_{i_0}(x)| = 1$ for every $x$, then for every $\nu$,
$$\mathrm{val}_6(\nu) \leq \gamma_p|\nu| - v(\nu!).$$

Lean: `New.CMLattice.leastValLE_of_unit_coefficients` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Let $N = |\nu|$. By [the limit of the divisibility](/decl/New.CMLattice.katz_divisibility_limit/) there is $g \in \mathfrak{o}[[y]]$ with $(p^{-\gamma_p})^N \leq |N!\,\mathrm{coeff}_Ng|$. Take $\delta$ and $V$ from the six scalings lemma. Put $G = g(\mu_{i_0}z)$, $H_0 = GV$ and $H_c = 1$ for $c \neq 0$. These lie in $\mathfrak{o}[[y(\mu z)]]$. As $\delta_0 = 1$,
$$\prod_c(H_c\Theta)(\delta_cz) = G\,V\prod_c\Theta(\delta_cz) = G.$$
The coefficient of $G$ at $z^\nu$ is
$$\mathrm{coeff}_\nu G = \mathrm{coeff}_Ng\cdot\frac{N!}{\nu!}\prod_x\mu_{i_0}(x)^{\nu(x)}.$$
Its norm is $|N!\,\mathrm{coeff}_Ng|\,p^{v(\nu!)} \geq p^{-\gamma_pN + v(\nu!)}$. The scaling corollary, with $|\delta_c| \leq 1$, gives the claim. $\square$

**Theorem (Valuation zero on six copies).** Let $a_{x,j} \in \mathfrak{o}$ and $|s| = 1$ with
$$\sum_ja_{x,j}\,\mu_j(x') = \begin{cases}s & x = x',\\ 0 & x \neq x'.\end{cases}$$
Then $\mathrm{val}_6(\nu) \leq 0$ for every $\nu$.

Lean: `New.CMLattice.leastValLE_zero_of_span` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Put $G_x = \sum_ja_{x,j}\,y(\mu_jz)$. It lies in $\mathfrak{o}[[y(\mu z)]]$. As $y = z + O(z^2)$, the part of $G_x$ of degree at most $1$ is $\sum_ja_{x,j}\,\mu_jz = s\,z_x$. So $G_x$ has lowest term $s\,z_x$ for the total degree. The theta product has lowest term $1$. By the product rule, $\prod_xG_x^{\nu(x)}\,\Theta$ has lowest term $s^{|\nu|}z^\nu$. So its coefficient at $\nu$ is $s^{|\nu|}$, of norm $1$. This gives $\mathrm{val}_1(\nu) \leq 0$. Rule (2) gives $\mathrm{val}_5(0) \leq 0$, and rule (3) gives $\mathrm{val}_6(\nu) \leq 0$. $\square$

The first theorem uses all six copies. The second theorem uses only one copy, and the other five are in degree $0$.

### Scaling integral series

**Lemma (Integral after scaling).** Let $|\mu_j(x)| \leq 1$ for all $j$, $x$, and let $|\varpi| \leq p^{-\rho_p}$. If $H \in \mathfrak{o}[[y(\mu z)]]$, then $H(\varpi z)$ has coefficients in $\mathfrak{o}$.

Lean: `New.CMLattice.rescale_mem_range_seriesToCp_of_mem_multiSeriesRing` (New/Derivatives/Sharpness/LeastValuation.lean).

*Proof.* Write $H = G(y(\mu z))$. By [the exponent on one curve](/chapter/cm-formal-group/#the-exponent-on-one-curve), $y(\varpi z) = Y_0(z)$ with $Y_0$ integral (`New.CMLattice.rescale_mem_range_seriesToCp`). Then $y(\mu_j\varpi z) = Y_0(\mu_jz)$ is integral and has no constant term, since the $\mu_j(x)$ are integral. So $H(\varpi z) = G(Y_0(\mu_jz))_j$ is integral. $\square$

Section 4 uses this lemma for the factors $H_c$ after the scaling $z \mapsto \varpi z$ of the normal form.
