---
title: The top coefficient clears denominators
lean:
  - New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean
decls:
  - New.Patching.BaseLevel.exists_norm_apply_eq_smul
  - New.Patching.BaseLevel.sum_mul_residueRep_apply_eq_smul
  - New.Patching.BaseLevel.smul_top_coeff_mem_ellIntegralForms
  - New.Patching.BaseLevel.C_prod_sub_prod_mul_mem
  - New.Patching.BaseLevel.exists_heckeAlgebra_ribetElement
  - New.Patching.BaseLevel.exists_diagOp_mem_ellIntegralForms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The top coefficient clears denominators

This section proves the fourth main result of the chapter. Ribet's element $\mathcal{D}$ of the tied ideal is a polynomial in the $\alpha_j$. Its top coefficient, the coefficient of $\alpha_J$, clears the denominator of the projection of a form to the lifts, up to the factor $c$. The bound for the loss does not depend on the orders of the even classes. [The bound for denominators](/chapter/denominator-bound/) uses the last theorem of this section. The notation is that of [the last section](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm).

### Two lemmas on the norm

**Lemma.** Let the places $w_j$ be off the base level. Then there is an integral operator $\Psi$ with $\mathrm{Nm}(\Psi y) = c\, y$ for every form $y$ of base level.

Lean: `New.Patching.BaseLevel.exists_norm_apply_eq_smul` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean).

*Proof.* Take the Higman operator with $\sum_g g^{-1} \Psi g = c$. A form of base level is fixed by $\Gamma$, so $\sum_g g \Psi y = \sum_g g^{-1} \Psi g\, y = c\, y$. $\square$

So $c$ times a form of base level is a norm. In the proof of the theorem below, the form $u = \Psi(d\, l)$ is integral when $d\, l$ is, and $\mathrm{Nm}\, u = d c\, l$.

Let $A, \delta_0 \in \mathbb{T}$ and $n_0 \in \mathbb{Z}_\ell$, and put $\delta = c^2 A \delta_0$. Since $\delta_0 - n_0$ divides $\delta^k - (n_0 c^2)^k A^k$ in $\mathbb{T}$, a form $y$ with $\delta_0 y = n_0 y$ has $\delta^k s\, y = (n_0 c^2)^k A^k s\, y$ for all $s \in \mathbb{T}$ (`New.Patching.BaseLevel.sub_dvd_pow_sub_smul_pow`, `New.Patching.BaseLevel.heckeAction_pow_apply`).

**Lemma (Only the top term survives).** Let the places be off the base level, and let $\delta = c^2 A \delta_0$. Let $u$, $l$, $y$ be forms of principal level with $\mathrm{Nm}\, u = d c\, l$, $A \delta_0 l = n_0 A y$ and $\delta_0 y = n_0 y$. Let $Y_\emptyset = \delta^i$, and let $\mathcal{D}_S \in \mathbb{T}$, for $S \subseteq J$, kill $y$ for $S \neq J$. Then
$$\sum_{S \subseteq J} Y_{J \setminus S}\, \mathrm{Nm}\, \delta\, \mathcal{D}_S\, u = (n_0 c^2)^{i+1}\, d c\, A^{i+1} \mathcal{D}_J\, y.$$

Lean: `New.Patching.BaseLevel.sum_mul_residueRep_apply_eq_smul` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean), with `New.Patching.BaseLevel.norm_mul_heckeAction_apply` for one term.

*Proof.* The Hecke algebra commutes with $\Gamma$, so $\mathrm{Nm}\, \delta\, s\, u = \delta\, s\, (d c\, l) = n_0 c^2\, d c\, A s\, y$ for $s \in \mathbb{T}$. For $S \neq J$ the term vanishes, since $\mathcal{D}_S y = 0$. For $S = J$ the factor $Y_\emptyset = \delta^i$ acts on $A \mathcal{D}_J y$ as $(n_0 c^2)^i A^i$. $\square$

### The top coefficient

**Theorem (Top coefficient).** Let the places $w_j$ be off the base level, and let $N_x = a \otimes \rho_x$ with $a(\gamma_j) = 1$ for all $j$. Let $H_j$ be integral polynomials, $t \neq 0$, $A, \delta_0 \in \mathbb{T}$ and $n_0 \in \mathbb{Z}_\ell$. Suppose that at each $w_j$ the Hecke polynomial of every system of base level with $(A\delta_0)(x) \neq 0$ has a root chain of length $t$ at $a(\varphi_j)^{-1}$ with cofactor dividing $H_j$. Suppose that
$$2\, n!\, (n_0 c^2)^{\#J + 1} \mid \ell^\nu.$$
Let $\mathcal{D} \in \mathbb{T}[\alpha]$ satisfy $(\delta_0 - n_0) \mathcal{D} \in \mathfrak{a}$, and write $\mathcal{D}_S$ for its coefficient at $\alpha_S$. Let $l$ be a form of base level with $d\, l$ integral for some $d \in \mathbb{N}$, and let $y$ be a form with $A \delta_0 l = n_0 A y$, $\delta_0 y = n_0 y$, and $\mathcal{D}_S y = 0$ for $S \neq J$. Then
$$d\, c\, A^{\#J + 1} \mathcal{D}_J\, y$$
is integral.

Lean: `New.Patching.BaseLevel.smul_top_coeff_mem_ellIntegralForms` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean).

In the application, $\mathcal{D}$ is Ribet's element, $A$ is the indicator function of the systems congruent to a fixed one, so $A^{\#J+1} = A$, and $y$ is the projection of $l$ to the lifts.

*Proof.* Put $i = \#J$, $n_1 = n_0 c^2$ and $\delta = c^2 A \delta_0$. Write $\ell^\nu = 2 n!\, n_1^{i+1} \mu'$. The ring of integral operators has no torsion, so the next chapter gives a reduction $\sigma$ modulo $\ell^\nu/(2 n!)$ whose kernel lies in $n_1^{i+1}\mu'$ times the integral operators (`New.Patching.exists_isReductionMod`). Take $\mathcal{N}$ and $Y$ from [the deformed norm](/decl/New.Patching.BaseLevel.exists_deformed_norm_family/) with $\delta' = A\delta_0$. Let
$$\mathcal{G} = \sum_S \mathcal{N}_{J \setminus S}\, \mathcal{D}_S, \qquad \mathcal{G}' = \sum_S Y_{J \setminus S}\, \mathrm{Nm}\, \delta\, \mathcal{D}_S.$$

First, $n_1^{i+1} A^{i+1} \mathcal{G} \equiv \delta^{i+1} \mathcal{G}$. Indeed $\delta^{i+1} - n_1^{i+1} A^{i+1}$ is a multiple of $\delta_0 - n_0$, so it multiplies $\mathcal{D}$ into $\mathfrak{a}$, and the deformed norm kills the top coefficient of every element of $\mathfrak{a}$. Second, $\delta^{i+1} \mathcal{G} \equiv \mathcal{G}'$. Write $\delta^{i+1} = \delta^i \cdot \delta$, move $\delta^i$ next to $\mathcal{N}_{J \setminus S}$, and use $\delta^i \mathcal{N}_{J \setminus S} \equiv Y_{J \setminus S} \mathrm{Nm}$.

So $n_1^{i+1} A^{i+1} \mathcal{G} - \mathcal{G}' = n_1^{i+1} \mu' W$ for an integral operator $W$. Let $u = \Psi(d\, l)$, which is integral with $\mathrm{Nm}\, u = d c\, l$. By the lemma on the top term, $\mathcal{G}' u = n_1^{i+1}\, d c\, A^{i+1} \mathcal{D}_J y$. Divide by $n_1^{i+1}$, which is not $0$ since it divides $\ell^\nu$. This gives
$$d c\, A^{i+1} \mathcal{D}_J\, y = (A^{i+1} \mathcal{G} - \mu' W)\, u,$$
an integral operator applied to an integral form. $\square$

The proof never divides by the order of an even class. The only loss is the factor $c$ on the left and the factor $2 n! (n_0 c^2)^{\#J+1}$ that $\ell^\nu$ must absorb. The triangle of primes fixes $\#J$ independently of $\nu$, so for $n_0 \neq 0$ this condition holds once $\nu$ is large.

### Ribet's element over the Hecke algebra

[Ribet elements](/chapter/ribet-elements/) defines trace ideals and common Ribet elements for a family $\delta_i$ of functions on systems, a set $\mathcal{X}$ of systems on which the $\delta_i$ vanish, and a system $\pi \in \mathcal{X}$. A common Ribet element multiplies each $\delta_i$ into the trace ideal, has no term below $\alpha_J$ on $\mathcal{X}$, and has a coefficient $r$ of $\alpha_J$ at $\pi$. Write $v$ for the $\ell$-adic valuation.

**Lemma.** Let $N_x = a \otimes \rho_x$, let $m \in \overline{\mathbb{Q}}_\ell$, and suppose that every trace ideal of the $N_x$ has a common Ribet element for the $\delta_i$ at $\pi$ with $v(m r) \leq b$. Then there are $\beta_i \in \mathbb{T}$ with values $\delta_i$, and one $f \in \mathbb{T}[\alpha]$ with these properties: $\beta_i f \in \mathfrak{a}$ for every $i$; the $\delta_i$ and the coefficients of $f$ below $\alpha_J$ vanish on $\mathcal{X}$; and the coefficient of $\alpha_J$ in $f$ has a value $r$ at $\pi$ with $v(m r) \leq b$.

Lean: `New.Patching.BaseLevel.exists_heckeAlgebra_ribetElement` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean).

*Proof.* Read a polynomial over $\mathbb{T}$ as a family of polynomials, one for each system. The image of $\mathfrak{a}$ is a trace ideal over the image of $\mathbb{T}[\alpha]$. It contains the variables, the coefficients of the characteristic polynomials, and the two kinds of generators. Its common Ribet element is the image of some $f$. Each $\delta_i$ is the constant term of an element of the image, so it is the function of some $\beta_i \in \mathbb{T}$. $\square$

**Lemma.** Let $R$ be a commutative ring, $I$ an ideal of $R[\alpha]$, and $f \in R[\alpha]$ with $\beta_i f \in I$ for all $i$. Then $\bigl(\prod_k (v_k - \beta_{g(k)}) - \prod_k v_k\bigr) f \in I$ for all finite families $v_k$ and indices $g(k)$.

Lean: `New.Patching.BaseLevel.C_prod_sub_prod_mul_mem` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean).

*Proof.* The elements of $R$ that multiply $f$ into $I$ form an ideal. Modulo it every $\beta_i$ is $0$. $\square$

### The form of the result that is used

**Theorem (Clearing the denominator).** Let the places $w_j$ be off the base level, let $N_x = a \otimes \rho_x$ with $a(\gamma_j) = 1$ for all $j$, and let the characteristic polynomials of all $N_x(g)$ be integral. Let $\delta_i$ be functions on systems, choose finitely many $\delta_{s(k)}$ and $\lambda_k \in \mathbb{Z}_\ell$, and put
$$\delta_0 = \prod_k (\lambda_k - \delta_{s(k)}), \qquad n_0 = \prod_k \lambda_k.$$
Suppose these hold.

1. At each $w_j$ the Hecke polynomial of every system $x$ of base level that is congruent to $\pi$ and has $\delta_0(x) \neq 0$ has a root chain of length $t \neq 0$ at $a(\varphi_j)^{-1}$ with cofactor dividing $H_j$.
2. $2 n!\, (n_0 c^2)^{\#J+1}$ divides $\ell^\nu$.
3. For a fixed $m$, every trace ideal of the $N_x$ has a common Ribet element for the $\delta_i$ at $\pi$ with $v(m r) \leq b$.

Then there is a function $s$ on systems with $v(m\, s(\pi)) \leq b$ with this property. Let $l$ and $y$ be forms of base level and $d \in \mathbb{N}$, with $d\, l$ integral, $y$ supported on $\mathcal{X}$, and $y$ equal to $l$ at the systems where $\delta_0 \neq 0$. Then $d\, c\, s\, y$ is integral.

Lean: `New.Patching.BaseLevel.exists_diagOp_mem_ellIntegralForms` (New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean).

*Proof.* The indicator function $A$ of the systems congruent to $\pi$ lies in $\mathbb{T}$, by a result of the next chapter. Take $\beta_i$ and $f$ from the last lemma but one, and let $\delta_0 = \prod_k (\lambda_k - \beta_{s(k)})$ in $\mathbb{T}$. The last lemma gives $(\delta_0 - n_0) f \in \mathfrak{a}$. Put $s = A^{\#J + 1} f_J$. At $\pi$, $A = 1$, so $v(m\, s(\pi)) \leq b$. Every $\delta_i$ vanishes on $\mathcal{X}$, so $\delta_0 y = n_0 y$. Since $y$ agrees with $l$ where $\delta_0 \neq 0$, $A \delta_0 l = A \delta_0 y = n_0 A y$. The coefficients below $\alpha_J$ vanish on $\mathcal{X}$, so they kill $y$. A system with $(A\delta_0)(x) \neq 0$ is congruent to $\pi$ and has $\delta_0(x) \neq 0$, so hypothesis 1 gives the root chains. The theorem on the top coefficient applies. $\square$

The source claims this theorem, and Lean accepts it if the reported checks hold.
