---
title: The height bound
lean:
  - New/OneLift/LiftVolumeHeight.lean
  - New/Determinant/Twist/LongForms.lean
decls:
  - New.Data.IsComparisonOperator.exists_normDet_sq_mul_det_eq
  - New.Data.IsComparisonOperator.norm_padic_det_liftCompression_le
  - New.Data.IsComparisonOperator.norm_map_det_liftCompression_le
  - New.Data.mFoldTwist_one_pow
  - New.Data.heightLe_liftDeterminant_ratio
  - New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The height bound

This section proves the theorem of Section 1. It has three steps. The first step is an identity: for a comparison operator $U$, the product $Z_j(\vartheta)\,\Delta(\vartheta)$ is $C\rho_j(\vartheta)^d$ with $C \neq 0$ independent of $\vartheta$. The second step bounds $\Delta(1)$ at every automorphism of $\mathbb{C}$ and $\Delta(\vartheta)$ at every isomorphism $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ with $\ell$ prime to the modulus of $\vartheta$. The third step puts the bounds into the calculus of heights and adds the height of $\rho^{-d}$. At the end we prove the corollary that the proof of Theorem C uses.

Throughout, $U$ is a comparison operator for $j$ (Section 3), $L_\vartheta$ is the space of lifts, $\mathrm{pr}_\vartheta$ is the orthogonal projection onto it, and $\Delta(\vartheta)$ is the determinant of the compression $\mathrm{pr}_\vartheta U_\vartheta|_{L_\vartheta}$ (Section 6). Put $A = f m b\log^2 b$, and let $d$ be the dimension of the good forms on $W_j$.

### Inputs

- *Heights.* A family $(z_\iota)$ has height at most $c$ if there are $H \neq 0$, a real $\alpha$ and reals $e(\ell)$ with $|\sigma(H)| \leq e^\alpha$ for every $\sigma$, $|\iota(H z_\iota)|_\ell \leq \exp(e(\ell))$ for every $\iota$ with prime $\ell$, and $\alpha + \sum_{\ell\in T}e(\ell) \leq c$ for every finite set $T$ of primes. Heights add under products, multiply by $n$ under $n$-th powers, and grow with $c$ (`New.HeightLe.of_mul_le`, `.mul`, `.pow`, `.mono`, [heights over the isomorphisms](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers)).
- *Regular families.* For a regular family $\theta$ and $1 \leq j \leq m$, there is a denominator bound $\beta \colon \mathbb{N} \to \mathbb{R}$ with $\sum_{\ell\in T}\beta(\ell) \leq \mathrm{denominatorBudget}$ for every finite $T$, and with `ClearsProjection` $\iota$ $(\theta(\iota)^j)$ $j$ $\beta(\ell)$ for every $\iota$. Also $\ell$ is prime to the modulus of $\theta(\iota)$ (`New.Data.IsRegularFamily`, [regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists)).
- *Clearing the projection.* `ClearsProjection` $\iota$ $\vartheta$ $j$ $\beta$ asks for an operator $\Lambda$ on $L_\vartheta$ with $|\iota(\det\Lambda)|_\ell \geq \exp(-\dim L_\vartheta\cdot r\beta)$, such that $\Lambda(\mathrm{pr}_\vartheta y)$ is integral at $\iota$ for every form $y$ integral at $\iota$ and orthogonal to the false lifts (`New.Data.ClearsProjection`, same chapter).
- *Hecke values.* For a regular family, $\iota \mapsto \rho_j(\theta(\iota)^j)^{-1}$ has height at most $10 m x_1 + k(6\,\mathrm{denominatorBudget} - \mathrm{directionAmount})$ (`New.Data.heightLe_inv_heckeValueProd_div`, [Hecke values of character lifts](/chapter/hecke-values/)).
- *Regular families exist* (`New.exists_isRegularFamily`, [the four inputs](/chapter/theorem-c-plan/#the-four-inputs)).
- *Dimensions.* $d$ is `D.targetDim` (`New.Data.targetDim_eq_finrank_goodForms_spaceW`, [good forms and the factorization](/chapter/chain-determinant/#good-forms-and-the-factorization)).

### The identity

**Lemma (The cancellation identity).** There is $C \in \mathbb{C}$, $C \neq 0$, such that for every twist $\vartheta$,

$$Z_j(\vartheta)\,\Delta(\vartheta) = |\det|^2(\Theta_\vartheta)\cdot\det\big(\mathrm{pr}_\vartheta U_\vartheta|_{L_\vartheta}\big) = C\,\rho_j(\vartheta)^d .$$

Lean: `New.Data.IsComparisonOperator.exists_normDet_sq_mul_det_eq` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Take $U^\circ$ from property 2. It is positive definite, so its kernel is $0$: if $U^\circ y = 0$ and $y \neq 0$, then $\langle y, U^\circ y\rangle = 0$, which is not positive. So $C = \det U^\circ \neq 0$. Property 2 says that $\langle y', \Theta_\vartheta^* U_\vartheta\Theta_\vartheta y\rangle = \langle\Theta_\vartheta y', U_\vartheta\Theta_\vartheta y\rangle = \rho_j(\vartheta)\langle y', U^\circ y\rangle$ for all $y'$. So $\Theta_\vartheta^*U_\vartheta\Theta_\vartheta = \rho_j(\vartheta)\,U^\circ$ as operators on the good forms. The map $\Theta_\vartheta$ is injective. The lemma on the determinant of a compression (Section 2) gives

$$|\det|^2(\Theta_\vartheta)\cdot\det\big(\mathrm{pr}_\vartheta U_\vartheta|_{L_\vartheta}\big) = \det\big(\Theta_\vartheta^*U_\vartheta\Theta_\vartheta\big) = \det\big(\rho_j(\vartheta)U^\circ\big) = \rho_j(\vartheta)^d\,C,$$

since the good forms have dimension $d$. $\square$

### The bound at an isomorphism with the l-adic numbers

**Lemma (The l-adic bound).** Let $\vartheta$ be a twist, $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ with $\ell$ prime to the modulus of $\vartheta$, and $\beta \in \mathbb{R}$ with `ClearsProjection` $\iota$ $\vartheta$ $j$ $\beta$. Then

$$|\iota(\Delta(\vartheta))|_\ell \leq \exp(d\,r\,\beta).$$

Lean: `New.Data.IsComparisonOperator.norm_padic_det_liftCompression_le` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Take $\Lambda$ from `ClearsProjection`, and let $P = \Lambda\,\mathrm{pr}_\vartheta U_\vartheta|_{L_\vartheta}$. We show that every eigenvalue $\alpha$ of $P$ has $|\iota(\alpha)|_\ell \leq 1$. Let $z \in L_\vartheta$ be an eigenvector, so $z \neq 0$ and $Pz = \alpha z$. Let $\iota_p$ be the place of $\mathbb{C}$ given by $\iota$ followed by $\overline{\mathbb{Q}}_\ell \subseteq \mathbb{C}_\ell$. By the lemma on scaling (Section 2), there is $c \neq 0$ such that $cz$ is integral at $\iota_p$ and such that $\mu c z$ integral implies $|\iota_p(\mu)| \leq 1$. Property 4 makes $U_\vartheta(cz)$ integral, since $\ell$ is prime to the modulus. Property 3 makes it orthogonal to the false lifts. So `ClearsProjection` makes $\Lambda\,\mathrm{pr}_\vartheta U_\vartheta(cz)$ integral. By linearity this vector is $c\,Pz = \alpha\,c z$. So $|\iota_p(\alpha)| \leq 1$. The inclusion $\overline{\mathbb{Q}}_\ell \subseteq \mathbb{C}_\ell$ keeps the norm, so $|\iota(\alpha)|_\ell \leq 1$.

The lemma on a determinant and its eigenvalues (Section 2), with the bound $1$ for each eigenvalue, gives $|\iota(\det P)|_\ell \leq 1$. Now $\det P = \det\Lambda\cdot\Delta(\vartheta)$, and $|\iota(\det\Lambda)|_\ell \geq \exp(-\dim L_\vartheta\cdot r\beta) = \exp(-d r\beta)$ by the dimension lemma of Section 6. So

$$\exp(-d r\beta)\,|\iota(\Delta(\vartheta))|_\ell \leq |\iota(\det\Lambda)|_\ell\,|\iota(\Delta(\vartheta))|_\ell = |\iota(\det P)|_\ell \leq 1,$$

and the claim follows. $\square$

**Remark (Formalization).** The real number $\beta$ is not asked to be nonnegative. If $\beta < 0$, `ClearsProjection` asks $|\iota(\det\Lambda)|_\ell \geq \exp(d r|\beta|) > 1$, and the lemma gives a bound below $1$. The proof does not change. The source of $\beta$ is Volume 12 ([the denominator bound](/chapter/denominator-bound/)); this chapter uses only the two fields `sum_le` and `clearsProjection`.

### The bound at an automorphism

**Lemma (The archimedean bound).** For every $\sigma \in \mathrm{Aut}(\mathbb{C})$,

$$|\sigma(\Delta(1))| \leq \exp(d\cdot 3A).$$

Lean: `New.Data.IsComparisonOperator.norm_map_det_liftCompression_le` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* By the lemma on a determinant and its eigenvalues, with $\dim L_1 = d$, it is enough that each eigenvalue $\alpha$ of $\mathrm{pr}_1U_1|_{L_1}$ has $|\sigma(\alpha)| \leq e^{3A}$. Let $z \in L_1$, $z \neq 0$, with $\mathrm{pr}_1U_1 z = \alpha z$. Property 3 says $U_1 z$ is orthogonal to the false lifts. The projection theorem of Section 6 and property 5 give

$$|\sigma(\alpha)|^2\,\|z\|_\sigma^2 = \|\alpha z\|_\sigma^2 = \|\mathrm{pr}_1U_1 z\|_\sigma^2 \leq \|U_1 z\|_\sigma^2 \leq e^{6A}\,\|z\|_\sigma^2 .$$

Here the first equality is the scaling rule $\|\lambda\varphi\|_\sigma^2 = |\sigma(\lambda)|^2\|\varphi\|_\sigma^2$ of Section 2. Since $\|z\|_\sigma^2 > 0$, we get $|\sigma(\alpha)|^2 \leq e^{6A}$, so $|\sigma(\alpha)| \leq e^{3A}$. $\square$

Only $\Delta(1)$ is bounded at the automorphisms. The twist $\vartheta = 1$ is the one for which property 5 holds. The other determinant $\Delta(\xi^j)$ is bounded only at the isomorphisms $\iota$. This is enough, because heights put one fixed number $H = \Delta(1)$ in the denominator and bound $H$ at infinity and the family $H z_\iota$ at $\iota$.

### The trivial twist

**Lemma (Power of the trivial twist).** For every $j$, the $j$-th power of the trivial $m$-fold twist is the trivial tame character.

Lean: `New.Data.mFoldTwist_one_pow` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The power of an $m$-fold twist is formed componentwise, and $1^j = 1$ in each component. $\square$

So $Z_j(1)$ is $|\det|^2(\Theta_1)$, and the cancellation identity applies to it with $\vartheta = 1$.

### The main theorem

**Theorem (The height of one lift determinant).** Let $\theta$ be a regular family and $1 \leq j \leq m$. Then $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most $d\,k\,(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$.

Lean: `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Write $B = \mathrm{denominatorBudget}$, $\xi_\iota = \theta(\iota)$, and $\vartheta_\iota = \xi_\iota^j$. Take $\beta$ from the regular family. Replace `D.targetDim` by $d$. Let $U$ be the comparison operator of Section 5, and take $C$ from the cancellation identity.

*Step 1: $\Delta$ does not vanish.* By the identity, $Z_j(\vartheta)\Delta(\vartheta) = C\rho_j(\vartheta)^d$. The right side is nonzero by $C \neq 0$ and property 1. So $\Delta(\vartheta) \neq 0$ for every $\vartheta$.

*Step 2: the height of $\Delta(\vartheta_\iota)/\Delta(1)$.* Apply the criterion for heights with $H = \Delta(1) \neq 0$, $\alpha = 3dA$ and $e(\ell) = d r\beta(\ell)$. The archimedean bound gives $|\sigma(H)| \leq e^{\alpha}$. The product $H\cdot\Delta(\vartheta_\iota)/\Delta(1)$ is $\Delta(\vartheta_\iota)$, and the $\ell$-adic bound gives $|\iota(\Delta(\vartheta_\iota))|_\ell \leq \exp(d r\beta(\ell))$; it applies because $\ell$ is prime to the modulus of $\xi_\iota$, and so of $\vartheta_\iota$, and `ClearsProjection` holds. For a finite set $T$ of primes, $\alpha + \sum_T d r\beta(\ell) \leq 3dA + d r B$. So the height is at most $d(3A + rB)$.

*Step 3: the Hecke factor.* The family $\rho_j(\vartheta_\iota)^{-d}$ has height at most $d\,(10 m x_1 + k(6B - \mathrm{dir}))$, by the input on Hecke values and the rule for powers. Here $\mathrm{dir} = \mathrm{directionAmount}$. The product of the two families has height at most

$$d\,\big(3A + rB + 10 m x_1 + k(6B - \mathrm{dir})\big).$$

*Step 4: the size inequality.* We show

$$3A + rB + 10 m x_1 + 6kB \leq k B\log b .$$

Then the bound of step 3 is at most $d\,k(B\log b - \mathrm{dir})$. The right side is $kB\log b = f a\log^4 b/m$, and $a = x b$. Divide each term on the left by it.

- $3A/(kB\log b) = 3 f m b\log^2 b\cdot m/(f x b\log^4 b) = 3m^2/(x\log^2 b) \leq 12/\log^2 b$, because $m^2 \leq 4x$.
- $rB/(kB\log b) = r/(k\log b) \leq 2/\log b$, because $r \leq 2k$.
- $6kB/(kB\log b) = 6/\log b$.
- $10 m x_1/(kB\log b) = 10 m^2 x_1/(f x b\log^4 b) \leq 10 m^2/(x\sqrt b) \leq 40/\sqrt b$, because $x_1 \leq \sqrt b$ and $f \geq 1$.

The sum is at most $1$, since $\log b \geq 10^{6}$. The bounds $m^2 \leq 4x$, $r \leq 2k$, $x_1 \leq \sqrt b$ and the size of $\log b$ are in [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes). In the source, `D.le_of_hasLogBound` proves the inequality at once from the logarithmic bounds of the data. Then the rule `mono` gives the bound of the theorem for the product family.

*Step 5: the product is the ratio.* Fix $\iota$ and write $\rho = \rho_j(\vartheta_\iota)$. By definition $Z_j(\xi_\iota) = |\det|^2(\Theta_{\vartheta_\iota})$, so the identity gives $Z_j(\xi_\iota)\Delta(\vartheta_\iota) = C\rho^d$. By the lemma on the trivial twist, $Z_j(1) = |\det|^2(\Theta_1)$, and the identity at $\vartheta = 1$ gives $Z_j(1)\Delta(1) = C\rho_j(1)^d = C$. Here $\rho_j(1) = \mathrm{HV}_j(1)/\mathrm{HV}_j(1) = 1$, because $\mathrm{HV}_j(1) \neq 0$. Divide:

$$\frac{Z_j(1)}{Z_j(\xi_\iota)} = \frac{C/\Delta(1)}{C\rho^d/\Delta(\vartheta_\iota)} = \frac{\Delta(\vartheta_\iota)}{\Delta(1)}\cdot(\rho^{-1})^d .$$

This is the product family of step 3. $\square$

**Remark (Formalization).** In Lean, $x/0 = 0$. So $\rho_j(1) = 1$ needs $\mathrm{HV}_j(1) \neq 0$. The proof gets it from property 1 at $\vartheta = 1$: if $\mathrm{HV}_j(1) = 0$, then $\rho_j(1) = 0/0 = 0$, which property 1 excludes. So property 1, the field that answers F-072 of [the register of findings](/chapter/register-of-findings/), is used twice: for $\Delta \neq 0$ and for $\rho_j(1) = 1$. The quotient $Z_j(1)/Z_j(\xi_\iota)$ is also a division, but $Z_j(\xi_\iota) \neq 0$ follows from the identity and $\rho \neq 0$, so no junk value enters.

### The corollary for Theorem C

**Corollary (Single lifts at good twists).** There is a family $\theta$ with small ratios such that for every $1 \leq j \leq m$ the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most

$$d\,\Big(\frac{f a\log^4 b}{m} - k\cdot\mathrm{directionAmount}\Big).$$

Lean: `New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take a regular family $\theta$. It has small ratios, because a regular family is a family with small ratios and a denominator bound. Since $k > 0$ and $\mathrm{denominatorBudget} = f a\log^3 b/(mk)$,

$$k\cdot\log b\cdot\mathrm{denominatorBudget} = \frac{f a\log^4 b}{m} .$$

So the bound of the theorem, $d\,(k\log b\cdot\mathrm{denominatorBudget} - k\cdot\mathrm{directionAmount})$, is the bound of the corollary. $\square$

The file `New/Determinant/Twist/LongForms.lean` belongs to Volume 1 ([integral target forms](/chapter/integral-target-forms/)), where the corollary enters the volume of the integral target forms. We prove it here because its proof is two lines from the theorem.

### The size of the bound

The budget cancels the factors $k$ and $m$. Over the $m$ lifts of a chain, the cost of the denominators is $m\cdot d\,f a\log^4 b/m = d f a\log^4 b$. The term $-d\,k\cdot\mathrm{directionAmount}$ is negative and large: it comes from the Hecke values, whose ratio is large and has no denominator. The proof of Theorem C turns it into the main amount ([the proof of Theorem C](/chapter/proof-of-theorem-c/)). The archimedean term $3dA$ and the terms $d\,rB$ and $6dkB$ are smaller than $d f a\log^4 b/m$ by factors $\log b$ or more, and the size inequality absorbs them.
