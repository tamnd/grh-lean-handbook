---
title: Densities as integrals over two frames
lean:
  - New/Spanning/Frames/Correlations.lean
  - New/Spanning/Frames/Densities.lean
decls:
  - New.Floors.PlaceData.pivotL1Norm
  - New.Floors.PlaceData.weightedSquare
  - New.Floors.PlaceData.weightedSquareSum
  - New.Floors.PlaceData.weightedSquareIntegral
  - New.Floors.PlaceData.invDepthWeight
  - New.Floors.PlaceData.headDensity
  - New.Floors.Place.IsBessel
  - New.Floors.PlaceData.IsCut
  - New.Floors.PlaceData.pairingNormSq
  - New.Floors.PlaceData.partialCorrelationProduct
  - New.Floors.PlaceData.formIntegrand
  - New.Floors.PlaceData.floorForm
  - New.Floors.PlaceData.formIntegrandL1Norm
  - New.Floors.PlaceData.formMajorant
  - New.Floors.Gauge.weightedSquareProduct
  - New.Floors.PlaceData.IsActive
  - New.Floors.PlaceData.HasDeepVector
  - New.Floors.PlaceData.enorm_floorForm_le
  - New.Floors.PlaceData.IsCut.formIntegrandL1Norm_le_formMajorant
  - New.Floors.Gauge.inner_besselOrbitalIntegral
  - New.Floors.Gauge.isPairingKernel_frameCorrelation
  - New.Floors.PlaceData.floorForm_zero_eq_integral
  - New.Floors.PlaceData.integrable_and_integral_succ_eq_mul_floorForm
  - New.Floors.Gauge.integral_weight_mul_floorForm_succ
  - New.Floors.Gauge.integral_psi_mul_floorForm_succ
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Densities as integrals over two frames

A local density at one place is an inner product of two orbital integrals of a Bessel function. This section writes it as an integral over a position and two frames, and then as a form $\mathcal{I}_j$ of floor $j$ that can be lowered one floor at a time. Each step down puts a weight on the bottom floor, and the integral over the head entry turns the weight into a character of a Gram entry.

### Cut Bessel functions

Let $I$ be a finite set and $W : \mathsf{G} \to \mathbb{C}^I$.

**Definition (Bessel function).** $W$ is a *Bessel function* of frequency $\eta \in A^\times$ if it is bounded and measurable and $W(ux) = \psi(\eta\,\sigma(u))W(x)$ for $u \in \mathsf{U}$, where $\sigma(u)$ is the sum of the superdiagonal entries of the frame block.

Lean: `New.Floors.Place.IsBessel` (New/Spanning/Frames/Densities.lean).

**Definition (Cut).** $W$ is *cut* for the place data if it is a Bessel function of frequency $M^{-1}$ and $W(x) \neq 0$ only if $ux \in K$ for some $u \in \mathsf{U}$.

Lean: `New.Floors.PlaceData.IsCut` (New/Spanning/Frames/Densities.lean).

A cut function vanishes off the points that are near at every level (`New.Floors.PlaceData.IsCut.isNear_of_ne_zero`), because $\mathsf{U} \subseteq R^{(j)}$ for every $j$. The kernel $k_d(x, y) = \langle W(x), W(dy)\rangle$ (`frameCorrelation W d`) is then a pairing kernel.

**Lemma (Correlations are pairing kernels).** If $\Gamma$ is a gauge and $W$ is cut, then for every $j$ and all $p, q$ the kernel $k_w$ with $w = w_q^{-1}w_p$ (`weylRatio j p q`) satisfies the five rules of a pairing kernel at floor $j$ with the twist $w$.

Lean: `New.Floors.Gauge.isPairingKernel_frameCorrelation` (New/Spanning/Frames/Densities.lean).

*Proof.* Measurability comes from $W$. For the rule on characters, move the unipotent elements to the left by conjugation. They stay in $\mathsf{U}$, where $W$ transforms by $\psi(\sigma(\cdot)/M)$; conjugation by an element of a floor keeps the entries that $\sigma$ sums, and $w$ is diagonal. The rule on mass holds because the kernel is bounded and lives on near points, whose mass on each floor is finite by the lemma on the mass of the near points. If $g$ is not near, then $W(\sigma g) = 0$ for every $\sigma$ in the floor, which is the last rule. $\square$

**Theorem (Two orbital integrals).** Let $\Gamma$ be a gauge, $\mu$ a Haar measure, $W$ continuous and cut, $p, q$ heads of length $\varrho$, and $x \in G^{(\varrho)}$. Write $J(\gamma) = \int W(y) \otimes \overline{W(\gamma^{-1}y)}\,d\mu(y)$. Then

$$\langle J(w_px), J(w_qx)\rangle = \iint\langle W(y), W(y')\rangle\,\overline{\langle W((w_px)^{-1}y), W((w_qx)^{-1}y')\rangle}\,d\mu(y)\,d\mu(y').$$

Lean: `New.Floors.Gauge.inner_besselOrbitalIntegral` (New/Spanning/Frames/Densities.lean).

*Proof.* Expand the inner product of the matrices $J$ entry by entry and use Fubini. For a head $r$, each entry of the integrand is continuous and lives on the compact set of the points of size $60n^2$, so it is integrable. $\square$

The left side is the density of the few-translates chapter. The right side is an integral over two frames, $y$ and $y'$, and this is the form that the rest of the chapter bounds.

### The forms of the floors

**Definition (Head density).** For $j$ and sequences of units $p, q$,

$$\kappa_j(p, q) = \prod_{a < j}|p_aq_a|^{d_a/2},\qquad d_a = k + 1 + 2(\varrho - a - 1).$$

Lean: `New.Floors.PlaceData.headDensity` (New/Spanning/Frames/Densities.lean).

**Definition (Correlation product).** At a position $x$, for $d, w, g \in \mathsf{G}$, the *correlation product* is

$$\Pi_j(x; d, w, g) = c_j(k_1)(g, gx)\cdot\overline{c_j(k_d)(w^{-1}g, w^{-1}gx)},$$

where $c_j$ is the correlation from floor $j$ on.

Lean: `New.Floors.PlaceData.partialCorrelationProduct` (New/Spanning/Frames/Densities.lean).

**Definition (Form integrand and form).** For a weight $\omega : \mathsf{G} \to \mathbb{C}$, the *form integrand* at $x$ and $g$ is

$$\Phi_j(x, \omega; g) = \iint\omega(\sigma\tau^{-1})\,\Pi_{j+1}(x; w, \sigma w_p\tau^{-1}, \sigma g)\,d\theta_j(\tau)\,d\theta_j(\sigma),\qquad w = w_q^{-1}w_p.$$

The *form* of floor $j$ is

$$\mathcal{I}_j(p, q; \omega) = \kappa_j(p, q)\int\Phi_j(x, \omega; g)\,d(\mathsf{M} \times \mathsf{m}_j)(x, g),$$

with $\mathsf{M}$ the group measure and $\mathsf{m}_j = \mu_{0,j}$ the measure of the floors below $j$.

Lean: `New.Floors.PlaceData.formIntegrand`, `New.Floors.PlaceData.floorForm` (New/Spanning/Frames/Densities.lean).

For the weight $1$ the double integral collapses: $\Phi_j(x, 1; g) = \Pi_j(x; w, w_p, g)$ (`New.Floors.PlaceData.partialCorrelationProduct_eq`). So $\mathcal{I}_j$ is the integral of a product of two correlations from floor $j$ on, one plain and one twisted.

**Definition (L1 norm and majorant).** At the position $x$,

$$\mathsf{F}_j(x; \omega) = \int|\Phi_j(x, \omega; g)|\,d\mathsf{m}_j(g),$$

$$\mathsf{F}^*_j(x) = \int P_j(k_1)(g, gx)\cdot P_j(k_w)(w_p^{-1}g, w_p^{-1}gx)\,d\mathsf{m}_j(g),$$

where the *pivot norm* $P_j(k)(g, y) = \int|c_{j+1}(k)(\sigma g, \sigma y)|\,d\theta_j(\sigma)$ is the integral over floor $j$ of the modulus of a correlation.

Lean: `New.Floors.PlaceData.formIntegrandL1Norm`, `New.Floors.PlaceData.formMajorant` (New/Spanning/Frames/Densities.lean), `New.Floors.PlaceData.pivotL1Norm` (New/Spanning/Frames/Correlations.lean).

**Lemma (The form is bounded by its L1 norm).** For every weight $\omega$,

$$|\mathcal{I}_j(p, q; \omega)| \leq \kappa_j(p, q)\int\mathsf{F}_j(x; \omega)\,d\mathsf{M}(x).$$

Lean: `New.Floors.PlaceData.enorm_floorForm_le` (New/Spanning/Frames/Densities.lean).

*Proof.* The norm of a Bochner integral is at most the integral of the norm, and the product measure splits by Tonelli. If the integrand is not integrable, the left side is $0$. $\square$

**Lemma (The majorant).** If $W$ is cut and $|\omega| \leq 1$, then $\mathsf{F}_j(x; \omega) \leq \mathsf{F}^*_j(x)$ for all $j, p, q, x$.

Lean: `New.Floors.PlaceData.IsCut.formIntegrandL1Norm_le_formMajorant` (New/Spanning/Frames/Densities.lean).

*Proof.* Bound $|\omega|$ by $1$ and the modulus of the double integral by the double integral of the modulus. Then the integrand splits into a function of $\sigma$ times a function of $\tau$, after the change of variables $\tau \mapsto \tau w_p^{-1}$ that $w_p$ normalizing $G^{(j)}$ allows. $\square$

So the forms are controlled by the majorant, which is free of $\omega$. The rest of the chapter bounds $\int\mathsf{F}^*_j\,d\mathsf{M}$.

### Squares, activity and deep vectors

The bounds compare the majorant with squares.

**Definition (Weighted squares).** At the position $x$, the *weighted square* of floor $j$ is $a_j(g) = \wp_j(g, gx)\,|c_{j+1}(k)(g, gx)|^2$. The *sum from floor $j$ on* is $b_j(g) = \int(a_j + b_{j+1})(\sigma g)\,d\theta_j(\sigma)$ for $j < n$, and $b_j = 0$ for $j \geq n$. The *second moment* is $\mathsf{S}_j(k, x) = \int b_j\,d\mu_{<j}$, for the convolution $\mu_{<j}$ of the floor measures below $j$ (`descConv floorMeasure 0 j`). The inverse weight $\wp_j^{-1}(z) = \mathbf{1}_{\text{near at}\ j}(z)\,\wp_j(z, zx)^{-1}$ is `invDepthWeight`.

Lean: `New.Floors.PlaceData.weightedSquare`, `New.Floors.PlaceData.weightedSquareSum`, `New.Floors.PlaceData.weightedSquareIntegral`, `New.Floors.PlaceData.invDepthWeight` (New/Spanning/Frames/Correlations.lean).

**Definition (Product of squares).** For a gauge $\Gamma$,

$$\mathsf{Q}_j(x) = \Bigl(\prod_{a < j}|p_a^{-1}|^{r_a + 1/2}\Bigr)^2\,\mathcal{F}_\Lambda^3\,\mathsf{S}_0(k_1, x)\,\mathsf{S}_j(k_w, x).$$

Lean: `New.Floors.Gauge.weightedSquareProduct` (New/Spanning/Frames/Densities.lean).

The source says that a number has *gain* $\varsigma$ at $x$ if its square is at most $\varsigma^2\mathsf{Q}_j(x)$. The head density is not part of $\mathsf{Q}_j$.

**Definition (Pairing norm).** The squared $L^2$ norm of the pairing is

$$\|W\|^2 = \iint|\langle W(x), W(y)\rangle|^2\,d\mu_{\geq 0}(x)\,d\mu_{\geq 0}(y),$$

where $\mu_{\geq 0}$ stands for the quotient $\mathsf{U}\backslash\mathsf{G}$.

Lean: `New.Floors.PlaceData.pairingNormSq` (New/Spanning/Frames/Densities.lean).

**Definition (Active points, deep vectors).** At the position $x$, a point $y$ is *active* for $p, q$ at level $j$ if $\langle W(y), W(yx)\rangle \neq 0$ and both $w_p^{-1}y$ and $w_q^{-1}yx$ are near at $j$. The position $x$ *has a deep vector* of depth $D$ if every active $y$ has some $a \geq j$ with $D \leq \delta_a(y, x)$.

Lean: `New.Floors.PlaceData.IsActive`, `New.Floors.PlaceData.HasDeepVector` (New/Spanning/Frames/Densities.lean).

By the lemma that bounded depths bound the position, a position far from $1$ has a deep vector. The shells of the last section ask for this as a field.

### The mass and the descent

**Theorem (The mass).** If $\Gamma$ is a gauge and $W$ is cut, then for all $p, q$,

$$\mathcal{I}_0(p, q; 1) = \int|c_0(k_1)(1, z)|^2\,d\mathsf{M}(z).$$

Lean: `New.Floors.PlaceData.floorForm_zero_eq_integral` (New/Spanning/Frames/Densities.lean).

*Proof.* At $j = 0$ the head density is $1$, the Weyl elements are $1$, and $\mathsf{m}_0$ is a point mass. The form is the integral in $x$ of $c_0(k_1)(1, x)$ times its conjugate. $\square$

**Lemma (A descent with a decomposition).** Let $b < n$, let $\Gamma$ be a gauge, $W$ cut, and $\varphi : A \to \mathbb{C}$ measurable with $|\varphi| \leq 1$. Assume $\int\mathsf{F}^*_b\,d\mathsf{M} < \infty$. Let the floor measure decompose as $\theta_b = v^{-1}_*(\rho(c)\,dc) * \zeta$, with $v$ and $\rho$ measurable, $\rho$ finite almost everywhere, and $\zeta$ an s-finite measure carried by $R^{(b+1)} \cap G^{(b)}$. Let $\Psi(c)$ be, for almost every $c$, the product of $t$, $\kappa_b(p, q)\rho(c)$, $\varphi(Z_{b,b}(v(c)))$ and the integral of $\Pi_{b+1}(z; w, w_pv(c), g)$ over $(z, g)$ for $\mathsf{M} \times ((\zeta * \theta_b) * \mathsf{m}_b)$. Then $\Psi$ is integrable, and

$$\int\Psi(c)\,dc = t\cdot\mathcal{I}_b(p, q; \varphi\circ Z_{b,b}),$$

where $Z_{b,b}(x) = h(f_b, xf_b)$ is a diagonal entry of the frame Gram matrix.

Lean: `New.Floors.PlaceData.integrable_and_integral_succ_eq_mul_floorForm` (New/Spanning/Frames/Densities.lean).

*Proof.* The source claims that the substitution $\tau = v(c)^{-1}n\sigma$, $g' = n\sigma g$, with $n$ under $\zeta$, gives the integrand on floor $b + 1$ and the integrand of $\Phi_b$ the same image measure. The entry $Z_{b,b}$ does not change under left or right multiplication by $R^{(b+1)} \cap G^{(b)}$ (`New.Floors.frameGram_diag_mul`), so the weight passes through. The finite majorant integral gives integrability, and Fubini does the rest. $\square$

**Theorem (Descent).** Let $\Gamma$ be a gauge, $W$ cut, $a < \varrho$, $t \in \mathbb{C}$, $\varphi$ measurable with $|\varphi| \leq 1$, and $\int\mathsf{F}^*_a\,d\mathsf{M} < \infty$. Write $(p, c)$ for $p$ with the entry $a$ replaced by $c$ (by $1$ if $c$ is not a unit). Then

$$f(c) = \varphi(c)\cdot t\cdot\mathcal{I}_{a+1}((p, c), (q, c); 1)$$

is integrable on $A$, and

$$\int f(c)\,dc = t\cdot\mathcal{I}_a(p, q; \varphi\circ Z_{a,a}).$$

Lean: `New.Floors.Gauge.integral_weight_mul_floorForm_succ` (New/Spanning/Frames/Densities.lean).

*Proof.* Apply the lemma above to the big cell: $\theta_a$ is the law of $(\mathrm{w}_a(c))^{-1}n$, for $c$ with the density $\rho(c) = |c|^{d_a}$ and $n$ under the Heisenberg measure of floor $a$, where $\mathrm{w}_a(c)$ is the Weyl element of floor $a$ (`floorWeyl`). At a unit $c$, the Weyl element of floor $a + 1$ for $(p, c)$ is $w_p\,\mathrm{w}_a(c)$, the twist is unchanged, the Gram entry of $\mathrm{w}_a(c)$ is $c$, and the new factor of the head density is the density $\rho(c)$. $\square$

**Corollary (Descent for a character).** Under the same hypotheses with $\varphi(c) = \psi(\eta c)$, the function $c \mapsto \psi(\eta c)\,t\,\mathcal{I}_{a+1}((p, c), (q, c); 1)$ is integrable, with integral $t\,\mathcal{I}_a(p, q; \psi(\eta Z_{a,a}))$.

Lean: `New.Floors.Gauge.integral_psi_mul_floorForm_succ` (New/Spanning/Frames/Densities.lean).

*Proof.* The character is measurable and has modulus $1$. $\square$

Read from the top floor down, the descent is the frequency side of the Plancherel bound: the density is an integral over the head entries of forms with a character of a Gram entry as weight. The bounds of the next two sections hold for every weight of modulus at most $1$, so the character does not matter for them.

**Remark (Formalization).** Every descent assumes that $\int\mathsf{F}^*_a\,d\mathsf{M}$ is finite. This hypothesis is not proved in this file. The shell bounds of [the last section](/chapter/local-frames/#gains-and-shells) bound that integral by an explicit expression, which is finite when $\Lambda$ and the pairing norm are finite. So a user of the descent has to apply the shell bound first, at each place. The decomposition of $\theta_b$ in the lemma uses an s-finite measure $\zeta$ and a density $\rho$ that may be infinite on a null set. This is the measure version of the Bruhat cell of floor $b$, and it avoids a quotient. The form $\mathcal{I}_j$ is a Bochner integral, so it is $0$ when the integrand is not integrable; the finite majorant is what makes the identities say something.
