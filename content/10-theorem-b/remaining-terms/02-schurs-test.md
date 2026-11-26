---
title: Schur's test
lean:
  - New/Spanning/RemainingTerms/SchurTest.lean
  - New/Spanning/RemainingTerms/SchurOrbit.lean
decls:
  - New.Filling.boxCutoff
  - New.Filling.besselCutNormSq
  - New.Filling.schurWeight
  - New.Filling.schurIntegral
  - New.Filling.inCut_of_besselKernel_ne_zero
  - New.Filling.amplitudeMajorant_sq_le
  - New.Filling.lintegral_cutoff_mul_le_of_average
  - New.Filling.lintegral_boxCutoff_le_of_average
  - New.Filling.IsLatticeTranslate
  - New.Filling.tsum_orbit_le_of_isLatticeTranslate
  - New.Filling.tsum_schurWeight_fibre_le
  - New.Filling.kernelBound
  - New.Filling.exists_tsum_schurWeight_le
  - New.Filling.kernelBound_le
  - New.Filling.prod_kernelBound_le
  - New.Filling.tsum_schurIntegral_le
  - New.Filling.sq_tsum_amplitudeMajorant_doubleCoset_le
  - New.Filling.div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment
  - New.Filling.b_pow_div_M_sq_le
  - New.Filling.tsum_amplitudeMajorant_orbit_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Schur's test

This section bounds the sum of the absolute amplitudes over one orbit of terms. Fix classes $c, c'$, a reduction $s$ and a term $\gamma$ over $(c, s, c')$ of cell rank $j \geq 1$. Put $i = \min(\varrho, j)$. The orbit of $\gamma$ is the double coset $\mathsf{U}^0_c\,\gamma\,\mathsf{U}^0_{c'}$, where $\mathsf{U}^0_c$ (`classUnipotent₀`) is the group of rational unipotent elements of the class $c$ that fix the frame. The result is that the sum is at most $\nu\operatorname{orbitBound}(j, x)$ for the gauge $x$ of $\gamma$, if $\operatorname{termDiscNorm}(\gamma) \leq N^f\operatorname{minorNorm}(j, \gamma)$.

### The model case

Schur's test for a matrix says: if $K(x, y) \geq 0$ and there are positive weights $p, q$ with $\sum_y K(x, y)q(y) \leq Ap(x)$ and $\sum_x K(x, y)p(x) \leq Bq(y)$, then the operator norm of $K$ is at most $\sqrt{AB}$. The proof is Cauchy-Schwarz: $K = (Kq/p)^{1/2}(Kp/q)^{1/2}$. Here the "matrix" is the amplitude majorant of a term, an integral over $y$ of $\beta_c(y)\beta_{c'}(\gamma^{-1}y)\|W^\flat(y)\|\,\|W^\flat(\gamma^{-1}y)\|$. The weight is a power of the ratio of the volumes of two frames. The ratio is inverted when $y$ and $\gamma^{-1}y$ are exchanged, and this makes Cauchy-Schwarz exact on the diagonal.

### The weight

At one infinite place, $\operatorname{volumeRatio}(g, y)$ is the ratio of the volume of the projection of the frame of $g$ to the negative space $yV_-$ to that of the standard frame. It is positive, and $\operatorname{volumeRatio}(g^{-1}, g^{-1}y) = \operatorname{volumeRatio}(g, y)^{-1}$ ([Lemma](/decl/New.volumeRatio_inv/), in [the chapter on frame counts](/chapter/frame-counts/)).

**Definition (Boxed cutoff, Bessel norm, Schur weight, Schur integral).** Let $c, c'$ be classes, $\gamma$ rational, $i \in \mathbb{N}$ and $y$ a point at the infinite places.

1. The boxed cutoff $\beta^\square_c$ is the cutoff $\beta_c$ (`classCutoff`) times the indicator of the boxed points.
2. $\|W^\flat\|^2(y) = \prod_v \|W^\flat_v(y_v)\|^2$, the product of the squared norms of the local cut Bessel functions.
3. $\omega_{c', \gamma, i}(y) = \beta^\square_{c'}(\gamma^{-1}y)\prod_v \operatorname{volumeRatio}(\gamma_v, y_v)^{-(k+i)}$.
4. $I(c, c', \gamma, i) = \int \beta^\square_c(y)\,\|W^\flat\|^2(y)\,\omega_{c', \gamma, i}(y)\,dy$.

Lean: `New.Filling.boxCutoff`, `New.Filling.besselCutNormSq`, `New.Filling.schurWeight`, `New.Filling.schurIntegral` (New/Spanning/RemainingTerms/SchurTest.lean).

All four take values in $[0, \infty]$.

**Lemma (The kernel lives in the cut).** If the cut Bessel kernel $W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*$ is not zero, then at every infinite place $v$ both $y_v$ and $(\gamma^{-1}y)_v$ lie in the cut, that is, have Bessel length at most $b^{6n+2}$.

Lean: `New.Filling.inCut_of_besselKernel_ne_zero` (New/Spanning/RemainingTerms/SchurTest.lean).

*Proof.* The norm of the kernel is the product of the norms of the local factors at $y$ and at $\gamma^{-1}y$. If it is not zero, every local factor is not zero. A cut Bessel function vanishes outside the cut ([Definition](/decl/New.IsCutPair/)). $\square$

**Lemma (Cauchy-Schwarz).** Let $S$ be admissible, $c, c'$ classes, $\gamma$ rational and $i \in \mathbb{N}$. The amplitude majorant of $\gamma$ for the cut functions satisfies

$$\operatorname{maj}(c, c', \gamma)^2 \leq I(c, c', \gamma, i)\cdot I(c', c, \gamma^{-1}, i).$$

Lean: `New.Filling.amplitudeMajorant_sq_le` (New/Spanning/RemainingTerms/SchurTest.lean).

*Proof.* Substitute $y \mapsto \gamma^{-1}y$ in the second integral; Haar measure is invariant. Both integrals are then integrals over $y$, and Cauchy-Schwarz bounds the square of $\int F$ by $\int G\cdot\int H$ if $F(y)^2 \leq G(y)H(y)$ at every $y$. If the integrand $F(y) = \beta_c(y)\beta_{c'}(\gamma^{-1}y)\|W^\flat(y) \otimes W^\flat(\gamma^{-1}y)^*\|$ is zero, there is nothing to prove. Otherwise the kernel is not zero, so $y$ and $\gamma^{-1}y$ are in the cut by the previous lemma. A point in the cut with $\beta_d \neq 0$ is boxed, so the boxed cutoffs equal the cutoffs at both points. The product $G(y)H(y)$ contains the weights $\prod_v\operatorname{volumeRatio}(\gamma_v, y_v)^{-(k+i)}$ and $\prod_v\operatorname{volumeRatio}(\gamma_v^{-1}, \gamma_v^{-1}y_v)^{-(k+i)}$, whose product is $1$. What remains is $\beta_c(y)^2\beta_{c'}(\gamma^{-1}y)^2\|W^\flat(y)\|^2\|W^\flat(\gamma^{-1}y)\|^2 = F(y)^2$. $\square$

### Integration in stages

**Lemma (Mean over a cutoff).** Let $G$ be a unimodular group with Haar measure $\mu$, $\Gamma$ a countable group acting on the left through $\iota: \Gamma \to G$, $p \geq 0$ measurable with $\sum_{\kappa \in \Gamma}p(\iota(\kappa)u) = 1$ for all $u$, and $F \geq 0$ measurable and left invariant under $\Gamma$. Let $m$ be a measure on $Y$, $t: Y \to G$ measurable and $B \subset Y$ with $0 < m(B) < \infty$. If $\int_B F(u\,t(x))\,dm(x) \leq m(B)C$ for all $u \in G$, then $\int pF\,d\mu \leq \int Cp\,d\mu$.

Lean: `New.Filling.lintegral_cutoff_mul_le_of_average` (New/Spanning/RemainingTerms/SchurTest.lean).

*Proof.* First, $\int p(u)F(u)\,d\mu = \int F(ut)p(u)\,d\mu$ for every $t \in G$. To see this, substitute $u \mapsto ut$, insert $1 = \sum_\kappa p(\iota(\kappa)^{-1}u)$, substitute $u \mapsto \iota(\kappa)u$ in the $\kappa$-th term, use the invariance of $F$ and sum the first factor $p$ over $\kappa$. Then $m(B)\int pF = \int_B\int F(u\,t(x))p(u)\,d\mu\,dm(x)$. Exchange the integrals by Tonelli and use the hypothesis: this is at most $\int m(B)Cp\,d\mu$. Divide by $m(B)$. $\square$

**Lemma (Integration in stages).** Let $S$ be admissible and $c$ a class. Let $F \geq 0$ be measurable with $F(uy) = F(y)$ for $u \in \mathsf{U}^0_c$. Let $m$ be a measure on $X$, $s: X \to G_\infty$ measurable with every component $s(x)_v$ in $\mathsf{U}^0(\mathbb{R})$, and $B \subset X$ with $0 < m(B) < \infty$. Suppose that $\int_B F(u\,s(x)\,y)\,dm(x) \leq m(B)C$ for every $u$ with components in $\mathsf{U}^0(\mathbb{R})$ and every boxed $y$. Then

$$\int \beta^\square_c(y)\,\|W^\flat\|^2(y)\,F(y)\,dy \leq C\,\nu\,\#\mathrm{BesselCoord}.$$

Lean: `New.Filling.lintegral_boxCutoff_le_of_average` (New/Spanning/RemainingTerms/SchurTest.lean).

*Proof.* The cutoff factors as $\beta_c = p\,\omega$, where $p$ is a cutoff for $\mathsf{U}^0_c$ in $\mathsf{U}^0(\mathbb{R})^f$ and $\omega$ is invariant under $\mathsf{U}^0(\mathbb{R})$ on the left ([Lemma](/decl/New.Filling.exists_classCutoff_eq_mul/), in [the chapter on Poincaré series](/chapter/poincare-series/)). Write the integral over $y$ as an integral over orbits $\mathsf{U}^0(\mathbb{R})^f a$ of integrals over $u$. On one orbit, $\omega$, the indicator of the boxed points ([Lemma](/decl/New.Filling.mul_mem_boxedPoints_iff/)) and $\|W^\flat\|^2$ do not depend on $u$: the norm of a Bessel function is invariant under $\mathsf{U}$ on the left, since $\mathsf{U}$ acts by a unitary character. Only $p(ua)$ and $F(ua)$ vary. The previous lemma, applied on the orbit with $\Gamma = \mathsf{U}^0_c$ and $t = s$, gives $\int p(ua)F(ua)\,du \leq \int Cp(ua)\,du$ when $a$ is boxed. Put the orbits back together. The result is $C\int\beta_c\|W^\flat\|^2$, and this is at most $C\nu\,\#\mathrm{BesselCoord}$, since each local cut function has squared $L^2$ norm at most the number of its coordinates and the cutoff integrates to $\nu$ over a fundamental domain. $\square$

The test function $F$ will be the sum of the Schur weights over the orbit. The translations $s(x)$ will be the Eichler shifts, and $B$ a fundamental domain of a lattice.

### From the orbit to lattice translates

Let $\Lambda$ be the lattice of the class $c$. The orbit of $\gamma$ is not a lattice. But modulo the isotropic space $A$, the frames of its terms move by lattice vectors in $X_0$.

**Definition (Lattice translate).** Let $p_0, p$ be terms and $l$ a $k \times i$ matrix over $E$. Then $p$ is a lattice translate of $p_0$ by $l$ if the columns of $l$ lie in $\Lambda \cap X_0$, and modulo $A$ the frame of $p$ is that of $p_0$ plus $Ml$ times the first $i$ isotropic rows of the frame products of $\gamma$.

Lean: `New.Filling.IsLatticeTranslate` (New/Spanning/RemainingTerms/SchurOrbit.lean).

**Lemma (The orbit falls into few classes).** Let $\gamma$ lie over $(c, s, c')$ with cell rank $j$, and let $w \geq 0$ be a function on terms. Suppose that $\sum_{p \in B}w(p) \leq C$ for every subset $B$ of the orbit whose terms are all lattice translates of one $p_0 \in B$. Then $\sum_{p \in \text{orbit}}w(p) \leq \iota^k C$, where $\iota = \operatorname{isotropicRowsIndex}(j, h_c^{-1}\gamma h_{c'})$.

Lean: `New.Filling.tsum_orbit_le_of_isLatticeTranslate` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* Two terms of the orbit differ by $u \in \mathsf{U}^0_c$ on the left and $u' \in \mathsf{U}^0_{c'}$ on the right. Modulo $A$ their frames differ in $X_0$ by $k$ rows, one for each vector of a basis of $\Lambda \cap X_0$. These rows lie in $M$ times the lattice of rows of products of $\Lambda \cap A$ with the frame of $h_c^{-1}\gamma h_{c'}$. The part of this lattice that comes from $e_a$ with $a < j$ has index $\iota$ in it, by the definition of `isotropicRowsIndex` ([Definition](/decl/New.Filling.minorGauge/)). Colour each term by the classes of its $k$ rows modulo $M$ times the smaller lattice. There are at most $\iota^k$ colours. Two terms of one colour differ by $M$ times rows of the smaller lattice. The first $i$ isotropic rows of $\gamma$ are linearly independent, since the determinant of their block is not zero (see the proof of the kernel bound below), so the coefficients are given by a rational matrix $l$ with columns in $\Lambda \cap X_0$, and the terms are lattice translates. Apply the hypothesis to each colour. $\square$

**Lemma (Packing in a fibre).** Let $B$ be a set of lattice translates of $p_0$ in the orbit of $\gamma$, with parameters $l(p)$, and fix $q$. If $C$ bounds $\prod_v \operatorname{volumeRatio}(p_v, y_v)^{-(k+i)}$ for every $p \in B$ with $l(p) = q$, then $\sum_{p \in B,\,l(p) = q}\omega_{c', p, i}(y) \leq \tau C$.

Lean: `New.Filling.tsum_schurWeight_fibre_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* Each weight is at most $\beta_{c'}(p^{-1}y)C$. Two terms of the fibre have the same frame modulo $A$, so the frame vectors at $p^{-1}y$ differ by vectors of the real space $V$ of $n$-tuples of vectors of $A$, seen from $y$. Its real dimension is at most $2fn\varrho$. The packing lemma of [the chapter on frame counts](/chapter/frame-counts/) ([Lemma](/decl/New.Filling.tsum_le_of_le_classCutoff_mul/)), with $R = 1$, bounds the sum of the cutoffs by $(b^{6n^2})^{\dim V}$. The exponent is $6n^2\dim V \leq 10^5n^9f$, so the factor is at most $\tau$ by [Lemma](/decl/New.Filling.pow_le_tailScale/). $\square$

### From the lattice to an integral

[The chapter on frame counts](/chapter/frame-counts/) proves the bound at one real place ([Theorem](/decl/New.RealPlace.exists_majorant_volumeRatio_inv_pow/)). In one line: if $y$ lies in the frame box of radius $\rho$ and has Bessel length at most $\theta$, and $\delta$ is the determinant of the block of the subframe $e_0, \dots, e_{i-1}, z$, then $\operatorname{volumeRatio}^{-(k+i)}$, as a function of the shift $A \in X_0^i$ of the frame, has a measurable majorant with integral at most $(2\rho^2)^{(i+1)i}(2^{i+1}\theta^{2(j-i)})^k/|\delta|^{k+i}$.

**Definition (The kernel bound).** For a place $v$, let $\sigma_v$ be the diagonal $i \times i$ matrix with entries $M/\kappa^{\mathrm{scale}}_v(e_l)$, which converts shifts in the rational frame to the unit frame at $v$. Then

$$\operatorname{kernelBound}(j, \gamma, v) = |\det\sigma_v|^{-2k}\,\frac{(2\rho^2)^{(i+1)i}\,(2^{i+1}(b^{6n+2})^{2(j-i)})^k}{|\det Z^{\mathrm{sub}}_v|^{k+i}},$$

with $\rho = b^{37n}$ the frame box radius and $Z^{\mathrm{sub}}_v$ the block of the subframe in the real frame products of $\gamma$ at $v$.

Lean: `New.Filling.kernelBound` (New/Spanning/RemainingTerms/SchurOrbit.lean).

The factor $|\det\sigma_v|^{-2k}$ is the Jacobian of the passage from the shift in the unit frame to the parameter $x$ of the Eichler shift $\operatorname{eichlerShift}(j, x)$, a unipotent element that fixes the frame and moves $X_0$ along $e_0, \dots, e_{i-1}$.

**Lemma (From cosets to a lattice).** Let $\gamma$ have cell rank $j$ over $(c, s, c')$, $B$ a set of lattice translates of $p_0 \in B$ in the orbit, $u$ with components in $\mathsf{U}^0(\mathbb{R})$ and $y$ boxed. There is a measurable $\varphi \geq 0$ with $\int\varphi \leq \prod_v\operatorname{kernelBound}(j, \gamma, v)$ such that for every $x$,

$$\sum_{p \in B}\omega_{c', p, i}(u\,\operatorname{eichlerShift}(j, x)\,y) \leq \tau\sum_{w \in (\Lambda \cap X_0)^i}\varphi(w + x).$$

Lean: `New.Filling.exists_tsum_schurWeight_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* Let $\varphi$ be the product over $v$ of the majorants of the one-place theorem for the base point $u^{-1}p_0$, read in the parameters of the Eichler shift; its integral is at most the product of the kernel bounds. The volume ratio of $p$ at the shifted point is bounded by $\varphi$ at the shifted lattice point $l(p) + x$, since the frame of $p$ differs from that of $p_0$ in $X_0$ by $Ml(p)$ times the first $i$ rows. Sort the terms by $l(p)$ and sum each fibre by the packing lemma. $\square$

**Lemma (The kernel bound).** Let $\gamma$ have cell rank $j \geq 1$ and let $\delta_v = |\Phi_v(D_j(\gamma))|$ for the leading minor $D_j$ of the frame products. Then

$$\operatorname{kernelBound}(j, \gamma, v) \leq \Big(\frac{(2\rho^2)^{i+1}N^j}{\delta_v}\Big)^i\Big(\frac{(b^{13}/M^2)^iN^{j-\varrho}}{\delta_v}\Big)^k,$$

where $j - \varrho$ is truncated: it is $1$ at the top rank and $0$ below.

Lean: `New.Filling.kernelBound_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* The block determinant is $|\det Z^{\mathrm{sub}}_v| = \delta_v w_v^2/N^j$ up to the scale factor $w_v = |\kappa_v|^{\sum_{a<j}(\varrho-a)} \geq 1$, and $|\det\sigma_v| = (M\sqrt N)^i/w_v$. In the $k$-th power the powers of $w_v$ cancel; in the $i$-th power they are dropped since $w_v \geq 1$. The last column gives $2^{i+1}\theta^{2(j-\varrho)} \leq b^{13i}$ with $\theta = b^{6n+2}$: at a rank below the top this is $2^{i+1} \leq b^{13i}$, and at the top $i = \varrho \geq 10^5$, so $2^{i+1} \leq b^{i-17}$ and $\theta^2 \leq b^{12n+4} \leq b^{17+12i}$. $\square$

**Lemma (The product over the places).** If $\gamma$ lies over $(c, s, c')$ with cell rank $j \geq 1$, then

$$\prod_v\operatorname{kernelBound}(j, \gamma, v) \leq \tau\,(b^{13}/M^2)^{ikf}\,\operatorname{minorNorm}(j, \gamma)^{-k/2}.$$

Lean: `New.Filling.prod_kernelBound_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* Let $P = \prod_v\delta_v$. The minor is a nonzero algebraic integer, so $P \geq 1$, and $\sqrt{\operatorname{minorNorm}} = P/N^{(j-\varrho)f}$, since the norm of a CM number is the product of the squared moduli. Take the product of the previous lemma. In the first factor, $(2\rho^2)^{i+1}N^j \leq b^{(74n+1)n + 60n^2} \leq b^{135n^2}$ by $\rho = b^{37n}$, $2 \leq b$ and $N \leq b^{60n}$. With $P \geq 1$ the first factor is at most $b^{135n^2f\varrho} \leq \tau$. The second factor is $((b^{13}/M^2)^{if}N^{(j-\varrho)f}/P)^k = (b^{13}/M^2)^{ikf}\operatorname{minorNorm}^{-k/2}$. $\square$

**Lemma (From the lattice to an integral).** If $\gamma$ lies over $(c, s, c')$ with cell rank $j \geq 1$, then

$$\sum_{\delta \in \text{orbit}}I(c, c', \delta, i) \leq \nu\,\#\mathrm{BesselCoord}\,\tau^2(b^{13}/M^2)^{ikf}\Big(\frac{\iota}{\sqrt{\operatorname{minorNorm}(j, \gamma)}}\Big)^k.$$

Lean: `New.Filling.tsum_schurIntegral_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* Let $F(y)$ be the sum of the Schur weights $\omega_{c', p, i}(y)$ over the orbit. It is invariant under $\mathsf{U}^0_c$ on the left, which permutes the orbit and fixes the frame. Let $D$ be a fundamental domain of $(\Lambda \cap X_0)^i$ in the parameter space, of measure at least $1$. For $u$ in $\mathsf{U}^0(\mathbb{R})^f$ and boxed $y$, split the orbit into at most $\iota^k$ classes of lattice translates. On each class, the previous lemma and the unfolding $\int_D\sum_w\varphi(w + x)\,dx = \int\varphi$ give the bound $\tau\prod_v\operatorname{kernelBound}$. So $\int_D F(u\,\operatorname{eichlerShift}(x)\,y)\,dx \leq m(D)\,C$ with $C = \iota^k\tau\prod_v\operatorname{kernelBound}$. Integration in stages bounds the sum of the Schur integrals by $C\nu\,\#\mathrm{BesselCoord}$. Insert the previous lemma. $\square$

### The test

**Theorem (Schur's test).** Let $S$ be admissible. Let $\gamma$ lie over $(c, s, c')$ and have cell rank $j \geq 1$. Then

$$\Big(\sum_{\delta \in \mathsf{U}^0_c\gamma\mathsf{U}^0_{c'}}\operatorname{maj}(c, c', \delta)\Big)^2 \leq \big(\nu\,d\,\tau^2(b^{13}/M^2)^{ikf}\big)^2\Big(\frac{N^f}{\mathsf{g}^\sharp}\Big)^k,$$

where $d = \#\mathrm{BesselCoord}$ and $\mathsf{g}^\sharp = \operatorname{minorGauge}(j, c, c', \gamma)$.

Lean: `New.Filling.sq_tsum_amplitudeMajorant_doubleCoset_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* A sum over the orbit is an integral for the counting measure. So Cauchy-Schwarz and the lemma of the same name bound the square by $\sum_\delta I(c, c', \delta, i)\cdot\sum_\delta I(c', c, \delta^{-1}, i)$. Inversion maps the orbit of $\gamma$ into the orbit of $\gamma^{-1}$ under $\mathsf{U}^0_{c'} \times \mathsf{U}^0_c$, and $\gamma^{-1}$ has the same cell rank and the same minor norm. Apply the previous lemma to both sums. The two indices are $\iota(h_c^{-1}\gamma h_{c'})$ and $\iota((h_c^{-1}\gamma h_{c'})^{-1})$, and $N^f/\mathsf{g}^\sharp$ is exactly their product divided by $\operatorname{minorNorm}$ ([Lemma](/decl/New.Filling.HasCellRank.maxGauge_eq/) and its companion for $\mathsf{g}^\sharp$). $\square$

It remains to write the bound in units of the orbit bound.

**Lemma (The second moments of the cells).** If $j \neq 0$, then $\tau^8\tau^{-32i}\mathcal{D}_{\mathrm{id}} \leq \mathcal{D}_j$.

Lean: `New.Filling.div_tailScale_pow_mul_identitySecondMoment_le_cellRankSecondMoment` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* At the top rank $\mathcal{D}_j = \mathcal{D}_{\mathrm{main}} \geq \tau^{44}\mathcal{D}_{\mathrm{id}} \geq \tau^8\mathcal{D}_{\mathrm{id}}$, since $\tau \geq 1$. Below the top, $i = j \geq 1$, so $\tau^8\tau^{-32i} \leq \tau^{-24} \leq \tau^{-16}$, and $\mathcal{D}_j = \tau^{-16}\mathcal{D}_{\mathrm{id}}$. $\square$

**Lemma (The level against the base).** $b^{13}/M^2 \leq (b^4M)^{-1}$.

Lean: `New.Filling.b_pow_div_M_sq_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* $b^{17} \leq b^{19} \leq M$, so $b^{13}\cdot b^4M \leq M^2$. $\square$

**Theorem (One orbit).** Let $\gamma$ lie over $(c, s, c')$ with cell rank $j \geq 1$, and let $\operatorname{termDiscNorm}(\gamma) \leq N^f\operatorname{minorNorm}(j, \gamma)$. Then

$$\sum_{\delta \in \mathsf{U}^0_c\gamma\mathsf{U}^0_{c'}}\operatorname{maj}(c, c', \delta) \leq \nu\operatorname{orbitBound}(j, \operatorname{maxGauge}(j, c, c', \gamma)).$$

Lean: `New.Filling.tsum_amplitudeMajorant_orbit_le` (New/Spanning/RemainingTerms/SchurOrbit.lean).

*Proof.* The hypothesis gives $\operatorname{maxGauge} = \mathsf{g}^\sharp$. Compare the squares. By Schur's test the left side squared is at most $\nu^2d^2\tau^4(b^4M)^{-2ikf}N^{kf}(\mathsf{g}^\sharp)^{-k}$. The right side squared is $\nu^2\tau^4\mathcal{D}_j/(n_p(M^{2if}\mathsf{g}^\sharp)^k)$. Use $\mathcal{D}_j \geq \tau^8b^{-8ikf}\mathcal{D}_{\mathrm{id}}$ (since $\tau^{32} = b^{8kf}$), $\mathcal{D}_{\mathrm{id}} = \#\bar R_0\,\#\mathrm{Classes}\,d$ and $n_p = \#\bar R_0\,\#\mathrm{Classes}/N^{kf}$. The right side squared is then at least $\nu^2\tau^4\tau^8d\,b^{-8ikf}M^{-2ikf}N^{kf}(\mathsf{g}^\sharp)^{-k}$. The two sides differ by the factor $d$ against $\tau^8$, and $d \leq b^{2kf} = \tau^8$ is a field of the admissible data. $\square$

**Remark (Formalization).** All sums of this section are taken in $[0, \infty]$, so they need no convergence proof. A divergent sum would have the value $\infty$, and the theorems show that the sums are finite. The orbit is summed as a set, so each term of the double coset is counted once, whatever the number of pairs $(u, u')$ that give it.
