---
title: Descents and block periods
lean:
  - Lib/Weil/Periods/DescentVanishing.lean
decls:
  - New.SiegelWeil.DescentsVanish
  - New.SiegelWeil.DescentsVanish.comp_mul_right
  - New.SiegelWeil.DescentsVanish.of_schrodingerOp
  - New.Space.ratStabilizer
  - New.Space.gram_eq_iff_mem_orbit
  - New.Space.Splitting.centreCoeff_integral_eq_tsum
  - New.Space.Splitting.centreCoeff_eq_integral_ratStabilizer
  - New.SiegelWeil.blockPeriod
  - New.SiegelWeil.frameChar
  - New.SiegelWeil.frameWeight
  - New.SiegelWeil.frameWeight_ne_zero_iff
  - New.SiegelWeil.DescentsVanish.integral_frameChar_mul_blockPeriod_eq_zero
  - New.SiegelWeil.integral_continuousMap_frameChar_eq_zero
  - New.SiegelWeil.exists_continuousMap_eq_conj_blockPeriod
  - New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Descents and block periods

This section proves a second unfolding, which is used for the false lifts of Volume 11. Let $Y$ be an automorphic function on a definite unitary group $U(n)$. Split the standard basis into two blocks, of sizes $n_1$ and $n_2$. Suppose that every theta descent of $Y$ to the split group of rank $2 n_1$ vanishes, for data that are vacua at a set $T$ of places. Then the period of $Y$ over the second block $U(n_2)$ vanishes, at every point of the first block. The proof unfolds one Fourier coefficient of a descent, as in the classical work of Rallis on the Howe duality conjecture. It then uses the Stone-Weierstrass theorem to pass from characters to the period itself.

### Vanishing descents

Let $W$ and $V$ be hermitian spaces, with a theta kernel $\theta_f(g, h)$ on $U(W)(\mathbb{A}) \times U(V)(\mathbb{A})$ for each datum $f$ on $\operatorname{Hom}(W, V)$. The kernel is twisted by $\alpha(\det h)$ for a character $\alpha$ of $U(1)$. For a set $S$ of finite places, let $\operatorname{pr}_S$ be the projection to the data that are vacua at the places of $S$ and their conjugates.

**Definition (Vanishing descents).** The descents of a function $Y$ on $U(V)(\mathbb{A})$ to $U(W)$ vanish for $\alpha$ and $S$ if

$$\int_{[U(V)]} \theta_f(g, h)\, Y(h)\, dh = 0 \qquad\text{for all } g \in U(W)(\mathbb{A}),$$

for every datum $f$ with $\operatorname{pr}_S f = f$.

Lean: `New.SiegelWeil.DescentsVanish` (Lib/Weil/Periods/DescentVanishing.lean).

**Remark (Formalization).** The definition takes no twist in $g$. A twist by a character of $\det g$ would only multiply each descent by that character, so it does not change the vanishing. The integral is the quotient integral of [the theta lifts](/chapter/theta-lifts-seesaw/), and the definition asks that the function $g \mapsto \int \theta_f(g, h) Y(h)\, dh$ be the zero function. For a non-integrable integrand the integral is $0$ by the convention of the library, but the users of the definition take $Y$ continuous on a compact quotient, where the integrals exist.

**Lemma.** Let $Y$ be automorphic, with vanishing descents for $\alpha$ and $S$. Let $h_0 \in U(V)(\mathbb{A})$ be integral at every place of $S$. Then the right translate $h \mapsto Y(h h_0)$ also has vanishing descents for $\alpha$ and $S$.

Lean: `New.SiegelWeil.DescentsVanish.comp_mul_right` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* By the invariance of the quotient measure, the descent of the translate by $f$ is the descent of $Y$ by $\omega(1, h_0^{-1}) f$. The point $h_0^{-1}$ is integral at $S$. So it preserves the vacuum there, and $\omega(1, h_0^{-1}) f$ is again a vacuum at $S$. $\square$

**Lemma.** Let $V$ be definite, and let $A$ be a set of finite places that is disjoint from its conjugate set. Let $\Sigma$ be $A$ together with its conjugates. To prove that the descents of $Y$ vanish for the data that are vacua off $\Sigma$, it is enough to test special data: the images of the vacuum under the finite Schrödinger operators of Schwartz-Bruhat functions above $A$, integrated against the Fock vectors of polynomials at the infinite places.

Lean: `New.SiegelWeil.DescentsVanish.of_schrodingerOp` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* At each $g$, the descent is a bounded linear functional of the datum, because $Y$ is rapidly decreasing. A lemma on the vacuum projections says that a bounded functional vanishes on the data that are vacua off $\Sigma$ once it vanishes on the data $v_P \otimes \varrho(x)\, \mathrm{vac}$, with $x$ finite and supported on $\Sigma$ (Lean: `New.Space.map_eq_zero_of_map_integrated_eq_zero`). Each $\varrho(x)\, \mathrm{vac}$ is a multiple of the image of the vacuum under a Schrödinger operator of an indicator function above $A$. $\square$

### Fourier coefficients of a theta lift

Let $W$ have a splitting $D$ with isotropic frames of rank $p$, as in [the Weil representation from a vacuum](/chapter/weil-representation/). The centre of the unipotent radical of $D$ is parametrised by $p \times p$ matrices $z$ over $\mathbb{A}$. For a function $F$ on $U(W)(\mathbb{A})$ and a rational matrix $\tau$, the Fourier coefficient along the centre is the mean

$$F_{\tau}(g) = \int_{M_p(E) \backslash M_p(\mathbb{A})} \psi\big(\operatorname{tr}(\tau z)\big)\, F(z \cdot g)\, dz.$$

The theta kernel is a sum over the rational frames $x \in M_{m \times p}(E)$ of terms $\theta_x(g, h)$. In the textbook, a central element acts on the term of $x$ by a character of the Gram matrix $x^{\dagger} J x$. So the coefficient picks out the frames of one Gram matrix, and, by Witt's theorem, this set is one orbit. This is the unfolding of the Fourier coefficients of theta lifts into periods over stabilisers. The source cites P. Walls, arXiv 1501.01565 (2015), Prop. 2.1.1, and S. Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984), 333-399, for it.

**Lemma (Witt's theorem for frames).** Let $x$ be a rational frame whose Gram matrix $x^{\dagger} J x$ is invertible. A rational frame $z$ has the same Gram matrix as $x$ if and only if $x$ lies in the orbit of $z$ under the rational unitary group.

Lean: `New.Space.gram_eq_iff_mem_orbit` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* If $z = \gamma x$ then the Gram matrices agree, because $\gamma$ is an isometry. If they agree, both frames are injective, because the Gram matrix is invertible, and Witt's theorem over $E$ gives $\gamma$. $\square$

**Definition (Rational stabiliser).** For a rational frame $x$, the rational stabiliser of $x$ is the image in $U(V)(\mathbb{A})$ of the group of rational points $\gamma$ with $\gamma x = x$.

Lean: `New.Space.ratStabilizer` (Lib/Weil/Periods/DescentVanishing.lean).

**Proposition.** Let $y$ be continuous on $U(V)(\mathbb{A})$, and let the terms of the theta kernel at $g$ be absolutely integrable against $y$. Let $\beta \in M_p(E)$. Then

$$\Big( k \mapsto \int_{[U(V)]} \theta_f(k, h)\, y(h)\, dh \Big)_{\jmath \beta}(g) = \sum_{x^{\dagger} J x = \beta} \int_{[U(V)]} \theta_x(g, h)\, y(h)\, dh .$$

If, in addition, $y$ is left invariant under the rational points and $x$ is a rational frame with invertible Gram matrix $\beta$, then $\theta_x(g, \cdot)\, y$ is integrable modulo the rational stabiliser $S_x$ of $x$, and the coefficient at $\jmath \beta$ is

$$\int_{S_x \backslash U(V)(\mathbb{A})} \theta_x(g, h)\, y(h)\, dh .$$

Lean: `New.Space.Splitting.centreCoeff_integral_eq_tsum`, `New.Space.Splitting.centreCoeff_eq_integral_ratStabilizer` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* The central element with parameter $z$ multiplies the term of $x$ by $\psi(\operatorname{tr}(-\jmath\, x^{\dagger} J x\, z))$. Expand the kernel into its terms and exchange the sum with the integral over $[U(V)]$. The hypothesis of absolute integrability allows this. In the mean over $z$, the frequency of the term of $x$ is $-\jmath\, x^{\dagger} J x + \jmath \beta$. Since $\jmath \neq 0$, it is $0$ exactly when $x^{\dagger} J x = \beta$. The mean of a nontrivial character over $M_p(E) \backslash M_p(\mathbb{A})$ is $0$. This gives the first formula. For the second, the frames with Gram matrix $\beta$ form one orbit, by Witt's theorem for frames, and the term of $\gamma x$ at $\gamma h$, times $y$, equals the term of $x$ at $h$, times $y$. So the sum over the orbit unfolds to the integral modulo the stabiliser (Lean: `New.integral_tsum_orbit_of_lt_top_or_integrable`). $\square$

**Remark (Formalization).** The integrability is part of the conclusion, not a hypothesis. The file has a global instance with low priority that lets a monoid that acts on columns act on matrices, column by column. It sits in the namespace `New.Space.Splitting` but it is not scoped, so it is active wherever the file is imported. The register of findings records it as F-024, open. The lemma `New.U.smul_matrix_eq_mul` says that the resulting action of the unitary group on frames is matrix multiplication, and it is proved by `rfl`.

### Characters of a frame and the weight

From here on, $V$ is the standard definite space of rank $n$, with Gram matrix $1$. The basis is split by a bijection $o \colon n_1 \sqcup n_2 \to n$. Let $o_1$ be the frame of the first $n_1$ basis vectors. The block embedding sends $(h_1, h_2)$ to $\operatorname{diag}(h_1, h_2)$. The stabiliser of $o_1$ is the second block.

**Definition (Block period).** For a function $Y$ on $U(n)(\mathbb{A})$ and a point $h_1$ of $U(n_1)(\mathbb{A})$, put

$$I(h) = \int_{[U(n_2)]} Y\big(\operatorname{diag}(h_1, h_2)\, h\big)\, dh_2 .$$

Lean: `New.SiegelWeil.blockPeriod` (Lib/Weil/Periods/DescentVanishing.lean).

The period $I(h)$ depends only on the frame $h^{-1} o_1$, because the second block fixes $o_1$ and the inner integral is invariant.

**Definition (Characters of a frame).** Fix a set $T$ of finite places, and let $\delta$ be an idele whose finite part generates the inverse different. For an adelic $n \times n_1$ frame $x$ and a family $u = (u_{ij})$ of adeles, put

$$\psi_u(x) = \psi\Big(\delta \sum_{i, j} u_{ij}\, x_{ij}\Big),$$

where the components of the sum at the places of $T$ and their conjugates are replaced by $0$.

Lean: `New.SiegelWeil.frameChar` (Lib/Weil/Periods/DescentVanishing.lean).

**Definition (Weight of a frame).** Let $e$ be the vacuum function on adelic vectors, and let $\alpha_0$ be the scale idele of the Weil data. The weight of a frame $x$ is $\mathrm{vac}[\alpha_0 x] = |e(\alpha_0 x)|^2$.

Lean: `New.SiegelWeil.frameWeight` (Lib/Weil/Periods/DescentVanishing.lean).

**Lemma.** The weight of $x$ is nonzero if and only if every entry of $x$ has integral finite part.

Lean: `New.SiegelWeil.frameWeight_ne_zero_iff` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* At the infinite places the vacuum function is a Gaussian, which has no zeros. At the finite places it is a function of modulus $1$ on a lattice and $0$ off it. Scaling by $\alpha_0$ carries this lattice to the integral vectors. $\square$

### From descents to an orthogonality

Let $g_0 = \operatorname{diag}(h_1, 1)$, and for $g \in U(n)(\mathbb{A})$ put $x(g) = (g_0^{-1} g)^{-1} o_1$ and $I_0(g) = I(g_0^{-1} g)$. Let $\nu$ be the invariant measure on $U(n_2)(\mathbb{A}) \backslash U(n)(\mathbb{A})$, carried by $U(n)(\mathbb{A})$.

**Proposition.** Let $Y$ be continuous on $U(n)(\mathbb{A})$ and left invariant under the rational points. Let the descents of $Y$ to the hyperbolic space of rank $2 n_1$ vanish for the character $\upsilon^{n_1}$ and the set $T$, where $\upsilon$ is the restriction of the splitting character to the norm-one ideles. Then, for every $u$, the function $\psi_u(x(g))\, \mathrm{vac}[\alpha_0 x(g)]\, I_0(g)$ is $\nu$-integrable, with integral $0$.

Lean: `New.SiegelWeil.DescentsVanish.integral_frameChar_mul_blockPeriod_eq_zero` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* Take the datum $f = \varrho(\xi_u)\, \mathrm{vac}$, a Heisenberg translate of the vacuum by a vector $\xi_u$ built from $u$, with the components at $T$ and their conjugates set to $0$. This datum is a vacuum at $T$, so its descent is $0$. Take the coefficient at the unit Gram matrix and at the Levi element given by $\alpha_0 h_1$. The rational frame $x_0 = o_1$ has Gram matrix $1$, which is invertible. By the last proposition, the coefficient is the integral of the term of $x_0$ modulo its stabiliser, which is the rational points of the second block. The term of $x_0$, times $Y$, is $c\, \psi_u(x(g))\, \mathrm{vac}[\alpha_0 x(g)]\, Y(g)$, for a constant $c \neq 0$. One factor of $c$ is the scalar by which the Levi element acts in the mixed model. So the integral of $\psi_u(x)\, \mathrm{vac}[\alpha_0 x]\, Y$ modulo the rational points of the second block is $0$. The factor $\psi_u(x)\, \mathrm{vac}[\alpha_0 x]$ is invariant under the whole second block. Integrating first over $[U(n_2)]$ gives the claim. $\square$

**Remark (Formalization).** The character in the hypothesis is written `1 * upsilonU1 ^ Fintype.card n₁`. The factor $1$ is the character of the zero space, which is the anisotropic part of the hyperbolic space. The constant $c$ is shown to be nonzero, and the proof needs that.

### Stone-Weierstrass and the end of the proof

**Lemma.** Let $x$ be a continuous family of frames on a space $Z$ with a measure $\nu$, and let $w$ be a function on $Z$. Suppose that for every $u$ the function $\psi_u(x(g))\, w(g)$ is integrable with integral $0$. Then for every continuous function $\chi$ on the product of circles indexed by the families $u$, the function $\chi\big(u \mapsto \psi_u(x(g))\big)\, w(g)$ is integrable with integral $0$.

Lean: `New.SiegelWeil.integral_continuousMap_frameChar_eq_zero` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* The case $u = 0$ shows that $w$ is integrable, and $\chi$ is bounded. So the integral is a continuous linear functional $\Lambda$ of $\chi$. The functions that agree with some $\psi_u$ on all frames form a monoid. It is closed under complex conjugation, because $\overline{\psi_u} = \psi_{-u}$, and it separates points of the product of circles. By the Stone-Weierstrass theorem its span is dense, and $\Lambda$ vanishes on it. $\square$

**Lemma.** Let $Y$ be continuous on $U(n)(\mathbb{A})$, left invariant under the rational points, and right invariant under the integral points supported on $T$ and its conjugates. Then there is a continuous function $\chi$ on the product of circles with

$$\chi\big(u \mapsto \psi_u(h^{-1} o_1)\big) = \overline{I(h)}$$

for every $h$ with $\mathrm{vac}[\alpha_0 h^{-1} o_1] \neq 0$.

Lean: `New.SiegelWeil.exists_continuousMap_eq_conj_blockPeriod` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* Let $K$ be the compact set of the points with integral finite part. On $K$ the period depends only on the values of the characters. For two points $a, b$ of $K$ with the same values, let $k$ be the part of $a^{-1} b$ at $T$ and its conjugates. Then $k$ fixes $Y$ on the right, and $a k$ has the same frame as $b$. The map from $K$ to the product of circles is continuous. A continuous function on a compact space that is constant on the fibres of such a map extends to a continuous function on the whole product, by the Tietze extension theorem. Every frame of nonzero weight is the frame of a point of $K$. $\square$

**Theorem.** Let $Y$ be continuous on $U(n)(\mathbb{A})$, left invariant under the rational points, and right invariant under the points of the standard level that are supported on $T$ and its conjugates. Split the basis as $n_1 \sqcup n_2$. Suppose that the descents of $Y$ to the hyperbolic space of rank $2 n_1$ vanish for the character $\upsilon^{n_1}$ and the set $T$. Then for every $h_1 \in U(n_1)(\mathbb{A})$,

$$\int_{[U(n_2)]} Y\big(\operatorname{diag}(h_1, h_2)\big)\, dh_2 = 0 .$$

Lean: `New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* Let $\chi$ be the function of the last lemma. By the orthogonality and the Stone-Weierstrass lemma,

$$\int \chi\big(\psi_\bullet(x(g))\big)\, \mathrm{vac}[\alpha_0 x(g)]\, I_0(g)\, d\nu(g) = 0 .$$

Where the weight is nonzero the factor $\chi$ is $\overline{I_0(g)}$. Where it is zero the integrand is $0$. So the integrand is $\rho(g) = \mathrm{vac}[\alpha_0 x(g)]\, |I_0(g)|^2$, and $\int \rho\, d\nu = 0$. The function $\rho$ is continuous, non-negative and invariant under the second block. So $\rho = 0$. At $g = g_0$ the frame is $o_1$, which is integral, so the weight is nonzero. So $I_0(g_0) = I(1) = 0$, and $I(1)$ is the period of the theorem. $\square$

**Remark (Formalization).** The theorem has no integrability hypothesis. The space is definite, so the quotient is compact and a continuous automorphic $Y$ is rapidly decreasing and bounded. The source gets all the integrability from this. The theorem is stated for the standard definite space with Gram matrix $1$ and for one splitting of its basis. The level hypothesis and the vacuum condition use the same set $T$. The chapter [false lifts](/chapter/false-lifts/) applies the theorem to a product of two functions.
