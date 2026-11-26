---
title: Determinants, norms and integral scalings
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.normDet_sq_mul_det_compression
  - New.Data.norm_map_det_le_pow
  - New.LevelPlaces.LevelForm.normSqAt_smul
  - New.LevelPlaces.LevelForm.normSqAt_nonneg
  - New.LevelPlaces.LevelForm.normSqAt_pos
  - New.DescentPair.exists_smul_mem_integralForms_maximal
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Determinants, norms and integral scalings

This section proves six general lemmas. Two are linear algebra: a formula for the determinant of a compression, and a bound for a determinant by its eigenvalues. Three are about the squared norm $\|\varphi\|_\sigma^2$ of a form at an automorphism $\sigma$ of $\mathbb{C}$. The last scales a nonzero form to valuation $0$ at an $\ell$-adic place. Sections 6 and 7 use all six. None of them uses the data $D$.

### The determinant of a compression

Let $U$ and $V$ be finite dimensional complex inner product spaces, $u \colon U \to V$ linear and $T$ an operator on $V$. Let $\mathrm{pr}$ be the orthogonal projection of $V$ onto the range $u(U)$. The *compression* of $T$ to $u(U)$ is the operator $\mathrm{pr}\,T|_{u(U)}$ on $u(U)$. The norm determinant $|\det|(u)$ is Mathlib's `LinearMap.normDet`, with $|\det|(u)^2 = \det(u^*u)$.

**Lemma (Determinant of a compression).** If $u$ is injective, then

$$|\det|(u)^2\cdot\det\big(\mathrm{pr}\,T|_{u(U)}\big) = \det\big(u^*\,T\,u\big).$$

Lean: `New.Data.normDet_sq_mul_det_compression` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Let $e \colon U \to u(U)$ be the isomorphism $x \mapsto u x$, and let $S = \mathrm{pr}\,T|_{u(U)}$. We claim

$$u^*\,T\,u = (u^*u)\circ\big(e^{-1}\,S\,e\big).$$

Both sides are operators on $U$. Fix $x, y \in U$ and compare $\langle x, \cdot\,\rangle$ of both sides at $y$. On the left, $\langle x, u^*Tuy\rangle = \langle ux, Tuy\rangle$. On the right, $u\,e^{-1}(z) = z$ for $z \in u(U)$, so $\langle x, u^*u\,e^{-1}S e y\rangle = \langle ux, S(uy)\rangle = \langle ux, \mathrm{pr}\,T u y\rangle$. The vector $ux$ lies in $u(U)$, and $\mathrm{pr}$ is self-adjoint with image $u(U)$, so $\langle ux, \mathrm{pr}\,w\rangle = \langle ux, w\rangle$ for every $w$. So the two sides agree. Take determinants. The determinant of a composite is the product, and $\det(e^{-1}Se) = \det S$ since conjugation by an isomorphism does not change the determinant. Finally $\det(u^*u) = |\det|(u)^2$, as a real number cast to $\mathbb{C}$. $\square$

The point of the lemma is that $|\det|(u)^2$ is the covolume of the lattice that $u$ carries, while $\det(u^*Tu)$ can be computed from the inner products $\langle ux, Tuy\rangle$ alone. Section 7 applies it with $u = \Theta_\vartheta$ and $T = U_\vartheta$.

### A determinant and its eigenvalues

**Lemma (Determinant bound by eigenvalues).** Let $L$ be a finite dimensional complex vector space, $u$ an operator on $L$, $K$ a normed field and $f \colon \mathbb{C} \to K$ a ring map. Let $B$ be real. If $\|f(\alpha)\| \leq B$ for every eigenvalue $\alpha$ of $u$, that is, for every $\alpha$ and $z$ such that $z$ is an eigenvector of $u$ for $\alpha$, then

$$\|f(\det u)\| \leq B^{\dim L}.$$

Lean: `New.Data.norm_map_det_le_pow` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The field $\mathbb{C}$ is algebraically closed, so the characteristic polynomial $\chi_u$ splits. So $\det u$ is the product of the roots of $\chi_u$, counted with multiplicity, and the number of roots is the degree $\dim L$. The map $\alpha \mapsto \|f(\alpha)\|$ is multiplicative, so $\|f(\det u)\|$ is the product of the numbers $\|f(\alpha)\|$ over the roots. Each factor is at least $0$. Each root $\alpha$ is an eigenvalue, since a root of $\chi_u$ has an eigenvector, so each factor is at most $B$. A product of $\dim L$ numbers in $[0, B]$ is at most $B^{\dim L}$. $\square$

The lemma is used twice. For $f = \sigma$ an automorphism of $\mathbb{C}$ it gives the archimedean bound for $\Delta(1)$. For $f = \iota$, an isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, it gives the $\ell$-adic bound for $\Delta(\vartheta)$.

**Remark (Formalization).** The lemma needs no hypothesis $B \geq 0$. If $\dim L > 0$, then $u$ has an eigenvalue, so $0 \leq \|f(\alpha)\| \leq B$. If $\dim L = 0$, then $\det u = 1$ and $B^0 = 1$.

### The norms of a form at an automorphism

Let $E$ be a CM field with a CM type and Weil data, and $O$ a descent pair over $E$: the datum of a lift from a hermitian space with basis $r$ to the standard space $V$ with basis $n$ ([single theta lifts](/chapter/single-theta-lifts/#descent-pairs-and-the-vector-kernel)). Let $\mathcal{F}$ be its space of forms on $V$, the algebraic forms of the weight and the level of $O$ (`O.FormV`). For $\varphi \in \mathcal{F}$ and an automorphism $\sigma$ of $\mathbb{C}$, the *squared norm at $\sigma$* is the class sum

$$\|\varphi\|_\sigma^2 = \sum_{g} \frac{1}{\#\mathrm{Aut}(g)}\,\big\|\sigma(\varphi(g))\big\|^2_{\mathrm{Gram}},$$

over representatives $g$ of the classes of the level, with the Gram norm $\|\xi\|^2_{\mathrm{Gram}} = \mathrm{Re}(\xi^*G\xi)$ of the positive definite Gram matrix $G$ of the weight ([the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). Lean: `New.LevelPlaces.LevelForm.normSqAt` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean). For $\sigma = 1$ it is $\|\varphi\|^2$, the square of the norm of the inner product.

**Lemma (Scaling).** For $c \in \mathbb{C}$, $\|c\,\varphi\|_\sigma^2 = |\sigma(c)|^2\,\|\varphi\|_\sigma^2$.

Lean: `New.LevelPlaces.LevelForm.normSqAt_smul` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* The value of $c\varphi$ at $g$ is $c\,\varphi(g)$, so $\sigma((c\varphi)(g)) = \sigma(c)\,\sigma(\varphi(g))$. The Gram norm of $\sigma(c)\xi$ is $|\sigma(c)|^2$ times the Gram norm of $\xi$, because $\xi \mapsto \xi^*G\xi$ is a hermitian form. The factor $|\sigma(c)|^2$ comes out of the class sum. $\square$

**Lemma (Nonnegativity).** $\|\varphi\|_\sigma^2 \geq 0$.

Lean: `New.LevelPlaces.LevelForm.normSqAt_nonneg` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Each weight $1/\#\mathrm{Aut}(g)$ is positive, and each Gram norm is at least $0$ since $G$ is positive definite. $\square$

**Lemma (Positivity).** If $\varphi \neq 0$, then $\|\varphi\|_\sigma^2 > 0$ for every $\sigma$.

Lean: `New.LevelPlaces.LevelForm.normSqAt_pos` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* A form of the level is determined by its values at the representatives $c$ of the double cosets, the chosen elements of each class. If all these values were $0$, then $\varphi = 0$. So $\varphi(c) \neq 0$ for some class $c$. Then $\sigma(\varphi(c)) \neq 0$, as $\sigma$ is injective, and its Gram norm is positive because $G$ is positive definite. So the class sum has one positive term and no negative terms. $\square$

The positivity at every $\sigma$, not only at $\sigma = 1$, is what Section 7 needs: it divides an inequality between squared norms at $\sigma$ by $\|z\|_\sigma^2$ for an eigenvector $z$.

### Scaling a form to valuation zero

Let $\ell$ be a prime and $\iota \colon \mathbb{C} \to \mathbb{C}_\ell$ a ring map, an *$\ell$-adic place* (`PadicPlace`). The gauge $\|\xi\|_g$ of a vector $\xi$ at $g \in G_f$ and the integral forms at $\iota$, the forms with $\|\varphi(g)\|_g \leq 1$ for every $g$, are those of [the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge). We use its properties (a) to (d): the gauge is invariant under rational points, invariant under right multiplication by elements $k$ of $\mathcal{K}_\ell$ (integral and invertible above $\ell$), scales by $|\iota(c)|$, and at an element $k$ of $\mathcal{K}_\ell$ it is at most $1$ exactly when every coordinate $\xi_i$ has $|\iota(\xi_i)| \leq 1$.

**Lemma (A scaling of valuation zero).** Let $O$ be a descent pair over $E$, $\varphi \neq 0$ a form in $\mathcal{F}$, $\ell$ a prime and $\iota$ an $\ell$-adic place. There is $c \neq 0$ in $\mathbb{C}$ such that $c\varphi$ is integral at $\iota$, and such that for every $\alpha \in \mathbb{C}$: if $\alpha c\varphi$ is integral at $\iota$, then $|\iota(\alpha)| \leq 1$.

Lean: `New.DescentPair.exists_smul_mem_integralForms_maximal` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Let $K$ be the level of $O$. For every class $q$ of $K$ choose a representative $s(q)$ that lies in $\mathcal{K}_\ell$. Such representatives exist by weak approximation above $\ell$ ([the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). As in the previous proof, some value $\varphi(s(q))_i$ is not $0$. The set of pairs $(q, i)$ of a class and a coordinate is finite. Choose $(q_0, i_0)$ at which $|\iota(\varphi(s(q))_i)|$ is largest, and put $x = \varphi(s(q_0))_{i_0}$. Then $|\iota(x)| > 0$, so $x \neq 0$. Let $c = x^{-1}$ and $\psi = c\varphi$.

First, $\psi$ is integral. By the choice of $x$, every coordinate of $\psi(s(q))$ has $|\iota(\cdot)| \leq |\iota(x)|/|\iota(x)| = 1$. Since $s(q) \in \mathcal{K}_\ell$, property (d) gives $\|\psi(s(q))\|_{s(q)} \leq 1$. Now let $g \in G_f$ be arbitrary, with class $q$. Write $g = \gamma\,s(q)\,k$ with $\gamma$ rational and $k \in K$. The form satisfies $\psi(g) = \chi(k)\,\rho(\gamma)\,\psi(s(q))$, where $\chi$ is the character of the level and $\rho$ the representation of the weight. The value $\chi(k)$ has finite order, so $|\iota(\chi(k))| = 1$. By properties (c), (b) and (a), in that order,

$$\|\psi(g)\|_g = \|\rho(\gamma)\psi(s(q))\|_{\gamma s(q) k} = \|\rho(\gamma)\psi(s(q))\|_{\gamma s(q)} = \|\psi(s(q))\|_{s(q)} \leq 1 .$$

Property (b) applies because the level $K$ lies in the standard level, which lies in $\mathcal{K}_\ell$.

Second, let $\alpha c\varphi$ be integral. Its gauge at $s(q_0) \in \mathcal{K}_\ell$ is at most $1$, so by (d) every coordinate of $\alpha\,c\,\varphi(s(q_0))$ is integral at $\iota$. The coordinate $i_0$ is $\alpha\,x^{-1}x = \alpha$. So $|\iota(\alpha)| \leq 1$. $\square$

So $c$ is a scalar that makes $c\varphi$ integral with one coordinate equal to $1$ at a representative in $\mathcal{K}_\ell$. No smaller scaling by a non-integral number stays integral. Section 7 applies this to an eigenvector $z$ of an operator that keeps integral forms integral: the eigenvalue $\alpha$ then satisfies $|\iota(\alpha)| \leq 1$.

**Example.** Take one class with trivial weight, so a form is one number, and $\varphi = 6$ at $\ell = 2$. The lemma gives $c = 1/6$, and $c\varphi = 1$. The number $\tfrac12 c\varphi = \tfrac12$ is not integral at $2$, in line with $|\iota(1/2)|_2 = 2 > 1$. The number $3c\varphi = 3$ is integral, and $|\iota(3)|_2 = 1$.
