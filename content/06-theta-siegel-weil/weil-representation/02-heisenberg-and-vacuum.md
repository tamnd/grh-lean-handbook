---
title: The Heisenberg datum and its vacuum
lean:
  - Lib/Weil/Construction/HeisenbergModel.lean
decls:
  - New.Heisenberg
  - New.Heisenberg.Rep
  - New.Heisenberg.IsVacuum
  - New.Heisenberg.IsVacuum.Model
  - New.Heisenberg.IsVacuum.modelInner_heisenbergOp_vacElem
  - New.Heisenberg.IsVacuum.map_eq_integral
  - New.Heisenberg.IsVacuum.integrated_eq_smul
  - New.Heisenberg.IsVacuum.eq_smul_one_of_commute
  - New.Heisenberg.IsVacuum.form_eq_mul_modelInner
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Heisenberg datum and its vacuum

This section gives the abstract setting of the chapter. The setting covers the real places, the finite places and the adeles at once. Its data are an abelian group $W$, an alternating bicharacter $\beta$ on $W$, a Haar measure $\mu$, and one function $e$, the vacuum. The vacuum defines a space of functions on $W$ by a reproducing kernel, and $W$ acts on this space by twisted translations. The section proves two results on this model: superposition, which writes every bounded map on the model as an integral over the translates of the vacuum, and Schur's lemma. Section 3 uses both to build the Weil operators and to compute their cocycle.

### The bicharacter

In the classical theory, a symplectic space $(W, \langle\,,\rangle)$ over a local field with a nontrivial additive character $\psi$ gives a Heisenberg group $W \times \mathbb{C}^1$ with the law $(x, s)(y, t) = (x + y, s t\, \psi(\tfrac12 \langle x, y \rangle))$. The function $\beta(x, y) = \psi(\tfrac12\langle x, y\rangle)$ is a bicharacter with $\beta(x, x) = 1$. The source keeps only this function.

**Definition (Heisenberg datum).** Let $W$ be an abelian group with a topology. A Heisenberg datum on $W$ is a function $\beta \colon W \times W \to \mathbb{C}$ with these properties.

1. $\beta(x + x', y) = \beta(x, y)\beta(x', y)$ and $\beta(x, y + y') = \beta(x, y)\beta(x, y')$.
2. $\beta(x, x) = 1$ for every $x$.
3. $|\beta(x, y)| = 1$ for all $x, y$.
4. $\beta$ is continuous on $W \times W$.

Lean: `New.Heisenberg` (Lib/Weil/Construction/HeisenbergModel.lean).

From these properties, $\beta(x, y)\beta(y, x) = \beta(x + y, x + y)\beta(x,x)^{-1}\beta(y,y)^{-1} = 1$, so $\overline{\beta(x, y)} = \beta(y, x)$ and $\beta(-x, y) = \beta(y, x)$. The source does not ask that $\beta$ is nondegenerate. Nondegeneracy is not a hypothesis of any result of this section. It is replaced by the existence of a vacuum, which is a stronger condition.

**Definition (Representation of a Heisenberg datum).** Let $X$ be a complex normed space. A representation of $\beta$ on $X$ is a family of bounded operators $\rho(x)$, $x \in W$, such that $\rho(x)\rho(y) = \beta(x, y)\rho(x + y)$, each $\rho(x)$ is an isometry, and $(x, v) \mapsto \rho(x) v$ is continuous on $W \times X$.

Lean: `New.Heisenberg.Rep` (Lib/Weil/Construction/HeisenbergModel.lean).

This is a representation of the Heisenberg group $W \times \mathbb{C}^1$ in which the center acts by the identity character, written as a projective representation of $W$ with the cocycle $\beta$.

### The vacuum

Let $\rho$ be an irreducible unitary representation of the Heisenberg group with a unit vector $\phi$. The matrix coefficient $e(x) = \langle \phi, \rho(x)\phi \rangle$ determines $\rho$. The Gaussian of the Fock model and the indicator of a self-dual lattice are such coefficients. The source turns the properties of a matrix coefficient into a definition.

**Definition (Vacuum).** Let $W$ carry a measure $\mu$. A function $e \colon W \to \mathbb{C}$ is a vacuum for $\beta$ and $\mu$ if it has these properties.

1. $e$ is continuous and integrable for $\mu$.
2. $e(0) = 1$, $e(-x) = e(x)$ and $\overline{e(x)} = e(x)$.
3. For all $x, y \in W$,
$$\int_W e(z)\,\beta(z, y)\,\beta(z + y, x)\,e(x - (z + y))\,d\mu(z) = e(y)\,e(x).$$

Lean: `New.Heisenberg.IsVacuum` (Lib/Weil/Construction/HeisenbergModel.lean).

The identity in (3) is the statement that $e$ is a matrix coefficient of a vector $\phi$ for which the projection $v \mapsto \langle \phi, v \rangle \phi$ is the integral $\int e(z)\rho(z)\,d\mu(z)$. With $x = y = 0$ it gives $\int e(z) e(-z)\,d\mu = 1$, and so the first two properties give the following lemma.

**Lemma.** If $e$ is a vacuum, then $\int_W |e|^2\,d\mu = 1$ and $|e(x)| \le 1$ for every $x$.

Lean: `New.Heisenberg.IsVacuum.integral_norm_sq_eq_one`, `New.Heisenberg.IsVacuum.norm_le_one` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* The first claim is the identity (3) at $x = y = 0$, since $e$ is even and real. For the second, put $y = x$ in (3). The right side is $e(x)^2$. The integrand on the left has absolute value $|e(z)|\,|e(-z)| = |e(z)|^2$, so the left side has absolute value at most $1$ by the first claim. So $|e(x)|^2 \le 1$. $\square$

**Example (A finite group of odd order).** Let $W$ be a finite abelian group of odd order, with the discrete topology. Let $\beta$ be a nondegenerate alternating bicharacter on $W$, and let $L \subset W$ be a subgroup with $\beta = 1$ on $L \times L$ and $|L|^2 = |W|$. Let $\mu$ be the counting measure divided by $|L|$, and let $e$ be the indicator of $L$. Then $e$ is a vacuum. For $x, y \in L$ the integrand of (3) is the indicator of $L$, and both sides are $1$. If exactly one of $x$ and $y$ is outside $L$, then the integrand is $0$, since $z \in L$ and $x - z - y \in L$ cannot both hold. If both are outside $L$, then the integrand is $0$ unless $x - y \in L$, and the sum is then $|L|^{-1}\beta(y, x)\sum_{z \in L}\beta(z, x + y)$. The character $z \mapsto \beta(z, x+y)$ of $L$ is trivial only if $x + y \in L$, because $L$ is its own orthogonal. Then $2y \in L$, and $y \in L$ because the order is odd. So the sum is $0$. Exercise 1 asks for the model of this vacuum.

### The model

**Definition (The model of a vacuum).** Let $W$ be a second countable abelian topological group with its Borel sets, let $\mu$ be a Haar measure on $W$, and let $e$ be a vacuum for $\beta$ and $\mu$. The model $\mathcal{H}_e$ is the space of the integrable functions $v$ on $W$ with
$$v(x) = \int_W v(y)\,\beta(y, x)\,e(x - y)\,d\mu(y) \quad \text{for every } x \in W.$$
It carries the norm $\|v\| = \int_W |v|\,d\mu$. The Heisenberg operators are $(\rho(y) v)(x) = \beta(y, x)\, v(x - y)$. The vacuum vector is $e$ itself. The inner product is $\langle v, w\rangle = \int_W \overline{v}\,w\,d\mu$, conjugate linear in $v$.

Lean: `New.Heisenberg.IsVacuum.Model`, `New.Heisenberg.IsVacuum.heisenbergRep`, `New.Heisenberg.IsVacuum.heisenbergOp`, `New.Heisenberg.IsVacuum.heisenbergOp_apply`, `New.Heisenberg.IsVacuum.vacElem`, `New.Heisenberg.IsVacuum.modelInner` (Lib/Weil/Construction/HeisenbergModel.lean).

The source proves these facts on the model. The elements of the model are continuous, and $|v(x)| \le \|v\|$, since $|\beta(y,x)e(x-y)| \le 1$. The model is a Banach space for the $L^1$ norm, because the defining identity passes to $L^1$ limits. The operators $\rho(y)$ map the model to itself, they are isometries, they satisfy $\rho(x)\rho(y) = \beta(x, y)\rho(x + y)$, and $(y, v) \mapsto \rho(y) v$ is continuous. So $\rho$ is a representation of $\beta$ on $\mathcal{H}_e$. The vacuum lies in the model by the identity (3) at $y = 0$. The inner product is a bounded sesquilinear form, since the elements are bounded by their norms. It is hermitian, it is invariant under the operators $\rho(y)$, and it is definite: if $\langle v, v \rangle = 0$, then $v = 0$, because $v$ is continuous.

**Lemma (Reproducing property).** For $v$ in the model and $x \in W$, $\langle \rho(x) e, v \rangle = v(x)$.

Lean: `New.Heisenberg.IsVacuum.modelInner_heisenbergOp_vacElem` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* The function $\rho(x)e$ is $y \mapsto \beta(x, y) e(y - x)$. Its conjugate is $\beta(y, x) e(x - y)$, since $e$ is real and even. So the inner product is the integral in the definition of the model at the point $x$. $\square$

**Remark (Formalization).** The classical model is a Hilbert space, for example $L^2(\mathbb{R}^n)$ in the Schrödinger model, or a space of holomorphic functions that are square integrable for a Gaussian measure in the Fock model. The source works with integrable functions and the $L^1$ norm. Reiter calls the corresponding space a Segal algebra, after Feichtinger: see the notes in Section 8. The inner product is a bounded form on this Banach space. The source does not form a Hilbert space from it. All the results of the chapter are about this $L^1$ space. The space $\mathcal{S}(V)$ of Section 6 is a space of this kind, so the theta functional is a bounded functional for the $L^1$ norm.

### Superposition

For a representation $R$ of $\beta$ on a Banach space $X$, the integrated action of the model is the bilinear map $(v, f) \mapsto \int_W v(y) R(y) f\,d\mu(y)$. It is bounded with norm at most $1$, since $R(y)$ is an isometry.

Lean: `New.Heisenberg.Rep.integrated`, `New.Heisenberg.Rep.integrated_apply` (Lib/Weil/Construction/HeisenbergModel.lean).

**Lemma (Superposition).** Let $Y$ be a complex Banach space and let $T \colon \mathcal{H}_e \to Y$ be a bounded linear map. For every $v$ in the model,
$$T v = \int_W v(y)\, T(\rho(y) e)\,d\mu(y).$$
So two bounded linear maps that agree on all the translates $\rho(y) e$ are equal.

Lean: `New.Heisenberg.IsVacuum.map_eq_integral`, `New.Heisenberg.IsVacuum.hom_ext`, `New.Heisenberg.IsVacuum.integrated_vacElem` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* The value at $x$ of $\int v(y)\rho(y)e\,d\mu(y)$ is $\int v(y)\beta(y, x)e(x - y)\,d\mu(y)$, which is $v(x)$ by the definition of the model. So $v = \int v(y)\rho(y)e\,d\mu(y)$ as an element of the model. A bounded operator passes under a Bochner integral. $\square$

The next lemma is the special case of the Moyal identity, or the orthogonality relations of the Heisenberg group, in which one vector is the vacuum.

**Lemma.** For $v$ and $w$ in the model,
$$\int_W v(y)\,\rho(y) w\,d\mu(y) = w(0)\, v.$$

Lean: `New.Heisenberg.IsVacuum.integrated_eq_smul` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* Both sides are bounded and linear in $v$ and in $w$. By [superposition](/decl/New.Heisenberg.IsVacuum.map_eq_integral/), applied twice, it is enough to take $v = \rho(y)e$ and $w = \rho(z)e$. Then the value of the left side at $x$ is $\beta(y, x)$ times the integral of the vacuum identity (3) at the points $z$ and $x - y$. The identity gives $e(z)\,\beta(y,x)\,e(x - y)$, and this is $w(0)\,v(x)$. $\square$

### Schur's lemma

**Theorem (Schur's lemma for the model).** Let $T$ be a bounded operator on the model that commutes with $\rho(y)$ for every $y \in W$. Then $T = (Te)(0)\cdot 1$.

Lean: `New.Heisenberg.IsVacuum.eq_smul_one_of_commute` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* Write $v = \int v(y)\rho(y)e\,d\mu(y)$ by [superposition](/decl/New.Heisenberg.IsVacuum.map_eq_integral/). Since $T$ commutes with each $\rho(y)$, $Tv = \int v(y)\rho(y)(Te)\,d\mu(y)$. By [the last lemma](/decl/New.Heisenberg.IsVacuum.integrated_eq_smul/) with $w = Te$, this is $(Te)(0)\,v$. $\square$

The classical Schur lemma needs the irreducibility of the representation. Here no irreducibility is proved or assumed. Its place is taken by the vacuum identity, which enters through the lemma above.

**Theorem (Invariant forms).** Let $W$ be locally compact. Let $B$ be a bounded sesquilinear form on the model, conjugate linear in the first variable, with $B(\rho(x) f, \rho(x) g) = B(f, g)$ for all $x \in W$ and all $f, g$. Then
$$B(v, w) = B(e, e)\,\langle v, w \rangle$$
for all $v$ and $w$ in the model.

Lean: `New.Heisenberg.IsVacuum.form_eq_mul_modelInner`, `New.Heisenberg.IsVacuum.integral_form_eq_mul_modelInner` (Lib/Weil/Construction/HeisenbergModel.lean).

*Proof.* The source proves a version for an integral $\int_Z B_z\,d\nu(z)$ of forms, and gets the theorem with a point mass. Invariance moves a translation from the second variable to the first: $B(f, \rho(x) u) = B(\rho(-x) f, u)$. Expand the first variable by superposition, use this move, and use [the Moyal lemma](/decl/New.Heisenberg.IsVacuum.integrated_eq_smul/). This gives $B(f, e) = B(e, e)\,\overline{f(0)}$. A translation of this identity gives $B(v, \rho(y) e) = B(e, e)\,\overline{v(y)}$, and the [reproducing property](/decl/New.Heisenberg.IsVacuum.modelInner_heisenbergOp_vacElem/) gives $\overline{v(y)} = \langle v, \rho(y)e\rangle$. Both sides are bounded and linear in $w$, so [superposition](/decl/New.Heisenberg.IsVacuum.map_eq_integral/) ends the proof. $\square$

The theorem is the uniqueness half of the Stone-von Neumann theorem in the form that the chapter needs. Section 6 uses the integral form, with a mean over the rational points, to prove that the theta functional is unique up to a scalar. Section 7 uses it for the integral of the inner products of the slices. Section 3 uses Schur's lemma for the cocycle relation of the Weil operators.
