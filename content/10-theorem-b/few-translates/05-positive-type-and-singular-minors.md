---
title: Positive type and singular minors
lean:
  - New/Spanning/SecondMoment/PositiveType.lean
decls:
  - New.norm_sq_sum_tmul_eq_card_mul_sum
  - New.expect_addChar_dotProduct
  - New.orthonormal_addChar_div_sqrt
  - New.inner_addChar_invTranspose_smul_single
  - New.re_sum_addChar_dotProduct_mul_le
  - New.card_le_card_filter_vecMul_eq_zero
  - New.card_mul_sum_det_eq_zero_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Positive type and singular minors

This section proves a bound for the mass of a set of group elements where a determinant vanishes. [The chapter on moments](/chapter/moments/) uses it to show that the elements of the finite group $\bar G$ that are not "open" carry a small share of the second moment. The section does not use near isometries or spread. It uses the lemma on sums over a group from [the section on one translate](/chapter/few-translates/#one-translate) and the orthogonality of additive characters from [the notation of Volume 0](/chapter/notation/).

### The setting

Let $G$ be a finite group, and let $\Theta : G \to \mathbb{R}$ be of positive type: there are vectors $u_a$, $a \in G$, of a complex inner product space $H$ with $\langle u_a, u_b\rangle = \Theta(a^{-1}b)$ for all $a, b$. Let $k$ be a field with $q$ elements, let $n$ and $m$ be finite index sets, and let $\pi : G \to \mathrm{GL}_n(k)$ be a homomorphism. Write $\pi'(s) = (\pi(s)^{\mathsf T})^{-1}$ for the contragredient. For $x, z \in k^n$, write $x \cdot z = \sum_i x_iz_i$. The key identity is $(\pi'(s)x)\cdot(\pi(s)z) = x\cdot z$, so $\pi'$ acts on linear forms in the way that keeps the pairing.

The mass of a set $E \subseteq G$ is $\Theta(E) = \sum_{s \in E}\Theta(s)$. Two examples of positive type are useful. The constant $\Theta = 1$ has $u_a = u$ for one unit vector $u$. The indicator of a subgroup $\Gamma$ has $u_a$ the indicator of the coset $a\Gamma$ in $\ell^2(G/\Gamma)$, since $a\Gamma = b\Gamma$ if and only if $a^{-1}b \in \Gamma$. The second example shows how the lemma applies to sums over a subgroup.

### Stabilizers as norms

**Lemma (A stabilizer as a squared norm).** Let $\rho : G \to \mathrm{GL}_n(k)$ be a homomorphism, let $\Theta$ be of positive type with the vectors $u_a$, let $(c_x)_{x \in k^n}$ be an orthonormal family in an inner product space $E$, and let $x \in k^n$. Then

$$\Bigl\|\sum_{a \in G}c_{\rho(a)x}\otimes u_a\Bigr\|^2 = |G|\sum_{s \in G,\ \rho(s)x = x}\Theta(s).$$

Lean: `New.norm_sq_sum_tmul_eq_card_mul_sum` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* The inner product of the terms for $a$ and $b$ is $\langle c_{\rho(a)x}, c_{\rho(b)x}\rangle\Theta(a^{-1}b)$. By orthonormality the first factor is $1$ if $\rho(a)x = \rho(b)x$, that is, if $\rho(a^{-1}b)$ fixes $x$, and $0$ otherwise. So the inner product is $f(a^{-1}b)$ with $f(s) = \Theta(s)$ on the stabilizer of $x$ and $f(s) = 0$ elsewhere. [Lemma](/decl/New.inner_sum_sum_eq_card_mul/) gives $|G|\sum_sf(s)$. $\square$

The lemma turns a $\Theta$-mass of a stabilizer into a squared norm. This is the only use of positive type in the section: it makes masses of stabilizers into norms, so that the Cauchy-Schwarz inequality applies to them.

### Characters

Let $\psi$ be a primitive additive character of $k$, a homomorphism $\psi : (k, +) \to \mathbb{C}^\times$ such that $y \mapsto \psi(ty)$ is nontrivial for each $t \neq 0$. One exists for each finite field.

**Lemma (Orthogonality as a mean).** For $z \in k^m$,

$$\frac{1}{q^{|m|}}\sum_{x \in k^m}\psi(z\cdot x) = \begin{cases}1 & z = 0,\\ 0 & z \neq 0.\end{cases}$$

Lean: `New.expect_addChar_dotProduct` (New/Spanning/SecondMoment/PositiveType.lean).

This is the orthogonality of characters, divided by $q^{|m|}$.

**Lemma (Normalized characters).** The functions $c_x(\zeta) = \psi(-x\cdot\zeta)/\sqrt{q^{|n|}}$ on $k^n$, one for each $x \in k^n$, are orthonormal in $\ell^2(k^n)$.

Lean: `New.orthonormal_addChar_div_sqrt` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* $\langle c_x, c_y\rangle = q^{-|n|}\sum_\zeta\psi((x - y)\cdot\zeta)$, by $\overline{\psi(t)} = \psi(-t)$. By orthogonality the sum is $q^{|n|}$ if $x = y$ and $0$ otherwise. $\square$

The point of the second family is a change of basis. Let $e_z$ be the indicator of $z$ in $\ell^2(k^n)$, and write $g^{-\mathsf T} = (g^{\mathsf T})^{-1}$.

**Lemma (The change of basis).** Let $\psi$ be an additive character of $k$, let $r$ be real, let $g, g' \in \mathrm{GL}_n(k)$, and let $x, z \in k^n$. The function $\zeta \mapsto \psi(-(g^{-\mathsf T}x)\cdot\zeta)/r$ has the inner product $\psi(x\cdot g^{-1}g'z)/r$ with $e_{g'z}$.

Lean: `New.inner_addChar_invTranspose_smul_single` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* The inner product is the conjugate of the value at $g'z$, that is $\psi((g^{-\mathsf T}x)\cdot g'z)/r$, and $(g^{-\mathsf T}x)\cdot g'z = x\cdot g^{-1}g'z$. $\square$

For $r = \sqrt{q^{|n|}}$ the function is $c_{g^{-\mathsf T}x}$. The inner product depends on $g$ and $g'$ only through $g^{-1}g'$. So the inner products between the two families have the form of [Lemma](/decl/New.inner_sum_sum_eq_card_mul/).

### The character sum

**Lemma (Off-axis sums are small).** Let $\Theta$ be of positive type, let $x, z \in k^n$, and let $Y$ be a real number. Suppose the stabilizer of $x$ under $\pi'$ and the stabilizer of $z$ under $\pi$ each have $\Theta$-mass at most $Y$. Then

$$\operatorname{Re}\sum_{s \in G}\psi(x\cdot\pi(s)z)\,\Theta(s) \leq \sqrt{q^{|n|}}\,Y.$$

Lean: `New.re_sum_addChar_dotProduct_mul_le` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* Put $r = \sqrt{q^{|n|}}$ and work in $\ell^2(k^n)\otimes H$. Let

$$X_1 = \sum_{a \in G}c_{\pi'(a)x}\otimes u_a, \qquad X_0 = \sum_{a \in G}e_{\pi(a)z}\otimes u_a.$$

By the change of basis, $\langle c_{\pi'(a)x}\otimes u_a, e_{\pi(b)z}\otimes u_b\rangle = w(a^{-1}b)$ with $w(s) = \psi(x\cdot\pi(s)z)\Theta(s)/r$. So $\langle X_1, X_0\rangle = |G|\sum_sw(s)$ by [Lemma](/decl/New.inner_sum_sum_eq_card_mul/). The lemma on stabilizers, for the orthonormal families $c$ and $e$, gives $\|X_1\|^2 \leq |G|Y$ and $\|X_0\|^2 \leq |G|Y$. Then

$$\operatorname{Re}\sum_s\psi(x\cdot\pi(s)z)\Theta(s) = \frac{r}{|G|}\operatorname{Re}\langle X_1, X_0\rangle \leq \frac{r}{|G|}\cdot\frac{\|X_1\|^2 + \|X_0\|^2}{2} \leq rY,$$

by $\operatorname{Re}\langle X_1, X_0\rangle \leq \|X_1\|\|X_0\| \leq \frac{1}{2}(\|X_1\|^2 + \|X_0\|^2)$. $\square$

The proof uses the arithmetic mean $\frac{1}{2}(\|X_1\|^2 + \|X_0\|^2)$ in place of the geometric mean. With two separate bounds $Y_0$ and $Y_1$, the geometric mean would give $r\sqrt{Y_0Y_1}$. The source needs only one $Y$.

**Remark (Formalization).** The lemma has no hypothesis $\Theta \geq 0$ and no hypothesis $Y \geq 0$. If $Y < 0$, the bound $\|X_1\|^2 \leq |G|Y$ is false for every vector, so the hypotheses cannot hold. Positive type in Lean is the equation $\langle u_a, u_b\rangle = \Theta(a^{-1}b)$ with a real-valued $\Theta$. The textbook notion allows complex values; a real $\Theta$ of positive type has $\Theta(s^{-1}) = \Theta(s)$. The inner product of Mathlib is conjugate-linear in the first argument, and the proof uses $\overline{\psi(t)} = \psi(-t)$ to match it. The contragredient is `New.invTransposeGL` applied to $\pi(s)$, from Lib/General/LinearAlgebra/IntegralLattices.lean.

### The kernel of a singular matrix

**Lemma (The left kernel is large).** Let $Z$ be an $m \times m$ matrix over $k$ with $\det Z = 0$. Then at least $q$ vectors $y \in k^m$ satisfy $y^{\mathsf T}Z = 0$.

Lean: `New.card_le_card_filter_vecMul_eq_zero` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* There is $y \neq 0$ with $y^{\mathsf T}Z = 0$. Its $q$ multiples $ty$, $t \in k$, are distinct and lie in the left kernel. $\square$

### The main lemma

**Theorem (Singular minors have small mass).** Let $\pi : G \to \mathrm{GL}_n(k)$ be a homomorphism, let $A_0$ and $A_1$ be $n \times m$ matrices over $k$, and let $\Theta \geq 0$ be of positive type. Let $Y \geq 0$, and suppose that for every $v \in k^m$ with $v \neq 0$,

$$\sum_{s:\ \pi(s)A_0v = A_0v}\Theta(s) \leq Y \qquad\text{and}\qquad \sum_{s:\ \pi'(s)A_1v = A_1v}\Theta(s) \leq Y.$$

Then

$$q\sum_{s:\ \det(A_1^{\mathsf T}\pi(s)A_0) = 0}\Theta(s) \leq 2\,\Theta(G) + q^{|m|}\sqrt{q^{|n|}}\,Y.$$

Lean: `New.card_mul_sum_det_eq_zero_le` (New/Spanning/SecondMoment/PositiveType.lean).

*Proof.* Let $Z(s) = A_1^{\mathsf T}\pi(s)A_0$, an $m \times m$ matrix, and let $N(s)$ be the number of $y \in k^m$ with $y^{\mathsf T}Z(s) = 0$. Choose a primitive additive character $\psi$ of $k$.

*Step 1: count the kernel.* By the lemma on the left kernel, $q \leq N(s)$ when $\det Z(s) = 0$. Since $\Theta \geq 0$,

$$q\sum_{\det Z(s) = 0}\Theta(s) \leq \sum_{s \in G}N(s)\Theta(s) = \sum_{y \in k^m}\ \sum_{s:\ y^{\mathsf T}Z(s) = 0}\Theta(s).$$

*Step 2: detect the kernel by a character.* By orthogonality as a mean, for each $y$,

$$\sum_{s:\ y^{\mathsf T}Z(s) = 0}\Theta(s) = \frac{1}{q^{|m|}}\sum_{v \in k^m}\operatorname{Re}\sum_{s \in G}\psi(y^{\mathsf T}Z(s)v)\,\Theta(s).$$

*Step 3: the terms on the axes.* If $y = 0$ or $v = 0$, then $\psi(y^{\mathsf T}Z(s)v) = \psi(0) = 1$, and the inner sum is $\Theta(G)$.

*Step 4: the terms off the axes.* Let $y \neq 0$ and $v \neq 0$. Then $y^{\mathsf T}Z(s)v = (A_1y)\cdot\pi(s)(A_0v)$. The hypotheses for $y$ and for $v$ are those of the lemma on off-axis sums with $x = A_1y$ and $z = A_0v$. So the inner sum has real part at most $\sqrt{q^{|n|}}\,Y$.

*Step 5: add up.* Bound each inner sum by $[y = 0]\Theta(G) + [v = 0]\Theta(G) + \sqrt{q^{|n|}}Y$, which is valid in all four cases since $\Theta(G) \geq 0$ and $Y \geq 0$. The term $[y = 0]\Theta(G)$ gives $\Theta(G)$ after the sum over $y$ and the mean over $v$. The term $[v = 0]\Theta(G)$ has the mean $\Theta(G)/q^{|m|}$ over $v$, and the sum over the $q^{|m|}$ values of $y$ gives $\Theta(G)$. The last term gives $q^{|m|}\sqrt{q^{|n|}}Y$. $\square$

Divide by $q\,\Theta(G)$. The theorem says that the share of the mass on the singular set is at most $2/q$ plus $q^{|m| - 1}\sqrt{q^{|n|}}$ times the largest share of a stabilizer. So the lemma is useful when the stabilizers of nonzero vectors and forms are much smaller than $q^{-|m|}q^{-|n|/2}$ of the group, in the sense of $\Theta$.

**Remark (Formalization).** The character $\psi$ is chosen by an existence statement, from the primitive character into $\mathbb{C}$ that Mathlib gives for each finite field. The result does not depend on the choice. If some $v \neq 0$ has $A_0v = 0$, then every $s$ fixes $A_0v$, so the first hypothesis gives $\Theta(G) \leq Y$, and the bound holds trivially, since the left side is at most $q\,\Theta(G) \leq q^{|m|}Y$ when $|m| \geq 1$. If $m$ is empty, the determinant of the empty matrix is $1$, the singular set is empty, and the hypotheses are empty. The index types $n$ and $m$ are arbitrary finite types, so $|n|$ and $|m|$ are their numbers of elements.

### A model case for minors

Take $G = \mathrm{GL}_n(\mathbb{F}_q)$ with $n \geq 3$, $\pi$ the identity, $\Theta = 1$, $m = 1$, and $A_0 = A_1 = e_1$, the first standard basis vector. Then $\det(A_1^{\mathsf T}\pi(s)A_0) = s_{11}$, the upper left entry. The first column of $s$ is a uniformly distributed nonzero vector, so the true share of the $s$ with $s_{11} = 0$ is $(q^{n - 1} - 1)/(q^n - 1)$, which is a little less than $1/q$.

Now the bound. The group acts transitively on the nonzero vectors, so the stabilizer of each $v \neq 0$ has $|G|/(q^n - 1)$ elements. The same holds for $\pi'$, which also acts transitively on nonzero vectors. So $Y = |G|/(q^n - 1)$, and the theorem gives the share at most

$$\frac{2}{q} + \frac{q^{n/2}}{q^n - 1}.$$

For $n \geq 3$ the second term is smaller than $2/q$. So the lemma loses a factor of about $2$ against the truth. The factor $2$ comes from the two axes $y = 0$ and $v = 0$, which both count the whole mass.

### The application in the source

[The chapter on moments](/chapter/moments/) applies the theorem once, in `New.Filling.sum_leadingMinor_eq_zero_le` of New/Spanning/Unfolding/MomentBounds.lean. There $G$ is a subgroup $\Gamma$ of the residue group, $\pi$ is the reduction at a place $w$ above the first level prime $p_0$, with $q = p_0$ and $n$ the Bessel index set. The function $\Theta$ is a weight $\beta \geq 0$ of positive type. The columns of $A_0$ are the first $l$ frame vectors and those of $A_1$ are their linear forms, so the determinant is the leading minor of size $l$ of the Gram matrix of the frame. The hypothesis on stabilizers is $Y = \beta(\Gamma)/b^{6k}$. The source has $b^{10} \leq p_0$ and $p_0^l\sqrt{p_0^{|n|}} \leq b^{6k}$. So

$$b^{10}\sum_{\text{minor} = 0}\beta \leq p_0\sum_{\text{minor} = 0}\beta \leq 2\beta(\Gamma) + b^{6k}\cdot\frac{\beta(\Gamma)}{b^{6k}} = 3\beta(\Gamma),$$

and the share of a singular leading minor is at most $3b^{-10}$. This is the only use of the theorem in the source.

The file PositiveType.lean imports nothing from the later chapters of this volume. It imports the additive characters of Lib/General/Analysis/FiniteFourier.lean, the contragredient of Lib/General/LinearAlgebra/IntegralLattices.lean, and Lib/Adelic/Unitary/Defs.lean.
