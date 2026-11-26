---
title: Liouville, Minkowski and Hadamard
lean:
  - Lib/General/LinearAlgebra/MinorProducts.lean
  - Lib/General/LinearAlgebra/GramDeterminant.lean
decls:
  - New.hadamard_det_inequality
  - New.fischer_det_inequality
  - New.formGram
  - New.norm_det_formGram_le
  - New.norm_det_pairing_sq_le
  - New.det_gram_comp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Liouville, Minkowski and Hadamard

This section does the model cases of the chapter. The first is a single algebraic number, where the inequality is Liouville's. The second is a lattice in a Euclidean space, where the covolume of a family of lattice vectors is bounded above by Hadamard's inequality and below by integrality. The section then states the results of linear algebra that the later sections use.

### Rank one: Liouville's inequality

Let $\alpha$ be a nonzero algebraic integer of degree $n$, with conjugates $\alpha_1, \dots, \alpha_n$ in $\mathbb{C}$. The norm $N(\alpha) = \alpha_1 \cdots \alpha_n$ is a nonzero rational integer. So $|N(\alpha)| \geq 1$, and
$$\max_{1 \leq i \leq n} |\alpha_i| \geq 1.$$
This is Liouville's inequality in its simplest form. Liouville used it in 1844 to show that an algebraic number of degree $n$ has no rational approximations $p/q$ much better than $q^{-n}$.

Two features of the proof are the features of the whole chapter. First, the bound is for the largest conjugate, not for $\alpha$ itself: $\sqrt 2 - 1$ is small, but its conjugate $-\sqrt 2 - 1$ is large. Second, the proof uses that $\alpha$ is integral at every prime. If $D\alpha$ is an algebraic integer for a positive integer $D$, the same proof gives $\max_i |\alpha_i| \geq D^{-1}$.

The product formula puts the two features in one identity. Let $K$ be a number field, and for a place $v$ of $K$ let $|\cdot|_v$ be the absolute value that extends the usual absolute value of $\mathbb{Q}$ at the place below $v$, and $n_v = [K_v : \mathbb{Q}_p]$ its local degree (with $\mathbb{Q}_\infty = \mathbb{R}$). For $\alpha \in K^\times$,
$$\sum_v n_v \log |\alpha|_v = 0$$
(Neukirch, *Algebraic Number Theory*, Chapter III, §1). Let $\log^+ u = \max(0, \log u)$ for $u \geq 0$. Split the sum into the archimedean and the finite places, and bound each finite term by $n_v \log^+|\alpha|_v$. Since $\sum_{v \mid \infty} n_v = [K : \mathbb{Q}]$, the largest archimedean term satisfies
$$\max_{\sigma\colon K \to \mathbb{C}} \log |\sigma \alpha| \geq -h_{\mathrm{fin}}(\alpha), \qquad h_{\mathrm{fin}}(\alpha) = \frac{1}{[K:\mathbb{Q}]} \sum_{v \nmid \infty} n_v \log^+ |\alpha|_v.$$
The quantity $h_{\mathrm{fin}}(\alpha)$ is the finite part of the absolute logarithmic height of $\alpha$ (Bombieri and Gubler, *Heights in Diophantine Geometry*, Chapter 1). It measures the denominators of $\alpha$. For an algebraic integer it is $0$, and the inequality is the one above. For $\alpha = 1/D$ with $D \in \mathbb{Z}_{\geq 1}$ it is $\log D$, and the inequality is an equality.

**Example (A square root with a denominator).** Let $\alpha = \sqrt 2 / 2$. Its conjugates are $\pm \sqrt 2 / 2$, both of absolute value $2^{-1/2}$. At the unique place $v$ above $2$ of $K = \mathbb{Q}(\sqrt 2)$, we have $n_v = 2$ and $|\sqrt 2|_v = 2^{-1/2}$, so $|\alpha|_v = 2^{1/2}$. At the other finite places $\alpha$ is a unit. So $h_{\mathrm{fin}}(\alpha) = \frac{1}{2} \cdot 2 \cdot \frac{1}{2}\log 2 = \frac{1}{2}\log 2$, and $\max_\sigma \log|\sigma\alpha| = -\frac{1}{2}\log 2$. The inequality holds with equality.

Section 3 states this inequality in the form of the source: [Corollary](/decl/New.HeightLe.neg_le_of_norm_map_le/). The rank-one case of the main inequality of the chapter is the same statement for $|\alpha|^2$ (Section 6).

### Rank $n$: lattices, Minkowski and Hadamard

Let $\mathcal{L} \subset \mathbb{R}^n$ be a lattice with basis $e_1, \dots, e_n$. Its Gram matrix is $G = (\langle e_i, e_k \rangle)$, and its covolume is $\operatorname{covol}(\mathcal{L}) = (\det G)^{1/2}$, the volume of a fundamental domain. Let $v_1, \dots, v_n \in \mathcal{L}$ be linearly independent, and write $v_i = \sum_k u_{ik} e_k$ with $U = (u_{ik})$ an integer matrix. Then the Gram matrix of $v$ is $U G U^{\mathsf T}$, so
$$\det \mathrm{Gram}(v_1, \dots, v_n) = (\det U)^2 \det G = [\mathcal{L} : M]^2 \operatorname{covol}(\mathcal{L})^2,$$
where $M$ is the lattice spanned by the $v_i$. The second equality is $|\det U| = [\mathcal{L} : M]$, which follows from the elementary divisor theorem (Lang, *Algebra*, Chapter III, §7). The square of the index appears because the Gram determinant is a quadratic quantity. This is the origin of the term $2\delta$ in the inequality of the chapter.

Now suppose that $\mathcal{L}$ is *integral*: all the products $\langle e_i, e_k \rangle$ are integers. Then $\det G$ is a positive integer, and so $\det \mathrm{Gram}(v) \geq 1$ for every independent family $v$ of lattice vectors. This is the rank-$n$ form of Liouville's inequality. If the $v_i$ are not in $\mathcal{L}$, but $D v_i \in \mathcal{L}$ for all $i$, then $\det \mathrm{Gram}(v) \geq D^{-2n}$. More precisely, if a matrix $u$ with integer entries and $|\det u| = D'$ takes $v$ into $\mathcal{L}$, then $\det \mathrm{Gram}(v) \geq D'^{-2}$. This is the form that the definition of the index in Section 4 copies.

The upper bound comes from the lengths of the vectors. Hadamard's inequality says
$$\det \mathrm{Gram}(v_1, \dots, v_n) \leq \prod_{i=1}^n \|v_i\|^2.$$
Minkowski's second theorem says that this bound is sharp up to a factor that depends only on $n$. (Minkowski's first theorem, the lattice point theorem, is in Neukirch, Chapter I, §4.) So short lattice vectors give an upper bound for the covolume, and the integrality of the lattice gives a lower bound. If the vectors were too short, the two bounds would contradict each other.

This is the method of the source in its simplest form. Theorem A supplies short vectors, and Hadamard's inequality bounds their covolume above. The integral structure bounds it below. The source does not use Minkowski's theorem. A factor $c^{d_T}$ with $c > 1$ would cost $d_T \log c$, and neither Hadamard's inequality nor the lower bound of Section 6 has such a factor.

In the source the space is complex with a rational Gram matrix, the integral structure is given one prime at a time, and at each prime the lower bound may pass through a different map $\Theta_{\xi_\iota}$.

### Results of linear algebra

The source proves Hadamard's and Fischer's inequalities in its library. The textbook forms are in Horn and Johnson, *Matrix Analysis*, Section 7.8. The source states them for positive semidefinite complex matrices, without the cases of equality.

**Theorem (Fischer's inequality).** Let $A$ be a positive semidefinite Hermitian complex matrix, written in blocks $A = \begin{pmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{pmatrix}$ along a partition of its index set into two parts. Then $|\det A| \leq |\det A_{11}| \cdot |\det A_{22}|$.

Lean: `New.fischer_det_inequality` (Lib/General/LinearAlgebra/MinorProducts.lean).

*Proof.* The source derives it from the inequality of Ostrowski and Taussky, applied to the block triangular matrix $\Theta = \begin{pmatrix} A_{11} & 2A_{12} \\ 0 & A_{22} \end{pmatrix}$, with $\Theta + \Theta^* = 2A$. The textbook proof uses the Schur complement. $\square$

**Theorem (Hadamard's inequality).** Let $A$ be a positive semidefinite Hermitian complex $k \times k$ matrix. Then $|\det A| \leq \prod_{i=1}^k |a_{ii}|$.

Lean: `New.hadamard_det_inequality` (Lib/General/LinearAlgebra/MinorProducts.lean).

*Proof.* By induction on $k$. Split off the last row and column, and apply Fischer's inequality. $\square$

The later sections use Gram matrices with respect to a form given by a matrix.

**Definition (Gram matrix for a form).** For a square complex matrix $G$ indexed by a finite set $I$ and a family $v = (v_i)_{i \in S}$ of vectors in $\mathbb{C}^I$, let $\mathrm{formGram}(G, v)$ be the matrix with entries $v_i^* G v_k$, for $i, k \in S$.

Lean: `New.formGram` (Lib/General/LinearAlgebra/GramDeterminant.lean).

**Corollary (Hadamard's inequality for a form).** Let $G$ be positive semidefinite, let $v_1, \dots, v_n \in \mathbb{C}^I$, and let $h \in \mathbb{R}$ with $\operatorname{Re}(v_i^* G v_i) \leq e^h$ for all $i$. Then $|\det \mathrm{formGram}(G, v)| \leq e^{nh}$.

Lean: `New.norm_det_formGram_le` (Lib/General/LinearAlgebra/GramDeterminant.lean).

*Proof.* The matrix $\mathrm{formGram}(G, v)$ is positive semidefinite. Its diagonal entries are $v_i^* G v_i \geq 0$, so they are equal to their real parts. Apply [Theorem](/decl/New.hadamard_det_inequality/). $\square$

**Lemma (Cauchy-Schwarz for determinants).** Let $G$ be positive semidefinite and let $v = (v_i)_{i \in S}$ and $w = (w_i)_{i \in S}$ be two families in $\mathbb{C}^I$ with the same finite index set $S$. Then
$$|\det (v_i^* G w_k)_{i,k}|^2 \leq |\det \mathrm{formGram}(G, v)| \cdot |\det \mathrm{formGram}(G, w)|.$$

Lean: `New.norm_det_pairing_sq_le` (Lib/General/LinearAlgebra/GramDeterminant.lean).

*Proof.* The three matrices are the blocks of $\mathrm{formGram}(G, v \sqcup w)$, which is positive semidefinite. For a positive semidefinite matrix $\begin{pmatrix} P & Q \\ Q^* & R \end{pmatrix}$ with square blocks of the same size, $|\det Q|^2 \leq \det P \det R$. $\square$

The last result relates Gram determinants before and after a linear map. For a linear map $u\colon W \to H$ of inner product spaces with $W$ of finite dimension, let $\operatorname{normDet}(u) = \det(u^* u)^{1/2} \geq 0$.

**Lemma (Gram determinants under a linear map).** Let $W$ and $H$ be complex inner product spaces with $W$ of finite dimension, let $u\colon W \to H$ be linear, and let $x = (x_i)_{i \in S}$ be a family in $W$ with $\# S = \dim W$. Then
$$\det \mathrm{Gram}(u x_i)_{i \in S} = \operatorname{normDet}(u)^2 \cdot \det \mathrm{Gram}(x_i)_{i \in S}.$$

Lean: `New.det_gram_comp` (Lib/General/LinearAlgebra/GramDeterminant.lean).

*Proof.* Let $X\colon \mathbb{C}^S \to W$ send the standard basis to $x$. Both sides are squared volumes: $\det \mathrm{Gram}(ux) = \operatorname{normDet}(uX)^2$ and $\det \mathrm{Gram}(x) = \operatorname{normDet}(X)^2$. Since $\dim \mathbb{C}^S = \dim W$, the map $X$ is a square matrix in orthonormal bases, and $\operatorname{normDet}(uX) = \operatorname{normDet}(u)\operatorname{normDet}(X)$. $\square$

The hypothesis $\#S = \dim W$ matters, as Section 6 explains.
