---
title: Minkowski's theorems over E
lean:
  - Lib/Adelic/Reduction/MinkowskiTheorems.lean
decls:
  - New.lintegral_encard_rat_points
  - New.minkowski_first
  - New.exists_ne_zero_inv_mulVec_mem
  - New.Core.frameLength
  - New.Core.exists_successive_minima
  - New.Core.minkowski_second_theorem
  - New.exists_basis_frameLength_le_two_zpow
  - New.Core.encard_le_of_dyadic_box
  - New.Core.exists_eq_zero_of_zpow_mul_mem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Minkowski's theorems over E

This section proves the geometry of numbers that the finiteness results of the chapter need. The objects are adelic: an invertible adelic matrix $y$ defines a lattice of rational vectors, a length on it, and a covolume $|\det y|$. The section proves Minkowski's first theorem with an explicit constant, the upper half of Minkowski's second theorem, a version with powers of $2$, and a count of rational points in dyadic boxes. All constants are explicit in $f$, $n$ and the root discriminant of $E$.

### The classical theorems

Let $\Lambda \subset \mathbb{R}^m$ be a lattice of covolume $d(\Lambda)$, and let $C$ be a convex body that is symmetric about $0$. *Minkowski's first theorem* says that if $\operatorname{vol}(C) > 2^m d(\Lambda)$, then $C$ contains a nonzero point of $\Lambda$. The *successive minima* $\lambda_1 \le \dots \le \lambda_m$ of $\Lambda$ with respect to $C$ are defined by: $\lambda_j$ is the least $\lambda$ such that $\lambda C$ contains $j$ linearly independent points of $\Lambda$. *Minkowski's second theorem* says
$$\frac{2^m}{m!} d(\Lambda) \le \lambda_1 \cdots \lambda_m \operatorname{vol}(C) \le 2^m d(\Lambda).$$
Cassels, *An Introduction to the Geometry of Numbers*, proves the first theorem in Chapter III and the second in Chapter VIII. The proof of the first theorem is Blichfeldt's principle: if a measurable set $S$ has volume larger than $d(\Lambda)$, two points of $S$ differ by a nonzero point of $\Lambda$. The upper bound of the second theorem is the deep half. It needs a careful choice of a convex body inside $C$.

Over a number field $E$, the lattice is replaced by a finitely generated $\mathcal{O}_E$-module in $E^n$, and its covolume is measured in $(E \otimes \mathbb{R})^n$. The adelic form puts all lattices of $E^n$ in one family: for $y \in \mathrm{GL}_n(\mathbb{A}_E)$, the lattice is the set of $\xi \in E^n$ with $y^{-1}\xi$ integral at the finite places, and the length of $\xi$ is the size of $y^{-1} \xi$ at the infinite places. Bombieri and Vaaler proved the adelic forms of Minkowski's theorems and of Siegel's lemma (E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. 73 (1983)). The source cites this work for the method. Its list of references says that the work was found, but no place in it was confirmed.

### The adelic setting

Recall from [the adeles of the source](/chapter/adeles-hermitian-spaces/#adeles-of-a-number-field) that $\mathbb{A}_E = \mathbb{C}^f \times \mathbb{A}_{E,f}$, with one coordinate for each infinite place of $E$, since $E$ is totally complex. The ring $\hat{\mathcal{O}}_E$ of integral finite adeles has volume $2^f / \sqrt{|d_E|}$, and $E^n$ embedded diagonally is a lattice of covolume $1$ in $\mathbb{A}_E^n$. The *root discriminant* is $\mathrm{rd} = |d_E|^{1/[E:\mathbb{Q}]} = |d_E|^{1/(2f)}$. The idele modulus of $a \in \mathbb{A}_E^\times$ is $|a| = \prod_w |a_w|^2 \cdot |a_f|$, with the square at each complex place. For $y \in \mathrm{GL}_n(\mathbb{A}_E)$ we write $|\det y|$ for the idele modulus of its determinant. By the product formula, $|\det Y| = 1$ for $Y \in \mathrm{GL}_n(E)$ (`New.Core.ideleAbs_det_map_toAdele`).

The *unit box* in $\mathbb{A}_E$ is the set of $a$ with $|a_w| < 1$ at each infinite place and $a_f \in \hat{\mathcal{O}}_E$. Its volume is $(2\pi / \mathrm{rd})^f$. The box of radius $r$ has volume $(r^2 \pi \cdot 2/\mathrm{rd})^f$ (`New.volume_pi_ball_prod_integral`).

**Lemma (Counting on average).** Let $y \in \mathrm{GL}_n(\mathbb{A}_E)$ and let $S \subset \mathbb{A}_E^n$ be measurable. Then
$$|\det y| \cdot \operatorname{vol}(S) = \int \#\{\xi \in E^n : y^{-1}(\xi + x) \in S\} \, d\mu_{E^n}(x),$$
where $\mu_{E^n}$ is the quotient measure of $E^n \backslash \mathbb{A}_E^n$ and the count is in $[0, \infty]$.

Lean: `New.lintegral_encard_rat_points` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* The map $v \mapsto y^{-1} v$ carries the Haar measure of $\mathbb{A}_E^n$ to $|\det y|$ times itself. Compose with the unfolding map of [Section 2](/chapter/reduction-theory/#integration-on-a-quotient-by-a-cutoff), $(x, \xi) \mapsto \xi + x$. The measure of the preimage of $S$ is the left side, and by Tonelli it is the right side. $\square$

### Minkowski's first theorem

**Theorem (Minkowski's first theorem with multiplicity).** For $y \in \mathrm{GL}_n(\mathbb{A}_E)$,
$$|\det y| \le \big((2\,\mathrm{rd})^f\big)^n \cdot \#\{\xi \in E^n : \text{every entry of } y^{-1}\xi \text{ lies in the unit box}\}.$$
In particular, if $|\det y| > ((2\,\mathrm{rd})^f)^n$, there is a nonzero $\xi \in E^n$ with every entry of $y^{-1} \xi$ in the unit box.

Lean: `New.minkowski_first`, `New.exists_ne_zero_inv_mulVec_mem` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* Let $N$ be the count on the right. Let $S$ be the product of $n$ boxes of radius $1/2$. For each $x$, if $\xi_0$ and $\xi$ both have $y^{-1}(\xi + x) \in S$, then $y^{-1}(\xi - \xi_0)$ has entries that are differences of two points of the box of radius $1/2$, so they lie in the unit box. So $\xi \mapsto \xi - \xi_0$ injects the set counted in the lemma into the set counted by $N$. The lemma gives $|\det y| \operatorname{vol}(S) \le N$, since the quotient has volume $1$. The volume of $S$ is $((\pi/4) \cdot 2 / \mathrm{rd})^{fn}$, and
$$\big((2\,\mathrm{rd})^f\big)^n \operatorname{vol}(S) = \pi^{fn} \ge 1.$$
So $|\det y| \le ((2\,\mathrm{rd})^f)^n \operatorname{vol}(S) |\det y| \le ((2\,\mathrm{rd})^f)^n N$. If $|\det y|$ is larger than the constant, then $N > 1$, and one of the points counted is not $0$. $\square$

The constant is not the best one. The proof loses the factor $\pi^{fn}$. The argument needs only some explicit constant.

**Example.** Let $E = \mathbb{Q}(i)$, so $f = 1$, $d_E = -4$ and $\mathrm{rd} = 2$. Let $n = 1$ and let $y$ be the idele that is $t > 0$ at infinity and $1$ at the finite places. Then $|\det y| = t^2$, the lattice is $\mathbb{Z}[i]$, and the count is the number of Gaussian integers $\xi$ with $|\xi| < t$. The theorem says that this number is at least $t^2 / 4$. For $t = 1$ it is $1$, and the theorem allows a count of $1$, which is the point $0$. For $t > 4$ the count must exceed $4$, and indeed the disc of radius $t$ contains about $\pi t^2$ Gaussian integers.

### Lengths and successive minima

**Definition (Frame lattice and length).** Let $z \in \mathrm{GL}_n(\mathbb{A}_E)$. The *frame lattice* of $z$ is the set of $\xi \in E^n$ such that $z^{-1} \xi$ has integral finite part. The *length* $\|\xi\|_z$ of $\xi \in E^n$ is the Euclidean norm of the $fn$ complex coordinates of $z^{-1} \xi$ at all infinite places together.

Lean: `New.Core.frameLattice`, `New.Core.frameLength` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

The frame lattice spans $E^n$ over $E$, it has only finitely many points of length at most $r$ for each $r$, and its nonzero points have positive length (`New.Core.span_frameLattice`, `New.Core.finite_frameLattice_of_frameLength_le`, `New.Core.frameLength_pos`). For a space $V = (J, x)$ and $g \in G$, the frame lattice of $xg$ is the base lattice of the moved space $(J, xg)$.

**Lemma (Successive minima).** Let $L$ be a set that spans a vector space $W$ over a field $K$, and let $\ell$ be a real function on $W$ such that $\{v \in L : \ell(v) \le r\}$ is finite for every $r$. For every $k \le \dim W$ there are linearly independent $y_0, \dots, y_{k-1} \in L$ such that, for each $j$, $\ell(y_j) \le \ell(v)$ for every $v \in L$ outside the span of $y_0, \dots, y_{j-1}$.

Lean: `New.Core.exists_successive_minima` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* Choose $y_j$ in turn. Since $L$ spans $W$ and $j < \dim W$, some point of $L$ lies outside the span of the earlier ones. Among these points, the finiteness gives one of least length. $\square$

### Minkowski's second theorem

**Theorem (Minkowski's second theorem over $E$).** Let $z \in \mathrm{GL}_n(\mathbb{A}_E)$. There are linearly independent vectors $y_0, \dots, y_{n-1}$ in the frame lattice of $z$, with $\|y_0\|_z \le \dots \le \|y_{n-1}\|_z$, such that
$$|\det z| \cdot \prod_{j=0}^{n-1} \|y_j\|_z^{2f} \le (2 f n \, \mathrm{rd})^{fn}.$$

Lean: `New.Core.minkowski_second_theorem` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* Take the successive minima $y_j$ of the lemma for the frame lattice and the length $\|\cdot\|_z$. They are ordered by length, since $y_{j+1}$ is a candidate at step $j$. Let $Y \in \mathrm{GL}_n(E)$ have the columns $y_j$, and put $g = Y^{-1} z$. Then $|\det g| = |\det z|$ by the product formula. A vector $c \in E^n$ is in the frame lattice of $g$ if and only if $Yc$ is in the frame lattice of $z$. If $j$ is the last index with $c_j \ne 0$, then $Yc$ lies outside the span of $y_0, \dots, y_{j-1}$, so $\|c\|_g = \|Yc\|_z \ge \|y_j\|_z =: \alpha_j$.

It remains to prove $|\det g| \prod_j \alpha_j^{2f} \le (2fn\,\mathrm{rd})^{fn}$ under this condition (`New.Core.ideleAbs_det_mul_prod_le_of_le_frameLength`). At each infinite place $w$, the Gram-Schmidt process applied to the columns of $g_w^{-1}$, in the order of the indices, gives an orthonormal basis in which $g_w^{-1}$ is triangular. Consider the box whose $j$-th coordinate in this basis has absolute value less than $\alpha_j / \sqrt{fn}$ at every infinite place, with integral finite part. A nonzero lattice vector $c$ in this box would have last nonzero index $j$, and its length would be less than $\alpha_j$ by the triangular form, against the condition. So the box has no nonzero lattice vector, and Minkowski's first theorem bounds $|\det g|$ times its volume. The volume is $\prod_j (\alpha_j^2 / (fn))^f$ times the factors of the first theorem. This gives the constant $(fn)^{fn} ((2\,\mathrm{rd})^f)^n = (2 f n\,\mathrm{rd})^{fn}$. $\square$

**Remark (Formalization).** The source proves only the upper bound of the second theorem. The lower bound, that the product cannot be too small, is easy classically but the argument does not use it. The constant $(2fn\,\mathrm{rd})^{fn}$ is far from the classical $2^m$, because the box of the proof is a cube inscribed in a ball.

The argument uses the theorem once by name, in Siegel's lemma for the remaining terms of [Theorem B](/chapter/theorem-b-plan/). There it gives a basis of the solutions of a linear system with a bound on the product of the lengths. The library also uses it in its file on cuspidality of automorphic forms.

### Bases with dyadic lengths

The proofs of Section 6 count bases by their lengths up to a factor $2$. The source rounds the lengths of Minkowski's basis up to powers of $2$.

**Corollary (Dyadic form).** Let $y \in \mathrm{GL}_n(\mathbb{A}_E)$. There are a matrix $Y \in M_n(E)$ with $\det Y \ne 0$ and integers $x_0, \dots, x_{n-1}$ such that each row $Y_j$ of $Y$ lies in the frame lattice of $y$, $\|Y_j\|_y \le 2^{x_j}$, and
$$|\det y| \cdot (2^{2f})^{\sum_j x_j} \le (8 f n \, \mathrm{rd})^{fn}.$$

Lean: `New.exists_basis_frameLength_le_two_zpow` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* Let $x_j = \lceil \log_2 \|y_j\|_y \rceil$ for the basis of the theorem. Then $2^{x_j} \le 2 \|y_j\|_y$, so $(2^{2f})^{\sum x_j} \le 4^{fn} \prod \|y_j\|^{2f}$. The factor $4^{fn}$ turns $2fn\,\mathrm{rd}$ into $8 fn\,\mathrm{rd}$. $\square$

The source states the vectors as the rows of $Y$. The rows and the columns play the same role here: only the invertibility of $Y$ and the membership of each vector are used.

### Counting points in a dyadic box

The last result of the section counts rational vectors in a box stretched by powers of $2$ at the infinite places. Let $\tau$ be the idele that is $2$ at every infinite place and $1$ at the finite places (`New.Core.twoAtInfinity`).

**Proposition (Points in a dyadic box).** Let $B \subset \mathbb{A}_E^n$ be compact. There is a finite $C \ge 0$ with the following property. Let $x \in \mathbb{Z}^n$, and let $\xi_a$, for $a$ in a set $S$, be distinct vectors in $E^n$ such that the vector with entries $\tau^{-x_i} \xi_{a,i}$ lies in $B$ for every $a$. Then
$$\# S \le C \cdot \big(2^{f \sum_i \max(x_i, 0)}\big)^2.$$

Lean: `New.Core.encard_le_of_dyadic_box` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* Let $F$ be a compact set that meets every translate of $E^n$ in $\mathbb{A}_E^n$. Let $K = \mathrm{box} \cdot B + \mathrm{box} \cdot F$, a compact set, and let $D$ be the diagonal matrix with entries $\tau^{\max(x_i, 0)}$. For each $v \in \mathbb{A}_E^n$, choose $\eta \in E^n$ with $\eta + v \in F$. The shifted vectors $\xi_a + \eta$ are distinct and satisfy $D^{-1}(\xi_a + \eta + v) \in K$. So $\# S$ is at most the count of the lemma on counting on average, for every $v$. The mean of that count is $|\det D| \operatorname{vol}(K) = 2^{2f \sum \max(x_i, 0)} \operatorname{vol}(K)$. The quotient has volume $1$, so a number below all values of the count is below its mean. Take $C = \operatorname{vol}(K)$. $\square$

**Proposition.** Let $B \subset \mathbb{A}_E$ be compact. There is an integer $c$ such that, for every integer $e < c$, every $a \in E$ with $\tau^{-e} a \in B$ is $0$.

Lean: `New.Core.exists_eq_zero_of_zpow_mul_mem` (Lib/Adelic/Reduction/MinkowskiTheorems.lean).

*Proof.* The set $\Phi$ of $a \in E$ with $a$ in $\mathrm{box} \cdot B$ is finite, since $E$ is discrete in $\mathbb{A}_E$. So some natural number $N$ is not a quotient of two elements of $\Phi$. Take $c = -N$. If $e < -N$ and $a \ne 0$ has $\tau^{-e} a \in B$, then $a$ and $N a$ both lie in $\Phi$, since $2^e \le 1$ and $N 2^e \le 1$. This is a contradiction. $\square$

The second proposition says that a nonzero rational vector cannot be made arbitrarily small at the infinite places while it stays integral. It is the idea behind the positivity of the first minimum in [Section 5](/chapter/reduction-theory/#the-first-minimum-and-the-height).
