---
title: The class count
lean:
  - New/UpperBound/Size/ClassCount.lean
decls:
  - New.Space.norm_map_mul_apply_le
  - New.Space.norm_gram_apply_le_cube
  - New.Space.isIntegral_conjTranspose_mul_apply
  - New.Space.stdClasses_eq_of_gram_eq
  - New.Space.card_stdClasses_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The class count

A value of a chain of lifts is a sum over classes, one set of classes for each stage. This section gives an explicit bound for the number of classes of the standard level. The bound is crude, but it is explicit, and its logarithm is a polynomial in the rank and the degree. The next section turns it into the bound $\exp(x^{30})$ at the data.

### The setting

Let $E$ be a CM field with $f$ infinite places, and let $n$ be a finite index set with $r = \#n$ elements. Let $G_f$ be the finite adelic points of the unitary group of the standard form $\sum_{i\in n} z_i\bar z_i$, and let $\Gamma$ be its group of rational points. For a subgroup $K$ of $G_f$, the set of classes is $\Gamma\backslash G_f/K$ ([automorphic forms](/chapter/automorphic-forms/)). The standard level is $K_0 = G_f \cap \mathrm{GL}_n(\hat{\mathcal O})$, the stabilizer of the lattice $\hat{\mathcal O}^n$ ([adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/)). For each infinite place $w$ of $E$, $\Phi_w$ is the chosen complex embedding at $w$.

A finite adelic matrix is *integral* if all its entries lie in $\hat{\mathcal O}$. An element of $E$ that lies in $\hat{\mathcal O}$ is an algebraic integer.

Let $N \ge 1$ be a natural number that lies in the different of $E$. Put
$$c = 6N(fr)^2,$$
the constant of short bases. Two results from other volumes are used.

- *Short bases* ([reduction theory](/chapter/reduction-theory/)). For every $g \in G_f$ there is $Y \in \mathrm{GL}_n(E)$ such that $g^{-1}Y$ is integral and $|\varphi(Y_{ij})| \le c$ for every complex embedding $\varphi$ of $E$ and all $i, j$.
- *Bounded approximation* ([the anatomy of a term](/chapter/anatomy-of-a-term/)). For every finite adele $y$ there is $\alpha \in E$ with $y - \alpha \in \hat{\mathcal O}$ and $|\Phi_w(\alpha)| \le (2f)^2N$ at every infinite place $w$. This is the lemma `New.exists_principal_near_of_mem_differentIdeal` with the archimedean target $0$ and $d = N$.

### Three lemmas on matrices

**Lemma (Size of a product).** Let $\varphi$ be a complex embedding of a field $E$, and let $M$, $M'$ be $n \times n$ matrices over $E$. If $|\varphi(M_{ij})| \le \alpha$ and $|\varphi(M'_{ij})| \le \beta$ for all $i, j$, then $|\varphi((MM')_{ij})| \le r\alpha\beta$ for all $i, j$.

Lean: `New.Space.norm_map_mul_apply_le` (New/UpperBound/Size/ClassCount.lean).

*Proof.* The entry is $\sum_k M_{ik}M'_{kj}$. Its image has absolute value at most $\sum_k |\varphi(M_{ik})||\varphi(M'_{kj})| \le r\alpha\beta$. $\square$

**Lemma (Size of the Gram matrix).** Let $w$ be an infinite place of the CM field $E$, and let $Y$, $X$ be $n\times n$ matrices over $E$ with $|\Phi_w(Y_{ij})| \le c$ and $|\Phi_w(X_{ij})| \le (2f)^2N$ for all $i, j$. Then all entries of $Y^{\mathsf H}Y$ and of $Y^{\mathsf H}YX$ have absolute value at most $c^3$ under $\Phi_w$.

Lean: `New.Space.norm_gram_apply_le_cube` (New/UpperBound/Size/ClassCount.lean).

*Proof.* The entries of $Y^{\mathsf H}$ are the conjugates of those of $Y$. Since $E$ is CM, $\Phi_w$ commutes with complex conjugation, so these entries are also bounded by $c$. By the lemma on products, the entries of $Y^{\mathsf H}Y$ are at most $rc^2$. As $r \le (fr)^2 \le c$, this is at most $c^3$. Apply the lemma again: the entries of $Y^{\mathsf H}YX$ are at most
$$r\cdot rc^2\cdot(2f)^2N = 4N(fr)^2\cdot c^2 \le c\cdot c^2 = c^3,$$
since $4N(fr)^2 \le 6N(fr)^2 = c$. $\square$

**Lemma (Integral inner products).** Let $g \in G_f$, and let $Y$, $Z$ be $n \times n$ matrices over $E$ such that $gY$ and $gZ$ are integral. Then the entries of $Y^{\mathsf H}Z$ are algebraic integers.

Lean: `New.Space.isIntegral_conjTranspose_mul_apply` (New/UpperBound/Size/ClassCount.lean).

*Proof.* The element $g$ is unitary for the standard form, so $g^{\mathsf H}g = 1$. Then $Y^{\mathsf H}Z = (gY)^{\mathsf H}(gZ)$ as adelic matrices. The right side is a product of integral matrices, so it is integral. Its entries lie in $E$ and in $\hat{\mathcal O}$, so they are algebraic integers. $\square$

### The class is fixed by its Gram data

**Lemma (Equal Gram matrices).** Let $g, g' \in \Gamma\backslash G_f/K_0$ be two classes with chosen representatives $g_\circ$, $g'_\circ$. Let $Y, Y' \in \mathrm{GL}_n(E)$ with $Y'^{\mathsf H}Y' = Y^{\mathsf H}Y$. Put $A = g_\circ^{-1}Y$ and $A' = g_\circ'^{-1}Y'$. If $A'A^{-1}$ is integral, then $g' = g$.

Lean: `New.Space.stdClasses_eq_of_gram_eq` (New/UpperBound/Size/ClassCount.lean).

*Proof.* Put $\gamma = YY'^{-1} \in \mathrm{GL}_n(E)$. From $Y'^{\mathsf H}Y' = Y^{\mathsf H}Y$ we get $\gamma^{\mathsf H}\gamma = Y'^{-\mathsf H}Y^{\mathsf H}YY'^{-1} = 1$. So $\gamma$ is a rational isometry, and $\gamma \in \Gamma$. Put $k = (\gamma g'_\circ)^{-1}g_\circ$. Then
$$k = g_\circ'^{-1}\gamma^{-1}g_\circ = g_\circ'^{-1}Y'Y^{-1}g_\circ = A'A^{-1}.$$
So $k$ is unitary and integral, that is $k \in K_0$. Then $g_\circ = \gamma g'_\circ k$, and the two representatives lie in the same double coset. So $g = g'$. $\square$

### The count

**Theorem (Class count of the standard level).** Let $E$ be a CM field with $f$ infinite places, $N \ge 1$ a natural number in the different of $E$, $n$ an index set of size $r$, and $c = 6N(fr)^2$. Then
$$\#\bigl(\Gamma\backslash G_f/K_0\bigr) \le (1 + 2c^3)^{4fr^2}.$$

Lean: `New.Space.card_stdClasses_le` (New/UpperBound/Size/ClassCount.lean).

*Proof.* *The invariant.* For each class $g$ let $g_\circ$ be its chosen representative. Take a short basis $Y_g$: then $g_\circ^{-1}Y_g$ is integral, and the entries of $Y_g$ are at most $c$ at every embedding. Put $A_g = g_\circ^{-1}Y_g \in \mathrm{GL}_n(\mathbb A_f)$. For each entry of $A_g^{-1}$ take a bounded approximation, and let $X_g$ be the matrix of these approximations. So $A_g^{-1} - X_g$ is integral, and the entries of $X_g$ are at most $(2f)^2N$ at every infinite place. Put $G_g = Y_g^{\mathsf H}Y_g$. The invariant of $g$ is the pair $(G_g, G_gX_g)$, a vector of $2r^2$ elements of $E$.

*Integrality.* For classes $g$, $g'$,
$$A_{g'}A_g^{-1} - A_{g'}X_g = A_{g'}(A_g^{-1} - X_g)$$
is integral, as a product of integral matrices. With $g' = g$ this gives that $1 - A_gX_g$ is integral, so $A_gX_g = g_\circ^{-1}(Y_gX_g)$ is integral. Now the lemma on integral inner products, applied to $g_\circ^{-1}$ and the pairs $(Y_g, Y_g)$ and $(Y_g, Y_gX_g)$, shows that all entries of $G_g$ and of $G_gX_g = Y_g^{\mathsf H}(Y_gX_g)$ are algebraic integers.

*Size.* By the lemma on the Gram matrix, all entries of $G_g$ and $G_gX_g$ have absolute value at most $c^3$ at every infinite place.

*Injectivity.* Let $(G_{g'}, G_{g'}X_{g'}) = (G_g, G_gX_g)$. The matrix $G_g$ is invertible, so $X_{g'} = X_g$. Then
$$A_{g'}A_g^{-1} = \bigl(A_{g'}A_g^{-1} - A_{g'}X_g\bigr) + A_{g'}X_{g'}$$
is a sum of two integral matrices. The lemma on equal Gram matrices gives $g' = g$.

*The count.* The invariant maps the classes injectively to vectors of $2r^2$ algebraic integers whose conjugates are at most $c^3$. Embed such a vector in $\mathbb C^{2r^2\times f}$ by the $f$ embeddings $\Phi_w$. This is a real space of dimension $2r^2\cdot f\cdot 2 = 4fr^2$. Two different images are at distance at least $1$ in the sup norm: if all conjugates of a difference of algebraic integers are less than $1$, then its norm is an integer of absolute value less than $1$, so the difference is $0$. The images lie in the ball of radius $c^3$. A packing argument gives at most $(1 + 2c^3)^{4fr^2}$ points: the disjoint balls of radius $\tfrac12$ around the points lie in the ball of radius $c^3 + \tfrac12$, and the ratio of volumes is $(1 + 2c^3)^{4fr^2}$. This count is the lemma `New.Filling.encard_le_of_isIntegral_norm_le` of [the anatomy of a term](/chapter/anatomy-of-a-term/). $\square$

**Remark (Formalization).** The representatives $g_\circ$, the short bases $Y_g$ and the approximations are taken by `choose`, and the representatives are the values of `Quotient.out`. The proof does not depend on these choices. The theorem has the instance hypothesis that $N \neq 0$; the bounded approximation needs $N \neq 0$, since $0$ lies in every ideal. The count of the packing lemma is a bound on `Set.encard` in $\mathbb N\cup\{\infty\}$, and the proof turns it into a bound on `Nat.card`. A set with infinitely many classes would have `Nat.card` equal to $0$, a junk value, but the packing lemma shows that the set is finite, so the bound is the true one.

### An example

Take $E = \mathbb Q(i)$, so $f = 1$, and $n$ with one element. Then $G_f$ is the group of finite ideles $u$ of $E$ with $u\bar u = 1$, and the classes are the classes of the norm one ideles modulo the rational norm one elements and the units of $\hat{\mathcal O}$. The different of $\mathbb Z[i]$ is $(2)$, so $N = 2$ is allowed. Then $c = 6\cdot 2\cdot 1 = 12$ and the bound is $(1 + 2\cdot 12^3)^4 = 3457^4$. The bound is far from sharp: it counts all pairs of small algebraic integers, and most of these pairs are not the Gram data of a class. Only its logarithm matters in the argument, and the logarithm is $4\log 3457 \approx 32.6$.

For the class of $1$, the short basis is $Y = (1)$, the Gram matrix is $G = (1)$, and one may take $X = (0)$. The invariant is the pair $(1, 0)$.

### The size of the bound

The logarithm of the bound is
$$4fr^2\log(1 + 2c^3) \le 4fr^2\bigl(\log 3 + 3\log(6N) + 6\log(fr)\bigr).$$
So it is linear in $f$ and in $\log N$, and quadratic in the rank $r$ up to a logarithm. At the data, $f \le x^{12}$ and $r \le 2n_m \le 2e^{12}x^{11/2}$. So the logarithm of the class count is at most a power of $x$ times $\log N$, and much smaller than $fa$. This is the only property of the count that the argument uses.
