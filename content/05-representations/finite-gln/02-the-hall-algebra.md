---
title: The ring of class functions
lean:
  - Lib/LocalGL/Green/HallAlgebra.lean
  - Lib/LocalGL/Green/CuspidalFunctions.lean
decls:
  - New.Hall
  - New.Hall.mul_simClassOf
  - New.Hall.evalGL
  - New.simClassOf_eq_dualMap
  - New.Hall.isUnit_constOne
  - New.Hall.moebius
  - New.Hall.sum_moebius_simClassOf_endOnSub
  - New.Hall.conj_moebius
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The ring of class functions

This section defines the ring in which the whole chapter computes. Its elements are complex functions on the similarity classes of square matrices over $k$, of all sizes. Its product is parabolic induction. The section proves that the ring is commutative, that the constant function $\mathbb{1}$ is a unit, and that the inverse $\mu$ of $\mathbb{1}$ is the Möbius function of the lattice of stable subspaces. Sections 3 to 6 use all of these facts.

Throughout the chapter, $k$ is a finite field and $q = |k|$. A *space* is a finite dimensional $k$-vector space, and an *endomorphism* is a $k$-linear map of a space to itself.

### Classes and functions

Two endomorphisms $g$ of $V$ and $g'$ of $V'$ are *similar* if there is a linear isomorphism $e : V \to V'$ with $e g e^{-1} = g'$. Similar endomorphisms act on spaces of the same dimension. The similarity class of an endomorphism of $k^n$ is the same as the conjugacy class of its matrix under $\mathrm{GL}_n(k)$.

**Definition (Similarity classes and the Hall space).** Let $\mathcal{C}(k)$ be the set of similarity classes of endomorphisms of the spaces $k^n$, for all $n \geq 0$. For an endomorphism $g$ of any space $V$, let $[g] \in \mathcal{C}(k)$ be its class. Each class $c$ has a dimension $\dim c$ and a characteristic polynomial $\chi_c \in k[X]$. Let $\mathcal{H}(k)$ be the complex vector space of all functions $\mathcal{C}(k) \to \mathbb{C}$. For a finite index set $I$ and $F \in \mathcal{H}(k)$, the *restriction* $F|_{\mathrm{GL}_I}$ is the function $g \mapsto F([g])$ on $\mathrm{GL}_I(k)$, where $g$ acts on $k^I$.

Lean: `New.Hall`, `New.SimClass`, `New.simClassOf`, `New.SimClass.charpoly`, `New.Hall.evalGL` (Lib/LocalGL/Green/HallAlgebra.lean).

For each $n$ there is exactly one class of dimension $0$: the zero map of the zero space. The classes of dimension $n$ are finite in number, and they include the classes of the singular matrices. An element of $\mathcal{H}(k)$ can have nonzero values in every dimension. Three elements recur. The *constant function* $\mathbb{1}$ has the value $1$ at every class. For $F \in \mathcal{H}(k)$ and $n \geq 0$, the *rank $n$ part* $[F]_n$ is $F$ on the classes of dimension $n$ and $0$ on the others. The element $1 = [\mathbb{1}]_0$ is the indicator function of the class of dimension $0$.

For a $g$-stable subspace $W$ of $V$, write $g|_W$ for the restriction of $g$ to $W$ and $g|_{V/W}$ for the map that $g$ induces on $V/W$.

**Lemma (The induction product).** For $F, H \in \mathcal{H}(k)$ there is a product $F * H \in \mathcal{H}(k)$ such that, for every endomorphism $g$ of every space $V$,
$$(F * H)([g]) = \sum_{W} F([g|_W]) \, H([g|_{V/W}]),$$
where $W$ runs over the $g$-stable subspaces of $V$.

Lean: `New.Hall.mul_simClassOf` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* Define $(F * H)(c)$ by the formula for a fixed endomorphism $g_c$ of $k^{\dim c}$ in the class $c$. The sum is finite, since $k$ is finite. If $e : V \to k^{\dim c}$ is an isomorphism with $e g e^{-1} = g_c$, then $W \mapsto e(W)$ is a bijection from the $g$-stable subspaces to the $g_c$-stable subspaces, and it preserves the classes of the restriction and of the quotient. So the formula holds for every $g$ in the class. $\square$

The function $F|_{\mathrm{GL}_I}$ is a class function on $\mathrm{GL}_I(k)$. Conversely, each class function on $\mathrm{GL}_n(k)$ is the restriction of an element of $\mathcal{H}(k)$, and the values of that element off $\mathrm{GL}_n(k)$ are free.

The product is parabolic induction. Let $a + b = n$, let $P \subset \mathrm{GL}_n(k)$ be the stabilizer of $W_0 = k^a \times 0$, and let $f$ and $h$ be class functions on $\mathrm{GL}_a(k)$ and $\mathrm{GL}_b(k)$. The function $f \otimes h$ on the Levi quotient $\mathrm{GL}_a(k) \times \mathrm{GL}_b(k)$ of $P$, pulled back to $P$ and induced to $\mathrm{GL}_n(k)$, has the value $|P|^{-1} \sum_x (f \otimes h)(x^{-1} g x)$ at $g$, where $x$ runs over the elements with $x^{-1} g x \in P$. The cosets $xP$ in this sum correspond to the $g$-stable subspaces $W = x W_0$ of dimension $a$, and the term of $xP$ is $f([g|_W]) \, h([g|_{V/W}])$. So for invertible $g$ the formula of the lemma is the sum over $a + b = n$ of the parabolically induced functions. This is the product of Green's ring $\bigoplus_n R(\mathrm{GL}_n(k))$ (Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter IV).

**Remark (Formalization).** The textbook ring has one summand for each $n$ and contains the class functions on the invertible matrices only. The source uses functions on all square matrices, invertible or not, with no grading. If $g$ is invertible, then $g|_W$ and $g|_{V/W}$ are invertible. So the values of $F * H$ at invertible classes depend only on the values of $F$ and $H$ at invertible classes, and restriction to the invertible classes is a ring map onto the completed textbook ring. The source cites Z. Chen, arXiv 2408.06191, Proposition 3.2 for this ring. The values at singular classes are used in one place: the inverse $\mu$ of $\mathbb{1}$, and so Green's function $C_\eta$, are defined in the larger ring. The theorems about characters restrict to $\mathrm{GL}_n(k)$ at the end.

### The ring laws

Commutativity is the only law that is not formal. The sum for $F * H$ puts $F$ on the subspace and $H$ on the quotient. The sum for $H * F$ puts them the other way. A duality exchanges subspaces and quotients, and it does not change classes.

**Theorem (The Hall ring).** With the pointwise sum and the product $*$, the space $\mathcal{H}(k)$ is a commutative ring with unit $1 = [\mathbb{1}]_0$. Complex scalars act pointwise and make it a $\mathbb{C}$-algebra. For every endomorphism $g$ of a space $V$, the dual map $g^*$ of $V^*$ has the same class as $g$.

Lean: the instances `CommRing (Hall k)` and `Algebra ℂ (Hall k)`, with `New.Hall.mul_simClassOf` and `New.simClassOf_eq_dualMap` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* First, $[g] = [g^*]$. Make $V$ a $k[X]$-module, with $X$ acting by $g$. By the structure theorem for modules over a principal ideal domain, $V$ is a finite product of cyclic modules $A = k[X]/I$. The dual of a product is the product of the duals, so it suffices to show that multiplication by $X$ on $A$ is similar to its dual. As a $k[X]$-module the dual $A^*$ is torsion, and its annihilator is $I$. Over a principal ideal domain there is $L \in A^*$ whose annihilator is the annihilator $I$ of the whole module. Then the bilinear form $(u, v) \mapsto L(uv)$ on $A$ is nondegenerate: if $L(uv) = 0$ for all $v$, then $u L = 0$ in $A^*$, so $u \in I$ and $u = 0$ in $A$. The form satisfies $L((Xu)v) = L(u(Xv))$. So the map $u \mapsto L(u \,\cdot)$ is an isomorphism $A \to A^*$ that carries $X$ to $X^*$.

Distributivity and the laws for $0$ hold term by term. In $(1 * F)([g])$ only $W = 0$ gives a nonzero term, and the term is $F([g])$. In $(F * 1)([g])$ only $W = V$ gives one. For associativity, both $((F * G) * H)([g])$ and $(F * (G * H))([g])$ are the sum over the chains $U \leq W$ of $g$-stable subspaces of $F([g|_U]) \, G([g|_{W/U}]) \, H([g|_{V/W}])$. On the left, $U$ runs over the stable subspaces of $W$. On the right, $W/U$ runs over the stable subspaces of $V/U$, and these correspond to the stable $W \geq U$.

For commutativity, use $[g] = [g^*]$. The map $W \mapsto W^\perp$ is a bijection from the $g$-stable subspaces of $V$ to the $g^*$-stable subspaces of $V^*$. It gives isomorphisms $W^\perp \cong (V/W)^*$ and $V^*/W^\perp \cong W^*$ that carry $g^*$ to the duals of $g|_{V/W}$ and $g|_W$. So
$$(H * F)([g]) = (H * F)([g^*]) = \sum_W H([(g|_{V/W})^*]) \, F([(g|_W)^*]) = (F * H)([g]),$$
by the first step applied to $g$, to $g|_{V/W}$ and to $g|_W$. The scalars come out of each finite sum. $\square$

### The constant function is a unit

**Theorem (The unit $\mathbb{1}$).** The constant function $\mathbb{1}$ is a unit of $\mathcal{H}(k)$.

Lean: `New.Hall.isUnit_constOne`, with `New.Hall.one_sub_constOne_pow_apply_eq_zero` and `New.Hall.mul_apply_eq_zero_of_dim_lt` (Lib/LocalGL/Green/HallAlgebra.lean).

*Proof.* Put $u = 1 - \mathbb{1}$. At the class of dimension $0$, the value of $u$ is $1 - 1 = 0$. If $F$ vanishes on the classes of dimension less than $m$ and $H$ vanishes on the classes of dimension less than $m'$, then $F * H$ vanishes on the classes of dimension less than $m + m'$: in each term, $\dim W < m$ or $\dim V/W < m'$. So $u^i$ vanishes on the classes of dimension less than $i$. At each class $c$ the series $\sum_{i \geq 0} u^i(c)$ has at most $\dim c + 1$ nonzero terms. Put $v = \sum_i u^i$, a pointwise finite sum. Each value of a product is a finite sum of products of values, so $(1 - u) * v = \sum_i (u^i - u^{i+1}) = 1$ at each class. As $1 - u = \mathbb{1}$, the element $v$ is the inverse of $\mathbb{1}$. $\square$

**Definition (The Möbius function $\mu$).** The element $\mu \in \mathcal{H}(k)$ is the inverse of $\mathbb{1}$. For $F \in \mathcal{H}(k)$, the element $F\mu$ is the pointwise product $c \mapsto F(c)\mu(c)$.

Lean: `New.Hall.moebius`, `New.Hall.mulMoebius` (Lib/LocalGL/Green/HallAlgebra.lean).

The source defines $\mu$ with the ring inverse of Mathlib, which is $0$ at an element that is not a unit. Since $\mathbb{1}$ is a unit, this junk value does not occur, and $\mu * \mathbb{1} = 1$.

**Lemma (The defining sums of $\mu$).** For every endomorphism $g$ of a space $V$,
$$\sum_W \mu([g|_W]) = 1([g]),$$
where $W$ runs over the $g$-stable subspaces of $V$. The right side is $1$ if $V = 0$ and $0$ otherwise. In particular $\mu$ has the value $1$ at the class of dimension $0$. The values of $\mu$ are real: $\overline{\mu(c)} = \mu(c)$ for every class $c$.

Lean: `New.Hall.sum_moebius_simClassOf_endOnSub`, `New.Hall.moebius_mul_constOne`, `New.Hall.moebius_eq_one_of_dim_eq_zero`, `New.Hall.conj_moebius` (Lib/LocalGL/Green/CuspidalFunctions.lean).

*Proof.* The left side is $(\mu * \mathbb{1})([g])$ by the lemma on the induction product, and $\mu * \mathbb{1} = 1$. For $V = 0$ the sum has one term, $\mu$ at the class of dimension $0$. The pointwise complex conjugation of $\mathcal{H}(k)$ preserves sums and the product, since each value of a product is a sum of products of values. It fixes $\mathbb{1}$. So it fixes the inverse $\mu$ of $\mathbb{1}$. $\square$

The lemma determines $\mu$ by recursion on the dimension: $\mu([g]) = -\sum_{W \neq V} \mu([g|_W])$ for $V \neq 0$. The $g|_W$-stable subspaces of $W$ are the $g$-stable subspaces of $V$ contained in $W$. So, by induction on $\dim W$, the number $\mu([g|_W])$ is the value $\mu_{\mathcal{L}}(0, W)$ of the Möbius function of the finite lattice $\mathcal{L}$ of $g$-stable subspaces. In particular $\mu([g]) = \mu_{\mathcal{L}}(0, V)$, and this explains the name.

For example, in dimension $1$ the stable subspaces are $0$ and $V$, so $\mu = -1$ at every class of dimension $1$. In dimension $2$ the recursion gives these values.

- The scalar $a \cdot 1$: every line is stable, so $\mu = -(1 - (q+1)) = q$.
- A map $a \cdot 1 + N$ with $N \neq 0$ nilpotent: the only stable line is $\ker N$, so $\mu = -(1 - 1) = 0$.
- A map with two distinct eigenvalues in $k$: two stable lines, so $\mu = -(1 - 2) = 1$.
- A map with no eigenvalue in $k$: no stable line, so $\mu = -1$.

For the scalar $a \cdot 1$ on $k^n$ the lattice is the lattice of all subspaces, and $\mu = \prod_{i < n} (-q^i) = (-1)^n q^{n(n-1)/2}$, by the classical formula for the subspace lattice. Section 4 proves a general form of this formula, and Section 4 also proves that $\mu$ vanishes off the semisimple classes, as at $a \cdot 1 + N$.

The values of $\mu$ are in fact integers, by the recursion. The chapter needs only that they are real.
