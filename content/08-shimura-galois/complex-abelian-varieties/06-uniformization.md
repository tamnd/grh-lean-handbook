---
title: Uniformization and the theorem of Appell and Humbert
lean:
  - Lib/Shimura/Uniformisation/HolomorphicFamilies.lean
  - Lib/Shimura/Uniformisation/LieExponential.lean
  - Lib/Shimura/Uniformisation/AppellHumbert.lean
  - Lib/Shimura/ComplexTheta/AppellHumbertData.lean
decls:
  - New.ValuativeArc
  - New.bijective_restrict_genericPt
  - New.HasGermAt
  - New.HolomorphicAt
  - New.IsJet
  - New.IsFirstOrderConst
  - New.IsHolomorphicImmersionAt
  - New.Uniformisation
  - New.HasThetaCoords
  - New.Uniformisation.card_torsion
  - New.exists_holomorphic_chart
  - New.LineBundle.IsProjEmbedding.compactSpace_complexPoint
  - New.exists_lie_exponential
  - New.LineBundle.IsProjEmbedding.nonempty_uniformisation
  - New.exists_analyticAt_double_eq
  - New.exists_extension_double
  - New.exists_factor_of_automorphy
  - New.Uniformisation.appell_humbert
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Uniformization and the theorem of Appell and Humbert

In the textbook, $A(\mathbb{C})$ is a compact connected complex Lie group, so its exponential map is surjective with a lattice as kernel (Mumford, *Abelian Varieties*, Section 1). The theorem of Appell and Humbert then describes line bundles on $V/L$ by data $(H, \alpha)$ (Mumford, Section 2; Birkenhake and Lange, *Complex Abelian Varieties*, Section 2.2).

The source has no analytification of schemes. It builds a small analytic calculus from functions on points and proves two theorems: the uniformization $A(\mathbb{C}) \cong \mathbb{C}^d / L$, and the existence half of the theorem of Appell and Humbert.

### Complex points over a valuation ring

**Definition (Valuative arc).** A *valuative arc* is a valuation ring $O$ whose fraction field is $\mathbb{C}$, with its algebra map $O \to \mathbb{C}$ and the induced *generic point* $\operatorname{Spec} \mathbb{C} \to \operatorname{Spec} O$. The ring $\mathbb{C}$ itself and every valuation subring of $\mathbb{C}$ are valuative arcs.

Lean: `New.ValuativeArc` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

**Proposition.** Let $O$ be a valuative arc and $A$ a proper scheme over $\operatorname{Spec} O$. Restriction to the generic point is a bijection from the sections of $A$ over $O$ to the points of $A$ over $\mathbb{C}$ that lie above the generic point.

Lean: `New.bijective_restrict_genericPt` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

This is the valuative criterion of properness. The theorems of this section are stated for $O = \mathbb{C}$. A complex point of a scheme $A$ over $\mathbb{C}$ is a section $\operatorname{Spec} \mathbb{C} \to A$ (`New.ComplexPoint`).

### Holomorphic families of points

Let $X$ be a scheme, $P$ a finite-dimensional complex vector space and $\varphi \colon P \to X(\mathbb{C})$ a family of complex points.

**Definition (Holomorphic family).** The family $\varphi$ is *holomorphic at* $w_0 \in P$ if, for every open $U \subseteq X$ that contains $\varphi(w_0)$ and every function $f$ that is regular on $U$, the point $\varphi(w)$ lies in $U$ for all $w$ near $w_0$, and $w \mapsto f(\varphi(w))$ is analytic at $w_0$.

Lean: `New.HolomorphicAt` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean), the case of `New.HasGermAt` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean) for the property "analytic at $w_0$".

The derivative of a family is a point over a ring of dual numbers. For a complex vector space $M$, let $\mathbb{C} \oplus M$ be the trivial square-zero extension.

**Definition (Jet).** Let $\ell$ be a linear map from the dual of $P$ to $M$. A point $\tau \colon \operatorname{Spec}(\mathbb{C} \oplus M) \to X$ is a *jet* of $\varphi$ at $w_0$ for $\ell$ if, for every open $U$ that contains $\varphi(w_0)$ and every section $s$ of $\mathcal{O}_X$ over $U$, the point $\tau$ lies in $U$ and
$$s(\tau) = s(\varphi(w_0)) + \ell\big(d(s \circ \varphi)_{w_0}\big).$$

Lean: `New.IsJet` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

**Definition (First-order constant, immersion).** The family $\varphi$ is *constant to first order at* $w_0$ *in the direction* $v \in P$ if the constant point $\varphi(w_0)$, read over the dual numbers $\mathbb{C}[\varepsilon]$, is a jet of $\varphi$ for evaluation at $v$. Equivalently, $d(s \circ \varphi)_{w_0}(v) = 0$ for every local section $s$ near $\varphi(w_0)$. The family is a *holomorphic immersion at* $w_0$ if it is holomorphic at $w_0$ and constant to first order there only in the direction $0$.

Lean: `New.IsFirstOrderConst` and `New.IsHolomorphicImmersionAt` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

### Uniformizations

**Definition (Uniformization).** Let $O$ be a valuative arc, $A$ a commutative group object over $\operatorname{Spec} O$ and $V$ a finite-dimensional complex vector space. A *uniformization* of $A$ by $V$ consists of a homomorphism $e \colon V \to A(O)$ and a subgroup $L \subseteq V$ such that:

1. $L$ is a full-rank lattice: it is discrete and spans $V$ over $\mathbb{R}$;
2. $e$ is surjective;
3. $e(z) = 0$ if and only if $z \in L$;
4. on complex points, $e$ is a holomorphic immersion at every $z \in V$;
5. every homomorphism $\gamma \colon W \to A(O)$ from a finite-dimensional complex vector space that is holomorphic at $0$ is $\gamma = e \circ F$ for a continuous $\mathbb{C}$-linear map $F \colon W \to V$.

Lean: `New.Uniformisation` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

So $V/L \cong A(O)$ as groups. Condition 5 replaces the statement that $V$ is the Lie algebra.

**Theorem.** Let $u$ be a uniformization of $A$ by $V$ and $m \neq 0$ a natural number. Then exactly $m^{2 \dim_{\mathbb{C}} V}$ sections $y \in A(O)$ satisfy $m y = 0$.

Lean: `New.Uniformisation.card_torsion` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

*Proof.* Let $F$ be multiplication by $m$ on $V$. Since $e$ is surjective with kernel $L$, the $m$-torsion of $A(O)$ is $e(F^{-1}L) \cong F^{-1}L / L$. The index of $L$ in $F^{-1}L$ is $|\det_{\mathbb{C}} F|^2$, since $\det_{\mathbb{R}} F = |\det_{\mathbb{C}} F|^2$ (`New.relIndex_comap_eq_det_mul_conj_det`). Here $\det_{\mathbb{C}} F = m^{\dim V}$, so the index is $m^{2 \dim V}$. $\square$

The count is stated with `Nat.card`, which is $0$ for an infinite set. The statement gives a positive value, so it includes the finiteness of the torsion.

### Theta coordinates

**Definition (Theta coordinates).** Let $\varphi \colon P \to X(\mathbb{C})$ be a family of complex points, $L \subseteq P$ a lattice, $N$ a line bundle on $X$ with index set $\iota$, $(B, \chi)$ a pair of a form and a function on $P$, and $\theta \colon P \to \mathbb{C}^\iota$. Then $\theta$ is a family of *theta coordinates* of $\varphi$ for $N$ of type $(B, \chi)$ if:

1. $N$ is a linear system;
2. $(B, \chi)$ are Appell-Humbert data for $L$ in the sense of [Section 2](/chapter/complex-abelian-varieties/);
3. each coordinate $z \mapsto \theta_i(z)$ is a theta function of type $(B, \chi)$;
4. for every $z \in P$, the vector $\theta(z)$ is a vector of homogeneous coordinates of $\varphi(z)$ for $N$.

Lean: `New.HasThetaCoords` (Lib/Shimura/Uniformisation/HolomorphicFamilies.lean).

Theta coordinates behave well under pull-back, powers, translations and tensor products (`New.HasThetaCoords.pull` and its neighbours). For powers the type $(B, \chi)$ becomes $(mB, \chi^m)$.

### The exponential map

The topology on $A(\mathbb{C})$ is the coarsest one for which, for every open $U$ and every function $f$ regular on $U$, the set of points in $U$ at which $f$ takes values in a given open set of $\mathbb{C}$ is open.

**Theorem.** Let $A$ be a scheme over $\mathbb{C}$ that is smooth of relative dimension $d$, and $x$ a complex point of $A$. Then there are maps $\varphi \colon A(\mathbb{C}) \to \mathbb{C}^d$ and $\psi \colon \mathbb{C}^d \to A(\mathbb{C})$ with $\varphi(x) = 0$ such that: $\psi \circ \varphi$ is the identity near $x$, where $\varphi$ is continuous; $\varphi \circ \psi$ is the identity near $0$; $\psi$ is a holomorphic family at $0$; and for every holomorphic family $\gamma$ with $\gamma(w) = x$, the map $\varphi \circ \gamma$ is analytic at $w$ with derivative $0$ in every direction in which $\gamma$ is constant to first order.

Lean: `New.exists_holomorphic_chart` (Lib/Shimura/Uniformisation/LieExponential.lean).

**Proposition.** Let $A$ be a scheme over $\mathbb{C}$ and $N$ a linear system with finite index set that embeds $A$ in projective space. Then $A(\mathbb{C})$ is compact.

Lean: `New.LineBundle.IsProjEmbedding.compactSpace_complexPoint` (Lib/Shimura/Uniformisation/LieExponential.lean).

**Theorem.** Let $G$ be a compact commutative topological group and $V$ a finite-dimensional complex normed space. Let $\varphi \colon G \to V$ and $\psi \colon V \to G$ satisfy: $\varphi(0) = 0$; $\psi \circ \varphi$ is the identity near $0$; $\varphi$ is continuous near $0$; $\varphi \circ \psi$ is the identity near $0$; $\psi$ is continuous at $0$; and $(v, w) \mapsto \varphi(\psi(v) + \psi(w))$ is analytic at $0$. Then there is a homomorphism $e \colon V \to G$ such that:

1. the kernel of $e$ is a full-rank lattice;
2. $\psi \circ \varphi \circ e = e$ near $0$, the map $\varphi \circ e$ is analytic at $0$, and its derivative at $0$ is the identity;
3. the image of $e$ has finite index in $G$;
4. every homomorphism $\gamma \colon P \to G$ from a finite-dimensional complex normed space that is continuous at $0$ and with $\varphi \circ \gamma$ differentiable at $0$ is $\gamma = e \circ F$ for a continuous $\mathbb{C}$-linear $F \colon P \to V$.

Lean: `New.exists_lie_exponential` (Lib/Shimura/Uniformisation/LieExponential.lean).

*Idea of the proof.* For $v \in V$, the value $e(v)$ is a limit of $n \cdot \psi(b_n)$ with $n b_n \to v$, along a non-principal ultrafilter on $\mathbb{N}$. The limit exists because $G$ is compact. Since addition in the chart has derivative $(v, w) \mapsto v + w$ at $0$, these limits define a homomorphism, and $\varphi \circ e$ has derivative $1$ at $0$. The inverse function theorem gives property 2. The image of $e$ is an open subgroup of a compact group, so it has finite index. The kernel is discrete by property 2, and compactness forces it to span $V$ over $\mathbb{R}$. $\square$

**Remark (Formalization).** The ultrafilter is the Mathlib `hyperfilter` on $\mathbb{N}$, a choice that no formula determines. The theorem is an existence statement, so the choice does not enter its meaning.

The theorem gives only an image of finite index. The source does not prove that $A(\mathbb{C})$ is connected. It obtains surjectivity from the definition of an abelian scheme.

**Theorem (Uniformization).** Let $A$ be an abelian scheme over $\operatorname{Spec} \mathbb{C}$ that is smooth of relative dimension $d$. Let $N$ be a linear system on $A$ with finite index set that embeds $A$ in projective space. Then $A$ has a uniformization by $\mathbb{C}^d$.

Lean: `New.LineBundle.IsProjEmbedding.nonempty_uniformisation` (Lib/Shimura/Uniformisation/LieExponential.lean).

*Proof.* Take the chart at $0$ of the theorem on holomorphic charts. Addition and negation are morphisms of schemes, so $A(\mathbb{C})$ is a topological group, and it is compact by the proposition. Addition read in the chart is a holomorphic family on $\mathbb{C}^d \times \mathbb{C}^d$, hence analytic. The theorem on the exponential map gives $e$ with properties 1 to 4.

*Surjectivity.* Let $m \neq 0$ be the index of the image of $e$. Multiplication by $m$ on $A$ is surjective, by the definition of an abelian scheme. So every complex point $y$ is $m x$ for a complex point $x$. Since $A(\mathbb{C})/e(V)$ has order $m$, $m x \in e(V)$, so $y \in e(V)$.

*Holomorphic immersion.* By translation it is enough to work at $0$. There $e = \psi \circ (\varphi \circ e)$ near $0$, and $\varphi \circ e$ is analytic with derivative $1$. So $e$ is holomorphic at $0$, and a direction $v$ in which $e$ is constant to first order has $d(\varphi \circ e)_0(v) = v = 0$.

*Universality.* A homomorphism that is holomorphic at $0$ is continuous at $0$ and, read in the chart, differentiable at $0$. Property 4 applies. $\square$

**Remark (Formalization).** The divisibility condition in `New.IsAbelianScheme` is used exactly once in the source, in the surjectivity step above. With the textbook definition, surjectivity follows from the connectedness of $A(\mathbb{C})$. Nowhere is $A(\mathbb{C})$ compared with an analytic space in the sense of GAGA.

### The theorem of Appell and Humbert

For the elliptic model case of [Section 2](/chapter/complex-abelian-varieties/), let $N$ embed $E = \mathbb{C}/L$ as a plane cubic by the linear system $|3 \cdot 0|$. Pulled back to $\mathbb{C}$ and multiplied by one nowhere vanishing entire function, the three coordinates become theta functions of one type with Riemann form $3E_0$. By the dimension formula of [Section 3](/chapter/complex-abelian-varieties/), they span a space of dimension $\sqrt{9} = 3$.

**Theorem (Appell and Humbert, existence).** Let $A$ be a commutative group object over $\operatorname{Spec} \mathbb{C}$ and $u = (e, L)$ a uniformization of $A$ by $V$. Let $N$ be a linear system on $A$ with finite index set $\iota$ that embeds $A$ in projective space, and assume that the class $[N] \in \operatorname{Pic}(A)$ satisfies the parallelogram law. Then there are a form $B$, a function $\chi$ and a map $\theta \colon V \to \mathbb{C}^\iota$ such that $\theta$ is a family of theta coordinates of $z \mapsto e(z)$ for $N$ of type $(B, \chi)$, and the Riemann form of $B$ is positive.

Lean: `New.Uniformisation.appell_humbert` (Lib/Shimura/Uniformisation/AppellHumbert.lean).

The textbook theorem (Mumford, *Abelian Varieties*, Section 2) says that every line bundle on $V/L$ is $L(H, \alpha)$ for unique data. The source does not state uniqueness, and its proof chooses $(B, \chi)$.

*Idea of the proof.* Let $p, s \colon A \times A \to A$ be the projections. The parallelogram law says that the bundle
$$X = (p^*N \otimes s^*N)^{\otimes 2} \otimes \big((p + s)^* N \otimes (p - s)^* N\big)^{-1}$$
has trivial class, so it has a frame. Its values define a nowhere vanishing function $C(x, y)$, analytic in fixed charts. One looks for a nowhere vanishing function $\sigma$ on $V$ that trivializes $e^*N$. Restricted to the diagonal, the frame gives the *doubling equation*
$$\sigma(2z) = \sigma(z)^4\,\exp(q(z, z))\,C(e(z), e(z))$$
for a bilinear form $q$. It is first solved near $0$, then continued to all of $V$ by halving. The automorphy factor of $\sigma$ along $L$ is then of the Appell-Humbert form, and $\theta(z) = \sigma(z) \cdot (\text{homogeneous coordinates of } e(z))$ are theta functions.

**Lemma.** Let $V$ be a complex normed space and $f \colon V \to \mathbb{C}$ analytic at $0$. Then there are $g \colon V \to \mathbb{C}$ analytic at $0$ and a continuous bilinear form $q$ on $V$ with $g(2z) = 4 g(z) + f(z) + q(z, z)$ for all $z$ near $0$.

Lean: `New.exists_analyticAt_double_eq` (Lib/Shimura/Uniformisation/AppellHumbert.lean).

*Proof.* Write $f = \sum_n P_n$ with $P_n$ homogeneous of degree $n$. In degree $n$ the equation reads $(2^n - 4) G_n = P_n$. Put $G_n = (2^n - 4)^{-1} P_n$. Since $|2^n - 4| \geq 1$ for $n \neq 2$, the series $\sum G_n$ converges where $\sum P_n$ does. In degree $2$ the factor is $0$, and $q = -P_2$ absorbs the term. $\square$

**Remark (Formalization).** In degree $2$ the source uses the junk value $0^{-1} = 0$, so $G_2 = 0$. The form $q$ is exactly what this junk value leaves over. The equation for $\sigma$ is the exponential of this one, which is why $\sigma$ satisfies the doubling equation only up to the factor $\exp(q(z,z))$.

**Lemma.** Let $r > 0$, and let $\sigma_0, c \colon V \to \mathbb{C}$ satisfy $\sigma_0(2z) = \sigma_0(z)^4 c(z)$ whenever $\|z\| < r$ and $\|2z\| < r$. Then there is $\sigma \colon V \to \mathbb{C}$ that agrees with $\sigma_0$ on the ball of radius $r$ and satisfies $\sigma(2z) = \sigma(z)^4 c(z)$ for all $z \in V$.

Lean: `New.exists_extension_double` (Lib/Shimura/Uniformisation/AppellHumbert.lean).

*Proof.* Outside the ball put $\sigma(z) = \sigma(z/2)^4 c(z/2)$. This is a recursion on $\lfloor \|z\|/r \rfloor$, which halving lowers. $\square$

**Lemma.** Let $f \colon V \to \mathbb{C}$ have no zero, and let $L \subseteq V$ be a lattice. Assume that for each $l \in L$ the quotient $w \mapsto f(l + w)/f(w)$ has as logarithmic derivative a constant $\mathbb{C}$-linear form. Then there is a form $B$ on $V$, real-linear in the first variable and complex-linear in the second, such that $f(z + l) = f(z)\,\exp(B(l, z))\,f(l)/f(0)$ for $l \in L$ and $z \in V$, and $\operatorname{Re} B$ is symmetric.

Lean: `New.exists_factor_of_automorphy` (Lib/Shimura/ComplexTheta/AppellHumbertData.lean).

*Proof.* The logarithmic derivatives $a_l$ are additive in $l$, so they extend to a real-linear map on $V$, which defines $B$. Integration gives the factor of automorphy, and the two ways to compute $f(z + l + m)$ give the symmetry of $\operatorname{Re} B$. $\square$

*End of the proof of the theorem.* With $\sigma$ from the doubling equation, the last lemma gives $B$. Put $\chi(l) = \sigma(l)/\sigma(0)/\exp(B(l, l)/2)$. The doubling equation at points of $L$ gives $|\chi(l)| = 1$, by a computation that eliminates $\exp(q(l, l))$, and the factor of automorphy gives the cocycle rule of Appell-Humbert data. So the $\theta_i$ are theta functions of type $(B, \chi)$.

For positivity, assume that $E(v, iv) \leq 0$ for some $v \neq 0$. The Liouville argument of [Section 2](/chapter/complex-abelian-varieties/) (`New.IsAppellHumbert.apply_smul_of_nonpos`) makes $\theta(tv)$ proportional to $\theta(0)$ for all $t \in \mathbb{C}$. Since $N$ embeds $A$, $e(tv) = e(0)$, and condition 5 of a uniformization gives $v = 0$ (`New.Uniformisation.linear_ext`). $\square$

**Remark (Formalization).** The parallelogram law is a hypothesis here, as in [Section 4](/chapter/complex-abelian-varieties/). In the PEL families of the next chapter it is part of the data.
