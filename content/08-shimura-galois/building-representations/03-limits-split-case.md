---
title: Limits and the split case
lean:
  - Lib/GaloisRep/WeightCongruence.lean
  - Lib/GaloisRep/Main/SplitCase.lean
decls:
  - New.stoneWeierstrass_ultrametric
  - New.padicModel_mem_uniformClosure
  - New.GaloisRep.exists_padicModel_hecke_contraction
  - New.GaloisRep.exists_attached_of_isApproximatingMonoid
  - New.GaloisRep.sphericalCompat_of_split
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Limits and the split case

The seed of Section 2 needs two local hypotheses that a general form does not satisfy: a cuspidal type at one place and free jumps at one embedding. This section removes both by an $\ell$-adic limit. Every form of odd rank is an $\ell$-adic uniform limit of combinations of forms that satisfy the hypotheses. The traces of their representations converge, and the limit is the trace of a representation attached to the form. The price is that the limit is attached only in the approximate sense of [the previous chapter](/chapter/attached-representations/). The result of the section is [the split case](/decl/New.GaloisRep.sphericalCompat_of_split/). It holds over a field that contains $\mathbb Q(\sqrt{-D})$, at places over split primes of $\mathbb Q(\sqrt{-D})$. Section 4 removes that restriction by base change.

### The $\ell$-adic model of a form

The classical idea is due to Serre, Hida and others: an algebraic form of any weight becomes, after a twist by its weight at $\ell$, a continuous $\ell$-adic function on one compact space, and the weight disappears. Let $f$ be a form of weight $\kappa$ on the definite unitary group of rank $N$. It satisfies $f(\gamma g) = \rho_\kappa(\gamma) f(g)$ for rational $\gamma$. Let $z(g) \in \prod_\tau \mathrm{GL}_N(\bar{\mathbb Q}_\ell)$ be the family of components of $g$ at the places above $\ell$, read through the embeddings $\tau$ (Lean: `New.padicComponents`). The $\ell$-adic model of $f$ is the function

$$F(g) = M\,\rho_{\kappa'}(z(g))^{-1}\,\iota_\ell(f(g))$$

for a fixed matrix $M$ that intertwines two weights $\kappa'$ and $\kappa$ (Lean: `New.padicModel`). On a rational element the algebraic weight acts through $z$ after $\iota_\ell$ (Lean: `New.comp_weightRep_eq_weylRep_mulVec`). So $F(\gamma g) = F(g)$ for rational $\gamma$, and $F$ is a continuous function on a compact quotient. Forms of different weights now live in one space of functions. A change of weight is a product with a matrix coefficient of an algebraic representation, evaluated at $z(g)$.

### An ultrametric Stone-Weierstrass theorem

Over $\mathbb R$, the Stone-Weierstrass theorem says that a subalgebra that separates points is dense. Over a non-archimedean field there is a version for modules. Let $X$ be a nonempty compact space and $k$ a normed field with an ultrametric norm. Let $N$ be a $k$-submodule of $C(X, k)$. Its *multipliers* are the functions $u$ with $uN \subseteq N$; they form the set $N/N$.

**Theorem (Ultrametric Stone-Weierstrass).** Let $\varphi \in C(X, k)$. Suppose that for each $a \in X$ there is $d \in N$ such that $\varphi(x) = d(x)$ at every $x$ where every multiplier $u$ of $N$ takes the same value as at $a$. Then for every $\varepsilon > 0$ there is $g \in N$ with $\|\varphi - g\| \leq \varepsilon$.

Lean: `New.stoneWeierstrass_ultrametric` (Lib/GaloisRep/WeightCongruence.lean).

*Proof.* Suppose that $\varphi$ has distance more than $\varepsilon$ from every element of $N$. Let $B$ be the ring of multipliers of norm at most $1$. The multipliers $w \in B$ such that $w\varphi$ is within $\varepsilon$ of $N$ form a proper ideal of $B$, since $1$ is not in it. Take a maximal ideal $\mathfrak m$ that contains it. It cuts out a set $Z \subseteq X$ on which every multiplier is constant. By hypothesis some $d \in N$ agrees with $\varphi$ on $Z$. By compactness and the ultrametric inequality, some multiplier outside $\mathfrak m$ makes $\varphi - d$ small everywhere after it multiplies it. This contradicts the choice of $\mathfrak m$. $\square$

The classical sources are Dieudonné (1944) and Kaplansky, *The Weierstrass theorem in fields with valuations*, Proc. Amer. Math. Soc. 1 (1950). The module form is in Prolla, *Approximation of vector valued functions* (1977).

The source applies the theorem with $X$ a product of groups $\mathrm{GL}_N$ over a finite extension of $\mathbb Q_\ell$, and $N$ the span of matrix coefficients of free weights. The free weights are closed under products in the relevant range, so the matrix coefficients are multipliers, and they separate the points of $X$. This gives density of combinations of matrix coefficients of free weights (Lean: `New.mem_uniformClosure_weylRep_coeff`). Transported to forms, it gives the next result.

**Proposition (Approximation by forms of free weight).** Let $K$ be an open subgroup of the integral points $\prod_w \mathrm{U}_N(\mathcal O_w)$, let $\theta$ be a character of $K$ trivial near $1$, and let $T$ be a set of infinite places. Let $f$ be a form of weight $\kappa$ that is fixed by every $d \in K$ whose components above $\ell$ at the places of $T$ are $1$, and let $\theta(d) = 1$ for these $d$. Let $D$ be a set of $\ell$-adic functions whose span contains every model $F$ as above of every form $\varphi$ of type $\theta$ at level $K$ and weight $\nu$, whenever $\nu$ agrees with $\kappa$ off $T$, is free on $T$, and $M$ intertwines $\nu$ and $\kappa$ on the families that are $1$ over $T$. Then the $\ell$-adic model of $f$ is a uniform limit of elements of the span of $D$.

Lean: `New.padicModel_mem_uniformClosure` (Lib/GaloisRep/WeightCongruence.lean).

*Proof.* On a double coset of $c$, write the model of $f$ as a part that carries the places off $T$, times a part that depends only on the components over $T$. Summing over the finitely many rational elements in each class, the model of $f$ is a combination of bounded operators applied to the coordinates of the second part. These coordinates are uniform limits of matrix coefficients of free weights, by the density above. The operators send such matrix coefficients to models of forms of type $\theta$ and free weight, which lie in the span of $D$. The bounds keep the limits uniform (Lean: `New.map_mem_uniformClosure_of_bound`). $\square$

Here "free on $T$" means that at each $\tau \in T$ the integers $-\sum_{j < h < N}(\nu_{\tau,h} + 1)$, for $j < N$, are free in the sense of [Section 2](/decl/New.HasNoSmallRelations/).

### Hecke operators that do not increase the norm

A limit of models is useful only if the Hecke eigenvalues pass to the limit. The next lemma gives Hecke operators on all $\ell$-adic functions that are contractions.

**Lemma (Hecke contractions).** Let $w$ be a finite place with $\bar w \neq w$, and let $j \geq 0$. There are a scalar $a \neq 0$ in $\bar{\mathbb Q}_\ell$ and a linear operator $T$ on $\ell$-adic functions such that:

1. $a = -1$ if $w$ does not lie over $\ell$;
2. if $|\varphi| \leq r$ everywhere, then $|T\varphi| \leq r$ everywhere;
3. for every weight $\kappa'$, every form $f$ of weight $\kappa'$, every matrix $M$ that intertwines $\kappa'$ and $\kappa$ on the elements supported at $w$ and $\bar w$, and every Hecke polynomial $P$ of $f$ at $w$, the model $F$ of $f$ satisfies $TF = a\,\iota_\ell(P_j)\,F$, where $P_j$ is the coefficient of $X^j$ in $P$.

Lean: `New.GaloisRep.exists_padicModel_hecke_contraction` (Lib/GaloisRep/WeightCongruence.lean).

The point of part 3 is that one operator $T$ works for all weights at once. Away from $\ell$ the weight plays no role at $w$, and $T$ is the usual Hecke operator up to sign. Above $\ell$ the constant $a$ is a normalization that depends on $w$ and $j$ but not on the form.

### From limits of traces to a representation

Combine the three results. The model of $f$ is a uniform limit of combinations $\sum_i t_{\eta,i} F_{\eta,i}$ of models of forms $g_{\eta,i}$ of free weight and cuspidal type, with $\eta \to 0$. Apply the contractions $T$. Since $T$ has norm at most $1$, the eigenvalues satisfy: $a\,\iota_\ell(P_{w,j})$ is the uniform limit of $\sum_i t_{\eta,i}\, a\,\iota_\ell(Q_{\eta,i,w,j})$, where $Q_{\eta,i,w}$ is the Hecke polynomial of $g_{\eta,i}$. The source packages this in a closed monoid $\mathcal N$ of pairs $(x, \varphi)$, on which $\sum_i t_{\eta,i}\,\varphi(\eta, i) \to x$ uniformly as $\eta \to 0$. This is the notion of an approximating monoid of [the previous chapter](/chapter/attached-representations/). The pairs of coefficients of Hecke polynomials lie in $\mathcal N$. The seed gives representations $r_{\eta,i}$ with characteristic polynomials $\iota_\ell(Q_{\eta,i,w})$.

**Theorem (Limits of characteristic polynomials).** Let $a \geq 1$. Let $\mathcal N$ be an approximating monoid for the coefficients $t_{\eta,i}$. Let continuous $r_{\eta,i}$ of rank $a$ have characteristic polynomials $\iota_\ell(Q_{\eta,i,w})$ at most Frobenius data. Let $L \subseteq \bar{\mathbb Q}_\ell$ be complete. Suppose that for most Frobenius data $p$ at a place $w$, the polynomial $P_w$ is monic of degree $a$, the number $-\iota_\ell(P_{w,a-1})$ lies in $L$, and for each $j$ the pair $(-\iota_\ell(P_{w,j}), (-\iota_\ell(Q_{\eta,i,w,j}))_{\eta,i})$ lies in $\mathcal N$. Then some $R$ is attached to $P$, and for every $g$ the pair $(\operatorname{tr} R(g), (\operatorname{tr} r_{\eta,i}(g))_{\eta,i})$ lies in $\mathcal N$.

Lean: `New.GaloisRep.exists_attached_of_isApproximatingMonoid` (Lib/GaloisRep/Main/SplitCase.lean).

*Proof.* The power sums of the roots of a monic polynomial are polynomials in its coefficients, by Newton's identities. So $\mathcal N$, a monoid, contains the pairs of the traces of $r_{\eta,i}(\mathrm{Frob})^m$ and of the corresponding power sums for $P$. Frobenius elements are dense and traces are continuous, so for every $g$ the functions $\operatorname{tr} r_{\eta,i}(g)$ have a limit combination. The limit is a pseudocharacter of dimension $a$, with values in the complete set $L$ on the dense set. The theorem on pseudocharacters of [the previous chapter](/chapter/attached-representations/) turns it into a representation $R$. The closeness of characteristic polynomials follows from the uniform convergence. $\square$

A second lemma carries the local properties to the limit (Lean: `New.GaloisRep.isCompatibleAt_of_isApproximatingMonoid`). If every $r_{\eta,i}$ is unramified or crystalline above $u$ with the jumps of $\kappa$, and $\iota_\ell(Q_{\eta,i,u})$ kills its geometric Frobenius elements, then the same holds for $\rho$ and $\iota_\ell(P_u)$. The crystalline property passes to trace limits by the results of Volume 7 (see [Kisin frames](/chapter/kisin-frames/)).

### The split case

**Theorem (The split case).** Let $E$ be a CM field that contains a primitive root of unity of order $5040$ and the field $\mathbb Q(\sqrt{-D})$, with $D \equiv 3 \bmod 4$. Let $a$ be odd and let $u$ be a finite place. Suppose that $u$ and every place above $\ell$ lie over split primes of $\mathbb Q(\sqrt{-D})$ prime to $D$. Then $\mathrm{SphericalCompat}$ holds for $E$, rank $a$ and the place $u$: every eigenform of any weight on the standard definite unitary group of rank $a$ has an attached representation, and if the form is spherical at $u$, every attached representation is unramified or crystalline at each place of $\Omega$ above $u$, has the jumps of the weight there, and, if $u$ is split, has its geometric Frobenius elements killed by the Hecke polynomial at $u$.

Lean: `New.GaloisRep.sphericalCompat_of_split` (Lib/GaloisRep/Main/SplitCase.lean).

*Proof.* Choose two places $v$ and $x$ above $\ell$, over one split prime of $\mathbb Q(\sqrt{-D})$, apart from each other and from $u$ up to conjugation (Lean: `New.GaloisRep.exists_place_apart`). Choose a cuspidal type $\vartheta$ at $v$ by [the proposition on types](/decl/New.Variety.exists_isCuspidalType/), and a level $K$ with a character $\chi$ that is $\vartheta$ at $v$ and fixes $f$ away from $v$ and $x$ (Lean: `New.GaloisRep.exists_isTypeLevel`). Let $T$ be the set of infinite places that do not induce $u$ or $\bar u$. By [the approximation proposition](/decl/New.padicModel_mem_uniformClosure/), the model of $f$ is a uniform limit of combinations of models of forms of type $\chi$ whose weights agree with $\kappa$ at the places that induce $u$ or $\bar u$ and are free on $T$. These forms are spanned by eigenforms off a finite set. Each such eigenform satisfies the hypotheses of [the seed theorem](/decl/New.GaloisRep.exists_rep_of_cuspidal_type/), with the type at $v$ and the free jumps at the embedding of $x$, and with $w' = u$. The contractions put the coefficients of the Hecke polynomials into an approximating monoid. [The theorem on limits](/decl/New.GaloisRep.exists_attached_of_isApproximatingMonoid/) gives an attached representation. Any attached $\rho$ has the trace of $R$, since $P$ determines the trace. The lemma on local properties gives the compatibility at $u$. $\square$

**Remark (Formalization).** The limit gives attachment only in the approximate sense: for each $\varepsilon > 0$ the characteristic polynomial is within $\varepsilon$ of $\iota_\ell(P_w)$ at most Frobenius data. The seeds have exact characteristic polynomials, but the limit argument does not keep exactness at a fixed place. This is enough for the argument: the trace of an attached representation is determined by $P$ (Lean: `New.GaloisRep.Attached.trace_eq`), and the local clauses are proved directly. The hypothesis that $\ell$ lies over split primes of $\mathbb Q(\sqrt{-D})$ comes from the seed: the type and the free jumps are placed above $\ell$.
