---
title: The terms of reducible polynomials
lean:
  - Lib/Adelic/TraceFormula/FibreIntegral.lean
  - Lib/Adelic/TraceFormula/CoprimeFactors.lean
  - Lib/Adelic/TraceFormula/ReduciblePolynomials.lean
decls:
  - New.exists_isCoprime_mul_of_not_irreducible
  - New.IsInvariantDistribution
  - New.IsSlice
  - New.IsImage
  - New.IsSlice.exists_isImage
  - New.TestFunction.map_eq_zero_of_integral_eq_zero
  - New.IsInvariantDistribution.eq_zero_of_isImage
  - New.eq_zero_of_coprime_factors
  - New.Space.geometricSide_singleton_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The terms of reducible polynomials

This section proves that $I_R(\varphi) = 0$ when $R$ is not irreducible, for a test function $\varphi$ that is cuspidal at a split place $w$ and has simple zeros at a place $w'$. The simple zero excludes the proper powers $R = Q^j$. Every other reducible monic $R$ is a product $A C$ of coprime factors. A descent to the block diagonal group at $w$ shows that an invariant distribution on the elements of characteristic polynomial $A C$ kills every cuspidal test function. The source credits the vanishing of these terms to Deligne and Kazhdan. The descent follows Harish-Chandra.

### A factorisation

**Lemma.** Let $F$ be a field and let $R \in F[X]$ be monic. Suppose that $R$ is not irreducible and is not of the form $Q^j$ with $Q \in F[X]$ and $j > 1$. Then $R = A C$ with $A$ and $C$ coprime and neither of them a unit.
Lean: `New.exists_isCoprime_mul_of_not_irreducible` (Lib/Adelic/TraceFormula/ReduciblePolynomials.lean).

*Proof.* $R$ is not a unit, since $1 = 1^2$ is excluded. Let $Q$ be a monic irreducible factor of $R$ and write $R = Q^i A$ with $Q \nmid A$ and $i \geq 1$. Then $Q^i$ and $A$ are coprime and $Q^i$ is not a unit. If $A$ were a unit, it would be $1$ since $R$ and $Q^i$ are monic. Then $R = Q$ is irreducible if $i = 1$, and $R = Q^i$ is a proper power if $i > 1$. Both are excluded. $\square$

The polynomial $R = 1$ is not irreducible and equals $1^2$, so the lemma does not apply to it. For $N \geq 1$ no characteristic polynomial is $1$, and the proof below excludes it by the simple zero.

### Invariant distributions and slices

Let $\Gamma$ and $G$ be topological groups and $j : \Gamma \to G$ a continuous homomorphism. Then $\Gamma$ acts on test functions on $G$ by conjugation, $(g \cdot f)(x) = f(j(g)^{-1} x\, j(g))$. In the application $G = G_f$, $\Gamma = \mathrm{GL}_N(E_w)$ and $j = \iota_w$.

**Definition (Invariant distribution).** Let $C \subseteq G$. A linear form $I$ on the test functions on $G$ is an *invariant distribution on $C$* if $I(g \cdot f) = I(f)$ for all $g \in \Gamma$ and every test function $f$, and $I(f) = 0$ for every $f$ that vanishes on $C$.
Lean: `New.IsInvariantDistribution` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

**Definition (Slice).** Let $H$ be a subgroup of $\Gamma$ and let $C, X \subseteq G$. Then $X$ is a *slice* of $C$ for $H$ if:

1. $H$ is closed in $\Gamma$, and $C$ is closed in $G$;
2. $x \in C$ if and only if $j(g)^{-1} x\, j(g) \in X$ for some $g \in \Gamma$;
3. for $y \in X$ and $g \in \Gamma$, $j(g)^{-1} y\, j(g) \in X$ if and only if $g \in H$;
4. for every neighbourhood $O$ of $1$ in $\Gamma$ and every $y \in X$, the points $x \in C$ near $y$ are conjugate into $X$ by elements $o \in O$.

Lean: `New.IsSlice` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

So the map $\Gamma \times X \to C$, $(g, y) \mapsto j(g)\, y\, j(g)^{-1}$, is onto. By item 3 its fibres are the orbits $\{(g h, j(h)^{-1} y\, j(h)) : h \in H\}$. Item 4 says that the map is open near $\{1\} \times X$.

**Definition (Image).** Let $\nu$ be a measure on $H$ and let $\Psi$ be a test function on $\Gamma \times G$. A test function $f$ on $G$ is an *image* of $\Psi$ if for all $g \in \Gamma$ and $y \in X$,
$$ f\big(j(g)\, y\, j(g)^{-1}\big) = \int_H \Psi\big(g h, j(h)^{-1} y\, j(h)\big)\, d\nu(h). $$
Lean: `New.IsImage` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

The integral on the right is the integral over the fibre (`New.fibreIntegral`).

**Proposition (Images).** Let $G$ be a Hausdorff, weakly locally compact topological group with a basis of open subgroups at $1$. Let $X$ be a slice of $C$ for $H$, and let $\nu$ be a Haar measure on $H$. Then every test function $\Psi$ on $\Gamma \times G$ has an image.
Lean: `New.IsSlice.exists_isImage` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

*Proof.* For $x \in C$ choose $g_x$ with $j(g_x)^{-1} x\, j(g_x) \in X$, and put $f_0(x)$ equal to the fibre integral at $(g_x, j(g_x)^{-1} x\, j(g_x))$. Two choices of $g_x$ differ by an element of $H$, and the fibre integral is the same for both, by invariance of $\nu$ (`New.IsSlice.fibreIntegral_conj_eq`). Item 4 of the definition makes $f_0$ locally constant on $C$, although $x \mapsto g_x$ need not be continuous. The function $f_0$ has compact support, because $\Psi$ has. Since $C$ is closed, $f_0$ extends to a test function on $G$. $\square$

The next step is the uniqueness of Haar measure in a form with a parameter.

**Lemma (Uniqueness of Haar measure, with a parameter).** Let $\Gamma$ have a compact open subgroup and let $\mu$ be a left Haar measure on $\Gamma$. Let $X \subseteq Y$, and let $\Lambda$ be a linear form on the test functions on $\Gamma \times Y$ such that:

1. $\Lambda(\Psi') = \Lambda(\Psi)$ when $\Psi'(g, y) = \Psi(a^{-1} g, y)$ for some $a \in \Gamma$;
2. $\Lambda(\Psi) = 0$ when $\Psi$ vanishes on $\Gamma \times X$.

If $\int_\Gamma \Psi(g, y)\, d\mu(g) = 0$ for every $y \in X$, then $\Lambda(\Psi) = 0$.
Lean: `New.TestFunction.map_eq_zero_of_integral_eq_zero` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

*Proof.* There is a compact open subgroup $O$ of $\Gamma$ such that $\Psi = \sum_{q} 1_{a_q O} \otimes \psi_q$, a finite sum over cosets $a_q O$ with test functions $\psi_q$ on $Y$. By item 1, $\Lambda(\Psi) = \Lambda(1_O \otimes \sum_q \psi_q)$. The integral of $\Psi(\cdot, y)$ is $\mu(O) \sum_q \psi_q(y)$, and $\mu(O) \neq 0$. So $\sum_q \psi_q$ vanishes on $X$, and item 2 gives $\Lambda(\Psi) = 0$. $\square$

**Theorem (Descent to a slice).** Let $\Gamma$ be a Hausdorff group with a compact open subgroup, let $\mu$ and $\nu$ be Haar measures on $\Gamma$ and on $H$, and let $X$ be a slice of $C$ for $H$. Let $I$ be an invariant distribution on $C$. Let $\Psi$ be a test function on $\Gamma \times G$ with $\int_\Gamma \Psi(g, y)\, d\mu(g) = 0$ for every $y \in X$. Then $I(f) = 0$ for every image $f$ of $\Psi$.
Lean: `New.IsInvariantDistribution.eq_zero_of_isImage` (Lib/Adelic/TraceFormula/FibreIntegral.lean).

*Proof.* Put $\Lambda(\Psi) = I(f)$ for an image $f$ of $\Psi$. This is well defined and linear: two images of $\Psi$ agree on $C$, and $I$ only sees $C$; the images of a sum are sums (`New.IsInvariantDistribution.exists_linearMap_eq_of_isImage`). A left translate of $\Psi$ by $a$ has as image the conjugate of $f$ by $a$, so item 1 of the lemma follows from the invariance of $I$. If $\Psi$ vanishes on $\Gamma \times X$, then its image vanishes on $C$, and item 2 follows. Apply [the lemma](/decl/New.TestFunction.map_eq_zero_of_integral_eq_zero/). $\square$

### Coprime factors

Let $w$ be a split place and let $A, C \in E_w[X]$ be coprime non-units. Let $C_{AC}$ be the set of $y \in G_f$ whose component $y_w$ has characteristic polynomial $A C$. Write $u A + v C = 1$. For $y \in C_{AC}$ the matrix $(v C)(y_w)$ is the projection onto $\ker A(y_w)$ along $\ker C(y_w)$. It has rank $\deg A$, and it is a fixed polynomial in $y_w$.

**Theorem (Coprime factors).** Let $w$ be a split finite place, let $A, C \in E_w[X]$ be coprime and not units, and let $I$ be a linear form on the test functions on $G_f$ with:

1. $I\big(y \mapsto f(g^{-1} y g)\big) = I(f)$ for all $g \in G_f$ and every test function $f$;
2. $I(f) = 0$ for every $f$ that vanishes at all $y$ with $\chi_{y_w} = A C$.

Then $I(\varphi) = 0$ for every test function $\varphi$ that is cuspidal at $w$.
Lean: `New.eq_zero_of_coprime_factors` (Lib/Adelic/TraceFormula/CoprimeFactors.lean).

*Proof.* If $C_{AC}$ is empty, item 2 gives $I(\varphi) = 0$. Otherwise $\deg A$ lies strictly between $0$ and $N$. Choose a set $T$ of indices with $|T| = \deg A$, so that $T \neq \emptyset$ and $T \neq n$. Let $\varepsilon = \varepsilon_T$ be the projector on the coordinates in $T$, let $H$ be the block diagonal group of matrices that commute with $\varepsilon$, and let $\mathcal{N}$ be the unipotent radical $\{r_T(Y)\}$ of the parabolic subgroup of $T$.

Step 0: averaging. Replace $\varphi$ by the mean $\psi$ of its conjugates $y \mapsto \varphi(\iota_w(k)^{-1} y\, \iota_w(k))$ over $k \in \mathrm{GL}_N(\mathcal{O}_w)$. Then $I(\psi) = I(\varphi)$ by item 1. The mean $\psi$ is invariant under these conjugations. It keeps the property of [the cuspidality lemma](/decl/New.IsCuspidalAt.exists_sum_translate_eq_zero/): with the matrices $\kappa_i$ of that lemma, $\sum_i \psi(x\, \iota_w(r_T(\kappa_i))) = 0$ for every $x$.

Step 1: the slice. Let $X$ be the set of $y \in C_{AC}$ with $(v C)(y_w) = \varepsilon$. Then $X$ is a slice of $C_{AC}$ for $H$ and $j = \iota_w$ (`New.isSlice_blockLocus`). The main point is item 2 of the definition: every $y \in C_{AC}$ is conjugate into $X$, and the conjugating matrix can be taken in $\mathrm{GL}_N(\mathcal{O}_w) \mathcal{N}$, by an Iwasawa decomposition of the projection $(v C)(y_w)$. Item 4 holds since $(vC)(x_w)$ is near $\varepsilon$ for $x$ near $y$.

Step 2: the function $\Psi$. Put $\Psi(g, y) = \psi(\iota_w(g)\, y\, \iota_w(g)^{-1})$ for $g \in \mathrm{GL}_N(\mathcal{O}_w) \mathcal{N}$ and $\Psi(g, y) = 0$ otherwise, for $y$ with $(vC)(y_w) = \varepsilon$. This is the restriction of a test function on $\mathrm{GL}_N(E_w) \times G_f$ (`New.exists_testFunction_eq_indicator`). Its image is $c\, \psi$, where $c \neq 0$ is the volume of $H \cap \mathrm{GL}_N(\mathcal{O}_w)$ (`New.isImage_blockLocus_smul`).

Step 3: the integrals vanish. Fix $y \in X$. Since $y_w$ is block diagonal with coprime blocks, every element $y\, \iota_w(r_T(\kappa))$ of the coset $y \mathcal{N}$ is a conjugate $\iota_w(m)\, y\, \iota_w(m)^{-1}$ with $m \in \mathcal{N}$. The right translates of $g \mapsto \Psi(g, y)$ by these $m_i$ add up to zero, by Step 0. Each has the same integral, since right translation by $\mathcal{N}$ preserves Haar measure on $\mathrm{GL}_N(E_w)$. So the number of indices $i$ times $\int \Psi(g, y)\, dg$ is $0$ (`New.integral_indicator_iwasawaSet_eq_zero`).

Now [the descent theorem](/decl/New.IsInvariantDistribution.eq_zero_of_isImage/) gives $I(c\, \psi) = 0$. So $I(\varphi) = I(\psi) = 0$. $\square$

The fact used in Step 3 is the classical statement that a semisimple element of a Levi subgroup with no common eigenvalue between the blocks has a conjugation orbit under $\mathcal{N}$ that fills $y \mathcal{N}$. Here it is linear algebra: the equation $m\, y\, m^{-1} = y\, r(\kappa)$ for $m = r(Z)$ is the Sylvester equation $Z y_2 - y_1 Z = y_1 \kappa_{12}$ in the upper right block. It has a solution since $y_1$ and $y_2$ have coprime characteristic polynomials.

### The terms of reducible polynomials

**Theorem.** Let $B \geq 13 N^3$ and let $e$ be a cusp kernel of order $B$. Let $w$ be a split finite place and $w'$ a finite place. Let $\varphi$ be a test function that is cuspidal at $w$, such that $\varphi(g) \neq 0$ implies that $g_{w'}$ has a simple zero. Then $I_R(\varphi) = 0$ for every $R \in E[X]$ that is not irreducible.
Lean: `New.Space.geometricSide_singleton_eq_zero` (Lib/Adelic/TraceFormula/ReduciblePolynomials.lean).

*Proof.* Suppose $I_R(\varphi) \neq 0$. If $\varphi(y) = 0$ for every $y$ with $\chi_{y_{w'}} = R$ over $E_{w'}$, then the integrand of $I_R$ is $0$, since the components of $x^{-1} \gamma x$ at $w'$ have the characteristic polynomial $\chi_\gamma$ (`New.Space.geometricSide_singleton_eq_zero_of_forall`). So there is $y$ with $\varphi(y) \neq 0$ and $\chi_{y_{w'}} = R$. Then $R$ is monic. It is not a proper power $Q^j$ over $E$: otherwise $\chi_{y_{w'}}$ would be one over $E_{w'}$, against [the simple zero lemma](/decl/New.HasSimpleZero.charpoly_ne_pow/). By [the factorisation lemma](/decl/New.exists_isCoprime_mul_of_not_irreducible/), $R = A C$ over $E$, with $A$ and $C$ coprime non-units. Their images in $E_w[X]$ are coprime non-units. Take $I = I_{\{AC\}}$. It is conjugation invariant by [the lemma of Section 3](/decl/New.Space.geometricSide_translate/), and it vanishes on test functions that vanish on $C_{AC}$, by the same argument at $w$. [The coprime factors theorem](/decl/New.eq_zero_of_coprime_factors/) gives $I_R(\varphi) = 0$, a contradiction. $\square$

**Remark (Formalization).** The places $w$ and $w'$ are not asked to be distinct, and $w'$ need not be split. The factorisation $R = A C$ is found over $E$ and then mapped to $E_w$. The simple zero at $w'$ is used only to exclude proper powers over $E$. At $w$ only the coprime factorisation is used.

### A model case

Take $N = 2$. A monic $R$ of degree $2$ that is not irreducible over $E$ is $(X - \alpha)(X - \beta)$ with $\alpha, \beta \in E$. If $\alpha \neq \beta$, the rational points with this polynomial are diagonalisable over $E$, and at $w$ they are conjugate to $\operatorname{diag}(\alpha, \beta)$. The theorem kills these terms by the coprime factors argument with $A = X - \alpha$, $C = X - \beta$, $T = \{1\}$: the slice is the set of diagonal matrices $\operatorname{diag}(\alpha, \beta)$ at $w$, the group $\mathcal{N}$ is the upper unipotent group, and Step 3 solves $z \beta - \alpha z = \alpha \kappa$, that is $z = \alpha \kappa / (\beta - \alpha)$. If $\alpha = \beta$, then $R = (X - \alpha)^2$ is a proper power. The rational points are $\alpha \cdot 1$ and the unipotent elements times $\alpha$. These are the terms that the simple zero at $w'$ removes. Suppose a support point $y$ had $\chi_{y_{w'}} = (X - \alpha)^2$. Then $\alpha$ is integral at $w'$, and modulo $w'$ the polynomial is $(X - \bar\alpha)^2$. Its root $0$ has multiplicity $0$ or $2$, never $1$.
