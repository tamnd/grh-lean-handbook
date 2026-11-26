---
title: When an eigensystem occurs in a weight
lean:
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Shimura/Transfer/Lefschetz.lean
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Shimura/TraceFormula/DefiniteTrace.lean
  - Lib/Shimura/TraceFormula/MarkedDefiniteSums.lean
  - Lib/Shimura/TraceFormula/TestFunction.lean
  - Lib/Shimura/Transfer/WeightOccurs.lean
decls:
  - New.Variety.IsRegularHecke
  - New.Variety.countTerm
  - New.Variety.IsNullHecke
  - New.Variety.OccursInWeight
  - New.Variety.IsNullFamily
  - New.Variety.Model.isNullHecke_of_isNullFamily
  - New.Variety.definiteForms
  - New.Variety.trace_definiteForms_eq_finsum_countTerm
  - New.Variety.finsum_countTerm_marked_eq_definite
  - New.Variety.trace_definiteForms_rep_eq_zero_of_isNullHecke
  - New.Variety.isNilpotent_of_trace_pow_succ_eq_zero
  - New.Variety.IsTestVector
  - New.Variety.exists_test_function
  - New.Variety.IsTestEigenform
  - New.Variety.occursInWeight_of_isTestEigenform
  - New.Variety.IsCoefficientSystem
  - New.Variety.exists_isCoefficientSystem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## When an eigensystem occurs in a weight

The main theorem of this chapter takes as input a system $\theta$ of Hecke eigenvalues and a set of weights $h$ in which $\theta$ *occurs*. The textbook meaning is that $\theta$ appears in the cohomology of the Shimura variety in a given degree, or with a given Hodge-Tate weight. The source avoids any computation of cohomology. It defines occurrence through the local terms of a Lefschetz formula, and it proves occurrence for the forms it needs by a comparison of two finite sums. This section explains the definition and the proof of occurrence. The proof is a finite form of the comparison of trace formulas between the unitary group of signature $(1, n - 1)$ and a definite inner form.

The textbook source is Harris and Labesse, *Conditional base change for unitary groups*, Asian J. Math. 8 (2004), Theorem 2.1.2, and Labesse, *Changement de base CM et séries discrètes* (2011), Theorem 5.4. The counting goes back to Shimura, *On the trace formula for Hecke operators*, Acta Math. 132 (1974), and Goresky and MacPherson, *The topological trace formula* (2003). These are the citations of the source.

### The idea

Let $b$ be a Hecke operator. On a compact variety, the Lefschetz formula writes the alternating trace of $b$ on cohomology as a sum of local terms over the fixed points of the correspondence $b$. With coefficients that separate the weights, each Hodge-Tate weight $h$ gets its own sum. Call $b$ *$h$-null* if the weight-$h$ sum is $0$.

Now suppose $\theta$ does not occur in weight $h$. Then there is a Hecke operator $p$ with $p(\theta) = 1$ that kills the weight-$h$ part of the cohomology (Section 4). Every multiple $b p$ then acts by $0$ on weight $h$, so every $b p$ is $h$-null. The source takes the contrapositive as the definition: $\theta$ occurs in weight $h$ if, for every $p$ with $p(\theta) = 1$, some $b p$ is not $h$-null.

To prove occurrence, the source computes the weight-$h$ sum in a different way. The fixed points of a Hecke correspondence on the Shimura variety are counted by rational elements $y \in \mathrm{GL}_n(E)$ with a marked eigenvalue. The same elements, without the mark, count the trace of $b$ on forms on the definite group. If all $(bp)^k$ are $h$-null, then $bp$ has trace $0$ in all positive powers on the definite forms, so it is nilpotent there. A test function $b$ makes this impossible for a given eigenform.

### Regular elements and the two counts

The Hecke algebra of level $\mathfrak{N}$ is a subalgebra of $\mathbb{C}[\mathrm{GL}_n(\mathbb{A}_{E,f})]$ (see [the integral model](/chapter/integral-model/)). An element $f = \sum a_g [g]$ gives a function $\sum a_g \mathbf{1}_{gK}$ on cosets of the principal level $K = K(\mathfrak{N})$. Write $f(x)$ for its value at $xK$.

**Definition (Regular Hecke element).** A Hecke element $f$ is *regular* if $f(x^{-1} y x) \neq 0$, with $y \in \mathrm{GL}_n(E)$ and $x \in \mathrm{GL}_n(\mathbb{A}_{E,f})$, forces the characteristic polynomial of $y$ to be separable.

Lean: `New.Variety.IsRegularHecke` (Lib/Shimura/HeckeTower/HeckeData.lean).

The two counts run over orbits under $\mathrm{GL}_n(E)$ of *marked triples* $(xK, y, \mu)$: a coset, a rational element $y$, and an index $\mu$ of an eigenvalue of $y$. For a weight function $\omega$ on pairs (polynomial, index), the term of an orbit is
$$f(x^{-1} y^{-1} x) \, \omega(\operatorname{charpoly} y, \mu)$$
if $x$ is a signed frame for the hermitian reflection that the source attaches to $(\varepsilon, y, \mu)$, and $0$ otherwise. With the flag $\varepsilon$ true this is the *marked count*: the frames are those of the indefinite side, where the marked eigenvalue picks the special direction. With $\varepsilon$ false it is the *definite count*. The value does not depend on the representative of the orbit.

Lean: `New.Variety.countTerm` (Lib/Shimura/HeckeTower/HeckeData.lean).

**Definition ($h$-null; occurs in weight $h$).** A Hecke element $b$ is *$h$-null* (with parameter $\nu$) if, when $b$ is regular, for every $\alpha \in \mathcal{O}_E^\nu$, the marked count of $b$ with weight $1$ has finite support, and the marked count with weight the coefficient of $X^h$ in the local term at $2\alpha$ is $0$. A system $\theta$ of eigenvalues at the safe places *occurs in weight $h$* if, for every finite combination $p = \sum_L c_L \tau_L$ of words in the Hecke operators $\tau_{w, j}$ with $\sum_L c_L \theta(L) = 1$, some $b p$ is not $h$-null.

Lean: `New.Variety.IsNullHecke` and `New.Variety.OccursInWeight` (Lib/Shimura/Transfer/Lefschetz.lean).

**Remark (Formalization).** The condition $h$-null is void for an element that is not regular: such an element is $h$-null. So occurrence needs a regular $b p$. The local terms are polynomials in $X$ that the source attaches to an element and a marked root; only the multipliers $2\alpha$ are used, because then $\det(1 - 2\alpha y)$ on the lattice is odd, so nonzero. The parameter $\nu$ is the number of extra points in the Kuga-Sato fibre power. Nothing in the definition refers to cohomology. The link to cohomology is the next lemma.

### The geometric side

**Definition (Null family).** A formal sum $\sum_i a_i [u_i]$ of maps $u_i : W \to Z$, with coefficients in a field $k$, is *null in weight $h$* for tangent polynomials of rank $d$ if the following holds for every $c : W \to Z$. Let $S$ be the set of coincidences $(i, y)$ with $a_i \neq 0$, $y \in W(k)$ and $c(y) = u_i(y)$. If each element of $S$ is given a tangent polynomial $P$ of rank $d$ with $P(1) \neq 0$, then $S$ is finite and
$$\sum_{(i, y) \in S} a_i \frac{[X^h] P_{(i, y)}}{P_{(i, y)}(1)} = 0.$$

Lean: `New.Variety.IsNullFamily` (Lib/Cohomology/Etale/Basic.lean).

A tangent polynomial of $(c, u_i)$ at $y$ is $P(t) = P(0) \det(1 - tA)$, where $A$ relates the differentials, $du = dc \circ A$. For a transversal coincidence, $1 / \det(1 - A)$ is the classical local term of the Lefschetz formula, and the coefficient of $X^h$ picks out one weight.

**Lemma (Lefschetz formula as a marked count).** Let $X$ be a model at a neat level $\mathfrak{N}$, and let $b$ be a Hecke element. Assume that for all deep levels $i$ of the tower and all $\alpha$, the family of maps $p_q \circ m_\alpha$, for the cosets $q$, with coefficients $b(q)$, is null in weight $h$ in dimension $\dim X$. Then $b$ is $h$-null.

Lean: `New.Variety.Model.isNullHecke_of_isNullFamily` (Lib/Shimura/Transfer/Lefschetz.lean).

*Proof.* Fix a deep level $i$ whose legs contain the support of $b$. Each coincidence of $p_1$ and $p_q \circ m_{2\alpha}$ at a complex point of level $i$ has, by neatness, exactly one fixed pair $(z, \mu)$ with $z \in \mathrm{GL}_n(E)$. This sends coincidences to classes of marked triples. The map is injective by neatness and onto by the uniformisation of the model. Each fibre over a class has (number of lattice solutions) times $|\text{deck group}|$ points, and the number of lattice solutions cancels the denominator $P(1)$ of the local term. So the sum in the null family is $|\text{deck group}|$ times the sum in the definition of $h$-null. $\square$

Section 6 supplies the hypothesis of this lemma from cohomology: if a Hecke operator kills the weight-$h$ vectors, then the Lefschetz sum in weight $h$ vanishes.

### The definite side

Let $\xi$ be a finite-dimensional representation of $\mathrm{GL}_a(E)$. The *definite forms* of level $\mathfrak{N}$ with coefficients in $\xi$ are the functions $\phi$ on $\mathrm{GL}_a(\mathbb{A}_{E,f})$ with $\phi(yx) = \xi(y) \phi(x)$ for rational $y$, with $\phi(xk) = \phi(x)$ for $k \in K(\mathfrak{N})$, and with $\phi(x) = 0$ unless $x$ is a frame for a totally definite form.

Lean: `New.Variety.definiteForms` (Lib/Shimura/TraceFormula/DefiniteTrace.lean).

At a neat level this space is finite-dimensional, and the Hecke algebra acts by right translation.

**Proposition (Definite trace formula).** Let $\mathfrak{N}$ be neat and $a$ a regular Hecke element. Assume that $\operatorname{tr} \xi(y^{-1}) = \sum_i \omega(\operatorname{charpoly} y, i)$ whenever $\operatorname{charpoly} y$ is separable. Then the trace of $a$ on the definite forms is the definite count of $a$ with weight $\omega$.

Lean: `New.Variety.trace_definiteForms_eq_finsum_countTerm` (Lib/Shimura/TraceFormula/DefiniteTrace.lean).

The proof is the usual unfolding. The space of forms is a sum over finitely many definite classes, and the trace becomes a sum over the classes $j$ and the rational $y$ of $a(x_j^{-1} y x_j) \operatorname{tr} \xi(y)$, with $x_j$ the frame of $j$. Neatness is used to make this sum finite and to regroup it by orbits of triples.

**Proposition (Marked and definite counts agree).** Let $\mathfrak{N}$ be neat, $n$ odd, and $f$ regular. Assume that $f$ has a cuspidal type $(J, \chi)$ at a split place $w_0$, and that both counts with weight $1$ have finite support. Then for every weight $\omega$ the marked count and the definite count of $f$ agree.

Lean: `New.Variety.finsum_countTerm_marked_eq_definite` (Lib/Shimura/TraceFormula/MarkedDefiniteSums.lean).

The proof splits the classes by the characteristic polynomial. The cuspidal type at $w_0$ makes the sum over the classes with reducible characteristic polynomial vanish, for both flags. For the classes with irreducible characteristic polynomial a separate lemma, which uses that $n$ is odd, matches the marked terms with the definite terms. The source calls the result the comparison of orbit sums in the simple trace formula on a definite group.

Putting the two together:

**Proposition (Null implies trace zero).** Let $a$ be odd, $\mathfrak{N}$ neat, and $f$ regular of cuspidal type at $w_0$. Assume that the character of $\xi$ at regular $y^{-1}$ is the product, over the complex embeddings $\sigma$, of polynomials $q_\sigma$ evaluated at the eigenvalues of $\sigma(y)$: a Schur polynomial $s_l$ at $\Phi(v_0)$ and $(-x_1)^m$ at the other embeddings. If $f$ is $h$-null in the weight
$$h = m\big(a - 1 + a(N_\infty - 1)\big) + l_j,$$
with $N_\infty$ the number of infinite places of $E$, then $f$ has trace $0$ on the definite forms with coefficients in $\xi$.

Lean: `New.Variety.trace_definiteForms_rep_eq_zero_of_isNullHecke` (Lib/Shimura/Transfer/WeightOccurs.lean).

*Proof.* By the two propositions, the trace is the marked count of $f$ with the weight $\omega$ read off from the character. The character is a product of the $q_\sigma$ at the eigenvalues, and on the marked side this product is a sum of powers of $X$ in which $X^h$ occurs a fixed number $M \geq 1$ of times. So the trace is $1/M$ times a linear form $\Lambda$ applied to the products $\prod_\sigma q_\sigma$. The hypothesis says that $\Lambda$ kills the products $\prod_t (1 - \sigma(2\alpha) t)$ over the Lie roots $t$, for every $\alpha$. A lemma of the source on evaluations of symmetric polynomials then shows that $\Lambda$ kills $\prod_\sigma q_\sigma$ as well. It uses that the images of the elements $2\alpha$ under the complex embeddings are algebraically independent in a suitable sense, and that $\deg q_\sigma$ is at most the parameter $\nu = \sum_\sigma \deg q_\sigma + 1$. So the trace is $0$. $\square$

### Nilpotence and the test function

**Lemma.** Let $V$ be a finite-dimensional complex vector space and $f \in \operatorname{End}(V)$ with $\operatorname{tr}(f^{k}) = 0$ for all $k \geq 1$. Then $f$ is nilpotent.

Lean: `New.Variety.isNilpotent_of_trace_pow_succ_eq_zero` (Lib/Shimura/Transfer/WeightOccurs.lean).

*Proof.* The power sums $p_k = \sum_i \lambda_i^k$ of the eigenvalues of $f$ are the traces of $f^k$, so they are all $0$. Newton's identities $k e_k = \sum_{i = 1}^{k} (-1)^{i - 1} e_{k - i} p_i$ over $\mathbb{C}$ give $e_k = 0$ for all $k \geq 1$. So the characteristic polynomial of $f$ is $X^{\dim V}$, and $f$ is nilpotent by the theorem of Cayley and Hamilton. $\square$

The lemma needs characteristic $0$: over $\mathbb{F}_p$, the identity of $\mathbb{F}_p^p$ has all traces $0$.

**Definition (Test vector; test eigenform).** A vector $v$ in a representation of $\mathrm{GL}_a(\mathbb{A}_{E,f})$ is a *test vector* of level $\mathfrak{N}$ at split places $w_0 \neq w_1$ if: $v \neq 0$; a subgroup $J$ of $\mathrm{GL}_a(\mathcal{O}_{w_0})$ that contains the level acts on $v$ by a character $\chi$ that is a cuspidal type; the level at $w_1$ lies in the pro-$p$ Iwahori subgroup and $\mathrm{GL}_a(\mathcal{O}_{w_1})$ fixes $v$; and $\mathfrak{N}$ lies in $w_1$ but neither in $\bar w_0$ nor in $\bar w_1$. A *test eigenform* is a definite form that is a test vector and an eigenvector of each $\tau_{w, j}$, $w$ safe, with eigenvalue $\theta(w, j)$.

Lean: `New.Variety.IsTestVector` (Lib/Shimura/TraceFormula/TestFunction.lean) and `New.Variety.IsTestEigenform` (Lib/Shimura/Transfer/WeightOccurs.lean).

**Theorem (Test function).** Let $\phi$ be a test vector of level $\mathfrak{N}$, and let $c$ be a Hecke element supported on unitary similitudes with component $1$ at $w_1$, with $c \phi = \phi$. Then there is a Hecke element $b$ such that, for every $k \geq 0$, $(bc)^k \phi \neq 0$, and $(bc)^{k + 1}$ is regular and of type $(J, \chi)$ at $w_0$.

Lean: `New.Variety.exists_test_function` (Lib/Shimura/TraceFormula/TestFunction.lean).

The element $b$ is a product $b_1 b_0$. Here $b_0$ averages against $\chi$ over $J$ at $w_0$, which projects onto the $\chi$-isotypic vectors and gives the type. The factor $b_1$ is a Hecke element at $w_1$, built from a strictly dominant diagonal element and the pro-$p$ Iwahori level. The source uses it to get regularity, and it does not kill $\phi$.

**Theorem (Test eigenforms occur).** Let $a$ be odd, $\mathfrak{N}$ neat, and let $\xi$, $q_\sigma$, $l$ and $m$ be as in the proposition on null elements. Let $\theta$ be the eigenvalues of a test eigenform of level $\mathfrak{N}$ with coefficients in $\xi$. Then for every $j$, $\theta$ occurs in weight $m(a - 1 + a(N_\infty - 1)) + l_j$, with parameter $\nu = \sum_\sigma \deg q_\sigma + 1$.

Lean: `New.Variety.occursInWeight_of_isTestEigenform` (Lib/Shimura/Transfer/WeightOccurs.lean).

*Proof.* Let $p = \sum_L c_L \tau_L$ with $\sum_L c_L \theta(L) = 1$, and suppose that every $b p$ is $h$-null. The words $\tau_L$ are supported on unitary similitudes with component $1$ at $w_1$, because the safe places differ from $w_1$. Since $\phi$ is an eigenform, $p \phi = \sum_L c_L \theta(L) \phi = \phi$. The test function gives $b$ with $(bp)^k \phi \neq 0$ for all $k$ and $(bp)^{k + 1}$ regular of type $\chi$. Each $(bp)^{k + 1} = ((bp)^k b) p$ is $h$-null by assumption, so it has trace $0$ on the definite forms. By the lemma, $bp$ is nilpotent there. Then $(bp)^k \phi = 0$ for large $k$, a contradiction. $\square$

**Example.** Let $E$ have degree $4$, so that $N_\infty = 2$, and take $a = 3$, $m = 1$ and $l = (2, 1, 0)$. Then $a - 1 + a(N_\infty - 1) = 2 + 3 = 5$, and the theorem gives occurrence in the three weights $5 + l_j$, that is $7$, $6$ and $5$. The shift $5$ comes from the powers of the determinant at the embeddings other than $\Phi(v_0)$; the spread $l$ comes from the Schur polynomial at $\Phi(v_0)$.

**Theorem (Coefficient systems).** Let $a$ be odd, $i : K_0 \to E$ and $s_0 : K_0 \to \mathbb{C}$ embeddings, and $\kappa$ a weight for $E$. Then there are a representation $\xi$ of $\mathrm{GL}_a(E)$ extending $\kappa$ (up to conjugation of unitary elements), integers $\mu, N \in \mathbb{N}$ and central exponents $A$ with $A(s_0) = \mu$, such that for every jump $z$ of $\kappa$ at an embedding $\sigma$ over $s_0$: $z + \mu \geq 0$, and for every CM type $\Psi$ with $\Psi(v_0) = \sigma$ and no other embedding over $s_0$, the eigenvalues of every test eigenform of neat level for $\Psi$ with coefficients in $\xi$ occur in weight $z + \mu$, with parameter $N + 1$.

Lean: `New.Variety.exists_isCoefficientSystem` (Lib/Shimura/Transfer/WeightOccurs.lean), with `New.Variety.IsCoefficientSystem`.

*Proof.* Twist the representation of weight $\kappa$ by $m$-th powers of the norm of the determinant, with $m$ large. By the Weyl character formula its character becomes a product of a Schur polynomial $s_{l_\sigma}$ with natural exponents at each $\sigma$ over $s_0$, and $(-x_1)^m$ at the others. Each jump $z$ at $\sigma$ is some $l_{\sigma, j} - m$, so $z + \mu$ with $\mu = m a N_\infty$ is the weight of the last theorem. $\square$

**Remark (Formalization).** Only occurrence is proved. The source states no multiplicity, no transfer of the form to $\mathrm{GL}_n$ and no stabilisation. The source's docstring says that in the literature the same occurrence follows from the description of automorphic forms on unitary groups through $\mathrm{GL}_n$, due to Labesse and to Moeglin-Waldspurger. The shift $\mu$ depends on $\kappa$ through the choice of $m$, not on the form or the level. The CM type $\Psi$ in the statement is arbitrary among those with the stated property, so the chapter [on building the representations](/chapter/building-representations/) can choose it.
