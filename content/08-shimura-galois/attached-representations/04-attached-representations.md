---
title: Attached representations and their traces
lean:
  - Lib/GaloisRep/Main/AttachedRepresentations.lean
  - Lib/General/LinearAlgebra/MatrixPolynomials.lean
  - Lib/GaloisRep/Main/AllRanks.lean
  - New/Congruences/GaloisRepresentations/AttachedRepresentations.lean
decls:
  - New.IsTraceNondeg
  - New.GaloisRep.Attached
  - New.continuous_coeff_charpoly
  - New.norm_eq_one_of_continuous
  - New.norm_coeff_le_of_mul_monic
  - New.GaloisRep.Attached.tendsto_charpoly_coeff
  - New.GaloisRep.Attached.trace_eq
  - New.Selmer.coeff_zero_mul_coeff_star
  - New.Selmer.isConjSelfDual_of_attached
  - New.Patching.Isotypic.galRep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Attached representations and their traces

This section gives the definition of an attached representation and its first consequences. The characteristic polynomial of $\rho(g)$ is the limit of the Hecke polynomials at Frobenius elements that tend to $g$. So the characteristic polynomials, and the traces, are determined by the family $P$. At the end we prove, as a model of how the source uses the definition, that a representation attached to an eigenform is conjugate self-dual.

Fix a prime $\ell$. Write $\bar{\mathbb{Q}}_\ell$ for an algebraic closure of $\mathbb{Q}_\ell$ with its absolute value (Lean `PadicAlgCl ℓ`), and $\iota_\ell : \mathbb{C} \to \bar{\mathbb{Q}}_\ell$ for the fixed field isomorphism (Lean `ιℓ`, from the instance `New.PadicIso ℓ`). The absolute value is ultrametric: $|a + b| \leq \max(|a|, |b|)$. The field $\bar{\mathbb{Q}}_\ell$ is not complete, and nothing below needs completeness.

### Semisimplicity through the trace form

**Definition (Non-degenerate trace form).** Let $k$ be a field, $G$ a group and $r : G \to \mathrm{GL}_n(k)$ a homomorphism. Let $B$ be the $k$-span of the matrices $r(g)$. The representation $r$ has a *non-degenerate trace form* if every $x \in B$ with $\mathrm{tr}(x\, r(g)) = 0$ for all $g \in G$ is $0$.

Lean: `New.IsTraceNondeg` (Lib/General/LinearAlgebra/MatrixPolynomials.lean).

The span $B$ is the image of the group algebra $k[G]$, so it is a subalgebra of the matrices. The condition says that the bilinear form $(x, y) \mapsto \mathrm{tr}(xy)$ on $B$ is non-degenerate, since every $y \in B$ is a combination of the $r(g)$.

**Example.** Let $k$ be algebraically closed of characteristic $0$. Then $r$ has a non-degenerate trace form if and only if $r$ is semisimple.

*Proof.* Suppose that $r$ is semisimple. Then $k^n$ is a semisimple $B$-module on which $B$ acts faithfully, so $B$ is a semisimple algebra, a product of matrix algebras $M_{d_i}(k)$ by Wedderburn's theorem. The factor $M_{d_i}(k)$ acts on $k^n$ through $m_i \geq 1$ copies of its standard module, so the trace of $x = (x_i)$ on $k^n$ is $\sum_i m_i \mathrm{tr}(x_i)$. If $\mathrm{tr}(xy) = 0$ for all $y \in B$, take $y$ in the factor $i$: then $m_i \mathrm{tr}(x_i y_i) = 0$ for all $y_i$. Since $m_i \neq 0$ in $k$, $x_i = 0$. So $x = 0$.

Suppose next that the trace form is non-degenerate. Let $J$ be the Jacobson radical of $B$. It is a nilpotent ideal, since $B$ is finite dimensional. For $x \in J$ and $y \in B$ the product $xy$ lies in $J$, so it is nilpotent, and its trace is $0$. By the hypothesis $x = 0$. So $J = 0$, $B$ is semisimple, and every $B$-module, in particular $k^n$, is semisimple. $\square$

The source uses the trace form and not semisimplicity, because the trace form is a property of the span alone, and Section 7 builds the span from traces.

### The definition

**Definition (Attached representation).** Let $E$ be a number field in $\Omega$ and let $P$ assign a complex polynomial $P_w$ to each finite place $w$ of $E$. Let $H$ be a topological group, $\rho : H \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ a homomorphism and $j : H \to \Gamma_E$ a map. Then $\rho$ is *attached to $P$ through $j$* if:

1. $\rho$ is continuous;
2. $\rho$ has a non-degenerate trace form;
3. $j$ is an open map;
4. for every $\eta > 0$, for most Frobenius data $(w, A, s)$ (Section 3), every $x \in H$ with $j(x) = s$ and every $i \in \mathbb{N}$,
$$\bigl|\text{coefficient of } X^i \text{ in } \det(X - \rho(x)) - \iota_\ell(P_w)\bigr| \leq \eta.$$

If $j$ is not given, then $H = \Gamma_E$ and $j$ is the identity.

Lean: `New.GaloisRep.Attached` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

**Remark (Formalization).** Four points. First, $j$ is only an open map. It need not be continuous, injective or a homomorphism. In the proof of conjugate self-duality below, $j$ is the automorphism $g \mapsto cgc$ of $\Gamma_E$. If the image of $j$ misses an open set $U$, then data with $s \in U$ give no condition. Second, condition 4 is an inequality for each $\eta$, and the set of data in the filter may depend on $\eta$. There is no single finite set of bad places. Third, condition 4 reads $P_w$ only at places of prime norm, and only up to finitely many places for each open set (see the Example below). Fourth, the definition does not ask that $P_w$ is monic or of degree $n$. If $\rho$ is attached to $P$, then for each $\eta < 1$ the leading coefficient condition forces $|\iota_\ell(\text{coefficient of } X^n \text{ in } P_w) - 1| \leq \eta$ for most data, but nothing more.

This is the definition that finding F-053 of the [register of findings](/chapter/register-of-findings/) records: an approximation along a filter, not an equality at almost all places.

**Example.** The textbook notion implies the source notion. Let $\rho : \Gamma_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ be continuous and semisimple, and let $S$ be a finite set of places such that $\det(X - \rho(s)) = \iota_\ell(P_w)$ for every $w \notin S$ and every geometric Frobenius $s$ at a place over $w$. Then $\rho$ is attached to $P$. Conditions 1 and 3 are clear, and condition 2 is the Example above. For condition 4, the property "the place is not in $S$" holds for all but finitely many $w$ and implies a difference of $0$. The lemma `New.eventually_mostFrobenii` of Section 3 gives condition 4 for every $\eta$.

**Example.** Changing $P$ at finitely many places does not change the condition. Let $P'_w = P_w$ for all $w$ outside a finite set $T$. If $\rho$ is attached to $P$, then it is attached to $P'$: by Section 3, most data have their place outside $T$, and the intersection of two sets in the filter is in the filter. The same holds if $P'_w = P_w$ at every place of prime norm, since a Frobenius datum has a place of prime norm. So the junk values of an eigenform's family (Section 2) do not matter.

### Three lemmas on $\ell$-adic matrices

**Lemma.** For every $i$, the coefficient of $X^i$ in $\det(X - M)$ is a continuous function of $M \in M_n(\bar{\mathbb{Q}}_\ell)$.

Lean: `New.continuous_coeff_charpoly` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* The coefficient is a polynomial with integer coefficients in the entries of $M$: it is the coefficient of the characteristic polynomial of the generic matrix, evaluated at $M$. A polynomial is continuous. $\square$

**Lemma.** Let $G$ be a compact group and $\psi : G \to \bar{\mathbb{Q}}_\ell^\times$ a continuous character. Then $|\psi(g)| = 1$ for all $g$.

Lean: `New.norm_eq_one_of_continuous` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* The function $|\psi|$ is continuous on a compact space, so it has a maximum at some $a$. Then $|\psi(a)||\psi(g)| = |\psi(ag)| \leq |\psi(a)|$, so $|\psi(g)| \leq 1$. Also $|\psi(a)|/|\psi(g)| = |\psi(a g^{-1})| \leq |\psi(a)|$, so $|\psi(g)| \geq 1$. Here $|\psi(a)| \neq 0$ since $\psi(a)$ is a unit. $\square$

**Lemma.** Let $D$ and $R$ be polynomials over $\bar{\mathbb{Q}}_\ell$ with $R$ monic, and let every coefficient of $DR$ have absolute value at most $\eta$. Then every coefficient of $D$ has absolute value at most $\eta$.

Lean: `New.norm_coeff_le_of_mul_monic` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Let $\|F\|$ be the largest absolute value of a coefficient of $F$. By Gauss's lemma for an ultrametric absolute value, $\|DR\| = \|D\| \|R\|$. Since $R$ is monic, $\|R\| \geq 1$. So $|D_i| \leq \|D\| \leq \|D\|\|R\| = \|DR\| \leq \eta$. $\square$

The second and third lemmas are used where the source removes known characters from an attached representation. If $\det(X - \rho(s))$ factors as $\det(X - r(s)) \prod_l (X - \psi_l(s))$ and $\rho$ is attached to $P_w \prod_l (X - c_{l,w})$ with $\iota_\ell(c_{l,w}) = \psi_l(s)$, then the third lemma shows that $r$ is attached to $P$ (`Lib/GaloisRep/Main/AllRanks.lean`, line 295). The first lemma is the reason why condition 4 passes to limits.

### Characteristic polynomials as limits

**Theorem.** Let $\rho$ be attached to $P$ through $j$, let $x \in H$ and $i \in \mathbb{N}$. Then, for most data $(w, A, s)$ near $j(x)$, $\iota_\ell$ of the coefficient of $X^i$ in $P_w$ tends to the coefficient of $X^i$ in $\det(X - \rho(x))$.

Lean: `New.GaloisRep.Attached.tendsto_charpoly_coeff` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Let $c(z)$ be the coefficient of $X^i$ in $\det(X - \rho(z))$ for $z \in H$. By condition 1 and the first lemma, $c$ is continuous. Let $\eta > 0$. The set $U$ of $z$ with $|c(z) - c(x)| \leq \eta$ is a neighbourhood of $x$, so it contains an open set around $x$. Since $j$ is open, $j(U)$ is a neighbourhood of $j(x)$. Consider the data $(w, A, s)$ that satisfy condition 4 for this $\eta$ and have $s \in j(U)$. This set lies in the filter $\mathcal{F}_E(j(x))$: the first property defines a set of $\mathcal{F}_E$, and the second a set of the inverse image of the neighbourhoods of $j(x)$. For such a datum choose $z \in U$ with $j(z) = s$. Then $|c(z) - \iota_\ell(P_{w,i})| \leq \eta$ by condition 4, and $|c(z) - c(x)| \leq \eta$. By the ultrametric inequality $|\iota_\ell(P_{w,i}) - c(x)| \leq \eta$. So $\iota_\ell(P_{w,i})$ lies in the closed ball of radius $\eta$ about $c(x)$ for most data near $j(x)$. Closed balls form a basis of neighbourhoods. $\square$

The ultrametric inequality is used in the form "every point of a closed ball is a centre". Over $\mathbb{C}$ the same proof gives the bound $2\eta$, which also suffices.

**Theorem (Uniqueness of traces).** Let $\rho$ on $H$ and $\sigma$ on $G$, both of rank $n$, be attached to the same $P$ through $j$ and $j'$. If $j(x) = j'(y)$, then $\det(X - \rho(x)) = \det(X - \sigma(y))$, and in particular $\mathrm{tr}\, \rho(x) = \mathrm{tr}\, \sigma(y)$.

Lean: `New.GaloisRep.Attached.trace_eq` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Let $g = j(x) = j'(y)$. By the theorem above, for each $i$ the coefficients $\iota_\ell(P_{w,i})$ tend, along $\mathcal{F}_E(g)$, both to the coefficient of $X^i$ in $\det(X - \rho(x))$ and to that in $\det(X - \sigma(y))$. The filter $\mathcal{F}_E(g)$ is not trivial (Section 3), and $\bar{\mathbb{Q}}_\ell$ is Hausdorff. So the limits are equal. The trace is the sum of the roots of the characteristic polynomial. $\square$

**Remark (Formalization).** The Lean statement concludes only the equality of traces. The equality of characteristic polynomials is the first step of its proof. This is where Chebotarev enters the theory of attached representations: without the non-triviality of $\mathcal{F}_E(g)$, limits would not be unique. With $H = G = \Gamma_E$ and $j = j'$ the identity, two representations attached to $P$ have the same character, and the Brauer-Nesbitt form of Section 7 (Lean `New.IsTraceNondeg.exists_conj_of_trace_eq`) makes them conjugate.

### The chosen representation

**Definition (Chosen attached representation).** For an isotypic space $x$ of forms of weight $\kappa$, with chosen Hecke eigenvalues and Hecke polynomials $P^x_w$, the representation $r_x$ is a chosen homomorphism $\Gamma_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ attached to $P^x$, or an arbitrary homomorphism if none exists.

Lean: `New.Patching.Isotypic.galRep` (Lib/GaloisRep/Main/AllRanks.lean).

**Remark (Formalization).** This is finding F-049. The definition is `Classical.epsilon (Attached x.heckePolyAt)`, at line 623 of `Lib/GaloisRep/Main/AllRanks.lean`. The eigenvalues are themselves a `choose` (`Isotypic.heckeEigenvalues`, line 614), so $P^x$ is one chosen family among the families that cut out $x$. The object $r_x$ has exactly the properties of the predicate `Attached` once existence is proved, and no others. By the uniqueness of traces its character does not depend on the choice.

### A consumer: conjugate self-duality

Let $E$ now be a CM field, the CM field of the data of the argument (Lean `D.E` for data `D`), and let $c$ be the chosen complex conjugation in $\mathrm{Gal}(\Omega/\mathbb{Q})$. Let $g^c = cgc$ (Lean `New.conjGal`), and let $\chi$ be the inverse of the $\ell$-adic cyclotomic character (Lean `New.Selmer.cyclotomicInv`). At a geometric Frobenius at a place $w$ prime to $\ell$, $\chi$ takes the value $q_w$.

**Lemma.** Let $f \neq 0$ be a function on $G_f$ of rank $k + 1$, spherical at the split place $w$ with Hecke polynomial $Q_w$ and at $\bar w$ with Hecke polynomial $Q_{\bar w}$. Then
$$Q_{w,0} \cdot Q_{\bar w,k} = q_w^k \cdot Q_{w,1},$$
where $Q_{w,i}$ is the coefficient of $X^i$.

Lean: `New.Selmer.coeff_zero_mul_coeff_star` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Let $s_j$ and $u_j$ be the eigenvalues of $T_{w,j}$ and $T_{\bar w,j}$ on $f$. By the duality of the Hecke operators at $w$ and $\bar w$ ([Theorem](/decl/New.heckeSplit_dual/), in [Iwahori and Satake](/chapter/iwahori-satake/)), $\pi(\varpi) T_{\bar w,i} f = T_{w,j} f$ for $i + j = k + 1$. With $i = 0$ this says that the scalar $\varpi$ acts on $f$ by $s_{k+1}$. With $i = 1$ it gives $u_1 s_{k+1} = s_k$. By the coefficient lemma of Section 2, $Q_{w,0} = (-1)^{k+1} q_w^{\binom{k+1}{2}} s_{k+1}$, $Q_{w,1} = (-1)^k q_w^{\binom{k}{2}} s_k$ and $Q_{\bar w,k} = -u_1$. Since $\binom{k+1}{2} = \binom{k}{2} + k$, the identity follows. $\square$

**Theorem (Attached representations are conjugate self-dual).** Let $f$ be an eigenform for $Q$ of rank $n$, and let $r : \Gamma_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ be attached to $Q$. Then $r$ is continuous, has a non-degenerate trace form, and for all $g \in \Gamma_E$
$$\mathrm{tr}\, r(g^c) = \chi(g)^{n-1}\, \mathrm{tr}\, r(g^{-1}).$$

Lean: `New.Selmer.isConjSelfDual_of_attached` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* The first two properties are conditions 1 and 2. For $n = 0$ both traces are $0$. Let $n = k + 1$.

Step 1. The map $g \mapsto g^c$ is a homeomorphism, so an open embedding. If $(w, A, s)$ is a Frobenius datum and $x^c = s$, then $(\bar w, \bar A, x)$ is a Frobenius datum, where $\bar A$ is the conjugate place. The transport lemma of Section 3 (`New.eventually_mostFrobenii_of_isOpenEmbedding`, with $\pi(w) = \bar w$) then shows that $r$ is attached to the family $w \mapsto Q_{\bar w}$ through $g \mapsto g^c$.

Step 2. For all but finitely many $w$ of prime norm, $w$ and $\bar w$ are split with Hecke polynomials $Q_w$ and $Q_{\bar w}$, and $w$ is prime to $\ell$. For most data the lemma above therefore gives
$$\iota_\ell(Q_{w,0})\, \iota_\ell(Q_{\bar w,k}) = \chi(s)^k\, \iota_\ell(Q_{w,1}).$$

Step 3. Take the limit along $\mathcal{F}_E(g)$. By the theorem on limits, applied to $r$ and to $r$ through $g \mapsto g^c$ at the point $g^c$ (whose image is $(g^c)^c = g$), and by continuity of $\chi$:
$$a_0(r(g))\, a_k(r(g^c)) = \chi(g)^k\, a_1(r(g)),$$
where $a_i(M)$ is the coefficient of $X^i$ in $\det(X - M)$.

Step 4. For an invertible $M$ of size $k + 1$, $a_0(M) = (-1)^{k+1} \det M$, $a_k(M) = -\mathrm{tr} M$, and $a_1(M) = (-1)^{k+1} \det M \cdot (-\mathrm{tr} M^{-1})$, from $\det(X - M) = (-1)^{k+1} \det M \cdot X^{k+1} \det(X^{-1} - M^{-1})$. Substitute and cancel the nonzero factor $(-1)^{k+1}\det r(g)$. $\square$

**Remark (Formalization).** Lean writes the exponent as the natural number $t - 1$ with $t = n$, so $n = 0$ is read as $n = 1$. In that case both traces are $0$ and the statement holds. The proof uses only conditions 1, 2 and 4 of the definition, the duality of Hecke operators, and Chebotarev through the non-triviality of $\mathcal{F}_E(g)$. It is the template for the other consumers: prove an identity of Hecke polynomials at most places, then pass to the limit.
