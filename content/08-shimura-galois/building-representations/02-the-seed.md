---
title: Killing polynomials and the seed representation
lean:
  - Lib/GaloisRep/KillingPolynomials.lean
  - Lib/GaloisRep/Main/SeedRepresentation.lean
  - Lib/GaloisRep/Main/CuspidalTypes.lean
  - Lib/General/LinearAlgebra/MatrixPolynomials.lean
decls:
  - New.HasNoSmallRelations
  - New.card_eq_and_charpoly_eq
  - New.Variety.exists_isCuspidalType
  - New.GaloisRep.exists_rep_of_cuspidal_type
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Killing polynomials and the seed representation

This section constructs the first representations of the chain. The input is the cohomology of a Shimura variety. The cohomology gives a representation of large rank, and the congruence relation gives polynomials that kill its Frobenius elements. The task is to extract a representation of the right rank $n$ whose characteristic polynomials are the Hecke polynomials. The tool is a lemma on killing polynomials. It works when the weight is far from degenerate at one embedding. The result of the section, [the seed theorem](/decl/New.GaloisRep.exists_rep_of_cuspidal_type/), is the only place in the chain where the characteristic polynomial is computed exactly. Every later step only takes limits and cancels characters.

### Why killing is not enough

Let $r$ be a representation of rank $N$, and let a monic polynomial $P_v$ of degree $n$ kill $r(\mathrm{Frob}_v)$ for most $v$. Two things can go wrong. The rank $N$ can be larger than $n$: the representation $r \oplus r$ has the same killing polynomials as $r$. And even if $N = n$, the polynomial $P_v$ is the characteristic polynomial only when the minimal polynomial of $r(\mathrm{Frob}_v)$ has degree $n$. The scalar matrix $1$ of rank $2$ is killed by $(X-1)(X-2)$. So one needs a way to see that $r(\mathrm{Frob}_v)$ has $n$ distinct eigenvalues, and that $r$ has no repeated pieces.

The source finds both facts near the identity, through Hodge-Tate theory. Near $1$, an $\ell$-adic representation that is Hodge-Tate looks like the cocharacter $T \mapsto \operatorname{diag}(T^{\kappa_1}, \dots, T^{\kappa_N})$, where the $\kappa_j$ are its Hodge-Tate jumps at one embedding. If the jumps are very different integers, this torus element has many distinct eigenvalues, and polynomial relations among small powers of it are impossible. The next definition makes "very different" exact.

**Definition (Free integers).** Integers $e_1, \dots, e_n$ are *free* if two vectors $\alpha, \beta \in \mathbb N^n$ with $\sum_i \alpha_i = \sum_i \beta_i \leq (n+1)^2$ and $\sum_i \alpha_i e_i = \sum_i \beta_i e_i$ are equal.

Lean: `New.HasNoSmallRelations` (Lib/General/LinearAlgebra/MatrixPolynomials.lean).

**Example.** Let $y_0 > y_1 > \dots > y_{n-1} \geq 0$ be natural numbers with $y_j < y_i / (n+1)^2$ for all $i < j$. Then the integers $-y_0, \dots, -y_{n-1}$ are free (Lean: `New.hasNoSmallRelations_of_lacunary`). For $n = 2$ one can take $y = (100, 1)$, since $1 < 100/9$. Two vectors with $\alpha_0 + \alpha_1 = \beta_0 + \beta_1 = d \leq 9$ and $100\alpha_0 + \alpha_1 = 100\beta_0 + \beta_1$ give $99(\alpha_0 - \beta_0) = 0$ after subtracting $d$. The weights of the forms in Section 3 are chosen of this lacunary kind (Lean: `New.hasNoSmallRelations_of_rapid_decrease`).

### The lemma on killing polynomials

Let $k$ be a field. For a square matrix $y$ over $k$ and $m \geq 1$, consider the matrix with rows indexed by the entries and with columns $1, y, y^2, \dots, y^{m-1}$, each written as a vector of entries. Its $m \times m$ minors all vanish exactly when $1, y, \dots, y^{m-1}$ are linearly dependent, that is, when the minimal polynomial of $y$ has degree less than $m$. These minors are polynomials in the entries of $y$. So "the minimal polynomial has degree at most $n$" is a closed algebraic condition. The source calls these minors the minors of the powers (Lean: `New.powMinor`).

**Theorem (Killing polynomials are characteristic).** Let $E \subset \Omega$ be a number field, let $K$ be a normed field, and let $r : \operatorname{Gal}(\Omega/E) \to \mathrm{GL}_N(K)$ be a continuous homomorphism. Let $k$ be a normed field over $K$, and let $n \geq 1$. Suppose:

1. the $K$-span of the image of $r$ contains every diagonal matrix;
2. for most Frobenius data $v$, the polynomial $P_v \in K[X]$ is monic of degree $n$ and $P_v(r(\mathrm{Frob}_v)) = 0$;
3. integers $e_1, \dots, e_n$ are free, and each $e_i$ occurs among the integers $\kappa_1, \dots, \kappa_N$;
4. there is $Q \in \mathrm{GL}_N(k)$ such that every polynomial $h$ in the $N^2$ entries, with coefficients in $k$, that vanishes at $Q\,r(g)$ for all $g$ near $1$ also vanishes at $\operatorname{diag}(T^{\kappa_1}, \dots, T^{\kappa_N})\,Q$ over the Laurent polynomial ring $k[T, T^{-1}]$.

Then $N = n$, and $P_v$ is the characteristic polynomial of $r(\mathrm{Frob}_v)$ for most Frobenius data $v$.

Lean: `New.card_eq_and_charpoly_eq` (Lib/GaloisRep/KillingPolynomials.lean).

*Proof.* Work with the conjugate $\varphi(r(g)) = Q\,r(g)\,Q^{-1}$ over $k$. The minors of the powers of order $n+1$ vanish at $r(\mathrm{Frob}_v)$ for most $v$, by hypothesis 2. The set where they vanish is closed, and the Frobenius elements of most Frobenius data are dense in each open set. So these minors vanish at $\varphi(r(g))$ for all $g$. By hypothesis 4, applied to the polynomial $Y \mapsto$ minor of $Y Q^{-1} \varphi(r(x))$, they also vanish at $\operatorname{diag}(T^{\kappa})\,\varphi(r(x))$ for every $x$. The source now applies a lemma on free integers (Lean: `New.HasNoSmallRelations.inv_scalar_on_blocks`). It says the following. If the minors of order $m \leq n+1$ vanish at $\operatorname{diag}(T^{e \circ c})\,x$ for a map $c$ onto $\{1, \dots, n\}$, then $n < m$, and $x^{-1}$ is scalar on each block $\{a : c(a) = \text{const}\}$ and has no entries between two members of one block. First, the integers $\kappa_j$ take only the $n$ values $e_i$: otherwise the torus would have $n+1$ distinct weights and a minor of order $n+1$ would survive. So $\kappa = e \circ c$ with $c$ onto. If $c(a) = c(b)$ with $a \neq b$, every $\varphi(r(g))$, and so every element of the span of the image, has entry $0$ at $(a, b)$ and equal entries at $(a, a)$ and $(b, b)$. The span contains the conjugates of all diagonal matrices by hypothesis 1, and a short computation shows that this is impossible. So $c$ is a bijection, and $N = n$. Second, the minors of order $n$ do not vanish on any nonempty open set, since the same lemma would then give $n < n$. So for most $v$ the minimal polynomial of $r(\mathrm{Frob}_v)$ has degree $n = N$. It is then the characteristic polynomial. The monic polynomial $P_v$ of degree $n$ kills $r(\mathrm{Frob}_v)$, so it is a multiple of the minimal polynomial of the same degree, and the two are equal. $\square$

Hypothesis 4 is the form in which the source uses the Hodge-Tate cocharacter. The source proves the needed fact in $\mathbb C_p$ coordinates. Let $x_i \in \mathbb C_p$ and $\kappa_i \in \mathbb Z$. If a polynomial vanishes at $(\chi(g)^{-\kappa_i} g(x_i))_i$ for all $g$ in $\operatorname{Gal}(\bar{\mathbb Q}_p/\mathbb Q_p)$ near $1$, with $\chi$ the cyclotomic character, then it vanishes at $(T^{\kappa_i} x_i)_i$ (Lean: `New.Period.aeval_cocharacter_eq_zero`). This is the statement that the Hodge-Tate cocharacter lies in the algebraic monodromy group, after Serre, *Groupes algébriques associés aux modules de Hodge-Tate*, Astérisque 65 (1979), §1, and Sen, Ann. of Math. 97 (1973).

### Cuspidal types

The seed theorem needs one more local hypothesis, at a split place $w_0$. Let $\varpi$ be a uniformizer of $E_{w_0}$, and let $K_1 = 1 + \varpi M_N(\mathcal O_{w_0})$. A character $\chi$ of $K_1$ is a *cuspidal type* if, for every idempotent matrix $\varepsilon \neq 0, 1$, it is nontrivial on the elements of $K_1$ in $1 + \varepsilon M_N(\mathcal O_{w_0})(1 - \varepsilon)$. In words: $\chi$ is nontrivial on the unipotent radical of every proper parabolic subgroup. A form on which $K_1$ acts by such a character cannot come from a proper parabolic subgroup at $w_0$.

**Proposition (Cuspidal types exist).** Let $N \geq 1$ and let $w$ be a finite place. Some character of $1 + \varpi M_N(\mathcal O_w)$ is a cuspidal type and is trivial on $1 + \varpi^2 M_N(\mathcal O_w)$.

Lean: `New.Variety.exists_isCuspidalType` (Lib/GaloisRep/Main/CuspidalTypes.lean).

*Proof.* Choose an integral matrix $b$ whose characteristic polynomial is irreducible modulo $w$ (Lean: `New.Variety.exists_irreducible_charpoly_residue`), and an additive character $u$ of $E_w/\varpi^2\mathcal O_w$ with $u(\varpi) \neq 0$. Put $\chi(k) = \exp(2\pi i\, u(\operatorname{tr}(b(k-1))))$. The map $k \mapsto \operatorname{tr}(b(k-1))$ is additive modulo $\varpi^2$ on $K_1$, so $\chi$ is a character trivial on $1 + \varpi^2 M_N(\mathcal O_w)$. For an idempotent $\varepsilon \neq 0, 1$, the reduction of $b$ does not stabilize the image of $\varepsilon$, since its characteristic polynomial is irreducible. So some matrix $\varpi x$ with $x \in \varepsilon M_N(1 - \varepsilon)$ has $\operatorname{tr}(b\varpi x) \notin \varpi^2\mathcal O_w$, and $\chi$ is nontrivial there. $\square$

### The seed theorem

The polynomial $P_w$ is the Hecke polynomial of $f$ at the split place $w$, as in Section 1. The multiset of jumps of the weight $\kappa$ at an embedding $\sigma$ is $\{j - 1 - \lambda_j\}$ if $\sigma$ is in the CM type, and $\{\lambda_j + N - j\}$ otherwise, for $1 \leq j \leq N$, with $\lambda$ the highest weight of $\kappa$ at the place of $\sigma$.

**Theorem (The seed representation).** Let $E$ be a CM field that contains a primitive root of unity of order $5040$ and the field $\mathbb Q(\sqrt{-d})$. Let $a$ be odd, and let $f$ be a form of weight $\kappa$ on the definite unitary group of rank $a$, spherical off a finite set $S$ with Hecke polynomials $P_w$. Let $w_0 \in S$ lie over a split prime of $\mathbb Q(\sqrt{-d})$ prime to $d$, and let $K_1 = 1 + \varpi M_a(\mathcal O_{w_0})$ act on $f$ by a cuspidal type $\chi$. Let $v$ be a place with $v, \bar v \notin S$, over the same place of $\mathbb Q(\sqrt{-d})$ as $w_0$. Let $\varepsilon : \Omega \to \bar{\mathbb Q}_\ell$ induce $v$, and let $\kappa$ have $a$ free jumps $e_1, \dots, e_a$ at the embedding $\iota_\ell^{-1} \circ \varepsilon$. Let $w'$ be a place over a split prime of $\mathbb Q(\sqrt{-d})$ prime to $d$ such that, if $w'$ lies over $\ell$, it lies over the same prime as $w_0$. Then there is a continuous $r : \operatorname{Gal}(\Omega/E) \to \mathrm{GL}_a(\bar{\mathbb Q}_\ell)$ such that

1. $\det(X - r(\mathrm{Frob}_y)) = \iota_\ell(P_{y})$ for most Frobenius data $y$;
2. if $w', \bar w' \notin S$, then at every place above $w'$ the representation $r$ is unramified or crystalline, its jumps are exactly those of $\kappa$, and $\iota_\ell(P_{w'})$ kills its geometric Frobenius elements.

Lean: `New.GaloisRep.exists_rep_of_cuspidal_type` (Lib/GaloisRep/Main/SeedRepresentation.lean).

*Proof.* The proof has three steps.

First, $f$ is moved to a form $\psi$ on $\mathrm{GL}_a(\mathbb A_{E,f})$ that vanishes off the definite frames, has a central character, and has at each split place the same local translates as $f$, up to one linear map (Lean: `New.GaloisRep.exists_central_eigenform`).

Second, for each embedding $\tau_0 : E \to \mathbb C$, the eigenvalues of $\psi$ are realized in the cohomology of a PEL model of signature $(1, a-1)$, built in [the integral model](/chapter/integral-model/), through the transfer and the congruence relation of [Chapter 3](/chapter/congruence-relation/). The cuspidal type is the local hypothesis under which the transfer applies. This gives a continuous representation $\rho_{\tau_0}$ with three properties at almost all places $w$: it is unramified or crystalline above $w$, the jumps of $\kappa$ at $\tau_0$ occur among its jumps, and $\iota_\ell(P_w)$ kills its geometric Frobenius elements. Its rank can be large. To reach the embedding $\tau_0$, the source chooses a second CM type whose distinguished embedding is $\tau_0$, and twists the eigenvalues of $\psi$ by an algebraic Hecke character $\omega$. An auxiliary split place $w_1$ with pro-$p$ Iwahori level makes the level neat.

Third, the $\rho_{\tau_0}$ are joined. Take the semisimplification of $\bigoplus_{\tau_0} \rho_{\tau_0}$ and keep each irreducible constituent once. The result $r_1$ has the jumps of $\kappa$ at every embedding at once, the same killing polynomials, and the span of its image contains the diagonal matrices (Lean: `New.GaloisRep.exists_rep_span_diagonal`). The free jumps at $\varepsilon$ and the cocharacter fact give hypothesis 4 of [the theorem on killing polynomials](/decl/New.card_eq_and_charpoly_eq/), with $\kappa_j$ the jumps of $r_1$ at $\varepsilon$. That theorem gives rank $a$ and the characteristic polynomials (Lean: `New.GaloisRep.exists_galRep_charpoly_eq_of_forall_embedding`). With rank $a$, the jumps that occur are all the jumps, which gives the equality in part 2. $\square$

**Remark (Formalization).** Part 1 is an equality of characteristic polynomials along the filter "most Frobenii", and not at all places outside a finite set. The filter is defined in [the previous chapter](/chapter/attached-representations/): a set of Frobenius data belongs to it if each nonempty open subset of the Galois group has a nonempty open part whose Frobenius elements at almost all places lie in the set. Part 2 is only stated at one place $w'$ at a time, and only if $w'$ lies over a split prime of $\mathbb Q(\sqrt{-d})$. The theorem has no conclusion at places of $S$. These are the exact limits of the seed. Section 3 removes the hypotheses on the type and on the jumps, at the price of approximate attachment.
