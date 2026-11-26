---
title: The odd part and the uniform bound
lean:
  - Lib/GaloisRep/Main/SelmerModules.lean
  - Lib/Cyclotomic/OddSha.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.shaLocalSet
  - New.Selmer.shaOdd
  - New.length_shaOdd_zero_le_addVal_classNumber
  - New.OddPart.exists_detecting_points_cocycles
  - New.exists_character_components
  - New.OddPart.nsmul_shaOdd_eq_zero_of_isStickelbergerBound
  - New.OddPart.length_shaOdd_le_addVal_pow
  - New.OddPart.length_shaOdd_le_of_le_sq
  - New.OddPart.length_shaOdd_le_of_sq_lt
  - New.exists_length_shaOdd_le
  - New.Selmer.eventually_length_shaOdd_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The odd part and the uniform bound

This section goes from $\mathbb{Q}$ back to the CM field $E$. It defines the module $\text{Ш}_{\mathrm{odd}}$ that the argument needs, splits it into the components of Section 5 by characters mod $N$, and puts the two bounds of Sections 5 and 6 together. The result is one integer $X$ whose valuation bounds the length of $\text{Ш}_{\mathrm{odd}}$ at every prime $\ell$. The section ends with the places where the argument uses $X$.

### The classical statement

Let $E$ be a CM field, $\ell$ a prime and $e \ge 1$. The Tate-Shafarevich group $\text{Ш}^1(E, \mathbb{Z}/\ell^n(-e))$ is the group of classes in $H^1(E, \mathbb{Z}/\ell^n(-e))$ that are locally trivial at all places, or, in the form used here, unramified away from $\ell$ and trivial at the places above $\ell$. Section 2 explains that its odd part is a twisted form of a minus part of a class group. For $\ell$ large with respect to $E$ and $e$, the main conjecture of Mazur and Wiles, and Greither's extension to abelian fields (C. Greither, Ann. Inst. Fourier 42 (1992), Thm. 3.2, cited in Section 2), compute the order of such odd parts by values of $\ell$-adic L-functions. Over all $\ell$ at once this gives no explicit integer. The source needs one explicit integer for all $\ell$, and an upper bound is enough.

### The module

Let $E \subseteq \Omega$ be a CM field, let $\ell$ be a prime, let $\Lambda$ be a $\mathbb{Z}_\ell$-algebra, and let $e, \nu \ge 0$. Let $c$ be the complex conjugation of Section 5. As $E$ is CM, $c$ normalizes $\mathrm{Gal}(\Omega/E)$, and $g \mapsto cgc$ is an automorphism of $\mathrm{Gal}(\Omega/E)$.

**Definition.** The set $D_\ell^e(E) \subseteq \mathrm{Gal}(\Omega/E)$ is, for $e = 0$, the union of the inertia groups at the places of $\Omega$ above $\ell$, and for $e \ne 0$, the set of $g$ in the decomposition group of a place above $\ell$ with $\mathrm{cyc}_\ell(g) = 1$.

Lean: `New.Selmer.shaLocalSet` (Lib/GaloisRep/Main/SelmerModules.lean).

**Definition.** The module $\text{Ш}_{\mathrm{odd}} = \text{Ш}_{\mathrm{odd}}(\ell, E, \Lambda, e, \nu)$ consists of the maps $z : \mathrm{Gal}(\Omega/E) \to \Lambda/\ell^\nu$ such that:

1. $z$ is a locally constant cocycle for $\mathrm{cyc}_\ell^{-e}$: $z(gh) = z(g) + \mathrm{cyc}_\ell(g)^{-e} z(h)$;
2. $z$ vanishes on the inertia groups at the places of $E$ not above $\ell$;
3. $z$ vanishes on $D_\ell^e(E)$;
4. if $e \ne 0$, then $z(cgc) = -z(g)$ for all $g$.

Lean: `New.Selmer.shaOdd` (Lib/GaloisRep/Main/SelmerModules.lean).

For $e = 0$ the cocycle relation says that $z$ is a homomorphism. Conditions 2 and 3 then say that it is unramified at all places. So $\text{Ш}_{\mathrm{odd}}(\ell, E, \Lambda, 0, \nu)$ is the group of unramified homomorphisms to $\Lambda/\ell^\nu$, and there is no parity condition. For $e \ne 0$, condition 3 asks that $z$ vanish on the part of the decomposition group above $\ell$ that fixes $\mu_{\ell^\infty}$.

**Remark (Formalization).** The source calls the module a model of the odd part of $\text{Ш}^1(E, \Lambda/\ell^\nu(-e))$. The file docstring says that no comparison with $\text{Ш}^1$ is proved. The module is a module of cocycles, not of classes: nothing is divided by coboundaries. The values are written as vectors of length one, because the definition is a special case of the Selmer modules of the source for representations of any rank. The argument needs only an upper bound for the length of this module of cocycles, and the bound below is for exactly this module. For $e = 0$ the module is a module of homomorphisms, so no question of coboundaries arises.

### The case $e = 0$

**Proposition.** Let $E$ be a CM field, $\ell$ a prime, $\mathcal{O}$ the ring of integers of a finite extension of $\mathbb{Q}_\ell$, and $n \ge 0$. Then
$$\mathrm{length}_{\mathcal{O}}\, \text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, 0, n) \le v_{\mathcal{O}}(h_E),$$
where $v_{\mathcal{O}}$ is the normalized valuation of $\mathcal{O}$.

Lean: `New.length_shaOdd_zero_le_addVal_classNumber` (Lib/Cyclotomic/OddSha.lean).

*Proof.* By class field theory (see [class field theory](/chapter/class-field-theory/)), the maximal unramified abelian extension of $E$ has Galois group $\mathrm{Cl}(E)$. Write $\mathrm{Cl}(E) = \prod_i \mathbb{Z}/m_i$ with generators the images of elements $p_i$ of $\mathrm{Gal}(\Omega/E)$, so $\prod_i m_i \mid h_E$. Every unramified homomorphism $z$ has $m_i z(p_i) = 0$, and it is $0$ if it vanishes at all $p_i$. Evaluation at the $p_i$ embeds the module into $\prod_i (\mathcal{O}/\ell^n)[m_i]$, of length at most $v_{\mathcal{O}}(\prod_i m_i) \le v_{\mathcal{O}}(h_E)$. $\square$

The last step is a general lemma on lengths. If $Z$ is a module of maps to a cyclic module $\mathcal{O}/\ell^n$, if $n_i z(q_i) = 0$ for all $z \in Z$, and if only $0$ vanishes at all $q_i$, then the length of $Z$ is at most $v_{\mathcal{O}}(\prod_i n_i)$ (Lean: `New.OddPart.length_le_of_detecting_points`). The rest of the section applies this lemma with $n_i$ an annihilator and the $q_i$ detecting points.

### Detecting points over $E$

**Lemma.** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a number field and $\ell$ a prime. There is a finite set $s \subseteq \mathrm{Gal}(\Omega/E)$ such that:

1. $|s| \le y^{20}$ for every $y$ with $N \le y$ and $\ell \le y^2$;
2. for every ring of integers $\mathcal{O}$ of a finite extension of $\mathbb{Q}_\ell$, all $n, e$, every locally constant cocycle $z : \mathrm{Gal}(\Omega/E) \to \mathcal{O}/\ell^n$ for $\mathrm{cyc}_\ell^{-e}$ that is unramified at the places not above $\ell$ and vanishes on $s$ is $0$.

Lean: `New.OddPart.exists_detecting_points_cocycles` (Lib/Cyclotomic/OddSha.lean).

*Proof.* Put $M = N\ell^2$ and $K = \mathbb{Q}(\mu_M)$, so $E \subseteq K$. The points are representatives of the cosets of $\mathrm{Gal}(\Omega/K)$ in $\mathrm{Gal}(\Omega/E)$, at most $\varphi(M)$ of them, and a set of generators for unramified homomorphisms on $\mathrm{Gal}(\Omega/K)$ killed by $M$. Such a homomorphism factors through a ray class group of $K$ built from the ideles that are $M$-th powers at the places above $\ell$. The source bounds the class number of $K$ times the index of these ideles by $2^{M^3 + 5M^2 + M}$, from a bound for the class number by the discriminant and $|d_K| \le M^{[K:\mathbb{Q}]}$. So at most $M^3 + 5M^2 + M$ generators are needed, and $\varphi(M) + M^3 + 5M^2 + M \le y^{20}$ for $N \le y$ and $\ell \le y^2$. Now let $z$ vanish on the points and let $\ell^k z = 0$. Use induction on $k$. As $\ell \mid M$, the cocycle $Mz$ is killed by $\ell^{k-1}$ and vanishes on the points, so $Mz = 0$ by the induction hypothesis. Then $\mathrm{Gal}(\Omega/K)$ acts trivially on the values of $z$, so $z$ restricted to $\mathrm{Gal}(\Omega/K)$ is an unramified homomorphism killed by $M$, and it is $0$. If $g = x\,r$ with $x \in \mathrm{Gal}(\Omega/K)$ and $r$ the representative of the coset of $g$, then $z(g) = z(x) + z(r) = 0$. $\square$

The docstring calls this a cocycle analogue, with the crude bound $y^{20}$, of the class field theory bound on the number of generators of the Galois group of the maximal pro-$\ell$ extension unramified outside $\ell$.

### Splitting by characters

Let $\mathcal{O}$ have enough roots of unity for the characters mod $N$: it contains a primitive root of unity of order the exponent of $(\mathbb{Z}/N)^\times$. Then the characters $\psi$ mod $N$ with values in $\mathcal{O}$ are all characters of $(\mathbb{Z}/N)^\times$, and they satisfy the orthogonality relations.

**Lemma (character components).** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a CM field, $\ell$ a prime, $\mathcal{O}$ as above, $e \ne 0$ and $n \ge 0$. There are $\sigma : (\mathbb{Z}/N)^\times \to G$ and $b : G \times G \to \mathrm{Gal}(\Omega/E)$, independent of the cocycle, such that for every $x \in \text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n)$, the maps
$$z_\psi(g) = \sum_{t \in (\mathbb{Z}/N)^\times} \Upsilon_\psi(\sigma(t))\, x\big(b(\sigma(t), g)\big), \qquad \Upsilon_\psi = \mathrm{cyc}^e\psi,$$
satisfy:

1. $z_\psi \in C_n(\ell, e, \psi)$ for every $\psi$;
2. if $z_\psi = 0$ for every $\psi$ with $\Upsilon_\psi(c) = -1$, then $4\varphi(N)\, x = 0$.

Lean: `New.exists_character_components` (Lib/Cyclotomic/OddSha.lean).

*Proof.* Choose lifts $\sigma(t) \in G$ of the units $t$, with $\sigma(1) = 1$. For $g \in G$, the commutator $cgc^{-1}g^{-1}$ fixes $\mu_N$, as $\mathrm{Gal}(\mathbb{Q}(\mu_N)/\mathbb{Q})$ is abelian, so it lies in $\mathrm{Gal}(\Omega/E)$. Let $b(u, g)$ be its conjugate by $u$. The cyclotomic character is $1$ at $b(u, g)$, so $x$ is additive there. With this, the cocycle rule for $z_\psi$ follows: the term for $u$ depends only on the coset of $u$ modulo $G_N$, and right multiplication by $g$ permutes these cosets. The local conditions of $C_n$ follow from those of $\text{Ш}_{\mathrm{odd}}$: the conjugates of an element of inertia away from $\ell$, or of a decomposition element above $\ell$ with trivial cyclotomic character, lift to elements where $x$ vanishes, and $b(u, c) = 1$ gives $z_\psi(c) = 0$. For property 2, the orthogonality relations give
$$\sum_\psi z_\psi(h) = \varphi(N)\big(x(chc) - x(h)\big), \qquad h \in \mathrm{Gal}(\Omega/E).$$
Each $\Upsilon_\psi(c)$ is $\pm 1$. The odd $z_\psi$ are $0$ by hypothesis, and an even $z_\psi$, being in $C_n$ with $z_\psi(c) = 0$, takes the same value at $chc$ and at $h$. So the left side takes the same value at $chc$ and at $h$, and $\varphi(N)(x(h) - x(chc)) = \varphi(N)(x(chc) - x(h))$. With $x(chc) = -x(h)$ this gives $4\varphi(N)\,x(h) = 0$. $\square$

**Remark (Formalization).** The maps $\sigma$ and $b$ are chosen with `choose`. The lemma needs the hypothesis that $\mathcal{O}$ has enough roots of unity. Without it the characters with values in $\mathcal{O}$ do not separate the units mod $N$. This is why the main theorem below has the same hypothesis. The argument meets it by passing to a large coefficient ring: see the end of the section.

### The annihilator and the two ranges of $\ell$

**Proposition.** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a CM field, $\ell$ a prime, $\mathcal{O}$ with enough roots of unity for the characters mod $N$, $e \ne 0$, and $X$ with the Stickelberger property for $N$ and $e$. Then $4\varphi(N) \cdot 4X^2$ kills $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n)$.

Lean: `New.OddPart.nsmul_shaOdd_eq_zero_of_isStickelbergerBound` (Lib/Cyclotomic/OddSha.lean).

*Proof.* The components of $4X^2 z$ are $4X^2$ times those of $z$. The odd ones vanish by the annihilation theorem of Section 5. By the lemma on character components, $4\varphi(N)$ kills $4X^2 z$. $\square$

**Lemma.** Let $E$ be a CM field. If $m \in \mathbb{N}$ kills $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n)$, and only $0$ vanishes at all of the at most $k$ points $p_i$, then its length is at most $v_{\mathcal{O}}(m^k)$.

Lean: `New.OddPart.length_shaOdd_le_addVal_pow` (Lib/Cyclotomic/OddSha.lean).

This is the general lemma on lengths with all $n_i = m$.

**Proposition (small primes).** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a CM field, $N \le y$, and $\ell \le y^2$ a prime. If $m$ kills $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n)$, then its length is at most $v_{\mathcal{O}}(m^{y^{20}})$.

Lean: `New.OddPart.length_shaOdd_le_of_le_sq` (Lib/Cyclotomic/OddSha.lean).

*Proof.* The detecting points over $E$ detect the cocycles of $\text{Ш}_{\mathrm{odd}}$, as these are unramified away from $\ell$. There are at most $y^{20}$ of them. Apply the last lemma. $\square$

**Proposition (large primes).** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a CM field, $e \ne 0$, $N + e + 3 \le y$, and $\ell > y^2$ a prime. Let $\mathcal{O}$ have enough roots of unity for the characters mod $N$. If $0 < X \le 2^{y^6}$ has the Stickelberger property for $N$ and $e$, then
$$\mathrm{length}_{\mathcal{O}}\, \text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n) \le v_{\mathcal{O}}\big((4\varphi(N) \cdot 4X^2)^{y^{20}}\big).$$

Lean: `New.OddPart.length_shaOdd_le_of_sq_lt` (Lib/Cyclotomic/OddSha.lean).

*Proof.* As $\ell > y^2 \ge (N + e + 3)^2$, the theorem of Section 6 applies to every odd $\Upsilon_\psi$. It gives points $\gamma_{\psi, i}$, $0 \le i \le v_\ell(X)$, that detect $C_n(\ell, e, \psi)$. Take the points $b(\sigma(u), \gamma_{\psi, i})$ of $\mathrm{Gal}(\Omega/E)$, for units $u$ mod $N$, characters $\psi$ and indices $i$. If $z$ vanishes at all of them, all odd components of $z$ vanish, so $4\varphi(N) z = 0$. As $4\varphi(N) \le 4N < \ell$ and $\ell^n z = 0$, $z = 0$. *Count.* There are $\varphi(N) \le y$ units and $\varphi(N) \le y$ characters, and $v_\ell(X) + 1 \le y^6 + 1 \le y^{18}$, as $X \le 2^{y^6}$. So there are at most $y^{20}$ points. The annihilator is the last proposition but one. $\square$

The docstring says that a bound of this kind is usually drawn from the main conjecture, and that here it comes from Kolyvagin's cocycles for each odd character.

### The main theorem

**Theorem.** Let $E \subseteq \mathbb{Q}(\mu_N)$ be a CM field and $t \ge 0$. There is a natural number $X \ne 0$ with
$$X \le 2^{4(N+t+3)^{27}}\, h_E$$
such that for every prime $\ell$, every ring of integers $\mathcal{O}$ of a finite extension of $\mathbb{Q}_\ell$ with enough roots of unity for the characters mod $N$, every $e < t$ and every $n \ge 0$,
$$\mathrm{length}_{\mathcal{O}}\, \text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n) \le v_{\mathcal{O}}(X).$$

Lean: `New.exists_length_shaOdd_le` (Lib/Cyclotomic/OddSha.lean).

*Proof.* Put $y = N + t + 3$. For each $e \ge 1$, Section 3 gives $X_e \ne 0$ with $X_e \le 2^{(N+e+3)^6}$ and the Stickelberger property. Put $Y_e = 4\varphi(N) \cdot 4X_e^2$ and
$$X = \Big(\prod_{0 < e < t} Y_e\Big)^{y^{20}} h_E.$$
It is nonzero, as $h_E \ne 0$. *Size.* For $0 < e < t$, $X_e \le 2^{y^6}$ and $4\varphi(N) \cdot 4 \le 2^{2y^6}$, so $Y_e \le 2^{4y^6}$. There are at most $y$ factors, so the product to the power $y^{20}$ is at most $2^{4y^{27}}$. *Length.* For $e = 0$ the proposition on the case $e = 0$ gives the bound by $v_{\mathcal{O}}(h_E)$, and $h_E \mid X$. For $0 < e < t$, $Y_e^{y^{20}} \mid X$. If $\ell \le y^2$, the proposition on small primes with $m = Y_e$ and the annihilator applies. If $\ell > y^2$, the proposition on large primes applies, as $N + e + 3 \le y$ and $X_e \le 2^{y^6}$. $\square$

**Remark (Formalization).** The integers $X_e$ are chosen with `choose!` in the proof, so $X$ is some integer with the stated properties. The statement fixes $N$, $t$ and $E$, and $X$ does not depend on $\ell$, $\mathcal{O}$, $e$ or $n$. For $t \le 1$ the product is empty, and $X = h_E$. The constants are crude: $(N + t + 3)^{27}$ in the exponent comes from $y^6$ (Voronoi's determinant), $y^{20}$ (the count of points) and one more factor $y$ (the number of $e$). Only the shape $\log X \le C\,(N+t+3)^{27} + \log h_E$ is used. The integer $X$ is a natural number, and $v_{\mathcal{O}}(X)$ is the valuation of its image in $\mathcal{O}$. No equality of characteristic ideals, and no main conjecture, is proved.

### Where the argument uses it

The congruence part of the argument fixes its constants in [file](lean:New/Congruences/FirstOrder/TraceRelations.lean#L74). There the number `oddClassBound` is the integer of the main theorem, for the cyclotomic conductor $N$ and the number $t$ of the data, taken with `Classical.choose`. Volume 12 states it as [Definition](/decl/New.Selmer.oddClassBound/), with its bound, in [the regular families plan](/chapter/regular-families-plan/). The argument uses three consequences.

**Lemma.** For every sufficiently large coefficient ring $\mathcal{O}$, for all $e < t$ and all $\nu$, the length of $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, \nu)$ is at most $v_{\mathcal{O}}(\mathrm{oddClassBound})$.

Lean: `New.Selmer.eventually_length_shaOdd_le` (New/Congruences/FirstOrder/TraceRelations.lean).

The coefficient rings are ordered by inclusion, and a large ring contains the roots of unity that the main theorem asks for. This is how the hypothesis on roots of unity is met. The lemma feeds the bound for Ribet's element: in [file](lean:New/Congruences/FirstOrder/RibetElement.lean#L343) the proof chooses one coefficient ring that is large enough for all its data at once, the odd classes included. The losses are added in [file](lean:New/Congruences/FirstOrder/RibetElement.lean#L116), where each odd length is bounded by the valuation of `oddClassBound`.

The odd classes enter there because of [file](lean:New/Congruences/FirstOrder/TateTwistCocycles.lean#L166). A module of cocycles for $\mathcal{O}(-e)$ with the local conditions of $\text{Ш}_{\mathrm{odd}}$, whose even parts are read at test points, has its length, up to bounded torsion, at most the length of $\text{Ш}_{\mathrm{odd}}$. So the even part is paid for by the test points, and the odd part by this chapter.

Second, the error term of the denominator bound starts with $t \cdot v_\ell(\mathrm{oddClassBound})$ ([file](lean:New/Congruences/FirstOrder/TraceRelations.lean#L106); see [the denominator bound](/chapter/denominator-bound/)). Third, these valuations are negligible: [Lemma](/decl/New.Selmer.isNegligible_padicValNat_oddClassBound/) shows that $\sum_{\ell \in T} v_\ell(\mathrm{oddClassBound}) \log \ell \le \log \mathrm{oddClassBound}$ is at most $4(N+t+3)^{27}\log 2 + x^{30}$ for every finite set $T$ of primes, by the bound $\log h_E \le x^{30}$ of the data, and so at most $x^{2000}$ in the sense of [data and sizes](/chapter/data-and-sizes/). This is the only place where the size of $X$ matters, and only its logarithm counts.
