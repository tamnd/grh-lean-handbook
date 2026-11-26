---
title: Avatars and conjugate self-duality
lean:
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/GaloisRepresentations/AttachedRepresentations.lean
decls:
  - New.Selmer.cyclotomicInv_frob
  - New.Data.TameChar.invAvatar
  - New.Selmer.avatar_conjGal_mul_frob
  - New.Selmer.avatar_conjGal_mul_avatar
  - New.Selmer.isLabelledAt_avatar
  - New.Selmer.IsConjSelfDual
  - New.Selmer.coeff_zero_mul_coeff_star
  - New.Selmer.isConjSelfDual_of_attached
  - New.Selmer.IsLatticeIn.exists_algHom
  - New.Selmer.IsLatticeIn.continuous
  - New.Selmer.IsLatticeIn.eq_one
  - New.Selmer.IsLatticeIn.trace_eq
  - New.Selmer.isTraceNondeg_transpose_inv
  - New.Selmer.count_jumps_comp_star
  - New.Selmer.isFiniteTypeAt_and_hasJumpsAt_of_conjPlace
  - New.Selmer.IsConjSelfDualOfLevel
  - New.Selmer.normalizingAvatar
  - New.Selmer.normalizingAvatar_eq_of_isFrob_inv
  - New.Selmer.normalisedRep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Avatars and conjugate self-duality

The representations of this chapter are conjugate self-dual: $R^c \cong R^\vee(1 - t)$, where $R^c(g) = R(cgc)$ for a complex conjugation $c$. This section proves that every representation attached to an eigenform on a unitary group of rank $n$ is conjugate self-dual with $t = n$, on traces. It also defines the characters by which the representations are twisted: the inverse avatar of a tame character, and the normalizing character of a descent pair.

### Background

- An algebraic Hecke character $\theta$ of $E$ has an $\ell$-adic *avatar* $\theta_\ell : G_E \to \bar{\mathbb{Q}}_\ell^\times$. At a geometric Frobenius element at a place $w \nmid \ell$ where $\theta$ is unramified, $\theta_\ell$ is $\iota$ of the value of $\theta$ at a uniformizer ([class field theory](/chapter/class-field-theory/)).
- A character $a$ of the norm-one torus of weight $e$ and tame part $\psi$, with integers $k, j$, gives the algebraic Hecke character $y \mapsto a(y/\bar y)\, \upsilon(y)^{-k} |y|^{j - k/2}$, with $\upsilon$ the fixed splitting character ([twists and critical pairs](/chapter/twists-critical-pairs/)).
- A representation $R$ is *attached* to a system $Q$ of polynomials if $R$ is continuous with a nondegenerate trace form and, for every $\eta > 0$, the coefficients of the characteristic polynomial of $R$ at most Frobenius data are within $\eta$ of $\iota$ of the coefficients of $Q$. Frobenius elements of most Frobenius data are dense in $G_E$ ([most Frobenius data](/chapter/attached-representations/#most-frobenius-data), [attached representations](/chapter/attached-representations/#attached-representations-and-their-traces)).
- A form $f$ is an *eigenform* for $Q$ if $f \neq 0$ and, for all but finitely many places $w$ of prime norm, $w$ is split and $f$ is spherical at $w$ with Hecke polynomial $Q(w) = \sum_{j \le n} (-1)^j q^{j(j-1)/2} t_j X^{n - j}$, where $t_j$ is the eigenvalue of the $j$-th Hecke operator ([eigenforms](/chapter/attached-representations/#eigenforms-hecke-polynomials-and-weights)).
- For $i + j = n$, the $i$-th Hecke operator at $\bar w$ followed by the central element of the uniformizer at $w$ is the $j$-th Hecke operator at $w$ ([split places](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials)).
- The local conditions on a representation at a place $A$ of $\bar{\mathbb{Q}}$: *finite type* (trivial on inertia near $1$ if $\ell$ is a unit at $A$, potentially crystalline at $\ell$), *good* (trivial on inertia if $\ell$ is a unit at $A$, crystalline at $\ell$), *jumps* $J$ (Hodge-Tate weights through $\iota$), and *kills* ($P(R(s)) = 0$ in Weil-Deligne form) ([local conditions](/chapter/attached-representations/#local-conditions-kills-and-characteristic)).

Write $\varepsilon$ for the $\ell$-adic cyclotomic character and $\varepsilon^{-1}$ for its inverse. Write $g^c = cgc$.

**Lemma (Inverse cyclotomic character at Frobenius).** If the place $w$ of a Frobenius datum does not divide $\ell$, then $\varepsilon^{-1}$ takes the value $q_w$, the norm of $w$, at its geometric Frobenius element.

Lean: `New.Selmer.cyclotomicInv_frob` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* The arithmetic Frobenius raises $\ell$-power roots of unity to the power $q_w$. $\square$

### Avatars

**Definition (Inverse avatar).** For a tame character $\vartheta$ of the data, $\vartheta^{-1}_\ell$ is the avatar of the algebraic Hecke character made from $\vartheta^{-1}$ with $k = j = 0$, read in $\bar{\mathbb{Q}}_\ell$.

Lean: `New.Data.TameChar.invAvatar` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Theorem (Avatars are conjugate self-dual).** Let $\mu$ be the avatar of $y \mapsto a(y/\bar y)\,\upsilon(y)^{-k}|y|^{j - k/2}$. Then $\mu(g^c)\,\mu(g) = \varepsilon(g)^{2j - k}$ for every $g \in G_E$.

Lean: `New.Selmer.avatar_conjGal_mul_avatar`, with `New.Selmer.avatar_conjGal_mul_frob` for Frobenius elements (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* First let $g$ be the Frobenius element of a datum at $w \nmid \ell$ with $\psi(w) = \psi(\bar w) = 1$. Then $g^c$ is a Frobenius element at $\bar w$. Let $c_v$ be the value of the Hecke character at the uniformizer of $v$. It is $a(\varpi_v/\bar\varpi_v)\,\upsilon(\varpi_v)^{-k}\sqrt{q_v}^{\,k - 2j}$. At $\bar w$ the factor of $a$ is the inverse of the factor at $w$, and $\upsilon(\varpi_{\bar w})\upsilon(\varpi_w) = 1$. So $c_{\bar w} c_w = q_w^{k - 2j}$. The avatar at a geometric Frobenius is $\iota(c)$, and $\varepsilon(g) = q_w^{-1}$. So $\mu(g^c)\mu(g) = \varepsilon(g)^{2j - k}$. These Frobenius elements are those of most Frobenius data, because only finitely many places are ramified for $\psi$. They are dense in $G_E$. Both sides are continuous, and the set where they agree is closed. $\square$

**Lemma (The label of an avatar).** Let $w$ be a split place with $\psi(\bar w) = 1$, and let $T$ be the faithful character of the residue field at $w$. At a place $A$ over $w$, an inertia element $s$ of tame exponent $i$ is killed, for $\mu$, by $X - \iota(T^i(\lambda))$, where $\lambda$ is the element of the residue field that names $\psi(w)$ through $T$.

Lean: `New.Selmer.isLabelledAt_avatar` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* By local class field theory, $s$ is the Artin image of a local unit $x$, and $s$ is killed by $X - \iota(\theta(x))$. Since $\upsilon$ is unramified at $w$ and $x$ is a unit, $\theta(x) = \psi(w)(\bar x)$, with $\bar x$ the residue of $x$. The tame exponent of $s$ turns this value into $T^i(\lambda)$. $\square$

### Conjugate self-duality

**Definition (Conjugate self-dual).** A representation $R : G_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ is *conjugate self-dual of twist $1 - t$* if:

1. $R$ is continuous;
2. the trace form on the span of the image of $R$ is nondegenerate;
3. $\mathrm{tr}\, R(g^c) = \varepsilon^{-1}(g)^{t - 1}\, \mathrm{tr}\, R(g^{-1})$ for all $g$.

Lean: `New.Selmer.IsConjSelfDual` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** The usual condition is an isomorphism $R^c \cong R^\vee \otimes \varepsilon^{1 - t}$. The source states it on traces. With the nondegenerate trace form, two representations with the same traces are conjugate ([representations from traces](/chapter/attached-representations/#representations-from-traces)), so the two forms agree. The exponent $t - 1$ is a truncated subtraction: $t = 0$ reads as $t = 1$.

**Lemma (Dual Hecke polynomials).** Let $f \neq 0$ be a form of rank $n = k + 1$, spherical at the split place $w$ with Hecke polynomial $Q(w)$, and at $\bar w$ with Hecke polynomial $Q(\bar w)$. Then
$$Q(w)_0 \cdot Q(\bar w)_k = q_w^{k}\, Q(w)_1,$$
where $P_i$ is the coefficient of $X^i$.

Lean: `New.Selmer.coeff_zero_mul_coeff_star` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Let $s_j$ and $u_j$ be the eigenvalues of the $j$-th Hecke operators at $w$ and $\bar w$. By the background on split places with $i = 0$, the central element acts on $f$ by $s_{k+1}$. With $i = 1$ and $j = k$ it gives $u_1 s_{k+1} = s_k$. From the formula for the Hecke polynomial, $Q(w)_0 = (-1)^{k+1} q^{k + \binom{k}{2}} s_{k+1}$ (with $\binom{k+1}{2} = k + \binom{k}{2}$), $Q(w)_1 = (-1)^k q^{\binom{k}{2}} s_k$ and $Q(\bar w)_k = -u_1$. Multiply. $\square$

**Theorem (Attached representations are conjugate self-dual).** Let $f$ be an eigenform of rank $n$ for $Q$, and let $R$ be attached to $Q$. Then $R$ is conjugate self-dual of twist $1 - n$.

Lean: `New.Selmer.isConjSelfDual_of_attached` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Continuity and the trace form come with "attached". For $n = 0$ both traces are $0$. Let $n = k + 1$ and fix $g$.

*Step 1.* The map $g \mapsto g^c$ is a homeomorphism of $G_E$, and it sends a Frobenius element at $w$ to one at $\bar w$. So $R(\,\cdot\,^c)$ is attached to the system $w \mapsto Q(\bar w)$.

*Step 2.* At most Frobenius data $w \nmid \ell$, and $\varepsilon^{-1}$ at the Frobenius element is $q_w$. The lemma on dual Hecke polynomials gives
$$\iota(Q(w)_0)\,\iota(Q(\bar w)_k) = \varepsilon^{-1}(\mathrm{Frob}_w)^k\, \iota(Q(w)_1).$$

*Step 3.* Take Frobenius elements that tend to $g$. By Step 1 and "attached", the coefficients converge to those of the characteristic polynomials. So $\chi_{R(g)}(0)\cdot \chi_{R(g^c)}{}_{,k} = \varepsilon^{-1}(g)^k\, \chi_{R(g)}{}_{,1}$, where $\chi_A$ is the characteristic polynomial.

*Step 4.* For an invertible matrix $A$ of size $k + 1$, $\chi_A(0) = (-1)^{k+1}\det A$, the coefficient of $X^k$ is $-\mathrm{tr}\, A$, and the coefficient of $X$ is $(-1)^k \det A \cdot \mathrm{tr}\, A^{-1}$. Substitute, cancel the nonzero factor $(-1)^{k+1}\det R(g)$, and use $(k + 1) - 1 = k$. $\square$

**Remark (Formalization).** "Attached" in the source is weak: it asks agreement only in the limit along most Frobenius data, not at every unramified place. The representation type is a bare group homomorphism with no continuity; continuity comes from "attached". The proof above uses exactly these two properties. It does not use the equality at any given place.

### Lattices

Recall that $u$ is a lattice in $R$ if $P^{-1}R(g)P = u(g)$ for one $P$ and all $g$.

**Lemma (Lattices).** Let $u$ be a lattice in $R$ over $O$. Then:

1. there is an injective map $F$ of $O$-algebras from $M_n(O)$ to $M_n(\bar{\mathbb{Q}}_\ell)$ with $F(u(g)) = R(g)$, which keeps determinants and traces;
2. if $R$ is continuous, so is $u$;
3. $R(g) = 1$ implies $u(g) = 1$;
4. $\mathrm{tr}\, u(g) = \mathrm{tr}\, R(g)$ in $\bar{\mathbb{Q}}_\ell$.

Lean: `New.Selmer.IsLatticeIn.exists_algHom`, `New.Selmer.IsLatticeIn.continuous`, `New.Selmer.IsLatticeIn.eq_one`, `New.Selmer.IsLatticeIn.trace_eq` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Take $F(A) = P\,A\,P^{-1}$, with the entries of $A$ read in $\bar{\mathbb{Q}}_\ell$. Conjugation keeps determinants and traces, and it is injective. Then 2 holds since $u$ is a fixed conjugate of $R$ and the inclusion of $O$ is an embedding. Parts 3 and 4 follow from 1. $\square$

### The conjugate place

**Lemma (Dual and conjugate).** If the trace form of $R$ is nondegenerate and $R'(g) = R(g^{-1})^{\mathsf T}$, then the trace form of $R'$ is nondegenerate. For a weight $\kappa$ in rank $k$ and an embedding $\sigma$, the multiplicity of $u$ among the jumps at $\bar\sigma$ is that of $(k - 1) - u$ at $\sigma$.

Lean: `New.Selmer.isTraceNondeg_transpose_inv`, `New.Selmer.count_jumps_comp_star` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Transposition maps the span of the image of $R'$ into that of $R$, and $\mathrm{tr}(x^{\mathsf T} y) = \mathrm{tr}(x\, y^{\mathsf T})$. For the jumps, $\sigma \circ c$ is the conjugate embedding, and the jumps of a weight at $\bar\sigma$ are $k - 1$ minus those at $\sigma$ ([Hodge-Tate jumps](/chapter/period-rings/#hodge-tate-jumps)). $\square$

**Theorem (Local conditions at the conjugate place).** Let $R$ be conjugate self-dual of twist $1 - k$, and of finite type at the conjugate place $\bar A$ of $A$. Then:

1. $R$ is of finite type at $A$;
2. for every weight $\kappa$, if $R$ has the jumps of $\kappa$ in rank $k$ at $\bar A$, it has them at $A$;
3. for every inertia element $s$ at $\bar A$ and every polynomial $P$ that kills $s$ at $\bar A$, $P$ kills $(s^{-1})^c$ at $A$.

Lean: `New.Selmer.isFiniteTypeAt_and_hasJumpsAt_of_conjPlace` (New/Congruences/GaloisRepresentations/AttachedRepresentations.lean).

*Proof.* Let $r' = \varepsilon^{-(k-1)} \otimes R^\vee$, with $R^\vee(g) = R(g^{-1})^{\mathsf T}$. Its trace form is nondegenerate by the lemma, and so is that of $R(\,\cdot\,^c)$. Condition 3 of conjugate self-duality says that $r'$ and $R(\,\cdot\,^c)$ have the same traces. So they are conjugate by one matrix ([representations from traces](/chapter/attached-representations/#representations-from-traces)). Conjugation by $c$ carries the decomposition and inertia groups of $\bar A$ to those of $A$. So each local clause for $r'$ at $\bar A$ gives the same clause for $R$ at $A$. It remains to pass the clauses from $R$ to $r'$ at $\bar A$. *Away from $\ell$:* the cyclotomic character is trivial on inertia. So $r'$ is trivial on inertia near $1$ where $R$ is, and for $s$ in inertia $r'(s^{-1})$ is the transpose of $R(s)$, which the same polynomials kill. *Above $\ell$:* the dot product pairs $r'$ and $R$ on the decomposition group into $\varepsilon^{-(k-1)}$. Through this pairing, $r'$ is potentially crystalline, its jump $u$ has the multiplicity of the jump $(k - 1) - u$ of $R$, and a polynomial that kills $s$ for $R$ kills $s^{-1}$ for $r'$ ([crystalline representations](/chapter/period-rings/#crystalline-representations)). An inertia element has Weil degree $0$, so only this case of the kill condition occurs. With the lemma on jumps at $\bar\sigma$, the jumps of $\kappa$ at $\bar A$ give the jumps of $\kappa$ at $A$. $\square$

**Definition (Conjugate self-dual of level $S$).** Let $S$ be a set of finite places and $J$ a family of jumps. $R$ is *conjugate self-dual of twist $1 - t$, level $S$ and jumps $J$* if it is conjugate self-dual of twist $1 - t$, and at every place $v$ that is outside $S$ or divides $\ell p_0 p_1$, and every $A$ over $v$:

1. $R$ is of finite type at $A$;
2. $R$ has the jumps $J$ at $A$;
3. if $v \nmid p_0 p_1$, then $R$ is good at $A$.

Lean: `New.Selmer.IsConjSelfDualOfLevel` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** At the places above $\ell$ that divide $p_0 p_1$, if any, the source asks only potentially crystalline. Good reduction, that is crystalline at $\ell$ and unramified elsewhere, is asked only at the places prime to $p_0 p_1$. The research note on congruences says that a main summand is "crystalline at $\ell$". That is true only at the places prime to $p_0 p_1$.

### The normalizing character

A descent pair $V$ pairs a definite space of rank $n$ with a space $W$ of rank $r < n$ and a character of $W$ ([single theta lifts](/chapter/single-theta-lifts/)). The representation attached to a form on $V$ must be twisted to compare it with one on $W$.

**Definition (Normalizing character).** For a descent pair $V$, $\chi_V$ is the avatar of the algebraic Hecke character made from the inverse of the character of $W$, with $k = -r$ and $j = 0$. The *normalized representation* of $R$ is $\chi_V \otimes R$.

Lean: `New.Selmer.normalizingAvatar`, `New.Selmer.normalisedRep` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma (Value at Frobenius).** Let $A$ lie over $w \nmid \ell$, and let $s^{-1}$ act at $A$ as the $d$-th power of Frobenius. Then $\chi_V(s) = \iota(X_w)^{-d}$, where $X_w$ is the value at a uniformizer of $w$ of the Hecke character of $W$, times $q_w^{r/2}$.

Lean: `New.Selmer.normalizingAvatar_eq_of_isFrob_inv` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* The element $s$ is the local Artin symbol of some $z$ of valuation $-d$. Away from $\ell$ the avatar at $s$ is $\iota$ of the character at $z$. The character is unramified at $w$, so this is the $d$-th power of its value at the uniformizer, which is $X_w^{-1}$. $\square$
