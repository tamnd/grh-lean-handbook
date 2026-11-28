---
title: Characters of finite groups
lean:
  - Lib/General/Groups/CharacterTheory.lean
decls:
  - New.finMean
  - New.classInner
  - New.IsChar
  - New.IsIrreducibleChar
  - New.virtualChars
  - New.isChar_of_mem_virtualChars
  - New.exists_isExpansionFamily
  - New.IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast
  - New.IsCentralProj
  - New.IsCentralProj.isChar_card_mul_coeff
  - New.IsCentralProj.norm_coeff_le_one
  - New.IsCentralProj.sum_norm_sq_conv_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Characters of finite groups

The characters of the finite groups $\mathrm{GL}_n(\mathbb{F}_q)$ enter the source at the finite places, through the types of cuspidal representations ([the characters of finite general linear groups](/chapter/finite-gln/)). Their construction needs two things from general character theory. The first is a test that a class function is an irreducible character. The second is a bound for central idempotents of the group algebra. This section gives both. The reference is Serre, *Linear Representations of Finite Groups*, Ch. 2.

### Means, inner products and characters

Let $G$ be a finite group. For $f : G \to \mathbb{C}$, the mean is $\mathbb{E}(f) = |G|^{-1} \sum_{g \in G} f(g)$.

**Definition (Inner product).** For $f, h : G \to \mathbb{C}$,
$$\langle f, h \rangle = \mathbb{E}\left( t \mapsto \overline{f(t)}\, h(t) \right).$$

Lean: `New.classInner` (Lib/General/Groups/CharacterTheory.lean). The mean is `New.finMean`.

The product is conjugate linear in the first argument. Serre writes $(\varphi | \psi) = \mathbb{E}(\varphi \bar\psi)$, which is conjugate linear in the second argument (Serre, §2.3). So $\langle f, h \rangle = (h | f)$.

**Definition (Character).** A function $f : G \to \mathbb{C}$ is a character if it is the character of a finite dimensional complex representation of $G$. A class function is a function constant on conjugacy classes.

Lean: `New.IsChar` (Lib/General/Groups/CharacterTheory.lean).

The zero function is a character, of the zero representation. Sums and products of characters are characters. So the $\mathbb{N}$-span of the characters is the set of characters, and the $\mathbb{Z}$-span is the ring of virtual characters.

**Proposition.** For a semiring $S$, let $\mathrm{Ch}_S(G)$ be the $S$-span of the characters in the functions $G \to \mathbb{C}$. Then $\mathrm{Ch}_S(G)$ is a subalgebra. Every element of $\mathrm{Ch}_{\mathbb{N}}(G)$ is a character.

Lean: `New.isChar_of_mem_virtualChars` (Lib/General/Groups/CharacterTheory.lean). The span is `New.virtualChars`.

*Proof.* The characters contain $0$ and $1$ and are closed under sums and products, by direct sums and tensor products of representations. $\square$

### Irreducible characters

**Definition (Irreducible character).** A function $f : G \to \mathbb{C}$ is an irreducible character, in the sense of the source, if:

1. $f$ is a character;
2. $\langle f, f \rangle = 1$;
3. for every class function $h$ and every $y \in G$,
$$f(1) \, \langle f, h(\cdot \, y) \rangle = \langle f, h \rangle \, f(y).$$

Lean: `New.IsIrreducibleChar` (Lib/General/Groups/CharacterTheory.lean).

Clause 3 says that a class function $h$ acts by a scalar in the representation of $f$. Indeed, if $f$ is the character of an irreducible representation $\rho$ of degree $d$, then $\sum_s h(s) \rho(s^{-1})$ commutes with $\rho$, so it is a scalar by Schur's lemma. Taking traces gives clause 3.

**Remark (Formalization).** The definition is particular to the source. The textbook definition is the character of an irreducible representation. By Serre, §2.3, Theorem 5, a character $f$ with $(f | f) = 1$ is the character of an irreducible representation. So clauses 1 and 2 already give the textbook notion, and clause 3 follows from it by the computation above. Thus the definition agrees with the textbook one. The source does not prove this agreement, and it does not connect the definition with the simple representations of Mathlib. Clause 3 is the form in which the users apply irreducibility, so the source puts it in the definition.

The source proves the expansion of class functions from the theorem of Wedderburn.

**Proposition.** There is a finite family of characters $\chi_1, \ldots, \chi_n$ of positive degree, each satisfying clause 3, such that every class function $\varphi$ is $\sum_i \langle \chi_i, \varphi \rangle \chi_i$.

Lean: `New.exists_isExpansionFamily` (Lib/General/Groups/CharacterTheory.lean).

*Proof.* By Wedderburn, $\mathbb{C}[G]$ is a product of matrix algebras $M_{d_i}(\mathbb{C})$. Let $\chi_i$ be the character of the dual of the $i$-th block. A class function $\varphi$ is central in $\mathbb{C}[G]$, so it acts by a scalar on each block. Compare the coefficients. $\square$

The family consists of the irreducible characters. This is Serre, §2.5, Theorem 6. The source does not need to identify the family. It needs only the expansion, and the criterion below follows from it.

**Theorem.** Let $f$ and $I$ be class functions on $G$. Assume:

1. $\langle I, f \rangle \neq 0$, $\langle f, f \rangle = 1$ and $\operatorname{Re} f(1) \geq 0$;
2. for every character $\chi$ with $\langle \chi, I \rangle \neq 0$ that satisfies clause 3 for the class function $I$, the number $\langle \chi, f \rangle$ is an integer.

Then $f$ is an irreducible character.

Lean: `New.IsClassFunction.isIrreducibleChar_of_classInner_eq_intCast` (Lib/General/Groups/CharacterTheory.lean).

*Proof.* Expand $f$ and $I$ in the family $(\chi_i)$. Since $\langle I, f \rangle \neq 0$, some $\chi_i$ is orthogonal to neither $I$ nor $f$. Its coefficient in $f$ is a nonzero integer $m$ by hypothesis 2. Since $\langle f, f \rangle = 1$ is the sum of the squares of the absolute values of the coefficients, $m = \pm 1$ and the other coefficients are $0$. So $f = \pm \chi_i$. The condition $\operatorname{Re} f(1) \geq 0$ and $\chi_i(1) > 0$ give $f = \chi_i$. $\square$

This is the classical argument that a virtual character of norm $1$ with positive degree is irreducible (Serre, §2.3, Theorem 5 and the remarks after it). The source applies it to characters of finite general linear groups. Hypothesis 2 needs to be checked only on the characters that $I$ sees.

### Central idempotents

Let $\mathbb{C}[G]$ be the group algebra. Write $e = \sum_g e(g) \, g$ for its elements.

**Definition (Central projection).** An element $e \in \mathbb{C}[G]$ is a central projection if $e^2 = e$ and $g \mapsto e(g)$ is a class function.

Lean: `New.IsCentralProj` (Lib/General/Groups/CharacterTheory.lean).

A class function gives a central element, so a central projection is a central idempotent. The projection formula (Serre, §2.6, Theorem 8) gives the examples: for an irreducible character $\chi$ of degree $d$,
$$e_\chi = \frac{d}{|G|} \sum_g \overline{\chi(g)} \, g$$
is a central projection. The central projections are exactly the sums of distinct $e_\chi$.

**Theorem.** Let $e$ be a central projection of $\mathbb{C}[G]$. Then $g \mapsto |G| \, e(g)$ is a character.

Lean: `New.IsCentralProj.isChar_card_mul_coeff` (Lib/General/Groups/CharacterTheory.lean).

*Proof.* The pairing of $|G| e$ with a character $\chi$ is the trace of $e$ on a representation with character $\bar\chi$. The element $e$ acts there by an idempotent, so this trace is its rank, a natural number. A class function whose pairing with every character is a natural number is in $\mathrm{Ch}_{\mathbb{N}}(G)$, so it is a character. $\square$

For $e = e_\chi$, the character is $d \bar\chi$, the character of $d$ copies of the dual representation.

**Corollary.** Let $e$ be a central projection of $\mathbb{C}[G]$. Then $|e(g)| \leq 1$ for every $g$.

Lean: `New.IsCentralProj.norm_coeff_le_one` (Lib/General/Groups/CharacterTheory.lean).

*Proof.* Also $1 - e$ is a central projection. The coefficients of $e$ and $1 - e$ at $g = 1$ add up to $1$. So the degrees $|G| e(1)$ and $|G| (1 - e)(1)$ of the two characters add up to $|G|$, and the representation of $|G| e$ has dimension at most $|G|$. The value of a character at $g$ has absolute value at most the dimension. So $|G| \, |e(g)| \leq |G|$. $\square$

The unfolding step of the source uses the last result. It says that convolution with a central projection is a contraction on $\ell^2$.

**Theorem.** Let $e$ be a central projection of $\mathbb{C}[G]$, let $\varphi : G \to H$ be a homomorphism to a finite group, and let $V$ be a complex inner product space. Then for every $f : H \to V$,
$$\sum_{s \in H} \Big\| \sum_{t \in G} e(t) \, f(\varphi(t)^{-1} s) \Big\|^2 \leq \sum_{s \in H} \| f(s) \|^2.$$

Lean: `New.IsCentralProj.sum_norm_sq_conv_le` (Lib/General/Groups/CharacterTheory.lean).

*Proof.* The group $G$ acts unitarily on $\ell^2(H, V)$ by left translation through $\varphi$. The left side is $\| e f \|^2$ for this action. A central projection is self adjoint (`New.IsCentralProj.self_adjoint`) for every invariant hermitian form. So $e$ acts as an orthogonal projection, and $\| ef \| \leq \| f \|$. $\square$

For $e = e_\chi$ the self adjointness is the identity $\overline{\chi(g)} = \chi(g^{-1})$. The source proves the self adjointness in a more general form: for forms that are semilinear for $\sigma^{-1} \circ \bar{\ } \circ \sigma$, with $\sigma$ an automorphism of $\mathbb{C}$. So the result holds for the Galois conjugates of $e$ too.

**Remark (Formalization).** The file declares `attribute [local instance low] Fintype.ofFinite` in several sections. This turns the hypothesis that $G$ is finite into a finite enumeration of $G$, chosen by `choice`. A local instance applies only in its section. The sums in the statements do not depend on the enumeration, because a finite sum does not depend on the order. Two different enumerations can still make two terms differ by definition and agree only by a proof. Row F-026 of [the register of findings](/chapter/register-of-findings/) explains this attribute. Its list of files does not include this one. The statement of `New.IsCentralProj.sum_norm_sq_conv_le` uses `Fintype` and not `Finite`, so a user supplies the enumeration there.
