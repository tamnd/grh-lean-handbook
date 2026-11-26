---
title: CM fields and two criteria
lean:
  - Lib/General/NumberTheory/CMFields.lean
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/GaloisRep/BaseChange/GlobalRoot.lean
decls:
  - New.map_star_complex
  - New.map_star_CM
  - New.isCMField_of_forall_exists_conj
  - New.isCMField_fixedField_zpowers
  - New.isCMField_adjoinRoot_of_forall_root_mul_star_eq
  - New.adjoinRoot_root_mul_star
  - New.aeval_root_finAdele_surjective
  - New.aeval_root_finAdele_eq_zero_iff
  - New.IsFinAdelePresentation
  - New.adjoinRoot_cm_presentation
status: drafted
drafted_by: writer@claude-opus-5-5
---

## CM fields and two criteria

The field $K$ of Section 2 is the model. A CM field is a field that behaves like $K$ with respect to complex conjugation, over a larger totally real field. This section gives the classical definition and its first property, the definition of Mathlib, and the two criteria by which the source shows that new fields are CM.

### The classical definition

A number field $F$ is totally real if every embedding $F \to \mathbb{C}$ has image in $\mathbb{R}$, and totally complex if no embedding has image in $\mathbb{R}$. A CM field is a totally complex quadratic extension $E$ of a totally real field $F$ (Washington, *Introduction to Cyclotomic Fields*, Ch. 4). Examples are the imaginary quadratic fields, with $F = \mathbb{Q}$, and the cyclotomic fields $\mathbb{Q}(\zeta_n)$ with $n > 2$, with $F = \mathbb{Q}(\zeta_n + \zeta_n^{-1})$.

**Proposition.** Let $E / F$ be a CM field, and let $c$ be the nontrivial automorphism of $E$ over $F$. Then for every embedding $\varphi : E \to \mathbb{C}$ and every $x \in E$, $\varphi(c x) = \overline{\varphi(x)}$. The field $F$ is the set of $x \in E$ with $\overline{\varphi(x)} = \varphi(x)$ for every $\varphi$.

Mathlib: `NumberField.IsCMField.complexEmbedding_complexConj` (Mathlib).

*Proof.* Write $E = F(\alpha)$ with $\alpha^2 = a \in F$. Since $E$ is totally complex, $\varphi(a) = \varphi(\alpha)^2$ is a real number that is not the square of a real number, so $\varphi(a) < 0$ and $\varphi(\alpha)$ is purely imaginary. So $\overline{\varphi(\alpha)} = -\varphi(\alpha) = \varphi(c \alpha)$. As $\varphi(F) \subset \mathbb{R}$, both $\varphi \circ c$ and $\overline{\varphi}$ agree on $F$ and at $\alpha$, so they are equal. For the second claim, $\overline{\varphi(x)} = \varphi(x)$ for one $\varphi$ means $\varphi(cx) = \varphi(x)$, so $cx = x$ and $x \in F$. The converse holds since $F$ is totally real. $\square$

So on a CM field one element $\bar x = c x$ is the complex conjugate of $x$ under all embeddings at once. The field $F$ is determined by $E$, and it is written $E^+$.

### The definition in Mathlib

**Definition (CM field).** For a field $K$ of characteristic $0$, the maximal real subfield $K^+$ is the set of $x \in K$ with $\overline{\varphi(x)} = \varphi(x)$ for every ring homomorphism $\varphi : K \to \mathbb{C}$. The field $K$ is a CM field if it is totally complex and $K$ is a quadratic extension of $K^+$.

Mathlib: `NumberField.IsCMField` and `NumberField.maximalRealSubfield` (Mathlib).

**Remark (Formalization).** Mathlib does not ask for a totally real field $F$ as data. It uses the one candidate, $K^+$, and the classical definition follows from it by the proposition above (`NumberField.IsCMField.ofCMExtension` (Mathlib) is the converse direction). Complex conjugation is `NumberField.IsCMField.complexConj` (Mathlib). It is defined with `choose`, as an automorphism of $K$ over $K^+$ that induces conjugation under one chosen embedding. Mathlib then proves that it induces conjugation under every embedding, so the choice does not matter. Mathlib makes it a `StarRing` instance, and the source writes it `star`. The source carries the class `IsCMField` as a hypothesis on every field that needs a conjugation, and it defines with it the conjugation of $\mathcal{O}_E$, of the finite places and of the finite adeles (Sections 5 and 6).

**Lemma.** Let $E$ be a CM field. For every embedding $\varphi : E \to \mathbb{C}$ and $x \in E$, $\varphi(\bar x) = \overline{\varphi(x)}$. If $f : K \to L$ is a ring homomorphism of CM fields, then $f(\bar x) = \overline{f(x)}$ for every $x \in K$.

Lean: `New.map_star_complex`, `New.map_star_CM` (Lib/Adelic/Adeles/Basic.lean).

*Proof.* The first claim is the proposition. For the second, take an embedding $\varphi$ of $L$. Then $\varphi(f(\bar x)) = \overline{\varphi(f(x))}$ by the first claim for $\varphi \circ f$, and $\varphi(\overline{f(x)}) = \overline{\varphi(f(x))}$ by the first claim for $\varphi$. As $\varphi$ is injective, $f(\bar x) = \overline{f(x)}$. $\square$

### A criterion by a conjugation

The base change steps produce fields that are not given as quadratic extensions of a known totally real field. The first criterion asks only that conjugation exist on the field.

**Theorem.** Let $E$ be a totally complex field and $L$ a number field with an $E$-algebra structure. Suppose that for every $x \in L$ there is $y \in L$ with $\varphi(y) = \overline{\varphi(x)}$ for every embedding $\varphi : L \to \mathbb{C}$. Then $L$ is a CM field.

Lean: `New.isCMField_of_forall_exists_conj` (Lib/General/NumberTheory/CMFields.lean).

*Proof.* The field $L$ contains the image of $E$, so it is totally complex. Let $L^+$ be its maximal real subfield. It suffices to show $[L : \mathbb{Q}] = 2 [L^+ : \mathbb{Q}]$. Let $v, w$ be infinite places of $L$ with the same restriction to $L^+$. Take $x \in L$ and $y$ as in the hypothesis. Then $\varphi(xy) = |\varphi(x)|^2$ for every $\varphi$, so $xy \in L^+$, and $u(xy) = u(x)^2$ for every infinite place $u$ of $L$. So $v(x)^2 = v(xy) = w(xy) = w(x)^2$, and $v(x) = w(x)$. Thus restriction is injective on infinite places. It is surjective, since every place of $L^+$ extends to $L$. So $L$ and $L^+$ have the same number $r$ of infinite places. All places of $L$ are complex, so $[L : \mathbb{Q}] = 2r$. All places of $L^+$ are real, since $L^+$ is totally real, so $[L^+ : \mathbb{Q}] = r$. $\square$

**Remark (Formalization).** The hypothesis on $E$ serves only to make $L$ totally complex. The algebra map $E \to L$ is any ring homomorphism, and $E$ need not be a number field. The conclusion is the class `IsCMField L` of Mathlib. In the source the theorem has two uses. One is the fixed field of an automorphism, the corollary below. The other is the field cut out by a character of the Galois group in the Grunwald step, `New.QZChar.stepField` (in Lib/ClassField/Grunwald.lean), where $y$ is the image of $x$ under a complex conjugation of $\bar{\mathbb{Q}}$.

**Corollary.** Let $E \subset L$ be CM fields, with $L$ a number field, and let $g \in \mathrm{Gal}(L/E)$. Then the fixed field of the group generated by $g$ is a CM field.

Lean: `New.isCMField_fixedField_zpowers` (Lib/GaloisRep/BaseChange/GlobalRoot.lean).

*Proof.* Let $x$ be fixed by $g$. Then $\bar x$ is fixed by $g$, since $g$ commutes with conjugation by the lemma. For an embedding $\varphi$ of the fixed field, extend it to $L$. Then $\varphi(\bar x) = \overline{\varphi(x)}$. The theorem applies with $y = \bar x$. $\square$

### A criterion by a polynomial

The second criterion builds a CM field by adjoining a root of a polynomial. The source uses it in the base change step and in the trace formula, where $P$ is the characteristic polynomial of a unitary element and its roots have absolute value $1$ under every embedding.

**Theorem.** Let $E$ be a CM field, let $P \in E[X]$ be irreducible, and let $L = E[X]/(P)$. Suppose there is $\nu \in \mathbb{Q}$ such that for every embedding $\sigma : E \to \mathbb{C}$ and every complex root $r$ of $P^\sigma$, $r \bar r = \nu$. Then $L$ is a CM field. If moreover $L$ is given its CM structure, then the class $\alpha$ of $X$ in $L$ satisfies $\alpha \bar \alpha = \nu$.

Lean: `New.isCMField_adjoinRoot_of_forall_root_mul_star_eq`, `New.adjoinRoot_root_mul_star` (Lib/General/NumberTheory/CMFields.lean).

*Proof.* Every element of $L$ is $q(\alpha)$ for some $q \in E[X]$. Put $y = \bar q(\nu / \alpha)$, where $\bar q$ has the conjugate coefficients. Let $\varphi : L \to \mathbb{C}$ be an embedding, $\sigma$ its restriction to $E$ and $r = \varphi(\alpha)$, a root of $P^\sigma$. Then $r \bar r = \nu$. If $r \ne 0$, then $\nu / r = \bar r$. If $r = 0$, then $\nu = 0$ and $\nu / r = 0 = \bar r$ by the convention $x / 0 = 0$. In both cases
$$\varphi(y) = \sum_i \sigma(\bar a_i) \bar r^i = \sum_i \overline{\sigma(a_i)}\, \bar r^i = \overline{\varphi(q(\alpha))},$$
with $q = \sum a_i X^i$, by the lemma for $\sigma$. So the first criterion applies. The second claim holds under every embedding $\varphi$, by $\varphi(\alpha \bar\alpha) = r \bar r = \nu$, and the embeddings separate the points of $L$. $\square$

**Remark (Formalization).** The case $r = 0$ uses the junk value $\nu / 0 = 0$ of Lean. It cannot occur for irreducible $P \ne X$, but the source does not need to exclude it. The irreducibility of $P$ is a class `Fact (Irreducible P)`, and the source records with it an instance that $L$ = `AdjoinRoot P` is a number field. The field $L$ is abstract: it is a quotient of $E[X]$, not a subfield of $\mathbb{C}$ or of $\bar{\mathbb{Q}}$. The number $\nu$ must be rational and the same for all embeddings and all roots. In the uses, $\nu = 1$ (Lib/GaloisRep/BaseChange/GlobalRoot.lean) or $\nu$ is the similitude factor of an elliptic element (Lib/Adelic/TraceFormula/ChangingSigns.lean).

### The finite adeles of E[X]/(P)

For the base change step the source also needs the finite adeles of $L = E[X]/(P)$ in terms of those of $E$. Classically, for a finite extension $L/E$ of number fields, $\mathbb{A}_{L,f} = \mathbb{A}_{E,f} \otimes_E L$. For $L = E[X]/(P)$ with $P$ monic, this says that $\mathbb{A}_{L,f} = \mathbb{A}_{E,f}[X]/(P)$.

**Theorem.** Let $E$ be a CM field, $P \in E[X]$ monic and irreducible, and $\nu$ as in the last theorem. Let $\varepsilon : \mathbb{A}_{E,f}[X] \to \mathbb{A}_{L,f}$ be evaluation at $\alpha$. Then $L$ is a CM field, $\alpha \bar\alpha = \nu$, and $\varepsilon$ has the following four properties.

1. $\varepsilon$ is surjective.
2. $\varepsilon(q) = 0$ if and only if $P$ divides $q$ in $\mathbb{A}_{E,f}[X]$.
3. For $q \in E[X]$, $\varepsilon(q)$ is the image of $q(\alpha) \in L$.
4. If $c \in E[X]$ has $c(\alpha) = \bar\alpha$ in $L$, then $\varepsilon(\bar q \circ c) = \overline{\varepsilon(q)}$ for every $q \in \mathbb{A}_{E,f}[X]$.

Lean: `New.aeval_root_finAdele_surjective`, `New.aeval_root_finAdele_eq_zero_iff`, `New.IsFinAdelePresentation`, `New.adjoinRoot_cm_presentation` (Lib/General/NumberTheory/CMFields.lean).

*Proof.* The powers $1, \alpha, \dots, \alpha^{n-1}$, $n = \deg P$, form a basis of $L$ over $E$. The source shows that they also form a basis of $\mathbb{A}_{L,f}$ over $\mathbb{A}_{E,f}$ (`New.adjoinRootAdelePowerBasis`). This gives 1. For 2, write $q = P h + r$ with $\deg r < n$ by division by the monic $P$. Then $\varepsilon(q) = \varepsilon(r)$, which is $0$ if and only if all coefficients of $r$ vanish, by linear independence. Property 3 holds since $\varepsilon$ extends evaluation at $\alpha$. For 4, both sides are additive in $q$, so it suffices to take a monomial $q = a X^m$ with $a \in \mathbb{A}_{E,f}$. Then the left side is $\bar a \, \varepsilon(c)^m = \bar a \, \bar\alpha^m$ by 3, and the right side is $\overline{a \alpha^m} = \bar a \, \bar \alpha^m$, since the inclusion $\mathbb{A}_{E,f} \to \mathbb{A}_{L,f}$ commutes with conjugation (`New.adeleMap_star`). $\square$

**Remark (Formalization).** The structure `New.IsFinAdelePresentation` collects the four properties as fields. The source proves the CM property, the identity $\alpha\bar\alpha = \nu$ and the presentation in one existential statement, `New.adjoinRoot_cm_presentation`, of the form $\exists$ (an instance `IsCMField L`), $\dots$. The base change step applies it to each prime factor of a characteristic polynomial, and it takes the instances out with `choose`. Since `IsCMField` is a proposition, all choices give the same instance, so the choice does not change any statement.
