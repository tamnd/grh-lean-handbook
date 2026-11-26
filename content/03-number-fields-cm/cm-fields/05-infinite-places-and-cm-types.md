---
title: Infinite places and CM types
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Adeles/StrongApproximation.lean
decls:
  - New.PlaceEmbedding
  - New.CMType
  - New.𝔸
  - New.toAdele
  - New.abs_norm_eq_prod_norm_sq
  - New.one_le_prod_norm_Φ
  - New.trace_eq_sum_Φ
  - New.denseRange_Φ
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Infinite places and CM types

This section gives the classical infinite places of a number field and the classical CM types of a CM field. It then gives the form of the source, in which a "CM type" is a choice of one complex embedding at each infinite place, and the set $\Phi$ of the argument is the set of infinite places.

### The classical theory of infinite places

Let $F$ be a number field of degree $n$. A complex embedding of $F$ is a ring homomorphism $\sigma : F \to \mathbb{C}$, and there are $n$ of them. Complex conjugation acts on them by $\sigma \mapsto \bar\sigma$. An embedding is real if $\sigma = \bar\sigma$. If $r_1$ is the number of real embeddings and $r_2$ is the number of pairs $\{\sigma, \bar\sigma\}$ with $\sigma \ne \bar\sigma$, then $r_1 + 2 r_2 = n$ (Neukirch, Ch. I, §5).

An infinite place of $F$ is an equivalence class of archimedean absolute values. Each one is $x \mapsto |\sigma(x)|$ for an embedding $\sigma$, and two embeddings give the same place if and only if they are equal or conjugate. So there are $r_1 + r_2$ infinite places. For a totally complex field, $r_1 = 0$ and the number of infinite places is $n/2$.

Let $E$ be a CM field of degree $2g$ with maximal totally real subfield $E^+$. A CM type of $E$ is a set $\Phi$ of $g$ complex embeddings of $E$ such that the embeddings are $\Phi \sqcup \bar\Phi$ (CM fields are in Washington, Ch. 4). So a CM type is the same as one choice of embedding at each infinite place of $E$. Restriction to $E^+$ is a bijection from the infinite places of $E$ to those of $E^+$, since the complex conjugation of $E$ is the same at every embedding.

The absolute norm and the trace are given by the infinite places. For $x \in E$ and $E$ totally complex,
$$|N_{E/\mathbb{Q}}(x)| = \prod_{w} |\sigma_w(x)|^2, \qquad \mathrm{Tr}_{E/\mathbb{Q}}(x) = \sum_{w} 2\,\mathrm{Re}\,\sigma_w(x),$$
where $w$ runs over the infinite places and $\sigma_w$ is either embedding at $w$. These follow from $N(x) = \prod_\sigma \sigma(x)$ and $\mathrm{Tr}(x) = \sum_\sigma \sigma(x)$ over all $n$ embeddings, grouped in conjugate pairs.

### Infinite places in Mathlib

**Definition (Infinite place).** An infinite place of a number field $F$ is an absolute value $F \to \mathbb{R}$ of the form $x \mapsto |\varphi(x)|$ for a complex embedding $\varphi$. The place of $\varphi$ is $\mathrm{mk}\,\varphi$.

Mathlib: `NumberField.InfinitePlace`, `NumberField.InfinitePlace.mk`.

Mathlib defines an infinite place as the absolute value itself, not as a class of absolute values. So the type has exactly $r_1 + r_2$ elements, and `NumberField.InfinitePlace.mk_eq_iff` (Mathlib) states that $\mathrm{mk}\,\varphi = \mathrm{mk}\,\psi$ if and only if $\psi = \varphi$ or $\psi = \bar\varphi$. The formula $r_1 + 2 r_2 = n$ is `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank` (Mathlib). For a CM field, the bijection with the places of $E^+$ is `NumberField.IsCMField.equivInfinitePlace` (Mathlib).

**Remark (Formalization).** Mathlib's `NumberField.InfinitePlace.embedding` (Mathlib) gives one embedding at each place. It is defined by `choose` from the existence of an embedding, so it is a fixed embedding, but the user cannot say which of the two it is. Theorems that use it hold for both.

### CM types in the source

**Definition (Place embedding).** A place embedding of a field $E$ is a function $\Phi$ that gives, for each infinite place $w$ of $E$, a complex embedding $\Phi_w : E \to \mathbb{C}$ with $\mathrm{mk}\,\Phi_w = w$.

Lean: `New.PlaceEmbedding` (Lib/Adelic/Adeles/Basic.lean).

**Definition (CM type).** The class `CMType E` contains three hypotheses: $E$ is a number field, $E$ is a CM field, and $E$ has a place embedding.

Lean: `New.CMType` (Lib/Adelic/Adeles/Basic.lean).

For a CM field, a place embedding is a CM type in the classical sense: it is the set $\{\Phi_w\}$ of one embedding at each place. The source writes $\Phi$ both for this function and, in the main theorem, for the index set. The index set of the twists and of the products in the argument is the type of infinite places of $E$, which [the field E](/chapter/fields-places-twists/) calls `New.Parameters.Φ`, with $f = \mathrm{towerDeg} \cdot \varphi(q_0)$ elements. The CM type on $E$ itself is given there by the place map `New.Parameters.galOfPlace`.

**Remark (Formalization).** The source declares a low priority instance of `PlaceEmbedding E` for every field, with $\Phi_w$ = `NumberField.InfinitePlace.embedding w` (Mathlib). So a place embedding is always found, and it is chosen by `choose`. This has three consequences.

1. A statement that depends on the place embedding is true for Mathlib's choice, unless a different instance is in scope. In the base change step of the source, `let : CMType (AdjoinRoot P) := ⟨⟩` gives $E[X]/(P)$ a CM type with the default place embedding.
2. The field $E$ has its own CM type instance, with priority over the default. A statement about $E$ in the main theorem uses the embeddings $\Phi_w$ from `New.Parameters.galOfPlace`, not Mathlib's.
3. Two statements about the same field can use different place embeddings if they elaborate with different instances in scope. This book has not found a place where this happens in the argument. A reader who checks a step should check which instance it uses.

The source also declares `DecidableEq (InfinitePlace E)` with `Classical.decEq`. Finite sums and products over the places use it.

### The adele ring and the norm

**Definition (Adeles of a totally complex field).** For a number field $E$, let $\mathbb{A}_E = \mathbb{C}^{\{\text{infinite places}\}} \times \mathbb{A}_{E,f}$, the product of one copy of $\mathbb{C}$ for each infinite place with the finite adeles. For a place embedding $\Phi$, the map $E \to \mathbb{A}_E$ is $x \mapsto ((\Phi_w(x))_w, x)$.

Lean: `New.𝔸`, `New.toAdele` (Lib/Adelic/Adeles/Basic.lean).

**Remark (Formalization).** The type `New.𝔸 E` is defined for every number field $E$. It is the adele ring of $E$ only when $E$ is totally complex. If $E$ has a real place $w$, then the component at $w$ should be $\mathbb{R}$, and here it is $\mathbb{C}$. The fields of the argument are CM, so they are totally complex and the definition is correct for them. The map `New.toAdele` depends on the place embedding: a different choice of $\Phi_w$ at one place changes the component by complex conjugation.

**Proposition.** Let $E$ be a totally complex number field with a place embedding $\Phi$, and let $x \in E$. Then:

1. $|N_{E/\mathbb{Q}}(x)| = \prod_w \|\Phi_w(x)\|^2$;
2. if $x \ne 0$ is an algebraic integer, then $\prod_w \|\Phi_w(x)\| \ge 1$;
3. $\mathrm{Tr}_{E/\mathbb{Q}}(x) = \sum_w 2\,\mathrm{Re}\,\Phi_w(x)$;
4. the image of $x \mapsto (\Phi_w(x))_w$ is dense in $\mathbb{C}^{\{\text{infinite places}\}}$.

Lean: `New.abs_norm_eq_prod_norm_sq`, `New.one_le_prod_norm_Φ`, `New.trace_eq_sum_Φ`, `New.denseRange_Φ` (Lib/Adelic/Adeles/StrongApproximation.lean).

*Proof.* For 1, the norm is the product over all $n$ embeddings, which come in the pairs $\{\Phi_w, \bar\Phi_w\}$, and $|\Phi_w(x)|\,|\bar\Phi_w(x)| = |\Phi_w(x)|^2$. Mathlib states the product over places with the multiplicity $2$ of a complex place (`NumberField.InfinitePlace.prod_eq_abs_norm` (Mathlib)), and the source rewrites it with $\mathrm{mk}\,\Phi_w = w$. For 2, the norm of a nonzero algebraic integer is a nonzero integer, so its absolute value is at least $1$, and so is the square root of the product in 1. For 3, take real parts in $\mathrm{Tr}(x) = \sum_\sigma \sigma(x)$ and group the embeddings in conjugate pairs. For 4, the source applies strong approximation, with the set of all finite places, and passes to the components at infinity. Classically 4 is the weak approximation theorem for the infinite places (Neukirch, Ch. II, Prop. 3.4), and it also follows from the fact that $E \otimes_{\mathbb{Q}} \mathbb{R} \cong \mathbb{C}^{r_2}$ and $\mathbb{Q}$ is dense in $\mathbb{R}$. $\square$

**Remark (Formalization).** Statements 1 to 3 do not depend on the place embedding, since $\|\bar z\| = \|z\|$ and $\mathrm{Re}\,\bar z = \mathrm{Re}\,z$. Statement 4 is true for every choice. The proof of 4 in the source goes through strong approximation for $\mathrm{GL}_n$ over the adeles, a deeper result than the statement. The argument uses 2 to bound from below the norms of algebraic integers, and 3 to show that the standard additive character of $\mathbb{A}_E$ is trivial on $E$ (`New.stdAddChar_toAdele`).

### What the argument uses of the infinite places

The argument uses the infinite places of $E$ in three ways. They index the twists $\chi_\phi$ and the products $\prod_{\phi \in \Phi}$ of the main theorem, as in [the field E](/chapter/fields-places-twists/). They give the components at infinity of the adeles, through `New.toAdele`. They give the bound $\prod_w \|\Phi_w(x)\| \ge 1$ for nonzero integers. This book has not found the reflex field or the type norm of a classical CM type in the source. The source uses only one embedding at each place and the group law that `New.Parameters.galOfPlace` puts on the places of $E$.
