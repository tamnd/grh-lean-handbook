---
title: Splitting characters and Weil data
lean:
  - Lib/Weil/Construction/WeilData.lean
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/ClassField/Global/CMSplittingCharacters.lean
  - Lib/ClassField/Grunwald.lean
  - New/Derivatives/Field/WeilData.lean
decls:
  - New.SplittingChar
  - New.WeilData
  - New.HasPrimitiveRoot5040
  - New.CMTypeOver
  - New.Cohomology.IsRealTimesNorm
  - New.Cohomology.quadraticIdeleChar
  - New.Cohomology.upsilon_eq_quadraticIdeleChar
  - New.Cohomology.upsilon_atUniformizer_eq_neg_one
  - New.nonempty_splittingChar
  - New.nonempty_splittingChar_of_cmTypeOver
  - New.nonempty_weilData_of_not_dvd_differentIdeal
  - New.Parameters.exists_unit_prod_phi_eq_one_and_mul_star_eq
  - New.Parameters.instWeilDataE
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Splitting characters and Weil data

The steps of the last section carry Weil data: an element, an idele and a *splitting character* on a CM field. A splitting character is an unramified unitary Hecke character that restricts to the quadratic character of the CM extension on the real subfield. 

### The textbook form

Let $E$ be a CM field with maximal real subfield $E^+$, complex conjugation $x \mapsto \bar x$ and a CM type $\Phi$, one embedding $\Phi_w$ for each infinite place $w$. Weil introduced the characters of type $A_0$: those $\chi$ for which there is an integer function $n$ on the embeddings with $\chi((\alpha)) = \prod_\sigma \sigma(\alpha)^{n_\sigma}$ for $\alpha \equiv 1$ modulo the conductor (A. Weil, "On a certain type of characters of the idèle-class group of an algebraic number-field", *Proceedings of the International Symposium on Algebraic Number Theory, Tokyo-Nikko 1955*, Science Council of Japan, 1956). An exposition of these characters is in A. Raghuram, "Notes on the arithmetic of Hecke L-functions", arXiv:2207.03399, §4. The source cites both.

A splitting character in the sense of the source is the unitary form of such a character: on the ideles whose finite part is a unit, it is $x \mapsto \prod_w x_w/|x_w|$, so it is unramified at every finite place. In addition $\upsilon(\bar x) = \upsilon(x)^{-1}$. On an idele fixed by conjugation, this gives $\upsilon(x)^2 = 1$. The source shows that $\upsilon$ is then the quadratic character $\eta$ of $E/E^+$ on the ideles of $E^+$.

Such a character does not exist for every CM field. Here is a necessary condition. A root of unity $\zeta \in E$ is a principal idele whose finite part is a unit. So a splitting character has $1 = \upsilon(\zeta) = \prod_w \Phi_w(\zeta)$. Exercise 5 applies this to $\mathbb{Q}(i)$.

### The definitions

**Definition (Splitting character).** For a field $E$ with a CM type, a `SplittingChar E` is a unitary Hecke character $\upsilon$ of $E$ with two properties. (a) If the finite part of the idele $x$ is a unit of $\hat{\mathcal{O}}$, then $\upsilon(x) = \prod_w x_w/|x_w|$ over the infinite places. (b) $\upsilon(\bar x) = \upsilon(x)^{-1}$.

Lean: `New.SplittingChar` (Lib/Weil/Construction/WeilData.lean).

**Definition (Roots of unity of order $5040$).** `HasPrimitiveRoot5040 E` says that $E$ contains a primitive $5040$-th root of unity.

Lean: `New.HasPrimitiveRoot5040` (Lib/Adelic/Adeles/Basic.lean).

Here $5040 = 7!$. The docstring of `WeilData` says that under this condition $E/E^+$ is unramified at the finite places. The source also proves that a finite place fixed by conjugation then has norm $r^2$ with $r \equiv 3 \pmod 4$ (`New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert`, Lib/General/NumberTheory/FrobeniusOrbits.lean).

**Definition (Weil data).** For a CM field $E$ with a CM type, `WeilData E` extends `HasPrimitiveRoot5040 E` and `SplittingChar E` with the following fields. An element $\jmath \in E$ with $\bar\jmath = -\jmath$ and $\mathrm{Im}\, \Phi_w(\jmath) > 0$ for every infinite place $w$. A finite idele $\alpha$ such that, at every finite place $w$, the order of $\jmath \alpha \bar\alpha$ is minus the order of the different of $E$ at $w$. The condition that $(1 - \jmath^{-1})/2$ is an algebraic integer. The condition that $\upsilon$ is $-1$ at the chosen uniformiser of every finite place $w$ with $\bar w = w$.

Lean: `New.WeilData` (Lib/Weil/Construction/WeilData.lean).

The condition on $\alpha$ says that $\hat{\mathcal{O}}$ is self-dual for the pairing $(z, u) \mapsto \psi_f(\jmath \alpha \bar\alpha z u)$, with $\psi_f$ the standard additive character of the finite adeles. This chapter uses only the existence of these data.

**Definition (Compatible CM types).** For an extension $L/E$, `CMTypeOver E L` is a CM type of $L$ that restricts to the given CM type of $E$: an embedding of $L$ is the chosen one at its place exactly when its restriction to $E$ is the chosen one at the place below.

Lean: `New.CMTypeOver` (Lib/GaloisRep/BaseChange/CommutingHeckeFamilies.lean).

CM types are treated in the chapter [CM fields, towers and places](/chapter/cm-fields/#infinite-places-and-cm-types).

### The restriction to the real subfield

**Definition (Real times norm).** An idele $x$ of $E$ is *real times norm* if $x = a z \bar z$ for some $a \in E^\times$ with $\bar a = a$ and some idele $z$ of $E$.

Lean: `New.Cohomology.IsRealTimesNorm` (Lib/ClassField/Global/CMSplittingCharacters.lean).

**Definition (Quadratic character).** `quadraticIdeleChar E x` is $1$ if $x$ is real times norm and $-1$ otherwise.

Lean: `New.Cohomology.quadraticIdeleChar` (Lib/ClassField/Global/CMSplittingCharacters.lean).

On the ideles of $E^+$ this is the quadratic character $\eta$ of $E/E^+$, by the norm theorem of class field theory. Its values at ideles moved by conjugation are not used.

**Theorem (Splitting characters restrict to $\eta$).** Let $\upsilon$ be a splitting character of $E$, and let $x$ be an idele with $\bar x = x$. Then $\upsilon(x) = $ `quadraticIdeleChar E x`.

Lean: `New.Cohomology.upsilon_eq_quadraticIdeleChar` (Lib/ClassField/Global/CMSplittingCharacters.lean).

*Proof.* From (b), $\upsilon(x)\upsilon(\bar x) = 1$, so $\upsilon(x)^2 = 1$ and $\upsilon(x) = \pm 1$. If $x = a z \bar z$, then $\upsilon(x) = \upsilon(a)\upsilon(z)\upsilon(\bar z) = 1$. Conversely, the source shows that $\upsilon(x) = 1$ forces $x$ to be real times norm, with the norm theorem for $E/E^+$. $\square$

**Corollary.** A splitting character is $-1$ at the chosen uniformiser of every finite place $w$ with $\bar w = w$.

Lean: `New.Cohomology.upsilon_atUniformizer_eq_neg_one` (Lib/ClassField/Global/CMSplittingCharacters.lean).

So the field `υ_inert` of `WeilData` holds for every splitting character.

### Existence

**Theorem (Existence of splitting characters).** Let $E$ be a CM field with a CM type $\Phi$ and a primitive $5040$-th root of unity. Suppose that every root of unity $y \in E$ is $\delta/\bar\delta$ for a unit $\delta$ of $\mathcal{O}_E$ with $\prod_w \Phi_w(\delta) = 1$. Then $E$ has a splitting character.

Lean: `New.nonempty_splittingChar` (Lib/ClassField/Global/CMSplittingCharacters.lean).

*Proof.* Let $S(x) = \prod_w x_w/|x_w|$, let $U$ be the open group of ideles that are units at every finite place, and let $R$ be the group of ideles $y b \bar b$ with $y \in E^\times$. The key step is $S = 1$ on $U \cap R$. For $x = y b \bar b \in U$, the number $\bar y/y$ is a root of unity, so it is $\delta/\bar\delta$ by the hypothesis. Then $a = y\delta$ is real, the finite part of $a b \bar b$ is a local norm because $E/E^+$ is unramified at the finite places, and class field theory for $E/E^+$ gives $\prod_w \Phi_w(a) > 0$. So $S(x) = 1$. The circle group is divisible, so $S|_U$ extends to a character trivial on $R$. It is continuous because it agrees with $S$ on $U$, and it satisfies (b) because $x\bar x \in R$. $\square$

The hypothesis implies the necessary condition above. The source does not show that it is necessary.

**Theorem (The hypothesis for the field of the construction).** Let $E = K(\zeta)$, with $K = \mathbb{Q}(\sqrt{-d})$ and $\zeta$ a primitive root of unity of order $q_1$, as in the parameters of the source. Every root of unity of $E$ is $\delta/\bar\delta$ for a unit $\delta$ of norm $1$ over $K$.

Lean: `New.Parameters.exists_unit_prod_phi_eq_one_and_mul_star_eq` (New/Derivatives/Field/WeilData.lean).

*Proof.* Write $y = \zeta^k$. Since $4 \mid q_1$, a power $i$ of $\zeta$ is a square root of $-1$. The element $\eta = i(\zeta - 1)$ has norm $1$ to $K$ and satisfies $\zeta\bar\eta = \eta$. Take $\delta = \eta^k$. The product $\prod_w \Phi_w(\delta)$ is the norm of $\delta$ to $K$. $\square$

**Definition (Weil data of the field of the construction).** The source defines Weil data on $E = K(\zeta)$ with $\jmath = -1/\sqrt{-d}$, an explicit idele $\alpha$, and the splitting character given by `nonempty_splittingChar` and the last theorem.

Lean: `New.Parameters.instWeilDataE` (New/Derivatives/Field/WeilData.lean).

So in the only use, the hypothesis of `nonempty_splittingChar` is proved.

### Lifting to extensions

**Theorem (Splitting characters lift).** Let $L/E$ be an extension with compatible CM types, and let $E$ have a splitting character $\upsilon$. Then $\upsilon \circ N_{L/E}$ is a splitting character of $L$, where the norm at an infinite place $w$ of $E$ is the product of the components at the places of $L$ above $w$.

Lean: `New.nonempty_splittingChar_of_cmTypeOver` (Lib/ClassField/Grunwald.lean).

**Theorem (Weil data lift).** Let $L/E$ be an extension of CM fields with compatible CM types. Let $E$ have Weil data, and let $L$ contain a primitive $5040$-th root of unity. If no finite place of $L$ fixed by conjugation divides the relative different of $\mathcal{O}_L$ over $\mathcal{O}_E$, then $L$ has Weil data.

Lean: `New.nonempty_weilData_of_not_dvd_differentIdeal` (Lib/ClassField/Grunwald.lean).

*Proof.* Keep $\jmath$ and take $\upsilon \circ N_{L/E}$. Let $g$ generate the different of $L$ and let $s = \jmath g$. At a place $u = \bar u$, the hypothesis on the relative different and `self_dual` for $E$ make the order of $s$ even. So a new idele $\beta$ can take half of the order of $s$ at each pair $\{u, \bar u\}$, and $s\beta\bar\beta$ is a unit everywhere. The field `υ_inert` holds by the corollary above. $\square$

**Remark (Formalization).** The source claims proofs of all statements of this section. The hypothesis with content is the condition on roots of unity in `New.nonempty_splittingChar`. It is a hypothesis of the theorem, not a field of a structure. The user `New.Parameters.instWeilDataE` proves it for $E = K(\zeta)$ by an explicit unit. The condition on $5040$-th roots of unity is a hypothesis of both existence theorems. No statement of this section takes a duality or reciprocity statement as a hypothesis; the norm theorem for $E/E^+$ is used inside the proofs. If the reported checks hold, Lean accepts these statements with the hypotheses as stated.
