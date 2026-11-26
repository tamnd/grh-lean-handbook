---
title: Graded spaces and the map T
lean:
  - Lib/Weil/Periods/Grading.lean
  - Lib/Weil/Periods/StringPowers.lean
decls:
  - New.Grading
  - New.HasDegreeGe
  - New.Grading.stringPower
  - New.Grading.form_stringPower
  - New.Grading.shift
  - New.Grading.shift_mulVec_stringPower
  - New.Grading.stringMap
  - New.Grading.hasDegreeGe_neg_one_stringMap
  - New.Grading.stringMap_mulVec_stringPower
  - New.Grading.formAdjoint_stringMap_mul_stringMap
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Graded spaces and the map T

This section sets up the linear algebra of the chapter. A graded space is a hermitian space $V = X \oplus J_s$ with an orthonormal part $X$ and a string of $s$ vectors. The string behaves like the ring $E[\mathfrak{e}]/(\mathfrak{e}^s)$, with a hermitian form that pairs $\mathfrak{e}^i$ with $\mathfrak{e}^{s-1-i}$. For a second graded space $V' = X' \oplus J_{s-1}$ the section defines a rational map $T \colon V \to V'$ and proves the two identities $T^\dagger T = \mathfrak{e}$ and $T T^\dagger = \mathfrak{e}'$. These identities are the source of the generic characters in Section 3 and of the survival of orbits in Section 4.

### Spaces with a point

Let $E$ be a CM field with complex conjugation $z \mapsto \bar z$, and let $\mathbb{A}$ be its adele ring. A hermitian space with a point (Lean: `New.Space`) is a hermitian matrix $J$ over $E$, indexed by a finite set $\iota$, with an adelic matrix $x$ such that $x^{*} J x$ is a diagonal matrix of signs at the infinite places and $1$ at the finite places. Its group $G$ is the adelic unitary group of that standard form. For $g \in G$ the matrix $x g x^{-1}$ lies in $U(J)(\mathbb{A})$. It is the matrix of $g$ in rational coordinates (Lean: `New.Space.ratCoordMatrix`). All conditions on matrices in this chapter are conditions on this matrix. The group $V.\Gamma$ of rational points is the set of $g$ whose matrix in rational coordinates has entries in $E$.

### Gradings

**Definition (Grading).** Let $N \in E$ with $\bar N = N \neq 0$, let $X$ be a finite set and let $s \geq 0$. A grading of $V$ with constant $N$, part $X$ and string length $s$ consists of:

1. a bijection $X \sqcup \{0, \dots, s - 1\} \to \iota$; the basis vectors with index in $X$ are written $x_a$, and those with index $i$ in the string are written $e_i$;
2. the condition that the Gram matrix $J$ is the graded Gram matrix: $\langle x_a, x_b \rangle = \delta_{ab}$, $\langle x_a, e_i \rangle = 0$, and $\langle e_i, e_j \rangle = 0$ unless $i + j = s - 1$, with $\langle e_i, e_{s-1-i} \rangle = 1$ if $2i \neq s - 1$ and $\langle e_i, e_i \rangle = -N$ if $2i = s - 1$;
3. a constant $c \in E$ with $\bar c = c \neq 0$, the constant of the generic character.

The grade of $x_a$ is $0$, and the grade of $e_i$ is $s - 1 - 2i$.

Lean: `New.Grading`, with `New.gradedGram`, `New.Grading.gradeOf`, `New.Grading.genericConst` (Lib/Weil/Periods/Grading.lean).

So the grades on the string are $s - 1, s - 3, \dots, 1 - s$. The vectors $e_i$ and $e_{s-1-i}$ have opposite grades and pair to $1$. If $s$ is odd, the middle vector $e_{(s-1)/2}$ has grade $0$ and norm $-N$. If $s$ is even, every string vector has odd grade and the string is a sum of $s/2$ hyperbolic planes. The space $X$ is the definite part, and $X^\perp$ is the span of the string.

**Definition (Degree of a matrix).** Let $w'$ and $w$ be integer weights on the rows and on the columns of a matrix $x$, and let $d \in \mathbb{Z}$. The matrix $x$ has degree at least $d$ if $x_{ba} = 0$ whenever $w'(b) < w(a) + d$.

Lean: `New.HasDegreeGe` (Lib/Weil/Periods/Grading.lean).

A matrix of degree at least $d$ sends a basis vector of weight $k$ into the span of basis vectors of weight at least $k + d$. Degrees add under products (Lean: `New.HasDegreeGe.mul`). In this chapter the weights are the grades, except at one place in Section 4.

### The string as a truncated polynomial ring

The string vectors are normalised so that the string looks like $E[\mathfrak{e}]/(\mathfrak{e}^s)$.

**Definition (The vectors $\mathfrak{e}^i$).** For $0 \leq i$ put $\mathfrak{e}^i = p_i e_i$ if $i < s$ and $\mathfrak{e}^i = 0$ if $i \geq s$, where

$$p_i = c^{\,i - \lfloor s/2 \rfloor} \ \text{ if } 2i < s, \qquad p_i = -N c^{\,i - \lfloor (s-1)/2 \rfloor} \ \text{ if } 2i \geq s .$$

Lean: `New.Grading.stringPower`, `New.Grading.powerCoeff` (Lib/Weil/Periods/StringPowers.lean).

The exponents are integers, and they can be negative. The vector $\mathfrak{e}^i$ has grade $s - 1 - 2i$.

**Proposition (The form on the string).** For $0 \leq i, l < s$,

$$\langle \mathfrak{e}^i, \mathfrak{e}^l \rangle = -N \ \text{ if } i + l + 1 = s, \qquad \langle \mathfrak{e}^i, \mathfrak{e}^l \rangle = 0 \ \text{ otherwise}.$$

Lean: `New.Grading.form_stringPower` (Lib/Weil/Periods/StringPowers.lean).

*Proof.* The form is zero unless $l = s - 1 - i$. Let $l = s - 1 - i$. If $2i + 1 = s$ then $i = l$ is the middle index, $p_i = c^0 = 1$, and $\langle e_i, e_i \rangle = -N$. Otherwise exactly one of $i, l$, say $i$, has $2i < s$, and then $\bar p_i\, p_l = c^{\,i - \lfloor s/2 \rfloor} \cdot (-N) c^{\,l - \lfloor (s-1)/2 \rfloor}$. Since $i + l = s - 1 = \lfloor s/2 \rfloor + \lfloor (s-1)/2 \rfloor$, the powers of $c$ cancel, and the product is $-N$. Here $\bar c = c$ is used. $\square$

For odd $s$ the vector $z_N = \mathfrak{e}^{(s-1)/2}$ is the middle string vector, and its norm is $-N$ (Lean: `New.Grading.middlePower`, `New.Grading.form_middlePower`).

**Definition (The shift).** The shift $\mathfrak{e}$ is the rational endomorphism of $V$ that kills $X$ and $e_{s-1}$, and sends $e_b$ to $t_b\, e_{b+1}$ for $b < s - 1$, where $t_b = -N c$ if $e_b$ has grade $0$, $t_b = -N c^2$ if $e_b$ has grade $1$, and $t_b = c$ otherwise.

Lean: `New.Grading.shift` (Lib/Weil/Periods/Grading.lean).

**Proposition (The shift is multiplication by $\mathfrak{e}$).** For $0 \leq i < s$ the shift sends $\mathfrak{e}^i$ to $\mathfrak{e}^{i+1}$. In particular it sends $\mathfrak{e}^{s-1}$ to $0$.

Lean: `New.Grading.shift_mulVec_stringPower` (Lib/Weil/Periods/StringPowers.lean).

*Proof.* Both sides are multiples of $e_{i+1}$, so one compares coefficients: $t_i\, p_i = p_{i+1}$. If $2i + 2 < s$ both coefficients are powers of $c$ with exponents that differ by one, and $t_i = c$. If $e_i$ has grade $1$, then $2i + 2 = s$, $p_i = c^{-1}$ and $p_{i+1} = -N c$, so $t_i = -N c^2$. If $e_i$ has grade $0$, then $p_i = 1$, $p_{i+1} = -Nc$ and $t_i = -Nc$. If $2i \geq s$ both coefficients carry the factor $-N$ and $t_i = c$. $\square$

The shift raises grades by exactly $2$. So it is nilpotent, and $\mathfrak{e}^s = 0$. The vectors $\mathfrak{e}^0, \dots, \mathfrak{e}^{s-1}$ form a basis of $X^\perp$, and with the shift as multiplication, $X^\perp$ is a free module of rank one over $E[\mathfrak{e}]/(\mathfrak{e}^s)$. Over the finite adeles the source proves that the $\mathfrak{e}^i$ span $X^\perp$ (Lean: `New.Grading.exists_stringSum_eq`).

**Example (Small strings).** For $s = 1$ the string is one vector $e_0$ of grade $0$ and norm $-N$, $\mathfrak{e}^0 = e_0$ and $\mathfrak{e} = 0$. For $s = 2$ the string is a hyperbolic plane with $e_0$ of grade $1$ and $e_1$ of grade $-1$. Then $\mathfrak{e}^0 = c^{-1} e_0$, $\mathfrak{e}^1 = -Nc\, e_1$, and $\mathfrak{e} e_0 = -N c^2 e_1$. For $s = 3$ the grades are $2, 0, -2$, and $\mathfrak{e}^0 = c^{-1} e_0$, $\mathfrak{e}^1 = e_1$, $\mathfrak{e}^2 = -Nc\, e_2$. The shift sends $e_0$ to $c\, e_1$ and $e_1$ to $-Nc\, e_2$. In each case one checks the pairing $\langle \mathfrak{e}^i, \mathfrak{e}^{s-1-i} \rangle = -N$ directly.

### The map between neighbouring strings

Now let $Y$ be a grading of $V$ with string length $s$, and let $Y'$ be a grading of a second space $V'$ with the same constant $N$ and string length $s'$. Write $e'_j$ for the string vectors of $V'$, and $c'$ for its constant.

**Definition (The map $T$).** The map $T \colon V \to V'$ kills $X$. It sends $e_a$ to $\tau_a e'_a$ if $a < s'$, and to $0$ if $a \geq s'$. The factor $\tau_a$ depends on the parity of $s$ and on the grade of $e_a$ in $V$. If $s$ is odd, $\tau_a$ is $1$, $-Nc$ or $c$ when the grade is positive, zero or negative. If $s$ is even, $\tau_a$ is $c$ or $1$ when the grade is positive or negative.

Lean: `New.Grading.stringMap` (Lib/Weil/Periods/Grading.lean).

The map $T$ has entries in $E$, so it is a rational point of $\operatorname{Hom}(V, V')$. Only the constant $c$ of $V$ enters its definition.

**Lemma (Degree of $T$).** If $s' = s - 1$, then $T$ has degree at least $-1$ for the grades of $V'$ on the rows and of $V$ on the columns.

Lean: `New.Grading.hasDegreeGe_neg_one_stringMap` (Lib/Weil/Periods/Grading.lean).

*Proof.* The only nonzero entries of $T$ are at $(e'_a, e_a)$. The grade of $e'_a$ in $V'$ is $s - 2 - 2a$, and the grade of $e_a$ in $V$ is $s - 1 - 2a$. The difference is $-1$. $\square$

**Proposition ($T$ is the projection).** Let $s' = s - 1$ and $c' = c$. For $0 \leq i < s$ the map $T$ sends $\mathfrak{e}^i$ of $V$ to $\mathfrak{e}^i$ of $V'$. In particular $T \mathfrak{e}^{s-1} = 0$.

Lean: `New.Grading.stringMap_mulVec_stringPower`, with `New.Grading.stringMapFin_stringSum` for the same statement over the finite adeles (Lib/Weil/Periods/StringPowers.lean).

*Proof.* One compares $\tau_i\, p_i$ with the coefficient $p'_i$ for the string of length $s - 1$, in the cases of the definitions. The case $i = s - 1$ holds since $\mathfrak{e}^{s-1} = 0$ in $V'$. $\square$

So $T$ is the reduction $E[\mathfrak{e}]/(\mathfrak{e}^s) \to E[\mathfrak{e}]/(\mathfrak{e}^{s-1})$ on $X^\perp$, and zero on $X$. This explains the factors $\tau_a$: they are the ratios of the normalising coefficients of the two strings.

### The adjoint identities

For an adelic map $y \colon V \to V'$ its adjoint is $y^\dagger = J^{-1} y^{*} J'$, so that $\langle y v, v' \rangle' = \langle v, y^\dagger v' \rangle$ (Lean: `New.Space.formAdjoint`).

**Theorem (The adjoint identities).** Let $s' = s - 1$. Then

1. $T^\dagger T = \mathfrak{e}$, the shift of $V$;
2. if $c' = c$, then $T T^\dagger = \mathfrak{e}'$, the shift of $V'$.

Lean: `New.Grading.formAdjoint_stringMap_mul_stringMap`, which joins `New.Grading.formAdjoint_stringMap_mul_stringMap_eq_shift` and `New.Grading.stringMap_mul_formAdjoint_stringMap_eq_shift` (Lib/Weil/Periods/Grading.lean).

*Proof.* The map $T^\dagger$ kills $X'$ and sends $e'_b$ to a multiple of $e_{b+1}$, because $e'_b$ pairs only with $e'_{s-2-b}$ and $e_{b+1}$ pairs only with $e_{s-2-b}$. So $T^\dagger T$ and $T T^\dagger$ raise the number of a string vector by one, and both sides of each identity are of the same shape. It remains to compare one factor for each $b$. For (1) the factor of $T^\dagger T$ at $e_b$ is $\tau_b$ times the factor of $T^\dagger$ at $e'_b$. That second factor is computed from the pairings: it is $\bar\tau_{s-2-b}$ times the ratio of the pairings $\langle e'_b, e'_{s-2-b} \rangle'$ and $\langle e_{b+1}, e_{s-2-b} \rangle$. A case check on the parity of $s$ and on the grade of $e_b$ gives $t_b$. For (2) the same check gives $t'_b$, the factor of the shift of $V'$. Here the constant of $V'$ must be $c$, because $T$ uses only $c$ and $\mathfrak{e}'$ uses $c'$. $\square$

**Example (The case $s = 3$).** Let $s = 3$ and $s' = 2$. Then $T e_0 = e'_0$, $T e_1 = -Nc\, e'_1$ and $T e_2 = 0$. From $\langle T e_0, e'_1 \rangle' = 1 = \langle e_0, e_2 \rangle$ one gets $T^\dagger e'_1 = e_2$. From $\langle T e_1, e'_0 \rangle' = -Nc = \langle e_1, c\, e_1 \rangle$ one gets $T^\dagger e'_0 = c\, e_1$. So $T^\dagger T e_0 = c\, e_1$ and $T^\dagger T e_1 = -Nc\, e_2$. These are the values of the shift of $V$. In the other order, $T T^\dagger e'_0 = c\, T e_1 = -N c^2 e'_1$, which is the shift of $V'$ at the vector $e'_0$ of grade $1$, if $c' = c$.

**Remark (Formalization).** The constant $c$ is a field of the structure `New.Grading`, not a datum chosen inside a proof. Each grading carries its own constant, and the hypothesis $c' = c$ of part (2) is stated as `Y'.genericConst = Y.genericConst`. Part (1) needs no such hypothesis. Part (2) is used only for the iteration of the unfolding in Section 5. A chain of gradings in which all constants are equal satisfies the hypothesis at each step.
