---
title: Dirichlet characters in Mathlib
lean:
  - Statements.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Dirichlet characters in Mathlib

Three of the five statements quantify over a modulus $N$ and a Dirichlet character $\chi$ modulo $N$. One of them adds the hypothesis that $\chi$ is primitive, and one of them excludes the case $\chi = 1$. This section reads the definitions of Mathlib behind these words: `DirichletCharacter`, the character `1`, the change of level, the conductor and `IsPrimitive`. Each one is the classical object. The section ends with three small moduli, as a test.

### The classical definition

Let $q \geq 1$. A Dirichlet character modulo $q$ is a function $\chi \colon \mathbb{Z} \to \mathbb{C}$ that comes from a group homomorphism $(\mathbb{Z}/q\mathbb{Z})^\times \to \mathbb{C}^\times$, extended by $\chi(n) = 0$ when $\gcd(n, q) > 1$ (Davenport, Chapter 4; Apostol, Chapter 6). The *principal character* $\chi_0$ is $1$ on the integers prime to $q$ and $0$ on the others. A character $\chi$ modulo $q$ is *induced* by a character $\chi^*$ modulo a divisor $d$ of $q$ if $\chi(n) = \chi^*(n)$ for every $n$ prime to $q$. The *conductor* of $\chi$ is the least $d$ such that $\chi$ is induced by a character modulo $d$. The character is *primitive* if its conductor is $q$ (Davenport, Chapter 5).

### Characters in Mathlib

**Definition (Dirichlet character).** For a commutative monoid with zero $R$ and $n \in \mathbb{N}$, a Dirichlet character of level $n$ with values in $R$ is a multiplicative character of the ring $\mathbb{Z}/n\mathbb{Z}$: a map $\chi \colon \mathbb{Z}/n\mathbb{Z} \to R$ with $\chi(1) = 1$, $\chi(ab) = \chi(a)\chi(b)$, and $\chi(a) = 0$ for every $a$ that is not a unit.
Mathlib: `DirichletCharacter` is the abbreviation `MulChar (ZMod n) R`, and `MulChar` is the structure of a monoid homomorphism with the field `map_nonunit'`.

The statements take $R = \mathbb{C}$. For $n \geq 1$ the units of $\mathbb{Z}/n\mathbb{Z}$ are the classes prime to $n$. So a term of `DirichletCharacter ℂ N` is a homomorphism of the unit group into the multiplicative monoid $\mathbb{C}$, extended by $0$. The units form a finite group, so the values on units are roots of unity, and in particular not $0$. This is the classical object. A character is applied to an integer or a natural number through the cast into `ZMod N`. So `χ p` for a prime $p$ is $\chi(p \bmod N)$.

Two levels need care.

- At $N = 1$ the ring `ZMod 1` has one element, and $0 = 1$ in it. So $0$ is a unit, and the only character sends it to $1$. As a function on $\mathbb{Z}$ this character is $1$ at every integer. This is the classical principal character modulo $1$.
- At $N = 0$ the ring `ZMod 0` is $\mathbb{Z}$. Its units are $\pm 1$, so its characters have no classical meaning. The statements exclude $N = 0$ by the hypothesis `[NeZero N]`. They include every $N \geq 1$.

**Definition (The character 1).** For every level $n$, the character `1` of `DirichletCharacter R n` is the character that is $1$ on units and $0$ on nonunits.
Mathlib: the instance `MulChar.hasOne`, with value `MulChar.trivial`, and the lemma `MulChar.one_apply`.

So `1` modulo $N$ is the principal character $\chi_0$ modulo $N$. It is not the constant function $1$, except at $N = 1$. The docstrings of Mathlib and of Main.lean call it the "trivial" character. The README of the source calls it the principal character (grh/README.md, line 18). Both names refer to the same object. The hypothesis `χ ≠ 1 ∨ s ≠ 1` in the half-plane statement therefore excludes the pole of $L(s, \chi_0)$ for every modulus, and nothing else.

**Definition (Change of level).** Let $n \mid m$ and let $\psi$ be a character of level $n$. Then `changeLevel hm ψ` is the character of level $m$ whose value at a unit $a$ of $\mathbb{Z}/m\mathbb{Z}$ is $\psi(a \bmod n)$, and whose value at a nonunit is $0$.
Mathlib: `DirichletCharacter.changeLevel`, defined as `MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))`.

Here `ZMod.unitsMap hm` is the reduction map $(\mathbb{Z}/m\mathbb{Z})^\times \to (\mathbb{Z}/n\mathbb{Z})^\times$, and `MulChar.ofUnitHom` extends a homomorphism on units by $0$. So `changeLevel hm ψ` is the character modulo $m$ induced by $\psi$. Its value at an integer $a$ that is prime to $n$ but not to $m$ is $0$, though $\psi(a) \neq 0$. This loss of Euler factors is the reason for the product in `DirichletCharacter.LFunction_changeLevel`, which Section 4 states.

**Definition (Conductor and primitivity).** Let $\chi$ be a character of level $n$.

1. $\chi$ *factors through* $d$ if $d \mid n$ and $\chi = $ `changeLevel h χ₀` for some character $\chi_0$ of level $d$.
2. The *conductor set* of $\chi$ is the set of $d \in \mathbb{N}$ such that $\chi$ factors through $d$.
3. The *conductor* of $\chi$ is `sInf` of the conductor set.
4. $\chi$ is *primitive* if its conductor is $n$.

Mathlib: `DirichletCharacter.FactorsThrough`, `DirichletCharacter.conductorSet`, `DirichletCharacter.conductor` and `DirichletCharacter.IsPrimitive`.

Item 1 is the classical "induced by a character modulo $d$". Two characters modulo $n$ that agree on units are equal, so equality of characters is equality on integers prime to $n$, as in the classical definition. For a set of natural numbers that is not empty, `sInf` is its least element. So item 3 is the classical conductor, and item 4 is the classical primitivity.

**Remark (Formalization).** In Lean, `sInf ∅ = 0` for sets of natural numbers. This junk value cannot occur here. The level $n$ is always in the conductor set, since $\chi$ = `changeLevel (dvd_refl n) χ` (Mathlib: `DirichletCharacter.level_mem_conductorSet`). For $n \neq 0$ Mathlib also proves that the conductor is not $0$ (`DirichletCharacter.conductor_ne_zero`) and that it divides $n$ (`DirichletCharacter.conductor_dvd_level`).

**Remark (Formalization).** Mathlib also defines a primitive character `DirichletCharacter.primitiveCharacter` of level equal to the conductor, which induces $\chi$. It is chosen by `Classical.choose`, but it is unique: change of level is injective, so at most one character of level $d$ induces $\chi$. None of the five statements uses it. The source uses it in the reduction from an imprimitive character to a primitive one, in [the deduction of the line from the half-plane](/chapter/half-plane-to-line/).

**Theorem (The principal character).** For every $n \neq 0$, the conductor of `1` of level $n$ is $1$. In particular `1` of level $1$ is primitive, and `1` of level $n > 1$ is not primitive.
Mathlib: `DirichletCharacter.conductor_one` and `DirichletCharacter.isPrimitive_one_level_one`.

**Definition (Parity).** A character $\psi$ is *even* if $\psi(-1) = 1$ and *odd* if $\psi(-1) = -1$. Every character with values in $\mathbb{C}$ is even or odd.
Mathlib: `DirichletCharacter.Even`, `DirichletCharacter.Odd` and `DirichletCharacter.even_or_odd`.

Parity fixes the gamma factor of the L-function, and the source uses it in the functional equation. The characters of level $N$ form a group under pointwise product, with inverse $\chi^{-1}$. For values in $\mathbb{C}$, $\chi^{-1}(a)$ is the complex conjugate of $\chi(a)$ at every unit $a$. The functional equation relates $L(s, \chi)$ to $L(1 - s, \chi^{-1})$.

### Three small moduli

**Example (Modulus 4).** The units of $\mathbb{Z}/4\mathbb{Z}$ are $1$ and $3$. There are two characters. The character `1` has conductor $1$. The other character $\chi_{-4}$ has $\chi_{-4}(3) = -1$. It does not factor through $1$, since the only character of level $1$ induces `1`. It does not factor through $2$, since the only unit modulo $2$ is $1$, so the only character of level $2$ induces `1` as well. So $\chi_{-4}$ has conductor $4$ and is primitive. It is odd, since $-1 = 3$ in $\mathbb{Z}/4\mathbb{Z}$.

**Example (Modulus 6).** The units of $\mathbb{Z}/6\mathbb{Z}$ are $1$ and $5$. There are two characters: `1`, and $\chi$ with $\chi(5) = -1$. Let $\chi_{-3}$ be the character modulo $3$ with $\chi_{-3}(2) = -1$. Then `changeLevel` of $\chi_{-3}$ to level $6$ sends $5$ to $\chi_{-3}(5 \bmod 3) = \chi_{-3}(2) = -1$. So $\chi$ factors through $3$. It does not factor through $1$ or $2$, as in the example of modulus $4$. Its conductor is $3$. So there is no primitive character modulo $6$. The same holds for every $N \equiv 2 \pmod 4$. The statement `PrimitiveDirichletLZerosOnLine` of Section 5 is empty at such $N$.

**Example (Modulus 12).** The units of $\mathbb{Z}/12\mathbb{Z}$ are $1, 5, 7, 11$, and each one has square $1$. There are four characters. Their values at $5, 7, 11$ are these.

| character | $\chi(5)$ | $\chi(7)$ | $\chi(11)$ | conductor | parity |
|---|---|---|---|---|---|
| `1` | $1$ | $1$ | $1$ | $1$ | even |
| induced by $\chi_{-4}$ | $1$ | $-1$ | $-1$ | $4$ | odd |
| induced by $\chi_{-3}$ | $-1$ | $1$ | $-1$ | $3$ | odd |
| $\chi_{12}$ | $-1$ | $-1$ | $1$ | $12$ | even |

The second row is $\chi_{-4}$ at $5 \equiv 1$, $7 \equiv 3$ and $11 \equiv 3 \pmod 4$. The third row is $\chi_{-3}$ at $5 \equiv 2$, $7 \equiv 1$ and $11 \equiv 2 \pmod 3$. The last character is the product of the second and the third. It is not $1$ on the units that are $1$ modulo $4$, since $\chi_{12}(5) = -1$, and it is not $1$ on the units that are $1$ modulo $3$, since $\chi_{12}(7) = -1$. A character modulo $12$ that factors through $2$ or $6$ also factors through $4$ or $3$ respectively, by the two examples above. So $\chi_{12}$ is the only primitive character modulo $12$. It is the character of the field $\mathbb{Q}(\sqrt{3})$.

### What the reader can take from this section

Each word of the statements about characters has its classical meaning in Mathlib. The only junk values are at the level $N = 0$, which the statements exclude, and the value `sInf ∅`, which cannot occur. The one point of language is the name of `1`: it is the principal character of level $N$, and the docstrings call it "trivial".
