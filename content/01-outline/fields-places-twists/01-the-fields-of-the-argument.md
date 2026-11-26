---
title: The fields of the argument
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/LevelAndTwists.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The fields of the argument

This chapter fixes the arithmetic objects on which the rest of the proof is built. They are two integers $q_0$ and $d$, an imaginary quadratic field $K$, a CM field $E$ over $K$, the group $\Phi$ of the infinite places of $E$, a real number $\Omega$, and three kinds of characters of the norm-one adeles of $E$: tame characters, twists and $m$-fold twists. Most of the facts are classical. The interest is in the exact choices: why the modulus $q_0$ is a multiple of $18480$, why $d$ lies in the class $q_0/2 - 1$ modulo $q_0$, why the degree of $E$ over $K$ has the special form $3 \cdot l_0 \cdot 2^s \cdot \varphi(q_0)$, and why every field of the argument contains a primitive root of unity of order $5040 = 7!$.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) reduces the theorem to a one-sided bound for a weighted sum over primes. The bound concerns the primes that split in a quadratic field $K = \mathbb{Q}(\sqrt{-d})$, and it must hold for every prime $d$ in a fixed class modulo $q_0$. This is the hypothesis of [Landau's criterion](/chapter/landau-criterion/), which asks for $8 \mid q_0$ and $d \equiv 7 \bmod 8$. The source proves the bound with a lattice of automorphic forms on unitary groups over the CM field $E$ ([why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/)). The forms have weights at the infinite places of $E$, and they are twisted by characters of $U(1)$ over $E$ with prescribed weights and ramification. This chapter builds these objects. The next chapter, [the data and its sizes](/chapter/data-and-sizes/), adds the scales $x \le x_1 \le b$, the weights, the levels and the primes, and gives the sizes of all of them.

### The objects

Here is the list, in the order of the chapter. Each item has its exact statement in a later section.

1. The parameters (Section 2). A multiple $q_0$ of $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$, and a prime $d$ with $q_0 \mid 2(d+1)$ and $q_0 \nmid d + 1$. Then $d \equiv q_0/2 - 1 \bmod q_0$ and $d \equiv 7 \bmod 8$.
2. The field $K = \mathbb{Q}(\sqrt{-d}) \subset \mathbb{C}$, with the character $\chi_K = (\cdot / d)$ (Section 2).
3. The tower degree $\mathrm{towerDeg}(s) = 3 \cdot l_0(s) \cdot 2^s$, where $l_0(s)$ is a power of $3$ between $27s$ and $81s$, and the modulus $q_1 = q_0 \cdot \mathrm{towerDeg}(s)$ (Section 3).
4. The field $E = K(\zeta)$, with $\zeta$ a primitive root of unity of order $q_1$. It has degree $\varphi(q_1)$ over $K$, it is abelian over $\mathbb{Q}$, and it is a CM field (Section 3).
5. The group $\Phi$ of the infinite places of $E$, with an isomorphism $\Phi \cong \mathrm{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$ (Section 4).
6. The number $\Omega = e^{\mathrm{CS}(d)} \cdot 2\pi / \mathrm{rd}_E$, where $\mathrm{CS}(d) = \gamma - \operatorname{Re} L'/L(1, \chi_K)$ and $\mathrm{rd}_E$ is the root discriminant of $E$ (Section 4).
7. Characters of $U(1)(\mathbb{A}_E)$ with a weight and a tame part, the tame characters, twists and $m$-fold twists, and the characters $\mu_j^0 \vartheta^j$ of a chain of lifts (Section 6).

Section 5 is a worked example with $q_0 = 18480$, $d = 9239$ and $s = 0$.

### What the chapter uses

The chapter uses algebraic number theory at the level of Neukirch, Chapter I: Dedekind domains, the decomposition of primes in Galois extensions, the Dedekind and Kummer criterion, and cyclotomic fields. It also uses the adeles. The only analysis is the definition of the constant $\mathrm{CS}(d)$ (see [the weighted prime remainder](/chapter/weighted-prime-remainder/)).

### The sketch

The arithmetic rests on one observation. The norm of $\beta_K = (1 + \sqrt{-d})/2$ is $(d+1)/4$, and the condition on $d$ makes every prime of $q_0$ divide it. By the criterion of Dedekind and Kummer, these primes split in $K$, and in particular $2, 3, 5, 7, 11$ split. The prime $d$ is prime to $q_1$, so $E = K(\zeta)$ has degree $\varphi(q_1)$ over $K$, with Galois group $(\mathbb{Z}/q_1)^\times$. This group permutes the infinite places of $E$ simply transitively, so they form a group $\Phi$. Since $d > 64$, the field $E$ has no primitive $d$-th root of unity, so its roots of unity are the powers of $\zeta$. This controls the characters of $U(1)$: a character with a given weight and tame part exists if the formula for it is $1$ on the integral elements of norm one, and these are roots of unity.

The number $5040$ comes from the root of unity. The order $q_1$ is a multiple of $3 \cdot 18480 = 55440$, and $5040$ divides $55440$. A primitive $5040$-th root of unity gives a square root $i$ of $-1$ and the element $\omega = (1 \pm \sqrt{-7})/2$ of norm $2$. From these, the source proves that $E$ is unramified over its maximal real subfield at every finite place, that the places over $2$ are moved by complex conjugation, and that every residue field of $E$ has at least $4$ elements. Section 3 proves each of these facts.

### Conventions

Throughout, $q_0$, $d$ and $s$ are natural numbers, and $s$ is called the tower exponent. In the data of [the data and its sizes](/chapter/data-and-sizes/) the exponent $s$ is chosen with $2^s = m^{22}$. In this chapter $s$ is arbitrary. We write $\varphi$ for Euler's function. A finite place $w$ has a residue field with $q_w$ elements. Complex conjugation on the CM field $E$ is written $y \mapsto \bar y$, and it acts on the places by $w \mapsto \bar w$. A finite place $w$ is called split if $\bar w \neq w$. This is the convention of the source: split means split over the maximal real subfield $E^+$.
