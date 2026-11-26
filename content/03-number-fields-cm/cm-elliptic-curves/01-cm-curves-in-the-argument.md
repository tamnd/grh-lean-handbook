---
title: CM elliptic curves in the argument
lean:
  - Lib/CM/ChowlaSelberg.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## CM elliptic curves in the argument

This chapter gives the background on elliptic curves with complex multiplication that the source uses. The field is $K = \mathbb{Q}(\sqrt{-d})$ for a prime $d \equiv 7 \pmod 8$. The chapter treats the classical theory first: lattices with complex multiplication by $\mathcal{O}_K$, the main theorem of complex multiplication, the Hecke character of a CM curve, Kronecker's first limit formula and the formula of Chowla and Selberg. Then it says what the source proves, in which form, and with which hypotheses. The last result of the chapter is the form of the Chowla-Selberg formula that the source proves, [Theorem](/decl/New.CMLattice.chowla_selberg/). Volume 1 uses it through the constant $C_d$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/).

### Where the chapter sits

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The argument fixes a prime $d \equiv 7 \pmod 8$ and the field $K = \mathbb{Q}(\sqrt{-d})$. The first chapter of this volume, [CM fields](/chapter/cm-fields/), gives the facts on $K$ that this chapter uses: $K$ is a subfield of $\mathbb{C}$, the prime $2$ splits in $K$, and only $d$ ramifies. The second chapter, [class field theory](/chapter/class-field-theory/), gives the Hecke L-functions and Euler products over the places of $K$. This chapter uses one Euler product from there, the Dedekind zeta function of $K$. The third chapter, [local duality](/chapter/local-duality/), is not used here. The next chapter that uses this one is in Volume 9: [the CM formal group](/chapter/cm-formal-group/) and [the integral vacuum](/chapter/integral-vacuum/) work with the curve, its theta function and the number $u$ of the Chowla-Selberg formula.

Two numbers of the argument come from this chapter. The first is the Chowla-Selberg constant
$$C_d = \gamma - \operatorname{Re} \frac{L'}{L}(1, \chi_K),$$
where $\gamma$ is Euler's constant and $\chi_K = (\cdot / d)$ is the Legendre symbol modulo $d$. [Definition](/decl/New.chowlaSelbergConst/) in Volume 1 gives it with its Lean form. The second is the scale
$$\Omega = e^{C_d} \cdot \frac{2\pi}{\mathrm{rd}_E},$$
where $\mathrm{rd}_E$ is the root discriminant of the CM field $E$ of the argument. The source defines $\Omega$ in `New.Parameters.bigOmega` (New/Reduction/Data/FieldsAndPlaces.lean). The derivative bounds of Theorem A compute the modulus of a period scale from the area of a CM lattice and the Chowla-Selberg formula (New/Derivatives/Vacuum/Scale.lean). The link between the two numbers is the Chowla-Selberg formula: the period lattices of a CM curve and of its Galois conjugates have the area $\pi e^{C_d} \cdot 2\pi / \sqrt d$, after a scaling by a $p$-adic unit at every $p$.

### What the chapter proves

The chapter follows the files of the directory `Lib/CM` of the source. The order is the order in which a reader needs the results.

1. Section 2 gives the classical theory, with citations. No Lean names appear there.
2. Section 3 defines the objects of the source. A CM lattice for $K$ is a lattice $\Lambda \subset \mathbb{C}$ stable under $\mathcal{O}_K$, with a point $t$ of order $2$ and a normalisation $\wp''(t) = 2$. The source builds a sigma function $\sigma$ and a theta function $\theta$ for $\Lambda$, and the curve $y^2 + a_1 x y = x^3 + x$ with discriminant $a_1^4 - 64$.
3. Section 4 proves that every CM lattice is a multiple of a fractional ideal, computes the areas, and proves good reduction: $a_1^4 - 64$ is a unit at every $p$-adic place of $\mathbb{C}$. It also proves that the class number of $K$ is odd.
4. Section 5 proves integrality at a $p$-adic place: torsion values of $\sigma$ and $\theta$, the formal group law, isogenies, and a bound on the height of the formal group.
5. Section 6 constructs the Galois conjugate of a CM lattice and proves a soft form of the main theorem of complex multiplication for the translates of $\theta$.
6. Section 7 proves Kronecker's first limit formula for real $s$, sums it over the class group, and proves the Chowla-Selberg formula of the source.
7. Section 8 has exercises and notes.

### The sketch

The proof of the Chowla-Selberg formula of the source has four steps.

1. **Kronecker's limit formula.** For a lattice $\Lambda$ of area $A$ and discriminant $\Delta = g_2^3 - 27 g_3^2$, the Epstein zeta function $\sum_{l \ne 0} (|l|^2 / A)^{-s}$ has a pole at $s = 1$ with residue $\pi$, and its constant term is $\pi (2\gamma - \log(A |\Delta|^{1/6} / \pi^2))$. The source proves this for real $s \in (1, 2)$, with a right derivative at $s = 1$.
2. **Sum over the classes.** Take one CM lattice in each ideal class. The sum of the Epstein zeta functions is $\#\mathcal{O}_K^\times \cdot \zeta_K(s)$, up to a factor. The factorisation $\zeta_K(s) = \zeta(s) L(s, \chi_K)$ and the comparison of the constant terms give the geometric mean of $A |\Delta|^{1/6}$ over the classes in terms of $L'/L(1, \chi_K)$.
3. **Good reduction.** For a CM lattice with the normalisation of the source, $|\Delta| = |a_1^4 - 64|$, and $a_1^4 - 64$ is a unit at every $p$-adic place. A multiplier that takes one CM lattice into another is $p$-adically integral. So the scalings between the lattices of the classes are $p$-adic units in total.
4. **One number for all conjugates.** The odd class number gives ideals $\mathfrak{c}_{\mathcal{C}}$, one in each class, with product $(1)$. A $12h$-th root $u$ of a product of the discriminants and scalings is then a unit at every $p$-adic place. The areas of the conjugate lattices, scaled by $\sigma(u)$, all equal $\pi e^{C_d} \cdot 2\pi/\sqrt d$.

The source makes three choices that a reader must know before Section 3.

1. **No algebraic geometry.** The source works with lattices in $\mathbb{C}$ and with power series. It does not define the curve over a number field, its reduction modulo a prime, or its Néron model. "Good reduction" means that the number $a_1^4 - 64$ has norm $1$ under every ring homomorphism $\mathbb{C} \to \mathbb{C}_p$.
2. **Automorphisms of $\mathbb{C}$.** The Galois action is the action of all field automorphisms of $\mathbb{C}$ over $K$, most of them not continuous. The source applies them to the Taylor coefficients of functions at $0$, never to the functions.
3. **Choices.** The sigma function and the conjugate lattice are chosen with `choose`. So the statements of the source are about these chosen objects. Each section says where this matters.

The source claims that all results of `Lib/CM` are proved. Lean accepts them, if the reported checks hold. This chapter explains the statements and the proofs.
