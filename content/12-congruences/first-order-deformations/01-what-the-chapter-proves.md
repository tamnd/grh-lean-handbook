---
title: What the chapter proves
lean:
  - New/Congruences/FirstOrder/TrianglePrimes.lean
  - New/Congruences/FirstOrder/HeckeStrings.lean
  - New/Congruences/FirstOrder/AuxiliaryPrimeTie.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter builds the auxiliary places of Ribet's method and the operators that live at them. It has four results. The first chooses finitely many places of a CM field, the same number at every level $\ell^\nu$, such that the tame generators and the Frobenius elements at these places cut down the even classes in the Tate twists. The second shows that at most Frobenius elements the Hecke polynomial of a weak lift is a full chain of roots times an integral factor. The third deforms the norm map from the deep auxiliary level to the base level, to first order in one parameter for each place. The fourth shows that the top coefficient of Ribet's element clears the denominator of the projection to the lifts.

### Its place in the plan

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). Theorem C needs regular families, and [the plan of this volume](/chapter/regular-families-plan/) states the chain of steps that gives them. The first step of that chain is Ribet's method to first order. It gives, for one lift generator, an integral Hecke operator that is not too divisible by $\ell$ at the lift and that kills the forms far from it. Three chapters prove this step. [Ribet elements](/chapter/ribet-elements/) builds Ribet's element from a trace ideal. This chapter supplies the trace ideal, the auxiliary places at which it lives, and the operators that carry the element back to the base level. [The bound for denominators](/chapter/denominator-bound/) puts the pieces together and turns a congruence into a Selmer class.

The argument of this chapter is the core of the first-order method. The reader must follow every step from this book. The background is in Volumes 2 to 8, and each piece of it is stated here in one line with a link.

### What it uses

The chapter uses these facts from earlier volumes.

1. CM fields, their maximal real subfields, and the standing condition that $E$ contains the $5040$-th roots of unity: [CM fields](/chapter/cm-fields/).
2. Chebotarev's density theorem in the form of an existence statement: [class field theory](/chapter/class-field-theory/).
3. The Greenberg-Wiles count of relations as an inequality: [local duality](/chapter/local-duality/).
4. Finite sets of test points that detect cocycles unramified off $\ell$, from the bound on odd classes: [odd classes](/chapter/odd-classes/).
5. The filter of most Frobenius elements, and what it means for a representation to be attached: [what attached means](/chapter/attached-representations/).
6. Taylor-Wiles places, the base level of forms, its Hecke algebra and local-global compatibility at split places: [building the representations](/chapter/building-representations/).
7. The chain lemma for Satake parameters of unitary unramified representations: [Iwahori exponents and the chain lemma](/chapter/iwahori-satake/).
8. Ribet's element of a trace ideal, and the notions of trace ideal and common Ribet element: [Ribet elements](/chapter/ribet-elements/).

The chapter also uses definitions that belong to [the bound for denominators](/chapter/denominator-bound/): even classes, the triangle condition, the tied ideal, the trace elements of the Hecke algebra and the reductions modulo $\ell^\nu/(2 n!)$. This chapter states each of them in full where it first appears.

### Notation

Fix a prime $\ell$. Let $\Omega$ be the algebraic closure of $\mathbb{Q}$. Let $E \subset \Omega$ be a CM field that contains a primitive $5040$-th root of unity, and let $F$ be its maximal real subfield. Write $G = \mathrm{Gal}(\Omega/E)$ and $G_F = \mathrm{Gal}(\Omega/F)$. Fix a complex conjugation $c \in G_F$, so that $G_F = G \cup Gc$, and write $g^c = c g c^{-1}$ for $g \in G$. Let $\mathrm{cyc} \colon G \to \mathbb{Z}_\ell^\times$ be the $\ell$-adic cyclotomic character, and let $G_\nu$ be the kernel of $\mathrm{cyc}$ modulo $\ell^\nu$, that is, the subgroup that fixes the $\ell^\nu$-th roots of unity. A *coefficient ring* is the ring of integers $O$ of a finite Galois extension of $\mathbb{Q}_\ell$ inside $\overline{\mathbb{Q}}_\ell$. For $e \geq 0$, the module $(O/\ell^\nu)(-e)$ is $O/\ell^\nu$ with $G$ acting by $\mathrm{cyc}^{-e}$.

A *Frobenius datum* is a prime $w$ of $E$ of prime norm $q$, a place of $\Omega$ above $w$, and a geometric Frobenius element $\varphi$ at that place. At each place of $\Omega$ above a prime $w$ off $\ell$ there is a chosen generator $\tau$ of tame inertia, the *tame generator*.

### A sketch

The chapter has three parts.

The first part is Galois cohomology over $F$. An even class is a cocycle of $G$ in $(O/\ell^\nu)(-e)$ that is invariant under $g \mapsto g^c$. It extends to $G_F$, and over $F$ it pairs with the relations of the Greenberg-Wiles count. The restriction of a relation to $G$ is a *Kummer map* $\psi \colon G \to \mathbb{Z}/\ell^\nu$. For places $w_j$ with Frobenius elements $\varphi_j$ and tame generators $\gamma_j$, the pairing gives the reciprocity law

$$\sum_j \psi(\varphi_j) \cdot 2 z(\gamma_j) = 0$$

for every even class $z$ that may ramify at the $w_j$ ([the reciprocity law](/chapter/first-order-deformations/#kummer-maps-and-the-reciprocity-law)). The count gives more Kummer maps modulo $\ell$ than there are places so far. So a new Kummer map exists that the old ones do not span. Nakayama's lemma gives an element of $G_\nu$ at which the old maps vanish and the new one is nearly a unit. Chebotarev's theorem gives a new place whose Frobenius element is near that element. The reciprocity law of the new map then has one term at the new place, and it bounds the even classes at the new tame generator. Done in order, for each exponent $e$ with $0 < e < t$ and each test point, this gives the triangle of primes ([the triangle of primes](/chapter/first-order-deformations/#the-triangle-of-primes)).

The second part is about Hecke polynomials. Let $u$ be the representation of a weak lift, twisted so that every $u(g)$ has the eigenvalue $1$. Local-global compatibility makes $X_0$ a root of the Hecke polynomial at a split place $w$ of norm $q$, where $X_0$ comes from the twisting character at Frobenius. The unitary chain lemma then gives the whole chain $X_0, X_0 q, \dots, X_0 q^{t-1}$, with $t = n - r$. At most Frobenius elements, the rest of the Hecke polynomial divides an integral polynomial with value $1$ at $1$ ([root chains of weak lifts](/chapter/first-order-deformations/#root-chains-of-weak-lifts)).

The third part is about operators on forms. At an auxiliary place $w_j$, write $\mathrm{Nm}_j$ for the sum over the group $\mathrm{GL}_n(\mathbb{F}_{w_j})$. The root chain gives an integral operator $\partial_j$ at $w_j$ with

$$\mathrm{Nm}_j\, \mathrm{tr}[(\gamma_j - 1) g] = 0, \qquad \partial_j\, \mathrm{tr}[(\gamma_j - 1) g] \equiv \mathrm{Nm}_j\, \mathrm{tr}[(\varphi_j - 1) H_j(\varphi_j) g]$$

modulo $\ell^\nu/(2 n!)$. The product $\prod_j (\mathrm{Nm}_j + \alpha_j \partial_j)$ in variables $\alpha_j$ with $\alpha_j^2 = 0$ kills the ideal of tied relations $\gamma_j - 1 - \alpha_j (\varphi_j - 1) H_j(\varphi_j)$ ([the deformed norm](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm)). Applied to Ribet's element of that ideal, the family gives the bound: if $2 n! (n_0 c^2)^{\#J + 1}$ divides $\ell^\nu$, then $d c$ times the top coefficient of Ribet's element, applied to the projection of a form $l$ with $d l$ integral, is integral ([the top coefficient](/chapter/first-order-deformations/#the-top-coefficient-clears-denominators)).

### The four main results

Here are the four results in short form. Each section states its result in full with all hypotheses.

1. (Triangle of primes.) Let $E$ lie in a cyclotomic field of level $N$, let $N + t < y$, let $\gamma$ generate $G$ modulo $\ker \mathrm{cyc}$, let $\mathrm{cyc}(\gamma)^a - 1$ divide $\ell^h$ for $0 < a < t$, let $\ell \leq y^2$ or $h = 0$, let $E$ have at least four infinite places, and let a set $W$ of Frobenius data contain most Frobenius elements near $\delta^{\ell^\nu} g$ for some $\delta$ of trivial $\mathrm{cyc}$, for all $\nu$ and $g$. Then one finite ordered index set $J$ serves every level $\ell^\nu$, $\nu > 0$, with Taylor-Wiles places in $W$ that form a triangle of primes for $\gamma^{-1}$ with the bounds $y h$ and $y^{22} h$.
2. (Root chains.) For most Frobenius data, if the characteristic polynomial of $u(\varphi)$ is congruent to $S \cdot \prod_{i < t} (X - \mathrm{cyc}(\varphi)^{-i})$ with $\|S(1)\| \geq 1$, then the rescaled Hecke polynomial is $\prod_{i<t}(X - q^i)$ times a divisor of an integral polynomial $e$ with $e(1) = 1$.
3. (Deformed norm.) There are integral operators $\mathcal{N}_S$, for $S \subseteq J$, that commute with the Hecke algebra, with $\mathcal{N}_\emptyset = \mathrm{Nm}$, that kill the tied ideal modulo $\ell^\nu/(2 n!)$, and that factor through $\mathrm{Nm}$ after multiplication by $(c^2 \delta')^{\#J}$.
4. (Top coefficient.) The top coefficient of a common Ribet element, times $d c$ and applied to the projection of $l$, gives an integral form, under the divisibility $2 n! (n_0 c^2)^{\#J+1} \mid \ell^\nu$.

The source claims these results. Lean accepts them, if the reported checks hold.

### How the sections are arranged

The sections follow the order in which a reader learns the material. [The real subfield and even classes](/chapter/first-order-deformations/#the-real-subfield-and-even-classes) sets up the passage from $E$ to $F$ and defines even classes. [Kummer maps](/chapter/first-order-deformations/#kummer-maps-and-the-reciprocity-law) proves the reciprocity law and counts the Kummer maps. [The triangle of primes](/chapter/first-order-deformations/#the-triangle-of-primes) chooses the places, and it works a model case with one exponent and one test point. [Root chains](/chapter/first-order-deformations/#root-chains-of-weak-lifts) treats the Hecke polynomials. The last two sections build the operators and the bound. The chapter ends with [exercises and notes](/chapter/first-order-deformations/#exercises).
