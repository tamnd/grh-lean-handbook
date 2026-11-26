---
title: The field E at the primes
lean:
  - New/Derivatives/Field/PrimeDecomposition.lean
  - New/Derivatives/Field/WeilData.lean
  - New/Derivatives/Field/ChosenPlaces.lean
decls:
  - New.Parameters.betaKInE_mul_one_sub
  - New.Parameters.star_betaKInE
  - New.Parameters.adjoin_betaKInE_zetaInt_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The field E at the primes

The proof of Theorem A works one prime at a time and then at the infinite places. At each step it needs a fact about the CM field $E = K(\zeta)$: how a rational prime splits in $E$, what the different of $E$ is, which Weil data the theta lifts use, and which places carry the level $M = p_0 p_1$. This chapter collects these facts. It states each one as Lean states it, and it proves each one from the book.

### Where the chapter sits

[Theorem A and its plan](/chapter/theorem-a-plan/) states Theorem A and its three inputs: the divisibility of a chain of theta lifts prime by prime, the seesaw identity, and the archimedean size of the composite lift. The place of Theorem A in the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/). The objects of the upper bound are built in [the objects of the upper bound](/chapter/upper-bound-objects/), and the first half of the seesaw identity is in [the seesaw identity, part 1](/chapter/seesaw-identity-1/).

This chapter gives the arithmetic of $E$ that the later chapters use. The list shows where each part goes.

1. The different of $E$ and its imaginary generator $\varpi$ (Section 2). The size of $\varpi$ at the infinite places gives the size of the root discriminant, which enters the archimedean size of the composite lift. The generator of the different of $E/K$ enters the idele $\alpha$ of the Weil data.
2. The decomposition of a prime $p \nmid q_1 d$ (Section 3). The columns and the lift chains of [the objects of the upper bound](/chapter/upper-bound-objects/) use that such a prime is unramified.
3. Inert primes and self-conjugate places (Section 4). The nonsplit primes of the gain, the marked primes of [marked primes and the valuation of a chain](/chapter/chain-valuation/) and the mark operator of [divisibility prime by prime](/chapter/divisibility/) use the description of the decomposition group of an inert prime and a congruence for the Frobenius.
4. The places above a prime $p \equiv 1 \bmod q_1 d$ and the Weil data (Section 5). The level $N$ and the primes $p_0$, $p_1$ are of this kind. The Weil data fix the Weil representation of [the Weil representation](/chapter/weil-representation/) on $E$. The number $s_0$ of Section 5 is the scale of [the integral vacuum](/chapter/integral-vacuum/).
5. The chosen places, their residue characters, the finiteness of pairs, and the bounds for $\varpi$ and $\mathrm{rd}_E$ (Section 6).

### What the chapter uses

The parameters $q_0$, $d$, $s$, the numbers $q_1$, $q_2$, the field $E$, the root $\zeta$ and the group $\Phi$ of infinite places are defined in [fields, places and twists](/chapter/fields-places-twists/). The scales $x$, $b$, the primes $p_0$, $p_1$ and the integer $\bar\pi_M$ are in [data and sizes](/chapter/data-and-sizes/). The imaginary quadratic field, finite places, the conjugate place $\bar w$, the norm $q_w$, root discriminants and the differents $\delta_{E/K}$ and $\sqrt{-d}$ are in [CM fields](/chapter/cm-fields/). Ideles and Hecke characters are in [class field theory](/chapter/class-field-theory/). Splitting characters and the class of Weil data are in [local duality](/chapter/local-duality/).

We recall the notation. The prime $d$ satisfies $d \equiv q_0/2 - 1 \bmod q_0$, with $18480 \mid q_0$. So $d \equiv 7 \bmod 8$, and $K = \mathbb{Q}(\sqrt{-d})$. The character $\chi_K(p) = (p/d)$ is the Legendre symbol. Every prime that divides $q_1$ splits in $K$ and divides $(d+1)/4$. A prime $p$ with $\chi_K(p) \ne 1$ satisfies $p \geq 13$. The field $E$ is $K(\zeta)$ with $\zeta$ of order $q_1$, and $\mathrm{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$. There are $f = \varphi(q_1)$ infinite places. For $v \in \Phi$ we write $\sigma_v \in \mathrm{Gal}(E/K)$ for its automorphism and $\Phi_v = \iota \circ \sigma_v$ for its embedding. For an integer $\nu$ prime to $q_1$, $v_\nu$ is the place that corresponds to the class of $\nu$, so $\sigma_{v_\nu}(\zeta) = \zeta^\nu$.

The ring of integers of $K$ is $\mathbb{Z}[\beta_K]$ with $\beta_K = (1 + \sqrt{-d})/2$. Its image in $E$ is the first generator that this chapter uses.

**Lemma.** In $\mathcal{O}_E$, $\beta_K (1 - \beta_K) = (d+1)/4$ and $\bar\beta_K = 1 - \beta_K$. So $\beta_K \bar\beta_K = (d+1)/4$ and $\beta_K + \bar\beta_K = 1$.

Lean: `New.Parameters.betaKInE_mul_one_sub`, `New.Parameters.star_betaKInE` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* The first identity is $(1 + \sqrt{-d})(1 - \sqrt{-d})/4 = (1 + d)/4$ in $\mathcal{O}_K$, mapped to $\mathcal{O}_E$. Complex conjugation sends $\sqrt{-d}$ to $-\sqrt{-d}$. So $2\bar\beta_K - 1 = -(2\beta_K - 1)$, and $\bar\beta_K = 1 - \beta_K$ after division by $2$ in the domain $\mathcal{O}_E$. $\square$

So no prime ideal of $\mathcal{O}_E$ contains both $\beta_K$ and $\bar\beta_K$: it would contain their sum $1$. The chapter uses this fact several times.

**Theorem.** The ring of integers of $E$ is $\mathbb{Z}[\beta_K, \zeta]$.

Lean: `New.Parameters.adjoin_betaKInE_zetaInt_eq_top` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* By [CM fields](/chapter/cm-fields/), $\mathcal{O}_K = \mathbb{Z}[\beta_K]$. By Section 2, $\mathcal{O}_E = \mathcal{O}_K[\zeta]$. So $\mathcal{O}_E$ is generated over $\mathbb{Z}$ by $\beta_K$ and $\zeta$. $\square$

So a ring homomorphism from $\mathcal{O}_E$ is fixed by its values at $\beta_K$ and $\zeta$ (Lean: `New.Parameters.ringHom_ext_zetaInt_betaKInE`). All the computations of Sections 3 and 4 reduce to these two values.

### A model case

The true parameters are very large: $q_1 \geq 18480 \cdot 3^5$. To see the mechanism, take a model that is not an instance of the parameters: $d = 23$ and $q_1 = 12$. It has the two properties that the chapter uses most. First, $d \equiv 7 \bmod 8$. Second, the primes $2$ and $3$ of $q_1$ split in $K = \mathbb{Q}(\sqrt{-23})$ and divide $(d+1)/4 = 6$. Indeed $(2/23) = 1$ since $23 \equiv 7 \bmod 8$, and $(3/23) = -(23/3) = -(2/3) = 1$ by reciprocity.

**Example.** Let $E = \mathbb{Q}(\sqrt{-23}, \zeta_{12})$. It has degree $8$, $f = 4$ infinite places, and $\mathrm{Gal}(E/K) \cong (\mathbb{Z}/12)^\times = \{1, 5, 7, 11\}$. The cyclotomic polynomial is $\Phi_{12}(X) = X^4 - X^2 + 1$, so $\Phi_{12}'(\zeta) = 2\zeta(2\zeta^2 - 1)$. With $\zeta = e^{2\pi i/12}$ we have $2\zeta^2 - 1 = i\sqrt{3}$, so $\Phi_{12}'(\zeta) = 2\sqrt{-3}\,\zeta$. Its absolute value is $2\sqrt{3}$ at every place. The discriminant of $E$ is $144^2 \cdot 23^4 = 2^8 \cdot 69^4$, since $\mathbb{Q}(\zeta_{12})$ and $K$ have coprime discriminants $144$ and $-23$. So $\mathrm{rd}_E = 2\sqrt{69}$, which is $|\Phi_{12}'(\zeta)| \cdot \sqrt{23}$. Section 2 proves this equality for the true $E$.

**Example.** In the same model, take $p = 11$. Then $(11/23) = -(23/11) = -(1/11) = -1$, so $11$ is inert in $K$. As $11 \equiv -1 \bmod 12$, the Frobenius sends $\zeta$ to $\zeta^{11} = \bar\zeta$, and it sends $\sqrt{-23}$ to $-\sqrt{-23}$. So it acts on $E$ as complex conjugation, and every place of $E$ above $11$ is its own conjugate. The places have norm $11^2$, and there are $8/2 = 4$ of them. Section 4 shows that, for the true parameters, a self-conjugate place lies over a prime $p \equiv -1 \bmod 2^{s+1}$. The same argument in the model gives $p \equiv -1 \bmod 4$, and indeed $11 \equiv -1 \bmod 4$.

**Example.** In the same model, take $p = 5$. Then $(5/23) = (23/5) = (3/5) = -1$, so $5$ is inert in $K$. The Frobenius sends $\zeta$ to $\zeta^5$ and $\sqrt{-23}$ to $-\sqrt{-23}$. In $\mathrm{Gal}(E/K) \times \{\pm 1\}$ it is the element $\sigma_7$ followed by conjugation, since $\sigma_7(\bar\zeta) = \zeta^{-7} = \zeta^5$. This element has order $2$. So a place $w$ above $5$ has norm $25$, the stabilizer of $w$ is $\{1, \sigma_7 \circ c\}$ with $c$ the complex conjugation, and $\bar w \neq w$.

### The plan of the chapter

Section 2 computes the different. It finds a generator $\varpi$ of the different of $E$ with $\bar\varpi = -\varpi$, and it proves $\prod_v |\varpi|_v = \mathrm{rd}_E^f$. Section 3 defines the Frobenius element of a prime $p \nmid q_1 d$ as a pair in $\Phi \times \mathbb{Z}$. It describes the decomposition group, the norm of a place, the ramification and the transitivity of the Galois action. Section 4 treats inert primes, self-conjugate places, and primes $p \equiv 1 \bmod q_1 d$. Section 5 counts the places above such a prime that divide a given element, and it builds the Weil data of $E$ and the number $s_0$. Section 6 treats the chosen places, their residue characters, the finiteness of pairs, and the bounds $x^{10} \le |\varpi|_v, \mathrm{rd}_E \le x^{12}$. Section 7 has exercises and notes.

The arguments in this chapter are standard algebraic number theory. The interest is in the exact form of the statements, and in the places where Lean picks an object by a choice.

**Remark (Formalization).** The source writes `P.E s` for $E$, `P.Φ s` for $\Phi$, `P.zetaInt s` for $\zeta$ as an element of $\mathcal{O}_E$, `P.betaKInE s` for $\beta_K$ and `star` for complex conjugation. The letter $P$ in the comments of the source sometimes means the cyclotomic polynomial, as in $P'(\zeta)$, and sometimes the parameters. The book writes $\Phi_{q_1}'(\zeta)$ or $\delta_{E/K}$ for the first, as [CM fields](/chapter/cm-fields/) does.
