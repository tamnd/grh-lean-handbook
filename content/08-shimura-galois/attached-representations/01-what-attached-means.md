---
title: What attached means
lean:
  - Lib/GaloisRep/Main/AttachedRepresentations.lean
  - Lib/GaloisRep/Main/Defs.lean
  - Lib/GaloisRep/Main/LocalConditions.lean
  - Lib/GaloisRep/Main/AllRanks.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What attached means

The argument needs Galois representations attached to automorphic forms on a definite unitary group. The source builds them itself, from Shimura varieties, in the files of `Lib/GaloisRep/Main`. Before the construction can be read, the reader must know what the source means by "attached". This chapter gives that meaning. It is weaker than the textbook meaning in three ways, and the chapter states each difference.

The chapter proves no existence theorem. It gives the definitions, the consequences that follow from the definitions alone, and the tools that the construction uses to make attached representations: the filter of most Frobenius elements, Chebotarev density, and pseudocharacters. The existence proof is in the chapter [Building the representations](/chapter/building-representations/).

### The classical notion

The model is Deligne's theorem for modular forms. Let $f$ be a newform of weight $k \geq 2$, level $N$ and character $\chi$, with Hecke eigenvalues $a_p$. Let $\ell$ be a prime and fix an isomorphism $\bar{\mathbb{Q}}_\ell \cong \mathbb{C}$. Then there is a continuous irreducible representation $\rho_f : \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\bar{\mathbb{Q}}_\ell)$ that is unramified at every prime $p \nmid N\ell$, and for such $p$ the characteristic polynomial of a Frobenius element at $p$ is $X^2 - a_p X + \chi(p) p^{k-1}$ (Diamond and Shurman, *A First Course in Modular Forms* (2005), Section 9.6). The representation is unique up to isomorphism, by Chebotarev density and the Brauer-Nesbitt theorem.

The general form is a theorem for regular algebraic, conjugate self-dual, cuspidal representations $\pi$ of $\mathrm{GL}_n$ over a CM field $F$. It gives a continuous semisimple $r_{\ell,\iota}(\pi) : \mathrm{Gal}(\bar F/F) \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$. At every finite place $v$, the Frobenius semisimple Weil-Deligne representation of $r_{\ell,\iota}(\pi)$ at $v$ corresponds to $\pi_v$ under the local Langlands correspondence, after a twist. At places above $\ell$ the representation is de Rham, with Hodge-Tate weights given by the weight of $\pi$. The statement is in T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, Potential automorphy and change of weight, Ann. of Math. 179 (2014), Section 2.1.

Three parts of the classical statement matter here. First, the characteristic polynomial of Frobenius is *equal* to the Hecke polynomial at almost all places. Second, at a place where $\pi$ is unramified, the representation is unramified (or crystalline above $\ell$) and the characteristic polynomial of Frobenius is again the Hecke polynomial. Third, the representation is unique up to isomorphism.

### What the source states

The source works with eigenforms $f$ on the definite unitary group $G$ of a CM field $E$, not with representations of $\mathrm{GL}_n$. An eigenform has, at almost all places $w$ of prime norm, a Hecke polynomial $P_w$ of degree $n$. Section 2 recalls these polynomials. A representation $\rho : \mathrm{Gal}(\Omega/E) \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ is *attached* to the family $P$ (Section 4) when four conditions hold:

1. $\rho$ is continuous;
2. the trace form of $\rho$ is non-degenerate, which is the source's form of semisimplicity;
3. a map $j$ from the group of $\rho$ to the Galois group is open (by default the group is the Galois group and $j$ is the identity);
4. for every $\eta > 0$, the coefficients of $\det(X - \rho(x)) - \iota_\ell(P_w)$ have absolute value at most $\eta$, for most Frobenius data $(w, A, s)$ and all $x$ with $j(x) = s$.

"Most" is a filter on Frobenius data (Section 3). It is weaker than "all Frobenius elements at almost all places". Condition 4 is an approximation and not an equality. These are the first difference and finding F-053 of the [register of findings](/chapter/register-of-findings/).

The local conditions are separate (Section 5). At a place $w$ where $f$ is spherical, the source asks that $\rho$ is unramified or crystalline, that it has the Hodge-Tate jumps of the weight, and that $\iota_\ell(P_w)$ *kills* every geometric Frobenius element: $\iota_\ell(P_w)(\rho(s)) = 0$. The polynomial need not be the characteristic polynomial. Above $\ell$ the source uses a linearized Frobenius on periods and no Weil-Deligne representation. This is the second difference and finding F-054.

Uniqueness holds only for traces (Section 4): two representations attached to the same family have the same trace. With non-degenerate trace forms, the Brauer-Nesbitt form of Section 7 makes them conjugate. This is the third difference.

### The place of the chapter

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The Galois side of the argument uses one theorem from `Lib/GaloisRep`. We state it here in full. It is proved in [Building the representations](/chapter/building-representations/), and its terms are defined in Sections 2 to 5 of this chapter.

**Theorem (Attached representations exist).** Let $\ell$ be a prime with a fixed isomorphism $\iota_\ell : \mathbb{C} \to \bar{\mathbb{Q}}_\ell$. Let $E$ be a CM field inside $\Omega$ with a CM type and Weil data, let $n$ be a nonempty finite set and let $w$ be a finite place of $E$. Let $f$ be an algebraic modular form of weight $\kappa$ on the standard definite unitary group of rank $|n|$, and an eigenform with Hecke polynomials $P$. Then:

1. some representation $r : \mathrm{Gal}(\Omega/E) \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ is attached to $P$;
2. if $f$ is spherical at $w$, then every representation $r$ attached to $P$ satisfies, at every place $A$ of $\Omega$ over $w$: $r$ is unramified or crystalline at $A$; $r$ has the Hodge-Tate jumps of $\kappa$ in rank $|n|$ at $A$; and if $w$ is split with Hecke polynomial $Q$, then $\iota_\ell(Q)$ kills every geometric Frobenius at $A$.

Lean: `New.GaloisRep.sphericalCompat_std` (Lib/GaloisRep/Main/AllRanks.lean).

The conclusion is the proposition `New.GaloisRep.SphericalCompat E n (card n) w` of Section 5. The Weil data contain a primitive root of unity of order $5040$ in $E$; the chapter [The Weil representation](/chapter/weil-representation/) defines them. The head of `Lib/GaloisRep/Main/AllRanks.lean` says that this theorem replaces base change to $\mathrm{GL}_n$ (Labesse), the Galois representations with local-global compatibility (Shin, Chenevier-Harris, Barnet-Lamb-Gee-Geraghty-Taylor) and the local Langlands correspondence. It also says: "Local polynomials kill but need not be characteristic. No Weil-Deligne representation is built."

The consumers are in `New/Congruences`. Volume 12, [the plan of the regular families](/chapter/regular-families-plan/), shows where the attached representations enter the argument. Section 4 of this chapter gives one consumer in full: an attached representation is conjugate self-dual.

### The model case

In rank one the source identifies the attached representation completely (Section 6). A form on $U(1)$ gives a character of the finite ideles, and the source shows that this character is an algebraic Hecke character $\theta$. The determinant of any attached representation is the $\ell$-adic avatar of $\theta$, the Galois character that class field theory gives. This is the analogue of the classical fact that the Galois representation of an algebraic Hecke character is its avatar. The reader can test each definition of the chapter on this case.

### What the chapter uses

The chapter uses the following. From Volume 3: the field $\Omega$, an algebraic closure of $\mathbb{Q}$; places of $\Omega$ as valuation subrings; arithmetic Frobenius elements and inertia groups ([CM fields](/chapter/cm-fields/)); and Chebotarev density in existence form ([class field theory](/chapter/class-field-theory/)). From Volumes 4 and 5: algebraic modular forms, the Hecke operators $T_{w,j}$ at split places and the Hecke polynomial ([automorphic forms](/chapter/automorphic-forms/), [Iwahori and Satake](/chapter/iwahori-satake/)). From Volume 7: crystalline representations, Weil pairs, the relation "kills" and Hodge-Tate jumps ([period rings](/chapter/period-rings/)).

The letter $\Omega$ follows Volume 3. In Volume 0 the same letter is the period of the data. This chapter does not use the period.

### Sketch and plan

Section 2 recalls eigenforms and Hecke polynomials and proves that a Hecke polynomial is monic of degree $n$. Section 3 defines the filter of most Frobenius data and proves, from Chebotarev, that a property of most Frobenius elements holds on a dense set. Section 4 defines attached representations, proves that the characteristic polynomial of $\rho(g)$ is a limit of Hecke polynomials, and deduces that two attached representations have the same trace. Section 5 gives the local conditions and the statement `SphericalCompat`, and explains "kills" against "characteristic". Section 6 treats rank one. Section 7 gives the pseudocharacter theorems with which the source makes representations from traces and passes to limits. Section 8 has exercises and notes.
