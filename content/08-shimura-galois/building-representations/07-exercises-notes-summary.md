---
title: Exercises, notes and a summary of the volume
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $a = 2$. Show that the matrix $1 \in \mathrm{GL}_2(\bar{\mathbb Q}_\ell)$ is killed by $(X - 1)(X - 2)$, but that its characteristic polynomial is $(X - 1)^2$. Then show that if a polynomial $P$ of degree $a$ kills a matrix $g$ of size $a$ whose eigenvalues are distinct, then $P$ is a scalar multiple of $\det(X - g)$.

*Hint.* For the second part, every eigenvalue of $g$ is a root of $P$, and there are $a$ of them.

**Exercise 2.** Let $P = X^2 - e_1 X + e_2$ have roots $\alpha$ and $\beta$. Write $\alpha^m + \beta^m$ for $m = 1, 2, 3$ as polynomials in $e_1$ and $e_2$. Explain why the trace of $r(s)^m$ is close to $\alpha^m + \beta^m$ when the characteristic polynomial of $r(s)$ is close to $\iota_\ell(P)$. This is the first step of the proof of [the theorem on limits](/decl/New.GaloisRep.exists_attached_of_isApproximatingMonoid/).

*Hint.* Newton's identities give $p_1 = e_1$, $p_2 = e_1^2 - 2e_2$ and $p_3 = e_1^3 - 3e_1e_2$. In an ultrametric field, products and sums of numbers of norm at most $1$ have norm at most $1$.

**Exercise 3.** Let $Q$ be a polynomial of degree $d$ and $z \neq 0$. The polynomial `Q.scaleRoots z` is $z^{d} Q(X/z)$. Show that its roots are $z$ times the roots of $Q$, with the same leading coefficient. Compute it for $Q = (X - \alpha)(X - \beta)$.

*Hint.* The coefficient of $X^i$ in `Q.scaleRoots z` is $Q_i z^{d - i}$.

**Exercise 4.** Take $n$ of size $1$ in [the theorem on every rank](/decl/New.GaloisRep.sphericalCompat_std/). Find $t$ and the rank of the theta lift. List the roots of the Hecke polynomial of the lift at a split place $w$, multiplied by $\theta_{t,t}(w)$. Explain why the theorem in rank one also follows from [the model case](/decl/New.isSplit_of_q_prime/) of Section 1, and why the source does not treat rank one separately.

*Hint.* Here $t = 2$ and the rank is $3$. The roots are $\alpha$, $\theta_{3,2}(w)$ and $\theta_{3,1}(w)$. The source proves all ranks by one argument and has no separate proof in rank one.

**Exercise 5.** Let $L = K(\sqrt d)$ be a quadratic extension of number fields with nontrivial automorphism $\sigma$. Let $u$ be a finite idele of $L$ with $u\,\sigma(u) = 1$. Show that $c = a + u\,\sigma(a)$ satisfies $u\,\sigma(c) = c$ for every finite adele $a$. [Hilbert 90 for finite ideles](/decl/New.hilbert90_finite_idele/) says that some such $c$ is invertible. Show this at one place $v$ of $L$ where $u_v$ is a unit and $L_v/K_v$ is an unramified quadratic extension of local fields of odd residue characteristic.

*Hint.* For the first part, use $\sigma^2 = 1$. For the second part, reduce modulo the maximal ideal. The map $a \mapsto a + \bar u\,\sigma(a)$ on the residue field is a nonzero linear map over the residue field of $K_v$, so it has a nonzero value.

**Exercise 6.** Let $\Delta = \{1, g\}$ act on $\mathbb Z_\ell^2$ by exchanging the two coordinates. Find an endomorphism $\Psi$ of $\mathbb Z_\ell^2$ with $\Psi + g^{-1}\Psi g = 1$. Then let $\Delta$ act trivially on $\mathbb Z_\ell$. Show that $\Psi + g^{-1} \Psi g = 2\Psi$ for every $\Psi$, and deduce that the smallest $c$ in [the theorem on the Higman operator](/decl/New.Patching.BaseLevel.exists_higman_operator/) for this module is $2$ up to a unit. For which $\ell$ is the module projective over $\mathbb Z_\ell[\Delta]$?

*Hint.* For the first part, take the projection to the first coordinate. For the second part, the module is projective exactly when $2$ is a unit, that is, when $\ell \neq 2$.

**Exercise 7.** In the proof of [the gluing lemma](/decl/New.GaloisRep.exists_attached_of_open_subgroups/), the map $R(g) = \rho_0(g\sigma(g))$ depends on a choice of $\sigma(g) \in K$ with $g\sigma(g) \in N_0$. Show that $R(g)$ does not depend on this choice, if $\rho_0$ kills $K \cap N_0$. Show also that $R$ is a homomorphism.

*Hint.* Two choices differ by an element of $K \cap N_0$ on the right. For the product, use that $K$ is normal: $g\sigma(g)h\sigma(h) = gh \cdot (h^{-1}\sigma(g)h)\sigma(h)$.

## Notes and references

The construction of Galois representations for automorphic forms on unitary groups has a long history. Kottwitz, *On the λ-adic representations associated to some simple Shimura varieties*, Invent. Math. 108 (1992), and Harris and Taylor (2001) treat representations that are discrete series at a place. Shin (2011) and Chenevier and Harris (2013) remove the local condition. Barnet-Lamb, Gee, Geraghty and Taylor (2014) collect the local properties. The use of congruences between forms of different weight, which Section 3 uses in the form of an $\ell$-adic limit, goes back to Serre and to Hida. The approximation of a general form by forms with a type at one place above $\ell$ is in the spirit of Emerton and Paškūnas, *On the density of supercuspidal points of fixed regular weight in local deformation rings and global Hecke algebras*, J. Éc. polytech. Math. 7 (2020), which the source names together with Fintzen and Shin, *Congruences of algebraic automorphic forms and supercuspidal representations*, Camb. J. Math. 9 (2021). The ultrametric Stone-Weierstrass theorem is due to Dieudonné (1944) and Kaplansky, Proc. Amer. Math. Soc. 1 (1950).

Section 4 glues representations of open subgroups that come from base change along many cyclic extensions. This passes from fields that contain $\mathbb Q(\sqrt{-D})$ to a general CM field. Base change for unitary groups is in Arthur and Clozel (1989) and Labesse (2011). The theta lift in place of endoscopic transfer is the method of Harris, Soudry and Taylor (1993), with the idea of Blasius and Rogawski (1993) and Shin (2011) to pass to odd rank.

The source differs from the literature in four ways that a reader should keep in mind. First, it treats only definite unitary groups and the standard hermitian space. Second, "attached" means approximate agreement of characteristic polynomials at most Frobenius data, not equality at almost all places. Third, at a place where the form is spherical, the local clause is that the Hecke polynomial kills a Frobenius element, not that it is the characteristic polynomial. Fourth, there is no Weil-Deligne representation and no local Langlands correspondence. The theorems of [what attached means](/chapter/attached-representations/) explain how much of the classical statement these weaker notions recover.

The results of this chapter are inputs to Volume 12. Lean accepts the statements of this chapter, if the reported checks hold. This chapter does not claim that the argument of the source proves the Riemann hypothesis.

## Summary of Volume 8

Volume 8 builds the geometric and Galois-theoretic objects that the congruences of Volume 12 need. It goes from complex tori to $\ell$-adic Galois representations attached to forms on definite unitary groups.

1. [Complex abelian varieties through theta functions](/chapter/complex-abelian-varieties/) describes complex tori and their line bundles by the theorem of Appell and Humbert, the theta group, the uniformization of the source and abelian schemes.
2. [An integral model without a moduli problem](/chapter/integral-model/) builds an integral model of a PEL Shimura variety from a PEL datum, without a moduli problem. It uses good reduction, theta-null points and a Hecke tower.
3. [The congruence relation](/chapter/congruence-relation/) proves the congruence relation and gives a Galois representation on an eigenquotient of the cohomology.
4. [What attached means](/chapter/attached-representations/) defines agreement at most Frobenius elements, compares "kills" with "is the characteristic polynomial", and turns pseudocharacters into representations.
5. This chapter, [Building the representations](/chapter/building-representations/), builds a representation attached to every eigenform on a definite unitary group, over a CM field with Weil data. It goes from a seed in odd rank with a cuspidal type, through $\ell$-adic limits, base change and gluing, to theta lifts that reach every rank. It ends with local-global compatibility at ramified split places, the Higman operator at auxiliary places and the Selmer modules of the source.

Chapters 1 to 3 are geometry: they produce the cohomology of a Shimura variety and the action of Frobenius on it. Chapters 4 and 5 are Galois theory: they turn that action into representations with the local properties that Volume 12 uses. The main output of the volume is [the theorem on every rank](/decl/New.GaloisRep.sphericalCompat_std/) and the chosen representation [`Isotypic.galRep`](/decl/New.Patching.Isotypic.galRep/). Volume 12 reads Selmer classes from congruences between eigenforms inside these representations. See [the regular families](/chapter/regular-families-plan/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
