---
title: The chain of constructions
lean:
  - Lib/GaloisRep/Main/AllRanks.lean
  - Lib/General/NumberTheory/FrobeniusOrbits.lean
decls:
  - New.isSplit_of_q_prime
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chain of constructions

This chapter builds the Galois representations that the argument attaches to automorphic forms on definite unitary groups. The previous chapter, [what attached means](/chapter/attached-representations/), fixed the meaning of the words. A continuous representation $r : \operatorname{Gal}(\Omega/E) \to \mathrm{GL}_n(\bar{\mathbb Q}_\ell)$ is *attached* to a family of Hecke polynomials $P_w$ if its trace form is non-degenerate and, for each $\varepsilon > 0$, the characteristic polynomial $\det(X - r(s))$ is within $\varepsilon$ of $\iota_\ell(P_w)$, coefficient by coefficient, for most Frobenius elements $s$ at places $w$. The statement $\mathrm{SphericalCompat}$ of that chapter asks two things of every eigenform $f$: some representation is attached to its Hecke polynomials, and every attached representation satisfies the local conditions at each place where $f$ is spherical. This chapter explains how the source proves that statement in every positive rank. The result is [the theorem on every rank](/decl/New.GaloisRep.sphericalCompat_std/) in Section 5.

### Where the result is used

The argument of the source has three main theorems, A, B and C, and one input from Galois cohomology (see [the plan](/chapter/theorem-and-plan/)). The Galois representations of this chapter enter in Volume 12, [the regular families](/chapter/regular-families-plan/). There a congruence between eigenforms gives a Selmer class, and the Selmer class lives in a Galois representation attached to an eigenform. The source uses the theorem on every rank in three files of Volume 12: the file of attached representations, the file that reads rows from eigensystems, and the file of Hecke strings at first order. The local result at split places of Section 6 is used through the labels of Volume 12, and the Higman operator of Section 6 is used at the auxiliary primes. Volume 12 also uses the Selmer modules of Section 6.

### The textbook form

The classical theorem is due to many authors. Let $E$ be a CM field and let $\Pi$ be a regular algebraic, conjugate self-dual, cuspidal automorphic representation of $\mathrm{GL}_n(\mathbb A_E)$. Then there is a continuous semisimple representation $r_\Pi : \operatorname{Gal}(\bar E/E) \to \mathrm{GL}_n(\bar{\mathbb Q}_\ell)$ such that, at each place $w$ not above $\ell$ where $\Pi$ is unramified, $r_\Pi$ is unramified and the characteristic polynomial of a Frobenius element is the Satake polynomial of $\Pi_w$. See Chenevier and Harris, *Construction of automorphic Galois representations II*, Camb. J. Math. 1 (2013), Theorem 3.2.3, and Shin, *Galois representations arising from some compact Shimura varieties*, Ann. of Math. 173 (2011). Barnet-Lamb, Gee, Geraghty and Taylor, *Potential automorphy and change of weight*, Ann. of Math. 179 (2014), Theorem 2.1.1, collect the local properties, including the Hodge-Tate weights and the crystalline property above $\ell$.

The source proves a weaker statement, for forms on the definite unitary group $U(n)$ itself and not for $\mathrm{GL}_n$. It does not pass through base change to $\mathrm{GL}_n$. It replaces the characteristic polynomial by two weaker conditions. Away from a small set, the characteristic polynomial is close to the Hecke polynomial in the $\ell$-adic sense. At a place where the form is spherical, the Hecke polynomial *kills* a geometric Frobenius element, which means that $\iota_\ell(P_w)(r(s)) = 0$. A polynomial that kills a matrix is a multiple of its minimal polynomial. It need not be its characteristic polynomial. The source builds no Weil-Deligne representation and uses no local Langlands correspondence.

### The model case: rank one

In rank one the theorem is class field theory. A form on $U(1)$ of weight $\kappa$ is a function on the finite adelic group $U(1)(\mathbb A_f) = \{x \in \mathbb A_{E,f}^\times : x\bar x = 1\}$ that transforms under $U(1)(E)$ through the algebraic character of weight $\kappa$. An eigenform is a character $\mu$ of $U(1)(\mathbb A)/U(1)(E)$. The map $x \mapsto x/\bar x$ sends $\mathbb A_E^\times$ onto the norm one ideles, by Hilbert 90, so $\mu(x/\bar x)$ is a Hecke character of $E$. After a twist by a fixed algebraic character, it becomes an algebraic Hecke character $\theta$. Weil's construction gives the $\ell$-adic avatar of $\theta$, a continuous character $\psi : \operatorname{Gal}(\Omega/E) \to \bar{\mathbb Q}_\ell^\times$ with $\psi(\mathrm{Frob}_w) = \iota_\ell(\theta(\varpi_w))$ at almost all $w$. In rank one, "kills" and "is the characteristic polynomial" mean the same thing, since $X - a$ kills the scalar $b$ only if $a = b$.

Two features of the model case come back in every rank. First, the extra characters that the theta lift of Section 5 adds to a Hecke polynomial are of this kind: they are the values $\theta(\varpi_w)$ of algebraic Hecke characters $x \mapsto \mu(x/\bar x)\,\upsilon(x)^{-k}\,|x|^{j - k/2}$, where $\upsilon$ is a fixed splitting character. Second, the comparison is always made at split places $w \neq \bar w$, because only there does the local group become $\mathrm{GL}_n(E_w)$.

### The five steps

The proof is a chain of five constructions. Each one feeds the next.

1. *The seed* (Section 2). Let $n$ be odd. Let $f$ transform at one split place by a cuspidal type, and let its weight have free jumps at one embedding. Then the cohomology of a PEL Shimura variety of signature $(1, n-1)$, from [the congruence relation](/chapter/congruence-relation/), gives a large representation. Its Frobenius elements are killed by the Hecke polynomials. A lemma on killing polynomials cuts it down to rank $n$ and proves that the Hecke polynomials are its characteristic polynomials. This is the only place in the chain where equality of characteristic polynomials is proved.
2. *Limits* (Section 3). Every form of odd rank is an $\ell$-adic uniform limit of forms of the kind in step 1. The traces of their representations converge, and a pseudorepresentation argument gives a representation of the limit. This works over a field that contains $\mathbb Q(\sqrt{-D})$ with $D \equiv 3 \bmod 4$, when $\ell$ and the place in question lie over split primes of $\mathbb Q(\sqrt{-D})$.
3. *Odd rank* (Section 4). A quadratic base change moves the form to a field where step 2 applies. Many such steps give representations of open subgroups of the Galois group. They are glued to one representation of the whole group.
4. *The theta lift* (Section 5). A form of rank $n$ lifts to a form of rank $n + t$ with $t > n$, and its Hecke polynomials gain $t$ factors $X - \theta_l(\varpi_w)$ from characters.
5. *Every rank* (Section 5). With $t = n + 1$ the rank $n + t = 2n + 1$ is odd. Two lifts along two characters with disjoint values give two representations of rank $2n + 1$. Each contains the wanted representation plus $n + 1$ characters, at the level of traces. The characters are cancelled.

Section 6 treats local-global compatibility at split places where the form is not spherical, and the Higman operator and Selmer modules of the source. Section 7 has the exercises, the notes and a summary of Volume 8.

### Standing hypotheses

The field $E$ is a CM field inside a fixed algebraic closure $\Omega$ of $\mathbb Q$. The prime $\ell$ and an isomorphism $\iota_\ell : \mathbb C \to \bar{\mathbb Q}_\ell$ are fixed. Two conditions on $E$ recur. The first is that $E$ contains a primitive root of unity of order $7! = 5040$. The second is the existence of Weil data: an element $\jmath \in E$ with $\bar\jmath = -\jmath$ and positive imaginary part under the CM type, a finite idele $\alpha$ such that $\jmath\alpha\bar\alpha$ has, at each finite place, the order of minus the different, an integrality condition on $(1 - \jmath^{-1})/2$, and a splitting character $\upsilon$. The Weil data contain the root of unity condition. Odd rank needs only the root of unity. Every rank needs the Weil data, because the theta lift is built from them.

The filter "most Frobenii" of [the previous chapter](/chapter/attached-representations/) runs over data $(w, A, s)$ with $w$ a finite place of prime norm $q_w$. The next lemma explains why the root of unity makes these places split.

**Lemma (Places of prime norm split).** Let $E$ be a CM field that contains a primitive root of unity of order $5040$. Let $w$ be a finite place of $E$ whose residue field has a prime number $q_w$ of elements. Then $w$ is split, that is, $\bar w \neq w$.

Lean: `New.isSplit_of_q_prime` (Lib/General/NumberTheory/FrobeniusOrbits.lean).

*Proof.* Suppose that $\bar w = w$. The field $E$ contains $i$, since $4$ divides $5040$. The source shows that then $q_w = r^2$ for an integer $r$ with $r \equiv 3 \bmod 4$ (Lean: `New.HasPrimitiveRoot5040.exists_sq_eq_q_of_inert`). A square of an integer $r \geq 3$ is not prime. This contradicts the hypothesis. $\square$

So, at most Frobenius data, the local group is $\mathrm{GL}_n(E_w)$, the Hecke polynomial $P_w$ is defined by the Satake parameters there, and the comparison with $\det(X - r(s))$ makes sense. The Hecke polynomial at a split place $w$ of a form fixed by $\mathrm{GL}_n(\mathcal O_w)$, with eigenvalues $t_j$ of the operators $T_{w,j}$, is

$$P_w(X) = \sum_{j=0}^{n} (-1)^j q_w^{j(j-1)/2}\, t_j\, X^{n-j}.$$

**Remark (Formalization).** The theorem on every rank of the source has the hypotheses `[WeilData E] [CMType E] [Nonempty n]` and holds for the standard definite hermitian space of rank $|n|$ only. It says nothing about inner forms that are not definite, or about $\mathrm{GL}_n$. The source states in its docstring that it is a weak analogue of the theorems of Shin, Chenevier and Harris, and Barnet-Lamb, Gee, Geraghty and Taylor. This chapter follows that description.
