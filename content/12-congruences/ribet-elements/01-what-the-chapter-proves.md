---
title: What the chapter proves
lean:
  - New/Congruences/FirstOrder/RibetLemma.lean
  - New/Congruences/FirstOrder/RibetElement.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter constructs one element of a ring of families of polynomials, the *Ribet element*, and it bounds one coefficient of it. The element kills the determinants $\det(1 - u_x(g))$ of a finite family of Galois representations $u_x$, modulo an ideal $\mathcal{J}$ of traces. Its coefficient at the product of all tie variables has a valuation that the chapter bounds by a Selmer length, a local loss and explicit error terms. [The bound for denominators](/chapter/denominator-bound/) uses this element to give the operator for one lift generator. That is Step 4 of [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) in the plan of the volume.

The chapter has two main results. The first is algebraic. It is stated for any group $G$ and any discrete valuation ring $O$, and it does not mention Galois groups. The second applies the first to conjugate self-dual $\ell$-adic representations of the absolute Galois group of the CM field $E$ of the data.

### The algebraic statement

Let $u_x$, for $x$ in a finite set $Y$, be representations $G \to \mathrm{GL}_\sigma(O)$. Let $J$ be a finite, linearly ordered set of variables $X_j$, and let $L$ be an $O$-algebra. Let $S$ be an $O$-algebra of families $Y \to L[X_j : j \in J]$, and let $\mathcal{J}$ be an $S$-module of such families. On a subset $\mathcal{X} \subseteq Y$, the representation $u_x$ is the sum of a block $\rho_x$ and $t$ characters $\xi_0 = 1, \xi_1, \dots, \xi_{t-1}$. For $\omega : G \to O$ with finite support, write
$$u_x(\omega) = \sum_g \omega(g)\,(u_x(g) - 1) .$$
On $\mathcal{X}$ the trivial character $\xi_0$ sees $u_x(\omega)$ as $0$, so $\det u_x(\omega) = 0$ for $x \in \mathcal{X}$.

**Theorem (Ribet's lemma to first order, short form).** Under the hypotheses of the section on the main lemma, there is $c \in O$ and one $f \in S$ with these properties:

1. for every $\omega$, $f \cdot \det u_x(\omega) \in \mathcal{J}$;
2. for $x \in \mathcal{X}$, the polynomial $f(x)$ has no monomial that properly divides $\prod_j X_j$;
3. at one point $\pi \in \mathcal{X}$, the coefficient of $\prod_j X_j$ in $f(\pi)$ is $c$;
4. $v(c) \leq b_0 + \sum_e b_e + t\,(\sum_v v(o_v(1)) + 2\,\#s\, v(C)) + (\#J + 1)\, v(C)$.

Lean: `New.Selmer.exists_isCommonRibetElement_addVal_le` (New/Congruences/FirstOrder/RibetLemma.lean).

Here $b_0$ bounds the length of a module of cocycles of the block with values in $K/O$, $b_e$ bounds a cost for the character $\xi_e$, the $o_v$ are polynomials that kill elements $\delta_v$, $s$ is a finite set of test elements, and $C$ is the cost of telling the characters apart. [The main lemma](/chapter/ribet-elements/#the-main-lemma) states all hypotheses and proves the theorem.

### The Galois statement

**Theorem (Ribet's element for conjugate self-dual representations, short form).** Let $u_x$, $x \in Y$, be conjugate self-dual representations of a fixed type. For $x \in \mathcal{X}$, let $u_x$ have the trace of $\psi \otimes R_x$ plus the powers $\varepsilon^{-e}$, $0 \leq e < t'$, of the cyclotomic character, with $R_x$ a main summand. Let the module $\mathcal{J}$ hold $\ell^\nu$ times the traces and the traces of the tie relations at the new places. Let the Selmer group of $\psi \otimes R_\pi$ with divisible coefficients have length at most $\mathrm{sel} < \infty$. Then there is one Ribet element for all $\det(1 - u_x(g))$, and its coefficient $d$ of $\prod_j X_j$ at $\pi$ satisfies
$$v_\ell(d) + 2\,v_\ell(N) \leq \mathrm{sel} + 2\,t'\,\mathrm{ram} + r' \cdot \mathrm{loc} + e_\ell .$$

Lean: `New.Selmer.ribet_columns` (New/Congruences/FirstOrder/RibetElement.lean).

Here $N$ is the chosen group order of the data, $r'$ is the rank of the main summand, $\mathrm{ram}$ bounds the ramification of the auxiliary twist $\psi$, $\mathrm{loc}$ is the local defect bound at $\ell$, and $e_\ell$ is the denominator error of [the denominator budget](/chapter/regular-families-plan/#the-denominator-budget). [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) states the hypotheses in full.

### The idea in one paragraph

Ribet's method finds an element that acts on one summand of a reducible representation and is zero on the others, and that kills a lattice modulo a congruence ideal. Ribet used it to construct unramified extensions from congruences between Eisenstein series and cusp forms (Ribet, *A modular construction of unramified p-extensions of* $\mathbb{Q}(\mu_p)$, Invent. Math. 34 (1976)). This chapter uses the version that works with traces only. It does not choose a lattice in which the representation is upper triangular. It takes a square matrix $B$ over the group algebra whose rows give relations modulo a two-sided ideal $\mathfrak{a}$ of traces. Then Cayley and Hamilton give a polynomial $P$ with $P(0) = \det B$, such that $P(\rho_0)$ multiplies a left ideal into $\mathfrak{a}$. The trace $f = \operatorname{tr} \rho(\rho_1 P(\rho_0))$ is the Ribet element. On the points of $\mathcal{X}$, $f$ is $\mu_0 \det(\psi B) \prod_e \det(\eta_e B)$, a product of determinants that the chapter bounds by Fitting ideals.

### The sketch of the proof

The proof has five steps. Each step is a section of the chapter.

1. Amitsur's theorem says that characteristic polynomials of a spanned algebra stay integral. Its block form and the Cayley and Hamilton theorem give an adjugate for every square matrix over the algebra ([Amitsur and Cayley-Hamilton](/chapter/ribet-elements/#amitsur-and-cayley-hamilton)).
2. Ribet's polynomial $P$ and the trace ideal give the element for one matrix of tied rows ([Ribet's method for tied rows](/chapter/ribet-elements/#ribets-method-for-tied-rows)).
3. Fitting ideals of modules of functions bound the determinants of rows that come from relations. The bound has three stages, and it ends with a coefficient of $\prod_j X_j$ ([Fitting ideals and the triangle cost](/chapter/ribet-elements/#fitting-ideals-and-the-triangle-cost)).
4. The tie ideal over $O[X_j][G]$ and its tied rows give square matrices with bounded determinant, one for the block and some for the characters ([tied rows](/chapter/ribet-elements/#tied-rows) and [the matrices for the block and the characters](/chapter/ribet-elements/#the-matrices-for-the-block-and-the-characters)).
5. A projector onto the characters glues the matrices into one element, and the valuations add up ([the main lemma](/chapter/ribet-elements/#the-main-lemma)). The Galois statement then chooses a coefficient ring, checks the hypotheses, and adds up the losses ([Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations)).

### What the chapter uses

The chapter uses these results from earlier volumes. It states each of them where it is used and does not prove them again.

- Amitsur's theorem on characteristic polynomials and the adjugate from Cayley and Hamilton, from the linear algebra of [Weyl modules](/chapter/weyl-modules/) in Volume 5.
- Fitting ideals, relative lengths and the modules of forms modulo a power of the uniformizer, from [Fitting ideals](/chapter/fitting-ideals/) in Volume 7.
- Coefficient rings, the normalized length and the valuation $v_\ell$ on $\overline{\mathbb{Q}}_\ell$, also from [Fitting ideals](/chapter/fitting-ideals/).

It also uses definitions from later chapters of this volume. The modules of cocycles that obey the relations of the family come from [the local loss](/chapter/local-loss/). The constants $\beta_\ell$, $e_\ell$ and the bounds for odd classes come from [the bound for denominators](/chapter/denominator-bound/). The chapter states these definitions where it uses them, and it uses only the facts that it states.

### The status of the claim

The chapter explains the proof in the source. It does not claim that the proof is correct. It does not check that the source builds. The constants in the bounds are the constants of the source, and the chapter does not try to make them smaller.
