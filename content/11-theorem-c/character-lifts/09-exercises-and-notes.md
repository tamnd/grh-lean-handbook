---
title: Exercises and notes
lean:
  - New/OneLift/TestedForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 8.

**Exercise 1.** Let $O$ be a descent pair with $r = 1$ and $N = 3$, so $t = 2$. Let $w$ be a split place of norm $q = 2$ off the level. Write the $q$-Pochhammer factor $(\nu T; 2)_2$ as a product of two linear factors. Find its zeros, and check that $x_w = (2\nu)^{-1}$ is one of them.

*Hint.* $(\nu T; 2)_2 = (1 - \nu T)(1 - 2\nu T)$. Use Step 3 of the root lemma in Section 5.

**Exercise 2.** In the root lemma, replace the hypothesis on $\nu$ by the Lean convention $0^{-1} = 0$ and suppose $\nu = 0$. Compute $x_w$ and the value $p_w(x_w)$. Explain why the conclusion $H_w(x_w)\,y = 0$ can fail in this case.

*Hint.* Read the formalization remark of Section 5. The first factor at $T = 0$ is $1$.

**Exercise 3.** Let $r = 1$ and $N = 2$, with one chosen place of residue field $\mathbb{F}_3$ and no twist places. List the matrices $Y$ of size $2 \times 1$ over $\mathbb{F}_3$ of full column rank. For $Y = (1, 1)^{\mathsf T}$, give an invertible $2 \times 2$ matrix $A$ whose column at the index of `O.incl` is $Y$. Is $A$ unique?

*Hint.* There are $3^2 - 1 = 8$ such columns. The other column of $A$ can be any vector outside the line of $Y$.

**Exercise 4.** In the setting of Exercise 3, compute `pointFormDatum Y e X` for every $X$. Then use the lemma on moving the datum to describe the finite datum of the descent of a point form as an indicator function.

*Hint.* With no twist places the product over $Q$ is empty, so it is $1$.

**Exercise 5.** Let $H$ be an operator on a finite dimensional inner product space with an adjoint $A'$ that commutes with $H$. Show that $\|Hu\| = \|A'u\|$ for every $u$, and deduce that $(\mathrm{range}\,H)^\perp = \ker H$. Compare your proof with the lemma on range and kernel in Section 8.

*Hint.* $\|Hu\|^2 = \langle u, A'Hu\rangle = \langle u, HA'u\rangle = \|A'u\|^2$.

**Exercise 6.** Show by an example in $\mathbb{C}^2$ that the projection bound of Section 8 fails without the hypothesis on false lifts. Take a subspace $Z$, a decomposition $\mathbb{C}^2 = Z \oplus Z'$ with $Z'$ not orthogonal to $Z$, and a second Hermitian form for which $Z$ and $Z'$ are orthogonal. Find a vector $y$ whose orthogonal projection to $Z$ has a larger norm for the second form than $y$.

*Hint.* The proof of the theorem uses that the complement $\ker e_0 + \mathrm{range}\,A$ is orthogonal to $Z$ at every $\sigma$ at once. In the example it is orthogonal at only one of the two forms.

**Exercise 7.** For $W$ of rank $r = 1$, the idempotent `tupleIdem r (X − 1)` is the mean over $G_M = \prod_{w \in M} k_w^\times$. Show that its image in `O.FormV` is the space of forms $\varphi$ with $g\varphi = \varphi$ for all $g \in G_M$. Describe this condition in terms of right translations and the characters $\psi_w$.

*Hint.* The mean $e$ satisfies $ge = e$ for each $g$, and $e\varphi = \varphi$ if $\varphi$ is invariant.

## Notes and references

**Inner product formulas.** Section 6 computes the norm of the lift of a character as an $L$-value by a direct computation, with no use of Eisenstein series. The general form of this computation is the Rallis inner product formula: S. Rallis, *L-functions and the oscillator representation*, Lecture Notes in Math. 1245, Springer (1987). The relation of theta integrals to Eisenstein series is the Siegel-Weil formula, of which a standard reference is S. Kudla and S. Rallis, *On the Weil-Siegel formula*, J. reine angew. Math. 387 (1988). The handbook does not use these formulas. The source proves only the case it needs, for a datum that is sharp at every place, in [the Rallis inner product](/chapter/rallis-inner-product/) of Volume 6 and in Section 6.

**Theta lifts of characters.** Lifts from $U(1)$ to unitary groups of larger rank are classical. For the local and global behaviour of such lifts for unitary groups, a standard reference is M. Harris, S. Kudla and W. J. Sweet, *Theta dichotomy for unitary groups*, J. Amer. Math. Soc. 9 (1996). The source does not use their results. It needs only the explicit kernel of Section 3, the descent of Section 4 and the Hecke polynomials of Section 5.

**Hecke polynomials.** The shape of the Hecke polynomial of a lift, a product of $q$-Pochhammer factors from the trivial representation and a rescaled polynomial of the source, is the unramified theta correspondence at a split place. Volume 5 proves it for the vacuum datum, and the previous chapter transfers it to theta lifts. Section 5 extracts from it the single root $x_w$, which is all that the definition of false lifts needs.

**Galois conjugates.** The law of Section 7 follows the method of algebraicity results for theta lifts: write the lift through a Schwartz function whose jets have algebraic coefficients up to a period, and let $\sigma$ act on the Schwartz function. In the source the period is a power of $t$ with $|t| = \Omega^{-1/2}$, and the remaining constant $l$ is not computed.

**Tested forms.** The point forms, the false lifts and the projection bound of Section 8 are specific to the source. They are tools for the congruences of [Hecke values of character lifts](/chapter/hecke-values/), [false lifts](/chapter/false-lifts/) and Volume 12. The key fact is that the projection to the kernel of the descent is controlled at every conjugate pairing, because the complement is orthogonal at every $\sigma$ at once.

**Errors in the plan.** The plan of Volume 11 in [the plan of Theorem C](/chapter/theorem-c-plan/) assigns the point forms and the false lifts to a later chapter, and the notes of the second chapter assign the files `CharacterLiftNorm.lean` and `TestedForms.lean` to other chapters. The file `volume.yaml` puts both files in this chapter, which follows it.
