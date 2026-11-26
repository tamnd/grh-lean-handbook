---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\eta_1, \eta_2$ be two characters of an algebra $A$ and $a \in A$ with $\eta_1(a) - \eta_2(a) = \delta$. Find $\pi_1, \pi_2 \in A$ with $\eta_e(\pi_{e'}) = \delta$ for $e = e'$ and $0$ otherwise. Glue two $1 \times 1$ matrices $(w_1)$ and $(w_2)$ into one row, as in the example of [The matrices for the block and the characters](/chapter/ribet-elements/#the-matrices-for-the-block-and-the-characters). Compute its values on $\eta_1$ and $\eta_2$.

*Hint.* Take $\pi_1 = a - \eta_2(a)$ and $\pi_2 = \eta_1(a) - a$. The glued row is $\pi_1 w_1 + \pi_2 w_2$. Its values are $\delta\,\eta_1(w_1)$ and $\delta\,\eta_2(w_2)$. The factor $\delta$ plays the part of $C$.

**Exercise 2.** Show by an example that the lemma on coboundaries at $\gamma$ fails without the hypothesis that $y - 1$ is a unit.

*Hint.* Take $G = \mathbb{Z}^2$, the ring $\mathbb{Z}_3$ and $\rho(a, b) = 2^b$ of degree $1$. Let $\gamma = (1, 0)$, so $y = 1$. The coboundary of $m = 1$ is $g \mapsto 2^b - 1$. It is $0$ at $\gamma$ and equal to $1$ at $(0, 1)$.

**Exercise 3.** In the main lemma, let $t = 2$, let $W$ be empty, and let $\#s = 1$ and $\#J = 2$. Write out the bound for $v(c)$. Which terms come from the block, which from the characters and which from the gluing?

*Hint.* The bound is $b_0 + \sum_e b_e + 7v(C)$. The block gives $b_0$. The characters give the $b_e$ and $(\#J + t\#s)v(C) = 4v(C)$. The gluing gives $v(C)$ through $\mu_0$ and $t\#s\,v(C) = 2v(C)$ through $c_0$.

**Exercise 4.** Compare the bound of Exercise 3 with the trivial Ribet element $\mu_0 p^t$ of the smallest case in [Ribet's method for tied rows](/chapter/ribet-elements/#ribets-method-for-tied-rows). When is the main lemma better?

*Hint.* The trivial element has valuation $t\,v(p) + v(\mu_0)$. In the application $p = \ell^\nu$ with $\nu$ large. The numbers $b_0$, $b_e$ and $v(C)$ do not grow with $\nu$.

**Exercise 5.** Let $H \in O[X]$ with $H(1) = 1$, and let $\zeta \in O$ with $\zeta \equiv 1$ modulo $\ell^\nu$. Show that $H(\zeta) \equiv 1$ modulo $\ell^\nu$. Explain why this gives hypothesis 3 of the main lemma in [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations).

*Hint.* Write $H(X) - H(1) = (X - 1)Q(X)$ with $Q \in O[X]$. The element $\varphi_j$ acts on $O(-e)$ by a power of the cyclotomic character, which is $1$ modulo $\ell^\nu$.

The exercises use only the statements of this chapter.

## Notes and references

The method goes back to Ribet, who built an unramified extension from a congruence between an Eisenstein series and a cusp form (K. Ribet, *A modular construction of unramified $p$-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976), Section 4). Bellaïche and Chenevier develop pseudocharacters and the lattices that Ribet's lemma uses for representations of higher rank (J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*, Astérisque 324 (2009), Chapter 1). Amitsur's theorem on characteristic polynomials of sums of matrices is in S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear Algebra 8 (1980). Urban uses Fitting ideals and a lattice construction of this kind for $\mathrm{GSp}_4$ (E. Urban, *Selmer groups and the Eisenstein-Klingen ideal*, Duke Math. J. 106 (2001)). The module notes of the source also name Dasgupta, Kakde, Silliman and Wang (2023) for the case of $\mathrm{GL}_2$ with residually indistinguishable characters. This chapter does not compare the statements of the source with any of these texts.

The volume plan and the research notes have errors for this chapter. The plan of the volume lists only RibetMethod, FittingBlock and RibetLemma for this chapter. By the prefix rule of `volume.yaml` the chapter also owns RibetMatrices and RibetElement. Research note f places RibetElement in a later chapter, and it misnames the authors of the 2023 work. It also describes Amitsur's theorem as a statement on traces of products. The Lean statement is about the characteristic polynomials of block matrices over a spanning set.

Two files of this chapter import files of later chapters. FittingBlock imports `New/Congruences/LocalLoss/Basic`, which belongs to [The main summands of the attached Galois representations](/chapter/main-summands/). RibetElement imports `New/Congruences/FirstOrder/TraceRelations`, which belongs to [From a congruence to a Selmer class](/chapter/denominator-bound/). The chapter states the results it uses from them where it uses them. It does not prove them, and it gives in each place the reason for the import. The volume order puts these chapters later because they need the main summands and the full denominator budget.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
