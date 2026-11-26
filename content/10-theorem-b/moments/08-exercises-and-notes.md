---
title: Exercises and notes
lean:
  - New/Spanning/Unfolding/Moments.lean
  - New/Spanning/Unfolding/MomentBounds.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $H = \mathbb{Z}/m\mathbb{Z}$ and let $x = \frac{1}{m}\sum_s\chi(s)s$ for a character $\chi$ of $H$. Show that $x$ is a central idempotent of $\mathbb{C}[H]$, and check [the lemma on the $\ell^2$ norm](/decl/New.Filling.sum_norm_sq_coeff_of_isCentralProj/) for $x$ and for $1 - x$.

*Hint.* $x\cdot x = x$ by the orthogonality of characters. $\sum_s|x(s)|^2 = 1/m = x(1)$, and $\sum_s|(1 - x)(s)|^2 = 1 - 1/m$.

**Exercise 2.** In [the theorem on one prime](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le/), replace the hypothesis $\operatorname{Re}x(1) \leq b^{-8}/2$ by $\operatorname{Re}x(1) \leq \eta$. Which bound does the same proof give? For which $\eta$ is the bound still at most $2b^{-4}D_X$?

*Hint.* Cauchy-Schwarz gives $\sqrt{2\eta}$ in place of $b^{-4}$. The bound is $(\sqrt{2\eta} + b^{-4})D_X$, which is at most $2b^{-4}D_X$ if $\eta \leq b^{-8}/2$.

**Exercise 3.** Let $G$ be a finite group, $U \leq G$ a subgroup and $\psi$ a character of $U$ of degree $1$, extended by $0$ to $G$. Let $\psi^\natural$ be its mean over conjugates. Show that $\#G\,\psi^\natural = \#U\,\chi_{\mathrm{ind}}$, where $\chi_{\mathrm{ind}}$ is the character of the induced representation. Deduce that $\sum_s|\psi^\natural(s)|^2 = (\#U^2/\#G)\sum_\pi m_\pi^2$, with $m_\pi$ the multiplicity of $\pi$ in the induced representation. What does [the theorem on the induced character](/decl/New.Filling.sum_norm_reducedCharMean_sq_le/) say about these multiplicities?

*Hint.* Use the Frobenius formula for $\chi_{\mathrm{ind}}$ and the orthogonality of irreducible characters. The bound says that $\sum_\pi m_\pi^2 \leq 2\#G/\#U^2$, while $\sum_\pi m_\pi\dim\pi = \#G/\#U$.

**Exercise 4.** Show that the constant $9$ in [the second moment of the blocks](/decl/New.Filling.sum_secondMoment_le/) comes from the constants $4$ (open elements) and $1$ (elements that are not open). Find the constant if the open elements give $(1 + \alpha x)\tau$ and the rest gives $\beta x$ times the mass, with $x \leq 1/10$.

*Hint.* Solve $m \leq (1 + \alpha x)C + \beta xm$. Then $m \leq C(1 + \alpha x)/(1 - \beta x)$, and $(1 + \alpha x)/(1 - \beta x) \leq 1 + (\alpha + \beta)x/(1 - \beta x)$.

**Exercise 5.** In [the lemma on the fixer of all places](/decl/New.Filling.secondMoment_fixer_univ_le/), the scalar cosets carry at most $2M^f\mathcal{D}_{\mathrm{id}}$. Compare this with the size of $\tau_f = b^{-6kf}\mathcal{D}_{\mathrm{main}}$, using (1.1). Why is the bound on the scalar cosets crude but sufficient?

*Hint.* By (1.1), $\mathcal{D}_{\mathrm{id}} \leq b^{-11kf}\mathcal{D}_{\mathrm{main}}$, and $M^f \leq b^{23f}$. So the scalar cosets give at most $2b^{23f - 11kf}\mathcal{D}_{\mathrm{main}}$, far below $\tau_f$ as $k \geq 1000$.

**Exercise 6.** Show that the proof of [the theorem on the induced character](/decl/New.Filling.sum_norm_reducedCharMean_sq_le/) gives $\sum_s|\psi_U^\natural(s)|^2 \leq 1 + 2^{-n}/\mathrm{vol}(K)$. Which result of [the section on masses](/chapter/finite-densities/#masses-at-the-standard-level) turns this into the constant $2$, and where does it use that the places of $T$ are chosen places or their conjugates?

*Hint.* Divide the bound on the mass integral by $\mathrm{vol}(K)^2\mathrm{vol}(K(M))$. The result is [the lower bound for the volume](/decl/New.Floors.IntegralPlace.IsLargeLatticeData.inv_two_pow_le_groupMeasure/). The places of $T$ then have large norm, so the non-units have small volume.

## Notes and references

The model of this chapter is the Petersson formula for the Fourier coefficients of Poincaré series in rank one. In this formula the inner product of two Poincaré series is a diagonal term plus a sum of Kloosterman sums weighted by Bessel functions; see H. Iwaniec, *Topics in Classical Automorphic Forms*, Graduate Studies in Mathematics 17 (1997), Chapter 3. Here the diagonal term is the operator $r_\psi$, the Kloosterman sums are the sums over the terms of a block, and the weights are the amplitudes.

The source names three works as related, with no theorem numbers: J. Herman, on beyond endoscopy for the Rankin-Selberg L-function (2011); H. Iwaniec and X. Li, on the orthogonality of Hecke eigenvalues (2007); and P. Michel, D. Ramakrishnan and L. Yang, on Bessel periods on $\mathrm{U}(2,1)\times\mathrm{U}(1,1)$ (2023). This chapter has not compared them with the source, and it does not use them.

The character theory of finite groups (central idempotents, induced characters and the Frobenius formula) is in J.-P. Serre, *Linear Representations of Finite Groups*, Graduate Texts in Mathematics 42 (1977), Sections 2.6 and 7.2. The bound on the induced character in this chapter does not use the representation theory of $\mathrm{GL}_r(\mathbb{F}_q)$. It goes through the finite places and the mass integral of [the chapter on densities at the finite places](/chapter/finite-densities/).

The method of the maximal family of fixed vectors and the lemma on singular minors follow the source. The source proves the three exchanges of a sum and an integral of [the section on the induced character](/chapter/moments/#the-induced-character) with no appeal to Fubini's theorem for infinite sums: each exchange is a finite sum, or a sum of nonnegative functions in $[0, \infty]$. The constants $b^{-12}$, $b^{-4}$, $5b^{-4}$ and $9b^{-4}$ are those of Lean. The statements in this chapter are those of Lean. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument proves Theorem B in the sense of a refereed proof, and it does not claim that the Generalized Riemann Hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
