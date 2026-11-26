---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\Lambda$ be diagonal in a basis $b_1, \dots, b_m$ with entries $\mu_k$, and let $\mathrm{ellVal}(\mu_k) \leq B$ for every $k$. Show that $\|\det \Lambda\| \geq \ell^{-mB}$. Compare with [the bound for denominators](/chapter/denominator-bound/#the-bound-for-denominators).

*Hint.* $\|\mu_k\| = \ell^{-\mathrm{ellVal}(\mu_k)}$ when $\mu_k \neq 0$, and the norm is multiplicative.

**Exercise 2.** Let $l_{p,k}$ be elements of $\overline{\mathbb{Q}}_\ell$ for $p, k \leq 2$. Find $d_1, d_2$ with $\|d_p\| \leq 1$ such that $\|l_{1,k} d_1 + l_{2,k} d_2\| \geq \|l_{k,k}\|$ for $k = 1, 2$.

*Hint.* Choose $d$ in the integral elements with residues outside the finitely many residue classes that make a leading term cancel. The residue field is infinite.

**Exercise 3.** Let $x$ be a system whose normalised representation is $\vartheta^{-1}_\ell R \oplus \bigoplus_{e<t'} \chi^e$. Show that $x$ is a weak lift. Give an example of a weak lift of rank $2$ that is not of this form.

*Hint.* The summand $\chi^0 = 1$ gives the eigenvalue $1$ at every $g$. For the example, take a representation on which every $g$ acts unipotently.

**Exercise 4.** Let $\delta_0 = \prod_k (a_k - \delta_k)$ with $a_k \neq 0$, as in [the operator at one base system](/chapter/denominator-bound/#the-operator-at-one-base-system). Show that $\delta_0(x) = \prod_k a_k$ at every weak lift $x$, where $\delta_k(x) = \det(1 - N_x(\mathrm{elt}(k)))$.

*Hint.* At a weak lift every $\det(1 - N_x(g))$ is $0$.

**Exercise 5.** Check that $\mathrm{liftValuationBound}(\ell, O, e'_\ell, e'_\ell) + v \leq \#r\, \beta_\ell$ follows from $1 \leq \#r \leq r$ and $t' \leq t$, by expanding both sides with the definitions of [the constants](/chapter/denominator-bound/#the-constants).

*Hint.* Use $\#r \geq 1$ for the terms that carry no factor $\#r$ on the left.

**Exercise 6.** Let $Z$ be stable under a family of commuting self-adjoint operators, and let $T$ be one of them. Show that $Z^\perp$ and $(Z^\perp \cap \ker T)^\perp$ are stable under the family.

*Hint.* A self-adjoint operator that keeps $Z$ keeps $Z^\perp$. An operator that commutes with $T$ keeps $\ker T$.

The exercises use only the statements of this chapter.

## Notes and references

Ribet's method builds a Galois cohomology class from a congruence between an Eisenstein series and a cusp form (K. Ribet, *A modular construction of unramified $p$-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976)). The source files name related work. `DenominatorBound.lean` names Dasgupta, Kakde, Silliman and Wang, *The residually indistinguishable case of Ribet's method for GL2* (2023), Dotto and Thorne, *Modularity of residually reducible representations of rank 2* (2026), and Martin and Wakatsuki, *Mass formulas and Eisenstein congruences in higher rank* (2024). `TraceRelations.lean` names Sweeting, *Bloch-Kato conjecture for four-dimensional symplectic representations* (2025), Chang and Diamond, *Extensions of rank one $(\varphi,\Gamma)$-modules* (2011), and T. Liu, *Torsion $p$-adic Galois representations and a conjecture of Fontaine* (2007). This chapter does not compare the statements of the source with these texts.

The chapter has three layers. Sections 2 to 5 give the constants and the inputs of Ribet's element: the trace ideal of the twisted lifts, the block diagonal lattices, the bound for cocycles, the local defects at the places above $p_0 p_1$, and the tame relations. Sections 6 and 7 run the method at one base system and identify the false lifts. Section 8 joins the operators for the basis vectors into one operator and bounds its determinant with the clearing bound. [The chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) uses the last theorem, `New.Selmer.denominatorLe_clearingBound`.

The research notes and the volume plan have errors for this chapter.

- Note f of the volume plan places `RibetElement.lean` in this chapter. `volume.yaml` places it in [Ribet elements](/chapter/ribet-elements/), chapter 2 of this volume.
- The register lists F-094, the negligibility of the error $e_\ell$, as open. [The denominator budget](/chapter/regular-families-plan/#the-denominator-budget), chapter 1, proves `New.Selmer.isNegligible_denominatorError` with the exponent $4000$.

The files of this chapter import files of chapters 2, 3, 4, 5 and 9 of this volume ([the map of the files](/chapter/regular-families-plan/#the-map-of-the-files)). No file of this chapter imports a file that `volume.yaml` places in a later chapter of Volume 12. Results of [the local loss](/chapter/local-loss/), chapter 9, are used with one line and a link.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
