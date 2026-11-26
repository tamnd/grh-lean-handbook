---
title: Exercises, notes and a summary of the volume
lean:
  - Lib/SiegelWeil/RallisInner/Doubling.lean
  - Lib/SiegelWeil/Tower/FiniteTateIntegral.lean
  - Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 6.

**Exercise 1.** Let $S$ be a hermitian space and $\phi$ a linear map from $S^-$ to $S$. Show that the graph $\{(\phi(x), x)\}$ is isotropic in $S \oplus S^-$ exactly when $\phi$ is an isometry. Deduce that the graph of $\phi$ is a Lagrangian when $\phi$ is an isometry.

*Hint.* The form of $S \oplus S^-$ at two points of the graph is $\langle \phi(x), \phi(y) \rangle - \langle x, y \rangle$. For the second part, count dimensions.

**Exercise 2.** Let $M > 2n$ and let $q \ge 2$. Show that the number of lines in $\mathbb{F}_q^n$ is at most $q^n/(q - 1)$, and that $q^n q^{-M/2} \le q^{-1/2}$. Deduce the bound $s_w \le N_w / ((q_w - 1)\sqrt{q_w})$ of Section 4, where $N_w$ is the number of neighbour classes at $w$.

*Hint.* The number of lines is $(q^n - 1)/(q - 1)$. As $M$ is an integer, $M > 2n$ gives $M \ge 2n + 1$.

**Exercise 3.** Write $L_*(2)$ as a product of values of $L^S(\cdot, \nu)$ and of powers of the $q_w$. Check the result against the recursion $L_*(2) = L^\sharp(2)^2 L_*(1)$.

*Hint.* By definition $L_*(2) = (\prod_{w \in S} q_w)^4 |L^S(1, \nu)|^2 |L^S(2, \nu)|^2$. On the other side, $L^\sharp(2)^2 = |L^S(2, \nu)|^2 \prod_{w \in S} q_w^3$.

**Exercise 4.** Derive the downward recursion $L_*(-z) = L^\sharp(z + 1)^2 L_*(-z - 1)$ from the upward recursion and the rule $L_*(-e) = L_*(e)^{-1}$.

*Hint.* Take inverses in $L_*(z + 1) = L^\sharp(z + 1)^2 L_*(z)$ and use $L^\sharp(z + 1) > 0$.

**Exercise 5.** In the setting of the functional equation of Section 5, let $k \ge 1$. Show that $\Lambda(0) \neq 0$, and express $|\Lambda(0)|$ by $L^\sharp(1)$ and $C(1)$.

*Hint.* Take $z = 1$. The product over $S$ on the left side is $\prod_{w \in S} q_w^{-1/2}$.

**Exercise 6.** Let $c \in E$. Show that the mean of $\psi(\operatorname{tr}(c\, q))$ over $q \in \mathbb{A}/E$ is $1$ if $c = 0$ and $0$ otherwise. Explain why only isotropic vectors give terms in the constant term of Section 5.

*Hint.* For $c \neq 0$ the character $q \mapsto \psi(\operatorname{tr}(cq))$ of the compact group $\mathbb{A}/E$ is not trivial. Take $c = \langle x, x \rangle$.

**Exercise 7.** Let $p = 1$ in Section 6, and let $\gamma$ be an idele. Suppose that $T[\gamma]$ is integral at $S \cup \bar S$. Replace $\gamma$ by $\varpi_w \gamma$ for a uniformizer $\varpi_w$ at a place $w \in S$. Show that the dual index increases.

*Hint.* The bracket is multiplied by $\varpi_w \bar\varpi_w$. As $T[\gamma]$ is integral at $w$, its inverse has valuation at most $0$ there, and the new inverse has a pole at $w$ of larger order.

## Notes and references

**Doubling and the inner product formula.** The inner product formula is due to Rallis. The source cites S. Rallis, *L-functions and the oscillator representation*, Lecture Notes in Math. 1245, Springer (1987), and J.-S. Li, J. reine angew. Math. 428 (1992). For the unfolding in the unitary case it cites Y. Liu (2011), Proposition 2.3, and Eischen, Harris, Li and Skinner, Section 4.1.4. The source treats only Weil's range $m > 2n$, with forms that are rapidly decreasing, and it removes the boundary orbits by the clean condition on the datum.

**Injectivity.** For the injectivity of theta lifts in a large rank the source cites S. Rallis, *Injectivity properties of liftings associated to Weil representations*, Compositio Math. 52 (1984), and J.-S. Li, *Non-vanishing theorems for the cohomology of certain arithmetic quotients*, J. reine angew. Math. 428 (1992). The source proves its version without $L$-functions: the Rallis series is close to the identity.

**Lattices.** The count of lattices by neighbours is the method of Kneser. The source cites M. Greenberg and J. Voight, *Lattice methods for algebraic modular forms on classical groups* (2014), Section 5.

**$L$-values from $U(1)$.** For critical Hecke $L$-values of CM fields as norms of theta lifts from $U(1)$, the source cites G. Shimura, Ann. of Math. 102 (1975), T. Yang, J. reine angew. Math. 485 (1997), Harris, Li and Skinner (2005), and Finis, Ann. of Math. 163 (2006).

**The tower.** For the tower property the source cites S. Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984), Theorem I.1.1, and C. Wu, *Irreducibility of theta lifting for unitary groups*, J. Number Theory 133 (2013), Proposition 3.1. For Tate's integral it cites J. Tate's thesis (1950), Section 2.5 and the Main Theorem 4.4.1.

**Singular forms.** For the vanishing criterion the source cites E. Freitag, *Singular Modular Forms and Theta Relations*, Lecture Notes in Math. 1487, Springer (1991), and J.-S. Li, *Automorphic forms with degenerate Fourier coefficients*, Amer. J. Math. 119 (1997).

**What differs.** The source does not use Eisenstein series, the regularized Siegel-Weil formula or the local doubling zeta integrals. It does not identify the unramified part with an $L$-function of a cuspidal representation, except in rank one. In the tower, the lifted object is a character and the isotropic orbit gives a Tate integral; the source treats only real arguments and absolute values. The vanishing criterion for singular forms is adelic and not holomorphic, and its singularity is a shear invariance.

## A summary of Volume 6

Volume 6 builds the theta correspondence for unitary groups over a CM field and the formulas that the plan of Theorem C takes from it. It has six chapters.

1. [The Weil representation from a vacuum](/chapter/weil-representation/) builds the Heisenberg group, the Weil representation from a vacuum vector, the cocycle as a Gauss sum, the Fock model at the real places and the mixed models of a split space. It ends with the invariance of the theta functional under the rational points, after Weil.
2. [Local theta in the Fock model](/chapter/local-theta/) treats local theta in the Fock model, and the argument after Howe that the source uses in place of Howe duality.
3. [Theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) treats the growth of theta kernels, definite lifts, the Galois law and the seesaw for periods.
4. [Bessel periods and one step of unfolding](/chapter/bessel-periods/) treats Bessel periods and one step of unfolding.
5. [The Siegel-Weil formula](/chapter/siegel-weil/) proves the Siegel-Weil formula in Weil's range and treats Siegel's mass.
6. This chapter applies the Siegel-Weil formula to a doubled space. It proves the doubling identity and the inner product formula, the injectivity of theta lifts in a large rank through the Rallis series, the constant terms of the tower with their $L$-values, and a vanishing criterion for singular forms.

The chapters form one line. The Weil representation gives the theta functional. The theta functional gives theta kernels and lifts. The Siegel-Weil formula computes the integral of a theta kernel. Doubling turns the Petersson product of two lifts into such an integral. The plan of Theorem C in [Theorem C: the plan](/chapter/theorem-c-plan/) takes from the volume the injectivity of a single theta lift and, through the tower, the products $L_*$ of $L$-values in the identity for the determinant of a chain.

In this chapter the main limits of the source are these: only Weil's range of absolute convergence, rapidly decreasing forms in place of cusp forms, real arguments in the functional equation, and constants that are shown to be nonzero but are not computed.

Status: drafted by a model. No person has checked this chapter against the Lean source.
