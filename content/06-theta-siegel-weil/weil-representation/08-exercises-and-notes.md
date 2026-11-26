---
title: Exercises and notes
lean:
  - Lib/Weil/Construction/HeisenbergModel.lean
  - Lib/Weil/MixedModel/ThetaInvariance.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 7.

**Exercise 1.** In the example of a finite group of odd order in Section 2, show that the model of the vacuum is the space of functions $v$ on $W$ with $v(x + l) = \beta(x, l)\, v(x)$ for all $l \in L$. Deduce that the model has dimension $|L|$.

*Hint.* The defining identity reads $v(x) = |L|^{-1} \sum_{l \in L} \beta(l, x)\, v(x + l)$. Check that the right side, as a function of $x$, has the stated law, and use $\beta(-m, x) = \beta(x, m)$.

**Exercise 2.** Show that the elements $\gamma$ of $U(J)$ with $\theta_V \circ \omega(\gamma) = \theta_V$ form a subgroup.

*Hint.* For the inverse, apply the identity for $\gamma$ to the vector $\omega(\gamma^{-1}) f$.

**Exercise 3.** Check the three Gram conditions of the diagonal splitting of $V \oplus V^-$: the frames $k$ and $l$ are isotropic, and $l^*(J \oplus -J)k = 1$.

*Hint.* Use that $J$ and $J^{-1}$ are hermitian.

**Exercise 4.** In the proof of the invariance on a split space, let $a \in \mathrm{GL}_p(\mathbb{A})$ be adelic and not rational. Find the place where the argument fails, and compute the factor that replaces $1$.

*Hint.* The factor is $\chi_{\mathbb{A}}(\det a)^{-1}$. It is $1$ for $\det a \in E^\times$ by the product formula and because $\upsilon$ is trivial on $E^\times$.

**Exercise 5.** Let $V_0 = 0$ and $p = 1$. Use the mixed law to compute the slice of $\varrho(y)\varrho(y')f$ in two ways, and find the scalar that relates them.

*Hint.* Use $\varrho(y)\varrho(y') = \beta(y, y')\varrho(y + y')$ and $l^* J k = 1$.

**Exercise 6.** Let $p$ have one element, and let $z, z' \in \mathbb{A}$ be real, that is $\bar z = z$ and $\bar z' = z'$. Assume that the product of the radical elements of $z$ and $z'$ is the radical element of $z + z'$. Check that the formula for the centre of the radical in Section 7 agrees with this product rule.

*Hint.* The characters $\psi(-\tfrac12 \bar x z x)$ and $\psi(-\tfrac12 \bar x z' x)$ multiply to the character of $z + z'$.

## Notes and references

**The Weil representation.** The construction of the representation and of the invariant distribution on the adelic points goes back to Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964). For the invariance under the rational points the source cites n° 16 to 19 (Theorem 4) and n° 41 (Theorem 6) of this paper. Weil works with the symplectic group and its metaplectic cover. The source works with the unitary group of a hermitian space with a point and fixes the scalars by the vacuum, so no cover appears.

**Unitary groups and splittings.** The splitting of the metaplectic cover over a unitary group by a character of the determinant is in Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994), 361 to 401. The multipliers of Sections 4 and 5 are the normalization of the source for this splitting.

**Models.** The Schrödinger and mixed models, and the action of the parabolic subgroups, are in Mœglin, Vignéras and Waldspurger, *Correspondances de Howe sur un corps p-adique*, Lecture Notes in Math. 1291 (1987). The source proves the formulas of Section 7 from the vacuum and does not take them as definitions. The space of integrable coefficients against a vacuum is close to the Segal algebras of Reiter, *Metaplectic Groups and Segal Algebras*, Lecture Notes in Math. 1382 (1989), after Feichtinger, *On a new Segal algebra*, Monatsh. Math. 92 (1981).

**The cocycle.** The cocycle of three lattices as a finite sum is in Zelenov, *p-adic Heisenberg group and Maslov index*, Comm. Math. Phys. 155 (1993), 489 to 502, Proposition 4. For the real normalization in the Fock model the source cites Robinson and Rawnsley, Mem. Amer. Math. Soc. 410 (1989). The sign of the Gauss sum at an inert place by a congruence modulo $4$ is the argument of the source.

**What differs.** The source does not use the Stone-von Neumann theorem, a Schrödinger model on $L^2$ or a metaplectic group. It uses a vacuum, its model, Schur's lemma and explicit multipliers. The mixed model is a family of maps to $\mathcal{S}(V_0)$, not an isomorphism. The theta functional is unique up to a scalar, and the source fixes its absolute value by the mean of the vacuum.

**Further reading in this volume.** [Local theta in the Fock model](/chapter/local-theta/) uses the polynomial vectors and the derivative of Section 4. [The Siegel-Weil formula](/chapter/siegel-weil/) uses the slices and the Levi law of Section 7. [The Rallis inner product formula](/chapter/rallis-inner-product/) uses the doubled space $V \oplus V^-$.

Status: drafted by a model. No person has checked this chapter against the Lean source.
