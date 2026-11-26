---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $q$ be a polynomial over a field and $y$ a unit that is not a root of $q$. Show that $1$ is not a root of $q$ with its roots scaled by $y^{-1}$. Use this to check condition 6 of a lift setting for the descent pairs of the lifts, as in [lift settings and representations of a type](/chapter/main-summands/#lift-settings-and-representations-of-a-type).

*Hint.* The scaled polynomial at $X$ is $y^{-\deg q}\,q(yX)$ up to a unit. At $X = 1$ it is a unit times $q(y)$.

**Exercise 2.** Let $x$ be a root of unity in $\bar{\mathbb{Q}}_\ell$ of order prime to $\ell$, and $x \neq 1$. Show that $|x - 1| = 1$. Then show by an example that $|x - 1| < 1$ is possible when the order of $x$ is a power of $\ell$.

*Hint.* For order $k$ prime to $\ell$, $\prod_{1 \leq a < k}(1 - x^a) = k$ is a unit. For an $\ell$-th root of unity, $\prod_{1 \leq a < \ell}(1 - x^a) = \ell$, and all factors have the same norm.

**Exercise 3.** Let $Z$ be a matrix of size $2$ over $\bar{\mathbb{Q}}_\ell$ whose eigenvalues are two distinct roots of unity $\zeta_1, \zeta_2 \neq 1$ of order dividing $p^d - 1$. Bound $v_\ell \det(Z - 1)$ by $2\,v_\ell(p^d - 1)$. Compare with the lemma on determinants in [inertia above the level and main summand like](/chapter/main-summands/#inertia-above-the-level-and-main-summand-like).

*Hint.* $\det(Z - 1) = (\zeta_1 - 1)(\zeta_2 - 1)$, and $\zeta_i - 1$ divides $p^d - 1$ in the integers.

**Exercise 4.** Let $s$ be an element of tame inertia and $\varphi$ a Frobenius, with $\varphi s \varphi^{-1} = s^q$. Let $R$ be a representation of rank $2$ in which $R(s)$ has the eigenvalues $\zeta$ and $\zeta^q \neq \zeta$. Show that $R(\varphi)$ swaps the eigenlines of $R(s)$ and that $R(\varphi^2)$ is diagonal in the same basis.

*Hint.* If $R(s)v = \zeta v$, then $R(s)R(\varphi^{-1})v = R(\varphi^{-1})R(s^q)v = \zeta^q R(\varphi^{-1})v$.

**Exercise 5.** For the main pair of [the weights](/chapter/main-summands/#main-summands-from-eigensystems), with $z = D.r$, compute the length $2z - 1$ of the string and check that it is at most $D.t$.

*Hint.* $2D.r - 1 < 5D.r = D.t$.

**Exercise 6.** Show that $\mathrm{tr}\,u = \psi\,\mathrm{tr}\,T + \sum_{e < t}\varepsilon^{-e}$ does not determine $T$ up to isomorphism if $\psi$ is not given. Then explain why the definition of a main summand fixes $\psi$ as the inverse avatar of the twist.

*Hint.* Replace $T$ by $\eta T$ and $\psi$ by $\eta^{-1}\psi$ for a character $\eta$.

The exercises use only the statements of this chapter.

## Notes and references

The crystalline Selmer group and its local conditions at $\ell$ follow Bloch and Kato (S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, in The Grothendieck Festschrift, Vol. I, Birkhäuser, 1990, Section 3). The idea to build a Galois extension from a congruence goes back to Ribet (K. Ribet, *A modular construction of unramified $p$-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976)). This chapter does not compare the statements of the source with these texts.

The main theorem gives one representation $T$ for each eigensystem and lift index. The trace identity holds for all twisted lifts at once. Later chapters of this volume use $T$ only through the definition of a main summand. They do not use the label $c$ or the representation $R$ of the proof. The choice of $c$ is not unique: any good tuple with $e_c z \neq 0$ works, and the source picks one by an existential. So $T$ is not canonical, but its trace is fixed on all of $G_E$ by the trace identity and density of Frobenius elements. The weights of $T$ come from the target parameters, which the data fixes.

The research notes and the volume plan have errors for this chapter.

- Research note f-congr says that a main summand is crystalline at $\ell$. In the source the condition is only finite type, that is potentially crystalline, at the places above $\ell$ that divide $p_0 p_1$. Good reduction is asked only at the places prime to $p_0 p_1$.
- The section numbers of the plan for this chapter, in plan 07.4, do not match the order of the files in `volume.yaml`.
- [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) points to this chapter for the auxiliary twist $\psi$. That object is defined in [tied traces and even classes](/chapter/tied-traces/).

No file of this chapter imports a file that `volume.yaml` places in a later chapter of Volume 12.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
