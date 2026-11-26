---
title: Exercises and notes
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\Theta \colon \mathbb{C}^d \to V$ be injective, $K$ its range, $U$ an operator on $V$, and $\mathrm{pr}_K$ the orthogonal projection onto $K$. Prove that $\det(\Theta^*\Theta)\cdot\det(\mathrm{pr}_K U|_K) = \det(\Theta^*U\Theta)$.

*Hint.* Write $\Theta = \iota_K\circ\Theta_0$ with $\Theta_0 \colon \mathbb{C}^d \to K$ an isomorphism. Then $\Theta^*U\Theta = \Theta_0^*(\mathrm{pr}_K U|_K)\Theta_0$ and $\Theta^*\Theta = \Theta_0^*\Theta_0$. Take determinants and use $\det(\Theta_0^*)\det(\Theta_0) = \det(\Theta_0^*\Theta_0)$.

**Exercise 2.** In the model case of Section 1, replace $U = \mathrm{diag}(1, 0)$ by $U = \mathrm{diag}(1, 3)$ and keep $v = (1, 2)$. Compute $Z$, $\Delta$ and $Z\Delta$. Which primes $\ell$ give $|\Delta|_\ell > 1$, and what operator $\Lambda$ on the line clears the projection?

*Hint.* $\langle v, Uv\rangle = 1 + 12 = 13$ and $Z = 5$, so $\Delta = 13/5$. Only $\ell = 5$ gives a denominator. The projection of $(1, 0)$ is $\tfrac15 v$, as before, so $\Lambda = 5$ works.

**Exercise 3.** Show that a bound for $U_1$ at $\sigma = 1$ alone does not give property 5. Find an algebraic number $\lambda$ with $|\lambda| \leq 1$ and an automorphism $\sigma$ of $\mathbb{C}$ with $|\sigma(\lambda)| > 1$. For the operator $U = \lambda\cdot\mathrm{id}$ on a space of forms, compare $\|U\varphi\|_1^2/\|\varphi\|_1^2$ with $\|U\varphi\|_\sigma^2/\|\varphi\|_\sigma^2$.

*Hint.* Take $\lambda = \sqrt 2 - 1$ and $\sigma(\sqrt 2) = -\sqrt 2$. By the scaling rule of Section 2 the two quotients are $|\lambda|^2$ and $|\sigma(\lambda)|^2 = (1 + \sqrt 2)^2$.

**Exercise 4.** Check the size inequality of step 4 of the main theorem term by term, from the table of sizes. Which of the four terms is the largest, and by what power of $\log b$ is it smaller than $kB\log b$?

*Hint.* The terms $rB$ and $6kB$ are of relative size $1/\log b$; the term $3A$ is of relative size $1/\log^2 b$; the term $10 m x_1$ is of relative size at most $40/\sqrt b$. The largest is $6kB$ or $rB$, depending on $r/k \in [1, 2]$.

**Exercise 5.** In the proof of the main theorem, the archimedean bound is used only at $\vartheta = 1$ and the $\ell$-adic bound only at $\vartheta = \xi_\iota^j$. Explain why the proof would fail if the two roles were exchanged, that is, with $H = \Delta(\xi_\iota^j)$.

*Hint.* In the criterion for heights the number $H$ is one fixed number for all $\iota$. The determinant $\Delta(\xi_\iota^j)$ depends on $\iota$.

**Exercise 6.** Let $P$ be an operator on a finite dimensional space $L$ over $\mathbb{C}$, and $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. Suppose that $P$ maps a lattice $\Lambda_0 \subseteq L$ over the valuation ring at $\iota$ into itself. Show that $|\iota(\det P)|_\ell \leq 1$. Compare this with the eigenvector argument of the $\ell$-adic bound, which does not choose a lattice.

*Hint.* The determinant of $P$ is the determinant of its matrix in a basis of $\Lambda_0$, and that matrix has integral entries. The source works with a gauge on forms, and the eigenvector argument needs only one integral scaling of each eigenvector.

## Notes and references

**The method.** The chapter compares two Gram determinants through a fixed positive operator $U^\circ$ and a scalar $\rho_j(\vartheta)$. This is a form of the classical method of comparing Petersson norms of lifts with $L$-values through an inner product identity. Hida [Hida 1981] used congruences between such norms and the special values of $L$-functions to detect congruences of modular forms. Böcherer-Dummigan-Schulze-Pillot [Böcherer-Dummigan-Schulze-Pillot 2012] used the Yoshida lift and a pullback formula to relate the norm of a lift to $L$-values, and so to congruences. X. Zhang [Zhang 2018] related special $L$-values of Siegel modular forms of genus 2 to Selmer groups by the same kind of comparison. The source works with a determinant of a whole space of lifts, not with one form, and with the height over all isomorphisms $\iota$ at once.

**Heights.** The heights of this chapter are heights of families of algebraic numbers indexed by isomorphisms with the $\ell$-adic numbers, as defined in Volume 1. The model is the absolute logarithmic height; see Bombieri-Gubler [Bombieri-Gubler 2006, chapter 1]. The criterion `HeightLe.of_mul_le` is the product formula estimate: one bounds a fixed multiple $H z$ at the finite places and $H$ at the infinite places.

**Conjugate norms.** The norms $\|\varphi\|_\sigma$ at every automorphism of $\mathbb{C}$ are the main technical device of the chapter. Property 5 and the projection bound must hold at every $\sigma$, because the height sees every conjugate of $\Delta(1)$. Volume 4 defines these norms and proves their invariance ([the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)).

**Formalization.** The chapter has several formalization remarks. Section 3 discusses the choice of the twist factors and the division in $\rho_j$. Section 5 discusses the property that answers F-072. Section 6 notes that the compression is an operator on the lifts. Section 7 notes that $\beta$ may be negative and that $\rho_j(1) = 1$ needs property 1 at $\vartheta = 1$. The field `ratio_ne_zero` is the answer of the source to F-072 of [the register of findings](/chapter/register-of-findings/).

**Numbering.** The plan of the volume lists this chapter as chapter 16, after the two parts of the comparison operator and the Hecke values. Some planning notes give it the number 15. The order of `volume.yaml` is the one used here.

**References.**

- [Hida 1981] H. Hida, Congruences of cusp forms and special values of their zeta functions, Invent. Math. 63 (1981), 225-261.
- [Böcherer-Dummigan-Schulze-Pillot 2012] S. Böcherer, N. Dummigan, R. Schulze-Pillot, Yoshida lifts and Selmer groups, J. Math. Soc. Japan 64 (2012), 1353-1405.
- [Zhang 2018] X. Zhang, Special L-values and Selmer groups of Siegel modular forms of genus 2, 2018.
- [Bombieri-Gubler 2006] E. Bombieri, W. Gubler, Heights in Diophantine Geometry, Cambridge University Press, 2006.

Status: drafted by a model. No person has checked this chapter against the Lean source.
