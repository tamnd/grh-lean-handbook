---
title: Exercises
lean:
  - New/Appendix/DiscreteSeries/Periods.lean
  - New/Appendix/DiscreteSeries/StationaryPosition.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Show that the set $\{z \in \mathbb{C} : |z| \leq 2\operatorname{Re}z\}$ is the closed sector $|\arg z| \leq \pi/3$, together with $0$. Let $f$ be an integrable function with values in this sector. Show that $\int|f| \leq 2\left|\int f\right|$. Give an example where equality holds.

*Hint.* Write $z = re^{i\alpha}$. Then the condition is $\cos\alpha \geq 1/2$. Integrate $|f| \leq 2\operatorname{Re}f$, and use $\operatorname{Re}\int f \leq |\int f|$. For equality take $f$ with the two values $e^{\pm i\pi/3}$ on two sets of equal measure.

**Exercise 2.** Prove the lemma on the product of two near numbers of section 6: for $a, c, t \in [0, 1]$, $|u - a| \leq a/10 + t$ and $|v - c| \leq c/10 + t$ imply $|uv - ac| \leq 0.21\,ac + 4t$. Then prove the cone lemma: $p \geq 0$ and $|z - p| \leq 0.21\,p + 4t$ imply $|z| \leq 2\operatorname{Re}z + 12t$. Why is $1/10$ small enough here, and would $1/2$ be small enough?

*Hint.* Expand $uv - ac = a(v - c) + c(u - a) + (u - a)(v - c)$. For the cone, $|z| - 2\operatorname{Re}z \leq 3|z - p| - p$. The argument needs $3 \cdot 0.21 < 1$. With $1/2$ in place of $1/10$ the first constant becomes $1/2 + 1/2 + 1/4 = 5/4$.

**Exercise 3.** Let $\beta \geq 16$ and $N \geq 1$. Check that $48\beta^{16N}16^{9N} \leq \beta^{50N}$ and $16\beta^{16N} \leq \beta^{20N}$. Deduce the lemma on absorbing the error: if $V, I \geq 0$, $V \leq \beta^{16N}W$ and $W/4 \leq 2I + 6\beta^{-50N}16^{9N}V$, then $V \leq \beta^{20N}I$.

*Hint.* Use $48 \leq \beta^2$, $16 \leq \beta$ and $16^{9N} \leq \beta^{9N}$. Substitute the bound for $W$ into the bound for $V$ and move the term in $V$ to the left.

**Exercise 4.** Let $L = 3$, $L' = 0$ and $d = 1$, and let $\mu = (-1, -2, -3)$. So $q = 1$ and $p = (t + 1)(t + 2)(t + 3)$. Compute the vectors $v_1 = [1]$ and $v_2 = [t]$ of section 7 explicitly. Check that $\langle v_1, v_1\rangle = \langle v_1, v_2\rangle = 0$ and $\langle v_2, v_2\rangle = 1$ for the alternating form, and that $\mu v_1 = v_2$.

*Hint.* We have $p'(-1) = 2$, $p'(-2) = -1$ and $p'(-3) = 2$. So $v_1 = (2^{-1/2}, 1, 2^{-1/2})$ and $v_2 = (-2^{-1/2}, -2, -3 \cdot 2^{-1/2})$. Compare $\sum_i\mu_i^{a}/p'(\mu_i)$ for $a = 0, 1, 2$ with the coefficient of $t^2$ in $t^a$.

**Exercise 5.** Let $(v, i_0)$ be a position and $R$ its group. Show that $g \mapsto \exp(\overline{\sigma(g)} - \sigma(g))$ is a unitary character of $R$. Show that for $d = 0$ the character is trivial, and that $R$ is then the stabilizer of $v_1$ in $U(\varepsilon)$.

*Hint.* Additivity of $\sigma$ is the lemma of section 8. The number $\overline\sigma - \sigma$ is imaginary. For $d = 0$ the matrix $N$ has no rows, so $\sigma = 0$, and lowering the flag means $(g - 1)v_1 = 0$.

**Exercise 6.** Let $z$ be a positive semidefinite matrix. Show that $\|z - 1\| \leq \|z^2 - 1\|$ in the Frobenius norm. Show by an example that the inequality fails for Hermitian matrices that are not positive semidefinite.

*Hint.* Diagonalize $z$ by a unitary matrix, which does not change the Frobenius norm. For an eigenvalue $t \geq 0$, $|t^2 - 1| = |t - 1|(t + 1) \geq |t - 1|$. For the example take $z = -1$ of size $1$.

## Notes and references

Laplace's method for integrals of the form $\int e^{tf(x)}\,dx$ is treated in de Bruijn, *Asymptotic Methods in Analysis*, Chapter 4, and in Olver, *Asymptotics and Special Functions*, Chapter 3. The classical method gives an asymptotic expansion. The version in this chapter gives only a lower bound, but it is uniform in all the parameters and has explicit constants. Its three ingredients are a Gaussian shape near the identity, the removal of a phase that is a character of the group, and the decay of the integrand away from a compact subgroup.

The polar decomposition used in section 3 is in Horn and Johnson, *Matrix Analysis*, Theorem 7.3.1. Weyl's dimension formula, used in section 5 through the lower bound for the size of a $K$-type, is in Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 24.3. Schwarz's lemma, used in section 4, is in Rudin, *Real and Complex Analysis*, Theorem 12.2.

The subgroups of section 8 are the subgroups that occur in the Bessel case of the Gan-Gross-Prasad problem for unitary groups (Gan, Gross and Prasad, *Astérisque* 346, 2012). The source names as related work Nelson and Venkatesh, *The orbit method and analysis of automorphic forms* (2021); H. He, *On the Gan-Gross-Prasad conjecture for U(p,q)* (2017); and B. Sun, *Matrix coefficients of cohomologically induced representations* (2007). The source does not record a comparison with these works, and this chapter does not make one.

The discrete series coefficients, their conjugation formula, their decay and their lower bound near $1$ are in [Discrete series through one matrix coefficient](/chapter/discrete-series/). The source uses the restriction theorem in the deep level argument (see [/chapter/deep-level-poincare/](/chapter/deep-level-poincare/)) and the stationary position and the period bound for groups that map onto $R$ in the spanning argument at the real place (see [/chapter/bessel-real-place/](/chapter/bessel-real-place/)). The source claims that these steps, with the rest of the argument, give the result described in [The theorem and the plan](/chapter/theorem-and-plan/). Lean accepts the statements of this chapter, if the reported checks hold.
