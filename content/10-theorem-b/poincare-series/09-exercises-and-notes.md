---
title: Exercises and notes
lean:
  - New/Spanning/Unfolding/FrameMass.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Exercises

**Exercise 1.** Let $u \in \mathsf U_c(M)$ and $u' \in \mathsf U_{c'}(M)$. Show that the amplitude sum of the block $(c, s, c')$ is unchanged when $s$ is replaced by $usu'^{-1}$, up to the factor $\chi(u)^{-1}\chi(u')$. Deduce that the sum is $0$ if $s$ does not agree.

*Hint.* Move the two factors into the kernel, as in [moving blocks](/chapter/poincare-series/#moving-blocks), and use that $W$ transforms under the Bessel unipotent group by $\chi$.

**Exercise 2.** Let $v \neq 0$ be a vector of $\mathbb F_N^k$. Show that the stabilizer of $v$ in $GL_k(\mathbb F_N)$ has index $N^k - 1$. Deduce the index $(N^k - 1)^f$ of [the lattice stabilizer lemma](/chapter/poincare-series/#the-data-are-admissible) from the description of the lattice stabilizer by the row $k_0$.

*Hint.* The group $GL_k(\mathbb F_N)$ acts transitively on the nonzero vectors. Use the orbit stabilizer formula at each of the $f$ places above $N$, and the fact that reduction is onto.

**Exercise 3.** Let $l \ge 1$ and $w > 0$. Show that the volume of the unit sphere of $\mathbb C^l$ for the measure $dy/d\langle y, y\rangle$ is $\pi^l/(l-1)!$ when $\mathbb C$ carries Lebesgue measure. Then show that the normalizations of the section on admissibility give $\mathrm{sph}_l = (2\pi)^l/(w^{l-1/2}(l-1)!)$.

*Hint.* The volume of the ball of radius $\rho$ in $\mathbb C^l = \mathbb R^{2l}$ is $\pi^l\rho^{2l}/l!$. Differentiate in $t = \rho^2$. The measure $2/w$ on $\mathbb C$ gives a factor $(2/w)^l$, and the measure $w^{-1/2}$ on $\mathbb R$ divides by $w^{-1/2}$ in the fibre.

**Exercise 4.** Assume only the ratio of masses with error $\epsilon$ at each rank $k \le i < r$. Show that the frame mass estimate holds with $1 + b^{-9}$ replaced by $\exp\bigl((r - k)\epsilon + 4f/N\bigr)$.

*Hint.* Follow the proof of the frame mass estimate. The telescoping step is unchanged, and only the sum of the errors changes.

**Exercise 5.** Let $j \in E$ be purely imaginary and $c \in F$. Show that $\psi_E\bigl(\tfrac{j}{2}c(\sigma - \bar\sigma)\bigr) = \psi_E(jc\sigma)$ for all $\sigma \in \mathbb A_E$, when $\psi_E$ is the standard character of $E$ composed with the trace to $F$. Explain why the hypothesis $\jmath c_Y = -(M\varpi)^{-1}$ then makes $\mathrm{bc}$ equal to $\psi_U$ on $U(\mathbb A)$.

*Hint.* The standard character of $E$ is $\psi_F\circ\mathrm{tr}_{E/F}$, and $\mathrm{tr}(z) = z + \bar z$. Compute $\mathrm{tr}$ of both arguments with $\bar j = -j$ and $\bar c = c$.

**Exercise 6.** Let $\Gamma \subset G$ be a discrete subgroup of a unimodular group and let $\beta$ be a cutoff for $\Gamma$. Let $\phi$ be integrable on $G$ and $y$ bounded and left invariant under $\Gamma$. Show that $\int_{\Gamma\backslash G}y(x)\sum_{\gamma\in\Gamma}\phi(\gamma x)\,dx = \int_Gy\,\phi$, where the left side is computed with $\beta$.

*Hint.* Write the left side as $\int_G\beta(x)y(x)\sum_\gamma\phi(\gamma x)\,dx$. Exchange sum and integral, which is allowed by absolute convergence, and substitute $x \mapsto \gamma^{-1}x$. The sum $\sum_\gamma\beta(\gamma^{-1}x)$ is $1$.

**Exercise 7.** Show that the ratio $\mathrm{msm}/\mathrm{ism}$ of the second moments does not depend on the class number $n_X$, but only on $d$, $N$, $\deg$, the masses and $|\bar U|$. Explain why this makes the range of the ratio a statement about the data and not about the classes.

*Hint.* Use $\mathrm{msm} = (n_Xd)^2/(\deg\,\mathrm{mass}(r))$, $\mathrm{ism} = |\bar S|n_Xd$, $|\bar S| = |\bar H||\bar U|$ and the formula for $n_X$.

## Notes and references

Poincaré series were introduced by Poincaré for Fuchsian groups. Their unfolding against an automorphic form, and the Petersson formula for the inner product of two series, are standard. For the classical case of $SL_2(\mathbb Z)$ see H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS Graduate Studies in Mathematics 17 (1997), chapter 3. The present series is a sum over the rational points of a unitary group of a cut Bessel function. The source unfolds it in the general setting of `New.Filling.IsAdmissible`, so that each step has the form of the classical argument.

The decision of which terms contribute is the climbing argument of section 4. It is specific to this source. The file Climbing.lean is placed in this chapter by the plan of the volume. Two older notes of the project place it with [the anatomy of a term](/chapter/anatomy-of-a-term/). This book follows the plan.

The masses of genera of hermitian lattices enter through [the ratio of masses](/chapter/siegel-weil/#the-ratio-of-masses). The remark there names the literature for the exact mass formula. This chapter uses only the approximate ratio that the source proves.

The size conditions of admissible data are many inequalities, each used once. The exponents $11$, $6$, $23$ and $60$ of `New.Filling.IsAdmissible` are those of the source. The source does not claim that they are optimal.

The identity of section 8 is stated for one point and one linear form, both chosen. The source does not compute them. Theorem B needs only that they exist. The hypothesis on the generic constant, F-080 in the register, is proved for the data inside `New.Data.exists_poincareAt_eq_poincareMap_comp`.

The chapter states what Lean accepts, if the reported checks hold. It does not claim that the argument is correct.
