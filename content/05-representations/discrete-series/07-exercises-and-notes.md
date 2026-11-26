---
title: Exercises and notes
lean:
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - Lib/DiscreteSeries/Holomorphic/ModelFunction.lean
  - Lib/General/Groups/BesselGroups.lean
  - Lib/General/Analysis/HolomorphicIntegrals.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $G = U(1,1)$, with $J = \operatorname{diag}(1, -1)$. Show that $|g_{11}|^2 - |g_{21}|^2 = 1$ for $g \in G$, so $|g_{11}| \ge 1$. Let $k \ge 1$ and $w_2$ be integers, and put $c(g) = g_{11}^{-k}(\det g)^{w_2}$. Show that $c(1) = 1$, that $c(g^{-1}) = \overline{c(g)}$, and that $|c(g)| = |g_{11}|^{-k}$.

*Hint.* The first statement is the $(1,1)$ entry of $g^* J g = J$. For the inverse use $g^{-1} = J g^* J$, so $(g^{-1})_{11} = \overline{g_{11}}$, and $|\det g| = 1$.

**Exercise 2.** Let $n = 3$, $\varepsilon = (1, 1, -1)$, and let $o$ be the order $o(1) < o(2) < o(3)$. Compute $2\rho$ from the formula of Section 6 and check that it is $(2, 0, -2)$. For $w = (0, 0, \gamma)$, write down $l = 2w + 2\rho$, and check that $l$ decreases strictly along $o$ on the indices of sign $+1$ and jumps up from the index $2$ to the index $3$.

*Hint.* The value of $2\rho$ at the index of rank $r$ is $n + 1 - 2r$. Then $l = (2, 0, 2\gamma - 2)$.

**Exercise 3.** Let $\varepsilon = (1, -1)$ and $w = (a, b)$ with $a \le b$. Use the description of `New.weightMinors` in Section 3 to compute $\operatorname{holMinors}_\varepsilon(w)(g)$ for an invertible $2 \times 2$ matrix $g$ with $g_{11} \ne 0$, and check the formula of `New.holMinors_ite_sign`.

*Hint.* Put $C = 2(|a| + |b|)$. The two weights are $w + c = (a + C, b)$ and $c = (C, 0)$. For a weight $(v_1, v_2)$ with $v_1 \ge v_2$, Section 3 gives $m_v(g) = g_{11}^{v_1 - v_2}(\det g)^{v_2}$. The quotient is $g_{11}^{a - b}(\det g)^b$.

**Exercise 4.** Check the formal degree of the holomorphic discrete series of $U(1,1)$ of weight $k \ge 2$: show that
$$\int_0^\infty \cosh^{-2k} t\,\sinh 2t\,dt = \frac{1}{k - 1}.$$
Compare with the value of the formal degree in Section 2.

*Hint.* Put $u = \cosh^2 t$. Then $du = \sinh 2t\,dt$, and the integral is $\int_1^\infty u^{-k}\,du$.

**Exercise 5.** Let $g$ be a random element of $U(2)$ for the Haar measure of mass $1$. Show that $|g_{11}|^2$ is uniformly distributed on $[0, 1]$. Deduce that in the polar coordinates $g = k\exp(iX_t)k'$ of Section 2, where $|g_{11}| = \cos t$, the density of $t$ on $[0, \pi/2]$ is $\sin 2t$. This is the normalisation of the measure that Section 2 uses for $U(1,1)$.

*Hint.* The first column of $g$ is a uniform point $(z_1, z_2)$ on the unit sphere $S^3 \subset \mathbb C^2$. Write $z_j = r_j e^{i\theta_j}$. The surface measure on $S^3$ in the coordinates $(r_1^2, \theta_1, \theta_2)$ is a constant times $d(r_1^2)\,d\theta_1\,d\theta_2$. This is the complex form of Archimedes' theorem on the sphere. With $u = \cos^2 t$, $|du| = \sin 2t\,dt$.

**Exercise 6.** Show that $\operatorname{wave}(c) = \exp(2i\operatorname{Im} c)$, that $\operatorname{wave}(c + c') = \operatorname{wave}(c)\operatorname{wave}(c')$, and that $x \mapsto \mathbf e(-2\operatorname{Re} x)$ is $x \mapsto \operatorname{wave}(-2\pi i x)$. Show that every continuous homomorphism $\chi$ from the additive group $\mathbb C$ to the circle is $x \mapsto \operatorname{wave}(\alpha x)$ for exactly one $\alpha \in \mathbb C$.

*Hint.* For the last part, $\chi$ restricted to $\mathbb R$ and to $i\mathbb R$ gives two real characters $t \mapsto e^{i s_1 t}$ and $t \mapsto e^{i s_2 t}$. Then $\operatorname{wave}(\alpha x) = \exp(2i(\operatorname{Re}\alpha\operatorname{Im} x + \operatorname{Im}\alpha\operatorname{Re} x))$. Solve for $\alpha$.

**Exercise 7.** Check `New.hua_integral_le` in the case $k = 1$, $S = 1$, $a = 0$, $|s| = 1$ and $M = m > 0$: show that
$$\int_{\mathbb C} (m + |y|^2)^{-(r+1)}\,dy = \frac{\pi}{r\,m^r} \le \pi\,m^{-r}$$
for every natural number $r \ge 1$.

*Hint.* Use polar coordinates and put $u = |y|^2$. Then $dy = \pi\,du$ after the integral over the angle.

## Notes and references

The classical theory of Section 2 follows Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples* (Princeton University Press, 1986), with the references to Harish-Chandra and to Schmid and Hecht given there. The formula for Flensted-Jensen's coefficient is in M. Flensted-Jensen, *Discrete series for semisimple symmetric spaces*, Ann. of Math. 111 (1980) 253-311. Fischer's inequality is in Horn and Johnson, *Matrix Analysis* (Cambridge University Press, 1985), Section 7.8. The source proves the bound of Hua's type that it uses.

The source does not construct the discrete series. Every statement in this chapter is about the explicit functions $c_\lambda$, $\tilde c_\lambda$, $e_\lambda$ and the model function of Section 6. In the source, the abstract representations occur only in the rigidity theorem of Section 5, where a unitary representation of polynomial growth is a hypothesis.

The junk values in the definitions of the chapter are these. `New.weightMinors` is $1$ at a singular matrix, because a `finprod` with infinitely many factors different from $1$ is $1$. `New.HCParam.formalDegree` is $0$ when $|c_\lambda|^2$ is not integrable. `New.HCParam.splitCoeff` takes a factor with `choose`. The theorems of Sections 4 and 5 remove each of these under the gap hypotheses.

The register of findings has the entry F-034 on these junk values. The entry says that `weightMinors` divides by $\det g$, which is $0$ for a singular $g$. This is not the whole story: the division by $0$ makes infinitely many factors $0$, and then the `finprod` is $1$, not $0$. Section 3 gives the details.

The spec question Q-68 is answered in Section 6. The research note on the general library calls the normalisation of `wave` unusual. The source proves its relation to the standard character, `New.Filling.wave_two_pi_I_mul`, so the normalisation is a convention and not an inconsistency.

The plan of Volume 9 for this volume names fewer chapters of Volume 5 than the imports of the source show. The list in Section 1 follows the source files, by the rule stated there.

Status: drafted by a model. No person has checked this chapter against the Lean source.
