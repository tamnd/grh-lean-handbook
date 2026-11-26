---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** In the model case $\varrho = 0$ of Section 1, let $y \in U(k, 1)$. Show that $|h(z, yz)| \ge 1$, with equality if and only if $yz$ is a multiple of $z$. Deduce that the big cell is the whole group.

*Hint.* Write $yz = v + c z$ with $v$ in the definite block. Then $h(yz, yz) = \|v\|^2 - |c|^2 = -1$, and $h(z, yz) = -c$.

**Exercise 2.** Let $a < \varrho$. Show that the parameters of a Heisenberg element are unique: if $\nu_a(v, \beta) = \nu_a(v', \beta')$, then $v = v'$ and $\beta = \beta'$.

*Hint.* Apply both sides to $e^*_a$. The image is $e^*_a + v + (\beta - \tau h(v, v)) e_a$. The components on the floors at least $a + 1$ give $v = v'$, and the coefficients of $e_a$ then give $\beta = \beta'$.

**Exercise 3.** Let $u \in S$. Use the trace formula of Section 6 and $\sigma(u^{-1}) = -\sigma(u)$ to show that $\operatorname{tr}(C u) = 2i \operatorname{Im} \sigma(u)$ and $\operatorname{wave}(\sigma(u)) = \exp(\operatorname{tr}(C u))$. Give an element $u$ of the unitary group outside $S$, for $\varrho = 1$, with $\sigma(u^{-1}) \ne -\sigma(u)$.

*Hint.* Here $\sigma(u)$ is the coefficient of $e_0$ in $u z$. Take $u = \nu(v, \beta)\, g$ with $g$ an isometry of the middle block that does not fix $z$. Since $g$ fixes $e_0$, $\sigma(u)$ is $-h(v, g z)$ and $\sigma(u^{-1})$ is $h(v, z)$, with the formula of Section 1 for the coefficient of $e_0$.

**Exercise 4.** Prove the Plancherel inequality of Section 7 at the place $\mathbb C$ with $|\iota| = 1$, and show that it is an equality for $f \in L^1 \cap L^2$.

*Hint.* Write $w = w_1 + i w_2$. Then $\psi(\eta \bar v w) = \exp(2i \operatorname{Im}(\eta \bar v w))$, which is $e^{i \langle \xi, w \rangle}$ for a vector $\xi \in \mathbb R^2$ with $|\xi| = 2|\eta||v|$. The map $v \mapsto \xi$ is a rotation times $2|\eta|$, of Jacobian $4|\eta|^2$. The Plancherel theorem on $\mathbb R^2$ gives $(2\pi)^2 / (4|\eta|^2) = \pi^2/|\eta|^2$.

**Exercise 5.** Let $k = 1$, so that the top floor group is $U(1, 1)$ on the plane of $x$ and $z$. Let $\sigma \in U(1,1)$ with $c = h(z, \sigma z)$ and $|c| > 1$. Find $k_1, k_2 \in U(1)$ with $\sigma = \iota(k_1) w(c) \iota(k_2)$. Show that $k_1$ and $k_2$ are unique.

*Hint.* The column $\sigma z$ is $v x - c z$ with $|v|^2 = |c|^2 - 1$, and $w(c) z = s x - c z$ with $s = \sqrt{|c|^2 - 1}$. So $k_1 = v/s$. For uniqueness, let $w(c) = \iota(t) w(c) \iota(t')$ and compare the entries at $(x, z)$ and $(z, x)$. Both are $\pm s \ne 0$, so $t = t' = 1$.

**Exercise 6.** Let $S_k(r) = 2 \pi^k r^{k-1}/(k-1)!$. Show that $\int_0^R S_k(r)/2\, dr$ is the volume of the ball of radius $\sqrt R$ in $\mathbb C^k$. Compute $\operatorname{vol} U(1)$, $\operatorname{vol} U(2)$ and $\operatorname{vol} U(3)$ from $\operatorname{vol} U(j) = \prod_{i=1}^j S_i(1)$. Then compute the constant $\operatorname{vol} U(r) / (\operatorname{vol} U(k)\, 2^{\varrho + 1})$ of the frame bound for $\varrho = 1$ and $k = 1$.

*Hint.* The ball has volume $\pi^k R^k / k!$. The values are $S_1(1) = 2\pi$, $S_2(1) = 2\pi^2$ and $S_3(1) = \pi^3$. Then $S_4(1) = \pi^4/3$. For $\varrho = 1$ and $k = 1$ the dimension is $r = 4$, and the constant is $\pi^9/6$.

## Notes and references

The Bruhat decomposition of a reductive group over a field, with the big cell as the open cell of the longest Weyl element, is in Borel, *Linear Algebraic Groups*, 2nd ed., Theorem 14.12. Section 4 proves the case of a parabolic subgroup directly, over a ring with an involution, by a descent through the floors.

Bessel subgroups of unitary groups and the Bessel models that they define are in Gan, Gross and Prasad, Astérisque 346 (2012), §12. This chapter uses the subgroup and its character, and no Bessel model.

The Schur orthogonality relations for square integrable representations, and the formal degree, are the model for Section 6. There the relations are proved from an idempotent kernel. The kernels come from [discrete series through one matrix coefficient](/chapter/discrete-series/).

The Plancherel theorem used for the constant at $\mathbb C$ is Folland, *Real Analysis*, 2nd ed., Theorem 8.29. The Cartan decomposition $KAK$ is in Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Theorem 7.39. The invariant measure of the hyperboloid in polar coordinates follows Helgason, *Groups and Geometric Analysis*, Ch. I §5. The comparison of Haar measure of a unitary group with the fibre measure of the Gram map is the local form of Siegel's mass computation (Siegel, Ann. of Math. 36 (1935)).

The measures of Sections 5 and 7 enter the unfolding of the Poincaré series of Theorem B in [local densities at the real places](/chapter/real-densities/).
