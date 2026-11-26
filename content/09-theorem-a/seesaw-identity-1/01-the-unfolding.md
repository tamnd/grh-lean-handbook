---
title: The unfolding of the seesaw
lean:
  - New/UpperBound/Seesaw/UnfoldingStages.lean
decls:
  - New.Data.unfoldStageOn
  - New.Data.unfoldStage
  - New.Data.unfoldStageOn_zero
  - New.Data.unfoldStageOn_succ
  - New.Data.unfoldStage_update
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The unfolding of the seesaw

This chapter and [the seesaw identity, part 2](/chapter/seesaw-identity-2/) prove the seesaw identity, the second input of [Theorem A and its plan](/chapter/theorem-a-plan/). The identity says that the lower chain of lifts, applied to the Poincaré series $\mathcal{P}\varphi$ of a ramified source form $\varphi$, is a constant times the composite lift of the source form along an upper chain. This chapter does the analytic half of the proof. It pairs the lower chain of $\mathcal{P}\varphi$ with a test form $z$, unfolds the pairing one lift at a time, and writes the result as a finite sum over classes of finite adelic points, with a factor that does not depend on the twist. It also proves the facts on lattices and on combinations that the second part needs to identify the terms of the sum.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of Volume 1 reduces the source to the main inequality, and Theorem A gives its upper bound. [Theorem A and its plan](/chapter/theorem-a-plan/) states the seesaw identity:

**Theorem (Seesaw identity).** Let $t$ be a linear form on the values of source forms and let $g$ be an archimedean point of $U(Y_0)$. There is $c \in \mathbb{C}^\times$ such that every tame character $\vartheta$ has a chain datum $\Psi$ with $\iota_\vartheta(\mathcal{P}\varphi) = c \cdot B_{\vartheta,\Psi}\varphi$ for every ramified source form $\varphi$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

Here $\mathcal{P} = \mathcal{P}_{g,t}$ is the Poincaré map of [the objects of the upper bound](/chapter/upper-bound-objects/), $\iota_\vartheta$ is the lower chain of $m$ lifts with the twist $\vartheta$, and $B_{\vartheta,\Psi}$ is the composite lift along the upper chain with the chain datum $\Psi$. The proof has two parts. This chapter proves the unfolding theorem at the end of this section. [Part 2](/chapter/seesaw-identity-2/) evaluates each term of the cut sum on neighbour lattices, chooses a good datum, and assembles $\Psi$.

### A model case: the classical Poincaré series

The method of the chapter is the unfolding of a Poincaré series, done many times. The classical case shows the idea.

Let $\Gamma = \mathrm{SL}_2(\mathbb{Z})$, let $\Gamma_\infty$ be its subgroup of upper triangular matrices, let $k \geq 4$ be even and let $n \geq 1$. For $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ put $j(\gamma, z) = cz + d$ and $e(z) = e^{2\pi i z}$. The Poincaré series is

$$P_n(z) = \sum_{\gamma \in \Gamma_\infty \backslash \Gamma} j(\gamma, z)^{-k}\, e(n\gamma z).$$

It converges absolutely and uniformly on compact sets for $k \geq 4$, because $|e(n\gamma z)| \leq 1$ and $\sum_{(c,d) = 1} |cz + d|^{-k}$ converges. The Petersson product of two forms of weight $k$ is $\langle f, h\rangle = \int_{\Gamma\backslash\mathbb{H}} f(z)\overline{h(z)}\, y^k\, d\mu(z)$ with $d\mu = dx\,dy/y^2$.

**Example (Unfolding of a Poincaré series).** Let $f(z) = \sum_{l \geq 1} a_l\, e(lz)$ be a cusp form of weight $k$ for $\Gamma$. Then

$$\langle f, P_n\rangle = a_n\, \frac{\Gamma(k-1)}{(4\pi n)^{k-1}}.$$

*Proof.* Put $F(w) = f(w)\,\overline{e(nw)}\,(\operatorname{Im} w)^k$. For $\gamma \in \Gamma$ we have $f(\gamma z) = j(\gamma, z)^k f(z)$ and $\operatorname{Im}(\gamma z) = y\,|j(\gamma, z)|^{-2}$. So

$$f(z)\,\overline{j(\gamma,z)^{-k}\, e(n\gamma z)}\, y^k = f(\gamma z)\, j(\gamma,z)^{-k}\,\overline{j(\gamma,z)}^{-k}\,\overline{e(n\gamma z)}\, y^k = F(\gamma z).$$

Thus $f(z)\overline{P_n(z)}y^k = \sum_{\gamma \in \Gamma_\infty\backslash\Gamma} F(\gamma z)$. The sum of the absolute values is bounded by $|f(z)|y^{k/2}$ times $\sum_\gamma \operatorname{Im}(\gamma z)^{k/2}$, an Eisenstein series of weight $0$ at $s = k/2$. The function $|f(z)| y^{k/2}$ is bounded and decays rapidly at the cusp, and the Eisenstein series grows like $y^{k/2}$ there. So the sum of the absolute values is integrable on $\Gamma \backslash \mathbb{H}$, and Fubini's theorem gives

$$\langle f, P_n \rangle = \int_{\Gamma\backslash\mathbb{H}} \sum_{\gamma \in \Gamma_\infty\backslash\Gamma} F(\gamma z)\, d\mu(z) = \int_{\Gamma_\infty\backslash\mathbb{H}} F(z)\, d\mu(z).$$

The quotient $\Gamma_\infty \backslash \mathbb{H}$ is the strip $0 \leq x < 1$, because $-1$ acts trivially. On the strip, $\int_0^1 f(x + iy)\, e^{-2\pi i n x}\, dx = a_n e^{-2\pi n y}$ and $\overline{e(n(x + iy))} = e^{-2\pi i n x} e^{-2\pi n y}$. So

$$\langle f, P_n\rangle = \int_0^\infty a_n\, e^{-4\pi n y}\, y^{k-2}\, dy = a_n\, \frac{\Gamma(k-1)}{(4\pi n)^{k-1}}. \qquad \square$$

Three features of the model case recur in this chapter.

1. *The fold.* The pairing with a series over $\Gamma_\infty\backslash\Gamma$ becomes an integral over the larger space $\Gamma_\infty\backslash\mathbb{H}$. Here the role of $\Gamma_\infty$ is taken by the rational points of a Bessel group $R$, and the role of the series by a theta kernel.
2. *The character.* The integral over the compact part $\Gamma_\infty \backslash N$ of the unipotent group picks out one Fourier coefficient. Here it picks out the constant term of a datum at a fixed map $T$ between strings, and the generic character of $R$.
3. *The constant.* What is left is one coefficient times an integral that does not depend on $f$. Here what is left at the end is a finite sum over classes, times a constant that does not depend on the twist.

### The tower

Recall from [the data and its sizes](/chapter/data-and-sizes/) and [the objects of the upper bound](/chapter/upper-bound-objects/) the following objects. There are $m = 2\varrho + 2$ lifts. For $0 \leq k \leq m$ the hermitian space $Y_k$ over the CM field $E$ has the unitary group $G_k = U(Y_k)(\mathbb{A})$, with $[G_k] = G_k(E)\backslash G_k$. For $k \leq 2\varrho + 1$ the standard grading $\mathsf{Y}_k$ of $Y_k$ (Lean: `New.Data.gradingY`) has a definite part $X_k$ and a string of length $s_k = 2\varrho + 1 - k$. Its Bessel group is $R_k$, with the compact quotient $[R_k] = R_k(E)\backslash R_k(\mathbb{A})$ and the generic character of [Bessel periods](/chapter/bessel-periods/). The string becomes one shorter at each lift, and $Y_{2\varrho+2}$ has the empty string.

For a tame character $\vartheta$ the lift $\iota_k = \iota_{\vartheta,k}$ from forms on $Y_k$ to forms on $Y_{k+1}$ is the theta lift with the datum $\Phi_k = $ `datumY ϑ k` on $\operatorname{Hom}(Y_k, Y_{k+1})$ and the Weil action twisted by the character `chainChar ϑ (k+1)`, times the index $[J^\circ : J_k(\vartheta)]$. Here $J^\circ$ is the stabiliser of the standard lattice, $J_k(\vartheta) = $ `levelY ϑ k` is its subgroup of elements congruent to $1$ at the places of the level, and $J_M = $ `chosenLevel` is the subgroup of elements congruent to $1$ at the two chosen places. The lower chain up to $k$ is $\iota_{k-1}\circ\cdots\circ\iota_0$ (Lean: `New.Data.lowerChainUpTo`). The source function $\mathcal{W}_\varphi$ on $R_0$ of a source form $\varphi$ and a linear form $t$ is the equivariant function of [Bessel periods](/chapter/bessel-periods/) (Lean: `New.Grading.sourceFn`).

The chapter uses one step of unfolding from [Bessel periods](/chapter/bessel-periods/), stated here in one line. For an equivariant $W$ on the Bessel group $R$ of a grading $\mathsf{Y}$ of $V$, a grading $\mathsf{Y}'$ of $V'$ with a string one shorter, a datum $\Phi$ on $\operatorname{Hom}(V, V')$ and an automorphic rapidly decreasing $y$ on $U(V')$, the function $W'(h) = \int_{[R]} W(r)\,\mathrm{CT}(r, h)\,dr$ (Lean: `New.Grading.unfoldStep`) satisfies

$$\int_{[R]} W(r) \int_{[U(V')]} \theta(r, h)\, y(h)\, dh\, dr = \int_{R'(E)\backslash U(V')(\mathbb{A})} W'(h)\, y(h)\, dh,$$

and the right side converges absolutely ([the theorem](/decl/New.Grading.integral_besselGroup_unfold/)). The adjointness of a theta lift and its transpose is in [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/).

### The functions of the unfolding

The unfolding is done at outer variables. For each $k$ fix an archimedean point $\xi_k$ and a finite adelic point $y_k$ of $G_k$, and put $g_k = (\xi_k, y_k)$. Move the datum of lift $k + 1$ by $g_k$: the moved datum is $\omega(g_k, 1)\Phi_k$ (Lean: `New.Data.movedDatum`).

**Definition (Functions of the unfolding).** Define functions $W_k$ on $R_k$ for $k \leq 2\varrho + 1$ by recursion:

$$W_0 = \mathcal{W}_\varphi, \qquad W_{k+1}(\gamma) = \mathcal{W}_{k+1}(\gamma\, g_{k+1}),$$

where, for a grading $\mathsf{Y}'$ of $Y_{k+1}$, the function $\mathcal{W}_{k+1}$ on $G_{k+1}$ is the unfolded function of $W_k$ for the grading $\mathsf{Y}_k$, the grading $\mathsf{Y}'$, the moved datum of lift $k + 1$ and the twist of lift $k + 1$:

$$\mathcal{W}_{k+1}(h) = \int_{[R_k]} W_k(r)\, \mathrm{CT}\bigl(\omega(r, h)\,\omega(g_k, 1)\Phi_k\bigr)\, dr.$$

Lean: `New.Data.unfoldStageOn`, `New.Data.unfoldStage`, `New.Data.unfoldStageOn_zero`, `New.Data.unfoldStageOn_succ` (New/UpperBound/Seesaw/UnfoldingStages.lean).

So $W_k$ is the function that the first $k$ steps of unfolding leave, restricted to $R_k$ and translated by $g_k$. The two equations of the recursion hold by `rfl`; in the second, $\mathcal{W}_{k+1}$ is taken with $\mathsf{Y}' = \mathsf{Y}_{k+1}$. The outer variable $g_0$ enters $W_1$ through the moved datum; it is the point at which the Poincaré series is evaluated.

**Lemma.** The function $\mathcal{W}_{k+1}$ depends only on the outer variables $g_j$ with $j \leq k$.

Lean: `New.Data.unfoldStage_update`.

*Proof.* By induction on $k$, $W_k$ depends only on $g_j$ for $j \leq k$ (Lean: `New.Data.unfoldStageOn_update`). The function $\mathcal{W}_{k+1}$ is built from $W_k$ and the moved datum $\omega(g_k, 1)\Phi_k$. $\square$

**Remark (Formalization).** The recursion is on a natural number $k$ with a proof of $k \leq 2\varrho + 1$, because the grading $\mathsf{Y}_k$ exists only in that range; $Y_{2\varrho+2}$ has the empty string and gets the separate grading `New.Data.lastGrading`. The outer variables are given as functions $\xi, y$ on all of $\mathbb{N}$, and only the values at indices $\leq k$ matter, by the lemma. The function $\mathcal{W}_{k+1}$ takes the grading $\mathsf{Y}'$ of $Y_{k+1}$ as an argument, with a string of any length; the integrability statements of Section 5 need the length $s_{k+1}$.

### The theorem of the chapter

For a form $z$ of the conjugate type on $Y_{k+1}$ and a grading $\mathsf{Y}'$ of $Y_{k+1}$ with a string of length $s_{k+1}$, put

$$\Xi_{k+1}(\xi, y) = \int_{R'(E)\backslash G_{k+1}} \mathcal{W}_{k+1}(h)\, z(h)\, dh,$$

where $R'$ is the Bessel group of $\mathsf{Y}'$ (Lean: `New.Data.unfoldedPeriod`). This is the period left after $k + 1$ steps. The chapter ends with the following theorem. Its formal proof is in the file of [part 2](/chapter/seesaw-identity-2/), and it uses the results of every section of this chapter.

**Theorem (The pairing as a cut sum).** Fix $t$, an archimedean point $g$ of $G_0$, $k \leq 2\varrho + 1$, a grading $\mathsf{Y}'$ of $Y_{k+1}$ with a string of length $2\varrho + 1 - (k+1)$, and a function $a$ of the archimedean tuples $\xi$. There is $c \in \mathbb{C}$ with the following property. Let $\vartheta$ be a tame character, $\varphi$ a ramified source form, $z$ a form of the conjugate type on $Y_{k+1}$, and $S$ a function on the tuples of classes $(y_i J_i(\vartheta))_i$. Suppose that $\Xi_{k+1}(\xi, y) = a(\xi)\, S\bigl((y_i J_i(\vartheta))_i\bigr)$ whenever $y_0 \in J_M$ and $y_{2\varrho+2} = 1$. Then

$$\int_{[G_{k+1}]} z(h)\, (\iota_k\circ\cdots\circ\iota_0)(\mathcal{P}\varphi)(h)\, dh = c\cdot \sum_{c_0 \in \Omega_0}\cdots\sum_{c_k \in \Omega_k} \frac{S(c_0, \ldots, c_k, 1, 1, \ldots)}{m_0(c_0)\cdots m_k(c_k)}.$$

Lean: `New.Data.exists_integral_mul_lowerChainUpTo_eq_cutSum` (New/UpperBound/Seesaw/SeesawIdentity.lean).

Here $\Omega_j$ is a finite set of classes of $G_j^{\mathrm{fin}}/J_j(\vartheta)$ and $m_j$ is a positive integer multiplicity on it, both built in Section 7; the sum on the right is `New.Data.cutSum`. The constant $c$ depends on $t$, $g$, $k$, $\mathsf{Y}'$ and $a$, but not on $\vartheta$, $\varphi$, $z$ or $S$. The constant can be $0$; Section 7 explains where it comes from.

The base case $k = 0$ is the unfolding of the Poincaré series:

**Theorem (The first lift of the Poincaré series).** For every grading $\mathsf{Y}'$ of $Y_1$ with a string of length $2\varrho$ and every form $z$ of the conjugate type on $Y_1$,

$$\int_{[G_1]} z(h)\, \iota_0(\mathcal{P}\varphi)(h)\, dh = [J^\circ : J_M] \sum_{c \in \Omega_0} \Xi_1\bigl((g, 1, 1, \ldots), (c^{\mathrm{out}}, 1, 1, \ldots)\bigr),$$

where $\Omega_0$ is the set of classes modulo $J_0(\vartheta)$ of the elements of $J_M$, and $c^{\mathrm{out}}$ is a chosen representative of $c$.

Lean: `New.Data.integral_mul_liftY_poincareAt` (New/UpperBound/Seesaw/SeesawIdentity.lean).

*Proof.* Move the lift to $z$: $\int z\cdot \iota_0(\mathcal{P}\varphi) = \int \iota_0^{t}(z)\cdot \mathcal{P}\varphi$, where $\iota_0^t$ is the transposed lift, times the same index (Lean: `New.Data.integral_mul_liftY`). The form $\iota_0^t(z)$ is right invariant under $J_0(\vartheta)$. The defining property of $\mathcal{P}$ ([the objects of the upper bound](/chapter/upper-bound-objects/)) gives

$$[J_M : J_0(\vartheta)] \int_{[G_0]} \iota_0^t(z)\, \mathcal{P}\varphi = \sum_{q \in J_M/J_0(\vartheta)} \int_{[R_0]} \mathcal{W}_\varphi(r)\, \iota_0^t(z)\bigl(r\,(g, q)\bigr)\, dr$$

(Lean: `New.Data.integral_mul_poincareAt`). The sum over $J_M/J_0(\vartheta)$ is the sum over $\Omega_0$, since the summand is right invariant under $J_0(\vartheta)$. By the stage identity of Section 5 each term is $[J^\circ : J_0(\vartheta)]\,\Xi_1$. Divide by $[J_M : J_0(\vartheta)] \neq 0$ and use $[J^\circ : J_0(\vartheta)] = [J^\circ : J_M][J_M : J_0(\vartheta)]$. $\square$

*Proof of the theorem on the cut sum (outline).* Induction on $k$. For $k = 0$ the multiplicities on $\Omega_0$ are $1$, and the previous theorem gives the claim with $c = [J^\circ : J_M]\, a(g, 1, \ldots)$. For the step from $k$ to $k + 1$, move the last lift to $z$ and apply the claim for $k$ to the function $S'$ that is the integral over $[R_{k+1}]$ against the descent of $z$. By the stage identity of Section 5 that integral is $[J^\circ : J_{k+1}(\vartheta)]\,\Xi_{k+2}$, as a function of $y_{k+1}$. The theorem of Section 7 on the integral as a coset sum turns the integral over the finite points into $\kappa \sum_{c \in \Omega_{k+1}} m_{k+1}(c)^{-1}(\ldots)$, with a number $\kappa$ that does not depend on $\vartheta$. The support theorem of Section 6 shows that only points with bounded lattices contribute, which is what makes $\Omega_{k+1}$ finite and the multiplicities nonzero. $\square$

### The plan of the chapter

Section 2 defines admissible combinations: finite sums with controlled denominators and sizes, in which every term of the cut sum is expressed. Section 3 computes the standard lattices of the gradings $\mathsf{Y}_k$, and Section 4 the frequencies of a constant term and the evaluation of two lifts at once. Section 5 proves the stage identity and evaluates $\mathcal{W}_{k+1}$ after each pair of lifts. Section 6 proves the support theorem: for a ramified source form, $\mathcal{W}_{k+1}$ vanishes outside points with bounded lattices. Section 7 writes the integral over finite points as a sum over cosets and builds the cut $\Omega_j$, $m_j$. Section 8 has exercises and notes.
