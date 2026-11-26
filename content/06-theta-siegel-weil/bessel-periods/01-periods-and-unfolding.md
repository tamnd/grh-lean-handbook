---
title: Periods against a theta kernel
lean:
  - Lib/Weil/Periods/Unfolding.lean
  - Lib/Weil/Periods/DescentVanishing.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Periods against a theta kernel

This chapter studies periods of automorphic functions over Bessel subgroups of unitary groups, and how such a period changes under a theta lift. The main result is one step of an unfolding. Take a hermitian space $V = X \oplus J_s$, where $X$ is definite and $J_s$ is a graded string of $s$ vectors, and a second space $V' = X' \oplus J_{s-1}$ with a string that is one vector shorter. Take a function $W$ on the Bessel group $R$ of $V$ that is equivariant for a generic character, and a rapidly decreasing automorphic function $y$ on $U(V')$. The theorem says that the period of $W$ against the theta lift of $y$ is the period of $y$ against a new function $W'$ on $U(V')$, over the Bessel group $R'$ of $V'$. The new function $W'$ is again equivariant for $R'$. So the step can be repeated, and each step makes the string one vector shorter. The chapter also proves the results on lattices that control the support of $W'$ at the finite places, and a second, simpler unfolding: if all theta descents of a function vanish, then its periods over a block subgroup vanish.

### Where the chapter sits

The source proves its main theorem through a chain of claims. The plan of the chain is in [the theorem and the plan](/chapter/theorem-and-plan/). The results of this chapter are inputs of two parts of it.

The first part is the seesaw of Volume 9. There a double theta integral over two definite unitary groups is written as a coefficient of a composite of theta lifts. The source unfolds the composite one string vector at a time. Each step is an application of the main theorem of this chapter, [Theorem](/decl/New.Grading.integral_besselGroup_unfold/), and each step uses the equivariance of the new function, [Theorem](/decl/New.Grading.isEquivariant_unfoldStep/). The finite support of the functions that the steps leave is controlled by [Theorem](/decl/New.Grading.exists_finite_representatives/), [Theorem](/decl/New.Grading.exists_isGraded/) and [Proposition](/decl/New.Grading.stringMapFin_stringSum/). The chapter [seesaw identity, part 1](/chapter/seesaw-identity-1/) uses these results.

The second part is the study of false lifts in Volume 11. There a form on a definite unitary group is shown to have vanishing periods over a block subgroup, because all its descents to split groups vanish. The tool is [Theorem](/decl/New.SiegelWeil.integral_blockEmb_eq_zero_of_descentsVanish/) of the last section. The chapter [false lifts](/chapter/false-lifts/) uses it.

### The model case

The simplest case shows the mechanism. Let $V$ be a hermitian space over a CM field $E$, and let $e \in V(E)$ be a vector with $\langle e, e \rangle = -N \neq 0$. Put $X = e^{\perp}$, and suppose that $X$ is definite. The stabiliser $H$ of $e$ in $U(V)$ is $U(X)$. Let $V'$ be a second hermitian space, and let $\theta(g, h)$ be a theta kernel on $U(V)(\mathbb{A}) \times U(V')(\mathbb{A})$, built from a datum $\Phi$ on $\operatorname{Hom}(V, V')$. For an automorphic $y$ on $U(V')$ and an automorphic $W$ on $U(X)$, consider the period

$$P = \int_{[U(X)]} W(r) \int_{[U(V')]} \theta(r, h)\, y(h)\, dh\, dr .$$

Here $[G]$ is $G(E) \backslash G(\mathbb{A})$. The theta kernel is a sum over the rational maps $w \colon V \to V'$. In a model where the theta kernel is $\theta(r, h) = \sum_{w} (\omega(r, h)\Phi)(w)$, change the order of the two integrals and of the sum. The sum over $w$ breaks into orbits of $U(V')(E)$. The orbit of $w$ is determined by the restriction of $w$ to the span of $e$, up to the Gram data of $w$. In the case $s = 1$ the source has no unipotent part, the Bessel group is $H$ itself, and the computation is only an exchange of integrals. In the case $s = 2$ the Bessel group is the stabiliser of an isotropic vector $e_0$. It is a Heisenberg group times $U(X)$, and the function $W$ transforms by a character of the centre of the Heisenberg group. A Fourier expansion along the centre kills every orbit of maps $w$ except those with $\langle w e_0, w e_0 \rangle = -N c^2$, for the constant $c$ of the character. By Witt's theorem these maps form one orbit under $U(V')(E)$, with representative $T$, and the stabiliser of $T$ is the Bessel group $R'$ of $V' = X' \oplus \langle e_0' \rangle$. The period becomes

$$P = \int_{R'(E) \backslash U(V')(\mathbb{A})} W'(h)\, y(h)\, dh, \qquad W'(h) = \int_{[R]} W(r)\, \mathrm{CT}\big(\omega(r, h)\Phi\big)(T)\, dr,$$

where $\mathrm{CT}$ is a constant term of the theta function along the maps of positive degree. The general step has the same three parts: a Fourier expansion of the theta function, a vanishing for the orbits that do not survive, and Witt's theorem for the orbits that survive.

### The plan of the chapter

Section 2 sets up the graded spaces $X \oplus J_s$. It defines the grades, the vectors $\mathfrak{e}^i$, the shift $\mathfrak{e}$, and the map $T \colon V \to V'$. Its main identities are $T^\dagger T = \mathfrak{e}$ and $T T^\dagger = \mathfrak{e}'$.

Section 3 defines the groups: the unipotent group $U$, the embedding of $U(X)$, and the Bessel group $R = U \rtimes U(X)$. It proves that $R(E)$ is cocompact in $R(\mathbb{A})$, defines the generic character $\psi_U$, and defines the equivariant functions $W$. The source function $\mathcal{W}_\varphi$ of an automorphic form $\varphi$ on $U(X)$ is the first such function.

Section 4 is the algebra of surviving orbits. It says which rational maps $w$ survive the unipotent twists, and it moves each survivor to $T$ by a rational point of $U(V')$.

Section 5 proves the unfolding step and the equivariance of the new function.

Section 6 studies the lattices of finite points. It proves an Iwasawa decomposition and a finiteness theorem for the lattices that satisfy given bounds.

Section 7 proves the vanishing of block periods from the vanishing of descents.

Section 8 has exercises and the notes.

### What the chapter uses

The chapter uses the adelic Weil representation $\omega$ on the space $\mathcal{S}(V)$, the Heisenberg operators $\varrho(x)$, and the theta functional $\theta_V$ of [the Weil representation from a vacuum](/chapter/weil-representation/). For $f \in \mathcal{S}(V)$ the source writes $f(x)$ for the theta function $\theta_V(\varrho(x) f)$, so that $f(0) = \theta_V(f)$. The chapter also uses the mixed models of that chapter, the theta kernels and theta lifts of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) and the invariant measures on adelic quotients. The symbol $\psi$ is the standard additive character of $\mathbb{A}_E / E$, and $\jmath$ is the imaginary element of $E$ fixed by the Weil data, with $\bar\jmath = -\jmath$.

**Remark (Formalization).** The source states the step for hook orbits with a definite complement $X$, for unitary groups, and for one step at a time. It cites the general theorem of B. Wang (J. Number Theory 271 (2025), Prop. 3.2 and Thm. 4.5) as the source of the method, but it does not formalize that theorem. The text states the Lean forms. The notes in the last section compare them with the literature.
