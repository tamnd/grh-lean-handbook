---
title: The chapter
lean:
  - Lib/Adelic/AutomorphicForms/Basic.lean
  - Lib/Weil/DualPair/ThetaLiftConvergence.lean
  - Lib/Weil/Lift.lean
  - Lib/Weil/Seesaw.lean
decls:
  - New.ThetaKernel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter

This chapter builds the global theta lift between two adelic unitary groups and proves the four properties of it that the rest of the argument uses. The lift has moderate growth and converges on forms of rapid decay. Its adjoint is a descent. Along an archimedean "edge" it sends forms of one discrete series type to forms of another type. Finally, a seesaw identity moves a proportionality of periods from a lift to a transposed lift. The chapter also treats two special topics: the lift between definite unitary groups, where it is a finite class sum, and a Galois law for the finite Weil representation.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) reduces the main theorem to three statements on automorphic forms on unitary groups. Theorem A says that certain theta lifts are short, and Theorem C gives a lower bound that comes from heights. Both theorems reach the forms that they measure through theta lifts. The proof of Theorem A ([its plan](/chapter/theorem-a-plan/)) uses the edges of this chapter to build its chains of forms in [the objects of the upper bound](/chapter/upper-bound-objects/), and it uses the Galois law for the conjugates of theta jets in [theta kernels and gauges](/chapter/theta-kernels-gauges/). The Galois law enters the proof of Theorem C as well, in [Hecke values](/chapter/hecke-values/). The proof of Theorem C ([its plan](/chapter/theorem-c-plan/)) uses the seesaw for periods and the definite lift in [grids, columns and turns](/chapter/grids-paths-turns/), the decay of theta kernels in [seesaw squares](/chapter/seesaw-squares/), and the edges again in [the chain determinant](/chapter/chain-determinant/).

### What the chapter uses

The chapter uses three earlier pieces.

1. The adelic groups, the hermitian spaces with a point and the rational points $\Gamma_S$ of [adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/), and the height $\operatorname{ht}_S$ and Mahler's criterion of [reduction theory](/chapter/reduction-theory/).
2. Automorphic functions, the Petersson product, functions of moderate growth and of rapid decay, and forms of a type of [automorphic forms](/chapter/automorphic-forms/). A form of type $e$ is a bounded automorphic function $F$ with $F * e = F$ for the right convolution by a kernel $e$ on the real points. The discrete series kernels $e = e_l$ of [discrete series](/chapter/discrete-series/) give the types that occur here.
3. The Weil representation $\omega$ on the Banach space $\mathcal{S}(V)$ of data, its theta functional $\theta$ and its Fock model at the real places, from [the Weil representation from a vacuum](/chapter/weil-representation/), and the local theory of joint harmonics from [local theta in the Fock model](/chapter/local-theta/).

### Notation

$E$ is a CM field, and $F$ is its totally real subfield. A space $S$ is a hermitian space over $E$ with $n$ coordinates, signs $s = (s_1, \dots, s_n)$ at the real places and a point in $\mathrm{GL}_n(\mathbb{A}_E)$. Its adelic unitary group is $G_S = G_{S,\infty} \times G_{S,f}$, and $[S] = \Gamma_S \backslash G_S$ carries the finite measure of [automorphic forms](/chapter/automorphic-forms/). A second space $T$ has $n'$ coordinates and signs $t$. The letters $g, k$ denote points of $G_S$, and $h, l$ denote points of $G_T$. We write $\operatorname{ht}_S(g)$ for the height of $g \in G_S$. It is at least $1$, and it is large when the lattice moved by $g$ has a short vector.

### The model case

The classical case is the theta lift for $\mathrm{SL}_2 \times \mathrm{O}(V)$, with $V$ a positive definite rational quadratic space of even dimension $m$ and an even lattice $L \subset V$. The theta series $\theta_L(\tau) = \sum_{x \in L} e^{\pi i \tau Q(x)}$ is a modular form of weight $m/2$ for a congruence group (Serre, *A Course in Arithmetic*, Chapter VII, Section 6). In adelic language, $\theta_L(\tau)$ is a value of the kernel $(g, h) \mapsto \theta(\omega(g, h)\varphi)$ on $\mathrm{SL}_2(\mathbb{A}) \times \mathrm{O}(V)(\mathbb{A})$, where $\varphi$ is the Gaussian at infinity times the characteristic function of $L \otimes \hat{\mathbb{Z}}$, and $\theta(\varphi) = \sum_{\xi \in V(\mathbb{Q})} \varphi(\xi)$. Integrating the kernel against a function $y$ on $\mathrm{O}(V)(\mathbb{Q}) \backslash \mathrm{O}(V)(\mathbb{A})$ gives a modular form. This is the theta lift. Since $\mathrm{O}(V)(\mathbb{R})$ is compact, the integral is a finite sum over the classes in the genus of $L$. Section 6 treats the unitary form of this finite case.

In this chapter both groups are unitary, and both can be indefinite. The data lie on the space $\operatorname{Hom}(S, T)$ of $n' \times n$ matrices, and the pair $(g, h)$ acts by $x \mapsto h x g^{-1}$.

### The abstract kernel

The growth estimates and the adjointness of Section 3 do not need the Weil representation. They need only the following structure.

**Definition (Theta kernel).** Let $S$ and $T$ be spaces, and let $X$ be a complex normed space. A theta kernel for $S$ and $T$ on $X$ consists of a homomorphism $\omega$ from $G_S \times G_T$ to the continuous linear maps of $X$, and a continuous linear functional $\theta$ on $X$, with two properties. First, the map $((g, h), \varphi) \mapsto \omega(g, h)\varphi$ is jointly continuous. Second, for $\gamma \in \Gamma_S$, $\gamma' \in \Gamma_T$, all $g, h$ and all $\varphi \in X$,
$$\theta(\omega(\gamma g, \gamma' h)\varphi) = \theta(\omega(g, h)\varphi).$$
The function $(g, h) \mapsto \theta(\omega(g, h)\varphi)$ is the kernel of $\varphi$.

Lean: `New.ThetaKernel` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Remark (Formalization).** The structure does not ask that $\omega$ be unitary or that $\theta$ be the theta distribution. Every estimate of Section 3 is proved from joint continuity and the invariance alone. Section 2 gives the instance that the argument uses, the Weil representation of $\operatorname{Hom}(S, T)$ with its theta functional. In the source that functional is chosen, and it is fixed only up to a scalar of modulus one ([the Weil representation from a vacuum](/chapter/weil-representation/)). A scalar of modulus one does not change any statement of this chapter, since each statement is linear in $\theta$ or states a bound on $\|\theta\|$ that holds for every choice.

### A sketch

Section 2 defines the Weil representation $\omega_{a,b}$ of $G_S \times G_T$ on data for $\operatorname{Hom}(S, T)$, twisted by two characters $a, b$ of the norm one ideles. It defines the data $v \otimes \Psi \otimes \mathrm{vac}$, made of a Fock vector $v$ at infinity and a function $\Psi$ on matrices modulo an ideal $\mathfrak{m}$. It proves the seesaw identities for the kernels of these data: on a direct sum of spaces the kernel is a product.

Section 3 proves moderate growth: $|\theta(\omega(g, h)\varphi)| \leq C \|\varphi\| (\operatorname{ht}_S(g) \operatorname{ht}_T(h))^A$. The proof moves $g$ and $h$ by rational points into a compact set times a short product of real points. The lift $\mathcal{L}_\varphi y(h) = \int_{[S]} \theta(\omega(g, h)\varphi) y(g)\,dg$ then converges for $y$ of rapid decay, and Fubini's theorem gives the adjointness of lift and descent. The section also states the rapid decay of the kernel in $g$ for data supported on matrices of full rank at a split place.

Section 4 defines an edge: a Fock vector $\Phi$ at infinity such that the lift with $\Phi$ sends forms of type $e$ to forms of type $e'$, and back with the conjugate types. Joint harmonics of corresponding parameters are edges. This is the point where [local theta in the Fock model](/chapter/local-theta/) enters. An edge and a finite datum give an arrow, a datum for which the lift is a linear map between spaces of forms.

Section 5 proves the seesaw for periods. If the kernels of two pairs agree up to moderate weights on a spanning set of polynomials, then a proportionality of sums of periods passes from the lifts of one pair to the transposed lifts of the other. The proof is Fubini's theorem, the convolution property of edges, and a density argument in the Fock space.

Section 6 treats the definite case, where the lift with a joint harmonic is a constant times a class sum built from Taylor coefficients of theta series. It also states the Galois law $L(\omega(g)f) = (\sigma(\Delta_g)/\Delta_g)\, \omega(g) L(f)$ for semilinear maps $L$ that scale translations, and a local Gauss sum. Section 7 has exercises and notes.
