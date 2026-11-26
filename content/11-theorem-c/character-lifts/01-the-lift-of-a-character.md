---
title: The lift of a character
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
  - New/OneLift/TestedForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The lift of a character

This chapter studies one special theta lift. The source is the unitary group $U(1)$ of a definite hermitian line $W$ over a CM field $E$. The target is the unitary group of the standard definite space $V = I_N$ of rank $N \geq 2$. The form that we lift is the constant function $1$ on $U(1)(\mathbb{A})$, and the theta kernel carries a character $\mu$ of $U(1)$ and a weight with one row at each infinite place. The result is an algebraic form $\varphi_X$ on $V$. We call it the lift of the character. The chapter proves three things about it. Its inner products with other forms are class sums of descents. Its squared norm is an explicit multiple of the critical value $L(k, \mu^{-1})$ when $N = 2k$. Its Galois conjugates are, up to simple factors, the lifts of the conjugate characters. The last part of the chapter is about a different object, the tested forms: integral forms on $V$ that are orthogonal to the false lifts. For these forms the projection to a space of lifts does not increase any conjugate norm.

### Where the chapter sits in the argument

The plan of Theorem C is in [Theorem C and the height argument](/chapter/theorem-c-plan/). The algebraic part $L^{\mathrm{alg}}(z, \nu\vartheta)$ of a critical value is defined in [twists, critical pairs and regular families](/chapter/twists-critical-pairs/) as $\|\varphi\|^2 / N(Q)^{2z-1}$, where $\varphi$ is a scaled lift of the character $\nu\vartheta$. That definition uses the objects of this chapter. The formula that makes $L^{\mathrm{alg}}$ a multiple of an $L$-value is the main theorem of Section 6.

The previous chapter, [single theta lifts and their norms](/chapter/single-theta-lifts/), lifts forms from a space $W$ of any rank $r < N$. It uses two general lemmas that the source puts in the first file of this chapter. The first compares the class sum inner product on algebraic forms with the Petersson product of the functions on the adelic group. The second says that a form whose Hecke polynomials are those of a lift is killed by the Hecke polynomial operator at one explicit number $x_w$. Section 2 and Section 5 state and prove these two lemmas in full.

The later chapters use the rest. The Galois law of Section 7 enters [Hecke values of character lifts](/chapter/hecke-values/), where it bounds the heights of twisted values. The tested forms of Section 8 enter the same chapter, the chapter [false lifts](/chapter/false-lifts/), and the height bound of [the height of one lift determinant](/chapter/lift-volume-height/).

### The model case

Take $E$ imaginary quadratic, so that there is one infinite place. Take no chosen places and no twist places, row length $0$, and a character $\mu$ of $U(1)(\mathbb{A})$ of weight $-k$ that is unramified at every finite place. Put $N = 2k$ with $k \geq 2$. The integral points of $U(1)(\mathbb{A}_f)$ form a compact open group $K$. The double cosets $U(1)(E) \backslash U(1)(\mathbb{A}_f) / K$ form a finite set. For each point $g$ the theta kernel $\theta_X(g)$ is the scalar theta function of the vacuum, twisted by $\mu$, as a function of $h \in U(N)(\mathbb{A}_f)$. The lift is the finite sum

$$\varphi_X(h) = \sum_{[g]} \frac{1}{\#\mathrm{Aut}(g)}\, \theta_X(g)(h).$$

Its Petersson norm is computed by the Rallis inner product formula of [the Rallis inner product formula](/chapter/rallis-inner-product/), in which the coefficients of the vacuum add up to a partial $L$-value divided by a partial value of $\zeta_F$. For the model case the result of Section 6 reads

$$\langle\varphi_X, \varphi_X\rangle = C \cdot L(k, \mu^{-1}), \qquad C = \frac{\mathrm{vol}[U(N)]\,\mathrm{vol}[U(1)]}{\zeta_F(2k)} \neq 0,$$

because all products over places are empty, the hook number of the empty weight is $1$, and the weight has dimension $1$. The general case adds a factor at each chosen place and at each twist place, and the size of the weight.

### The three files

The source has three files for this chapter.

- `New/OneLift/HeckeValues/CharacterLift.lean` defines the data `LValueData`, the descent pair with a line as source, the kernel and the lift. It proves the comparison with the Petersson product, the adjointness of the lift and the descent, the root lemma for Hecke polynomials and the Galois law.
- `New/OneLift/HeckeValues/CharacterLiftNorm.lean` defines the scaled lift of a critical pair and the algebraic part, and proves that the lift is a multiple of the theta lift of $1$. It computes the indices and masses at the level and proves the norm formula.
- `New/OneLift/TestedForms.lean` defines point forms, false lifts, test forms and the denominator bound, and proves the adjoint law of the Hecke polynomials and the projection bound.

No file of the chapter imports a file of a later chapter of this volume. The imports are files of Volumes 4 to 9 and of [single theta lifts and their norms](/chapter/single-theta-lifts/).

### Notation

We keep the notation of [single theta lifts and their norms](/chapter/single-theta-lifts/). $E$ is a CM field with maximal real subfield $F$, and the infinite places $\tau$ of $E$ are the places of a CM type. $V = I_N$ is the standard definite space with index set $n$ and $N = \#n$. $G_f = U(V)(\mathbb{A}_f)$ and $K_0 = $ `stdLevel E n` is the stabilizer of the standard lattice. A descent pair $O$ has a space $W$, places $M$ (the chosen places) and $Q$ (the places of the twist), a weight $\kappa$ and characters $\nu_W$, $\nu_V$. Its space of forms is $\mathcal{A}(O)$ = `O.FormV`: algebraic forms on $V$ of weight $\kappa$ on which the level $K$ acts by a character. The inner product of two forms is the class sum

$$\langle\Xi, \Xi'\rangle = \sum_{[g] \in \Gamma\backslash G_f/K} \frac{1}{\#(\Gamma \cap gKg^{-1})}\, \langle\Xi(g), \Xi'(g)\rangle_{\mathrm{Gram}},$$

with $\Gamma$ the rational points and $\langle\cdot,\cdot\rangle_{\mathrm{Gram}}$ the hermitian form of the integral Gram matrix of the weight. It is conjugate linear in the first variable. The class sums and their laws are in [automorphic forms on definite unitary groups](/chapter/automorphic-forms/) of Volume 4.

### The order of the sections

Section 2 compares the class sum product with the Petersson product and introduces forms supported on one class. Section 3 defines the data, the kernel and the lift, and proves that the lift does not depend on a translation. Section 4 shows that the descent is the inner product with the kernel and that the lift is a multiple of the theta lift of $1$. Section 5 is about Hecke polynomials. Section 6 proves the norm formula. Section 7 proves the Galois law. Section 8 treats tested forms. Section 9 has exercises and notes.
