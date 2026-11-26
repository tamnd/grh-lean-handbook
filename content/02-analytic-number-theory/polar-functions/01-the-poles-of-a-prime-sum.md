---
title: The poles of a prime sum
lean:
  - Lib/Analytic/EntireLFunction.lean
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The poles of a prime sum

This chapter gives the background for one step of the proof: the step that reads the zeros of L-functions off the poles of a transform of a sum over primes. The classical form of this step is the explicit formula. It writes a prime sum as a main term plus a sum over the zeros of L-functions. The source does not prove an explicit formula in this form. It proves a weaker statement about poles, and it packs that statement in one definition, the notion of a *polar function*. This chapter states the classical theory with sources, then defines the polar functions of the source, proves their elementary properties, and explains the form of the explicit formula that the source proves. A remark on the formalization follows each difference between the two forms.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof ends with a one-sided bound for the weighted prime remainder $R_q(x)$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/). [Landau's criterion](/chapter/landau-criterion/) turns that bound into the absence of zeros of the L-functions modulo $q_0$ in a half-plane. The bridge between the bound and the zeros is a statement about the transform
$$\Phi(s) = \int_1^\infty R_q(y)\, y^{-s}\, dy = \int_0^\infty R_q(e^v)\, e^{(1 - s)v}\, dv.$$
The source proves that $\Phi$ continues to a meromorphic function on $\mathbb{C}$, that its poles in $\operatorname{Re} s > 0$ are at most simple, and that the residue at a pole is a count of zeros. In the language of the source, $v \mapsto R_q(e^v)$ is polar with these residues. Landau's lemma ([Landau's theorem](/chapter/landau-theorem/)) then needs only this information.

Volume 1 proves the explicit formula of the source for $R_q$ in full, and Volume 1 uses it. This chapter does not repeat that proof. It gives the theory around it: why a transform of a prime sum has poles at the zeros, why the residues are orders of zeros, what the classical explicit formula says in addition, and what the notion of a polar function keeps and what it drops. The Dirichlet L-functions $L(s, \chi)$, the entire functions $\tilde L(s, \chi)$ and their basic properties are the subject of [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/). This chapter uses them and does not treat them again.

### The notation

The notation is that of Volume 1. For a Dirichlet character $\chi$ modulo $N \geq 1$, $\tilde L(s, \chi)$ is $L(s, \chi)$ if $\chi$ is not principal, and the entire function $(s - 1)L(s, \chi)$ if $\chi$ is principal. For $\rho \in \mathbb{C}$, $\operatorname{ord}_\rho f$ is the order of the zero of an analytic function $f$ at $\rho$, and it is $0$ if $f(\rho) \neq 0$. Fix a prime $d$, let $\chi_K = (\cdot/d)$, and for a character $\psi$ modulo $q$ let $\psi\chi_K$ be the twist, a character modulo $qd$. Put
$$n(\rho) = \sum_{\psi \bmod q} \operatorname{ord}_\rho \tilde L(\cdot, \psi), \qquad n_K(\rho) = \sum_{\psi \bmod q} \operatorname{ord}_\rho \tilde L(\cdot, \psi\chi_K).$$
The remainder $R_q$ and the constant $c_q$ are those of [the weighted prime remainder](/chapter/weighted-prime-remainder/).

### The main results in brief

The chapter has three results of the source and two classical results.

1. The residue of a logarithmic derivative. For every Dirichlet character $\chi$ and every $\rho \in \mathbb{C}$, $(z - \rho)\tilde L'/\tilde L(z, \chi) \to \operatorname{ord}_\rho \tilde L(\cdot, \chi)$ as $z \to \rho$. This is the local fact behind every explicit formula (Section 2).
2. The classical explicit formula for $\psi(x)$ and for the weighted sum $\sum_{n \leq x} \Lambda(n)(1/n - 1/x)$, with the sources (Section 3).
3. The definition of a polar function, and its elementary properties: linearity, the residues of an exponential, and the fact that a two-sided bound kills the poles (Section 4).
4. The explicit formula of the source: $v \mapsto R_q(e^v)$ is polar with the residues
$$r(s) = \frac{n(s) - n_K(s)}{\varphi(q)\, s(1 - s)},$$
for every prime $d \equiv 7 \bmod 8$ prime to $q$ (Section 5).

Section 5 also checks a point of the notes: the hypothesis $d \equiv 7 \bmod 8$ of the last result is used only to get $d \neq 2$.

### What the chapter uses

The chapter uses the entire functions $\tilde L$, their non-vanishing on $\operatorname{Re} s \geq 1$, and the Euler product for $\operatorname{Re} s > 1$ ([Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/)). It uses the identity theorem and the local form $f(z) = (z - \rho)^m g(z)$, $g(\rho) \neq 0$, of an analytic function that is not identically $0$. The results of the source in this chapter use no functional equation, no Hadamard product, no zero-free region inside the critical strip, and no count of zeros. The classical explicit formula of Section 3 uses all four. That is the main difference between the two forms, and the reason the source can prove its form with little analysis.

### The sketch

The idea is one line. For $\operatorname{Re} s > 1$ the Dirichlet series of $\chi(n)\Lambda(n)$ is $-L'/L(s, \chi)$. A logarithmic derivative has a simple pole at each zero, with residue the order. A transform of a sum $\sum_{n \leq x} a(n) w(n/x)$ is the Dirichlet series of $a$ times the Mellin transform of the weight. So the transform has a pole at each zero $\rho$, and its residue is the order of the zero times a factor that depends on the weight and on $\rho$. For the weight $1/n - 1/x$ of the source this factor is $1/(\rho(1 - \rho))$ (Section 3). The classical explicit formula goes further: it inverts the transform, moves the line of integration to the left, and sums the residues. The source does not invert the transform. It keeps the poles and their residues, and Landau's lemma does the rest.

Lean accepts the results of the source in this chapter, if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
