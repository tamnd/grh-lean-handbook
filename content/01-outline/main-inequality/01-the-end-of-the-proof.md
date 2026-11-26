---
title: The end of the proof
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The end of the proof

This chapter closes the argument of the source. It proves the half-plane form of the generalized Riemann hypothesis: for every modulus $q \geq 1$, every Dirichlet character $\chi$ modulo $q$ and every $s$ with $\operatorname{Re} s > 1/2$, $L(s, \chi) \neq 0$, except at the pole $s = 1$ of a principal character. [From the half-plane to the line](/chapter/half-plane-to-line/) deduces the five theorems of the source from this statement. So this chapter is the last step above Theorems A, B and C. Lean accepts the steps of this chapter, if the checks that the source reports hold. This chapter explains the mathematics of these steps. It does not say that the proof is correct.

### What the chapter proves

The chapter proves four results, in this order.

1. **The main inequality.** For admissible data $D$, $m \cdot \mathrm{rem} \leq f a \log^5 b$. Here $m$ is the number of theta lifts, $\mathrm{rem}$ is the total remainder of the prime sums, $f$ is the number of infinite places of the CM field $E$, $a = xb$ is the long order and $b$ is the large weight. The proof compares an upper bound and a lower bound for the covolume of one family of lattice vectors. The two bounds have the same main term, and it cancels.
2. **The bound at $x$.** The identity of [the prime sums and the total remainder](/chapter/prime-sums/) writes $\mathrm{rem}$ through the weighted prime remainder $R_{q_0}$ at $x$ and at the cut-off $x_1$. Division by $m a \#\Phi_b$ gives $R_{q_0}(x) \leq \varphi(q_0) \log^6 b / m + |R_{q_0}(x_1)| + \log b \, |R_1(x_1)|$.
3. **The one-sided bound.** The prime number theorem for $R_q$, applied at the huge cut-off $x_1$, makes the last two terms smaller than $x^{-2}$. The data have $m \geq \sqrt{x}$ and $\log b \leq 2 x^{\varepsilon}$. So $R_{q_0}(x) \leq (64 \varphi(q_0) + 3) x^{-1/2 + 6\varepsilon}$ for all large integers $x$, and then $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for all large real $y$.
4. **The half-plane theorem.** The criterion of [Landau's criterion](/chapter/landau-criterion/) turns a one-sided bound $R_{q_0}(y) \leq y^{\beta - 1}$, for every prime $d$ in a class modulo $q_0$, into $L(\rho, \psi) \neq 0$ for every character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$. The source applies it with $q_0 = 18480 q$, to the character modulo $q_0$ that $\chi$ induces.

### Where the chapter sits

[The theorem and the plan](/chapter/theorem-and-plan/) gives the shape of the whole argument: the half-plane theorem; the criterion; the one-sided bound; the main inequality; and Theorems A, B and C, which rest on the background of Volumes 2 to 8. This chapter proves the top three arrows. It uses [Theorems A, B and C](/chapter/theorems-a-b-c/), the identity of [the prime sums and the total remainder](/chapter/prime-sums/), the sizes of [the data and its sizes](/chapter/data-and-sizes/) and [the data exist](/chapter/data-exist/), the remainder $R_q$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/), the prime number theorem in progressions for a fixed modulus (Volume 2, [the prime number theorem in progressions](/chapter/prime-number-theorem/)), and [Landau's criterion](/chapter/landau-criterion/). Section 2 recalls the exact statements.

### A model of the main inequality

The main inequality has one idea, and a model shows it. Let $V$ be a real number, the logarithm of a covolume. Suppose that two arguments bound it, one from above and one from below, with the same main term $d \cdot M$:

$$d (M - e_1) \;\leq\; V \;\leq\; n (M - m \cdot \mathrm{rem} + e_2) + e_3,$$

with $0 < n \leq d$, $M + e_2 \geq 0$ and $n \geq d/2$. Then $n(M + e_2) \leq d (M + e_2)$, so the main terms cancel, and

$$n \, m \cdot \mathrm{rem} \;\leq\; d (e_1 + e_2) + e_3, \qquad m \cdot \mathrm{rem} \;\leq\; 2 (e_1 + e_2) + 2 e_3 / d.$$

The point is that $M$ is very large. In the source, $M$ is the main amount, at least $x^4 f a$, while the errors are of size $f a \log^4 b$. Neither bound alone says anything about $\mathrm{rem}$. Only the cancellation of $M$ between them leaves a statement about the primes. Section 3 carries out this model with the exact objects and the exact errors.

### The exponents in one line

The data have $m \in [\sqrt{x}, 2\sqrt{x}]$ and $\log b \leq 2x^{\varepsilon}$, with $0 < \varepsilon < 1/100$ fixed, and $x_1$ so large that the prime number theorem makes $R(x_1)$ smaller than $x^{-2}$. So the bound at $x$ reads

$$R_{q_0}(x) \;\leq\; \frac{\varphi(q_0) (2 x^{\varepsilon})^6}{x^{1/2}} + x^{-2} + 2 x^{\varepsilon} x^{-2} \;\leq\; (64 \varphi(q_0) + 3)\, x^{-1/2 + 6\varepsilon}.$$

The factor $x^{-1/2}$ is $1/m$, and the factor $x^{6\varepsilon}$ is $\log^6 b$. So the exponent $-1/2$ comes from one source: the number $m$ of lifts. Section 7 discusses this fact.

### The plan of the chapter

Section 2 recalls the inputs with their exact hypotheses. Section 3 proves the main inequality and gives the budget of errors for each dimension. Section 4 deduces the bound at $x$. Section 5 proves the prime number theorem at the cut-off. Section 6 proves the one-sided bound for all large real $y$ and the half-plane theorem. Section 7 explains where the exponent $1/2$ comes from, and what is open about it. Section 8 has the exercises and the notes.
