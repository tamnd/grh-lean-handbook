---
title: The total remainder in the argument
lean:
  - New/Reduction/PrimeSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The total remainder in the argument

This chapter defines the arithmetic amounts that the lattice argument compares, and it proves one identity about them. The amounts are the prime sums $s_{\mathrm{fin}}(y, \sigma)$, the jet sizes $s_\infty(j)$, the direction amount, the main amount, the expected value $s_{\mathrm{main}}$ and the total remainder $\mathrm{rem}$. The identity is

$$\mathrm{rem} = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a\, R_1(x_1)\Bigr).$$

It writes the total remainder, which the lattice argument bounds, through the weighted prime remainder $R_q$, which Landau's criterion needs. It is the only place in the proof where the places of the field $E$ meet the prime remainder. The chapter proves it in full and checks it by hand in a small case.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) has five layers. At the top, [Landau's criterion](/chapter/landau-criterion/) turns a one-sided bound $R_{q_0}(y) \leq y^{-1/2 + \eta}$ for every prime $d$ in a class into the absence of zeros in $\operatorname{Re} s > 1/2 + \eta$. Here $\eta > 0$ is a margin; Section 6 takes $\eta = 6\varepsilon$, with $\varepsilon$ the exponent of the scales of the data. At the bottom, Theorems A, B and C give the main inequality

$$m \cdot \mathrm{rem} \leq f\, a\, (\log b)^5$$

([the main inequality and the end of the proof](/chapter/main-inequality/)). The identity of this chapter connects the two layers. With it, the main inequality becomes an upper bound for $R_{q_0}(x)$, with error terms at the second scale $x_1$ that the prime number theorem controls. Section 6 makes this deduction.

The heuristic reason that a lattice can bound a prime sum is in [why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/). That chapter explains that the shortness bound of Theorem A contains the term $\mathrm{main} - m \cdot \mathrm{rem}$, with $\mathrm{main}$ the main amount of Section 3, so that a positive total remainder makes the short vectors shorter. This chapter gives the exact definitions of the two terms.

### What the chapter uses

The chapter uses three earlier chapters of this volume.

1. The weighted prime remainder $R_q(z)$ and the weight $\Lambda_K(n) = \Lambda(n)(1 - \chi_K(n))$, from [the weighted prime remainder](/chapter/weighted-prime-remainder/). Section 2 recalls them.
2. The modulus $q_1 = q_0 \cdot 3 l_0 2^s$, with $s$ the tower exponent of the data and $l_0 = 3^{\lfloor \log_3 s \rfloor + 4}$ (Lean: `New.Parameters.q₁`), the field $E = K(\zeta_{q_1})$ with $\zeta_{q_1}$ a primitive root of unity of order $q_1$, and its group $\Phi \cong (\mathbb{Z}/q_1\mathbb{Z})^\times$ of infinite places, from [fields, places and twists](/chapter/fields-places-twists/).
3. The data $D$, its scales $x$, $x_1$, $b$, $a = xb$, its sets of places $\Phi_a$ and $\Phi_b$, its weights $\kappa$, and the table of sizes, from [the data and its sizes](/chapter/data-and-sizes/).

The chapter uses no analytic input. Every proof is a finite computation with sums over $1 \leq \nu \leq a$ and over places. The only estimates are the elementary bound $\sum_{n \leq y} \Lambda(n)/n \leq 2 \log y$ and, in a forward result of Section 4, the Stirling bound for $\log a!$.

### The idea of the identity

Three observations give the identity. Each is one line.

*A weight is a cut-off.* For $z > 0$ and an integer $a \geq z$,

$$\Bigl(\frac{a}{\nu} - \frac{a}{z}\Bigr)_+ = a\Bigl(\frac{1}{\nu} - \frac{1}{z}\Bigr)_+ .$$

So a prime sum with the kernel $(a/\nu - \kappa)_+$ and the weight $\kappa = a/z$ is $a$ times a prime sum of length $z$. The data give each place one of two weights: $\kappa = b = a/x$ on the set $\Phi_b$ and $\kappa = a/x_1$ on the other places. So each place sees a prime sum of length $x$ or of length $x_1$.

*Two weights telescope.* Write the term at a place $\sigma$ as the term of weight $a/x_1$, plus a correction if $\sigma \in \Phi_b$:

$$\Bigl(\frac{a}{\nu} - \kappa(\sigma)\Bigr)_+ = \Bigl(\frac{a}{\nu} - \frac{a}{x_1}\Bigr)_+ + \mathbf{1}_{\Phi_b}(\sigma)\Bigl[\Bigl(\frac{a}{\nu} - \frac{a}{x}\Bigr)_+ - \Bigl(\frac{a}{\nu} - \frac{a}{x_1}\Bigr)_+\Bigr].$$

The correction gives the difference of the prime sums of lengths $x$ and $x_1$. Their constants cancel. This is the term $R_{q_0}(x) - R_{q_0}(x_1)$.

*The mean over $\Phi_a$ sees only $q_0$.* The prime sum $s_{\mathrm{fin}}(a, \tau)$ asks if the place $-\nu\tau$ lies in $\Phi_b$. That condition depends on $\nu$ modulo $q_1$. The total remainder sums over the places $\tau \in \Phi_a$, the places of class $1$ modulo $q_0$. After this sum, the number of $\tau$ with $-\nu\tau \in \Phi_b$ is $\#\Phi_b$ if $\nu \equiv 1 \bmod q_0$, and $0$ otherwise. So the modulus $q_1$ disappears, and only the class $1$ modulo $q_0$ is left.

The third point is the reason for the shape of the construction. The modulus $q_1$ grows with $x$: $q_1 \geq 2^s = m^{22} \geq x^{11}$, and the table of sizes gives $q_1 \leq x^{12}$. So $q_1 > x$, and each class modulo $q_1$ contains at most one integer $\nu \leq x$. The places $-\nu\tau$ with $\nu \leq x$ are far from equidistributed. The modulus $q_0$ is fixed. So after the mean over $\Phi_a$, the identity contains only $R_{q_0}$ and $R_1$, which are the remainders of Landau's criterion and of the prime number theorem for a fixed modulus.

### The plan of the chapter

Section 2 recalls the weight $\Lambda_K$, the places and the weights $\kappa$, defines the prime sums and bounds them. Section 3 defines the jet size, the direction amount and the main amount, and proves the bounds that the main inequality uses. Section 4 explains the expected value $s_{\mathrm{main}}$ and defines the total remainder. Section 5 proves the identity. Section 6 checks the identity by hand in a small case and deduces the bound for $R_{q_0}(x)$ from the main inequality. Section 7 has exercises and notes.

Lean accepts the results of this chapter if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2). The register of findings has a question on this identity: "Check `totalRemainder_eq` by hand for boundary terms" (question Q-16). Sections 5 and 6 answer it for the terms with $\nu$ not prime to $q_1$, the terms $\nu > x_1$, and the cut at $\nu \leq a$.
