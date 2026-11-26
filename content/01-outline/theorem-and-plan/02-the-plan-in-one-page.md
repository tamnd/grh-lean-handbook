---
title: The plan in one page
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/MainInequality.lean
decls:
  - New.grh
  - New.eventually_primeRemainder_le_rpow
  - New.Data.primeRemainder_le
  - New.star_inequality
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The plan in one page

The proof is a chain of statements. Each statement comes from the one below it, by one tool. The top of the chain is the five theorems. The bottom is the background theories of Volumes 2 to 8. This section gives the chain as a diagram, then states each link with its Lean name. The statements of the last step are exact. The proofs are in the chapters that the links name.

### The chain

Read the diagram from the bottom up. A line with a name in parentheses is a statement. A line after a bar is the tool that turns the statement below it into the statement above it.

```text
GRH: the five theorems                     (Main.lean)
  ^
  |  zeros on the line, by reflection
  |  s -> 1 - s, for every character
L(s, chi) != 0 for Re s > 1/2              (New.grh)
  ^
  |  Landau's criterion, with quadratic
  |  twists: one prime d whose twists
  |  have no zero near rho
R_q0(y) <= y^(-1/2 + eps), y large
           (New.eventually_primeRemainder_le_rpow)
  ^
  |  the identity for rem, the prime
  |  number theorem at x1, the data exist
m * rem <= f * a * (log b)^5               (New.star_inequality)
  ^
  |  Hadamard's inequality; the main
  |  amount cancels
Theorems A, B and C        (ShortAndEnough, LongForms)
  ^
  |  Volumes 9 to 12
the background theories        (Lib, Volumes 2 to 8)
```

### Zeros on the line, by reflection

The five theorems of Section 1 come from the half-plane theorem below. The tool is the reflection of zeros: if $0 < \operatorname{Re} \rho < 1$ and $L(\rho, \chi) = 0$, then $L(1 - \rho, \bar\chi) = 0$. The source proves this for every Dirichlet character, primitive or not, as [Theorem](/decl/New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero/). The two lemmas [Theorem](/decl/New.zeros_on_line/) and [Theorem](/decl/New.zeta_zeros_on_line/) take the half-plane statement as a hypothesis and give the line statement and the zeta statement. [From the half-plane to the line](/chapter/half-plane-to-line/) proves them.

### The half-plane theorem

**Theorem (The half-plane theorem).** For every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

*Proof.* The proof is in [the main inequality and the end of the proof](/chapter/main-inequality/). Here is its shape. Let $\rho$ satisfy the hypotheses. If $\rho = 1$, then $\chi \neq \chi_0$, and $L(1, \chi) \neq 0$ by Dirichlet's theorem, which Mathlib has (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`). If $\rho \neq 1$, choose $\beta$ with $1/2 < \beta < \operatorname{Re} \rho$. Let $q_0 = 18480\, q$ and $d_0 = 9240\, q - 1 = q_0/2 - 1$ (Exercise 1). For every prime $d \equiv d_0 \bmod q_0$, the one-sided bound below with $\eta = \beta - 1/2$ gives $R_{q_0}(y) \leq y^{\beta - 1}$ for all large $y$. Landau's criterion, [Theorem](/decl/New.LFunction_ne_zero_of_primeRemainder_le/), then gives $L(\rho, \psi) \neq 0$ for the character $\psi$ modulo $q_0$ that $\chi$ induces. The function $L(s, \psi)$ is $L(s, \chi)$ times the finitely many factors $1 - \chi(p)p^{-s}$ with $p \mid q_0$, $p \nmid q$. So $L(\rho, \chi) \neq 0$. $\square$

### Landau's criterion, with quadratic twists

Let $d$ be a prime, let $\chi_K(n) = (n/d)$, and let $q \geq 1$. Put $\lambda(n) = \Lambda(n)(1 - \chi_K(n))$ for $n \equiv 1 \bmod q$, and $\lambda(n) = 0$ otherwise. The weighted prime remainder is
$$R_q(x) = \sum_{1 \leq n \leq x} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \frac{\log x}{\varphi(q)} - c_q,$$
where $c_q$ is the constant for which $R_q(x) \to 0$. [The weighted prime remainder](/chapter/weighted-prime-remainder/) defines $c_q$ and finds the poles of the Mellin transform of $R_q$. The criterion reads as follows. Let $8 \mid q_0$, let $d_0 \equiv 7 \bmod 8$ be prime to $q_0$, and let $\beta > 1/2$. Suppose that for every prime $d \equiv d_0 \bmod q_0$ the remainder $R_{q_0}$ of $d$ satisfies $R_{q_0}(x) \leq x^{\beta - 1}$ for all large $x$. Then $L(\rho, \psi) \neq 0$ for every character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$.

Since $\lambda(n) \geq 0$, Landau's lemma applies, and a bound on one side is enough. The twists $L(s, \psi\chi_K)$ enter the residues with the wrong sign. The proof avoids them with one prime $d$ of the class whose twists have no zero near $\rho$. A zero-density estimate for the quadratic twists gives this prime (`New.exists_entireL_quadTwist_ne_zero`, Volume 2). The prime depends on $\rho$ and is not explicit, so the bound is needed for every prime of the class. [Landau's criterion](/chapter/landau-criterion/) proves the criterion.

### The one-sided bound

**Theorem (The one-sided bound).** Let $q_0 \geq 1$ be a multiple of $18480$, let $d$ be a prime with $d \equiv q_0/2 - 1 \bmod q_0$, and let $\eta > 0$. Then the remainder $R_{q_0}$ of $d$ and $q_0$ satisfies
$$R_{q_0}(y) \leq y^{-1/2 + \eta} \qquad \text{for all large real } y.$$

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

*Proof.* The proof is in [the main inequality and the end of the proof](/chapter/main-inequality/). It uses the next theorem at each large integer $x$, with data chosen so that $\log b \leq 2x^{\varepsilon_1}$, $m \geq \sqrt{x}$ and $\log x_1 \geq x^{\varepsilon_1/12}$, where $\varepsilon_1 = \min(1/200, \eta/7)$ is the scale exponent of the data. The prime number theorem for $R_q$ gives $|R_q(y)| \leq (\log y)^{-B}$ for large $y$ and every $B$, so the two terms at $x_1$ are at most $x^{-2}$ and $2x^{\varepsilon_1} \cdot x^{-2}$. The main term is at most $\varphi(q_0)(2x^{\varepsilon_1})^6/\sqrt{x} = 64\,\varphi(q_0)\, x^{-1/2 + 6\varepsilon_1}$. So $R_{q_0}(x) \leq (64\,\varphi(q_0) + 3)\,x^{-1/2 + 6\varepsilon_1}$ for large integers $x$. The bound $R_{q_0}(y) - R_{q_0}(\lfloor y \rfloor) \leq 26/y$ and the bound $\lfloor y \rfloor^{u} \leq 2y^{u}$ for $-1 \leq u \leq 0$ pass to real $y$, with the factor $2(64\,\varphi(q_0) + 3) + 26$. For large $y$ this factor is at most $y^{\varepsilon_1}$, and $6\varepsilon_1 + \varepsilon_1 \leq \eta$. $\square$

**Remark (Formalization).** The congruence is written `d ≡ q₀ / 2 - 1 [MOD q₀]` with division and subtraction of natural numbers. Since $q_0$ is even and $q_0 \geq 18480$, both are exact, so the hypothesis is the congruence of the textbook. The bound is eventual: the threshold for "large" may depend on $q_0$, $d$ and $\eta$. The criterion needs nothing more.

### From the star inequality to the remainder

The lattice argument works with *data*: a term $D$ that bundles the integer scales $x \leq x_1 \leq b$, the number $m$ of lifts, a CM field $E$, two sets of places $\Phi_a$ and $\Phi_b$ of $E$, and many more choices. Here $a = xb$, $f$ is the number of infinite places of $E$, and the data satisfy $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$ and $\sqrt{x} \leq m \leq 2\sqrt{x}$. [The data and its sizes](/chapter/data-and-sizes/) lists all the fields. [The data exist](/chapter/data-exist/) proves that data exist for every large $x$. The *total remainder* $\mathrm{rem}$ is the sum over the places $\tau \in \Phi_a$ of a prime sum at $\tau$ less its expected value. [Prime sums and the total remainder](/chapter/prime-sums/) proves the identity
$$\mathrm{rem} = a\bigl(\#\Phi_b\,(R_{q_0}(x) - R_{q_0}(x_1)) + \#\Phi_a\, R_1(x_1)\bigr)$$
(Lean: `New.Data.totalRemainder_eq`), where $R_1$ is the remainder for the modulus $1$.

**Theorem (The remainder at the scale $x$).** Let $D$ be data for a modulus $q_0$ and a prime $d$. Then
$$R_{q_0}(x) \leq \frac{\varphi(q_0)\log^6 b}{m} + |R_{q_0}(x_1)| + \log b \cdot |R_1(x_1)|.$$

Lean: `New.Data.primeRemainder_le` (New/Reduction/OneSidedBound.lean).

*Proof.* The star inequality below gives $\mathrm{rem} \leq f a \log^5 b / m$. Divide the identity for $\mathrm{rem}$ by $a\,\#\Phi_b$. This gives
$$R_{q_0}(x) = \frac{\mathrm{rem}}{a\,\#\Phi_b} + R_{q_0}(x_1) - \frac{\#\Phi_a}{\#\Phi_b} R_1(x_1) \leq \frac{f \log^5 b}{m\,\#\Phi_b} + |R_{q_0}(x_1)| + \frac{\#\Phi_a}{\#\Phi_b}|R_1(x_1)|.$$
The data satisfy $f = \varphi(q_0)\,\#\Phi_a$ and $\#\Phi_a \leq \#\Phi_b \log b$. Insert both. $\square$

This is the only place where the exponent $1/2$ enters: the first term is about $x^{-1/2}$ because $m \approx \sqrt{x}$ (Section 3).

### The star inequality

**Theorem (The star inequality).** Let $D$ be data for a modulus $q_0$ and a prime $d$. Then
$$m \cdot \mathrm{rem} \leq f \cdot a \cdot \log^5 b.$$

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

*Proof.* The proof uses Theorems A, B and C below, Hadamard's inequality and $\mathrm{main} \geq 0$, where $\mathrm{main}$ is the main amount of [the prime sums](/chapter/prime-sums/). Write $d_T$ for the dimension of the space of target forms, $\mathrm{loss} = f a \log^4 b$ and $\mathrm{err}_0 = f a \log^3 b$. Theorem B gives $d_T > 0$ and a finite set $t$ of translations. By Theorem A(a), the images of short integral forms under the maps $s\mathfrak{p}$, $s \in t$, span the sum of their ranges. Choose a basis $y_1, \dots, y_n$ of that sum among these images. Theorem B gives $(1 - 4/b^2)d_T \leq n$, and $n \leq d_T$. Each $y_i$ has squared length at most $\exp(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss})$ at every archimedean place, so Hadamard's inequality bounds the covolume of $y$ by $c = n(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss})$. Theorem A(b) and the bound on $\#t$ bound the index by $\delta = d_T \cdot 10\log(1 + 2b^2)\, \mathrm{err}_0$. Theorem C gives
$$d_T(\mathrm{main} - 3\,\mathrm{loss}) \leq n(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss}) + 2\delta.$$
Since $n \leq d_T$ and $\mathrm{main} + \mathrm{loss} \geq 0$, we have $n(\mathrm{main} + \mathrm{loss}) \leq d_T(\mathrm{main} + \mathrm{loss})$, and so $n\, m\,\mathrm{rem} \leq d_T\, \mathrm{err}$ with $\mathrm{err} = 4\,\mathrm{loss} + 20 \log(1 + 2b^2)\, \mathrm{err}_0$. The main amount has cancelled. Since $b^2 \geq 8$, we have $d_T \leq 2n$, so $n > 0$ and $m\,\mathrm{rem} \leq 2|\mathrm{err}|$. Finally $2|\mathrm{err}| = 8 f a \log^4 b + 40 \log(1 + 2b^2) f a \log^3 b \leq f a \log^5 b$, because $\log b$ is large. $\square$

### Theorems A, B and C

The three theorems are about one space of automorphic forms on a unitary group, the *target forms*, of dimension $d_T$, with a structure of twisted lattice: for each twist $\xi$, a lift $\Theta_\xi$ to an inner product space with integral vectors at each prime. There is also a space of *source forms*, a fixed linear map $\mathfrak{p}$ from the ramified source forms to the target forms, built from Poincaré series, and its translates $s\mathfrak{p}$ by elements $s$ of a group of translations. Write $\mathrm{src}$ for the space of ramified source forms and $\mathrm{int}$ for its subset of forms that are integral at every prime. In one line each:

- **A(a), short forms.** $\operatorname{span}_{\mathbb{C}}\{\varphi \in \mathrm{int} : \|\Theta_1(s\mathfrak{p}\varphi)\|_\sigma^2 \leq \exp(\mathrm{main} - m\,\mathrm{rem} + f a \log^4 b) \text{ for all } s, \sigma\} = \mathrm{src}$.
- **A(b), index.** If each $y_i$ lies in $s\mathfrak{p}(\mathrm{int})$ for some $s \in t$, then the index of $y$ is at most $\#t \cdot \dim \mathrm{src} \cdot 2 f a \log^3 b$.
- **B, enough forms.** $d_T > 0$, and some $t$ has $\#t \cdot \dim \mathrm{src} \leq 5 d_T \log(1 + 2b^2)$ and $(1 - 4/b^2)\, d_T \leq \dim \sum_{s \in t} s\mathfrak{p}(\mathrm{src})$.
- **C, long forms.** If $y_1, \dots, y_n$ are independent with $n \geq (1 - 4/b^2)d_T$, index at most $\delta$ and covolume at most $c$, then $d_T(\mathrm{main} - 3 f a \log^4 b) \leq c + 2\delta$.

Here $\sigma$ runs over the automorphisms of $\mathbb{C}$, which play the part of the archimedean places. [Theorems A, B and C](/chapter/theorems-a-b-c/) states them exactly, with their sizes, and gives a plan of each proof. Volumes 9, 10 and 11 prove them, and Volume 12 proves the congruences that Theorem C needs.

**Remark (Formalization).** The Lean names are `New.Data.span_short_integralRamified_eq_top` and `New.Data.indexLe_normalizedPoincare` for Theorem A, `New.Data.enough_forms` for Theorem B, and `New.Data.integral_forms_long` for Theorem C. The map $s\mathfrak{p}$ is `D.normalizedPoincare s`: the projected Poincaré series, times a positive constant $c_B$. The constant does not change any span or any range. The proof of the star inequality calls the four theorems exactly in the forms above ([MainInequality.lean](lean:New/Reduction/MainInequality.lean#L87)).

### The background theories

Theorems A, B and C rest on the library of the source, which [the map of the book](/chapter/theorem-and-plan/#the-map-of-the-book) sorts into Volumes 2 to 8: analytic number theory, class field theory and complex multiplication, unitary groups and automorphic forms, representations, the theta correspondence and the Siegel-Weil formula, p-adic Hodge theory, and Galois representations. The source often proves a weaker form of a standard theorem, which suffices here.
