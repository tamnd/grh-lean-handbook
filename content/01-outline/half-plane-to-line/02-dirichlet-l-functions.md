---
title: Dirichlet L-functions and their completions
lean:
  - Statements.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Dirichlet L-functions and their completions

This section defines the objects of the five statements and of their proof: Dirichlet characters, their L-functions, the gamma factor and the completed L-function. All of them are definitions of Mathlib. The section also states three classical facts: the formula for an induced character, the functional equation, and the conjugate symmetry. For each object the text gives the Mathlib name and its values at the classical poles.

### Characters

**Definition (Dirichlet character).** Let $q \geq 1$ be an integer. A *Dirichlet character modulo $q$* is a map $\chi : \mathbb{Z}/q\mathbb{Z} \to \mathbb{C}$ with $\chi(1) = 1$ and $\chi(ab) = \chi(a)\chi(b)$, and with $\chi(a) = 0$ exactly when $a$ is not a unit. We write $\chi(n)$ for $\chi(n \bmod q)$, $n \in \mathbb{Z}$. The *principal character* $\chi_0$ modulo $q$ has the value $1$ on the units and $0$ on the other classes.

Mathlib: `DirichletCharacter ℂ q`, the multiplicative characters of `ZMod q`; the principal character is `1`.

The characters modulo $q$ form a group under the product of values, with identity $\chi_0$. The values of $\chi$ on units are roots of unity, so the inverse of $\chi$ is its complex conjugate $\bar\chi$. Mathlib writes `χ⁻¹`, and this book writes $\bar\chi$. There is one character modulo $1$, and it has the value $1$ at every integer.

**Definition (Induced character, conductor, primitive).** Let $q^* \mid q$ and let $\psi$ be a character modulo $q^*$. The character *induced* by $\psi$ modulo $q$ is $\chi(n) = \psi(n)$ if $\gcd(n, q) = 1$ and $\chi(n) = 0$ otherwise. The *conductor* of $\chi$ is the least divisor $q^*$ of $q$ such that $\chi$ is induced by a character modulo $q^*$. The character $\chi$ is *primitive* if its conductor is $q$.

Mathlib: `DirichletCharacter.changeLevel`, `DirichletCharacter.conductor`, `DirichletCharacter.IsPrimitive`, `DirichletCharacter.primitiveCharacter`.

Each $\chi$ modulo $q$ is induced by exactly one primitive character $\chi^*$ modulo its conductor (Davenport, Chapter 5). The principal character modulo $q$ is induced by the character modulo $1$, so its conductor is $1$.

**Definition (Parity).** Since $\chi(-1)^2 = \chi(1) = 1$, the value $\chi(-1)$ is $1$ or $-1$. The character is *even* if $\chi(-1) = 1$ and *odd* if $\chi(-1) = -1$. Put $a(\chi) = 0$ if $\chi$ is even and $a(\chi) = 1$ if $\chi$ is odd.

Mathlib: `DirichletCharacter.Even`, `DirichletCharacter.Odd`; the number $a(\chi)$ is the case split `if χ.Even` in `DirichletCharacter.gammaFactor`.

A character and the character that it induces have the same parity, because $-1$ is prime to every modulus.

**Example (Characters modulo 4).** There are two characters modulo $4$: the principal character, and $\chi_4$ with $\chi_4(1) = 1$ and $\chi_4(3) = -1$. The character $\chi_4$ is odd. It is primitive: the characters modulo $1$ and modulo $2$ are principal, and they induce the principal character modulo $4$. It is real, so $\bar\chi_4 = \chi_4$.

### L-functions

**Definition (Dirichlet L-function).** For $\operatorname{Re} s > 1$ let $L(s, \chi) = \sum_{n \geq 1} \chi(n) n^{-s}$. This function continues to a meromorphic function on $\mathbb{C}$. The continuation is entire if $\chi \neq \chi_0$, and it has one simple pole, at $s = 1$, if $\chi = \chi_0$. For $q = 1$ it is the Riemann zeta function $\zeta(s)$.

Mathlib: `DirichletCharacter.LFunction` (Mathlib/NumberTheory/LSeries/DirichletContinuation.lean), `riemannZeta`, `DirichletCharacter.LFunction_modOne_eq`.

Mathlib defines $L(s, \chi)$ at every $s \in \mathbb{C}$ as a finite linear combination of Hurwitz zeta functions. Away from the pole it is the continuation. At $s = 1$ for $\chi = \chi_0$ it is a value with no meaning, which the five statements never use. For an imprimitive $\chi$ it is the imprimitive L-function, not the L-function of $\chi^*$. The two differ by finitely many Euler factors.

**Proposition (Change of level).** Let $q^* \mid q$, let $\psi$ be a character modulo $q^*$, and let $\chi$ be the character that $\psi$ induces modulo $q$. If $\psi \neq \chi_0$ or $s \neq 1$, then
$$L(s, \chi) = L(s, \psi) \prod_{p \mid q} \left(1 - \psi(p) p^{-s}\right),$$
where the product is over the primes that divide $q$.

Mathlib: `DirichletCharacter.LFunction_changeLevel`.

A factor with $p \mid q^*$ is $1$, since $\psi(p) = 0$. So only the primes that divide $q$ and not $q^*$ contribute.

*Proof.* For $\operatorname{Re} s > 1$ both series have Euler products, $L(s, \chi) = \prod_p (1 - \chi(p)p^{-s})^{-1}$. For $p \nmid q$ we have $\chi(p) = \psi(p)$, and for $p \mid q$ we have $\chi(p) = 0$. So the Euler product of $\chi$ is that of $\psi$ with the factors at $p \mid q$ removed, which is the formula. The identity theorem extends it to $\mathbb{C} \setminus \{1\}$. If $\psi \neq \chi_0$, both sides are entire, and the formula holds at $s = 1$ by continuity. $\square$

### The gamma factor

**Definition (The real gamma factor).** For $s \notin \{0, -2, -4, \dots\}$ let $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$. At the points $s = -2n$, $n \in \mathbb{N}$, the function $\Gamma(s/2)$ has simple poles. Mathlib gives its function $\Gamma$ the value $0$ at $0, -1, -2, \dots$, so Mathlib's $\Gamma_{\mathbb{R}}$ is a function $\mathbb{C} \to \mathbb{C}$ with $\Gamma_{\mathbb{R}}(-2n) = 0$ for every $n \in \mathbb{N}$.

Mathlib: `Complex.Gammaℝ` (Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean), `Complex.Gammaℝ_eq_zero_iff`, `Complex.Gammaℝ_ne_zero_of_re_pos`.

The classical $\Gamma$ has no zeros. So in Mathlib, $\Gamma_{\mathbb{R}}(s) = 0$ holds exactly when $s = -2n$ for some $n \in \mathbb{N}$, that is, exactly at the poles of the classical $\Gamma_{\mathbb{R}}$. In particular $\Gamma_{\mathbb{R}}(s) \neq 0$ when $\operatorname{Re} s > 0$. This book calls this *the convention for $\Gamma_{\mathbb{R}}$*.

**Definition (Gamma factor and completed L-function).** The *gamma factor* of $\chi$ is $G_\chi(s) = \Gamma_{\mathbb{R}}(s + a(\chi))$. The *completed L-function* is $\Lambda(s, \chi) = G_\chi(s) L(s, \chi)$, as a meromorphic function. For $q = 1$ we write $\Lambda(s) = \Gamma_{\mathbb{R}}(s)\zeta(s)$.

Mathlib: `DirichletCharacter.gammaFactor`, `DirichletCharacter.completedLFunction`, `completedRiemannZeta`, `DirichletCharacter.LFunction_eq_completed_div_gammaFactor`, `riemannZeta_def_of_ne_zero`.

By the convention, $G_\chi(s) = 0$ exactly at the poles of the gamma factor: at $0, -2, -4, \dots$ if $\chi$ is even, and at $-1, -3, -5, \dots$ if $\chi$ is odd. Mathlib defines $\Lambda(s, \chi)$ at every point. It proves
$$L(s, \chi) = \Lambda(s, \chi) / G_\chi(s)$$
for every $s \in \mathbb{C}$, except $s = 0$ when $q = 1$. In Lean a quotient by $0$ is $0$. So at a pole of $G_\chi$ the formula says $L(s, \chi) = 0$, which is true: the L-function has a trivial zero there. For $q = 1$ and $s = 0$ the formula fails, because $\Lambda$ has a pole at $0$ and $\zeta(0) = -1/2$.

### The functional equation

For a primitive character $\chi$ modulo $q$ let $\tau(\chi) = \sum_{b \bmod q} \chi(b) e^{2\pi i b / q}$ be its Gauss sum, and let $w(\chi) = \tau(\chi) / (i^{a(\chi)} q^{1/2})$. Then $|\tau(\chi)| = q^{1/2}$, so $|w(\chi)| = 1$ (Davenport, Chapter 9).

**Theorem (Functional equation).** Let $\chi$ be a primitive character modulo $q \geq 1$. Then
$$\Lambda(1 - s, \chi) = q^{s - 1/2}\, w(\chi)\, \Lambda(s, \bar\chi).$$
If $q > 1$, then $\Lambda(s, \chi)$ is entire. If $q = 1$, this is $\Lambda(1 - s) = \Lambda(s)$, and $\Lambda$ has simple poles at $s = 0$ and $s = 1$ and no other poles.

Mathlib: `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, `completedRiemannZeta_one_sub`. Mathlib's $\Lambda$ has a value at every point, and the identity holds at every $s \in \mathbb{C}$.

*Proof.* The case $q = 1$ is Riemann's theorem (Davenport, Chapter 8). We give the proof for $q > 1$ and $\chi$ even, after Davenport, Chapter 9. For $x > 0$ let $\theta(x, \chi) = \sum_{n \in \mathbb{Z}} \chi(n) e^{-\pi n^2 x / q}$. Since $\chi$ is primitive, $\tau(\bar\chi)\chi(n) = \sum_{b \bmod q} \bar\chi(b) e^{2\pi i b n / q}$ for every $n \in \mathbb{Z}$; for $\gcd(n, q) > 1$ both sides are $0$, and this is where primitivity enters. Poisson summation, applied to $t \mapsto e^{-\pi t^2 x/q} e^{2\pi i b t / q}$ for each $b$, then gives
$$\tau(\bar\chi)\,\theta(x, \chi) = (q / x)^{1/2}\,\theta(1/x, \bar\chi).$$
Since $\chi$ is even and $\chi(0) = 0$, the Mellin transform is $\int_0^\infty \theta(x, \chi) x^{s/2}\, dx/x = 2 q^{s/2}\Lambda(s, \chi)$ for $\operatorname{Re} s > 1$. Split the integral at $x = 1$, and on $(0, 1)$ substitute $x \mapsto 1/x$ and use the transformation formula with $\bar\chi$ in place of $\chi$. This gives
$$2 q^{s/2}\Lambda(s, \chi) = \int_1^\infty \theta(x, \chi) x^{s/2}\,\frac{dx}{x} + \frac{\tau(\chi)}{q^{1/2}} \int_1^\infty \theta(x, \bar\chi) x^{(1-s)/2}\,\frac{dx}{x}.$$
The function $\theta(x, \chi)$ decays exponentially as $x \to \infty$, so both integrals are entire in $s$, and $\Lambda(s, \chi)$ is entire. Write the same formula for $\bar\chi$ at $1 - s$, and use $\tau(\chi)\tau(\bar\chi) = \chi(-1) q = q$. The two formulas then give $\Lambda(1 - s, \bar\chi) = q^{s - 1/2} w(\bar\chi) \Lambda(s, \chi)$, which is the theorem for $\bar\chi$. For $\chi$ odd, use $\theta_1(x, \chi) = \sum_{n} n\chi(n) e^{-\pi n^2 x / q}$; the same steps give the factor $i^{-1}$ in $w(\chi)$ (Davenport, Chapter 9). $\square$

The last step uses one consequence only. Since $q^{s - 1/2} w(\chi) \neq 0$, for a primitive $\chi$ $\Lambda(s, \chi) = 0$ implies $\Lambda(1 - s, \bar\chi) = 0$, at every point where $\Lambda(s, \chi)$ is finite.

### The conjugate symmetry

**Proposition (Conjugate symmetry).** Let $\chi$ be a Dirichlet character modulo $q$ and let $s \neq 1$. Then $L(\bar s, \bar\chi) = \overline{L(s, \chi)}$.

Not in the source. The source applies the half-plane statement to $\bar\chi = \chi^{-1}$ at $1 - s$ directly, in the proof of `New.zeros_on_line` (New/Main.lean), so it needs no conjugation of $L$.

The source does not state this proposition, and the last step does not use it. It is here because it gives the classical form of the symmetry (Section 5).

*Proof.* The function $f(s) = \overline{L(\bar s, \chi)}$ is holomorphic on $\mathbb{C} \setminus \{1\}$. For $\operatorname{Re} s > 1$, we have $\overline{n^{-\bar s}} = n^{-s}$ for each integer $n \geq 1$, so $f(s) = \sum_n \bar\chi(n) n^{-s} = L(s, \bar\chi)$. The identity theorem on the connected set $\mathbb{C} \setminus \{1\}$ gives $f(s) = L(s, \bar\chi)$ for all $s \neq 1$. Replace $s$ by $\bar s$. $\square$

**Example (The functional equation modulo 4).** Take $\chi_4$. It is odd, so $G_{\chi_4}(s) = \Gamma_{\mathbb{R}}(s + 1)$. The Gauss sum is $\tau(\chi_4) = e^{2\pi i/4} - e^{2\pi i \cdot 3/4} = i - (-i) = 2i$, so $w(\chi_4) = 2i/(i \cdot 2) = 1$. The functional equation is $\Lambda(1 - s, \chi_4) = 4^{s - 1/2}\Lambda(s, \chi_4)$. The gamma factor has its poles at $-1, -3, -5, \dots$, and there $L(s, \chi_4)$ has its trivial zeros. They do not reflect. For example $L(-1, \chi_4) = 0$, while $L(2, \chi_4) = 1 - 3^{-2} + 5^{-2} - \dots$ is Catalan's constant $0.9159\ldots$, which is not $0$. The zero of $L$ at $-1$ comes from the pole of the gamma factor. This is why the reflection theorem of Section 5 has two alternatives.
