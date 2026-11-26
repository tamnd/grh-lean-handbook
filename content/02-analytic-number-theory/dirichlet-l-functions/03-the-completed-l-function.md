---
title: The completed L-function
lean:
  - Lib/Analytic/ZeroSymmetry.lean
decls:
  - New.gammaFactor_changeLevel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The completed L-function

This section adds the gamma factor to $L(s, \chi)$ and states the functional equation. The classical form is for a primitive character. Mathlib states the same theorem with a different normalization. From the primitive case we then derive a functional equation for every character. The source does not state this last identity. It uses only its consequence for the zeros, which is the subject of Section 5.

### The gamma factor

For $s \in \mathbb{C}$ put
$$\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\,\Gamma(s/2).$$
The function $\Gamma_{\mathbb{R}}$ is meromorphic on $\mathbb{C}$. It has no zero. It has simple poles at $s = 0, -2, -4, \ldots$ and no other pole. It is not zero for $\operatorname{Re} s > 0$.

Mathlib: `Complex.Gammaℝ`, `Complex.Gammaℝ_ne_zero_of_re_pos`, `Complex.Gammaℝ_eq_zero_iff`.

Mathlib defines $\Gamma(s)$ at every $s \in \mathbb{C}$. At a pole $s = -n$ it gives $\Gamma$ the value $0$. So `Complex.Gammaℝ s = 0` holds exactly when $s = -2n$ for some $n \in \mathbb{N}$, that is, exactly at the poles of the classical function. In this book a statement of the form "$\Gamma_{\mathbb{R}}(s) = 0$" about a Lean term means "$s$ is a pole of $\Gamma_{\mathbb{R}}$".

**Definition (Gamma factor).** Let $\chi$ be a character modulo $q$ with parity $a(\chi)$. The *gamma factor* of $\chi$ is $G_\chi(s) = \Gamma_{\mathbb{R}}(s + a(\chi))$. So $G_\chi(s) = \Gamma_{\mathbb{R}}(s)$ if $\chi$ is even and $G_\chi(s) = \Gamma_{\mathbb{R}}(s + 1)$ if $\chi$ is odd.

Mathlib: `DirichletCharacter.gammaFactor`, `DirichletCharacter.Even.gammaFactor_def`, `DirichletCharacter.Odd.gammaFactor_def`.

The poles of $G_\chi$ are the points $s = -a(\chi) - 2n$ with $n \in \mathbb{N}$. For an even $\chi$ these are $0, -2, -4, \ldots$. For an odd $\chi$ they are $-1, -3, -5, \ldots$. Since the gamma factor depends only on the parity, and induction keeps the parity, an induced character has the gamma factor of the character that induces it.

**Lemma (Gamma factor of an induced character).** Let $q^* \mid q$, let $\psi$ be a character modulo $q^*$, and let $\chi$ be the character that $\psi$ induces modulo $q$. Then $G_\chi(s) = G_\psi(s)$ for every $s \in \mathbb{C}$.

Lean: `New.gammaFactor_changeLevel` (Lib/Analytic/ZeroSymmetry.lean).

*Proof.* The class of $-1$ is a unit modulo $q^*$ and modulo $q$. So $\chi(-1) = \psi(-1)$, and $\chi$ is even exactly when $\psi$ is even. Both gamma factors are then given by the same branch of the definition. $\square$

### The completed L-function

**Definition (Completed L-function).** Let $\chi$ be a character modulo $q$. The *completed L-function* of $\chi$ is the meromorphic function
$$\Lambda(s, \chi) = G_\chi(s)\, L(s, \chi).$$

Mathlib: `DirichletCharacter.completedLFunction`, `DirichletCharacter.LFunction_eq_completed_div_gammaFactor`.

Classically $\Lambda(s, \chi)$ is defined by this product. Mathlib defines `completedLFunction χ` directly, as a combination of completed Hurwitz zeta functions, at every $s \in \mathbb{C}$. It then proves the identity in the other direction:
$$L(s, \chi) = \frac{\Lambda(s, \chi)}{G_\chi(s)} \qquad \text{if } s \neq 0 \text{ or } q \neq 1.$$
The identity holds at the poles of $G_\chi$ too, with the conventions $G_\chi(s) = 0$ there and $x/0 = 0$. So at such a point Mathlib's $L(s, \chi)$ is $0$. This agrees with the classical value when the classical $\Lambda(s, \chi)$ is finite at $s$. The excluded case $s = 0$, $q = 1$ is the zeta function at $0$: there $\Lambda$ has a pole, and $\zeta(0) = -1/2$.

The analytic facts are these. If $\chi \neq \chi_0$, then $\Lambda(s, \chi)$ is entire (Mathlib: `DirichletCharacter.differentiable_completedLFunction`). If $\chi = \chi_0$, then $\Lambda(s, \chi_0)$ has a pole at $s = 1$, and also at $s = 0$ when $q = 1$. In the second case, $\Lambda(s, \chi_0) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$ is Riemann's completed zeta function (Mathlib: `DirichletCharacter.completedLFunction_modOne_eq`).

The classical texts use a second normalization. Davenport, *Multiplicative Number Theory*, Chapter 9, puts
$$\xi(s, \chi) = \left(\frac{q}{\pi}\right)^{(s + a)/2}\Gamma\!\left(\frac{s + a}{2}\right) L(s, \chi) = q^{(s + a)/2}\,\Lambda(s, \chi), \qquad a = a(\chi).$$
The factor $q^{(s+a)/2}$ has no zero and no pole. So $\xi(s, \chi)$ and $\Lambda(s, \chi)$ have the same zeros, with the same orders. The two normalizations differ only in the power of $q$ in the functional equation.

### The functional equation of a primitive character

The *root number* of a character $\chi$ modulo $q$ with parity $a$ is
$$w(\chi) = \frac{\tau(\chi)}{i^{a}\, q^{1/2}}.$$
If $\chi$ is primitive, then $|w(\chi)| = 1$ by the proposition on Gauss sums of Section 2.

Mathlib: `DirichletCharacter.rootNumber`.

**Theorem (Functional equation, primitive case).** Let $\chi$ be a primitive character modulo $q$. Then, as an identity of meromorphic functions,
$$\xi(1 - s, \chi) = w(\chi)\, \xi(s, \bar\chi).$$
In the normalization of $\Lambda$, the same identity reads
$$\Lambda(1 - s, \chi) = q^{s - 1/2}\, w(\chi)\, \Lambda(s, \bar\chi).$$

Mathlib: `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`.

The first form is in Davenport, Chapter 9, written with $\chi$ and $\bar\chi$ exchanged: $\xi(1 - s, \bar\chi) = i^{a} q^{1/2}\tau(\chi)^{-1}\xi(s, \chi)$. The two forms agree, since $\tau(\chi)\tau(\bar\chi) = \chi(-1)q$ for a primitive $\chi$, and so $w(\bar\chi) = i^{a}q^{1/2}/\tau(\chi)$. The form with $\Lambda$ follows from the form with $\xi$: by definition $\xi(1 - s, \chi) = q^{(1 - s + a)/2}\Lambda(1 - s, \chi)$ and $\xi(s, \bar\chi) = q^{(s + a)/2}\Lambda(s, \bar\chi)$, and the quotient of the powers of $q$ is $q^{s - 1/2}$. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 4, prove the theorem with the Poisson summation formula, and Chapter 5 places it in the general frame of L-functions.

The proof of Davenport, Chapter 9, follows Riemann's three steps for $\zeta$ (Section 1). Let $\chi$ have parity $a$, and put
$$\vartheta(x, \chi) = \sum_{n \in \mathbb{Z}} n^{a}\chi(n)\, e^{-\pi n^2 x/q}, \qquad x > 0.$$

1. Poisson summation and the proposition on Gauss sums give $\vartheta(x, \chi) = w(\chi)\, x^{-a - 1/2}\,\vartheta(1/x, \bar\chi)$. This is the step that needs primitivity: the Fourier coefficients of $\chi$ are $\tau(\chi, n) = \bar\chi(n)\tau(\chi)$, and this identity can fail for an imprimitive $\chi$.
2. For $\operatorname{Re} s > 1$, a Mellin transform gives $\int_0^\infty \vartheta(x, \chi)\, x^{(s + a)/2}\, dx/x = 2\, \xi(s, \chi)$ when $q > 1$.
3. Split the integral at $x = 1$ and use step 1 on $(0, 1)$. The result continues $\xi(s, \chi)$ to an entire function when $\chi \neq \chi_0$, and gives the functional equation.

The source does not reprove this theorem. Mathlib proves it with Hurwitz zeta functions and the discrete Fourier transform on $\mathbb{Z}/q\mathbb{Z}$. Section 4 describes the theta series of the source. They follow steps 1 and 2, but they keep only absolute values.

### Every character

Let $\chi$ be any character modulo $q$. Let $\chi^*$ be the primitive character modulo $q^*$ that induces $\chi$ (Section 2). Put
$$E(s) = \prod_{p \mid q}\left(1 - \chi^*(p)p^{-s}\right), \qquad \bar E(s) = \prod_{p \mid q}\left(1 - \bar\chi^*(p)p^{-s}\right).$$
These are finite products of entire functions. By the lemma on the finite Euler factors, they have no zero off the line $\operatorname{Re} s = 0$.

**Proposition (Functional equation for every character).** With this notation, as an identity of meromorphic functions,
$$\Lambda(1 - s, \chi)\, \bar E(s) = (q^*)^{s - 1/2}\, w(\chi^*)\, \Lambda(s, \bar\chi)\, E(1 - s).$$

This proposition has no Lean line: the source does not state it. Section 5 proves in Lean the part of it that the argument needs.

*Proof.* By the change of level of Section 2, $L(s, \chi) = L(s, \chi^*)E(s)$. The character $\bar\chi^*$ induces $\bar\chi$, so also $L(s, \bar\chi) = L(s, \bar\chi^*)\bar E(s)$. By the lemma on gamma factors above, $G_\chi = G_{\chi^*}$ and $G_{\bar\chi} = G_{\bar\chi^*}$. Hence
$$\Lambda(s, \chi) = \Lambda(s, \chi^*)E(s), \qquad \Lambda(s, \bar\chi) = \Lambda(s, \bar\chi^*)\bar E(s).$$
Multiply the first identity at $1 - s$ by $\bar E(s)$ and apply the theorem to the primitive $\chi^*$:
$$\Lambda(1 - s, \chi)\bar E(s) = \Lambda(1 - s, \chi^*)E(1 - s)\bar E(s) = (q^*)^{s - 1/2}w(\chi^*)\Lambda(s, \bar\chi^*)\bar E(s)E(1 - s).$$
By the second identity the right side is $(q^*)^{s - 1/2}w(\chi^*)\Lambda(s, \bar\chi)E(1 - s)$. $\square$

If $\chi$ is primitive, then $q^* = q$, every factor of $E$ and $\bar E$ is $1$, and the proposition is the theorem. If $\chi$ is imprimitive, the factors $\bar E(s)$ and $E(1 - s)$ can vanish. The zeros of $\bar E(s)$ lie on $\operatorname{Re} s = 0$, and the zeros of $E(1 - s)$ lie on $\operatorname{Re} s = 1$. Away from these two lines the proposition says that $\Lambda(1 - s, \chi)$ and $\Lambda(s, \bar\chi)$ have the same zeros, with the same orders.

**Example (The principal character modulo a prime).** Let $p$ be a prime and let $\chi_0$ be the principal character modulo $p$. Then $\chi^*$ is the character modulo $1$, $q^* = 1$, $w(\chi^*) = 1$, and $E(s) = \bar E(s) = 1 - p^{-s}$. The proposition reads
$$\Lambda(1 - s, \chi_0)(1 - p^{-s}) = \Lambda(s, \chi_0)(1 - p^{s - 1}).$$
At $s = 2\pi i k/\log p$ with $k \neq 0$, the left side is $0$ and $\Lambda(s, \chi_0) = \Gamma_{\mathbb{R}}(s)\zeta(s)(1 - p^{-s}) = 0$. But $1 - s$ has real part $1$, and $L(1 - s, \chi_0) = \zeta(1 - s)(1 - p^{s - 1}) \neq 0$ there. So $s$ is a zero of $L(\cdot, \chi_0)$ and $1 - s$ is not. Exercise 1 asks for the details.

**Remark (Formalization).** Three points separate the textbook and the Lean forms.

1. Normalization. Mathlib's completed L-function is $\Lambda(s, \chi) = G_\chi(s)L(s, \chi)$, without the factor $q^{(s+a)/2}$ of Davenport's $\xi(s, \chi)$. So the power $q^{s - 1/2}$ appears in Mathlib's functional equation. The zeros are the same in both normalizations.
2. Junk values. Mathlib's root number `DirichletCharacter.rootNumber χ` is defined for every $\chi$, by the formula above. Its docstring calls it junk when $\chi$ is not primitive, since the functional equation then fails with it. The value of `completedLFunction χ` at a pole, and the value `Gammaℝ s = 0` at a pole of $\Gamma_{\mathbb{R}}$, are also junk values. They matter in Section 5: there the alternative "$G_\chi(s) = 0$" of the reflection theorem means that $s$ is a pole of the gamma factor.
3. What the argument uses. The source does not use the root number, the power of $q$, or the identity of this proposition. It uses only the functional equation for a primitive character, through `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, to move a zero from $s$ to $1 - s$. The factors $E$ and $\bar E$ enter only through the lemma on the finite Euler factors.
