---
title: The model case, the zeta function
lean:
  - New/Main.lean
decls:
  - New.zeta_zeros_on_line
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model case, the zeta function

This section proves the zeta statement from the half-plane statement. It is the model case of the general deduction of Section 6. For the modulus $1$ there are no Euler factors to remove and no primitive character to find: the only character is principal, and it is primitive. Two points need care, and both come back in the general case. The first is the trivial zeros, which are poles of $\Gamma_{\mathbb{R}}$. The second is the point $s = 0$, where Mathlib's $\zeta$ is not the quotient $\Lambda / \Gamma_{\mathbb{R}}$.

### The functional equation in the form of Mathlib

The proof uses three facts of Mathlib (Section 2).

1. For $s \neq 0$, $\zeta(s) = \Lambda(s) / \Gamma_{\mathbb{R}}(s)$, with the convention for $\Gamma_{\mathbb{R}}$ and with $x / 0 = 0$ (Mathlib: `riemannZeta_def_of_ne_zero`).
2. For every $s \in \mathbb{C}$, $\Lambda(1 - s) = \Lambda(s)$ (Mathlib: `completedRiemannZeta_one_sub`). At $s = 0$ and $s = 1$ both sides are Mathlib's values of $\Lambda$ at its poles, and the identity holds for these values too.
3. $\zeta(0) = -1/2$ (Mathlib: `riemannZeta_zero`).

The first fact also holds at the trivial zeros. For $n \geq 1$, Mathlib has $\Gamma_{\mathbb{R}}(-2n) = 0$, so the quotient is $0$, and $\zeta(-2n) = 0$ is true. On paper, $\Lambda$ is holomorphic at $-2n$ and $\Gamma_{\mathbb{R}}$ has a pole there.

### The reflection for zeta

The next lemma is a step of the proof of the theorem below. The source does not state it apart.

**Lemma (Reflection for zeta).** Let $s \in \mathbb{C}$ with $\zeta(s) = 0$, $s \neq 1$, and $s \neq -2(n+1)$ for every $n \in \mathbb{N}$. Then $s \neq 0$ and $\zeta(1 - s) = 0$.

*Proof.* Since $\zeta(0) = -1/2 \neq 0$, we have $s \neq 0$.

Next, $\Gamma_{\mathbb{R}}(s) \neq 0$. Suppose $\Gamma_{\mathbb{R}}(s) = 0$. By the convention, $s = -2n$ for some $n \in \mathbb{N}$. If $n = 0$, then $s = 0$, which we excluded. If $n = m + 1$ with $m \in \mathbb{N}$, then $s = -2(m+1)$, which the hypothesis excludes.

Since $s \neq 0$, fact 1 gives $0 = \zeta(s) = \Lambda(s) / \Gamma_{\mathbb{R}}(s)$. The denominator is not $0$, so $\Lambda(s) = 0$. Fact 2 gives $\Lambda(1 - s) = 0$. Since $s \neq 1$, we have $1 - s \neq 0$, and fact 1 at $1 - s$ gives $\zeta(1 - s) = \Lambda(1 - s) / \Gamma_{\mathbb{R}}(1 - s) = 0$. $\square$

The last step needs no information about $\Gamma_{\mathbb{R}}(1 - s)$, because $0 / x = 0$ for every $x$, including $x = 0$. On paper, a pole of $\Gamma_{\mathbb{R}}$ at $1 - s$ would mean $\operatorname{Re} s > 1$, where $\zeta$ has no zeros. The proof does not need to know this.

**Example (A trivial zero does not reflect).** Take $s = -2$. Then $\zeta(-2) = 0$, but the lemma does not apply, since $s = -2(0 + 1)$. The proof breaks at the second step: $\Gamma_{\mathbb{R}}(-2) = 0$ in Mathlib, so $\zeta(-2) = 0$ gives no information about $\Lambda(-2)$. In fact $\Lambda(-2) = \Lambda(3) = \pi^{-3/2}\Gamma(3/2)\zeta(3) = \zeta(3)/(2\pi) = 0.1913\ldots$, since $\Gamma(3/2) = \sqrt{\pi}/2$. So $\Lambda(-2) \neq 0$, and $\zeta(3) \neq 0$: the zero at $-2$ has no partner at $3$. The zero of $\zeta$ at $-2$ comes from the pole of $\Gamma_{\mathbb{R}}$, not from a zero of $\Lambda$.

**Example (The point 0).** At $s = 0$ the quotient $\Lambda(0) / \Gamma_{\mathbb{R}}(0)$ is $0$ in Mathlib, while $\zeta(0) = -1/2$. On paper, $\Lambda$ has a simple pole at $0$ with residue $-1$, and $\Gamma_{\mathbb{R}}$ has a simple pole at $0$ with residue $2$. Their quotient is $-1/2$, which is $\zeta(0)$. Mathlib cannot see this as a quotient of values, so it sets $\zeta(0)$ apart, and fact 1 asks $s \neq 0$.

### The theorem

**Theorem (The zeta statement from the half-plane statement).** Assume the half-plane statement. Then the zeta statement holds: for every $s \in \mathbb{C}$ with $\zeta(s) = 0$, $s \neq -2(n+1)$ for every $n \in \mathbb{N}$, and $s \neq 1$, we have $\operatorname{Re} s = 1/2$.

Lean: `New.zeta_zeros_on_line` (New/Main.lean).

*Proof.* Apply the half-plane statement with $q = 1$ and $\chi$ the character modulo $1$. Its L-function is $\zeta$ (Section 2). For this $\chi$ the clause "$\chi \neq \chi_0$ or $z \neq 1$" becomes $z \neq 1$. So we get: if $z \neq 1$ and $\zeta(z) = 0$, then $\operatorname{Re} z \leq 1/2$.

Let $s$ satisfy the hypotheses. Since $s \neq 1$ and $\zeta(s) = 0$, we get $\operatorname{Re} s \leq 1/2$. By the lemma, $s \neq 0$ and $\zeta(1 - s) = 0$. Since $s \neq 0$, we have $1 - s \neq 1$. So $\operatorname{Re}(1 - s) = 1 - \operatorname{Re} s \leq 1/2$. The two inequalities give $\operatorname{Re} s = 1/2$. $\square$

**Remark.** The zeta statement covers all of $\mathbb{C}$. A zero $s$ with $\operatorname{Re} s < 0$ that is not trivial would reflect to $1 - s$ with $\operatorname{Re}(1 - s) > 1$, and the half-plane statement excludes it there. That part of the half-plane statement is the classical non-vanishing of $\zeta$ on $\operatorname{Re} s \geq 1$.

**Remark (Formalization).** The proof uses the convention for $\Gamma_{\mathbb{R}}$ at two places. It gets $\Gamma_{\mathbb{R}}(s) \neq 0$ from Mathlib's description of the zeros of its $\Gamma_{\mathbb{R}}$, `Complex.Gammaℝ_eq_zero_iff`, with the case analysis $n = 0$ or $n = m + 1$ of the lemma ([New/Main.lean](lean:New/Main.lean#L50)). It gets $\zeta(1 - s) = 0$ from $\Lambda(1 - s) = 0$ with no condition on $\Gamma_{\mathbb{R}}(1 - s)$. In Mathlib, "$\Gamma_{\mathbb{R}}(s) = 0$" means "$s$ is a pole of $\Gamma_{\mathbb{R}}$". The proof gets $\zeta$ from the half-plane statement by the instance $q = 1$, $\chi = \chi_0$, with Mathlib's `DirichletCharacter.LFunction_modOne_eq`.
