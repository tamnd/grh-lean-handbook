---
title: The Riemann hypothesis in Mathlib
lean:
  - Statements.lean
  - Main.lean
decls:
  - RiemannZetaZerosOnLine
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Riemann hypothesis in Mathlib

This section reads the first two types of the source. Both are forms of the Riemann hypothesis. One is a definition of Mathlib, and one is a definition of Statements.lean. The section unfolds Mathlib's $\zeta$ down to an integral of a theta function, shows by checked theorems that it is the classical $\zeta$ away from $s = 1$, and computes its values at the points where a reader can expect trouble.

### The classical Riemann hypothesis

For $\operatorname{Re} s > 1$ put $\zeta(s) = \sum_{n \geq 1} n^{-s}$. Riemann showed that $\zeta$ has a meromorphic continuation to $\mathbb{C}$, with one pole, a simple pole at $s = 1$ with residue $1$. He also showed that the function $\xi(s) = \pi^{-s/2} \Gamma(s/2) \zeta(s)$ satisfies $\xi(1 - s) = \xi(s)$ (Riemann 1859; Titchmarsh, Chapter II; Davenport, Chapter 8). The factor $\Gamma(s/2)$ has poles at $s = 0, -2, -4, \ldots$. So $\zeta$ vanishes at $-2, -4, -6, \ldots$. These are the *trivial zeros*. At $s = 0$ the pole of $\Gamma(s/2)$ cancels the pole of $\xi$, and $\zeta(0) = -1/2$.

**Conjecture (Riemann hypothesis).** Every zero of $\zeta$ in $\mathbb{C}$ that is not a trivial zero has real part $1/2$.

The usual form says "every zero in the critical strip $0 < \operatorname{Re} s < 1$". The two forms are equivalent. The last remark of this section gives the argument.

### The two Lean forms

**Definition (Riemann hypothesis in Mathlib).** The proposition `RiemannHypothesis` says: for every $s \in \mathbb{C}$ with $\zeta(s) = 0$, with $s \neq -2(n+1)$ for every $n \in \mathbb{N}$, and with $s \neq 1$, the real part of $s$ is $1/2$.
Mathlib: `RiemannHypothesis`, in Mathlib/NumberTheory/LSeries/RiemannZeta.lean.

The Lean text is this.

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1))
    (_ : s ≠ 1), s.re = 1 / 2
```

**Definition (Zeta zeros on the line).** The proposition `RiemannZetaZerosOnLine` says: for every $s \in \mathbb{C}$, if $\zeta(s) = 0$, and $s \neq -2(n+1)$ for every $n \in \mathbb{N}$, and $s \neq 1$, then $\operatorname{Re} s = 1/2$.
Lean: `RiemannZetaZerosOnLine` (Statements.lean).

The Lean text is this.

```lean
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → s.re = 1 / 2
```

The two texts differ in two places. The source writes the hypotheses with arrows, and Mathlib writes them as unnamed binders. The source writes the cast `(n : ℂ)`, and Mathlib leaves it to the elaborator. A remark below shows that the two propositions are equal by definition. The source uses this: the theorem `riemannZeta_eq_zero_re` in Main.lean, line 8, has the proof term `riemannHypothesis` and nothing more.

### Unfolding Mathlib's zeta function

Mathlib does not define $\zeta$ by the series. It defines $\zeta$ as a special case of the even Hurwitz zeta function, and it builds that function from a theta function by a Mellin transform. The steps are these. All names are in the namespace `HurwitzZeta` unless the text says otherwise.

1. `riemannZeta` is `hurwitzZetaEven 0`, where $0$ is the point $0$ of the circle $\mathbb{R}/\mathbb{Z}$.
2. `hurwitzZetaEven a` is the function $s \mapsto \Lambda_a(s) / \Gamma_{\mathbb{R}}(s)$, changed at the one point $s = 0$ by `Function.update`. At $s = 0$ its value is $-1/2$ if $a = 0$ and $0$ otherwise. Here $\Lambda_a$ is `completedHurwitzZetaEven a`.
3. `Complex.Gammaℝ s` is $\pi^{-s/2} \Gamma(s/2)$. Mathlib's $\Gamma$ is $0$ at the poles $0, -1, -2, \ldots$, because Lean has no partial functions. The theorem `Complex.Gammaℝ_eq_zero_iff` of Mathlib says that $\Gamma_{\mathbb{R}}(s) = 0$ if and only if $s = -2n$ for some $n \in \mathbb{N}$.
4. `completedHurwitzZetaEven a s` is $\tfrac12 \Lambda(s/2)$, where $\Lambda$ is the function `WeakFEPair.Λ` of the pair `hurwitzEvenFEPair a`. This pair is a structure with fields $f$, $g$, $k$, $\varepsilon$, $f_0$, $g_0$. For $a = 0$ the fields are $f = g = \theta$, $k = 1/2$, $\varepsilon = 1$ and $f_0 = g_0 = 1$, where $\theta(x) = \sum_{n \in \mathbb{Z}} e^{-\pi n^2 x}$ for $x > 0$. The sum formula for $\theta$ is the theorem `hasSum_int_evenKernel`.
5. For such a pair, $\Lambda(s) = \Lambda_0(s) - \tfrac1s f_0 - \tfrac{\varepsilon}{k - s} g_0$, and $\Lambda_0$ is the Mellin transform $\int_0^\infty x^{s-1} F(x)\,dx$ of the function `f_modif`. Here $F(x) = f(x) - f_0$ for $x > 1$, and $F(x) = f(x) - \varepsilon x^{-k} g_0$ for $0 < x < 1$.

Put $\omega(x) = \tfrac12(\theta(x) - 1) = \sum_{n \geq 1} e^{-\pi n^2 x}$. For $0 < x < 1$ the theta relation $\theta(x) = x^{-1/2} \theta(1/x)$ gives $F(x) = \theta(x) - x^{-1/2} = 2 x^{-1/2} \omega(1/x)$. For $x > 1$, $F(x) = 2\omega(x)$. Substitute $x \mapsto 1/x$ on $(0,1)$. Then steps 4 and 5 give, for every $s \in \mathbb{C}$,
$$\texttt{completedRiemannZeta}(s) = \int_1^\infty \omega(x)\left(x^{s/2} + x^{(1-s)/2}\right) \frac{dx}{x} - \frac1s - \frac1{1-s}.$$
This is Riemann's formula for $\xi(s)$, from his proof of the functional equation by the theta relation (Titchmarsh, Chapter II). The integral converges for every $s$, because $\omega$ decays like $e^{-\pi x}$. Mathlib states the split as `completedRiemannZeta_eq`, and states that the integral part `completedRiemannZeta₀` is entire as `differentiable_completedZeta₀`. In Lean $1/0 = 0$, so the formula also gives values at $s = 0$ and $s = 1$. Those values are junk.

So a reader who follows the definitions finds the classical construction. But the reader does not have to check this computation. The next theorem fixes $\zeta$ by two checked facts.

### Mathlib's zeta is the classical zeta

**Theorem (Mathlib's zeta function).** Let $\zeta_{\mathrm{cl}}$ be the classical zeta function on $\mathbb{C} \setminus \{1\}$. Then `riemannZeta s` $= \zeta_{\mathrm{cl}}(s)$ for every $s \neq 1$.
Mathlib: `zeta_eq_tsum_one_div_nat_cpow` and `differentiableAt_riemannZeta`, with the identity theorem.

*Proof.* The theorem `zeta_eq_tsum_one_div_nat_cpow` of Mathlib says that for $1 < \operatorname{Re} s$, `riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s`. The term at $n = 0$ is $1/0^s$. Mathlib's complex power gives $0^s = 0$ for $s \neq 0$, and then $1/0 = 0$, so the term at $n = 0$ is $0$. The series converges absolutely for $\operatorname{Re} s > 1$, so the `tsum` is the usual sum. So the two functions agree on the half-plane $\operatorname{Re} s > 1$. The theorem `differentiableAt_riemannZeta` says that `riemannZeta` is complex differentiable at every $s \neq 1$. The classical function is holomorphic there too. The set $\mathbb{C} \setminus \{1\}$ is open and connected, and it contains the half-plane. By the identity theorem the two functions agree on $\mathbb{C} \setminus \{1\}$. $\square$

The theorem leaves one point open, $s = 1$. The definitions fix the value there.

**Example (Special values).** The definitions give these values.

- At $s = 0$: the update in step 2 gives `riemannZeta 0 = -1 / 2`. This is the classical value. Mathlib states it as `riemannZeta_zero`.
- At $s = -2(n+1)$: $\Gamma_{\mathbb{R}}(s) = 0$, so the quotient in step 2 is a division by $0$, and Lean gives $0$. The classical value is also $0$. Mathlib states this as `riemannZeta_neg_two_mul_nat_add_one`.
- At $s = 1$: $\Gamma_{\mathbb{R}}(1) = \pi^{-1/2}\Gamma(1/2) = 1$ (`Complex.Gammaℝ_one`), and the term $1/(1-s)$ of the formula above is $1/0 = 0$. So `riemannZeta 1` is `completedRiemannZeta₀ 1 - 1`. Mathlib computes it: `riemannZeta_one` says `riemannZeta 1 = (γ - log (4 * π)) / 2`, where $\gamma$ is Euler's constant. Numerically this is $(0.57722 - 2.53102)/2 \approx -0.97690$. Mathlib also proves `riemannZeta_one_ne_zero`.

The value at $1$ is junk. The classical $\zeta$ has a pole there. The value is also not the constant term of the Laurent series at $1$, which is $\gamma$. Mathlib gives that constant as `riemannZeta₀ 1 = γ`, for a different function `riemannZeta₀`.

### Remarks on the zeta statements

**Remark (Formalization).** The hypothesis `s ≠ 1` excludes the junk point. Since `riemannZeta 1` is not $0$, the hypothesis is not needed for the truth of the statement: the point $s = 1$ does not satisfy `riemannZeta s = 0`. It costs nothing, and it makes the statement independent of the junk value. A different choice of junk value, for example $0$, would make the statement without the hypothesis false, since $\operatorname{Re} 1 = 1 \neq 1/2$.

**Remark (Formalization).** The excluded points are $-2(n+1)$ for $n \in \mathbb{N}$, that is $-2, -4, -6, \ldots$. The point $s = 0$ is not excluded. This is correct, because `riemannZeta 0 = -1 / 2` is not $0$. Here the update in step 2 matters. Without it, `riemannZeta 0` would be $\Lambda(0)/\Gamma_{\mathbb{R}}(0) = \Lambda(0)/0 = 0$, and the statement would be false at $s = 0$.

**Remark (Formalization).** The right side `1 / 2` has the type `ℝ`, because `s.re` is real. It is the real number $0.5$. In natural numbers `1 / 2` is $0$, but no natural number occurs here.

**Remark (Formalization).** In Mathlib's text, the expression `-2 * (n + 1)` has the type `ℂ`, because `s` is complex. Lean's elaborator for arithmetic puts the cast at the leaf, so the expression is `-2 * ((n : ℂ) + 1)`. This is the source's text. A binder `(_ : P)` with no name in a `∀` is the same term as the arrow `P →`. So the two definitions unfold to the same term, and Lean accepts `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis` by definitional unfolding.

**Remark (Formalization).** The statements say nothing about the multiplicity of zeros or about simple zeros. They are statements about the zero set only.

**Remark (The forms of the hypothesis).** The Lean form quantifies over all of $\mathbb{C}$, and the usual form quantifies over the strip $0 < \operatorname{Re} s < 1$. They are equivalent, by two classical facts that Mathlib proves. First, $\zeta(s) \neq 0$ for $\operatorname{Re} s \geq 1$ (Mathlib: `riemannZeta_ne_zero_of_one_le_re`, which covers $s = 1$ by the junk value). Second, for $\operatorname{Re} s \leq 0$ the functional equation `riemannZeta_one_sub` writes $\zeta(s)$ as a product of $\zeta(1 - s) \neq 0$, a power of $2\pi$, $\Gamma(1 - s)$ and $\cos(\pi(1 - s)/2)$. The product vanishes only where the cosine vanishes, that is at the trivial zeros, and $s = 0$ is not a zero. So every zero outside the strip is trivial, and the Lean form is the strip form.

### How the source proves this statement

The source deduces `RiemannZetaZerosOnLine` from its half-plane theorem `New.grh`, applied at modulus $N = 1$ and the character $1$. The deduction is [New.zeta_zeros_on_line](/decl/New.zeta_zeros_on_line/) in Volume 1. Its proof uses the functional equation `completedRiemannZeta_one_sub` to move a zero with $\operatorname{Re} s < 1/2$ to $1 - s$, and the half-plane theorem to exclude both. Section 6 states the five theorems with their Lean text.
