---
title: Limits, filters and the symbol O
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/QuadraticTwist.lean
decls:
  - New.eventually_primeRemainder_le_rpow
  - New.tendsto_primeRemainder
  - New.tendsto_sub_mul_logDerivMean
  - New.zero_density_quadTwist
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Limits, filters and the symbol O

Analysis in Mathlib speaks of limits through filters. A reader needs only a few of them, and this section explains those few on the statements of the analytic part of the argument: the one-sided bound, the prime number theorem for the weights, a residue, and the count of bad primes. The section ends with the symbol $O$, whose constant Lean does not show.

### Filters in one paragraph

A filter on a set $X$ is a collection of subsets of $X$ that are "large" in a given sense: it contains $X$, it is closed under supersets, and it is closed under finite intersections. Three filters occur in almost every analytic statement of the source. The filter `atTop` on $\mathbb{R}$ or $\mathbb{N}$ contains the sets that contain a half-line $[y_0, \infty)$. The filter `𝓝 a` contains the neighbourhoods of a point $a$. The filter `𝓝[≠] a` contains the sets that contain $U \setminus \{a\}$ for a neighbourhood $U$ of $a$: the punctured neighbourhoods. Similarly `𝓝[>] a` is the filter of right half-neighbourhoods $(a, a + \varepsilon)$.

Two notations use filters. The statement `∀ᶠ y in F, P y` says that the set of $y$ with $P(y)$ is in $F$. For `F = atTop` it reads "$P(y)$ holds for all large $y$": there is $y_0$ with $P(y)$ for every $y \geq y_0$. The statement `Tendsto f F G` says that the preimage under $f$ of every set of $G$ is in $F$. For `Tendsto f atTop (𝓝 a)` this is $f(y) \to a$ as $y \to \infty$. For `Tendsto f (𝓝[≠] ρ) (𝓝 a)` it is $f(z) \to a$ as $z \to \rho$ with $z \neq \rho$. The value $f(\rho)$ plays no part, which matters when $f(\rho)$ is a junk value (Section 3).

### Eventually

**Theorem (One-sided bound).** Let $q_0 \geq 1$ be a multiple of $18480$, let $d$ be a prime with $d \equiv q_0/2 - 1 \pmod{q_0}$, and let $\varepsilon > 0$. Then $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for all large real $y$, where $R_{q_0}$ is the prime remainder of Section 2 for the prime $d$.

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

```lean
theorem eventually_primeRemainder_le_rpow {q₀ : ℕ} [NeZero q₀] (hq₀ : 18480 ∣ q₀) {d : ℕ}
    [hd_prime : Fact d.Prime] (hd : d ≡ q₀ / 2 - 1 [MOD q₀]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℝ in atTop, primeRemainder d q₀ y ≤ y ^ (-1 / 2 + ε) := by
```

This is [Theorem](/decl/New.eventually_primeRemainder_le_rpow/) of Volume 1, the main output of the argument. Read the hypotheses. The modulus $q_0$ and the prime $d$ are implicit: Lean finds them from the other hypotheses. The instance `[NeZero q₀]` gives $q_0 \neq 0$, and `[hd_prime : Fact d.Prime]` gives that $d$ is prime; the second has a name, so the proof can use it. The congruence `d ≡ q₀ / 2 - 1 [MOD q₀]` is in $\mathbb{N}$: `q₀ / 2` is the quotient in $\mathbb{N}$ and `- 1` is truncated. Since $q_0$ is even and $q_0 \geq 18480$, both are the classical numbers. The power `y ^ (-1 / 2 + ε)` is a real power with a real exponent, and it is the classical one, since only large $y > 0$ matter.

**Remark (Formalization).** The conclusion is `∀ᶠ y in atTop`. So the statement says: there is $y_0$, which may depend on $q_0$, $d$ and $\varepsilon$, with the bound for all $y \geq y_0$. It gives no value of $y_0$. The criterion of Landau type in [the Landau criterion](/chapter/landau-criterion/) needs only this form, because a bound for large $y$ is all that the analytic continuation uses.

### Tendsto

**Theorem.** Let $d \neq 2$ be a prime, and let $q \geq 1$ be prime to $d$. Then $R_q(y) \to 0$ as $y \to \infty$.

Lean: `New.tendsto_primeRemainder` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

```lean
theorem tendsto_primeRemainder (hd : d ≠ 2) (h_cop : q.Coprime d) :
    Tendsto (primeRemainder d q) atTop (𝓝 0) := by
```

The hypotheses $d$ prime and $q \neq 0$ are section variables of the file, as in Section 2. The first line of the proof is `have h_le : ∀ᶠ y : ℝ in atTop, ‖primeRemainder d q y‖ ≤ 1 / y.log`: the proof first shows $|R_q(y)| \leq 1/\log y$ for large $y$, and then that $1/\log y \to 0$. This shows a common pattern. A bound that holds eventually gives a limit, by a lemma of Mathlib on filters (squeeze). In [the weighted prime remainder](/chapter/weighted-prime-remainder/) this is [Theorem](/decl/New.tendsto_primeRemainder/).

A limit along a punctured neighbourhood gives a residue.

**Lemma.** Let $q \geq 1$ and $\rho \in \mathbb{C}$. Then $(z - \rho)\,G_q(z)$ tends to
$$\frac{1}{\varphi(q)} \sum_{\psi \bmod q} \bigl(\operatorname{ord}_\rho E_{\psi\chi_K} - \operatorname{ord}_\rho E_\psi\bigr)$$
as $z \to \rho$ with $z \neq \rho$. Here $G_q$ is `logDerivMean d q` and $E_\psi$ is as in Section 3.

Lean: `New.tendsto_sub_mul_logDerivMean` (New/Reduction/Zeros/PrimeError.lean).

```lean
lemma tendsto_sub_mul_logDerivMean (ρ : ℂ) :
    Tendsto (fun z : ℂ ↦ (z - ρ) * logDerivMean d q z) (𝓝[≠] ρ)
      (𝓝 ((∑ ψ : DirichletCharacter ℂ q, (analyticOrderNatAt (entireL (quadTwist ψ d)) ρ -
        analyticOrderNatAt (entireL ψ) ρ : ℂ)) / φ q)) := by
```

The filter `𝓝[≠] ρ` makes the limit a limit from the punctured neighbourhood. The lemma says that $G_q$, a difference of logarithmic derivatives, has at most a simple pole at $\rho$ with this residue. Since $G_q(\rho)$ is a junk value where $G_q$ has a pole, the filter `𝓝[≠] ρ` is needed. A filter `𝓝 ρ` would make the statement false or meaningless at a pole.

### The symbol O

Mathlib writes $f = O(g)$ along a filter $F$ as `f =O[F] g`. This is `Asymptotics.IsBigO F f g` (Mathlib). It says: there is a constant $C$ with $\|f(x)\| \leq C\,\|g(x)\|$ for all $x$ in a set of $F$. For `F = atTop` this is the classical $f(x) = O(g(x))$ as $x \to \infty$. The source also uses the symbol inside proofs. In the proof of `New.LSeries_lambdaKResidueClass` it writes:

```lean
  have h_sum : (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 + r : ℝ) := by
```

This is the bound $\sum_{k \leq n} |f(k)| = O(n^{1+r})$ as $n \to \infty$, which partial summation needs. Both sides are functions of $n \in \mathbb{N}$, and the right side casts $n$ and $1 + r$ to $\mathbb{R}$ to make a real power.

**Theorem (Bad primes are rare).** Let $N \geq 1$, $\delta > 0$, $H \in \mathbb{R}$ and $a \in \mathbb{Z}/N\mathbb{Z}$. Assume that every prime $d$ with $d \equiv a \pmod N$ has $d \equiv 7 \pmod 8$ and is prime to $N$. Then the number of $d \in \{1, \dots, X\}$ that are bad for $(a, 1/2 + 9\delta, H)$ in the sense of Section 2 is $O(X^{1 - \delta/2})$ as $X \to \infty$.

Lean: `New.zero_density_quadTwist` (Lib/Analytic/QuadraticTwist.lean).

```lean
open scoped Classical in
lemma zero_density_quadTwist {N : ℕ} [NeZero N] {δ : ℝ} (hδ : 0 < δ) (H : ℝ) {a : ZMod N}
    (h_class : ∀ d : ℕ, d.Prime → (d : ZMod N) = a → d % 8 = 7 ∧ N.Coprime d) :
    (fun X : ℕ ↦ (#{d ∈ Ioc 0 X | IsBadPrime a (1 / 2 + 9 * δ) H d} : ℝ)) =O[atTop]
      fun X : ℕ ↦ (X : ℝ) ^ (1 - δ / 2) := by
```

In [fields, places and twists](/chapter/fields-places-twists/) this is [Theorem](/decl/New.zero_density_quadTwist/). The count is a natural number, cast to `ℝ` so that it can be compared with a real power.

**Remark (Formalization).** The constant of $O$ is not explicit. It exists for each choice of the arguments, so it may depend on $N$, $\delta$, $H$ and $a$, and the statement says nothing about how. The same holds for the point from which the bound holds. The file uses the theorem to show that some prime of the class $a$ is not bad. The proof is by contradiction. If every prime of the class were bad, the count would bound the number of primes of the class up to $X$ by $O(X^{1 - \delta/2})$, and then $\sum \log d / d$ over the primes of the class would converge. This contradicts the theorem of Dirichlet on primes in progressions. For that use an implicit constant is enough. A reader who wants a numerical bound on the size of the first good prime cannot get it from this statement.

### Choice inside a proof

The proof of the last theorem starts with a step that combines Section 4 and this section. It proves, for each character $\xi$ modulo $N$, the existence of a primitive character that induces it, by [Lemma](/decl/New.exists_isPrimitive_changeLevel_eq/) of Section 4. Then it writes `choose M hMN ψ hM hψ h_induced using h_exists`. The tactic `choose` turns the statement $\forall \xi\, \exists M\, \exists \psi \dots$ into functions $\xi \mapsto M(\xi)$ and $\xi \mapsto \psi(\xi)$ with their properties. This is the axiom of choice in a proof. It is allowed because the goal is a proposition, and it adds no datum to any statement.

### What to take from the filters

A statement with `∀ᶠ y in atTop` is a statement for all large $y$, with no explicit threshold. A statement with `Tendsto` is a limit, and the filter says from where: `𝓝[≠] ρ` ignores the point $\rho$ and its junk value. A statement with `=O[atTop]` has an implicit constant that may depend on every argument of the statement.
