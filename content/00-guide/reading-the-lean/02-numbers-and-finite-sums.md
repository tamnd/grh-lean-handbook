---
title: Numbers, coercions and finite sums
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/ZeroSymmetry.lean
  - Lib/Analytic/QuadraticTwist.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.lambdaKSum
  - New.primeRemainder
  - New.IsBadPrime
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Numbers, coercions and finite sums

This section shows how the source writes numbers, maps between number systems, and finite sums and products. The examples are the weighted prime sums of [the weighted prime remainder](/chapter/weighted-prime-remainder/), where the argument starts, and a count of primes from the choice of the prime $d$.

### Number systems are different types

In Lean, $\mathbb{N}$, $\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{R}$ and $\mathbb{C}$ are five different types, written `ℕ`, `ℤ`, `ℚ`, `ℝ` and `ℂ`. A natural number is not a complex number. There is a map from `ℕ` to `ℂ`, and Lean inserts it where an expression needs it. Such a map is a coercion. Lean prints it as an arrow `↑n`, and the source often writes it as a type ascription `(n : ℂ)`. The ring `ZMod N` of residues modulo $N$ is also a type, with a coercion from `ℕ` and from `ℤ`. The units of a ring $R$ are a type `Rˣ`, with a coercion to $R$ (Section 4).

A reader must know where each coercion goes, because the operations differ. Here are the rules that matter most in this source.

1. Subtraction in `ℕ` is truncated: $a - b = 0$ if $a \leq b$. Division in `ℕ` rounds down. A cast before the operation and a cast after it give different values.
2. The power `x ^ n` with `n : ℕ` is the power in a monoid: repeated multiplication. The power `x ^ y` with `y : ℝ` and `x : ℝ` is `Real.rpow` (Mathlib), and with `y : ℂ` and `x : ℂ` it is `Complex.cpow` (Mathlib). These are different functions, with junk values at a base $0$ or at a negative base (Section 3).
3. A Dirichlet character `χ : DirichletCharacter ℂ N` is a function on `ZMod N`. So `χ p` with `p : ℕ` means $\chi$ applied to the residue class of $p$. A character with values in `ℤ` is cast to `ℝ` or `ℂ` where needed.
4. The totient `φ q` is a natural number. In a real formula it is cast to `ℝ`.

**Example.** In [Lemma](/decl/New.prod_euler_factor_ne_zero/) of Section 1 the factor is written `(1 - χ p * (p : ℂ) ^ (-s))`. The term `χ p` is $\chi$ at the class of $p$ in `ZMod N`, a complex number. The term `(p : ℂ)` is the prime $p$ as a complex number, and `(p : ℂ) ^ (-s)` is the complex power $p^{-s}$. Without the ascription `(p : ℂ)`, Lean could not raise $p$ to a complex power.

### Finite sums and products

A finite sum is written `∑ x ∈ A, f x`, where `A` is a finite set of type `Finset`. A product is written `∏ x ∈ A, f x`. The common finite sets are intervals of natural numbers: `Icc a b` is $\{a, \dots, b\}$, `Ioc a b` is $\{a + 1, \dots, b\}$, and `Ico a b` is $\{a, \dots, b - 1\}$. The set `M.primeFactors` is the set of primes that divide $M$. For $M = 0$ it is empty, so the product in Section 1 is $1$ when $M = 0$. A sum over all elements of a finite type is written without a set: `∑ ψ : DirichletCharacter ℂ q, f ψ` is the sum over all characters modulo $q$. The number of elements of a finite set is `#A` (or `A.card`), and `#{x ∈ A | P x}` is the number of $x \in A$ with $P(x)$.

The floor of a real number $y$ as a natural number is `⌊y⌋₊`. It is the largest $n \in \mathbb{N}$ with $n \leq y$ when $y \geq 0$, and it is $0$ when $y < 0$. So `Icc 1 ⌊y⌋₊` is the set of integers $n$ with $1 \leq n \leq y$, and it is empty for $y < 1$.

### The weighted prime sums

Fix a prime $d$ and a modulus $q$. Let $\chi_K(n) = (n/d)$ be the Legendre symbol, and let $\Lambda$ be the von Mangoldt function. Define the weight
$$\lambda(n) = \begin{cases} \Lambda(n)\,(1 - \chi_K(n)) & \text{if } n \equiv 1 \pmod q, \\ 0 & \text{otherwise.} \end{cases}$$
The source writes $\lambda$ as `lambdaKResidueClass d q`. Its Lean text is `def lambdaKResidueClass (n : ℕ) : ℝ := residueClass (1 : ZMod q) n * (1 - chiK d n)`. The first factor is Mathlib's restriction of $\Lambda$ to the class of $1$ modulo $q$. The second factor has `chiK d n`, an integer, cast to a real number. Since $\chi_K(n) \in \{-1, 0, 1\}$, the weight satisfies $0 \leq \lambda(n) \leq 2\Lambda(n)$.

**Definition.** For $r \in \mathbb{N}$ and $y \in \mathbb{R}$, let
$$S_r(y) = \frac{1}{y^r} \sum_{1 \leq n \leq y} \frac{\lambda(n)}{n}\, n^r.$$

Lean: `New.lambdaKSum` (New/Reduction/Zeros/PrimeError.lean).

The Lean text is this.

```lean
def lambdaKSum (r : ℕ) (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, lambdaKResidueClass d q n / n * n ^ r) / y ^ r
```

The arguments `d` and `q` do not appear in the head. They come from the line `variable (d : ℕ) [Fact d.Prime] (q : ℕ)` of the file (Section 1). So the full name takes $d$, a proof that $d$ is prime, $q$, $r$ and $y$, in this order, and the source writes `lambdaKSum d q 0 x`. In the sum, $n$ is a natural number. In `lambdaKResidueClass d q n / n` Lean casts $n$ to `ℝ`, because the numerator is real. The power `n ^ r` and the power `y ^ r` are powers with exponent in `ℕ`. The source uses only $r = 0$ and $r = 1$: $S_0(y) = \sum_{n \leq y} \lambda(n)/n$ and $S_1(y) = y^{-1}\sum_{n \leq y}\lambda(n)$.

**Definition (The prime remainder).** Let $q \geq 1$. For $x \in \mathbb{R}$, let
$$R_q(x) = S_0(x) - S_1(x) - \frac{\log x}{\varphi(q)} - \operatorname{Re} G_q(1),$$
where $G_q$ is the function `logDerivMean d q` of [the weighted prime remainder](/chapter/weighted-prime-remainder/).

Lean: `New.primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

The Lean text is this.

```lean
def primeRemainder [NeZero q] (x : ℝ) : ℝ :=
  lambdaKSum d q 0 x - lambdaKSum d q 1 x - x.log / φ q - re (logDerivMean d q 1)
```

Here `x.log` is `Real.log x`, `φ q` is cast to `ℝ`, and the `1` in `logDerivMean d q 1` is the complex number $1$. For $x \geq 1$, $S_0(x) - S_1(x) = \sum_{n \leq x} \lambda(n)(1/n - 1/x)$, and this is the form in the docstring of the source. [Theorem](/decl/New.tendsto_primeRemainder/) of Volume 1 says that $R_q(x) \to 0$ as $x \to \infty$ when $d \neq 2$ and $q$ is prime to $d$, and Section 5 reads its Lean form.

**Remark (Formalization).** The function $R_q$ is defined for every real $x$, but it has its classical meaning only for $x \geq 1$. For $x < 1$ the sum is empty. At $x = 0$ the term $S_1(0)$ is a division by $0$, which Lean sets to $0$, and $\log 0 = 0$ in Lean. For $x < 0$, Lean sets $\log x = \log |x|$. None of these values matter. Every statement about $R_q$ in the source is about large $x$, or about $R_q(e^v)$ with $v > 0$, as in the integral of [Theorem](/decl/New.integral_primeRemainder/). A reader must still check, for each statement, that it does not use $R_q$ at a point $x < 1$.

**Example.** Take $q = 1$ and $d = 7$. Every $n$ is $\equiv 1 \pmod 1$, so $\lambda(n) = \Lambda(n)(1 - (n/7))$. The squares modulo $7$ are $1, 2, 4$. So $(2/7) = 1$ and $(3/7) = -1$, and $\lambda(1) = 0$, $\lambda(2) = 0$, $\lambda(3) = 2\log 3$. At $x = 3$ the sum $S_0(3)$ is $\frac{2}{3}\log 3$ and $S_1(3)$ is $\frac{1}{3} \cdot 2\log 3$. The two terms cancel, and $R_1(3) = -\log 3 - \operatorname{Re} G_1(1)$. In Lean, `⌊(3 : ℝ)⌋₊` is $3$, the set `Icc 1 3` is $\{1, 2, 3\}$, and `φ 1` is $1$.

### Counts of primes

The choice of the prime $d$ in [fields, places and twists](/chapter/fields-places-twists/) uses a count of primes with a property. The source writes it with `#{...}`.

**Definition.** Let $N \geq 1$, $a \in \mathbb{Z}/N\mathbb{Z}$, $\beta, H \in \mathbb{R}$ and $d \in \mathbb{N}$. The natural number $d$ is a bad prime for $(a, \beta, H)$ if $d \equiv a \pmod N$ and there is a Dirichlet character $\xi$ modulo $N$ such that `IsPrimeWithTwistZero ξ β H d` holds. That predicate of the same file is a structure with two fields: $d$ is prime, and there is $s \in \mathbb{C}$ with $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq H$ and $L(s, \xi\,(\cdot/d)) = 0$, where $\xi\,(\cdot/d)$ is the twist `quadTwist ξ d`, a character modulo $Nd$.

Lean: `New.IsBadPrime` (Lib/Analytic/QuadraticTwist.lean).

```lean
def IsBadPrime (a : ZMod N) (β H : ℝ) (d : ℕ) : Prop :=
  (d : ZMod N) = a ∧ ∃ ξ : DirichletCharacter ℂ N, IsPrimeWithTwistZero ξ β H d
```

The first clause casts $d$ to `ZMod N` and compares it with $a$. This is the congruence $d \equiv a \pmod N$. The count of bad primes up to $X$ is then `#{d ∈ Ioc 0 X | IsBadPrime a (1 / 2 + 9 * δ) H d}`, the number of $d \in \{1, \dots, X\}$ that are bad for $(a, 1/2 + 9\delta, H)$. To count, Lean must decide the property for each $d$. The property involves an existence statement over characters and zeros, and Lean has no algorithm for it. The source opens the scope `Classical` for this statement (`open scoped Classical in`), which makes every proposition decidable by the axiom of choice. This changes nothing for a reader: the count is the usual count. Section 5 reads the full statement, with its symbol $O$.

### What to take from the coercions and sums

Read the type of each number. Find each cast. A cast of a natural number difference, or of a quotient in `ℕ`, is a place to stop and check. A finite sum is the usual sum over a finite set. Its set is often an interval `Icc 1 ⌊y⌋₊`, which is empty for $y < 1$. A function of a real variable is defined on all of $\mathbb{R}$, even where the mathematics needs only large values, and a reader must check that the statements use it only there.
