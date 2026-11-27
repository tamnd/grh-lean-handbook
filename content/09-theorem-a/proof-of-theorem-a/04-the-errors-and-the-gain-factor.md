---
title: The errors and the gain factor
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - New/UpperBound/Size/Estimates.lean
decls:
  - New.Data.smallNonsplitPrimes
  - New.Data.chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes
  - New.Data.divisibilityError
  - New.Data.divisibilityError_nonneg
  - New.Data.divisibilityError_eq_zero
  - New.Data.sum_divisibilityError_mul_log_le
  - New.Data.exists_colengthDvd_gaugeLe_divisibilityError
  - New.Data.gainExponent
  - New.Data.invGainFactor
  - New.Data.prime_of_mem_smallNonsplitPrimes_union
  - New.Data.invGainFactor_pos
  - New.Data.sum_log_smallNonsplitPrimes_union_le
  - New.Data.log_invGainFactor_le
  - New.Data.norm_invGainFactor
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The errors and the gain factor

The divisibility of Section 2 is an existence statement. This section fixes one function $\mathrm{err}$ with its four properties. It then defines the gain factor $c_B$, a positive rational number that divides out the divisibility. The section proves the two facts about $c_B$ that Theorem A uses: a bound for $\log c_B$, used in part (a), and the value of $|c_B|$ at every prime, used in part (b).

### The small nonsplit primes

**Definition (Small nonsplit primes).** $\mathcal{S}$ is the finite set of natural numbers $p < \lceil x_1\rceil$ such that $p$ is prime and $\chi_K(p) \neq 1$.

Lean: `New.Data.smallNonsplitPrimes` (New/UpperBound/Size/Estimates.lean).

**Lemma (Outside the small nonsplit primes).** Let $p$ be a prime with $p \notin \mathcal{S}$. Then $\chi_K(p) = 1$ or $x_1 \leq p$.

Lean: `New.Data.chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* For a natural number $p$, $p < \lceil x_1\rceil$ holds if and only if $p < x_1$. So $p \notin \mathcal{S}$ says that $p \geq x_1$ or $\chi_K(p) = 1$. $\square$

So for a prime $p \notin \mathcal{S}$ the vanishing lemma of Section 2 gives $\mathrm{gain}_p = 0$, and property 2 of the divisibility gives $\mathrm{err}(p) = 0$ if also $p \neq N$.

### The divisibility errors

**Definition (The divisibility errors).** $\mathrm{err} : \mathbb{N} \to \mathbb{R}$ is a function with the four properties of the theorem on the divisibility of the composite lift, chosen once.

Lean: `New.Data.divisibilityError` (New/Reduction/ShortAndEnough.lean).

**Lemma (The four properties of the errors).** The function $\mathrm{err}$ has these properties.

1. $\mathrm{err}(\ell) \geq 0$ for every $\ell$.
2. If $\ell \neq N$, and $\chi_K(\ell) = 1$ or $x_1 \leq \ell$, then $\mathrm{err}(\ell) = 0$.
3. For every finite set $U$ of natural numbers, $\sum_{\ell\in U}\mathrm{err}(\ell)\log\ell \leq f a\log^3 b$.
4. Let $\ell$ be a prime with an embedding $\mathbb{C} \to \mathbb{C}_\ell$, let $\mathcal{O}$ be its valuation ring in $\mathbb{C}$ and $L$ the module of integral ramified source forms. There are a natural number $j \leq \mathrm{err}(\ell)\,D_X$ and an $\mathcal{O}$-submodule $S$ of the source forms with $\mathrm{ColengthDvd}(L, S, \ell^j)$, such that $\mathrm{GaugeLe}(1, \ell^{\mathrm{err}(\ell) - \mathrm{gain}_\ell}, B_{\vartheta,\Psi}\varphi)$ for every twist $\vartheta$, every chain datum $\Psi$ for $\vartheta$ with $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$, and every $\varphi \in S$.

Lean: `New.Data.divisibilityError_nonneg`, `New.Data.divisibilityError_eq_zero`, `New.Data.sum_divisibilityError_mul_log_le`, `New.Data.exists_colengthDvd_gaugeLe_divisibilityError` (New/Reduction/ShortAndEnough.lean).

*Proof.* Each part is the corresponding property of the chosen function in the theorem on the divisibility of the composite lift. In part 4 the source drops the inclusion $S \subseteq L$, which the proof of part (b) does not need. $\square$

**Remark (Formalization).** The definition is `D.exists_err_gaugeLe_compositeLift.choose`. Nothing is known about this function except the four properties. The proof of the divisibility names a witness, the allowed loss of [prime sums and allowed losses](/chapter/archimedean-size/#prime-sums-and-allowed-losses), but `choose` does not unfold to it. So Theorem A holds for every function with the four properties. In particular, no proof in this chapter uses the value $\mathrm{err}(N) = 2mfb$ of the witness. The error at $N$ enters only through property 3, which bounds $\mathrm{err}(N)\log N$ with all the other terms.

### The gain exponents and the gain factor

**Definition (Gain exponents).** For a natural number $\ell$, $g_\ell = \lfloor\mathrm{gain}_\ell - \mathrm{err}(\ell)\rfloor \in \mathbb{Z}$.

Lean: `New.Data.gainExponent` (New/Reduction/ShortAndEnough.lean).

**Definition (The gain factor).** $c_B = \prod_{\ell\in\mathcal{S}\cup\{N\}}\ell^{-g_\ell} \in \mathbb{Q}$.

Lean: `New.Data.invGainFactor` (New/Reduction/ShortAndEnough.lean).

**Lemma (The primes of the product).** Every $\ell \in \mathcal{S}\cup\{N\}$ is prime, and $c_B > 0$.

Lean: `New.Data.prime_of_mem_smallNonsplitPrimes_union`, `New.Data.invGainFactor_pos` (New/Reduction/ShortAndEnough.lean).

*Proof.* The members of $\mathcal{S}$ are prime by definition, and the level $N$ is prime. So each factor $\ell^{-g_\ell}$ is a positive rational number. $\square$

At $N$ the gain is $0$, by the vanishing lemma, since $x_1 \leq N$. So $g_N = \lfloor -\mathrm{err}(N)\rfloor \leq 0$, and the factor $N^{-g_N}$ is a nonnegative power of $N$. It pays for the loss at the level. At $\ell \in \mathcal{S}$ the exponent $g_\ell$ can have either sign.

### The size of the gain factor

**Lemma (The logarithms of the primes).** $\sum_{\ell\in\mathcal{S}\cup\{N\}}\log\ell \leq b$.

Lean: `New.Data.sum_log_smallNonsplitPrimes_union_le` (New/Reduction/ShortAndEnough.lean).

*Proof.* Each $\ell \in \mathcal{S}$ has $\log\ell \leq \ell < \lceil x_1\rceil$, so $\log\ell \leq x_1$, and $\#\mathcal{S} \leq \lceil x_1\rceil$. So the sum is at most $\lceil x_1\rceil x_1 + \log N$. The sizes of the data give $\lceil x_1\rceil x_1 + \log N \leq b$: $\log N \leq 30\,m\log b$ and $x_1^{10^6} \leq b$ ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)). $\square$

**Lemma (Logarithm of the gain factor).**

$$\log c_B \leq -\sum_{\ell\in\mathcal{S}}\mathrm{gain}_\ell\log\ell + f a\log^3 b + b.$$

Lean: `New.Data.log_invGainFactor_le` (New/Reduction/ShortAndEnough.lean).

*Proof.* We have $\log c_B = \sum_{\ell\in\mathcal{S}\cup\{N\}}(-g_\ell)\log\ell$. The floor satisfies $g_\ell > \mathrm{gain}_\ell - \mathrm{err}(\ell) - 1$, so $-g_\ell < -\mathrm{gain}_\ell + \mathrm{err}(\ell) + 1$. As $\log\ell \geq 0$,

$$\log c_B \leq -\sum_{\ell\in\mathcal{S}\cup\{N\}}\mathrm{gain}_\ell\log\ell + \sum_{\ell\in\mathcal{S}\cup\{N\}}\mathrm{err}(\ell)\log\ell + \sum_{\ell\in\mathcal{S}\cup\{N\}}\log\ell.$$

In the first sum the term at $N$ is $0$, as $\mathrm{gain}_N = 0$. So the first sum is the sum over $\mathcal{S}$. Property 3 bounds the second sum by $f a\log^3 b$. The lemma on the logarithms of the primes bounds the third by $b$. $\square$

The bound is used with a factor $2$, as $2\log c_B$. The loss of the integer parts is then $2b$, and the loss of the errors is $2 f a\log^3 b$.

### The gain factor at a prime

**Lemma (The gain factor at a prime).** Let $\ell$ be a prime. In $\mathbb{C}_\ell$, $\|c_B\| = \|\ell\|^{-g_\ell} = \ell^{g_\ell}$.

Lean: `New.Data.norm_invGainFactor` (New/Reduction/ShortAndEnough.lean).

*Proof.* The norm is multiplicative. For a prime $p \neq \ell$, $\|p\| = 1$ in $\mathbb{C}_\ell$, so every factor $p^{-g_p}$ with $p \neq \ell$ has norm $1$. If $\ell \in \mathcal{S}\cup\{N\}$, the only factor left is $\ell^{-g_\ell}$. If $\ell \notin \mathcal{S}\cup\{N\}$, then $\chi_K(\ell) = 1$ or $x_1 \leq \ell$, by the lemma on the primes outside $\mathcal{S}$, and $\ell \neq N$. So $\mathrm{gain}_\ell = 0$ and $\mathrm{err}(\ell) = 0$, hence $g_\ell = 0$, and both sides are $1$. $\square$

The lemma holds for every prime, not only for the primes of the product. This is what part (b) needs: it tests integrality at every $\iota$.

**Example (One small prime).** Suppose $\mathcal{S} = \{3\}$, with $\mathrm{gain}_3 = 3.7$ and $\mathrm{err}(3) = 0.5$, and suppose $\mathrm{err}(N) = 2.2$. Then $g_3 = \lfloor 3.2\rfloor = 3$ and $g_N = \lfloor -2.2\rfloor = -3$, so $c_B = 3^{-3}N^{3}$. At a place above $3$, $\|c_B\| = 3^{3}$. Multiplication by $c_B$ lowers the $3$-adic valuation by $3$. A form divisible by $3^{3.2}$ stays integral, as $3 \leq 3.2$. At a place above $N$, $\|c_B\| = N^{-3}$, and multiplication by $c_B$ raises the valuation by $3 \geq 2.2$. At infinity, $\log c_B = 3\log N - 3\log 3$. The bound of the lemma is $-3.7\log 3 + f a\log^3 b + b$. The excess of $\log c_B$ over $-3.7\log 3$ is $0.7\log 3 + 3\log N$, and this is less than $(\mathrm{err}(3) + 1)\log 3 + (\mathrm{err}(N) + 1)\log N$. Property 3 bounds the errors by $f a\log^3 b$, and $\log 3 + \log N \leq b$.

**Remark (Formalization).** The number $c_B$ is a rational number (type `ℚ`). It is cast to $\mathbb{C}$ in the map $s\mathfrak{p}$ and to $\mathbb{C}_\ell$ in the lemma on the gain factor at a prime. Being rational, it is fixed by every automorphism $\sigma$ of $\mathbb{C}$, and $|\sigma(c_B)| = c_B$. Part (a) uses this. The exponents $g_\ell$ are integers, so $c_B$ is an honest product of integer powers of primes. The source rounds down, so that the integrality in part (b) holds exactly. The cost of the rounding appears only in part (a).
