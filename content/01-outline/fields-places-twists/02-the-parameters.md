---
title: The parameters q₀ and d
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.Parameters
  - New.Parameters.instPrimeSevenModEight
  - New.Parameters.sixty_four_lt_d
  - New.Parameters.d_pow_ne_neg_one
  - New.Parameters.dvd_d_add_one_div_four_of_dvd_q₁
  - New.Parameters.chiK_eq_one_of_dvd
  - New.Parameters.thirteen_le_of_chiK_ne_one
  - New.Parameters.coprime_q₁_d
  - New.chiK
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The parameters $q_0$ and $d$

This section defines the parameters and proves the three facts about them that the rest of the argument uses: $d \equiv 7 \bmod 8$, every prime that divides $q_0$ splits in $K = \mathbb{Q}(\sqrt{-d})$, and $d$ is prime to $q_0$. The first fact is a hypothesis of [Landau's criterion](/chapter/landau-criterion/). The second fact is the reason for the factor $18480$.

### The definition

**Definition (Parameters).** A set of parameters is a pair of natural numbers $(q_0, d)$ with these properties.

1. $18480 \mid q_0$.
2. $d$ is prime.
3. $q_0 \mid 2(d+1)$ and $q_0 \nmid d + 1$.

Lean: `New.Parameters` (New/Reduction/Data/FieldsAndPlaces.lean).

Here $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$. Condition 1 makes $q_0$ even and positive. Write $q_0 = 2h$. Condition 3 says that $h \mid d + 1$ and that the quotient $(d+1)/h$ is odd. So $d + 1$ is an odd multiple of $q_0/2$, that is,
$$d \equiv \frac{q_0}{2} - 1 \pmod{q_0}.$$
Conversely this congruence gives condition 3. So the parameters are a modulus $q_0$ and a prime in the residue class $q_0/2 - 1$ modulo $q_0$. This class is prime to $q_0$: a prime $p \mid q_0$ divides $q_0/2$, since $4 \mid q_0$, and so $d \equiv -1 \bmod p$. By Dirichlet's theorem the class contains infinitely many primes. The one-sided bound must hold for every prime $d$ in the class (see [Landau's criterion](/chapter/landau-criterion/)).

**Remark (Formalization).** The source states the congruence as the two divisibilities of condition 3. This avoids the division $q_0/2$ in $\mathbb{N}$, and it gives $q_0 \neq 0$, since $0 \nmid d + 1$.

### The class of $d$ modulo $8$ and modulo $q_0$

**Lemma.** For parameters $(q_0, d)$, the prime $d$ satisfies $d \equiv 7 \pmod 8$.

Lean: `New.Parameters.instPrimeSevenModEight` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* Since $16 \mid q_0$, we have $8 \mid q_0/2$. Since $q_0/2 \mid d + 1$, we get $8 \mid d + 1$. $\square$

**Remark (Formalization).** The lemma is an instance of the class `PrimeSevenModEight d` of the source, which records that $d$ is prime and $d \bmod 8 = 7$. The results of the library on $K$ assume this class.

Note that $d \equiv 7 \bmod 8$ gives $d \equiv 3 \bmod 4$. So the discriminant of $K = \mathbb{Q}(\sqrt{-d})$ is $-d$, and the ring of integers of $K$ is $\mathbb{Z}[\beta_K]$ with
$$\beta_K = \frac{1 + \sqrt{-d}}{2}, \qquad \beta_K + \bar\beta_K = 1, \qquad \beta_K \bar\beta_K = \frac{d+1}{4}.$$

**Lemma.** For parameters $(q_0, d)$, one has $64 < d$.

Lean: `New.Parameters.sixty_four_lt_d` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* The number $2(d+1)$ is a positive multiple of $q_0$, which is a positive multiple of $18480$. So $2(d+1) \ge 18480$ and $d \ge 9239$. $\square$

The source needs only $d > 64$, in Section 3.

**Lemma.** For parameters $(q_0, d)$ and every $n \ge 0$, one has $d^n \not\equiv -1 \pmod{q_0}$.

Lean: `New.Parameters.d_pow_ne_neg_one` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* Write $d = 2w + 1$. In $\mathbb{Z}/q_0$ we have $2(d+1) = 0$ and $d + 1 \neq 0$. Then $d^2 - 1 = (d+1)(d-1) = (d+1) \cdot 2w = w \cdot 2(d+1) = 0$. So $d^2 = 1$, and every power of $d$ is $1$ or $d$. If $d = -1$ then $d + 1 = 0$, which is false. If $1 = -1$ then $2 = 0$, so $d + 1 = 2(w+1) = 0$, which is false again. $\square$

The lemma is used for the places of class $-1$ modulo $q_0$, in Section 4.

### Every prime of $q_0$ splits in $K$

The main fact of this section is that all primes that divide $q_0$ split in $K$. The proof is short, and it explains the shape of the condition on $d$.

**Proposition.** Let $(q_0, d)$ be parameters, let $s \ge 0$, and let $q_1 = q_0 \cdot \mathrm{towerDeg}(s)$ (defined in Section 3). If $p$ is a prime and $p \mid q_1$, then $p \mid (d+1)/4$.

Lean: `New.Parameters.dvd_d_add_one_div_four_of_dvd_q₁` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* The number $\mathrm{towerDeg}(s)$ is a power of $3$ times a power of $2$, and $2$ and $3$ divide $q_0$. So $p \mid q_0$, and so $p \mid 2(d+1)$. Since $d \equiv 7 \bmod 8$, we can write $2(d+1) = 2^3 \cdot (d+1)/4$. If $p \mid 2^3$ then $p = 2$, and $2 \mid (d+1)/4$ because $8 \mid d + 1$. Otherwise $p \mid (d+1)/4$ directly. $\square$

So the prime divisors of $q_1$ all divide the norm $\beta_K \bar\beta_K = (d+1)/4$. The prime $2$ needs the full power $16 \mid q_0$: with only $8 \mid q_0$, the quotient $(d+1)/4$ could be odd.

Recall the character of $K$. For a prime $d$, let $\chi_K$ be the Legendre symbol $n \mapsto (n/d)$, a Dirichlet character modulo $d$ with values in $\{0, \pm 1\}$.

Lean: `New.chiK` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

For $d \equiv 3 \bmod 4$ this is the character of $K$: an odd prime $p \neq d$ splits in $K$ if and only if $(-d/p) = 1$, and by quadratic reciprocity $(-d/p) = (-1/p)(d/p) = (p/d)$. The prime $2$ splits if and only if $d \equiv 7 \bmod 8$, and then $(2/d) = 1$ too. So for every prime $p \ne d$ we have: $p$ splits in $K$ if and only if $\chi_K(p) = 1$. See Ireland and Rosen, Chapter 13, Section 1, for the decomposition law in quadratic fields.

**Theorem.** Let $(q_0, d)$ be parameters, let $s \ge 0$, and let $p$ be a prime with $p \mid q_1$. Then $\chi_K(p) = (p/d) = 1$.

Lean: `New.Parameters.chiK_eq_one_of_dvd` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* By the proposition, $p \mid (d+1)/4$, so $4p \mid d + 1$, that is, $d \equiv -1 \bmod 4p$. The Jacobi symbol $(p/d)$ depends only on the class of $d$ modulo $4p$, by the reciprocity law for Jacobi symbols. So $(p/d) = (p / (4p - 1))$. The factor $4$ is a square, so $(p/(4p-1)) = (4p/(4p-1))$. Finally $4p \equiv 1 \bmod 4p - 1$, so this symbol is $(1/(4p-1)) = 1$. $\square$

There is a second proof, which is the conceptual one. The minimal polynomial of $\beta_K$ is $X^2 - X + (d+1)/4$. Modulo a prime $p \mid (d+1)/4$ it is $X(X - 1)$, with two distinct roots $0$ and $1$. By the criterion of Dedekind and Kummer (Neukirch, Chapter I, Proposition 8.3) the prime $p$ splits in $K$ as
$$p \mathcal{O}_K = (p, \beta_K)(p, \beta_K - 1).$$
This proof also covers $p = 2$, where the Legendre symbol is not the natural tool. The two ideals are $\mathfrak{p} = (p, \beta_K)$ and $\bar{\mathfrak{p}} = (p, \bar\beta_K)$, since $\bar\beta_K = 1 - \beta_K$.

**Corollary.** Let $(q_0, d)$ be parameters, and let $p$ be a prime with $\chi_K(p) \neq 1$. Then $p \ge 13$.

Lean: `New.Parameters.thirteen_le_of_chiK_ne_one` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* Every prime $p < 13$ is one of $2, 3, 5, 7, 11$, and each of them divides $18480$, hence $q_0$, hence $q_1$ for $s = 0$. The theorem gives $\chi_K(p) = 1$. $\square$

So a prime that is inert or ramified in $K$ is at least $13$. The ramified prime is $d$ itself, and $d \ge 9239$. The source uses the corollary in `New/UpperBound/Divisibility/MarkOperator.lean` and `New/Derivatives/Sharpness/Cases.lean`.

**Lemma.** For parameters $(q_0, d)$ and $s \ge 0$, the numbers $q_1$ and $d$ are coprime.

Lean: `New.Parameters.coprime_q₁_d` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* If the prime $d$ divided $q_1$, the theorem would give $\chi_K(d) = 1$. But $\chi_K(d) = (d/d) = 0$. $\square$

### Why $18480$

The source explains its constants in one paragraph of its guide. The factor $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$ has three jobs.

1. The factor $2^4$ gives $8 \mid d + 1$. So $d \equiv 7 \bmod 8$, which is the hypothesis of the criterion, and $2 \mid (d+1)/4$, so the prime $2$ splits in $K$.
2. The odd factors $3, 5, 7, 11$ are all the odd primes below $13$. With the factor $2$, they make every prime below $13$ split in $K$. This is the corollary above.
3. Together with the factor $3$ of $\mathrm{towerDeg}(s)$, the factor $2^4 \cdot 3 \cdot 5 \cdot 7$ gives $5040 \mid q_1$, since $5040 = 2^4 \cdot 3^2 \cdot 5 \cdot 7$ divides $3 \cdot 18480 = 55440$. Section 3 explains why the argument wants a primitive $5040$-th root of unity.

The factor $11$ serves only the second job. For the third job $2^4$ is necessary, since $16 \mid 5040$.
