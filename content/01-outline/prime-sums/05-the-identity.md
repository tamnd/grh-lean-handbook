---
title: The identity for the total remainder
lean:
  - New/Reduction/PrimeSums.lean
  - New/Reduction/Zeros/PrimeError.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
decls:
  - New.sum_lambdaKResidueClass_mul_posPart
  - New.primeRemainder_eq_sum
  - New.Data.card_aPlaces
  - New.Data.f_eq_card_aPlaces_mul
  - New.Data.mem_aPlaces_iff_of_mul_mem_bPlaces
  - New.Data.card_filter_mem_bPlaces
  - New.Data.sum_aPlaces_lambdaKResidueClass_mul_posPart
  - New.Data.sum_aPlaces_primeSum
  - New.Data.sum_log_weight
  - New.Data.card_aPlaces_mul_mainPrimeSum
  - New.Data.totalRemainder_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The identity for the total remainder

This section proves

$$\mathrm{rem} = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a\, R_1(x_1)\Bigr).$$

The proof has four steps: one weight, the count of places, the sum over $\Phi_a$, and the main terms. After the proof, the section explains each term and lists the points where the source differs from a proof on paper.

### Step 1: one weight

The model case is a prime sum with a constant weight $A/z$.

**Lemma (One weight).** Let $q \geq 1$, let $A$ be a natural number and let $z$ be a real number with $0 < z \leq A$. Then

$$\sum_{n = 1}^{A}\lambda_q(n)\Bigl(\frac{A}{n} - \frac{A}{z}\Bigr)_+ = A\Bigl(R_q(z) + \frac{\log z}{\varphi(q)} + c_q\Bigr).$$

Lean: `New.sum_lambdaKResidueClass_mul_posPart` (New/Reduction/PrimeSums.lean).

*Proof.* By definition $R_q(z) = \sum_{1 \leq n \leq z}\lambda_q(n)(1/n - 1/z) - \log z/\varphi(q) - c_q$. For $n \leq z$ the number $1/n - 1/z$ is at least $0$, so it equals its positive part. For $z < n \leq A$ the positive part of $1/n - 1/z$ is $0$. Since $\lfloor z\rfloor \leq A$, this gives

$$R_q(z) = \sum_{n = 1}^{A}\lambda_q(n)\Bigl(\frac1n - \frac1z\Bigr)_+ - \frac{\log z}{\varphi(q)} - c_q .$$

Since $A > 0$, $(A/n - A/z)_+ = A(1/n - 1/z)_+$. Multiply by $A$ and move the two terms to the left. $\square$

**Lemma (The remainder as a sum to $A$).** For $0 < z \leq A$ with $A$ a natural number,

$$R_q(z) = \sum_{n = 1}^{A}\frac{\lambda_q(n)\,(A/n - A/z)_+}{A} - \frac{\log z}{\varphi(q)} - c_q .$$

Lean: `New.primeRemainder_eq_sum` (New/Reduction/Zeros/PrimeError.lean). It is the only place where the prime remainder enters.

### Step 2: the count of places

The map $\Phi \cong (\mathbb{Z}/q_1\mathbb{Z})^\times \to (\mathbb{Z}/q_0\mathbb{Z})^\times$, reduction modulo $q_0$, is the *class* of a place. It is a surjective homomorphism, and $\Phi_a$ is its kernel.

**Lemma (Number of $a$-places).** $\#\Phi_a = 3 l_0 2^s$, the number $q_1/q_0$.

Lean: `New.Data.card_aPlaces` (New/Reduction/PrimeSums.lean).

**Lemma (Number of places).** $f = \#\Phi_a\cdot\varphi(q_0)$.

Lean: `New.Data.f_eq_card_aPlaces_mul` (New/Reduction/PrimeSums.lean).

*Proof of both.* By definition $q_1 = q_0 \cdot 3 l_0 2^s$. Every prime factor of $3 l_0 2^s$ is $2$ or $3$, and $2$ and $3$ divide $q_0$, since $18480 \mid q_0$. So $\varphi(q_0 \cdot 3 l_0 2^s) = 3 l_0 2^s\,\varphi(q_0)$, and $f = \varphi(q_1) = 3 l_0 2^s\,\varphi(q_0)$. The reduction map is onto, so its kernel $\Phi_a$ has index $\varphi(q_0)$ and $\#\Phi_a = f/\varphi(q_0) = 3 l_0 2^s$. The second lemma follows. $\square$

The next lemma turns a condition modulo $q_1$ into a condition modulo $q_0$.

**Lemma (Class condition).** Let $n \geq 1$ and $\tau \in \Phi$ with $[-n]\tau \in \Phi_b$. Then $\tau \in \Phi_a$ if and only if $n \equiv 1 \pmod{q_0}$.

Lean: `New.Data.mem_aPlaces_iff_of_mul_mem_bPlaces` (New/Reduction/PrimeSums.lean).

*Proof.* Write $\mathrm{cl}$ for the class. Since $\mathrm{cl}$ is a homomorphism and $[-n]\tau \in \Phi_b$, $\mathrm{cl}([-n])\cdot\mathrm{cl}(\tau) = -1$. So $\mathrm{cl}(\tau) = 1$ if and only if $\mathrm{cl}([-n]) = -1$. By the lemma below, this holds if and only if $-n \equiv -1$, that is, $n \equiv 1 \pmod{q_0}$. $\square$

**Lemma (Class of an integer).** For an integer $\nu$, $\mathrm{cl}([\nu]) = -1$ if and only if $\nu \equiv -1 \pmod{q_0}$.

Lean: `New.Parameters.placeClass_placeOfInt_eq_neg_one_iff` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* If $\nu$ is a unit modulo $q_1$, the class of $[\nu]$ is $\nu$ modulo $q_0$, and the claim is clear. If $\nu$ is not a unit modulo $q_1$, then $[\nu]$ is the identity place, of class $1$, and $1 \neq -1$ modulo $q_0$ since $q_0 > 2$. In this case also $\nu \not\equiv -1$: if $\nu \equiv -1 \pmod{q_0}$ then $\nu$ is prime to $q_0$, so prime to $q_1$, which has the same prime factors. $\square$

**Lemma (Count).** For every $n \geq 1$,

$$\#\{\tau \in \Phi_a : [-n]\tau \in \Phi_b\} = \begin{cases}\#\Phi_b & \text{if } n \equiv 1 \pmod{q_0},\\ 0 & \text{otherwise.}\end{cases}$$

Lean: `New.Data.card_filter_mem_bPlaces` (New/Reduction/PrimeSums.lean).

*Proof.* Suppose $n \equiv 1$. Multiplication by $[-n]$ is a bijection of $\Phi$. It maps the set $\{\tau \in \Phi : [-n]\tau \in \Phi_b\}$ onto $\Phi_b$. By the class condition, each $\tau$ in this set lies in $\Phi_a$. So the set in the lemma is this whole set, and it has $\#\Phi_b$ elements. Suppose $n \not\equiv 1$. By the class condition, no $\tau$ with $[-n]\tau \in \Phi_b$ lies in $\Phi_a$. So the set is empty. $\square$

The bijection does not need $[-n]$ to be the place of the class of $-n$. So the junk value of $[\nu]$ at a non-unit $\nu$ does no harm here.

### Step 3: the sum of the prime sums over $\Phi_a$

The telescoping happens at one integer $n$.

**Lemma (One integer).** For every $n \geq 1$,

$$\sum_{\tau \in \Phi_a}\Lambda_K(n)\Bigl(\frac{a}{n} - \kappa([-n]\tau)\Bigr)_+ = \#\Phi_a\,\Lambda_K(n)\Bigl(\frac an - \frac{a}{x_1}\Bigr)_+ + \#\Phi_b\Bigl[\lambda_{q_0}(n)\Bigl(\frac an - \frac ax\Bigr)_+ - \lambda_{q_0}(n)\Bigl(\frac an - \frac a{x_1}\Bigr)_+\Bigr].$$

Lean: `New.Data.sum_aPlaces_lambdaKResidueClass_mul_posPart` (New/Reduction/PrimeSums.lean).

*Proof.* The weight is $\kappa(\sigma) = a/x$ for $\sigma \in \Phi_b$ and $a/x_1$ otherwise, as real numbers. So for every place $\sigma$

$$\Bigl(\frac an - \kappa(\sigma)\Bigr)_+ = \Bigl(\frac an - \frac a{x_1}\Bigr)_+ + \mathbf{1}_{\Phi_b}(\sigma)\Bigl[\Bigl(\frac an - \frac ax\Bigr)_+ - \Bigl(\frac an - \frac a{x_1}\Bigr)_+\Bigr].$$

This is the telescoping: for $\sigma \notin \Phi_b$ the bracket is absent, and for $\sigma \in \Phi_b$ the first term cancels against the last one. Put $\sigma = [-n]\tau$ and sum over $\tau \in \Phi_a$. The first term gives $\#\Phi_a$ times itself. The second gives $\#\{\tau \in \Phi_a : [-n]\tau \in \Phi_b\}$ times the bracket. Multiply by $\Lambda_K(n)$. By the count, the coefficient of the bracket is $\#\Phi_b\,\Lambda_K(n)$ if $n \equiv 1 \pmod{q_0}$ and $0$ otherwise. This is $\#\Phi_b\,\lambda_{q_0}(n)$, since $\lambda_{q_0}(n) = \Lambda_K(n)$ for $n \equiv 1 \pmod{q_0}$ and $\lambda_{q_0}(n) = 0$ otherwise (Lean: `New.lambdaKResidueClass_eq_ite`). $\square$

**Proposition (The sum over $\Phi_a$).**

$$\sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(a, \tau) = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a R_1(x_1)\Bigr) + a\Bigl(\#\Phi_a(\log x_1 + c_1) + \#\Phi_b\,\frac{\log x - \log x_1}{\varphi(q_0)}\Bigr).$$

Lean: `New.Data.sum_aPlaces_primeSum` (New/Reduction/PrimeSums.lean).

*Proof.* Write $s_{\mathrm{fin}}(a, \tau)$ as a sum over $1 \leq n \leq a$ and exchange the two finite sums. By the lemma on one integer, the left side is

$$\#\Phi_a\sum_{n = 1}^{a}\lambda_1(n)\Bigl(\frac an - \frac a{x_1}\Bigr)_+ + \#\Phi_b\Bigl[\sum_{n = 1}^{a}\lambda_{q_0}(n)\Bigl(\frac an - \frac ax\Bigr)_+ - \sum_{n = 1}^{a}\lambda_{q_0}(n)\Bigl(\frac an - \frac a{x_1}\Bigr)_+\Bigr],$$

with $\lambda_1 = \Lambda_K$. The table of sizes gives $0 < x \leq x_1 \leq a$. Apply the lemma on one weight three times, with $A = a$: for $(q, z) = (1, x_1)$, $(q_0, x)$ and $(q_0, x_1)$. Since $\varphi(1) = 1$, the left side is

$$a\,\#\Phi_a\bigl(R_1(x_1) + \log x_1 + c_1\bigr) + a\,\#\Phi_b\Bigl[\Bigl(R_{q_0}(x) + \frac{\log x}{\varphi(q_0)} + c_{q_0}\Bigr) - \Bigl(R_{q_0}(x_1) + \frac{\log x_1}{\varphi(q_0)} + c_{q_0}\Bigr)\Bigr].$$

The constant $c_{q_0}$ cancels in the bracket. Sort the terms into remainders and main terms. $\square$

### Step 4: the main terms

**Lemma (Sum of the logarithms of the weights).**

$$\sum_{\tau \in \Phi}\log\kappa(\tau) = f(\log a - \log x_1) - \#\Phi_b(\log x - \log x_1).$$

Lean: `New.Data.sum_log_weight` (New/Reduction/PrimeSums.lean).

*Proof.* For every place, $\log\kappa(\tau) = \log a - \log x_1 - \mathbf{1}_{\Phi_b}(\tau)(\log x - \log x_1)$, since $\log(a/x) = (\log a - \log x_1) - (\log x - \log x_1)$. Sum over the $f$ places. $\square$

**Lemma (The expected value times $\#\Phi_a$).**

$$\#\Phi_a\, s_{\mathrm{main}} = a\Bigl(\#\Phi_a(\log x_1 + c_1) + \#\Phi_b\,\frac{\log x - \log x_1}{\varphi(q_0)}\Bigr).$$

Lean: `New.Data.card_aPlaces_mul_mainPrimeSum` (New/Reduction/PrimeSums.lean).

*Proof.* Insert the sum of the logarithms into the definition of $s_{\mathrm{main}}$:

$$s_{\mathrm{main}} = a\Bigl(\log a - (\log a - \log x_1) + \frac{\#\Phi_b}{f}(\log x - \log x_1) + c_1\Bigr) = a\Bigl(\log x_1 + c_1 + \frac{\#\Phi_b}{f}(\log x - \log x_1)\Bigr).$$

Multiply by $\#\Phi_a$ and use $f = \#\Phi_a\,\varphi(q_0)$, so $\#\Phi_a\,\#\Phi_b/f = \#\Phi_b/\varphi(q_0)$. $\square$

The right side is the second line of the proposition on the sum over $\Phi_a$. The theorem follows at once.

**Theorem (The total remainder).**

$$\mathrm{rem} = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a\, R_1(x_1)\Bigr).$$

Lean: `New.Data.totalRemainder_eq` (New/Reduction/PrimeSums.lean).

*Proof.* By definition, $\mathrm{rem} = \sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(a, \tau) - \#\Phi_a\, s_{\mathrm{main}}$. The proposition on the sum over $\Phi_a$ writes the first term as the remainders plus the main terms. The lemma on the expected value writes the second term as the same main terms. Subtract. $\square$

### Where each term comes from

The factor $a$ is the length factor of the lemma on one weight: a weight $a/z$ is a cut-off at $z$, and it scales the sum of length $z$ by $a$.

The term $a\,\#\Phi_a\, R_1(x_1)$ is the base level. At every place the weight is at least $a/x_1$. So every $a$-place sees a prime sum of length $x_1$ over all $n$, with no congruence condition. There are $\#\Phi_a$ such places. The modulus is $1$.

The term $a\,\#\Phi_b(R_{q_0}(x) - R_{q_0}(x_1))$ is the correction at the $b$-places. If $[-n]\tau \in \Phi_b$, the weight is $b = a/x$, larger than $a/x_1$, so the cut-off moves from $x_1$ down to $x$. The correction is the sum of length $x$ minus the sum of length $x_1$. Only $n \equiv 1 \pmod{q_0}$ can meet a $b$-place from an $a$-place, and each such $n$ meets $\#\Phi_b$ of them. So the correction is $\#\Phi_b$ times the difference for the progression $n \equiv 1 \pmod{q_0}$.

The coefficient $a\,\#\Phi_b$ of $R_{q_0}(x)$ is positive. So the upper bound for $\mathrm{rem}$ gives an upper bound for $R_{q_0}(x)$, which is all that Landau's criterion needs. The class $-1$ of $\Phi_b$ and the sign in $[-n]\tau$ select the class $n \equiv 1$ of that criterion (Exercise 3).

### Why the weights telescope

Three properties of the weights make the proof work.

1. *Two values.* With two values, the term at a place is the base term plus one correction. More values give one correction for each value (Exercise 5).
2. *Exact quotients.* Each value is $a/z$ for a length $z \leq a$. Then the kernel $(a/n - a/z)_+$ is $a(1/n - 1/z)_+$ with no rounding, and the lemma on one weight applies. The weights are natural numbers, so this needs $x \mid a$ and $x_1 \mid a$. The first holds since $a = xb$. The second holds since $q_1 x_1 \mid b$.
3. *Constant on the places that matter.* The correction is the same at every $b$-place. So the sum over $\tau \in \Phi_a$ reduces to a count, and the count depends only on $n$ modulo $q_0$.

The logarithms of the weights have the same two values. So the mean of $\log\kappa$ in $s_{\mathrm{main}}$ telescopes in the same way, and the main terms cancel exactly.

**Remark (Formalization).** The following points are where the source differs from a proof on paper, or where a reader may suspect a gap at the boundary of a sum. They answer question Q-16 of the register of findings.

1. *The scales.* The source defines $x$ and $x_1$ as the real numbers $e^{\ell}$ and $e^{\ell_1}$, where $\ell$ and $\ell_1$ are the fields `logX` and `logX₁` of the data, and the data state that they are natural numbers. So $\log x$ is the field `logX` exactly.
2. *The weights.* The weight is a natural number, $b$ on $\Phi_b$ and $\lfloor xb/x_1\rfloor$ elsewhere, with the division of natural numbers. The lemma `New.Data.cast_weight` gives $\kappa = a/x$ or $a/x_1$ as real numbers, and its proof uses $x_1 \mid b$. Without the divisibility, the floor would add an error to every term.
3. *The junk place.* For $\nu$ not prime to $q_1$, $[\nu]$ is the identity place. The proof does not need $\Lambda_K(\nu) = 0$ for such $\nu$. The class lemma handles them, since the identity has class $1 \neq -1$. Such $\nu$ do have $\Lambda_K(\nu) = 0$ when they are prime powers: their primes divide $q_0$, and these primes split in $K$ (Section 2).
4. *The terms $\nu > x_1$.* They lie in the range $1 \leq \nu \leq a$, and they contribute $0$ to both sides, since $a/\nu < a/x_1 \leq \kappa$.
5. *The cut at $\nu \leq a$.* The lemma on one weight needs $z \leq A$ with $A = a$. The source proves $x \leq a$ and $x_1 \leq a$ by its automation for sizes. So no term of the sums that define $R_{q_0}(x)$, $R_{q_0}(x_1)$ and $R_1(x_1)$ is lost.
6. *The constants.* The identity holds for any values of $c_{q_0}$ and $c_1$, provided that $R_q$ and $s_{\mathrm{main}}$ use the same ones.

This book checked these points by hand against the source. It did not rerun the Lean checks.
