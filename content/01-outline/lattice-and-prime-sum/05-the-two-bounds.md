---
title: The two bounds and the main inequality
lean:
  - New/Reduction/MainInequality.lean
decls:
  - New.star_inequality
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The two bounds and the main inequality

This section gives the two bounds of the source, shows where the prime sum enters, and proves the main inequality $m \operatorname{rem} \leq f a \log^5 b$ from Theorems A, B and C. The theorems are proved in Volumes 9 to 11.

### The objects

Fix data $D$ for parameters $P$ ([the data and its sizes](/chapter/data-and-sizes/)). Write $f$ for the number of infinite places of $E$, $a = xb$ for the long order, $\kappa(\tau)$ for the weight at a place $\tau$, $k = r + 1 - m$ for the rank of the source, and $d_T \geq 1$ for the dimension of the space of target forms. The size of a derivative of order $j$ and the prime sum are
$$s_\infty(j) = \log j! + j\log(M/\Omega), \qquad s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu)\Bigl(\frac{y}{\nu} - \kappa(-\nu\sigma)\Bigr)^{+}$$
(`New.Data.jetSize`, `New.Data.primeSum`). The source defines three numbers from them (New/Reduction/PrimeSums.lean).

- The main amount $\mathrm{mainAmount} = m k \sum_{\tau} \bigl(s_\infty(\kappa(\tau)) - s_{\mathrm{fin}}(\kappa(\tau), \tau)\bigr)$, summed over all $f$ infinite places (`New.Data.mainAmount`). It is at least $x^4 f a$ (`New.Data.le_mainAmount`), so it is positive and very large.
- The expected value $s_{\mathrm{main}} = a\bigl(\log a - \tfrac1f\sum_\tau \log\kappa(\tau) + c_1\bigr)$ (`New.Data.mainPrimeSum`).
- The total remainder $\operatorname{rem} = \sum_{\tau \in \Phi_a}\bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr)$ (`New.Data.totalRemainder`).

The total remainder is a weighted prime remainder in disguise. By [Theorem](/decl/New.Data.totalRemainder_eq/),
$$\operatorname{rem} = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_a\, R_1(x_1)\Bigr).$$
So an upper bound for $\operatorname{rem}$ is an upper bound for $R_{q_0}(x)$, up to the values at the second cut-off $x_1$, where the prime number theorem applies.

### Where the prime sum enters

The forms of the source are built by a chain of $m$ theta lifts. The size of the chain and its divisibility are computed separately ([Theorems A, B and C](/chapter/theorems-a-b-c/)).

1. Size. If the values of a source form $\varphi$ have squared norm at most $e^B$ at a conjugate, the lift of $\varphi$ by the chain has squared norm at most
$$\exp\Bigl(B + \mathrm{mainAmount} - m\operatorname{rem} + 2\sum_{p} \mathrm{gain}_p \log p + f a\log^3 b\Bigr)$$
at that conjugate (`New.Data.weylNormSq_compositeLift_le`). The sum runs over the primes $p < x_1$ that do not split in $K$, and $\mathrm{gain}_p$ is the divisibility at $p$ that the source asks of the chain.
2. The gains are prime sums. The source proves the identity
$$2\sum_p \mathrm{gain}_p \log p = m\sum_{\tau \in \Phi_a} s_{\mathrm{fin}}(a, \tau) + m k \sum_\tau s_{\mathrm{fin}}(\kappa(\tau), \tau)$$
(`New.Data.two_mul_sum_gain_mul_log`). With the definitions above it gives
$$\mathrm{mainAmount} - m\operatorname{rem} + 2\sum_p \mathrm{gain}_p\log p = m\,\#\Phi_a\, s_{\mathrm{main}} + m k\sum_\tau s_\infty(\kappa(\tau))$$
(`New.Data.mainAmount_sub_add_two_mul_sum_gain`). The right side has no prime sum. So the size of the chain depends only on the expected value $s_{\mathrm{main}}$, and the actual prime sums enter only through the gains.
3. Dividing out the gains. The source multiplies the lifts by the rational number $c_B = \prod_\ell \ell^{-g_\ell}$, where $g_\ell = \lfloor \mathrm{gain}_\ell - \mathrm{err}_\ell \rfloor$ and $\ell$ runs over the small nonsplit primes and the level $N$ (`New.Data.invGainFactor`). Then $\log c_B \leq -\sum_\ell \mathrm{gain}_\ell \log \ell + f a\log^3 b + b$ (`New.Data.log_invGainFactor_le`). The forms stay integral.

After the division, the term $2\sum_p \mathrm{gain}_p \log p$ cancels against $2\log c_B$, and the exponent becomes $\mathrm{mainAmount} - m\operatorname{rem}$ plus errors. If there are more primes than expected, then $\operatorname{rem} > 0$, the gains are larger, and the forms after the division are shorter by the factor $e^{-m \operatorname{rem}}$. The factor $m$ comes from the $m$ lifts: each lift contributes the divisibility $s_{\mathrm{fin}}(a,\tau)$ at each $a$-place.

The level $N$ of the forms pays the excess of the lifts. The restriction of the chain saves $\#\Phi_a\, a\log N$, and $m(s_\infty(a) - s_{\mathrm{main}}) - a\log N \leq 32\, a\log b$ (`New.Data.mul_jetSize_sub_mainPrimeSum_sub_le`). [The data and its sizes](/chapter/data-and-sizes/) explains the size of $N$.

### The upper bound: Theorems A and B

Theorem A has two parts ([Theorems A, B and C](/chapter/theorems-a-b-c/)). Write $\mathrm{src}$ for the space of ramified source forms, $s\mathfrak p$ for the map from the source to the target given by an element $s$ of a finite group $G$ (`New.Data.normalizedPoincare`), $\Theta_1$ for the chain of lifts for the trivial twist, and $\|\cdot\|_\sigma^2$ for the squared norm of the conjugate by an automorphism $\sigma$ of $\mathbb{C}$.

*Theorem A (a)* (`New.Data.span_short_integralRamified_eq_top`, New/Reduction/ShortAndEnough.lean). The space $\mathrm{src}$ is spanned by the forms $\varphi$ that are integral at every $\iota\colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ and satisfy
$$\|\Theta_1(s\mathfrak p\,\varphi)\|_\sigma^2 \leq \exp\bigl(\mathrm{mainAmount} - m\operatorname{rem} + f a\log^4 b\bigr) \qquad \text{for all } s \in G \text{ and all } \sigma .$$

*Theorem A (b)* (`New.Data.indexLe_normalizedPoincare`). Let $t \subset G$ be finite, and let $y_1, \dots, y_n$ be target forms such that each $y_i$ is $s\mathfrak p\,\varphi$ for some $s \in t$ and some $\varphi \in \mathrm{src}$ integral at every $\iota$. Then $y$ has index at most $\#t \cdot \dim \mathrm{src} \cdot 2 f a\log^3 b$ in the target lattice.

*Theorem B* (`New.Data.enough_forms`). We have $d_T > 0$, and there is a finite $t \subset G$ with
$$\#t \cdot \dim\mathrm{src} \leq 5\, d_T \log(1 + 2b^2), \qquad (1 - 4/b^2)\, d_T \leq \dim \sum_{s \in t} s\mathfrak p(\mathrm{src}).$$

So a few translates of the source fill almost all of the target. The index bound of Theorem A (b) then costs at most $10\, d_T \log(1 + 2b^2)\, f a\log^3 b$.

### The lower bound: Theorem C

[Theorem](/decl/New.Data.integral_forms_long/) of [twisted lattices](/chapter/twisted-lattices/) is Theorem C. Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2) d_T$, index at most $\delta$ and covolume at most $c$. Then
$$d_T\bigl(\mathrm{mainAmount} - 3 f a\log^4 b\bigr) \leq c + 2\delta .$$
Its proof is the product formula for the family $Z(1)/Z(\xi_\iota)$ of ratios of Gram determinants (Section 4). The main amount enters through the height of this family.

### The main inequality

**Theorem (Main inequality).** For data $D$ for the parameters $P$,
$$m \operatorname{rem} \leq f a\log^5 b .$$

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

The hypotheses are the fields of $D$, for example $(\log b)^{100} \leq x$ and $x_1^{10^6} \leq b$.

*Proof.* Let $L = f a\log^4 b$ and $\lambda = \mathrm{mainAmount} - m\operatorname{rem} + L$.

Step 1: the family. Theorem B gives $t$. Let $S \subset \mathrm{src}$ be the set of short integral forms of Theorem A (a). It spans $\mathrm{src}$, so the images $s\mathfrak p(S)$, $s \in t$, span $\sum_{s\in t} s\mathfrak p(\mathrm{src})$. Choose a basis $y_1, \dots, y_n$ of this span among the images. Then $(1 - 4/b^2)d_T \leq n \leq d_T$.

Step 2: the covolume. Each $y_i$ has $\|\Theta_1 y_i\|_\sigma^2 \leq e^\lambda$ for all $\sigma$. By Hadamard's inequality ([Theorem](/decl/New.TwistedLattice.covolumeLe_of_normSqAt_le/)), $y$ has covolume at most $n\lambda$.

Step 3: the index. Each $y_i$ is the image of an integral form. By Theorem A (b) and the bound on $\#t$ in Theorem B, $y$ has index at most $d_T I$, where $I = 10 \log(1 + 2b^2)\, f a\log^3 b$.

Step 4: the comparison. Theorem C gives
$$d_T(\mathrm{mainAmount} - 3L) \leq n(\mathrm{mainAmount} - m\operatorname{rem} + L) + 2 d_T I .$$
Since $\mathrm{mainAmount} \geq 0$ (`New.Data.mainAmount_nonneg`) and $n \leq d_T$, we have $n(\mathrm{mainAmount} + L) \leq d_T(\mathrm{mainAmount} + L)$. Add the two inequalities. The terms $d_T\,\mathrm{mainAmount}$ and $n\,\mathrm{mainAmount}$ cancel, and
$$n\, m\operatorname{rem} \leq d_T\,(4L + 2I).$$

Step 5: the division. The scales give $4/b^2 \leq 1/2$, so $d_T \leq 2n$ and $n > 0$. Divide by $n$: $m\operatorname{rem} \leq 2(4L + 2I) = 8 f a\log^4 b + 40\log(1 + 2b^2) f a\log^3 b$. Since $\log(1 + 2b^2) \leq 3\log b$ and $\log b \geq 128$, this is at most $f a\log^5 b$. $\square$

The proof never estimates the main amount. It uses only its sign, and the main amount cancels as a symbol in Step 4: the exact cancellation that the toy model of Section 3 lacks. The errors $L$ and $I$ do not contain $m$. They are smaller than the main amount, which is at least $x^4 f a$, by a factor of more than $x^{3.9}$, but the proof does not need this. They must be small against $m\operatorname{rem}$ for the result to be useful (Section 6). The head of New/Reduction/MainInequality.lean lists the same errors per dimension.

**Remark (Formalization).** The last step of the source is one call of its automation for sizes, which compares $|2(4L + 2I)|$ with $f a\log^5 b$ by the exponents on the scales ([the data and its sizes](/chapter/data-and-sizes/)). The basis in Step 1 comes from Mathlib (`exists_fun_fin_finrank_span_eq`), so $n$ is the dimension of the span. The compact edition counts the missing $d_T - n$ dimensions as an error, from a crude bound for the main amount. The readable edition uses the sign of the main amount, and the missing dimensions cost nothing.
