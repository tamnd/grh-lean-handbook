---
title: Bad types are rare
lean:
  - New/Spanning/MainTerm/BadTypes.lean
  - Lib/Analytic/Primes.lean
  - Lib/LocalGL/Green/TauFunctions.lean
decls:
  - New.card_not_isAllowedPolynomial_le
  - New.totient_le_mul_card_isPrimitivePolynomial
  - New.le_totient_mul_log
  - New.one_sub_le_card_allowed_mul
  - New.card_not_primitive_mul_le
  - New.labelChar_degree_bounds
  - New.prod_le_re_tupleIdem_coeff_one
  - New.re_coeff_one_sub_sum_tupleIdem_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bad types are rare

The good forms are the image of $e_0$. The near isometry (NI) of [the plan](/chapter/theorem-b-plan/) needs that the projection $e_0$ removes little from the Poincaré series. In the regular representation of a finite group $G$ the share of a central idempotent $e$ is $\dim(e\,\mathbb{C}[G]) / |G|$, and this is the coefficient of $e$ at the identity. So the statement to prove is that $1 - e$ has a small coefficient at $1$, for $e$ the sum of the idempotents of the good tuples. This section proves this for one level prime. The proof is a count of polynomials over a finite field, Green's lower bound for the degrees, and a union bound.

Throughout, $k$ is a finite field with $q$ elements, $M \geq 1$ and $r$ are natural numbers, and polynomials are monic of degree $r$ in $k[X]$. There are $q^r$ of them.

### The count of polynomials

**Lemma (Polynomials that are not allowed).** At most $(1 + M + r)\,q^{r-1}$ monic polynomials of degree $r$ over $k$ are not allowed for $M$ and $r$.

Lean: `New.card_not_isAllowedPolynomial_le` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* Let $c$ be monic of degree $r$ and not allowed. Then $c$ has a root $a \in k$ with $a = 0$ or $a^M = 1$, or $c$ is not squarefree. Indeed, if $c$ is squarefree and has no such root, then $c(0) \neq 0$, so $c$ is a label, and it is allowed.

In the first case $c = (X - a)B$ with $B$ monic of degree $r - 1$. There are at most $1 + M$ values of $a$, since $X^M - 1$ has at most $M$ roots, and $q^{r-1}$ polynomials $B$. In the second case $c = P^2 B$ with $P$ monic irreducible and $B$ monic. Let $d = \deg B < r$. Then $\deg P = (r - d)/2$, and the pair $(P, B)$ is one of $q^{(r-d)/2} q^d$ pairs. Since $(r - d)/2 + d \leq r - 1$ for $d < r$, each value of $d$ gives at most $q^{r-1}$ polynomials, and there are $r$ values of $d$. The total is $(1 + M)q^{r-1} + r q^{r-1}$. $\square$

The bound is crude. For $r \geq 2$ the number of squarefree monic polynomials of degree $r$ is exactly $q^r - q^{r-1}$, a classical count. The crude bound is enough, as only the order $q^{r-1}$ matters.

**Lemma (Primitive polynomials).** Let $r \neq 0$. Then

$$\varphi(q^r - 1) \leq r \cdot \#\{c : c \text{ primitive of degree } r\}.$$

Lean: `New.totient_le_mul_card_isPrimitivePolynomial` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* The algebraic closure $\bar k$ contains a primitive root of unity $\zeta$ of order $q^r - 1$, so there are $\varphi(q^r - 1)$ elements of order exactly $q^r - 1$. Let $\xi$ be one of them and let $c$ be its minimal polynomial over $k$, of degree $d$. Then $\xi \neq 0$, so $c(0) \neq 0$, and $c$ is monic, irreducible and squarefree. The field $k(\xi)$ has $q^d$ elements, so $\xi^{q^d - 1} = 1$ and $q^r - 1$ divides $q^d - 1$. Also $\xi^{q^r} = \xi$, so $d$ divides $r$, and $q^d - 1$ divides $q^r - 1$. Hence $q^d = q^r$ and $d = r$. So $c$ is primitive of degree $r$. The map $\xi \mapsto c$ goes from the elements of order $q^r - 1$ to the primitive polynomials of degree $r$, and each fibre consists of roots of one polynomial of degree $r$, so it has at most $r$ elements. $\square$

The map is in fact $r$ to $1$, so equality holds. Lean proves only the inequality, which is what the bound needs.

**Lemma (The totient).** For every integer $n \geq 1$, $n \leq \varphi(n)\,(2 \log n + 1)$.

Lean: `New.le_totient_mul_log` (Lib/Analytic/Primes.lean).

This is an elementary bound of [primes in windows](/chapter/primes-in-windows/). If $n$ has $j$ distinct prime factors, then $2^j \leq n$, so $j \leq 2\log n$, and $\varphi(n)/n = \prod_{p \mid n}(1 - p^{-1}) \geq 1/(1 + j)$. Sharper bounds of order $n/\log\log n$ hold, but they are not needed.

### Weights

Give every polynomial of degree $r$ the weight

$$m = \frac{1 - r/q}{q^r}.$$

The weight of a set is $m$ times its size. The whole set has weight $1 - r/q$, a little less than $1$.

**Lemma (Allowed polynomials weigh much).** Let $1 < r < q$ and $(1 + M + 2r)/q \leq \varepsilon$. Then the allowed polynomials of degree $r$ weigh at least $1 - \varepsilon$.

Lean: `New.one_sub_le_card_allowed_mul` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* By the count, at least $q^r - (1 + M + r)q^{r-1}$ polynomials are allowed. Their weight is at least

$$\Big(1 - \frac{1 + M + r}{q}\Big)\Big(1 - \frac{r}{q}\Big) \geq 1 - \frac{1 + M + r}{q} - \frac{r}{q} = 1 - \frac{1 + M + 2r}{q} \geq 1 - \varepsilon,$$

since the product of the two subtracted terms is nonnegative. $\square$

**Lemma (Polynomials that are not primitive weigh little).** Let $1 < r < q$. The polynomials of degree $r$ that are not primitive weigh at most

$$\exp\Big(-\frac{1}{2r\,(2r \log q + 1)}\Big).$$

Lean: `New.card_not_primitive_mul_le` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* Let $P$ be the number of primitive polynomials of degree $r$, $N = q^r - 1$, and $A = 2r(2r\log q + 1)$. Then $q^r \leq 2N$, and by the two lemmas above and $\log N \leq r \log q$,

$$q^r \leq 2N \leq 2\varphi(N)(2\log N + 1) \leq 2rP\,(2r\log q + 1) = AP.$$

The weight $m$ is at most $q^{-r}$. So the polynomials that are not primitive weigh at most $(q^r - P)/q^r = 1 - P/q^r \leq 1 - 1/A \leq e^{-1/A}$. $\square$

The bound is weak for one field: it says only that a share $1/A$ of the polynomials is primitive. It becomes strong for many fields, as the next theorem takes its $f$-th power.

### The share of the good types

Green's theory gives the lower bound for the weights of the types. Let $\Xi_c$ be the character of a label $c$ of degree $r$, of degree $d = \Xi_c(1)$. [Green's characters](/chapter/finite-gln/#greens-characters-with-squarefree-labels) proves the following.

**Theorem (Degrees of Green's characters).** Let $c$ be a label of degree $r$ over $k$. Then $\operatorname{Re} d \geq 0$, and

$$\frac{1 - r/q}{q^r} \leq \frac{d\,\bar d}{|\mathrm{GL}_r(k)|}.$$

Lean: `New.labelChar_degree_bounds` (Lib/LocalGL/Green/TauFunctions.lean).

The inequality is in the partial order of $\mathbb{C}$, so the right side is real. The coefficient of $e_c$ at $1$ is $d\bar d/|\mathrm{GL}_r(k)|$, by the definition of $e_c$. So every type of a label weighs at least $m$ in the regular representation.

**Lemma (One good tuple).** Let $(k_w)_{w \in I}$ be a finite family of fields with $q$ elements, let $r < q$, and let $c = (c_w)$ be a tuple of labels of degree $r$. Then

$$\prod_{w \in I} m \leq \operatorname{Re}\big(e_c(1)\big),$$

where $e_c(1)$ is the coefficient of $e_c$ at the identity.

Lean: `New.prod_le_re_tupleIdem_coeff_one` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* The coefficient of a tensor product at the identity is the product of the coefficients of the factors at the identity. Each factor is a real number at least $m \geq 0$, by the theorem on degrees. $\square$

**Theorem (Bad types are rare).** Let $(k_w)_{w \in I}$ be $f$ fields with $q$ elements, let $1 < r < q$, and let $\varepsilon, L \in \mathbb{R}$ satisfy

$$\frac{1 + M + 2r}{q} \leq \varepsilon \leq 1, \qquad 2r\,(2r\log q + 1)\,L \leq f.$$

Let $e = \sum_c e_c$, the sum over the good tuples $c$ for $M$ and $r$. Then

$$\operatorname{Re}\big((1 - e)(1)\big) \leq f\varepsilon + e^{-L}.$$

Lean: `New.re_coeff_one_sub_sum_tupleIdem_le` (New/Spanning/MainTerm/BadTypes.lean).

*Proof.* Let $\mathcal{A}$ be the set of tuples of allowed polynomials and $\mathcal{N}$ the set of tuples in which no member is primitive. A tuple in $\mathcal{A}$ but not in $\mathcal{N}$ is good. So, with $u = 1/(2r(2r\log q + 1))$,

$$(1 - \varepsilon)^f \leq \prod_w \big(m\,\#\mathcal{A}_w\big) = m^f\,\#\mathcal{A} \leq m^f\,\#\{\text{good}\} + m^f\,\#\mathcal{N} \leq \sum_{c \text{ good}} \operatorname{Re} e_c(1) + e^{-fu}.$$

The first inequality is the lemma on allowed polynomials at each $w$. The middle one is $\#\mathcal{A} \leq \#\{\text{good}\} + \#\mathcal{N}$. The last uses the lemma on one good tuple for each good $c$, and the lemma on polynomials that are not primitive at each $w$, as $m^f\#\mathcal{N} = \prod_w m\,\#\mathcal{N}_w$. Bernoulli's inequality gives $1 - f\varepsilon \leq (1 - \varepsilon)^f$, since $-\varepsilon \geq -2$. So

$$\operatorname{Re}\big((1 - e)(1)\big) = 1 - \sum_{c \text{ good}} \operatorname{Re} e_c(1) \leq f\varepsilon + e^{-fu}.$$

Finally $L \leq fu$ by the hypothesis on $L$, so $e^{-fu} \leq e^{-L}$. $\square$

The two terms have different sources. The term $f\varepsilon$ comes from polynomials with a root in $k$ or a square factor, and grows with the number of factors. The term $e^{-L}$ comes from tuples with no primitive member, and decays with the number of factors. This is why each good tuple asks for only one primitive member and why the bound needs both $q$ and $f$ large.

**Remark (Formalization).** The finiteness of the sets of polynomials comes from the local instance `Fintype.ofFinite` of the file, at low priority, from `Finite k`. The sets are filters of `Polynomial.monicsOfDegree`. The statements use `Nat.card k = q` and do not fix a `Fintype` structure on $k$. So no two `Fintype` instances meet in a statement.

### The import of a later chapter

The file New/Spanning/MainTerm/BadTypes.lean imports New/Spanning/RemainingTerms/Size.lean, which this volume places in [the chapter on the remaining terms](/chapter/remaining-terms/), a later chapter. The section uses no result of that file: every proof above uses only the lemmas stated here and the totient bound of Lib/Analytic/Primes.lean, which the file also imports. So there is no result of the later chapter to state here, and the import does not change the order of the argument. It is an import of the file, not a step of the proof.

### At the level primes

[The proof of Theorem B](/chapter/proof-of-theorem-b/) applies the theorem at each level prime $p_i$, with $k_w$ the residue fields at the chosen places above $p_i$, so $q = p_i$. It takes $M = q_2$, $r = \#\mathtt{RowIndex}$, $\varepsilon = (1 + q_2 + 2r)/p_i$, $L = 9 \log b$, and $f$ the number of chosen places above $p_i$, which equals the number of infinite places of $E$. The size inequalities of [the data](/chapter/data-and-sizes/) give $1 < r < p_i$, $\varepsilon \leq 1$, $2r(2r\log p_i + 1) \cdot 9\log b \leq f$ and

$$f\varepsilon + b^{-9} \leq \frac{b^{-8}}{2}.$$

So the share of the bad types at each level prime is at most $b^{-8}/2$. That chapter also checks that the tensor product of the two idempotents at $p_0$ and at $p_1$ acts as $e_0$ on $\mathcal{A}_M(Y_0)$.

### An example

Let $r = 2$ and $M = 1$. A monic quadratic $X^2 + uX + v$ over $k$ is allowed when it is squarefree, $v \neq 0$ and $1$ is not a root. The polynomials that are not squarefree are the $q$ squares $(X - a)^2$. Those with $v = 0$ are $q$ more, and those with root $1$ are $q$ more. These sets overlap, so at most $3q$ are not allowed, within the bound $(1 + 1 + 2)q = 4q$. The primitive quadratics are the minimal polynomials of the $\varphi(q^2 - 1)$ generators of $\mathbb{F}_{q^2}^\times$, so there are $\varphi(q^2 - 1)/2$ of them. For $q = 5$ there are $\varphi(24)/2 = 4$ primitive quadratics among $25$, a share of $4/25$. The lemma asks only for the share $1/A = 1/(4(4\log 5 + 1)) \approx 0.033$. With $f$ such fields the share of the tuples without a primitive member is at most $(21/25)^f$, which decays exponentially in $f$.
