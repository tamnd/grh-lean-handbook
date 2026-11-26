---
title: From progressions to places
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.Parameters.IsSparse
  - New.Parameters.exists_orderOf_placeClass_eq
  - New.Parameters.placeClass_sq_eq
  - New.modEq_orderOf_of_div_pow_eq
  - New.two_pow_le_of_pow_eq_one
  - New.Parameters.exists_large_isSparse
  - New.Parameters.exists_isSparse
  - New.mul_rank_lt_two_pow
  - New.Parameters.exists_isSparse_of_ranks
status: drafted
drafted_by: writer@claude-opus-5-5
---
## From progressions to places

This section turns the set of Section 3 into the set $\Phi_b$ of places. The plan is the one of Section 1. The places are $-g^e$ for one element $g$ of order $2^s$ and for exponents $e$ in a Behrend set. A forbidden configuration at an odd prime $\ell$ becomes a weighted congruence between exponents, which does not depend on $\ell$. The prime $\ell = 2$ is treated by a separate argument modulo a power of $3$. At the end the size of the set is compared with $\operatorname{towerDeg}(s)$ through an auxiliary scale $W$.

Throughout, $P$ is the parameters, $s$ the exponent, $q_1 = P.q_1(s)$, and $\Phi = P.\Phi(s) \cong (\mathbb{Z}/q_1\mathbb{Z})^\times$. For $q \mid q_1$, $\operatorname{cl}_q \colon \Phi \to (\mathbb{Z}/q\mathbb{Z})^\times$ is the class modulo $q$, written `P.placeClass` in Lean. For an integer $\nu$ prime to $q_1$, $[\nu] \in \Phi$ is the place with class $\nu$, written `P.placeOfInt s ν`.

### The definition of sparseness

**Definition (Sparse set of places).** A finite set $T \subseteq \Phi$ is *sparse for the primes up to $L$* if for every prime $\ell \leq L$ and all integers $0 < i < j < l_0(s)$ there are no $\sigma, \tau, \rho \in T$, distinct or not, and no units $\epsilon, \epsilon' \in \mathbb{Z}^\times = \{\pm 1\}$ with
$$\operatorname{cl}_{q_1^{(\ell)}}(\tau/\sigma) = \epsilon\, \ell^i \quad\text{and}\quad \operatorname{cl}_{q_1^{(\ell)}}(\rho/\sigma) = \epsilon'\, \ell^j,$$
where $q_1^{(\ell)} = q_1/\ell^{v_\ell(q_1)}$ is the part of $q_1$ prime to $\ell$.

Lean: `New.Parameters.IsSparse` (New/Reduction/Data/AdmissibleData.lean).

The data require `P.IsSparse s ((r + 1 - m) * (5 * r)) T` for the set $T = \Phi_b$, that is, sparseness for the primes up to $k t$ (field `sparse` of `New.Data`).

### The element of order $2^s$

**Lemma (An element of order $2^s$).** Let $g = 1 + 3 l_0 q_0$. There is $v \in \mathbb{N}$ with $2^{s+v} \mid q_1$ such that the class of the place $[g]$ modulo $2^{s + v}$ has order exactly $2^s$.

Lean: `New.Parameters.exists_orderOf_placeClass_eq` (New/Reduction/Data/Existence.lean).

*Proof.* Write $q_0 = 2^v u$ with $u$ odd. Since $4 \mid q_0$, we have $v \geq 2$. Then $g = 1 + 2^v a$ with $a = 3 l_0 u$, and $a$ is odd because $l_0$ is a power of $3$. The divisibility $2^{s+v} \mid q_0 \cdot 3 l_0 2^s = q_1$ is clear. The order of $1 + 2^v a$ modulo $2^{s+v}$, for $v \geq 2$ and $a$ odd, is $2^s$: this is `ZMod.orderOf_one_add_mul_prime_pow` (Mathlib) for the prime $2$. $\square$

The order statement is the classical description of $(\mathbb{Z}/2^K\mathbb{Z})^\times$. For $v \geq 2$ and $a$ odd, the binomial theorem gives $(1 + 2^v a)^{2} = 1 + 2^{v+1} a'$ with $a'$ odd. By induction $(1 + 2^v a)^{2^t} = 1 + 2^{v + t} a_t$ with $a_t$ odd. So the order modulo $2^{s+v}$ is $2^s$. The hypothesis $v \geq 2$ is needed: $3 = 1 + 2$ has order $2$ modulo $8$, not $4$.

In the data, $2^s \approx x^{11}$, so $[g]$ has an enormous order. It is the element $g$ of Section 1, and the group $\langle \operatorname{cl}_{2^{s+v}}([g]) \rangle$ is cyclic of order $2^s$.

### Three small lemmas

**Lemma (Squares remove the sign).** Let $\ell$ be a prime, $y \in \Phi$, and $\epsilon \in \{\pm 1\}$ with $\operatorname{cl}_{q_1^{(\ell)}}(y) = \epsilon\, \ell^i$. Let $q \mid q_1$ with $\gcd(\ell, q) = 1$. Then $\operatorname{cl}_q(y)^2 = \ell^{2i}$ in $\mathbb{Z}/q\mathbb{Z}$.

Lean: `New.Parameters.placeClass_sq_eq` (New/Reduction/Data/Existence.lean).

*Proof.* Since $q \mid q_1$ and $\ell \nmid q$, $q$ divides $q_1^{(\ell)}$. So $\operatorname{cl}_q(y)$ is the reduction of $\operatorname{cl}_{q_1^{(\ell)}}(y) = \epsilon \ell^i$, and its square is $\epsilon^2 \ell^{2i} = \ell^{2i}$. $\square$

**Lemma (Exponents modulo the order).** Let $G$ be a commutative group, $h \in G$, and $e_1, e_2, e_3, a, b \in \mathbb{N}$ with $(h^{e_2}/h^{e_1})^{a + b} = (h^{e_3}/h^{e_1})^{b}$. Then $(a + b) e_2 \equiv a e_1 + b e_3 \pmod{\operatorname{ord}(h)}$.

Lean: `New.modEq_orderOf_of_div_pow_eq` (New/Reduction/Data/Existence.lean).

*Proof.* Clear denominators: $h^{(a+b)e_2 + b e_1} = h^{b e_3 + (a + b) e_1}$. Two powers of $h$ agree if and only if the exponents agree modulo $\operatorname{ord}(h)$. Cancel $b e_1$ from both sides of the congruence. $\square$

**Lemma (Orders modulo powers of $2$).** Let $q \in \mathbb{Z}$ with $|q| > 1$, let $o > 0$ and $s \geq 0$, and let $q^o \equiv 1 \pmod{2^{s+1}}$. Then $2^s \leq (|q| + 1)\, o$.

Lean: `New.two_pow_le_of_pow_eq_one` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

*Proof.* The hypothesis makes $q$ odd. The source shows that $2^s$ divides $(q - 1) o$ or $(q + 1) o$. This follows from the lifting of exponents at $2$. If $q \equiv 1 \pmod 4$, then $v_2(q^o - 1) = v_2(q - 1) + v_2(o)$. If $q \equiv 3 \pmod 4$ and $o$ is even, then $v_2(q^o - 1) = v_2(q + 1) + v_2(o)$. If $q \equiv 3 \pmod 4$ and $o$ is odd, then $q^o \equiv 3 \pmod 4$, so $s = 0$. In each case $2^s$ divides $x o$ for some $x \in \{q - 1, q + 1\}$, and $x \neq 0$ because $|q| > 1$. So $2^s \leq |x|\, o \leq (|q| + 1)\, o$. $\square$

So a prime $\ell$ has order at least $2^s/(\ell + 1)$ modulo $2^{s+1}$. For $\ell \leq kt \approx x^{10}$ this is about $x$, and that is far above $2 l_0 \approx \log x$.

### The construction

**Theorem (A large sparse set of places).** Let $n, H, L \in \mathbb{N}$ with
$$(2 l_0 H)^n \leq 2^s \qquad\text{and}\qquad 2 l_0 (L + 1) < 2^s.$$
There is a finite set $T \subseteq \Phi$ such that every $\sigma \in T$ has class $-1$ modulo $q_0$, $H^n/(nH^2) \leq \# T$ in $\mathbb{R}$, and $T$ is sparse for the primes up to $L$.

Lean: `New.Parameters.exists_large_isSparse` (New/Reduction/Data/Existence.lean).

*Proof.* Let $g$, $v$ be as in the lemma on an element of order $2^s$, let $\psi = \operatorname{cl}_{2^{s+v}}$ and $h = \psi([g])$, of order $2^s$. Apply the theorem of Section 3 with the weights up to $2 l_0$, the side $H$ and the modulus $o = 2^s$. Its hypotheses are $0 < 2 l_0$ and $(2 l_0 H)^n \leq 2^s$. It gives a set $S$ of exponents $e < 2^s$ with at least $H^n/(nH^2)$ elements. Put $\pi(e) = [-1] \cdot [g]^e$ and $T = \pi(S)$.

*Injectivity and classes.* For $e, e' \in S$, $\pi(e) = \pi(e')$ gives $h^e = h^{e'}$, and so $e = e'$ since $e, e' < \operatorname{ord}(h)$. So $\# T = \# S$. For every divisor $q$ of $3 l_0 q_0$ we have $g \equiv 1 \pmod q$. So $\operatorname{cl}_q(\pi(e)) = -1$ for every $q$ that divides both $q_1$ and $3 l_0 q_0$. In particular every place of $T$ has class $-1$ modulo $q_0$.

*Sparseness.* Let $\ell \leq L$ be prime, $0 < i < j < l_0$, and suppose $\sigma = \pi(e_1)$, $\tau = \pi(e_2)$, $\rho = \pi(e_3)$ satisfy $\operatorname{cl}_{q_1^{(\ell)}}(\tau/\sigma) = \epsilon\ell^i$ and $\operatorname{cl}_{q_1^{(\ell)}}(\rho/\sigma) = \epsilon'\ell^j$.

*Case $\ell = 2$.* Let $c = \lfloor \log_3 s \rfloor + 5$, so that $3^c = 3 l_0$. Then $3^c$ divides $q_1$ and $3 l_0 q_0$, so $\operatorname{cl}_{3^c}(\tau/\sigma) = (-1)/(-1) = 1$. The lemma on squares with $q = 3^c$ gives $1 = 2^{2i} = 4^i$ in $\mathbb{Z}/3^c\mathbb{Z}$. But $4 = 1 + 3$ has order $3^{c-1} = l_0$ modulo $3^c$, by `ZMod.orderOf_one_add_prime` (Mathlib). So $l_0 \leq i$, against $i < l_0$.

*Case $\ell$ odd.* The modulus $2^{s+v}$ divides $q_1$ and is prime to $\ell$. The lemma on squares gives $\psi(\tau/\sigma)^2 = \ell^{2i}$ and $\psi(\rho/\sigma)^2 = \ell^{2j}$. Hence
$$\psi(\tau/\sigma)^{2j} = \ell^{2ij} = \psi(\rho/\sigma)^{2i}.$$
Write $j = a + i$ with $a > 0$. Since $\psi(\pi(e)/\pi(e_1)) = h^{e}/h^{e_1}$, the lemma on exponents gives
$$(2a + 2i)\, e_2 \equiv 2a\, e_1 + 2i\, e_3 \pmod{2^s}.$$
The weights $2a$ and $2i$ are positive with sum $2j < 2 l_0$. So the theorem of Section 3 gives $e_1 = e_2 = e_3$. Then $\tau = \sigma$, its class modulo $q_1^{(\ell)}$ is $1 = \epsilon \ell^i$, and the lemma on squares with $q = 2^{s+1}$ gives $\ell^{2i} \equiv 1 \pmod{2^{s+1}}$. Here $2^{s+1} \mid q_1$ because $q_0$ is even. The lemma on orders gives
$$2^s \leq (\ell + 1)\cdot 2i \leq (L + 1) \cdot 2 l_0 < 2^s,$$
a contradiction. $\square$

**Remark (Formalization).** The prime $\ell$ appears only at two points of the proof: in the reduction from $q_1^{(\ell)}$ to $2^{s+v}$, which needs $\ell$ odd, and in the final order bound. The congruence between exponents is the same for all odd $\ell$. This is why one set $S$ serves all the primes up to $kt$, a power of $x$ in number. The source reduces modulo $2^{s+v}$ and forgets the rest of $q_1^{(\ell)}$. That loses information but costs nothing, because the contradiction comes from the $2$-part alone.

**Remark (Formalization).** The prime $\ell = 2$ is special because $2$ is not a unit modulo a power of $2$, so the cyclic group generated by $h$ cannot see the class $\pm 2^i$. The source uses that the places of $T$ are all $\equiv -1$ modulo $3 l_0$, so all the ratios are $1$ there, and that $2^2 = 1 + 3$ has order $l_0$ modulo $3 l_0$. So this step uses the factor $3 l_0$ of $\operatorname{towerDeg}(s)$ and the fact that $l_0$ is a power of $3$.

**Remark (Formalization).** The conclusion of the theorem is stated with the exact constant $H^n/(nH^2)$ and no hypothesis $0 < n$. For $n = 0$ the count is $0$ by the convention $x/0 = 0$, and the theorem gives only a set with the right classes, possibly empty. The empty set is sparse.

### The count against $\operatorname{towerDeg}(s)$

**Theorem (Sparse places of the right size).** Let $n, L \in \mathbb{N}$ and $W \in \mathbb{R}$ with $0 < n$, $1 \leq W \leq 2^s \leq W^n$, $(2 l_0)^n \leq W$, $3 l_0 n 2^n \leq W^3$ and $2 l_0 (L + 1) < 2^s$. There is a finite set $T \subseteq \Phi$ of places of class $-1$ modulo $q_0$ with
$$\operatorname{towerDeg}(s) \leq \# T \cdot W^6$$
that is sparse for the primes up to $L$.

Lean: `New.Parameters.exists_isSparse` (New/Reduction/Data/Existence.lean).

*Proof.* Choose $k \in \mathbb{N}$ with $(2^n)^k \leq 2^s/W < (2^n)^{k+1}$. This is possible since $2^s/W \geq 1$ and $2^n > 1$. Put $H = 2^k$. Then $H^n W \leq 2^s < 2^n H^n W$. Since $H^n \leq 2^s \leq W^n$, also $H \leq W$. The room condition holds: $(2 l_0 H)^n = (2 l_0)^n H^n \leq W H^n \leq 2^s$. The theorem above gives $T$ with $H^n/(nH^2) \leq \# T$. Then
$$\operatorname{towerDeg}(s) = 3 l_0 2^s < 3 l_0 2^n H^n W = \frac{H^n}{n H^2}\cdot\bigl(3 l_0 n 2^n\bigr) \cdot W \cdot H^2 \leq \# T \cdot W^3 \cdot W \cdot W^2 = \# T \cdot W^6. \qquad \square$$

The exponent $6$ is the sum of three losses: $W^3$ for the factor $3 l_0 n 2^n$, $W$ for the gap between $H^n$ and $2^s$, and $W^2 \geq H^2$ for the pigeonhole step. In the data $\log b \in [W^6, W^6 + 1]$, so this count gives $\operatorname{towerDeg}(s) \leq \# \Phi_b \cdot \log b$, the property 2 of Section 1.

### The constants of the data

The hypothesis $2 l_0 (L + 1) < 2^s$ with $L = kt$ is a statement about the ranks.

**Lemma (The ranks leave room).** Let $y > 0$ with $10^6 y \leq e^y$, and let $m, r, s \in \mathbb{N}$ with $e^{y/2} \leq m$, $r \leq 3 e^{5y}$, $2^s = m^{22}$ and $l_0(s) \leq 2592\, y$. Then
$$2\, l_0(s)\, \bigl((r + 1 - m)(5 r) + 1\bigr) < 2^s.$$

Lean: `New.mul_rank_lt_two_pow` (New/Reduction/Data/Existence.lean).

*Proof.* Since $r + 1 - m \leq r$ (truncated subtraction, with $m \geq 1$), $(r + 1 - m)(5r) + 1 \leq 5 r^2 + 1 \leq 45 e^{10y} + 1 \leq 46 e^{10 y}$. So the left side is at most $2 \cdot 2592\, y \cdot 46\, e^{10 y} = 238464\, y\, e^{10y} < 10^6\, y\, e^{10 y} \leq e^{11 y} = (e^{y/2})^{22} \leq m^{22} = 2^s$. $\square$

**Theorem (Sparse places from the ranks).** Let $y \geq 2$, $n > 0$, $m, r, s \in \mathbb{N}$ and $W \in \mathbb{R}$ with $e^{y/2} \leq m$, $r \leq 3 e^{5y}$, $2^s = m^{22}$, $s \leq 32 y$, $W \leq e^{y/2}$, $2^s \leq W^n$, $10^6 y \leq W$, $(5184\, y)^n \leq W$ and $7776\, y\, n\, 2^n \leq W$. There is a finite set $T \subseteq \Phi$ of places of class $-1$ modulo $q_0$ with $\operatorname{towerDeg}(s) \leq \# T \cdot W^6$ that is sparse for the primes up to $(r + 1 - m)(5r)$.

Lean: `New.Parameters.exists_isSparse_of_ranks` (New/Reduction/Data/Existence.lean).

*Proof.* From $W \leq e^{y/2} \leq m \leq m^{22} = 2^s$ we get $1 < W \leq 2^s$ and $s \neq 0$. Then $l_0 \leq 81 s \leq 2592\, y$ by `New.l₀_le_mul`. So $(2 l_0)^n \leq (5184\, y)^n \leq W$ and $3 l_0 n 2^n \leq 7776\, y\, n\, 2^n \leq W \leq W^3$. The condition $10^6 y \leq W \leq e^{y/2}$ gives $10^6 y \leq e^y$, and the lemma on the ranks gives $2 l_0 (kt + 1) < 2^s$. Apply the previous theorem with $L = kt$. $\square$

In the data $y = \log x$ and $W = x^{\varepsilon/6}$. The structure `New.Parameters.IsLargeScale` holds the conditions $(5184 y)^n \leq W$ (field `pow_le`) and $7776\, y\, n\, 2^n \leq W$ (field `mul_two_pow_le`), and `New.Parameters.exists_eventually_isLargeScale` shows that they hold at every large $x$ for a fixed $n$ with $99 q_0 d < n \varepsilon/6$. Both are of the form "a polynomial in $\log x$ is at most $x^{\varepsilon/6}$", so they hold for large $x$ for each fixed $n$.

**Remark (Formalization).** The constants $2592 = 32 \cdot 81$, $5184 = 2 \cdot 2592$ and $7776 = 3 \cdot 2592$ come from $l_0 \leq 81 s$ and $s \leq 32 y$. They are not optimal, and nothing in the argument depends on their values. The constant $10^6$ in $10^6 y \leq e^y$ only has to exceed $2 \cdot 2592 \cdot 46 = 238464$.
