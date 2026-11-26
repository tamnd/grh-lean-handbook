---
title: A sparse set of places
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
decls:
  - New.Parameters.IsSparse
  - New.Parameters.exists_orderOf_placeClass_eq
  - New.modEq_orderOf_of_div_pow_eq
  - New.two_pow_le_of_pow_eq_one
  - New.Parameters.exists_large_isSparse
  - New.Parameters.exists_isSparse
  - New.mul_rank_lt_two_pow
  - New.Parameters.exists_isSparse_of_ranks
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A sparse set of places

This section builds the set $\Phi_b$ of places that get the weight $b$. It must be large, of size at least $\operatorname{towerDeg}(s)/\log b$, and sparse, in a sense defined below. The construction takes the places $-g^e$ for a fixed element $g$ of order $2^s$ and exponents $e$ in a set of Behrend type. Sparseness then reduces to the congruence of Section 2.

### The group of places

Fix parameters $P$ and an exponent $s$. The infinite places $\Phi$ of $E = K(\zeta_{q_1})$ form a group, and the source fixes an isomorphism $\Phi \cong (\mathbb{Z}/q_1\mathbb{Z})^\times$, through the action of $\operatorname{Gal}(E/K)$ on $\zeta_{q_1}$ (see [fields, places and twists](/chapter/fields-places-twists/)). For a divisor $q$ of $q_1$, reduction modulo $q$ gives a homomorphism $\Phi \to (\mathbb{Z}/q\mathbb{Z})^\times$, the *class modulo $q$*. For an integer $\nu$ prime to $q_1$, write $[\nu] \in \Phi$ for the place of the class of $\nu$. For a prime $\ell$, write $q_1^{(\ell)}$ for the part of $q_1$ prime to $\ell$, that is, $q_1$ divided by the largest power of $\ell$ that divides it.

**Definition (Sparse set of places).** Let $L \in \mathbb{N}$, and let $T \subseteq \Phi$ be finite. Then $T$ is *sparse for the primes up to $L$* if the following holds for every prime $\ell \leq L$ and all integers $i, j$ with $0 < i < j < l_0$. Let $\varphi \colon \Phi \to (\mathbb{Z}/q_1^{(\ell)}\mathbb{Z})^\times$ be the class modulo $q_1^{(\ell)}$. There are no $\sigma, \tau, \rho \in T$, distinct or not, and no signs $\epsilon, \epsilon' \in \{\pm 1\}$ with
$$\varphi(\tau/\sigma) = \epsilon\,\ell^i \quad\text{and}\quad \varphi(\rho/\sigma) = \epsilon'\,\ell^j.$$
Lean: `New.Parameters.IsSparse` (New/Reduction/Data/AdmissibleData.lean).

The data need $\Phi_b$ to be sparse for the primes up to $kt$, where $k = r + 1 - m$ and $t = 5r$. The data record this as one of their fields, and Volume 11 uses that field. The two signs are independent, and the case $\sigma = \tau$ is allowed. Since $i > 0$, the case $\sigma = \tau$ asks that $\pm \ell^i \not\equiv 1$, which is a statement about the order of $\ell$. The proof below meets this case at its end.

### An element of order $2^s$

Let $g = 1 + 3 l_0 q_0$. The place $[g]$ is the generator of the construction.

**Lemma (The order of $g$).** There is a $v \in \mathbb{N}$ with $2^{s + v} \mid q_1$ such that the class of $[g]$ modulo $2^{s + v}$ has order exactly $2^s$.
Lean: `New.Parameters.exists_orderOf_placeClass_eq` (New/Reduction/Data/Existence.lean).

*Proof.* Write $q_0 = 2^v u$ with $u$ odd. Since $16 \mid q_0$, $v \geq 4$; the proof uses only $v \geq 2$. Then $g = 1 + 2^v a$ with $a = 3 l_0 u$ odd, since $l_0$ is a power of $3$. The classical fact for the prime $2$ says that $1 + 2^v a$ with $a$ odd and $v \geq 2$ has order $2^s$ modulo $2^{s + v}$: by induction, $(1 + 2^v a)^{2^t} = 1 + 2^{v + t} a_t$ with $a_t$ odd. Finally $2^{s + v} = 2^v \cdot 2^s$ divides $q_0 \cdot 2^s$, which divides $q_1 = q_0 \cdot 3 l_0 2^s$. $\square$

The element $g$ is $\equiv 1$ modulo $3 l_0 q_0$, so every place $-g^e$ has class $-1$ modulo $3 l_0 q_0$, and in particular modulo $q_0$. This gives the condition on the classes of $\Phi_b$ at no cost.

### Two arithmetic facts

**Lemma (Exponents from a relation).** Let $G$ be a commutative group, $g \in G$, and $e_1, e_2, e_3, a, b \in \mathbb{N}$. If
$$\bigl(g^{e_2}/g^{e_1}\bigr)^{a + b} = \bigl(g^{e_3}/g^{e_1}\bigr)^b,$$
then $(a + b) e_2 \equiv a e_1 + b e_3$ modulo the order of $g$.
Lean: `New.modEq_orderOf_of_div_pow_eq` (New/Reduction/Data/Existence.lean).

*Proof.* Clear the denominators: $g^{(a + b)e_2 + b e_1} = g^{b e_3 + (a + b) e_1}$. So the two exponents are congruent modulo the order of $g$. Cancel $b e_1$ on both sides. $\square$

**Lemma (A lower bound for an order modulo $2^{s+1}$).** Let $q \in \mathbb{Z}$ with $|q| > 1$, and let $o, s \in \mathbb{N}$ with $o > 0$. If $q^o \equiv 1 \pmod{2^{s+1}}$, then $2^s \leq (|q| + 1)\, o$.
Lean: `New.two_pow_le_of_pow_eq_one` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

*Proof.* The congruence forces $q$ odd, so there is a sign $e \in \{\pm 1\}$ with $4 \mid q - e$. Also $q^{2o} \equiv 1 \pmod{2^{s+1}}$, and $e^{2o} = 1$. The lifting the exponent lemma at the prime $2$, for $4 \mid q - e$, gives
$$v_2\bigl(q^{2o} - e^{2o}\bigr) = v_2(q - e) + v_2(2o) = v_2(q - e) + v_2(o) + 1.$$
So $s + 1 \leq v_2((q - e) o) + 1$, that is, $2^s$ divides $(q - e) o$. Since $|q| > 1$, the integer $(q - e) o$ is not $0$, and its absolute value is at most $(|q| + 1) o$. $\square$

### Construction of the set

**Lemma (A large sparse set).** Let $n, H, L \in \mathbb{N}$ with
$$(2 l_0 H)^n \leq 2^s \qquad\text{and}\qquad 2 l_0 (L + 1) < 2^s.$$
There is a finite set $T \subseteq \Phi$ such that every $\sigma \in T$ has class $-1$ modulo $q_0$, $H^n/(nH^2) \leq \#T$ as real numbers, and $T$ is sparse for the primes up to $L$.
Lean: `New.Parameters.exists_large_isSparse` (New/Reduction/Data/Existence.lean).

*Proof.* Take $v$ from [the lemma on the order of $g$](/decl/New.Parameters.exists_orderOf_placeClass_eq/), and let $\psi$ be the class modulo $2^{s + v}$. Then $\psi([g])$ has order $2^s$. Apply [Behrend's theorem](/decl/New.exists_three_term_free/) with $o = 2^s$ and weight bound $2 l_0$. Its hypotheses hold: $2 l_0 > 0$, and $(2l_0 H)^n \leq 2^s$. It gives a set $S$ of exponents $e < 2^s$ with $\#S \geq H^n/(nH^2)$. Put
$$T = \{\, [-1]\,[g]^e : e \in S \,\}.$$
The map $e \mapsto [-1][g]^e$ is injective on $S$: if two values agree, then $\psi([g])^e = \psi([g])^{e'}$ with $e, e' < 2^s$, the order of $\psi([g])$, so $e = e'$. So $\#T = \#S$. Every element of $T$ has class $-1$ modulo $q_0$, since $g \equiv 1 \pmod{3 l_0 q_0}$.

Now let $\ell \leq L$ be prime, let $0 < i < j < l_0$, and suppose that $\sigma = [-g^{e_1}]$, $\tau = [-g^{e_2}]$ and $\rho = [-g^{e_3}]$ in $T$ satisfy $\varphi(\tau/\sigma) = \epsilon \ell^i$ and $\varphi(\rho/\sigma) = \epsilon' \ell^j$. Note that $\tau/\sigma = [g]^{e_2}/[g]^{e_1}$ and $\rho/\sigma = [g]^{e_3}/[g]^{e_1}$. For every divisor $q$ of $q_1$ that is prime to $\ell$, $q$ divides $q_1^{(\ell)}$, and squaring removes the sign. So
$$(\text{class of } \tau/\sigma \bmod q)^2 = \ell^{2i}, \qquad (\text{class of } \rho/\sigma \bmod q)^2 = \ell^{2j}. \tag{1}$$

*Case $\ell = 2$.* Let $c = \lfloor \log_3 s \rfloor + 5$, so that $3^c = 3 l_0$. Then $3^c$ divides $q_1$ and $3 l_0 q_0$, and is prime to $2$. Modulo $3^c$ every element of $T$ has class $-1$, so $\tau/\sigma$ has class $1$. By (1), $4^i \equiv 1 \pmod{3^c}$. But $4 = 1 + 3$ has order $3^{c - 1} = l_0$ modulo $3^c$, by the same classical fact for the prime $3$. Since $0 < i < l_0$, this is false.

*Case $\ell$ odd.* Then $2^{s + v}$ is prime to $\ell$. By (1) modulo $2^{s+v}$,
$$\psi(\tau/\sigma)^{2j} = \ell^{2ij} = \psi(\rho/\sigma)^{2i}.$$
Write $j = a + i$ with $a > 0$. With $h = \psi([g])$ this reads $(h^{e_2}/h^{e_1})^{2a + 2i} = (h^{e_3}/h^{e_1})^{2i}$. [The lemma on exponents](/decl/New.modEq_orderOf_of_div_pow_eq/) gives
$$(2a + 2i)\, e_2 \equiv 2a\, e_1 + 2i\, e_3 \pmod{2^s}.$$
The weights $2a$ and $2i$ are positive, and $2a + 2i = 2j < 2 l_0$. Property 3 of Behrend's set gives $e_1 = e_2 = e_3$. So $\tau = \sigma$, and $\varphi(\tau/\sigma) = 1$. Then (1) modulo $2^{s+1}$, which divides $q_1$, gives $\ell^{2i} \equiv 1 \pmod{2^{s+1}}$. [The lemma on orders modulo $2^{s+1}$](/decl/New.two_pow_le_of_pow_eq_one/) with $o = 2i$ gives
$$2^s \leq (\ell + 1) \cdot 2i \leq (L + 1) \cdot 2 l_0 < 2^s,$$
a contradiction. So $T$ is sparse for the primes up to $L$. $\square$

The proof shows the role of each hypothesis. The bound $(2l_0H)^n \leq 2^s$ is room for Behrend's set with weights up to $2 l_0$ in the cyclic group of order $2^s$. The bound $2l_0(L + 1) < 2^s$ excludes the degenerate configuration $\sigma = \tau = \rho$, in which the ratio $\ell^i$ would have to be $\pm 1$. The prime $2$ is handled by the factor $3 l_0$ of $q_1$, in which $g$ is invisible.

### The count

The lemma gives $H^n/(nH^2)$ places, while the group has order $\operatorname{towerDeg}(s) = 3 l_0 2^s$. The next step chooses $H$ so that the loss is a fixed power of a scale $W$.

**Lemma (A sparse set of density $W^{-6}$).** Let $n, L \in \mathbb{N}$ and $W \in \mathbb{R}$ with
$$0 < n, \quad 1 \leq W \leq 2^s \leq W^n, \quad (2 l_0)^n \leq W, \quad 3 l_0 n 2^n \leq W^3, \quad 2 l_0 (L + 1) < 2^s.$$
There is a finite set $T \subseteq \Phi$ of places of class $-1$ modulo $q_0$, sparse for the primes up to $L$, with $\operatorname{towerDeg}(s) \leq \#T \cdot W^6$.
Lean: `New.Parameters.exists_isSparse` (New/Reduction/Data/Existence.lean).

*Proof.* Since $1 \leq 2^s/W$, there is a $k \in \mathbb{N}$ with $(2^n)^k \leq 2^s/W < (2^n)^{k + 1}$. Put $H = 2^k$. Then
$$H^n W \leq 2^s < 2^n H^n W.$$
From $H^n \leq 2^s/W \leq W^{n - 1} \leq W^n$ we get $H \leq W$. The room condition holds: $(2 l_0 H)^n = (2l_0)^n H^n \leq W \cdot 2^s/W = 2^s$. [The lemma on a large sparse set](/decl/New.Parameters.exists_large_isSparse/) gives $T$ with $\#T \geq H^n/(nH^2)$. Then
$$\operatorname{towerDeg}(s) = 3 l_0 2^s < 3 l_0 2^n H^n W = \frac{H^n}{n H^2} \cdot \bigl(3 l_0 n 2^n\bigr) \cdot W \cdot H^2 \leq \#T \cdot W^3 \cdot W \cdot W^2 = \#T \cdot W^6. \qquad \square$$

**Example (The sizes in the application).** In the data, $2^s = m^{22}$ with $m \approx \sqrt{x}$, so $2^s \approx x^{11}$, and $W = x^{\varepsilon/6}$. So $H^n$ is about $x^{11 - \varepsilon/6}$, and $H$ is about $x^{11/n}$, where $n$ is the fixed exponent of [the large scales](/decl/New.Parameters.IsLargeScale/). The set $T$ has about $x^{11 - 22/n}$ elements in a group of order about $x^{11}\log x$. Its relative density $W^{-6} = x^{-\varepsilon}$ matches $1/\log b$, since $\log b \geq x^\varepsilon$.

### From the ranks to the set

The last lemma of this section puts in the ranks $m$ and $r$, the exponent $s$ and the bound $L = kt$.

**Lemma (The bound on the primes).** Let $y > 0$ and $m, r, s \in \mathbb{N}$ with $10^6 y \leq e^y$, $e^{y/2} \leq m$, $r \leq 3e^{5y}$, $2^s = m^{22}$ and $l_0 \leq 2592\,y$. Then
$$2 l_0 \bigl((r + 1 - m)(5r) + 1\bigr) < 2^s,$$
where $r + 1 - m$ is truncated subtraction in $\mathbb{N}$.
Lean: `New.mul_rank_lt_two_pow` (New/Reduction/Data/Existence.lean).

*Proof.* Since $m \geq 1$, $r + 1 - m \leq r$. So $(r + 1 - m)(5r) + 1 \leq 5r^2 + 1 \leq 45 e^{10y} + 1 \leq 46 e^{10 y}$. Then
$$2 l_0 \bigl((r + 1 - m)(5r) + 1\bigr) \leq 2 \cdot 2592\, y \cdot 46\, e^{10y} < 10^6\, y\, e^{10 y} \leq e^{11 y} = \bigl(e^{y/2}\bigr)^{22} \leq m^{22} = 2^s,$$
since $2 \cdot 2592 \cdot 46 = 238464 < 10^6$. $\square$

**Lemma (A sparse set from the ranks).** Let $y, W \in \mathbb{R}$ and $m, r, s, n \in \mathbb{N}$ with
$$2 \leq y, \quad 0 < n, \quad e^{y/2} \leq m, \quad r \leq 3 e^{5y}, \quad 2^s = m^{22}, \quad s \leq 32 y, \quad W \leq e^{y/2},$$
$$2^s \leq W^n, \quad 10^6 y \leq W, \quad (5184\, y)^n \leq W, \quad 7776\, y\, n\, 2^n \leq W.$$
There is a finite set $T \subseteq \Phi$ of places of class $-1$ modulo $q_0$ with $\operatorname{towerDeg}(s) \leq \#T \cdot W^6$, sparse for the primes up to $(r + 1 - m)(5r)$.
Lean: `New.Parameters.exists_isSparse_of_ranks` (New/Reduction/Data/Existence.lean).

*Proof.* First $W \leq e^{y/2} \leq m \leq m^{22} = 2^s$, so $s \neq 0$ (else $W \leq 1 < 10^6 y$). Then $l_0 \leq 81 s \leq 81 \cdot 32\, y = 2592\, y$, since $3^{\lfloor \log_3 s \rfloor} \leq s$ for $s \neq 0$. Also $10^6 y \leq W \leq e^{y/2} \leq e^y$. Now apply [the lemma on density $W^{-6}$](/decl/New.Parameters.exists_isSparse/) with $L = (r + 1 - m)(5r)$. Its hypotheses: $(2 l_0)^n \leq (5184\, y)^n \leq W$; $3 l_0 n 2^n \leq 7776\, y\, n\, 2^n \leq W \leq W^3$; and $2 l_0(L + 1) < 2^s$ by [the bound on the primes](/decl/New.mul_rank_lt_two_pow/). $\square$

**Remark (Formalization).** The set $T$ is an existential witness, built from Behrend's set, whose sphere is itself an existential witness. Nothing later depends on which set is chosen: the data only record the three properties. The bound $\operatorname{towerDeg}(s) \leq \#T \cdot W^6$ becomes the field $\operatorname{towerDeg}(s) \leq \#\Phi_b \log b$ of the data in Section 5, through $W^6 \leq \log b$. The main inequality needs this lower bound for $\#\Phi_b$: in [Data.primeRemainder_le](lean:New/Reduction/OneSidedBound.lean#L33) the source divides by $\#\Phi_b$, and the ratio $\#\Phi_a/\#\Phi_b \leq \log b$ turns $(\log b)^5$ into $(\log b)^6$. The numbers $2592 = 81 \cdot 32$, $5184 = 2 \cdot 2592$ and $7776 = 3 \cdot 2592$ come from $l_0 \leq 81 s$ and $s \leq 32 y$.
