---
title: Frobenius cycles and the twisted action
lean:
  - New/UpperBound/ElementaryDivisors/TwistingData.lean
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
  - New/UpperBound/ElementaryDivisors/Edges.lean
  - New/UpperBound/ElementaryDivisors/Depth.lean
decls:
  - New.FrobeniusCycle
  - New.FrobeniusCycle.letterRep
  - New.FrobeniusCycle.depth
  - New.FrobeniusCycle.defectWeight
  - New.FrobeniusCycle.defectWeight_sub_mem_Icc
  - New.FrobeniusCycle.translatesIn
  - New.FrobeniusCycle.multinomialExponent
  - New.FrobeniusCycle.divisorConstant
  - New.FrobeniusCycle.IsLargeDegree
  - New.FrobeniusCycle.IsLargeDegree.mul_pow_le_degree
  - New.FrobeniusCycle.IsLargeDegree.twenty_seven_le_log_q
  - New.FrobeniusCycle.IsLargeDegree.mul_degree_add_lt_P_pow
  - New.FrobeniusCycle.IsLargeDegree.multinomialExponent_mul_le_degree
  - New.FrobeniusCycle.IsLargeDegree.mul_multinomialExponent_le_divisorConstant
  - New.FrobeniusCycle.IsLargeDegree.mul_defectThreshold_le_mul_degree
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Frobenius cycles and the twisted action

The Hecke operator of the next chapter acts on forms on a product of $N$ copies of a vector space, one copy for each embedding of a field into $O$. The embeddings are linked by Frobenius: modulo $p$, each is the $P$-th power of the one before. This section fixes that structure, the action of $\mathrm{GL}_k(W)$, and three numbers attached to a monomial: its depth, its defect and the threshold for the defect. It ends with the size conditions and the inequalities that follow from them.

### Frobenius cycles

**Definition (Frobenius cycle).** Let $W$ be a local ring, $R$ a commutative ring and $N$ a natural number. A Frobenius cycle with $N$ letters consists of a natural number $p$, an exponent $f$, ring maps $\iota_s : W \to R$ for $s \in \mathbb Z/N$, a parity $\mathrm{even}(s) \in \{\mathrm{true}, \mathrm{false}\}$ for each $s$, and an element $w \in R$, such that: $p$ is prime; $P = p^f \ge 5$; $w^2 = p$ in $R$; $p \mid \iota_{s+1}(x) - \iota_s(x)^P$ for all $s$ and $x \in W$; $\mathrm{even}(s+1) = \lnot\,\mathrm{even}(s)$; and the residue field $k_W$ of $W$ has $q = P^N$ elements.

Lean: `New.FrobeniusCycle` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

The parities alternate around $\mathbb Z/N$, so $N$ is even when $N > 0$; with $N \ne 0$ one gets $N \ge 2$ (`New.FrobeniusCycle.two_le_card_letters`). A model: $W = O_0$ is the ring of integers of an unramified extension of $\mathbb Q_p$ of degree $fN$, $\varphi$ is its automorphism that lifts $x \mapsto x^P$ on the residue field, and $\iota_s = \iota_0 \circ \varphi^s$ for an embedding $\iota_0$ into a ring $O$ that contains $\sqrt p$. Then $\varphi(x) \equiv x^P \pmod p$ gives the congruence.

### The twisted action

**Definition (Twisted action).** For $g \in \mathrm{GL}_k(W)$ and a letter $s$, the letter matrix is $g_s = \iota_s(g)$ if $s$ is even and $g_s = \iota_s((g^{-1})^{\mathsf T})$ if $s$ is odd. The group acts on polynomials in the variables $x_{bs}$ by $x_{bs} \mapsto \sum_c (g_s)_{cb}\,x_{cs}$. On coefficient vectors $F : \mathrm{Exp} \to R$ of forms of degree $n$ in each letter, the matrix of $g$ is the Kronecker product

$$\rho(g) = \bigotimes_{s \in \mathbb Z/N} \mathrm{Sym}^n(g_s).$$

Lean: `New.FrobeniusCycle.letterRep` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

The maps $g \mapsto g_s$ and $g \mapsto \rho(g)$ are monoid homomorphisms, because inverse transpose is a homomorphism. The source proves that $\rho(g)$ acting on coefficients agrees with the substitution on polynomials (`New.FrobeniusCycle.polyAction_polyOfCoeffs`). Matrices act on coefficient vectors, so they are the transposes of the substituted matrices.

### Depth and defect

Fix $r \le k$. In an even letter the variables $x_{bs}$ with $b \ge r$ are deep; in an odd letter those with $b < r$ are deep. The swap matches the inverse transpose in odd letters.

**Definition (Depth).** The depth of $\beta \in \mathrm{Exp}$ is the total degree of $x^\beta$ in the deep variables.

Lean: `New.FrobeniusCycle.depth` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

The depth lies in $[0, Nn]$. In the model case $k = 2$, $r = 1$, $N = 2$, the depth of $x_{00}^{i}x_{10}^{n-i}\,x_{01}^{j}x_{11}^{n-j}$ is $(n - i) + j$.

The defect refines the depth along one root. Fix indices $a \ne a'$ of $\{0, \dots, k-1\}$ and a letter $i$. In the letter $s$ put $u_s = (a', s)$ if $s$ is even and $u_s = (a, s)$ if $s$ is odd, and let $\bar u_s$ be the other of the two variables $(a, s)$, $(a', s)$. Write $\langle s - i \rangle \in \{0, \dots, N-1\}$ for the representative of $s - i$.

**Definition (Defect).** The defect weights at the letter $i$ along $(a, a')$ are, for a variable $x = (b, s)$,

$$\delta_i(x) = \frac{[x = u_s]\,P^{1 + \langle s - 1 - i\rangle} - [x = \bar u_s]\,P^{\langle s - i\rangle}}{q - 1}.$$

The defect of an exponent $\alpha$ at $i$ is $\sum_x \alpha(x)\,\delta_i(x)$.

Lean: `New.FrobeniusCycle.defectWeight` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

At $s = i$ the exponent $1 + \langle -1\rangle$ is $N$, so the weight of $u_i$ is $q/(q-1) = 1 + 1/(q-1)$. At $s \ne i$ it is $P\cdot P^{\langle s - 1 - i \rangle}/(q-1)$, which equals $P^{\langle s - i\rangle}/(q-1)$. So, away from the letter $i$, moving one unit of degree from $\bar u_s$ to $u_s$ raises the defect by $2P^{\langle s - i\rangle}/(q-1)$, and at $i$ by about $1$. The weights are small except near $i$: the defect is a weighted count, in which the letter $i$ counts fully and the letter $i + j$ counts with weight about $P^{j-N}$.

**Lemma.** For $a \ne a'$ and every letter $s$, $\delta_i(u_s) - \delta_i(\bar u_s) \in [0, 3/2]$.

Lean: `New.FrobeniusCycle.defectWeight_sub_mem_Icc` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

*Proof.* Since $u_s \ne \bar u_s$, the difference is $(P^{1+\langle s-1-i\rangle} + P^{\langle s-i\rangle})/(q-1)$, which is $\ge 0$. The first power is at most $P^N = q$ because $1 + \langle s - 1 - i\rangle \le N$. The second satisfies $5P^{\langle s - i\rangle} \le q$, because $\langle s-i\rangle \le N - 1$ and $P \ge 5$. So the numerator is at most $q + q/5$. As $q \ge 5$, one has $q + q/5 \le \frac32(q-1)$. $\square$

The source also proves $\sum_s P^{1 + \langle s-1-i\rangle} \le 2(q-1)$ and that the defect of an exponent of degree at most $d$ in each letter has absolute value at most $2d$ (`New.FrobeniusCycle.sum_P_pow_le`, `New.FrobeniusCycle.abs_weight_defectWeight_le`).

### Conditions on translates

For a labelling $\tau$ of the indices, $\mathrm{levi}(\tau)$ is the group of $g \in \mathrm{GL}_k(W)$ with $g_{ij} = 0$ whenever $\tau(i) \ne \tau(j)$, and $\mathrm{parahoric}(\tau)$ the group of $g$ with $g_{ij} \in \mathfrak m_W$ whenever $\tau(i) < \tau(j)$ ([finite general linear groups](/chapter/finite-gln/)). The two block labelling $\mathrm{twoBlock}(k, r)$ is $0$ on $b < r$ and $1$ on $b \ge r$.

**Definition (Translates in an ideal).** For a labelling $\tau$, an ideal $I$ of $R$ and a set $B$ of exponents, $\mathrm{translatesIn}(\tau, I, B)$ is the submodule of $F : \mathrm{Exp} \to R$ with $(\rho(g)F)_\beta \in I$ for all $g \in \mathrm{levi}(\tau)$ and all $\beta \in B$.

Lean: `New.FrobeniusCycle.translatesIn` (New/UpperBound/ElementaryDivisors/TwistingData.lean).

Two cases are used. The deep forms of depth $d$ are $\mathrm{deepForms}(k,n,r,d) = \mathrm{translatesIn}(0, 0, \{\mathrm{depth} < d\})$. The labelling $0$ makes the Levi group all of $\mathrm{GL}_k(W)$, so these are the $F$ all of whose translates have only monomials of depth at least $d$. The defect conditions are

$$\mathrm{defectConditions}(n, a, a', I, h) = \mathrm{translatesIn}\big(\mathrm{twoBlock}(k, a'), I, \{\beta : \exists i,\ h < \mathrm{defect}_i(\beta)\}\big):$$

block diagonal translates have coefficients in $I$ at all monomials of defect above $h$ at some letter (`New.FrobeniusCycle.deepForms`, `New.FrobeniusCycle.defectConditions`).

### The constants

**Definition (Constants).** The multinomial exponent is $c_0 = k^2 f N$. The precision is $c = 5Nc_0$, the defect threshold of a precision $c$ is $c^* = 3kc$, and

$$c_{\mathrm{div}} = Nn\Big(\frac{1}{P^{2r}} + \frac{r^2}{kP}\Big).$$

Lean: `New.FrobeniusCycle.multinomialExponent` (New/UpperBound/ElementaryDivisors/Edges.lean).

Lean: `New.FrobeniusCycle.divisorConstant` (New/UpperBound/ElementaryDivisors/Depth.lean).

The precision and threshold are `New.FrobeniusCycle.congruencePrecision` and `New.defectThreshold`. Since $\log p \ge \log 2 \ge 2/3$ and $\log q = fN\log p$, one gets $c_0 \le \frac32 k^2\log q$ and $c \le \frac{15}2 k^2 N\log q$ (`New.FrobeniusCycle.multinomialExponent_le_mul_log`, `New.FrobeniusCycle.congruencePrecision_le_mul_log`).

### The size conditions

**Definition (Large degree).** The size conditions for the rank $k$, the degree $n$, the block size $r$ and the proportion $\theta$ are: $0 < r$; $2r \le k$; $0 < \theta \le 1$; $n^4 \le q$; and

$$\Big(\frac{Nk\log q}{\theta}\Big)^5 P^{3r} \le n.$$

Lean: `New.FrobeniusCycle.IsLargeDegree` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

The two conditions pull in opposite directions: $n$ must be large against $P^{3r}$ and the logarithm of $q$, and small against $q^{1/4}$. Both can hold because $q = P^N$ and $\log q$ grows slowly. For instance $N = 2$, $k = 2$, $r = 1$, $\theta = 1$ need $(4\log q)^5P^3 \le n \le q^{1/4} = P^{1/2}$, which fails. The conditions need $P^{N/4} \ge (Nk\log q/\theta)^5P^{3r}$, so $N > 12r$, and then they hold for $n$ near $q^{1/4}$ once $P$ is large.

**Lemma (Sizes).** Assume the size conditions. Then:

1. $k \ge 2$, $Nk \ge 4$ and $(Nk)^5 \le n$; hence $1 < n < q$;
2. $\log q \ge 27$;
3. if $2\ell = N$ then $Nk(\ell + 2)n + n + k < P^\ell$;
4. $c_0P^{2r} \le n$, and $Nc_0 \le c_{\mathrm{div}}$;
5. $8Nk\,c^*P^{2r} \le \theta n$, where $c^* = 3kc$ and $c = 5Nc_0$.

Lean: `New.FrobeniusCycle.IsLargeDegree.mul_pow_le_degree` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

Lean: `New.FrobeniusCycle.IsLargeDegree.twenty_seven_le_log_q` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

Lean: `New.FrobeniusCycle.IsLargeDegree.mul_degree_add_lt_P_pow` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

Lean: `New.FrobeniusCycle.IsLargeDegree.multinomialExponent_mul_le_degree` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

Lean: `New.FrobeniusCycle.IsLargeDegree.mul_multinomialExponent_le_divisorConstant` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

Lean: `New.FrobeniusCycle.IsLargeDegree.mul_defectThreshold_le_mul_degree` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* (1) $k \ge 2r \ge 2$ and $N \ge 2$. Since $q \ge 5$, $\log q \ge 1$, and $\theta \le 1$, so $Nk \le Nk\log q/\theta$; with $P^{3r} \ge 1$ this gives $(Nk)^5 \le n$. Then $n \ge 4^5 > 1$ and $n < n^4 \le q$. (2) $2^{40} = (4^5)^4 \le ((Nk)^5)^4 \le n^4 \le q$, and $40\log 2 > 27$. (3) From $P^{2\ell} = q \ge n^4$ one gets $P^\ell \ge n^2$. Also $\ell + 2 \le Nk$ and $(Nk)^2 + 2 \le (Nk)^5 \le n$. Since $k < n$, one gets $Nk(\ell+2)n + n + k < (Nk)^2n + 2n \le n^2 \le P^\ell$. (4) Put $L = \log q$. Clearing the denominator, $(NkL)^5P^{3r} = \theta^5 (NkL/\theta)^5P^{3r} \le \theta^5 n \le \theta n$. Then $c_0P^{2r} \le \frac32 k^2LP^{2r} \le N^2L\,k^2L\,P^{2r} = (NkL)^2P^{2r} \le (NkL)^5P^{3r} \le \theta n \le n$, using $\frac32 \le N\cdot NL$. Dividing by $P^{2r}$ and multiplying by $N$ gives $Nc_0 \le Nn/P^{2r} \le c_{\mathrm{div}}$. (5) Put $u = NkL \ge 27Nk$. Then $c \le \frac{15}{2}ku$, so $8Nkc^*P^{2r} = 24Nk^2cP^{2r} \le 180Nk^3uP^{2r}$. One checks $180Nk^3 \le u^4$ from $u \ge 27Nk$ and $N, k \ge 2$. So the left side is at most $u^5P^{2r} \le u^5P^{3r} \le \theta n$. $\square$

Part 3 is the inequality $D + k < P^N$ of the averaging map (Section 6), with $D = Nn k(\ell+2)P^\ell$. Part 5 is what makes the defect count of Section 5 cost at most a factor $1 + \theta$.
