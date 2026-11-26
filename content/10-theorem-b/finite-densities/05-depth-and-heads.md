---
title: Depth and heads
lean:
  - New/Spanning/Frames/FiniteDepth.lean
  - New/Spanning/Frames/BesselVector.lean
decls:
  - New.Floors.IntegralPlace.exists_unit_leadingCoord_iff_mem_integers
  - New.Floors.IntegralPlace.inv_modulus_eq_sqrt_genIndex_sq
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_stableProducts_eq_unit_mul_integers
  - New.Floors.IntegralPlace.IsLargeLatticeData.stableProducts_subset
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_mem_stableProducts
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_mem_boxSet_hasMatrixSize_of_inner_ne_zero
  - New.Floors.IntegralPlace.IsLargeLatticeData.leadingMinor_mem_of_besselOrbitalIntegral_ne_zero
  - New.Floors.IntegralPlace.IsLargeLatticeData.prod_mem_of_formMajorant_ne_zero
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_multiple_of_prod_mem
  - New.Floors.IntegralPlace.IsLargeLatticeData.two_div_modulus_pow_le_mul_sqrt_genIndex_pow
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_of_formMajorant_ne_zero
  - New.Floors.IntegralPlace.IsLargeLatticeData.mem_positions_of_formMajorant_ne_zero
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_star_eq_common_multiple
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_volume_stableProducts_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Depth and heads

The bounds of [local frames](/chapter/local-frames/#gains-and-shells) take three inputs from a place: what the depth is, which heads can occur, and why a position far from $1$ has a deep vector. At the finite places all three are statements about fractional ideals $cR$. This section proves them for a large lattice datum $F$, with $R$ the ring of integers, $K$ the integral group and $g = $ `F.levelUnit`.

### The model case

Let $A = \mathbb{Q}_p$ (or an unramified quadratic extension), so every fractional ideal is $p^eR$ with $e \in \mathbb{Z}$. A bounded nonzero $R$-submodule of $A$ is such an ideal. The stable products $\mathfrak{d}_a(x, y)$ are of this form, and for $x$ near they lie in $R$, so $\mathfrak{d}_a = p^eR$ with $e \ge 0$. The depth is $\mathrm{vol}(p^eR)^{-1} = |p^e|^{-1} = [R : p^eR]$. A deep vector is one with $e$ large. The general case replaces "closed under addition" by a lattice argument, because $\mathfrak{d}_a$ is defined as a projection of a lattice.

### Leading coordinates of a lattice

**Lemma (Leading coordinates).** Let $X$ be a matrix over $A$ with a left inverse, let $\mathrm{wt}$ be a weight on its column indices, and let the index $i$ be the only index of weight $\mathrm{wt}(i)$. Consider the vectors $v$ with $Xv$ integral and $v_l = 0$ for every $l$ with $\mathrm{wt}(l) > \mathrm{wt}(i)$. There is a unit $c$ of $A$ such that their coordinates $v_i$ form the set $\{t : c^{-1}t \in R\} = cR$.

Lean: `New.Floors.IntegralPlace.exists_unit_leadingCoord_iff_mem_integers` (New/Spanning/Frames/BesselVector.lean).

*Proof.* The set $\Lambda = \{v : Xv \in R^n\}$ is a lattice. A lemma on primitive matrices over the valuation ring gives $b \in \mathrm{GL}(A)$, block triangular for $\mathrm{wt}$ (so $b_{li} = 0$ if $\mathrm{wt}(l) > \mathrm{wt}(i)$), and an integral $L$ with $Xb$ integral and $L(Xb) = 1$. Then $b^{-1} = LX$, so $v \in \Lambda$ if and only if $b^{-1}v$ is integral: one direction because $L$ is integral, the other because $Xb$ is integral. The inverse $b^{-1}$ is also block triangular. For $v$ that vanishes at the larger weights, the row $i$ of $b^{-1}$ sees only the entry $i$, since $i$ is alone in its weight: $(b^{-1}v)_i = (b^{-1})_{ii}v_i$. Let $c = b_{ii}$; the same computation for $b^{-1}b = 1$ gives $(b^{-1})_{ii}b_{ii} = 1$, so $c$ is a unit with $c^{-1} = (b^{-1})_{ii}$.

If $v$ is in $\Lambda$ and vanishes at the larger weights, then $c^{-1}v_i = (b^{-1}v)_i \in R$. Conversely, if $c^{-1}t \in R$, let $v = (c^{-1}t)\cdot b_{\cdot i}$, the column $i$ of $b$ times an integer. Then $Xv = (c^{-1}t)(Xb)_{\cdot i}$ is integral, $v$ vanishes at the larger weights, and $v_i = c^{-1}t\cdot c = t$. $\square$

### The stable products form an ideal

Recall from [local frames](/chapter/local-frames/#depth) the stable products $\mathfrak{d}_a(x, y)$: the coordinates at $e^*_a$ of the vectors $\omega$ with $\omega \perp e_b$ for $b < a$ and with $(x^{-1}\omega, (xy)^{-1}\omega')$ a close pair for some $\omega'$ that agrees with $\omega$ at the indices of level at least $a$. The depth is $\delta_a(x, y) = \mathrm{vol}(\mathfrak{d}_a(x, y))^{-1}$. For a lattice datum the close pairs are the congruent pairs: $(v, v')$ with $v$ integral and $g^{-1}(v - v')$ integral.

**Lemma (Stable products are cR).** For $a < \varrho$ and $x, y \in \mathsf{G}$ there is a unit $c$ with $\mathfrak{d}_a(x, y) = \{t : c^{-1}t \in R\}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_stableProducts_eq_unit_mul_integers` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Write the second vector as $\omega' = \omega + d$. Consider the block matrix

$$X = \begin{pmatrix} x^{-1} & 0\\ g^{-1}(x^{-1} - (xy)^{-1}) & -g^{-1}(xy)^{-1}\end{pmatrix},$$

acting on pairs $(\omega, d)$. Then $X(\omega, d)$ is integral if and only if $x^{-1}\omega$ is integral and $g^{-1}(x^{-1}\omega - (xy)^{-1}(\omega + d))$ is integral, that is, if and only if $(x^{-1}\omega, (xy)^{-1}(\omega + d))$ is a congruent pair. The matrix $X$ has the left inverse $\begin{pmatrix} x & 0\\ xy - x & -g\,xy\end{pmatrix}$.

Give the coordinates of $\omega$ their level, and give the coordinate $k$ of $d$ the weight $0$ if its level is less than $a$ and $2\varrho + 1$ otherwise. Then the coordinates of weight larger than that of $e^*_a$ are the coordinates of $\omega$ at the $e^*_b$, $b < a$, and the coordinates of $d$ of level at least $a$. Their vanishing says exactly that $\omega \perp e_b$ for $b < a$ and that $\omega + d$ agrees with $\omega$ at the levels at least $a$. The coordinate $e^*_a$ of $\omega$ is alone in its weight. So $\mathfrak{d}_a(x, y)$ is the set of leading coordinates of the lemma before, and that lemma gives $c$. $\square$

**Lemma (Stable products are integral).** If $x$ is near at $a + 1$, then $\mathfrak{d}_a(x, y) \subseteq R$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.stableProducts_subset` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Take $\xi \in R^{(a+1)}$ with $\xi x \in K$. For a stable $\omega$, $x^{-1}\omega$ is integral, so $\xi\omega = (\xi x)(x^{-1}\omega)$ is integral. Since $\xi$ is unitriangular on the first $a + 1$ frame vectors and $\omega \perp e_b$ for $b < a$, the coordinate of $\xi\omega$ at $e^*_a$ is that of $\omega$. $\square$

**Theorem (Depth at the finite places).** Let $a < \varrho$, let $x$ be near at $a + 1$, and let $y \in \mathsf{G}$. There is an ideal $I$ of $R$ such that an element $t \in R$ lies in $I$ if and only if $t \in \mathfrak{d}_a(x, y)$, and

$$\delta_a(x, y) = [R : I].$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* By the lemma on $cR$, $\mathfrak{d}_a(x, y) = \{t : c^{-1}t \in R\}$ for a unit $c$. The element $t = c$ lies in this set, so $c \in R$ by the lemma on integrality. Let $I = cR$, an ideal of $R$ (`New.Floors.IntegralPlace.exists_ideal_cardQuot_eq`). Its image in $A$ is $\{t : c^{-1}t \in R\} = \mathfrak{d}_a(x, y)$, which gives the first claim, and its index is $[R : cR] = |c|^{-1}$, which is finite and nonzero. The volume of $\{t : c^{-1}t \in R\}$ is $|c^{-1}|^{-1} = |c|$ (`New.Floors.IntegralPlace.volume_setOf_mul_mem`). So $\delta_a(x, y) = |c|^{-1} = [R : I]$. $\square$

**Remark (Formalization).** The index is `Ideal.cardQuot`, a natural number, and Mathlib sets it to $0$ for an ideal of infinite index. Here $c$ is a unit, so the index is finite and the junk value does not occur. The source writes the depth as an element of $[0, \infty]$ and the theorem compares it with the cast of `I.cardQuot`.

**Lemma (A unit in the stable products).** If $\langle W_Z(x), W_Z(z)\rangle \ne 0$ for an intermediate group $Z$, then for every $a < \varrho$ and $y$ there is a unit $c \in R$ with $c \in \mathfrak{d}_a(x, y)$ and $\mathrm{vol}(\mathfrak{d}_a(x, y)) \le |c|$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_mem_stableProducts` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* The lemma on two facts of [the finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector) gives $u \in \mathsf{U}$ with $ux \in K$. Since $\mathsf{U} \le R^{(a+1)}$, $x$ is near at $a + 1$. With $c$ from the lemma on $cR$, $c \in \mathfrak{d}_a$, $c \in R$ by the lemma on integrality, and $\mathrm{vol}(\mathfrak{d}_a) = |c|$. $\square$

**Lemma (Close points in the box).** Let $\Gamma$ be any gauge of $F$. If $\langle W_Z(x), W_Z(y)\rangle \ne 0$, there are $u, v \in \mathsf{U}$ with $ux \in K$, $vy \in K$, and $g^{-1}(vy - ux)$ of matrix size $2$ for $\Gamma$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_mem_boxSet_hasMatrixSize_of_inner_ne_zero` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* The lemma on two facts gives $u, v \in \mathsf{U}$ with $ux \in K$ and $(ux)^{-1}vy \in K(g)$. Then $vy = ux\cdot(ux)^{-1}vy \in K$. The matrix $g^{-1}(vy - ux) = ux\cdot g^{-1}((ux)^{-1}vy - 1)$ is a product of two integral matrices. An integral column $\omega$ has size $1$ in every gauge, because $(\omega, \omega)$ is a close pair, and a gauge gives the entries of a close pair size $1$. Size $1$ implies size $2$. $\square$

**Corollary (Leading minors).** If the orbital integral of $W_Z$ at $\gamma$ is not zero, every leading minor of the frame Gram matrix of $\gamma$ is integral.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.leadingMinor_mem_of_besselOrbitalIntegral_ne_zero` (New/Spanning/Frames/BesselVector.lean).

*Proof.* The finite Bessel vector is cut. For a cut function with a nonzero orbital integral at $\gamma$, the lemma `New.Floors.Gauge.leadingMinor_mem_ofSize_of_besselOrbitalIntegral_ne_zero` (New/Spanning/Frames/Densities.lean), which rests on the lemma on leading minors at near points of [local frames](/chapter/local-frames/#place-data-floors-and-gauges), gives the minors size $9n$ in every gauge. In the gauge of scale $1$ every size is $R$. $\square$

### Heads and their weights

A form of floor $j$ is attached to two sequences of units $p, q$, the heads. The majorant $\mathsf{F}^*_j$ of [local frames](/chapter/local-frames/#densities-as-integrals-over-two-frames) vanishes unless the heads are integral in the following sense.

**Theorem (Heads of a nonzero form are integral).** Let $Z$ be an intermediate group, $j \le \varrho$, and $p, q$ sequences of units. If $\mathsf{F}^*_j(x) \ne 0$ for the majorant of $W_Z$ at some $x$, then $p_0\cdots p_{l-1} \in R$ and $q_0\cdots q_{l-1} \in R$ for every $l \le j$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.prod_mem_of_formMajorant_ne_zero` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* The majorant is the integral of a product of two pivot norms, so for some $y$ both are nonzero. A nonzero pivot norm has a nonzero integrand: there are $\sigma, \tau$ in the floor group $G^{(j)}$ with $\langle W_Z(\sigma y), W_Z(\sigma yx)\rangle \ne 0$ and $\langle W_Z(\tau w_p^{-1}y), W_Z(\tau w_q^{-1}yx)\rangle \ne 0$, where the second uses that $\tau$ commutes with the Weyl elements of floor $j$. A cut function that does not vanish at $\rho z$ with $\rho \in G^{(j)}$ makes $z$ near at $j$. So $y$, $yx$, $w_p^{-1}y$ and $w_q^{-1}yx$ are near at $j$. The lemma on head products (`New.Floors.Size.head_products_mem_ofSize`, New/Spanning/Frames/TwoGauges.lean; see [local frames](/chapter/local-frames/#sizes-lengths-and-balanced-frames)) says: if $z$ and $w_r^{-1}z$ are near at $j$, the products $r_0\cdots r_{l-1}$, $l \le j$, are leading minors of the frame Gram matrix of $w_r$ and have size $9n$. In the gauge of scale $1$ this means integral. Apply it with $(r, z) = (p, y)$ and $(q, yx)$. $\square$

Recall the finite head weight of [the anatomy of a term](/chapter/anatomy-of-a-term/):

$$\mathrm{hw}_K(j, r) = \prod_{l < j}\begin{cases}\sqrt{\mathrm{gi}(r_0\cdots r_l)}^{\,K} & \text{if } r_0\cdots r_l \in R,\\ 0 & \text{otherwise,}\end{cases}$$

where $\mathrm{gi} = $ `New.genIndex` is the generalized index: for a unit $D$, the inverse of the factor by which $D$ scales Haar measure. So $\mathrm{gi}(D) = |D|^{-1}$, and $\mathrm{gi}(D) = [R : DR]$ for $D \in R$ (`New.finHeadWeight`). The lemma `New.Floors.IntegralPlace.inv_modulus_eq_sqrt_genIndex_sq` records $|u|^{-1} = \sqrt{\mathrm{gi}(u)}^{\,2}$.

**Lemma (A common multiple of a head).** Let $r$ be a sequence of units with $r_0\cdots r_{l-1} \in R$ for every $l \le j$, and let $K \in \mathbb{N}$. There is a unit $\beta \in R$ such that $\beta/(r_0\cdots r_{l-1}) \in R$ for $l \le j$, $\beta/r_i \in R$ for $i < j$, and $\mathrm{hw}_K(j, r) = \sqrt{\mathrm{gi}(\beta)}^{\,K}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_multiple_of_prod_mem` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Let $P_l = r_0\cdots r_{l-1}$ and $\beta = \prod_{l \le j}P_l$. It is in $R$ as a product of elements of $R$. For $l \le j$, $\beta/P_l$ is the product of the other factors, so it is in $R$. For $i < j$, $\beta/r_i = (\beta/P_{i+1})\cdot P_i \in R$. All $P_{l+1}$ with $l < j$ are in $R$, so every factor of the weight is $\sqrt{\mathrm{gi}(P_{l+1})}^{\,K}$. Since $\mathrm{gi}$ is multiplicative and $P_0 = 1$, the product is $\sqrt{\mathrm{gi}(\beta)}^{\,K}$ (by induction on $j$ in the source). $\square$

**Lemma (Loss against weights).** Let $g, \beta, \gamma \in R$ be units and $\alpha$ a unit with $|\alpha| = |g|\,(|\beta|\,|\gamma|)^2$. If $4E \le K$, then

$$\Bigl(\frac{2}{|\alpha|}\Bigr)^E \le \Bigl(\frac{2}{|g|}\Bigr)^K\sqrt{\mathrm{gi}(\beta)}^{\,K}\sqrt{\mathrm{gi}(\gamma)}^{\,K}.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.two_div_modulus_pow_le_mul_sqrt_genIndex_pow` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Put $b = \sqrt{\mathrm{gi}(\beta)}$, $c = \sqrt{\mathrm{gi}(\gamma)}$, so $|\beta|^{-1} = b^2$ and $|\gamma|^{-1} = c^2$. Then $2/|\alpha| = (2/|g|)(bc)^4$, and $(2/|\alpha|)^E = (2/|g|)^E(bc)^{4E}$. Each base is at least $1$: $|g| \le 1$ because $g \in R$, and $b, c \ge 1$ because $\mathrm{gi} \ge 1$ on $R$. Since $E \le 4E \le K$, raise each exponent to $K$. $\square$

**Theorem (A gauge adapted to two heads).** Let $Z$ be an intermediate group, $j \le \varrho$, $K \in \mathbb{N}$, and $p, q$ sequences of units with $\mathsf{F}^*_j(x) \ne 0$ for some $x$. There is a unit $\alpha \in R$ with $\bar\alpha = \alpha$ such that, for the gauge $\Gamma_\alpha$ of [the lattice datum](/chapter/finite-densities/#the-lattice-datum):

1. $p$ and $q$ are heads of length $j$;
2. if $j \ne 0$, $g^{-1}$ has size $1$;
3. $p_i^{-1} - q_i^{-1}$ has size $1$ for $i < j$;
4. if $4E \le K$, then $\Lambda_\alpha^E \le (2/|g|)^K\,\mathrm{hw}_K(j, p)\,\mathrm{hw}_K(j, q)$, where $\Lambda_\alpha = 2/|\alpha|$ is the loss.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_of_formMajorant_ne_zero` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* By the theorem on heads, all products of $p$ and of $q$ of length at most $j$ are in $R$. Take $\beta$ for $p$ and $\gamma$ for $q$ from the lemma on common multiples, and set

$$\alpha = g\,\overline{\beta\gamma}\,\beta\gamma.$$

It is in $R$, since the involution keeps $R$, and $\bar\alpha = \alpha$ since $\bar g = g$ and $A$ is commutative. In $\Gamma_\alpha$, size $1$ means $\alpha z \in R$. A unit $u$ with $\beta/u \in R$ has $\alpha u^{-1} = g\,\overline{\beta\gamma}\,\gamma\,(\beta/u) \in R$, and the same for $\gamma$. This gives (1) for $u = P_l$, (3) as the difference of $\alpha/p_i$ and $\alpha/q_i$, and (2) since $\alpha/g = \overline{\beta\gamma}\beta\gamma$. The involution keeps the modulus, so $|\alpha| = |g|(|\beta||\gamma|)^2$, and (4) is the lemma before with the weights of the common multiples. $\square$

The loss estimate (4) is where the head weights of [the anatomy of a term](/chapter/anatomy-of-a-term/) come from: a head with large products costs a large loss, and the weight $\mathrm{hw}$ pays for it.

**Theorem (Supports lie in the positions).** If $\mathsf{F}^*_j(x) \ne 0$ for the majorant of $W_Z$, for any $j$, $p$, $q$, then $x$ is a position of $F$: $x = s^{-1}ws\cdot k$ with $s \in \mathsf{G}$, $w \in \mathsf{U}$ and $k \in K(g)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.mem_positions_of_formMajorant_ne_zero` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* As in the theorem on heads, there are $y$ and $\sigma$ with $\langle W_Z(\sigma y), W_Z(\sigma yx)\rangle \ne 0$. The lemma on two facts gives $u, v \in \mathsf{U}$ with $k = (u\sigma y)^{-1}(v\sigma yx) \in K(g)$. Then, with $s = \sigma y$,

$$x = s^{-1}(v^{-1}u)s\cdot k,$$

as one checks by expanding. Since $v^{-1}u \in \mathsf{U}$, $x$ lies in the set of positions of the lattice datum. $\square$

### Far positions have a deep vector

A position $x$ is far from $1$ when the entries of $g^{-1}(x - 1)$ have a large common denominator. The next theorem says that then some vector $e_i$ is deep.

**Lemma (A self-adjoint common multiple).** Let $d_i \in R$, $i < \varrho$, be units, let $\sigma \le 1$, and let $\sigma^2 \le |d_i|$ for $j \le i$. There is a unit $C \in R$ with $\bar C = C$, $C/d_i \in R$ for $j \le i$, and $\sigma^{4n} \le |C|$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_star_eq_common_multiple` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Let $C = \prod_{j \le i < \varrho}d_i\bar d_i$. It is in $R$ and self-adjoint, and $C/d_i$ is the product of the other factors. Then $|C| = \prod|d_i|^2 \ge \sigma^{4N}$ with $N = \#\{i : j \le i < \varrho\} \le n$, and $\sigma^{4N} \ge \sigma^{4n}$ since $\sigma \le 1$. $\square$

**Theorem (Far means deep).** Let $Z$ be an intermediate group, $j \le \varrho$, $\alpha \in R$ a unit with $\bar\alpha = \alpha$, $\Gamma = \Gamma_\alpha$ with loss $\Lambda = 2/|\alpha|$, and $p, q$ heads of length $j$ for $\Gamma$; if $j \ne 0$ let $g^{-1}$ have size $1$. Let $c$ be a unit that divides every common denominator of $g^{-1}(x - 1)$ in $R$: if $\varepsilon \in R$ and $\varepsilon\,(g^{-1}(x - 1))_{ik} \in R$ for all $i, k$, then $c^{-1}\varepsilon \in R$. Let $\sigma < 1$ with

$$|c|\cdot\Lambda^{10n\cdot 99n} \le \sigma^{400n^2}.$$

If $\langle W_Z(y), W_Z(yx)\rangle \ne 0$ and $w_p^{-1}y$ and $w_q^{-1}yx$ are near at $j$, then there is $i$ with $j \le i < \varrho$ and $\mathrm{vol}(\mathfrak{d}_i(y, x)) \le \sigma^2$, that is $\delta_i(y, x) \ge \sigma^{-2}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_volume_stableProducts_le` (New/Spanning/Frames/FiniteDepth.lean).

*Proof.* Suppose not: $\mathrm{vol}(\mathfrak{d}_i(y, x)) > \sigma^2$ for all $i \ge j$.

Step 1: units. The lemma on a unit in the stable products gives $d_i \in R \cap \mathfrak{d}_i(y, x)$ with $\mathrm{vol}(\mathfrak{d}_i) \le |d_i|$, so $\sigma^2 \le |d_i|$ for $i \ge j$. The lemma before gives $C$ with $\sigma^{4n} \le |C|$.

Step 2: a second gauge. Let $\Gamma' = \Gamma_{\alpha^{10n}C}$. Numbers of size $10n$ for $\Gamma$ have size $1$ for $\Gamma'$, since $\alpha^{10n}b \in R$ gives $\alpha^{10n}Cb \in R$. Each $d_i^{-1}$, $i \ge j$, has size $1$ for $\Gamma'$, since $\alpha^{10n}C/d_i \in R$. So for every $i \ge j$ the set $\mathfrak{d}_i(y, x)$ contains a unit whose inverse has size $1$.

Step 3: the position is close. The lemma on close points in the box gives the hypothesis on $u, v$ of the lemma "bounded depths bound the position" of [local frames](/chapter/local-frames/#depth) (`New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts`). That lemma gives: $g^{-1}(x - 1)$ has size $99n$ for $\Gamma'$. So $\varepsilon = (\alpha^{10n}C)^{99n}$ is a common denominator, and $c^{-1}\varepsilon \in R$ by hypothesis.

Step 4: compare moduli. From $c^{-1}C^{99n}\cdot\alpha^{990n^2} \in R$ we get $|c^{-1}C^{99n}| \le |\alpha|^{-990n^2} \le \Lambda^{990n^2}$. Put $X = |C|^{99n}$, which is positive and finite. Then

$$X = |c|\cdot|c^{-1}C^{99n}| \le |c|\,\Lambda^{990n^2} \le \sigma^{400n^2} \le \sigma\cdot(\sigma^{4n})^{99n} \le \sigma X < X,$$

where the third inequality uses $1 + 396n^2 \le 400n^2$ and $\sigma \le 1$, and the last uses $\sigma < 1$. This is a contradiction. $\square$

The constants are generous: $4\cdot 99 < 400$ leaves one spare factor $\sigma$, and this factor gives the strict inequality. The theorem is used in [the next section](/chapter/finite-densities/#shells-decay-and-mass) with $c$ a generator of the denominator ideal of the position.
