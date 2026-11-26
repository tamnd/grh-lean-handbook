---
title: The gauge at the complex place
lean:
  - New/Spanning/Frames/RealPlaceGauge.lean
decls:
  - New.Floors.RealPlaceSizes.gauge
  - New.Floors.RealPlaceSizes.mem_gauge_ofSize_iff
  - New.Floors.RealPlaceSizes.four_le
  - New.Floors.RealPlaceSizes.smul_mem_closePairs
  - New.Floors.RealPlaceSizes.norm_le_of_mem_productDifferences
  - New.Floors.RealPlaceSizes.norm_sq_mulVec_of_fixed
  - New.Floors.RealPlaceSizes.card_freeIndex_complexData
  - New.Floors.RealPlaceSizes.card_freeIndex_complexData_le
  - New.Floors.RealPlaceSizes.exists_rank_le_and_fixed_of_mulVec_eq_zero
  - New.Floors.RealPlaceSizes.exists_orthonormal_mul_eq_zero_and_fixed
  - New.Floors.exists_unitary_mul_submatrix_eq_zero
  - New.Floors.measurePreserving_normSq_prod_compl
  - New.Floors.setLIntegral_inv_pow_sphereDensity_le
  - New.Floors.exists_orthonormal_ker_lintegral_le
  - New.Floors.RealPlaceSizes.closedBall_subset_image_commonVectors
  - New.Floors.inv_volume_le_of_closedBall_subset
  - New.Floors.volume_le_of_subset_closedBall
  - New.Floors.RealPlaceSizes.exists_isCommonBound
  - New.Floors.RealPlaceSizes.norm_leadingMinor_le_of_isNear
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The gauge at the complex place

The general machine of [the chapter on frames](/chapter/local-frames/) needs a gauge for the place datum: sizes of numbers for one scale, and one constant $\Lambda$ whose powers bound moduli and volumes. This section builds the gauge at $\mathbb C$ for a scale $L \geq \rho$. The only field that needs real work is the common bound. It asks for a function $\varphi$ on the free span $X'$ that controls the products of a vector $u$ with a set of short vectors, and whose power $\varphi^s$ has a small integral. The model integral of [the opening section](/chapter/real-densities/#the-chapter-and-its-place) is the core of the proof.

### The fields of a gauge

Recall the structure `Gauge` of [the chapter on frames](/chapter/local-frames/) (Lean: `New.Floors.Gauge`, New/Spanning/Frames/Correlations.lean). It extends a structure of sizes $A_{(j)}$, $j \in \mathbb N$. The sizes are closed under products ($A_{(i)} A_{(j)} \subseteq A_{(i+j)}$), a sum of at most $r + 1$ terms of size $i$ has size $i + 1$, the sets are closed under $-$ and $\star$, they contain $0$ and $1$, and the entries of the Gram matrix and of its inverse have size $1$. The gauge adds these conditions:

1. each $A_{(j)}$ is compact, and $2 \leq \Lambda < \infty$;
2. the number $m$ of further hyperbolic pairs is at most $9n$, and the constant `kernelBound` of the Plancherel formula is at least $1$;
3. the level $M$, the entries of the basis, the element of trace one divided by the skew unit, and the entries of the elements of the box have size $1$;
4. for a close pair $(\omega_1, \omega_2)$, the vectors $\omega_1$ and $M^{-1}(\omega_1 - \omega_2)$ have size $1$;
5. if $M^{-1}$ has size $1$, some unit $c$ with $c^{-1}$ of size $i + 2$ turns any two vectors of size $i$ into a close pair;
6. an invertible number of size $j$ has modulus at most $\Lambda^j$, and $A_{(j)}$ has volume at most $\Lambda^{j+1}$;
7. two blocks fit among the orthonormal basis vectors, and the volume of $A^p$ (with $p$ the block rank) disintegrates along the standard form into measures that give mass at most $\Lambda^{p(j+1)}$ to the vectors of size $j$;
8. the common bound: for $g$ in the box, a position $z$ and a matrix $v$ of $\varrho$ linear forms on $X'$, there is $\varphi$ with the properties of `IsCommonBound` for the set of common vectors.

The last field is stated in full below.

### The sizes at the complex place

**Definition (The gauge at $\mathbb C$).** Assume the sizes at a real place, and let $L \geq \rho$. A number $x \in \mathbb C$ has size $j$ if $|x| \leq L^j$. The constant of the gauge is $\Lambda = L^2$.

Lean: `New.Floors.RealPlaceSizes.gauge`, `New.Floors.RealPlaceSizes.mem_gauge_ofSize_iff` (New/Spanning/Frames/RealPlaceGauge.lean).

The source uses this gauge with $L = \rho$ for the leading minors and with larger $L$ in the shells of [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells). The checks use two facts on the sizes: $\rho \geq 8r$ and $\rho \geq 4$.

**Lemma.** Assume the sizes at a real place. Then $4 \leq \rho$.

Lean: `New.Floors.RealPlaceSizes.four_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* The rank $r$ is at least $1$, and $\rho \geq 8r$. $\square$

Most fields are short checks. A sum of at most $r + 1$ terms of modulus at most $L^i$ has modulus at most $(r+1) L^i \leq L^{i+1}$, since $r + 1 \leq 8r \leq L$. The constant $\Lambda = L^2 \geq 16$ is finite. The datum has $m = 0$. The constant `kernelBound` of the place $\mathbb C$ is $\pi^2 \geq 1$. The level is $1$. The entries of the basis have modulus at most $2$. The element of trace one is $\tfrac12$ and the skew unit is $\tfrac i2$, so their quotient has modulus $1$. An element of the box has operator norm at most $\rho \leq L$, so its entries have modulus at most $L$. The modulus at $\mathbb C$ is $|x|^2$, so $|x| \leq L^j$ gives modulus at most $\Lambda^j$. The disc of radius $L^j$ has area $\pi L^{2j} \leq \Lambda^{j+1}$, since $\pi \leq 4 \leq L$. The block rank is $2m + 2 = 2$, and $4 \leq k - 1$. The spheres of $\mathbb C^2$ carry the disintegration of the block, and the sphere through a vector of size $j$ has mass at most $4\pi^2 L^{2j} \leq \Lambda^{2(j+1)}$.

For a close pair, $|\omega_1|^2 + |\omega_2|^2 < 1$, so every entry of $\omega_1$ and $\omega_2$ has modulus at most $1$ and every entry of $\omega_1 - \omega_2$ has modulus at most $2$. The last close field takes $c = L^{-(i+2)}$.

**Lemma.** Assume the sizes at a real place and $\rho \leq L$. Let $\omega_1$, $\omega_2$ be vectors whose entries have modulus at most $L^i$. Then $(L^{-(i+2)} \omega_1, L^{-(i+2)} \omega_2)$ is a close pair.

Lean: `New.Floors.RealPlaceSizes.smul_mem_closePairs` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* A vector with entries of modulus at most $R$ has squared length at most $r R^2$ (Lean: `New.Floors.norm_toLp_sq_le`). So the sum of the squared lengths is at most $2 r L^{2i} / L^{2i+4} = 2r/L^4$. Since $8r \leq L$ and $L \geq 4$, this is less than $1$. $\square$

### The common vectors

Let $e$ be the matrix whose columns are the free orthonormal basis vectors (Lean: `orthonormalPart`), so that $e$ embeds the free span $X' = \mathbb C^{\mathrm{FreeIndex}}$ into the space. For $x, y \in G_1$ and a matrix $v$ of linear forms on $X'$, the common vectors are

$$W = \{w \in X' : v w = 0,\ |x^{-1} e w|^2 + |(xy)^{-1} e w|^2 < 1\}.$$

Lean: `New.Floors.PlaceData.commonVectors`, `New.Floors.PlaceData.IsShortFrom` (New/Spanning/Frames/Levels.lean).

In general $W$ is the set of $w$ with $vw = 0$ such that $(x^{-1} e w, (xy)^{-1} e w)$ is a close pair. The products of $u \in X'$ with $W$ are the numbers $\langle u, w \rangle = u^* w$.

The set `productDifferences` is the set of numbers $M^{-1}(\langle \omega_1, \omega'_1 \rangle - \langle \omega_2, \omega'_2 \rangle)$ for two close pairs $(\omega_1, \omega_2)$ and $(\omega'_1, \omega'_2)$, with $\langle u, v \rangle = u^* J_1 v$.

**Lemma.** At the place $\mathbb C$, every element of `productDifferences` has modulus at most $1$.

Lean: `New.Floors.RealPlaceSizes.norm_le_of_mem_productDifferences` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* The matrix $J_1$ is a permutation with signs, so $|u^* J_1 v| \leq |u||v| \leq (|u|^2 + |v|^2)/2$. Each of the two products is at most $(|\omega_1|^2 + |\omega'_1|^2)/2$ or the same with index $2$. The sum of the two bounds is less than $1$. $\square$

**Definition (Common bound).** Let $S$ be a system of sizes, $\Lambda \in [0, \infty]$, $W \subseteq X'$ and $\varphi : X' \to [0, \infty]$. Then $\varphi$ is a common bound for $W$ with constant $\Lambda$ if:

1. $\varphi$ is measurable;
2. for every $u$, $\operatorname{vol}(\langle u, W \rangle)^{-1} \leq \varphi(u)$;
3. for every $u$, the volume of the set of $c$ with $\langle c u, w \rangle \in$ `productDifferences` for all $w \in W$ is at most $\varphi(u)$;
4. for every $j$, $\int_{X'_{(j)}} \varphi^{s'}\, du \leq \Lambda^{99n(j+1)}$, where $X'_{(j)}$ is the set of vectors of size $j$ and $s'$ is the number `volumeExponent`.

Lean: `New.Floors.PlaceData.IsCommonBound` (New/Spanning/Frames/Levels.lean).

The number `volumeExponent` is $\operatorname{card}(\mathrm{FreeIndex}) - (3n + 1 + m)$. At $\mathbb C$ the free index set has $s + 1 + 3n$ elements and $m = 0$, so `volumeExponent` is $s$.

**Lemma.** Assume the sizes at a real place. At $\mathbb C$, $\operatorname{card}(\mathrm{FreeIndex}) = s + 1 + 3n$, and $\operatorname{card}(\mathrm{FreeIndex}) \leq \rho$.

Lean: `New.Floors.RealPlaceSizes.card_freeIndex_complexData`, `New.Floors.RealPlaceSizes.card_freeIndex_complexData_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* The index set has $k - 1 = s + 3n + 5$ elements, and two blocks of rank $2$ are set aside. For the bound, $\operatorname{card}(\mathrm{FreeIndex}) \leq k \leq r \leq 8r \leq \rho$. $\square$

### Linear conditions

The proof of the common bound reduces $W$ to a ball in a subspace. The subspace consists of the $w$ that satisfy at most $3n$ linear conditions.

**Lemma.** Let $e$ embed $X'$ as above, let $g \in G_1$, and suppose $J_1$ fixes $g e w$. Then $|g e w|^2 = |w|^2$.

Lean: `New.Floors.RealPlaceSizes.norm_sq_mulVec_of_fixed` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Since $J_1$ fixes $g e w$, $|g e w|^2 = (g e w)^* J_1 (g e w)$. This is $h(g e w, g e w) = h(e w, e w)$, since $g$ preserves $h$. The columns of $e$ are orthonormal for $h$, so $h(e w, e w) = |w|^2$. $\square$

The matrix $J_1$ swaps $e_a$ with $e^*_a$, fixes the $x_i$ and negates $z$. So $J_1$ fixes a vector exactly when its coordinates at $e_a$ and $e^*_a$ agree for every $a$ and its coordinate at $z$ is $0$. These are $\varrho + 1 = n$ conditions. Call $N$ the matrix of these $n$ linear forms.

**Lemma.** Assume the sizes at a real place. Let $x, y \in G_1$, and let $v$ have at most $n$ rows. There is a matrix $C$ on $X'$ of rank at most $3n$ such that every $w$ with $Cw = 0$ has $vw = 0$, $J_1 x^{-1} e w = x^{-1} e w$ and $J_1 (xy)^{-1} e w = (xy)^{-1} e w$.

Lean: `New.Floors.RealPlaceSizes.exists_rank_le_and_fixed_of_mulVec_eq_zero` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Stack the rows of $v$, of $N x^{-1} e$ and of $N (xy)^{-1} e$. There are at most $3n$ rows. $\square$

**Lemma.** Let $C$ be a matrix with columns indexed by $\iota$. If $\operatorname{rank} C + d \leq \operatorname{card} \iota$, then there are a unitary matrix $Q$ and a set $D$ of $d$ columns with $C\, Q_D = 0$, where $Q_D$ is the submatrix of the columns in $D$.

Lean: `New.Floors.exists_unitary_mul_submatrix_eq_zero` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Take an orthonormal basis of eigenvectors of the Hermitian matrix $C^* C$. Its rank is the rank of $C$, so at least $d$ eigenvalues are $0$. The eigenvectors of eigenvalue $0$ lie in the kernel of $C$. $\square$

**Theorem.** Assume the sizes at a real place. Let $x, y \in G_1$, let $v$ have at most $n$ rows, and let $d + 3n \leq \operatorname{card}(\mathrm{FreeIndex})$. There is a matrix $O$ with $d$ orthonormal columns ($O^* O = 1$) such that $vO = 0$ and $J_1 g e O = g e O$ for $g = x^{-1}$ and $g = (xy)^{-1}$.

Lean: `New.Floors.RealPlaceSizes.exists_orthonormal_mul_eq_zero_and_fixed` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Apply the last lemma to the matrix $C$ of the lemma before it. $\square$

### The integral of the common bound

The function $\varphi$ is $\varphi(u) = 36/|O^* u|^2$ for a matrix $O$ with $s + 1$ orthonormal columns. Its integral needs the law of $|O^* u|^2$.

**Lemma.** Let $Q$ be unitary and $D$ a nonempty set of indices. The map $u \mapsto (|(Q^* u)_D|^2, (Q^* u)_{D^c})$ carries Lebesgue measure to the product of Lebesgue measure on $\mathbb C^{D^c}$ and the measure on $r > 0$ with density

$$\frac{S_{\# D}(r)}{2} = \frac{\pi^{\# D}\, r^{\# D - 1}}{(\# D - 1)!}.$$

Lean: `New.Floors.measurePreserving_normSq_prod_compl` (New/Spanning/Frames/RealPlaceGauge.lean).

Here $S_i(r) = 2\pi^i r^{i-1}/(i-1)!$ is the sphere density of [Volume 5](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place). The map $Q^*$ preserves Lebesgue measure, and the squared length on $\mathbb C^D$ has the stated law.

**Lemma.** For every $s \in \mathbb N$ and $R \in \mathbb R$,

$$\int_{0 < r \leq R} \Bigl(\frac{36}{r}\Bigr)^s \frac{S_{s+1}(r)}{2}\, dr \leq 4 \cdot 3^{144} \cdot R^+.$$

Lean: `New.Floors.setLIntegral_inv_pow_sphereDensity_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* The integrand is $36^s \pi^{s+1}/s!$, a constant in $r$. The constant is bounded uniformly in $s$, since $(36\pi)^s/s! \leq e^{36\pi}$ and $\pi e^{36\pi} \leq 4 \cdot 3^{144}$. The bound follows on integration over $(0, R]$. $\square$

In Lean the integrand is $(\mathrm{ofReal}(r/36))^{-1}$ to the power $s$, and $R$ enters through $\mathrm{ofReal}$. So a negative $R$ gives the bound $0$, which is correct since the domain is then empty.

**Theorem.** Let $C$ be a matrix with column set $\iota$, with $\operatorname{card} \iota = s + 1 + 3n$, $\operatorname{rank} C \leq 3n$, $L \geq 4$ and $\operatorname{card} \iota \leq L$. There are a set $D$ and a matrix $O$ with columns in $D$ such that $CO = 0$, $O^* O = 1$, and for every $j$

$$\int_{\{u : |u_i| \leq L^j\ \forall i\}} \Bigl(\frac{36}{|O^* u|^2}\Bigr)^s du \leq (L^2)^{99n(j+1)}.$$

Lean: `New.Floors.exists_orthonormal_ker_lintegral_le` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Take $D$ with $s + 1$ elements and a unitary $Q$ with $C Q_D = 0$, and let $O = Q_D$. Pass to the coordinates $Q^* u$. An entry of $Q^* u$ has modulus at most $\operatorname{card}(\iota) L^j \leq L^{j+1}$ (Lean: `New.Floors.norm_unitary_conjTranspose_mulVec_le`). So the box lies in the product of $\{|O^* u|^2 \leq R\}$ with $R = L \cdot L^{2(j+1)}$ and the polydisc $B$ of radius $L^{j+1}$ in the other $3n$ coordinates. The polydisc has volume $(\pi L^{2(j+1)})^{3n}$ (Lean: `New.Floors.volume_closedBall_pi_complex`). The law of $|O^* u|^2$ and the last lemma bound the integral by $4 \cdot 3^{144} R\, (\pi L^{2(j+1)})^{3n}$. With $4 \cdot 3^{144} \leq L^{145}$ and $\pi \leq L$, a count of the powers of $L$ gives the bound. $\square$

**Remark (Formalization).** The function $\varphi(u) = 36/|O^*u|^2$ is in Lean $(\mathrm{ofReal}(|O^* u|^2/36))^{-1}$ in $[0, \infty]$. On the subspace $O^* u = 0$ it is $\infty$. This is not a junk value: the bounds 2 and 3 hold trivially there, and the subspace has measure $0$ because $O$ has $s + 1 \geq 1$ columns. The integral bound counts it correctly.

### The common bound

**Lemma.** Assume the sizes at a real place. Let $O$ have orthonormal columns with $vO = 0$, and let $J_1$ fix $g e O t$ for every $t$ and $g \in \{x^{-1}, (xy)^{-1}\}$. Let $u \in X'$ with $r = |O^* u|^2 \neq 0$. Then the closed disc of radius $\sqrt{|r|}/2$ lies in $\langle u, W \rangle$ for the common vectors $W$ of $x$, $y$, $v$.

Lean: `New.Floors.RealPlaceSizes.closedBall_subset_image_commonVectors` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Let $|t| \leq \sqrt{r}/2$ and $w = (t/r)\, O O^* u$. Then $\langle u, w \rangle = (t/r) |O^* u|^2 = t$ and $|w|^2 = |t|^2/r \leq 1/4$. Since $vO = 0$, $vw = 0$. By the lemma on fixed vectors, $|x^{-1} e w|^2 = |(xy)^{-1} e w|^2 = |w|^2$. The sum is at most $1/2 < 1$. $\square$

**Lemma.** Let $t > 0$ and $W \subseteq \mathbb C$.

1. If $W$ contains the closed disc of radius $\sqrt t/2$, then $\operatorname{vol}(W)^{-1} \leq 36/t$.
2. If $W$ lies in the closed disc of radius $2/\sqrt t$, then $\operatorname{vol}(W) \leq 36/t$.

Lean: `New.Floors.inv_volume_le_of_closedBall_subset`, `New.Floors.volume_le_of_subset_closedBall` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* The discs have areas $\pi t/4 \geq t/36$ and $4\pi/t \leq 36/t$. $\square$

**Theorem (Common bound at $\mathbb C$).** Assume the sizes at a real place and $\rho \leq L$. Let $S$ be a system of sizes in which size $j$ means $|c| \leq L^j$. For all $x, y \in G_1$ and every matrix $v$ of $\varrho$ linear forms on $X'$, some $\varphi$ is a common bound for the common vectors of $x$, $y$, $v$, with constant $L^2$.

Lean: `New.Floors.RealPlaceSizes.exists_isCommonBound` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Take $C$ of rank at most $3n$ as in the lemma on linear conditions, and $O$ as in the integral theorem. The hypotheses hold by the lemma on the free index set and $\rho \leq L$. Let $\varphi(u) = 36/|O^* u|^2$. Condition 4 is the integral theorem, since `volumeExponent` is $s$. For conditions 2 and 3, let $q = |O^* u|^2$. If $q = 0$, then $\varphi(u) = \infty$. If $q > 0$, the disc lemma and the area lemma give condition 2. For condition 3, pick $w \in W$ with $\langle u, w \rangle = \sqrt q/2$. If $c$ is in the set, then $\bar c \sqrt q/2 \in$ `productDifferences`, so $|c| \sqrt q/2 \leq 1$. The set lies in the disc of radius $2/\sqrt q$. $\square$

This proves the last field of the gauge. The gauge applies it with $g$ in the box and $z$ a position, and takes $x = g$ and $y = z$.

### Leading minors

The general file proves that the leading minors of the frame Gram matrix of $\gamma$ have size $9n$ when $y$ and $\gamma^{-1} y$ are near (Lean: `New.Floors.Gauge.leadingMinor_mem_ofSize_of_isNear`, New/Spanning/Frames/Correlations.lean). The point $y$ is near at $l$ if some element $\xi$ of the partly unitriangular group of level $l$ moves it into the box.

**Theorem.** Assume the sizes at a real place. Let $y$ and $\gamma^{-1} y$ be near at $l$. For $j \leq l$, the leading minor of order $j$ of the matrix $(h(f_a, \gamma f_b))_{a,b}$ of the $n$ frame vectors $f = (e_0, \dots, e_{\varrho-1}, z)$ has modulus at most $\rho^{9n}$.

Lean: `New.Floors.RealPlaceSizes.norm_leadingMinor_le_of_isNear` (New/Spanning/Frames/RealPlaceGauge.lean).

*Proof.* Apply the general theorem to the gauge with $L = \rho$. $\square$

This bound is used in [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells). If one of the first $j$ products $p_0 \cdots p_{j-1}$ has modulus above $\rho^{9n}$, the density of the floor form vanishes.

**Example.** This example lies outside the sizes, which ask for $\varrho \geq 10^8$. It shows only the count of conditions. Take $n = 1$, so $\varrho = 0$ and there is only the frame vector $z$. The matrix $v$ has no rows, and $N$ has the single row of the coordinate at $z$. The matrix $C$ has the two rows $N x^{-1} e$ and $N (xy)^{-1} e$, so its rank is at most $2 \leq 3n$. The vectors $w$ with $Cw = 0$ are carried by $x^{-1} e$ and $(xy)^{-1} e$ into vectors with coordinate $0$ at $z$. On these vectors $h$ is the Euclidean form, so the condition $|x^{-1} e w|^2 + |(xy)^{-1} e w|^2 < 1$ becomes $|w|^2 < 1/2$ on the kernel. The set $\langle u, W \rangle$ is then the open disc of radius $|O^* u|/\sqrt 2$ when $O$ spans that kernel, which contains the disc of the lemma.
