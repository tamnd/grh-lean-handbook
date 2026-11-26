---
title: The lattice datum
lean:
  - New/Spanning/Frames/StandardLevel.lean
decls:
  - New.Floors.vectorOfLastEntry
  - New.Floors.form_vectorOfLastEntry
  - New.Floors.PlaceData.congruenceSubgroup
  - New.Floors.IntegralPlace.congruentPairs
  - New.Floors.IntegralPlace.isOpen_congruentPairs_and_isCompact_closure
  - New.Floors.IntegralPlace.IsLatticeData
  - New.Floors.IntegralPlace.exists_right_invariant_measure_besselH
  - New.Floors.IntegralPlace.exists_isIntMatrix_hyperbolicBasis
  - New.Floors.IntegralPlace.exists_measure_floorGroup_top
  - New.Floors.IntegralPlace.topEichler_mem_unitaryLevel_one
  - New.Floors.IntegralPlace.exists_isLatticeData
  - New.Floors.IntegralPlace.IsLargeLatticeData
  - New.Floors.IntegralPlace.IsLargeLatticeData.idealZeta_le_two
  - New.Floors.IntegralPlace.IsLargeLatticeData.inv_modulus_pow_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.idealZeta_mul_inv_modulus_pow_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_kernel_isDisintegration_coordinateBox_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_isCommonBound
  - New.Floors.IntegralPlace.IsLargeLatticeData.gauge
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The lattice datum

The abstract chapter asks a place for place data: a box, close pairs, positions, a level unit and two measures. At a finite place all of them come from one integral lattice. This section defines them, proves that they exist, and builds the gauges.

### The finite place

A finite place in the source is a class `New.Floors.IntegralPlace` on a semilocal field $A$ with involution. It has a ring of integers $R$ (`integers`), a modulus $|\cdot|$ on the units and an additive character $\psi$ ([Siegel-Weil](/chapter/siegel-weil/)). The ring $A$ may be a finite product of local fields, so a finite set of finite places is read as one ring. All statements of this chapter hold for such a product. For a unit $u$, $|u|$ is the factor by which $x \mapsto ux$ scales volume. The volume of $R$ is $1$.

The space has the basis $e_a$, the basis of the middle space and $e^*_a$, as in [local frames](/chapter/local-frames/). The middle space is $X_0 \oplus Az$, where $X_0 = A^\kappa$ has an orthonormal basis $x_i$ and $z$ is orthogonal to $X_0$ with $\langle z, z\rangle = -N$, $N = \pi\bar\pi$. Its Gram matrix in the *lattice basis* $x_i$ ($i \neq k_0$), $v = x_{k_0}/\bar\pi + z/N$, $z$ is `New.latticeMiddleGram` ([the anatomy of a term](/chapter/anatomy-of-a-term/)). The Gram matrix of the whole space is $J$ (`T.splitGram`).

### The vector of a last entry

The top floor is studied through the *last entry* $\langle z, e\rangle$ of a vector $e$ of the middle space.

**Definition (Vector of a last entry).** For a unit $\pi$, $t \in A$ and $x \in X_0$, the vector $x - (\pi\bar\pi)^{-1}t\,z$, written in the lattice basis of the whole space, is `vectorOfLastEntry π t x`.

Lean: `New.Floors.vectorOfLastEntry` (New/Spanning/Frames/StandardLevel.lean).

**Lemma (Norm and last entry).** Let $\pi\bar\pi = N$ and $e = $ `vectorOfLastEntry π t x`. Then

$$e^*Je = x^*x - (\pi\bar\pi)^{-1}t\bar t,\qquad (Je)_z = t.$$

Lean: `New.Floors.form_vectorOfLastEntry` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* In the standard basis the vector is $e = x - N^{-1}tz$. Since $z \perp X_0$ and $\langle z, z\rangle = -N$, its norm is $x^*x + N^{-1}\bar N^{-1}t\bar t\,\langle z, z\rangle = x^*x - N^{-1}t\bar t$, where $\bar N = N$. The coordinate $(Je)_z$ is the pairing $\langle z, e\rangle$, and $\langle z, x - N^{-1}tz\rangle = -N^{-1}t\,\langle z, z\rangle = t$. The source does the same computation with the matrix of the lattice basis. $\square$

### Congruence subgroups and close pairs

**Definition (Congruence subgroup).** For place data $F$ with level unit $g$, $K(g) = $ `unitaryLevel R g J` is the group of integral isometries congruent to $1$ modulo $g$. It is `F.congruenceSubgroup`, and $K = K(1)$ is the group of all integral isometries.

Lean: `New.Floors.PlaceData.congruenceSubgroup` (New/Spanning/Frames/StandardLevel.lean).

**Definition (Congruent pairs).** For a unit $g$, the *congruent pairs* are the pairs $(\omega_1, \omega_2)$ of vectors with $\omega_1$ integral and $g^{-1}(\omega_1 - \omega_2)$ integral.

Lean: `New.Floors.IntegralPlace.congruentPairs` (New/Spanning/Frames/StandardLevel.lean).

**Lemma (Congruent pairs are a compact neighbourhood).** The set of congruent pairs is open, contains $0$, and has compact closure.

Lean: `New.Floors.IntegralPlace.isOpen_congruentPairs_and_isCompact_closure` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The integral vectors form an open compact set, and the set is the intersection of two preimages of it under continuous maps. It lies in the image of the compact set of pairs of integral vectors under $(\omega, \delta) \mapsto (\omega, \omega - g\delta)$, so its closure is compact. $\square$

### The lattice datum

**Definition (Lattice datum).** Place data $F$ are a *lattice datum* (`P.IsLatticeData F`) if:

1. the Gram matrix $J$ is unimodular over $R$, the basis matrix is integral, and the level unit $g$ is integral with $\bar g = g$;
2. the box is $K$; the top floor measure gives $K$ mass at least $\mathrm{vol}(R^\times)$; the measure on $H$ gives $K$ mass $1$; the close pairs are the congruent pairs of level $g$; and the positions are the products $y^{-1}uy\,k$ with $y \in \mathsf{G}$, $u \in \mathsf{U}$ and $k \in K(g)$;
3. some vector $u$ has $u^*J = $ the dual of $z$ and $u_z = 0$, so $u$ is isotropic with $\langle u, z\rangle = 1$.

Lean: `New.Floors.IntegralPlace.IsLatticeData` (New/Spanning/Frames/StandardLevel.lean).

The construction of a lattice datum needs three pieces: a measure on $H$, an integral hyperbolic basis, and a measure on the top floor group.

**Lemma (The measure on H).** There is an s-finite measure $\eta$ on $\mathsf{G}$ that is carried by $H$, gives $K$ mass $1$, is invariant under right translation by $H$, and gives the set $\{h : uhy \in K \text{ for some } u \in \mathsf{U}\}$ mass at most $1$ for every $y$.

Lean: `New.Floors.IntegralPlace.exists_right_invariant_measure_besselH` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* $H$ is closed, so it is locally compact. Let $\nu$ be the right Haar measure on $H$ with $\nu(H \cap K) = 1$: the inverse of the left Haar measure normalized on the open compact set $(H \cap K)^{-1}$. Let $\eta$ be its image in $\mathsf{G}$. Then $\eta(K) = 1$, and right invariance comes from that of $\nu$. For the last claim, if $h$ and $h'$ both lie in the set, then $h'h^{-1}$ lies in $H \cap K$, by `New.div_mem_unitaryLevel_of_besselU_mul` ([floors and the Bessel subgroup](/chapter/bessel-bruhat/)). So the set lies in one right coset of $H \cap K$, of mass $1$. $\square$

**Lemma (An integral hyperbolic basis).** Let $N \in R$ with $\bar N = N$ and $k = \#\iota + 2m + 1$. Then the middle block has an integral hyperbolic basis $B$, with $m$ pairs after the first and an orthonormal part indexed by $\iota$, in which the coordinate at $z$ of a vector is its coefficient at the second vector of the first pair.

Lean: `New.Floors.IntegralPlace.exists_isIntMatrix_hyperbolicBasis` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The plane of $x_{k_0}$ and $z$ becomes hyperbolic in the lattice basis. Take $c \in R$ with $\bar cc = -1$, which the finite place provides. For two orthonormal vectors $x$ and $y$, the vector $x + cy$ is isotropic, since its norm is $1 + \bar cc = 0$. With such combinations the basis change turns $2m$ of the remaining orthonormal vectors into $m$ hyperbolic pairs, and it keeps the other $\#\iota$ vectors. Its entries are in $R$, and the modulus of the determinant of the Gram matrix is $1$, as the definition of a hyperbolic basis requires. $\square$

**Lemma (Integral Eichler maps).** Let $J$ be unimodular, let $u$ be integral with $u^*J$ the dual of $z$ and $u_z = 0$, and let $e$ be integral with $z$-coordinate $r$, a unit of $R$. Then the scaled Eichler map along $u$ attached to $e$ is an integral isometry.

Lean: `New.Floors.IntegralPlace.topEichler_mem_unitaryLevel_one` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The matrix of the map is $1$ plus $r^{-1}$ times a difference of two rank one matrices of the form $a\,(b^*J)$, with $a$ and $b$ integral combinations of $e$, $z$ and $u$. A rank one matrix of integral vectors against a unimodular $J$ is integral, and $r^{-1} \in R$. An integral isometry of a unimodular form is invertible over $R$. $\square$

**Lemma (The measure on the top floor).** Let $J$ be unimodular, $u$ as above, and $B$ an integral hyperbolic basis as in the lemma before. There is an s-finite measure $\theta$ carried by $G^{(\varrho)}$ whose image under $\sigma \mapsto \sigma^{-1}z$ is the measure of the top quadric of $B$, and with $\theta(K) \ge \mathrm{vol}(R^\times)$.

Lean: `New.Floors.IntegralPlace.exists_measure_floorGroup_top` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The flat chart of $B$ maps parameters $((t, w), a)$, with $a$ skew, to points $\varphi(t, w, a)$ of the top quadric, and it carries the volume times the skew measure to the quadric measure ([local frames](/chapter/local-frames/#quadrics-and-plancherel)). Let $\theta$ be the image of the same measure under the scaled Eichler map $\Phi(t, w, a)$ attached to $\varphi(t, w, a)$. When $t$ is a unit, which is true almost everywhere, $\Phi(t, w, a)^{-1}z = \varphi(t, w, a)$, so the two images agree. The parameters with all coordinates integral and $t \in R^\times$ have mass $\mathrm{vol}(R^\times)$, since the other integral coordinates have volume $1$. Their Eichler maps are integral isometries by the lemma before, so $\theta(K) \ge \mathrm{vol}(R^\times)$. $\square$

**Theorem (Lattice data exist).** Let $N \in R$ with $\bar N = N$, let $g$ be a unit in $R$ with $\bar g = g$, and let $k = \#\iota + 2m + 1$. Then there is place data $F$ for `latticeMiddleGram 𝔰 N` with $m$ further pairs such that $F$ is a lattice datum and $F$ has level unit $g$.

Lean: `New.Floors.IntegralPlace.exists_isLatticeData` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The form $J$ is unimodular because `latticeMiddleGram 𝔰 N` is. Let $u = -v$, the negative of the lattice basis vector $v = x_{k_0}/\bar\pi + z/N$. Then $u$ is integral, since it is a basis vector, $u^*J$ is the dual of $z$, and $u_z = 0$. This is field 3. Take $B$ from the lemma on hyperbolic bases, $\theta$ from the lemma on the top floor, and $\eta$ from the lemma on $H$. Let $F$ be $B$ with the top floor measure $\theta$, the measure $\eta$ on $H$, the level unit $g$, the congruent pairs of level $g$ as close pairs, $K$ as box, and $\{y^{-1}uy\} \cdot K(g)$ as positions. The axioms of place data hold: the close pairs form a compact neighbourhood by the lemma on congruent pairs, $K$ is compact and open, so the positions are measurable, and $\eta \neq 0$ since $\eta(K) = 1$. Fields 1 and 2 hold by construction. $\square$

**Remark (Formalization).** The theorem gives existence only, and the main term ([the main term](/chapter/main-term/)) uses any lattice datum. The positions are $\{y^{-1}uy\}\cdot K(g)$, a union of conjugates of $\mathsf{U}$ times $K(g)$, and not a subgroup. Only its measurability and the shape of its elements are used.

### Large lattice data

The bounds of the abstract chapter need ranks that are large compared with $n$, and an ideal zeta value close to $1$.

**Definition (Large lattice datum).** Place data $F$ with $m + 1$ further pairs form a *large lattice datum* (`P.IsLargeLatticeData F`) if $F$ is a lattice datum and:

1. $\zeta_R(m)^n \le 1 + 2^{-n}$, $m < 9n$, and $53n \le \#\iota$;
2. $\psi(x + \bar x) = 1$ for all $x \in A$;
3. some Haar measure on $\mathsf{G}$ is right invariant.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData` (New/Spanning/Frames/StandardLevel.lean).

Here $\zeta_R(m) = \sum_I[R : I]^{-m}$ over the ideals of finite index (`New.idealZeta`). Field 1 gives $\zeta_R(m) \le 2$ (`New.Floors.IntegralPlace.IsLargeLatticeData.idealZeta_le_two`). It is a class in the source, so the instance is found automatically in the rest of the chapter.

**Remark (Formalization).** Field 3 is unimodularity of $\mathsf{G}$. It is true for unitary groups, but the source does not prove it here and keeps it as a field. Field 2 says that $\psi$ is trivial on traces; it makes the characters on the quadrics depend only on the skew part.

**Lemma (Inverse moduli of powers).** For a unit $\alpha$ and $j \in \mathbb{N}$, $|\alpha^j|^{-1} \le (2/|\alpha|)^j$. If $\alpha \in R$ and $jn + 1 \le k'$, then

$$\zeta_R(m)\,|\alpha^j|^{-n} \le (2/|\alpha|)^{k'}.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.inv_modulus_pow_le`, `New.Floors.IntegralPlace.IsLargeLatticeData.idealZeta_mul_inv_modulus_pow_le` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* The first bound is $|\alpha|^{-j} \le 2^j|\alpha|^{-j}$. For the second, $|\alpha| \le 1$ gives $2/|\alpha| \ge 2 \ge \zeta_R(m)$. So the left side is at most $(2/|\alpha|)\cdot(2/|\alpha|)^{jn} = (2/|\alpha|)^{jn+1}$, and $2/|\alpha| \ge 1$ allows the larger exponent $k'$. $\square$

**Lemma (Block kernels).** A block has rank $2m + 4$. There is an s-finite kernel $q$ from the skew elements to $A^{2m+4}$ that disintegrates the volume along the standard form, such that for every skew $\beta$ and unit $u$ the points $y$ with every $uy_i \in R$ have $q_\beta$-mass at most $\zeta_R(m)\,|u|^{-(2m+3)}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_kernel_isDisintegration_coordinateBox_le` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* This is the disintegration with bounded masses of [Siegel-Weil](/chapter/siegel-weil/#local-densities-at-a-finite-place), with $r = 2m + 3$, $\mu = m$ and $\#\kappa = r + 1$; its hypotheses are field 2 and $\zeta_R(m) \le 2$. $\square$

### The gauge of scale α

**Definition (Gauge of scale α).** Let $\alpha$ be a unit with $\alpha \in R$ and $\bar\alpha = \alpha$. The gauge $\Gamma_\alpha$ (`gauge α`) has the sizes

$$\mathrm{ofSize}(j) = \{x \in A : \alpha^jx \in R\} = \alpha^{-j}R,$$

and the loss $\Lambda = 2/|\alpha|$. The default is $\alpha = 1$, where every size is $R$ and $\Lambda = 2$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.gauge` (New/Spanning/Frames/StandardLevel.lean).

The fields of a gauge ([local frames](/chapter/local-frames/#place-data-floors-and-gauges)) are checked one by one in the source. Most are closure properties of the ideals $\alpha^{-j}R$. Four need an argument. The volume of $\alpha^{-j}R$ is $|\alpha^j|^{-1} \le \Lambda^j$ by the lemma on inverse moduli. For the close pairs, $c = \alpha^{i+1}$ works: one factor $\alpha$ clears the denominator $g$, the others clear those of the vectors. The block kernels come from the lemma on block kernels and the bound $\zeta_R(m)|\alpha^j|^{-(2m+3)} \le \Lambda^{k'}$ with $j(2m+3) + 1 \le k'$. The common bound is the next lemma.

**Lemma (Common bounds).** Let $\alpha \in R$ be a unit and $S$ the sizes with $\mathrm{ofSize}(j) = \alpha^{-j}R$. Let $x \in K$, $z$ a position, and $W$ the common vectors of $x$, $z$ and $v$. There is a measurable $\varphi$ that is a common bound with loss $2/|\alpha|$ for $W$; in particular $\int_{\text{size } j}\varphi^s \le (2/|\alpha|)^{99n(j+1)}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_isCommonBound` (New/Spanning/Frames/StandardLevel.lean).

*Proof.* Split the free indices into $3\varrho$ excepted indices and $d = s + m + 5$ others. There is a matrix $V$ invertible over $R$ such that the integral combinations $Yt$ of its $d$ columns $Y$ at the other indices are common vectors (`New.Floors.IntegralPlace.IsLargeLatticeData.exists_intGL_mulVec_mem_commonVectors`). Take for $\varphi(w)$ the content index of $Y^*w$. If $t$ is the content of $Y^*w$, the products of $w$ with the common vectors $Y(a\bar r)$ fill $\bar tR$, so $\mathrm{vol}\langle w, W\rangle \ge |\bar t|$ and $\varphi(w) = |\bar t|^{-1}$ bounds its inverse. If $\langle cw, W\rangle$ lies in the product differences, which are integral (`New.Floors.IntegralPlace.IsLargeLatticeData.mem_of_mem_productDifferences`), then each $c(Y^*w)_i$ is integral; so the set of these $c$ has volume at most $\varphi(w)$. For the integral, the integral of a power of a content index over $(\alpha^{-j}R)^{d'}$ is at most $\zeta_R(m)|\alpha^j|^{-(3\varrho+m+5)}$, and the lemma on inverse moduli bounds this by $(2/|\alpha|)^{99n(j+1)}$, since $m < 9n$. $\square$

**Example.** For $\alpha = 1$ every size is $R$, the loss is $2$, and the gauge measures nothing but integrality. This is the gauge of the mass computations of the next section. For $\alpha = \pi^c$ with $\pi$ a uniformizer of a field with $q$ residues, $\mathrm{ofSize}(j) = \pi^{-cj}R$ and $\Lambda = 2q^c$. The shells of [the section on shells](/chapter/finite-densities/#shells-decay-and-mass) use $\alpha = \bar cc$ for a generator $c$ of a denominator ideal.
