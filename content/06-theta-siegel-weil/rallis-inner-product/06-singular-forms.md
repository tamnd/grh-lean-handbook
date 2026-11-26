---
title: Singular forms
lean:
  - Lib/Adelic/Witt/IwasawaDecomposition.lean
  - Lib/SiegelWeil/SingularForms/CentreCoefficients.lean
  - Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean
decls:
  - New.Space.Splitting.centreCoeff
  - New.Exchange.IsAutFunction
  - New.Space.Splitting.lineShift
  - New.Space.Splitting.partialMean
  - New.Space.Splitting.shiftedMean
  - New.Space.Splitting.centreCoeff_eq_mul_of_shiftedMean_eq_smul
  - New.Space.Splitting.shiftedMean_symm_eq_smul
  - New.Space.Splitting.frameStabilizer
  - New.Space.Splitting.ShearInvariant
  - New.Space.Splitting.borderedCentreCoeff
  - New.Space.Splitting.partialMean_radicalElement_mul
  - New.Exchange.closureIntegers
  - New.Exchange.closurePart
  - New.Exchange.invDifferentIdele
  - New.Exchange.siegelBracket
  - New.Exchange.dualIndex
  - New.IsPrimitiveMatrix
  - New.Exchange.StraightPoint
  - New.Exchange.exists_straightPoint
  - New.Exchange.centreCoeff_eq_zero_of_unimodular
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Singular forms

A Siegel modular form is *singular* if its Fourier coefficients vanish at all nonsingular indices. Freitag studied these forms and their relation to theta series. The source proves an adelic and unitary analogue of one of the ideas of that theory. A function with enough invariance along an extra isotropic line is governed by its Fourier coefficients at unimodular indices: if these vanish, then all its coefficients at a fixed index $T$ vanish on a large set of points. The source uses this criterion to show that certain lifts vanish. The forms here are not holomorphic, and "singular" means invariance under local shears, not a condition on the weight.

### Fourier coefficients along a frame

Let $W$ be a hermitian space over $E$. A splitting $D$ of $W$ into $p$ hyperbolic planes and a complement has an isotropic frame $k$ of $p$ vectors. The stabilizer of the span of $k$ has a unipotent radical. Its centre contains the elements $z(M)$, for $p \times p$ adelic matrices $M$, with $z(M) = 1 + k(M - M^*)k^*\varepsilon$, where $\varepsilon$ is the standard form.

**Definition.** A function $f$ on $U(W)(\mathbb{A})$ is *automorphic* if it is continuous and left invariant under the rational points. For a $p \times p$ matrix $T$ over $E$ the *Fourier coefficient* of $f$ along $D$ at $T$ is
$$f_T(g) = \int_{M \in M_p(\mathbb{A}) / M_p(E)} \psi(\operatorname{tr}(TM))\, f(z(M) g)\, dM,$$
the mean over adelic matrices modulo rational ones, with $\psi$ the standard additive character.

Lean: `New.Exchange.IsAutFunction` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean), `New.Space.Splitting.centreCoeff` (Lib/Adelic/Witt/IwasawaDecomposition.lean).

### An extra isotropic line

The criterion needs one more hyperbolic plane. Let $A$ split a hyperbolic plane off $W$, with isotropic vectors $u$ and $u'$ and complement $W_0$. Let $B$ split $p$ planes off $W_0$. The frame of $D$ is the image in $W$ of the frame of $B$; the source writes this condition as `D.kAdelic = A.iAdelic * B.kAdelic`. For an adelic row $a$ of length $p$ the *shift* $n_+(a)$ moves $u$ to $u - k a^*$ and fixes $k$. The shift $n_-(b)$ does the same for $u'$; it is the shift of the splitting with $u$ and $u'$ exchanged.

**Definition.** The *partial mean* of $f$ at $T$ is
$$f^+(g) = \int_{b} f_T(n_-(b)\, g)\, db,$$
the mean over adelic rows $b$ modulo rational rows. For a point $g$, the *shifted mean* is the function $\varphi^+_g(a) = f^+(n_+(a)\, g)$ of an adelic row $a$. Exchange $u$ and $u'$ to get $f^-$ and $\varphi^-_g$.

Lean: `New.Space.Splitting.lineShift`, `New.Space.Splitting.partialMean`, `New.Space.Splitting.shiftedMean` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

The functions $\varphi^+_g$ and $\varphi^-_g$ behave like a function and its Fourier transform. The next lemma makes this precise in one direction.

**Lemma.** Let $f$ be automorphic, let $\det T \neq 0$, and let $g, g'$ be points and $c \in \mathbb{C}$ with $\varphi^+_{g'} = c\, \varphi^+_g$. Then for all rows $a$, $b$,
$$f_T(n_-(b)\, n_+(a)\, g') = c\, f_T(n_-(b)\, n_+(a)\, g),$$
and $\varphi^-_{g'} = c\, \varphi^-_g$.

Lean: `New.Space.Splitting.centreCoeff_eq_mul_of_shiftedMean_eq_smul`, `New.Space.Splitting.shiftedMean_symm_eq_smul` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

*Proof.* The function $b \mapsto f_T(n_-(b) n_+(a) g)$ is continuous and periodic under rational rows. Its Fourier coefficient at a rational column $R$ is a value of $\varphi^+_g$: a shift by a rational row $a_0$ with $-T a_0^* = R$ turns the character into the mean that defines $f^+$. As $T$ is invertible, every $R$ has such an $a_0$. So the difference of the two sides has all its Fourier coefficients equal to $0$, and it is $0$. For $\varphi^-$, the order of the two shifts changes the coefficient only by a character that does not depend on the point. $\square$

### Shear invariance and singularity

**Definition.** For an adele $e$, the *frame stabilizer* is the group of the points $g$ with $g \cdot e k = e k$. If $e$ is the idempotent of a set of places, these are the points that fix the frame at those places.

Lean: `New.Space.Splitting.frameStabilizer` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

**Definition.** Let $e$ be an adele and $g$ a point. The partial mean $f^+$ is *shear invariant* for $e$ at $g$ if $f^+(\nu g) = f^+(g)$ for every point $\nu$ with matrix
$$1 + \bar e\, u c - e\, a,$$
where $c$ is a row with $c u = 0$ and $a$ is any matrix. If $e$ is the idempotent of a set $U$ of places that is disjoint from its conjugate, such a $\nu$ is $1 + uc$ on $\bar U$ and $1$ off $U \cup \bar U$.

Lean: `New.Space.Splitting.ShearInvariant` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

**Definition.** The *bordered coefficient* of $f$ is its Fourier coefficient along the composite splitting of $A$ and $B$, which has the frame $(u, k)$, at the block matrix $0 \oplus T$.

Lean: `New.Space.Splitting.borderedCentreCoeff` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

**Lemma (Singularity).** Let the frame of $D$ be the image of the frame of $B$, let $f$ be automorphic, let $U$ be a nonempty set of finite places and $e$ an adele. Suppose that $f^+$ is shear invariant for the idempotent of $U$ at all points of the frame stabilizer of $e$. Let $h$ be an element of the adelic radical of the stabilizer of the line of $u$. If $g$ and $hg$ are in the frame stabilizer of $e$, then $f^+(hg) = f^+(g)$.

Lean: `New.Space.Splitting.partialMean_radicalElement_mul` (Lib/SiegelWeil/SingularForms/CentreCoefficients.lean).

*Proof.* At a point of the frame stabilizer, shear invariance gives $f^+ = $ the bordered coefficient. The bordered coefficient is invariant under the radical of the line of $u$. The shears at $U$ spread this invariance, by strong approximation for the additive group, first to the centre of the radical and then to the whole radical. So
$$f^+(hg) = f_{0 \oplus T}(hg) = f_{0 \oplus T}(g) = f^+(g),$$
where $f_{0 \oplus T}$ is the bordered coefficient. $\square$

The invariance is the point of the word "singular". A Fourier coefficient of a form that is invariant under the whole radical of an extra isotropic line behaves as if the index $T$ were bordered by a zero row and column. This is the adelic form of the condition that only singular indices occur.

### Lattices on a set of places

Fix a set $S$ of finite places, away from the level of $f$, and write $S \cup \bar S$ for its conjugate closure.

**Definition.** The ring $\mathcal{O}_S$ consists of the adeles that are integral at the places of $S \cup \bar S$. The *closure part* of a point keeps its components at $S \cup \bar S$ and replaces all others by $1$. Let $\delta = \jmath \kappa \bar\kappa$, where $\jmath$ and $\kappa$ come from the Weil data. For an adelic $p \times p$ matrix $\gamma$ put
$$T[\gamma] = \delta^{-1}\, \gamma^* T \gamma.$$
The *dual index* of $\gamma$ is the denominator, at $S \cup \bar S$, of $\det(T[\gamma])^{-1}$. A matrix $X$ is *primitive* over a ring if it is integral and has an integral left inverse.

Lean: `New.Exchange.closureIntegers`, `New.Exchange.closurePart`, `New.Exchange.invDifferentIdele`, `New.Exchange.siegelBracket`, `New.Exchange.dualIndex` (Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean), `New.IsPrimitiveMatrix` (Lib/Adelic/Witt/WittTheorem.lean).

The matrix $T[\gamma]$ is the Gram matrix of the lattice spanned by the columns of $\gamma$, in the normalization of the Weil data. If $T[\gamma]$ is invertible and integral at $S \cup \bar S$, the dual index is the index of this lattice in its dual. For a square matrix, primitive means integral with an integral inverse. So $T[\gamma]$ is primitive over $\mathcal{O}_S$ exactly when the lattice of $\gamma$ is self-dual at $S \cup \bar S$. The source calls such indices *unimodular*.

**Definition.** A *straight point* is a point $P$ with the following data. It fixes the frame of $D$ off $S \cup \bar S$. On $S \cup \bar S$ it agrees with a point that scales $u$ by $t$ and $u'$ by $t'$, with $t'^* t = 1$, and acts on the frame $k$ by a matrix $\gamma$.

Lean: `New.Exchange.StraightPoint` (Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean).

If $A$ and $B$ are adapted to the integral structure, the lattice of a straight point on $S \cup \bar S$ is the direct sum of its parts in the two isotropic lines and in their orthogonal complement. The columns of $\gamma$ span the part in the span of $k$.

**Lemma (Straightening).** Let $f$ be automorphic and right invariant under the integral points supported on $S \cup \bar S$. Let $f^+$ be shear invariant for a nonempty set $U$ of finite places at the points that fix the frame of $D$ off $S \cup \bar S$. Let $X$ be such a point, equal to $g$ on $S \cup \bar S$, and let $g\kappa$, with $\kappa$ integral, act on the frame $(u, k)$ by a block upper triangular matrix with last block $\gamma$. If $f^+(X) \neq 0$, then there is a straight point with matrix $\gamma$ whose shifted mean is not $0$.

Lean: `New.Exchange.exists_straightPoint` (Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean).

*Proof.* Write $g\kappa = h m$ with $h$ in the radical of the line of $u$ and $m$ in the Levi subgroup. Move $X$ by the parts of $h^{-1}$ and $\kappa$ on $S \cup \bar S$. The singularity lemma removes the part of $h^{-1}$, and the level of $f$ removes the part of $\kappa$. So the shifted mean of the new point at $0$ is $f^+(X) \neq 0$. $\square$

### The vanishing criterion

**Theorem (After Freitag).** Let $f$ be automorphic and right invariant under the integral points supported on $S \cup \bar S$. Let $A$ and $B$ be adapted to the integral structure, let the frame of $D$ be the image of the frame of $B$, let $\det T \neq 0$, and let $U$ be a nonempty set of finite places. Suppose that:

1. $f^+$ and $f^-$ are shear invariant for $U$ at all points that fix the frame of $D$ off $S \cup \bar S$;
2. $f_T(X) = 0$ for every point $X$ that acts on the frame by $\gamma$ on $S \cup \bar S$ and by $1$ elsewhere, whenever $T[\gamma]$ is primitive over $\mathcal{O}_S$.

Then $f_T(g) = 0$ for every point $g$ that fixes the frame of $D$ off $S \cup \bar S$.

Lean: `New.Exchange.centreCoeff_eq_zero_of_unimodular` (Lib/SiegelWeil/SingularForms/UnimodularCoefficients.lean).

*Proof.* Suppose that $f_T(g) \neq 0$. By the lemma on shifted means, $\varphi^+_g$ is not $0$. By the straightening lemma, some straight point has a shifted mean that is not $0$. Choose such a point $P$ with the least dual index. The dual index takes values in $\mathbb{N}$, so a least value exists.

Let $a$ be a row with $\varphi^+_P(a) \neq 0$. The minimality gives that $\gamma^{-1} a^* t$ is integral on $S \cup \bar S$. Otherwise a step in the direction of $a$ gives a straight point with a smaller dual index and a shifted mean that is not $0$. So $\varphi^+_P$ is supported on the lattice of $\gamma$, up to the scale $t$. The point $P$ with $u$ and $u'$ exchanged is a straight point for the exchanged splitting, with the same matrix $\gamma$. It also has the least dual index there: by the second part of the lemma on shifted means, with $c = 0$, a straight point with $\varphi^+ = 0$ has $\varphi^- = 0$. So the same argument shows that $\varphi^-_P$ is supported on the lattice of $\gamma$, up to the scale $t'$.

The two supports together show that the inverse of $T[\gamma]$ is integral on $S \cup \bar S$. The matrix $T[\gamma]$ is integral as $\varphi^+_P \neq 0$. So $T[\gamma]$ is primitive. A coefficient $f_T(Y)$ with $Y$ as in hypothesis 2 is then not $0$, which is false. $\square$

The proof is a descent on lattices. The dual index measures how far the lattice of $\gamma$ is from its dual. A nonzero coefficient at a lattice that is not self-dual gives a nonzero coefficient at a smaller index. This descent stops only at a self-dual lattice, and there the hypothesis says that the coefficient is $0$.

**Example.** Let $p = 1$, so $T = (t_0)$ with $t_0 \in E^\times$. A matrix $\gamma$ is an idele $\gamma$, and $T[\gamma] = \delta^{-1} \gamma \bar\gamma t_0$. It is primitive over $\mathcal{O}_S$ exactly when $\delta^{-1}\gamma\bar\gamma t_0$ is a unit at every place of $S \cup \bar S$. The theorem says that $f_T$ vanishes at all points that fix the frame off $S \cup \bar S$ if it vanishes at the points that scale the frame at $S \cup \bar S$ by such ideles.

### Where the criterion is used

The criterion is used in `New/Determinant/Exchange/StableSpacesStandardData.lean`. There $f$ is the image of a standard datum under an equivariant lift. The source proves the shear invariance of hypothesis 1 for these images in `New.Exchange.IsEquivariantLift.shearInvariant_stdColDatum`. Hypothesis 2 is the vanishing at self-dual lattices. The file then proves that such a lift vanishes on every locally constant datum that has a matched function.

**Remark (Formalization).** The source labels this a known result after E. Freitag, *Singular Modular Forms and Theta Relations*, Lecture Notes in Math. 1487, Springer (1991), and refers also to J.-S. Li, *Automorphic forms with degenerate Fourier coefficients*, Amer. J. Math. 119 (1997). It gives no theorem numbers. The setting of the source is adelic, unitary and not holomorphic. Freitag works with holomorphic Siegel modular forms, so no textbook statement has the exact form of the theorem above. Singularity is not derived from a weight condition. It is the hypothesis of shear invariance at a nonempty set $U$ of finite places, for both $f^+$ and $f^-$. The vanishing at unimodular indices is also a hypothesis. The theorem does not say that a singular form is a combination of theta series. The proof chooses a straight point of least dual index by well-foundedness; the choice does not enter the statement.
