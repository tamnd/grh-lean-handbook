---
title: Stable spaces and self-dual lattices
lean:
  - New/Determinant/Exchange/StableSpacesStandardData.lean
decls:
  - New.Exchange.exists_pow_smul_add_eq
  - New.Exchange.match_mul_stdColDatum_translate
  - New.Exchange.match_mem_of_stdColDatum
  - New.Exchange.IntegralFrame.stdColDatum_shear_of_isIntMatrix
  - New.Exchange.sum_mul_addChar_lift_eq_zero
  - New.Exchange.IntegralFrame.stdColDatum_mul_sub_smul
  - New.Exchange.IntegralFrame.match_mem_of_isPrimitiveMatrix_vanishing
  - New.Exchange.IsEquivariantLift.apply_eq_zero_of_centreCoeff_eq_zero
  - New.Exchange.IsSelfDualTestPair
  - New.Space.Splitting.VanishesAtSelfDual
  - New.Space.Splitting.centreCoeff_eq_zero_of_orthonormal
  - New.Exchange.IsEquivariantLift.partialMean_shear
  - New.Exchange.IsEquivariantLift.exists_linear_partialMean
  - New.Exchange.IsEquivariantLift.shearInvariant_stdColDatum
  - New.Exchange.IsEquivariantLift.apply_eq_zero_of_areMatched
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Stable spaces and self-dual lattices

This section proves that an equivariant lift $\mathcal{D}$ is zero on all matched data once one value of it, the image of the standard datum of a frame, has vanishing Fourier coefficients at the self-dual lattices. The proof has a local part and a global part. The local part shows that a $GL_n(F)$-stable space $P$ that contains one standard datum contains every matched datum. The global part takes for $P$ the kernel of $\mathcal{D}$, and uses the Fourier coefficients along a frame to show that $P$ contains the standard datum.

### A stable space with one standard datum

Let $F$ be a semilocal field, $\chi$ a tame character, and $e \colon b \sqcup a \to n$ a split of the indices. Recall from Section 2 the standard column datum $\Psi_s(y) = \chi_O^{-1}(\det(s y))$ for integral $y$.

**Lemma.** Let $\Psi$ be locally constant and matched with some $\Phi$ for $\chi$ over $O$. There is $c \in \mathbb{N}$ with $\Psi(\varpi^c t + y) = \Psi(y)$ for all $y$ and all integral $t$.

Lean: `New.Exchange.exists_pow_smul_add_eq` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* $\Psi$ vanishes off the primitive matrices, which form a compact set. A locally constant function with compact support is uniformly locally constant. The sets $\varpi^c O$ form a basis of neighbourhoods of $0$, as $\varpi^c \to 0$ and $O$ is compact and open. $\square$

**Lemma.** Let $\Psi$ be matched with $\Phi$ and invariant under $\varpi^c$ times integral matrices. Let $s$ and $x$ be integral with $s x = 1$, and let $p = r \cdot \Psi_s$ with $r$ a function with values in $\mathbb{N}$. Put $d = \varpi^{-c}(1 - x s) + x s$. Then for every $k \in GL_n(O)$ and every $y$,
$$\Psi(k^{-1} x)\, p(d k y) = |p(d k y)|\, \Psi(y).$$

Lean: `New.Exchange.match_mul_stdColDatum_translate` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* The matrix $d$ is the identity on the columns of $x$ and multiplies the kernel of $s$ by $\varpi^{-c}$. Its inverse is $\varpi^c(1 - x s) + x s$, and $s d = s$. If $p(dky) = 0$, both sides are $0$. Otherwise $d k y$ is integral and $u = s\, d k y = s k y$ is in $GL_b(O)$. Then $k y = d^{-1}(d k y) = x u + \varpi^c t$ with $t$ integral, so $\Psi(y) = \Psi(k^{-1} x u)$ by the invariance, because $k^{-1}\varpi^c t = \varpi^c (k^{-1} t)$. The matching gives $\Psi(y' g) = \chi(\det g)^{-1}\Psi(y')$ for $y'$ a block of columns of an integral matrix and $g \in GL_b(O)$: apply the matching condition at $k'$ and at $k' \operatorname{diag}(g, 1)$, which have the same rows $x_{k'}$. So $\Psi(y) = \chi(\det u)^{-1}\Psi(k^{-1}x)$. Also $p(dky) = r(dky)\, \chi(\det u)^{-1}$, and $|p(dky)| = r(dky)$, as $\chi$ has modulus $1$ on units. Both sides equal $r(dky)\chi(\det u)^{-1}\Psi(k^{-1}x)$. $\square$

**Theorem (One standard datum suffices).** Let $P$ be a space of locally constant functions with compact support on the $n \times b$ matrices, stable under $f \mapsto f(g\, \cdot)$ for $g \in GL_n(F)$. Suppose that $P$ contains $p = r \cdot \Psi_s$, where $s$ is integral, $r$ has values in $\mathbb{N}$, and $r(x) \neq 0$ at an integral $x$ with $s x = 1$. Then $P$ contains every locally constant $\Psi$ that is matched with some $\Phi$ for $\chi$ over $O$.

Lean: `New.Exchange.match_mem_of_stdColDatum` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* Take $c$ and $d$ as in the two lemmas. The function
$$A(y) = \int_{GL_n(O)} \Psi(k^{-1} x)\, p(d k y)\, dk$$
lies in $P$: the integrand is locally constant in $k$, so $A$ is a finite combination of the translates $p(dk\, \cdot)$. By the second lemma, $A(y) = I(y)\, \Psi(y)$ with $I(y) = \int |p(dky)|\, dk \geq 0$. If $\Psi(y) \neq 0$, then $y$ is a block of columns of some $j \in GL_n(O)$, and so is $x$, of some $l$. So $y = j l^{-1} x$, and the right invariance of the Haar measure gives $I(y) = I(x)$. At $k$ near $1$ we have $d k x$ near $d x = x$, and $p(x) = r(x)\chi_O^{-1}(1) = r(x) \neq 0$. So $I(x) > 0$, and $\Psi = I(x)^{-1} A \in P$. $\square$

### Shears of a frame and Gauss sums

An *integral frame* is a matrix in $GL_n(O)$ cut into column blocks $(K\ I\ L)$, with $K$ and $L$ of width $b$. The rows of its inverse are cut into the blocks $K'$, $I'$, $L'$. So $K'K = L'L = 1$ and $K'L = L'K = 0$. Put $S_0 = \Psi_{K'}$ and, for a $b \times b$ matrix $z$, let $S_z(y) = S_0(y + L z K' y)$ be its *shear*.

**Lemma.** For integral $z$, $S_z = S_0$. For a matrix $r$ over $O$ and integral $x$,
$$\Psi_{L'}\bigl(L\, r\, K' x - \varpi x\bigr) = \eta(\det \bar r)\, \Psi_{K'}(x),$$
where $\bar r$ is the reduction of $r$ and $\eta$ is the residue character of $\chi$.

Lean: `New.Exchange.IntegralFrame.stdColDatum_shear_of_isIntMatrix`, `New.Exchange.IntegralFrame.stdColDatum_mul_sub_smul` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* For integral $z$ the shear is integral with integral inverse $y \mapsto y - L z K' y$, and $K'(y + L z K' y) = K' y$. For the second statement, $L'(L r K' x - \varpi x) = r K' x - \varpi L' x$, whose determinant reduces to $\det \bar r \cdot \det \overline{K' x}$. By tameness, $\chi^{-1}_O$ of an integral determinant is $\eta$ of its reduction. $\square$

**Lemma (Gauss sums of matrices).** Let $\pi \colon O \to R$ be the residue map, $\eta$ a primitive character of $R$, and $\varphi$ a primitive additive character of $R$ with $\varphi(\pi t) = \psi(\varpi^{-1} t)$. Let $l$ lift $b \times b$ matrices over $R$ to $O$. If $T$ is a matrix over $O$ with $\eta(\det \bar T) = 0$, then
$$\sum_{r \in M_b(R)} \eta(\det r)\, \psi\bigl(\varpi^{-1} \operatorname{tr}(T\, l(r))\bigr) = 0.$$

Lean: `New.Exchange.sum_mul_addChar_lift_eq_zero` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* The sum is $\sum_r \eta(\det r)\varphi(\operatorname{tr}(\bar T r))$. As $\det \bar T$ is not a unit, there is a factor of $R$ in which $\bar T$ is singular. There the image of $\bar T$ is a proper subspace, so for every unit $\lambda$ there is $u$ with $u \bar T = \bar T$ and $\det u = \lambda$. The change of variables $r \mapsto r u$ multiplies the sum by $\eta(\lambda)$, because $\operatorname{tr}(\bar T r u) = \operatorname{tr}(u \bar T r)$. As $\eta$ is primitive, $\eta(\lambda) \neq 1$ for some $\lambda$. So the sum is $0$. $\square$

**Theorem.** Let $\psi$ have conductor $O$, let $P$ be as in the previous theorem, and let $M$ be a space that contains every shear $S_z$. Suppose that $P$ contains every $f \in M$ with $\Lambda(f) = 0$ for all pairs $(T, \Lambda)$ of a $b \times b$ matrix and a linear functional such that
$$\Lambda(S_z) = \psi(\operatorname{tr}(T z))\, \Lambda(S_0) \text{ for all } z, \quad\text{and}\quad \Lambda(S_0) = 0 \text{ if } T \in GL_b(O).$$
Then $P$ contains every locally constant $\Psi$ that is matched with some $\Phi$ for $\chi$ over $O$.

Lean: `New.Exchange.IntegralFrame.match_mem_of_isPrimitiveMatrix_vanishing` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* Put $f = \sum_{r \in M_b(R)} \eta(\det r)\, S_{\varpi^{-1} l(r)}$, with $l(1) = 1$. Then $f \in M$. Let $(T, \Lambda)$ be a pair as in the hypothesis, with $\Lambda(S_0) \neq 0$. As $S_z = S_0$ for integral $z$, $\psi(\operatorname{tr}(Tz)) = 1$ for all integral $z$, so $T$ is integral. By hypothesis $T \notin GL_b(O)$, so $\eta(\det \bar T) = 0$, and $\Lambda(f)$ is $\Lambda(S_0)$ times the vanishing Gauss sum. So $f \in P$. Now translate $f$ by $y \mapsto -\varpi^{-1} y$. By the lemma on shears, each nonzero term of the translate at $y$ equals $\Psi_{L'}(y)$, so the translate is $r_0 \cdot \Psi_{L'}$ with $r_0(y)$ the number of nonzero terms. At $x = L - \varpi K$ we have $L' x = 1$, and the term $r = 1$ does not vanish, as $\Psi_{K'}(K) = 1$. The previous theorem applies, with $s = L'$. $\square$

### Fourier coefficients of a lift

From here on, $\mathcal{D}$ is an equivariant lift on $M$ (Section 4), for a hermitian space $X$ of rank $m$. Let $D$ split $X$ as $W_1$ plus $b$ hyperbolic planes, with an adapted frame. Its isotropic frame at $S$, read through the components at $S$, is an integral frame, and $\Psi_0 = \Psi_{L'}$ is the standard datum of its block $L'$, for $\chi = \chi_{\mathfrak{c}}$. The Fourier coefficients along $D$ are those of [singular forms](/chapter/rallis-inner-product/#singular-forms).

**Proposition.** Suppose that $\Psi_0 \in M$ and that the coefficient of $\mathcal{D}\Psi_0$ along $D$ at a skew-hermitian index $T$ vanishes at every point $(1, g)$ with $g$ trivial at $S$, whenever $\delta^{-1} T$ lies in $GL_b(O)$ at $S$; here $\delta$ is the inverse different idele. Then $\mathcal{D}\Psi = 0$ for every locally constant $\Psi$ that is matched with some $\Phi$ for $\chi_{\mathfrak{c}}$ over $O$.

Lean: `New.Exchange.IsEquivariantLift.apply_eq_zero_of_centreCoeff_eq_zero` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* Let $P = M \cap \ker \mathcal{D}$. By law 3 of an equivariant lift, $P$ is stable under $GL_m(F)$, since every element of $GL_m(F)$ is the component at $S$ of a point of $U(X)$. Apply the previous theorem with the shears of the frame of $D$. The functionals are the coefficients: $\Lambda_{T,x}(f) = (\mathcal{D} f)_T(x)$. A shear $S_z$ is the datum moved by a point of the centre of the radical at $S$, and law 3 turns it into a translation of $\mathcal{D}f$ by that point, which multiplies the coefficient by $\psi(\operatorname{tr}(Tz))$. So the hypothesis of the theorem is that a datum $f \in M$ whose coefficients $(\mathcal{D}f)_T(x)$ all vanish lies in $\ker\mathcal{D}$. This holds. The function $\mathcal{D} f$ is continuous and left invariant under the rational points, and a function on the compact quotient of the centre is $0$ if all its Fourier coefficients are $0$. Only skew-hermitian $T$ occur, as the hermitian matrices are periods of the centre. By weak approximation, [Volume 4](/chapter/adeles-hermitian-spaces/), and the invariance laws, it is enough to test the points $(1, g)$ with $g$ trivial at $S$. The condition $\Lambda(S_0) = 0$ for unimodular $T$ is the hypothesis of the proposition. $\square$

### Vanishing at self-dual lattices

Let $V'$ be a hermitian space of rank $b$ with Gram matrix $J'$, signs $t'$ and adelic frame $x'$. Let $\jmath$ be the skew element and $\lambda$ the scaling idele of the Weil data, which makes $\hat O$ self-dual.

**Definition.** A pair $(T, q)$ of a $b \times b$ matrix over $E$ and a point $q \in GL_b(\mathbb{A})$ is a *self-dual test pair* for $V'$ if either

(a) $T = J'$ and $q = \lambda\, x'\, Y$, where the finite part of $Y$ times some $k \in GL_b(\hat O)$ is unitary for the form $1$; or

(b) $T$ is invertible and at some infinite place $T$ is not of the form $a^* \operatorname{diag}(t') a$.

A function $f$ on $U(X)$ *vanishes at self-dual lattices* if its coefficient along $D$ at $\jmath T$ vanishes at every point $\rho\, m(q, g)$, with $\rho$ in the radical and $m(q, g)$ in the Levi, for every test pair $(T, q)$.

Lean: `New.Exchange.IsSelfDualTestPair`, `New.Space.Splitting.VanishesAtSelfDual` (New/Determinant/Exchange/StableSpacesStandardData.lean).

In case (a) the columns of $x' Y$ span a lattice that is self-dual for $J'$. Case (b) covers the indices that $V'$ cannot represent; Section 6 shows that both sides of the exchange identity have vanishing coefficients there.

**Lemma (Landherr).** Let $f$ be automorphic and vanish at self-dual lattices. Let $\det\beta \neq 0$, and let the columns of $q k$, with $k \in GL_b(\hat O)$, be orthonormal for $\beta$ at the finite places. Then the coefficient of $f$ at $\jmath \beta$ vanishes at $\rho\, m(\lambda q, g)$ for all $\rho$ and $g$.

Lean: `New.Space.Splitting.centreCoeff_eq_zero_of_orthonormal` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* If $\beta$ is not of the form $a^*\operatorname{diag}(t')a$ at some infinite place, case (b) applies. Otherwise $\beta$ and $J'$ have the same signs at infinity, and both have unimodular lattices at all finite places. By the theorem of Landherr, the Hasse principle for hermitian forms, $\beta = c^* J' c$ for a rational $c$. Move $c$ from the index to the point by the rational Levi point $m(c, 1)$, which changes $\jmath\beta$ to $\jmath J'$ and $q$ to $c q$. The finite part of $x'^{-1} c q k$ is unitary, so the new pair is a test pair of case (a). $\square$

### Shear invariance

The criterion [after Freitag](/chapter/rallis-inner-product/#singular-forms) needs the partial means of the coefficients to be invariant under local shears along an extra isotropic line.

**Lemma.** Let $A$ split one isotropic line off $X$ and $B$ split $b$ planes off the rest, compatibly with $D$. Then:

1. a point $\nu$ that is $1 + u c$ at $S$, with $c u = 0$, moves the partial mean of $\mathcal{D}\Psi$ at $x$ to the partial mean of $\mathcal{D}\Psi'$ at $\nu x$, where $\Psi'(y) = \Psi(g y)$ and $g$ is the component of $x^{-1}\nu x$ at $S$;
2. at each $x$, the partial mean of $\mathcal{D}\Psi$ is a linear form in $\Psi \in M$ that is invariant under $y \mapsto y + u\, w\, l\, y$ for all rows $w$;
3. the partial means of the coefficients of $\mathcal{D}\Psi_0$ are shear invariant.

Lean: `New.Exchange.IsEquivariantLift.partialMean_shear`, `New.Exchange.IsEquivariantLift.exists_linear_partialMean`, `New.Exchange.IsEquivariantLift.shearInvariant_stdColDatum` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* Part 1 is law 3 of the lift for the point $x^{-1}\nu x$, which is supported on $S \cup \bar S$. Part 2: a shift by a rational row fixes the partial mean, which is a mean over these shifts, and the shift acts on the datum by the stated map. Part 3: at $S$ the shears along the line $u$ of $A$ do not change the coordinates $L' y$ that $\Psi_0$ reads, because $L'$ kills the line; so part 2 fixes the value at $\Psi_0$. $\square$

**Theorem (Vanishing on matched data).** Let $\mathcal{D}$ be an equivariant lift on $M$, with $D$ and a splitting $D_1$ of $W_1$ adapted. Suppose that $\Psi_0 \in M$ and that $\mathcal{D}\Psi_0$ vanishes at self-dual lattices for $V'$. Then $\mathcal{D}\Psi = 0$ for every locally constant $\Psi$ that is matched with some $\Phi$ for $\chi_{\mathfrak{c}}$ over $O$.

Lean: `New.Exchange.IsEquivariantLift.apply_eq_zero_of_areMatched` (New/Determinant/Exchange/StableSpacesStandardData.lean).

*Proof.* By the proposition it suffices to show that $(\mathcal{D}\Psi_0)_T(1, g) = 0$ when $T$ is skew-hermitian, $\tau = \delta^{-1} T$ is unimodular at $S$, and $g$ is trivial at $S$. Such $T$ is invertible. By part 3 of the lemma, the criterion after Freitag applies, with the shears at $\bar S$ and with the places off $S \cup \bar S$ as its set. It reduces the claim to points $\rho\, m(q_0, g)$ at which the Gram matrix $T[q_0]$ is unimodular at all finite places: at $S \cup \bar S$ it is $\tau$, and elsewhere it is $T[\gamma]$, primitive by the criterion. A unimodular hermitian matrix over $\hat O$ has an integral orthonormal basis $k$. With $T = \jmath\beta$ and $q_0 = \lambda q$, the columns of $q k$ are orthonormal for $\beta$, and the lemma of Landherr gives the vanishing. $\square$

**Remark (Formalization).** The test pairs of case (a) use the frame of $V'$ only up to $GL_b(\hat O)$ and a unitary matrix. The source glues the Gram matrix at $S$ and off $S$ by an idempotent adele; the lemma `New.Exchange.SplitTameChar.isIntMatrix_glue_hermitian` checks that the glued matrix is integral. The source cites Landherr for the Hasse principle; the citation is in the notes of this chapter.
