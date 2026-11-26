---
title: Spaces, forms, lattices and normalizations
lean:
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
  - New/UpperBound/Objects/Rows.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
  - Lib/General/Analysis/FiniteFourier.lean
  - Lib/General/Analysis/GaussianIntegral.lean
  - Lib/Adelic/QuotientMeasure/Basic.lean
decls:
  - New.Data.ϱ
  - New.Data.X
  - New.Data.RowIndex
  - New.Data.card_rowIndex
  - New.Data.Y
  - New.Data.spaceY
  - New.Data.spaceY_gram_eq
  - New.Data.spaceW
  - New.Data.signsW
  - New.Data.paramW
  - New.Data.targetParameter
  - New.Data.descentPair
  - New.Data.TameChar
  - New.Data.Twist
  - New.Data.MFoldTwist
  - New.Data.untwistedLiftChar
  - New.Data.liftChar
  - New.Data.chainChar
  - New.Data.goodForms
  - New.Data.targetForms
  - New.Data.targetDim
  - New.TwistedLattice
  - New.TwistedLattice.IndexLe
  - New.TwistedLattice.CovolumeLe
  - New.TwistedLattice.volume
  - New.HeightLe
  - New.Data.targetLattice
  - New.Exchange.matrixFourier
  - New.quotMean
  - New.Fock.normalizedVolume
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Spaces, forms, lattices and normalizations

This section fixes the letters of the upper bound: the hermitian spaces of the chain of theta lifts, the characters of the lifts, the forms, and the twisted lattices. It ends with the normalizations of inner products, norms, measures and Fourier transforms. Volume 1, [the twisted lattices](/chapter/twisted-lattices/) and [the integral target forms](/chapter/integral-target-forms/), use these objects.

### Hermitian spaces

A hermitian space over the CM field $E$ is given in Lean by a matrix $J$ over $E$ and a point $x \in \mathrm{GL}_n(\mathbb{A}_E)$ such that $x^* J x$ is the diagonal matrix of the signs at the infinite places and $1$ at the finite places. Lean's type is `New.Space E n s`, with $n$ the index type of the basis and $s$ the signs. The book writes a space with the letter of the space alone and keeps $J$ and $x$ for the rare places where they matter.

**Definition (The index types).** Let $\varrho = \lfloor m/2 \rfloor - 1$. The basis of $X_j$ has $n_j = k + j(t+1)$ indices. The basis of $Y_0$ has the indices $e_1, \ldots, e_\varrho$, the indices of $X_0$, a middle vector $z$, and $e_1^*, \ldots, e_\varrho^*$. The basis of $Y_j$ has the indices of $Y_0$ followed by $j$ blocks of $t$ indices.

Lean: `New.Data.ϱ` (New/UpperBound/Objects/LabelsAndIndexTypes.lean), `New.Data.X` (New/UpperBound/Objects/LabelsAndIndexTypes.lean), `New.Data.RowIndex` (New/UpperBound/Objects/LabelsAndIndexTypes.lean), `New.Data.Y` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

**Lemma.** The basis of $Y_0$ has $r$ elements.

Lean: `New.Data.card_rowIndex` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

*Proof.* The count is $2\varrho + n_0 + 1 = m - 2 + k + 1 = r$, since $m$ is even, $n_0 = k$, and $k = r + 1 - m$. $\square$

So $Y_j$ has dimension $r + jt$. The index type of $Y_0$ is called `RowIndex` because the same $r$ indices number the rows of the matrices of the finite group $\mathsf{G} = \prod_w \mathrm{GL}_r(\mathbb{F}_w)$ and the basis of $W_j$.

**Definition (The spaces $Y_j$).** For $j < m$, $Y_j$ is a hermitian space whose Gram matrix is the identity on $X_j$ and antidiagonal on a string of $2\varrho + 1 - j$ further vectors, with entries $1$ except for $-N$ at the middle vector if there is one. For $j \geq m$, $Y_j$ is standard: all signs are $1$ and the point is $1$.

Lean: `New.Data.spaceY` (New/UpperBound/Objects/Rows.lean), `New.Data.spaceY_gram_eq` (New/UpperBound/Objects/Rows.lean).

**Remark (Formalization).** The space `D.spaceY j` is defined by `choose` from an existence theorem. Lean fixes its Gram matrix for $j < m$ and its lattice up to a matrix that is invertible over the integral finite adeles and is $1$ modulo each chosen place. It does not fix a formula for the point. A statement on $Y_j$ uses only these properties, so the choice does not change its meaning.

**Definition (The spaces $W_j$ and $V$).** $W_j$ is the diagonal space of rank $r$ with the sign $+1$ on the first $k + j - 1$ basis numbers and $-1$ on the others. $V = I_{r+t}$ is the standard positive definite space of rank $r + t$.

Lean: `New.Data.spaceW` (New/UpperBound/Objects/Rows.lean), `New.Data.signsW` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

The number $k + j - 1$ is `D.posRank j`, and the basis numbers come from a fixed bijection of the index type with $\{0, \ldots, r - 1\}$. Volume 1 does not use the letters $W_j$ and $V$; it names only $Y_0$ and $Y_m$. The book uses $W_j$ and $V$ as the source does.

### Parameters, characters and twists

**Definition (The target parameter).** For a place $\tau$ and $0 \leq i < r$, the target parameter $\varsigma_\tau(i)$ is $k/2 - 1 - i$ for $i + 1 < k$, and $\Delta/2 - \kappa_{i+2-k}(\tau)$ otherwise. The parameter of $W_j$ at the index with basis number $i$ is $2\varsigma_\tau(i)$.

Lean: `New.Data.targetParameter` (New/Reduction/Data/LevelAndTwists.lean), `New.Data.paramW` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Lean defines the second case as $-\kappa^{(2(i+1-k)+1)}(\tau)$ and proves the form above in `New.Data.targetParameter_eq`. The doubling avoids half-integers: Lean stores $2\varsigma$ as an integer.

**Definition (Tame characters and twists).** A tame character $\vartheta$ is an automorphic character of $U(1)$ of weight $0$ with a finite set $Q$ of finite places of $E$, of norm prime to $MN$ and disjoint from its conjugate set, such that the tame part of $\vartheta$ is trivial off $Q$. A twist is a tame character with tame part not $1$ at each place of $Q$. An $m$-fold twist is a twist whose tame part $\psi_w$ has $\psi_w^n \neq 1$ for $1 \leq n \leq m$ and $w \in Q$.

Lean: `New.Data.TameChar` (New/Reduction/Data/LevelAndTwists.lean), `New.Data.Twist` (New/Reduction/Data/LevelAndTwists.lean), `New.Data.MFoldTwist` (New/Reduction/Data/LevelAndTwists.lean).

The book writes $\vartheta$ for a twist and $1$ for the trivial twist, as the source does. Volume 1 writes $\xi$ in [the twisted lattices](/chapter/twisted-lattices/), where the twists are abstract, and $\vartheta$ in [the integral target forms](/chapter/integral-target-forms/). The book keeps $\xi$ for the abstract twisted lattice and $\vartheta$ for the twists of the data.

**Definition (The characters of the lifts).** The untwisted character of the $j$-th lift is $\mu_j^0 = \chi_0 (\upsilon^{-\Delta} \chi_M)^j$, of weight $-\kappa_j$. The character of the $j$-th lift for $\vartheta$ is $\mu_j^0 \vartheta$, and the character of the chain is $\mu_j^0 \vartheta^j$.

Lean: `New.Data.untwistedLiftChar` (New/Reduction/Data/LevelAndTwists.lean), `New.Data.liftChar` (New/Reduction/Data/LevelAndTwists.lean), `New.Data.chainChar` (New/Reduction/Data/LevelAndTwists.lean).

Here $\upsilon$ is `New.WeilData.upsilonU1`, and $\chi_0$ and $\chi_M$ are `New.Data.chiZero` and `New.Data.chiM`. Both are chosen by `choose`. The $j$-th descent pair, `New.Data.descentPair`, collects $W_j$, $V$, the character $\mu_j^0\vartheta$, the places $M$ and $Q$, and the column counts.

Lean: `New.Data.descentPair` (New/UpperBound/Objects/Rows.lean).

### Forms

**Definition (Good forms and target forms).** The good forms on a space are the image of the idempotent $e_0 \in \mathbb{C}[\mathsf{G}]$ on the forms of principal level at the chosen places above $p_0$ and $p_1$. The target forms are the good forms on $Y_0$, and $d_0$ is their dimension over $\mathbb{C}$.

Lean: `New.Data.goodForms` (New/UpperBound/Objects/Rows.lean), `New.Data.targetForms` (New/UpperBound/Objects/Rows.lean), `New.Data.targetDim` (New/UpperBound/Objects/Rows.lean).

The book writes $d_0$ for `D.targetDim`, since $d$ is the prime of the parameters. Volume 1 writes $\dim$ of the target forms in words.

### Twisted lattices

**Definition (Twisted lattice).** A twisted lattice on a complex vector space $V$, with twists $\xi \in T$ and a trivial twist $1$, is a family of linear maps $\Theta_\xi$ from $V$ to inner product spaces, in each of them a module of vectors integral at each $\iota$, and coordinates on the space of $\Theta_1$ in which the inner product has a positive definite rational matrix. If $\xi$ is allowed at the prime of $\iota$, the product of a vector integral at $\bar\iota$ and a vector integral at $\iota$ is integral at $\iota$.

Lean: `New.TwistedLattice` (New/Reduction/Lattices/TwistedLattice.lean).

Here $\iota$ is a pair of a prime $\ell$ and a ring isomorphism $\mathbb{C} \to \bar{\mathbb{Q}}_\ell$, Lean's `New.PrimePadicIso`. The book writes $\bar{\mathbb{Q}}_\ell$ for the algebraic closure; Volume 1 writes it in two ways.

**Definition (Index, covolume and volume).** A family $y$ in $V$ has index at most $\delta$ if there are numbers $e(\ell) \geq 0$ with $\sum_\ell e(\ell) \log \ell \leq \delta$ such that for each $\iota$ above $\ell$ a matrix over the integers of $\bar{\mathbb{Q}}_\ell$ carries $y$ into the integral vectors with loss $e(\ell)$. It has covolume at most $c$ if $|\det(\langle \sigma\Theta_1 y_i, \sigma\Theta_1 y_k\rangle)| \leq e^c$ for every automorphism $\sigma$ of $\mathbb{C}$, with the product given by the rational matrix. The volume is $Z(\xi) = \det(\Theta_\xi^* \Theta_\xi)$.

Lean: `New.TwistedLattice.IndexLe` (New/Reduction/Lattices/TwistedLattice.lean), `New.TwistedLattice.CovolumeLe` (New/Reduction/Lattices/TwistedLattice.lean), `New.TwistedLattice.volume` (New/Reduction/Lattices/TwistedLattice.lean).

The book writes $e(\ell)$ for the local loss; Volume 1 also writes $\delta_\ell$. In this section $\sigma$ is an automorphism of $\mathbb{C}$, not a place. Lean defines the volume as the square of the determinant norm of $\Theta_\xi$ (Mathlib's `LinearMap.normDet`), with a value in $\mathbb{C}$.

**Definition (Height).** A family $y_\iota$ of complex numbers has height at most $c$ if there are $H \neq 0$, a real $\alpha$ and $h(\ell) \geq 0$ with $|\sigma H| \leq e^\alpha$ for all $\sigma$, $\|\iota(H y_\iota)\| \leq \ell^{h(\ell)}$ for all $\iota$ above $\ell$, and $\alpha + \sum_\ell h(\ell) \log \ell \leq c$.

Lean: `New.HeightLe` (New/Reduction/Lattices/Heights.lean).

**Definition (The lattice of target forms).** The target forms are a twisted lattice whose twists are the $m$-fold twists. The map at $\vartheta$ is the chain of lifts $\Theta_\vartheta$ to forms on $Y_m$, and $\vartheta$ is allowed at $\ell$ if the norm of its set $Q$ is prime to $\ell$.

Lean: `New.Data.targetLattice` (New/Reduction/IntegralTargetForms.lean).

### Normalizations

1. The inner product of Mathlib is conjugate linear in the first variable: $\langle u, v \rangle = \sum_i \bar u_i v_i$. The Gram matrix of a family is $(\langle v_i, v_k \rangle)$, Lean's `New.formGram` for a matrix.
2. On $\bar{\mathbb{Q}}_\ell$ the norm has $\|\ell\| = \ell^{-1}$.
3. The Fourier transform on matrices has no normalizing factor: $\hat f(\rho) = \sum_v f(v) \psi(\operatorname{tr}(\rho v))$.
4. The mean over a compact quotient $B/B_0$ is the integral for the Haar probability measure. The mean over $\mathbb{R}/\mathbb{Z}$ is the same.
5. The Gaussian measure on $\mathbb{C}^n$ is Lebesgue measure divided by $\pi^n$. With this measure, $\int \exp(-\bar x^{\top} A (x - a)) = (\det A)^{-1}$ for accretive $A$, by `New.Fock.integral_gauss`.
6. The Fourier transform on $\mathbb{R}^n$ and on $\mathbb{C}^n$ is Mathlib's, with the kernel $e^{-2\pi i \langle v, w \rangle}$.
7. The Haar measure on the finite adelic unitary group gives the standard level mass $1$, by `New.volume_stdLevel`.

Lean: `New.Exchange.matrixFourier` (Lib/General/Analysis/FiniteFourier.lean), `New.quotMean` (Lib/Adelic/QuotientMeasure/Basic.lean), `New.Fock.normalizedVolume` (Lib/General/Analysis/GaussianIntegral.lean).

**Remark (Formalization).** Lean defines the mean as $\int F(q^{\mathrm{out}})\,d\mu(q)$, with $q^{\mathrm{out}}$ a representative of the coset $q$ chosen by `choose`. The mean is the textbook mean when $F$ is invariant under $B_0$, since then the choice of representative does not change the value. If $F \circ \mathrm{out}$ is not integrable, the mean is $0$.
