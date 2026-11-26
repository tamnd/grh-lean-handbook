---
title: The neighbour lattice
lean:
  - New/UpperBound/Seesaw/NeighbourLattice.lean
decls:
  - New.Seesaw.selfOrConj
  - New.Seesaw.PairIndex
  - New.Seesaw.IsNeighbourVector
  - New.Seesaw.IsScalingAtM
  - New.Seesaw.neighbourAxis
  - New.Seesaw.neighbourScale
  - New.Seesaw.neighbourMatrix
  - New.Seesaw.neighbourCoeff
  - New.Seesaw.neighbourTranslation
  - New.Seesaw.neighbourUnitary
  - New.Seesaw.isNeighbourVector_col_neighbourMatrix
  - New.Seesaw.neighbourMatrix_mulVec
  - New.Seesaw.commute_neighbourMatrix_diagonal
  - New.Seesaw.scalingUnitary
  - New.Seesaw.vanishingAbove
  - New.Seesaw.latticeUnitary
  - New.Seesaw.neighbourLattice
  - New.Seesaw.awayLattice
  - New.Seesaw.AwayLatticeQuotient
  - New.Seesaw.exists_class_star_idem_mul_mem_iff
  - New.Seesaw.exists_add_neighbourTranslation_mem_iff
  - New.Seesaw.latticeUnitary_smul_of_mem_vanishingAbove
  - New.Seesaw.mem_neighbourLattice_iff_of_mem_vanishingAbove
  - New.Seesaw.awayLattice_le_weightedTranslations
  - New.Seesaw.card_awayLatticeQuotient_dvd
  - New.Seesaw.neighbourTranslation_mem_neighbourLattice
  - New.Seesaw.existsUnique_add_neighbourTranslation_mem
  - New.Seesaw.neighbourCosetRep
  - New.Seesaw.existsUnique_sub_neighbourCosetRep_mem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The neighbour lattice

This section builds a lattice of matrices and a set of representatives for it modulo its integral points. Section 4 shows that it is the zero term lattice of a pair of lifts. All statements here are about finite adeles. No form and no theta function appears.

### Setting

Let $X$, $X'$, $X''$ be finite sets. The rows are indexed by $\mathrm{PairIndex}(X, X'') = (X \sqcup \{e\}) \sqcup (X'' \sqcup \{e''\})$, the basis of $X^- \oplus X''$ in a pair of lifts. The two added indices are $e$ (`lastSource`) and $e''$ (`lastTarget`). The columns are indexed by $X'$. A matrix is a function on $\mathrm{PairIndex}(X, X'') \times X'$ with values in $\mathbb A_{\mathrm f}$, the finite adeles of the CM field $E$.

Lean: `New.Seesaw.PairIndex` (New/UpperBound/Seesaw/NeighbourLattice.lean).

Let $N$ be a prime, split as a set $P$ of places and its conjugate (the class `IsSplitLevel` of [lift laws modulo $N$](/chapter/upper-bound-objects/)). Let $\pi$ be split squarefree for $N$ at $P$ ([standard lattices](/chapter/seesaw-identity-1/)). So $N = \pi\bar\pi$, $\pi$ is a uniformiser at $P$ and a unit elsewhere. Let $j$ be the idempotent of $P$: the adele that is $1$ at $P$ and $0$ elsewhere. Its conjugate $\bar j$ is the idempotent of the conjugate places. Since $P$ and $\bar P$ are disjoint, $j\bar j = 0$. Let $\eta$ be the fixed unit of norm $-1$ (Lean: `New.Weil.normNegOne`), so $\bar\eta\eta = -1$ and $\eta$ is integral.

For $\beta$ an integral adele, `selfOrConj` $\beta$ is $\beta$ on the first block $X \sqcup \{e\}$ and $\bar\beta$ on the second block $X'' \sqcup \{e''\}$.

Lean: `New.Seesaw.selfOrConj`.

### The scalings

The lattice also has factors $\kappa$ on the rows, away from $N$. In the application, $\beta\bar\beta$ is the auxiliary level $M$ and $\delta$ generates the ideal $(\beta/\bar\beta)$.

**Definition (Scaling at $M$).** A family $\kappa$ of adeles on the rows is a scaling at $M$ for $(N, \beta, \delta)$ if:

1. $\delta\bar\delta = 1$;
2. $\delta = 1$ at every place above $N$;
3. $\beta$ is a unit at every place above $N$;
4. each $\kappa_b$ is $1$ or $\delta$;
5. $\bar\beta\kappa_b$ is integral for every $b$;
6. $\mathrm{selfOrConj}(\beta)_b\,\kappa_b$ is integral for every $b$.

Lean: `New.Seesaw.IsScalingAtM`.

So $\kappa_b\bar\kappa_b = 1$, and $\kappa_b = 1$ above $N$. In particular $j\kappa_b = j$ and $\bar j\kappa_b = \bar j$.

### The matrix $\gamma$

**Definition (The neighbour matrix).** Put

$$\rho = e + \bar\eta\bar j\, e'', \qquad A = j(\pi - 1) + \bar j(\bar\pi^{-1} - 1), \qquad \gamma = 1 + A\,\rho\rho^*.$$

The coefficient vector $c$ is $0$ off $\{e, e''\}$, with $c_e = A\pi^{-1}\bar j$ and $c_{e''} = A\pi^{-1}\eta j$. For residues $y : X' \to P \to \mathbb Z/N$, let $y/N$ be the adele that is $y_w/N$ at $w \in P$ and $0$ elsewhere (Lean: `New.residueOverN`). The translation $n(y)$ is the matrix with row $\eta\,\overline{y/N}$ at $e$, row $-\overline{y/N}$ at $e''$ and $0$ elsewhere.

Lean: `New.Seesaw.neighbourAxis`, `New.Seesaw.neighbourScale`, `New.Seesaw.neighbourMatrix`, `New.Seesaw.neighbourCoeff`, `New.Seesaw.neighbourTranslation`.

Here $\rho^*$ is the conjugate transpose, so $\rho^*x = x_e + \eta j\,x_{e''}$. Then $\gamma x = x + A(x_e + \eta j\,x_{e''})\rho$.

Lean: `New.Seesaw.neighbourMatrix_mulVec`.

The translation $n(y)$ is supported at the conjugate places $\bar P$, because $\overline{y/N}$ is.

**Proposition (The neighbour unitary).** $\rho^*\rho = 1$ and $\overline{(1 + A)}(1 + A) = 1$. So $\gamma$ is a finite point of the unitary group. It scales $\rho$ by $1 + A$, which is $\pi$ at $P$, $\bar\pi^{-1}$ at $\bar P$ and $1$ elsewhere, and it fixes the vectors orthogonal to $\rho$.

Lean: `New.Seesaw.neighbourUnitary`.

*Proof.* $\rho^*\rho = 1 + \eta j\,\bar\eta\bar j = 1$, since $j\bar j = 0$. Write $1 + A = j\pi + \bar j\bar\pi^{-1} + (1 - j - \bar j)$. Its conjugate is $\bar j\bar\pi + j\pi^{-1} + (1 - j - \bar j)$. The three idempotents are orthogonal, so the product is $j + \bar j + (1 - j - \bar j) = 1$. Then

$$\gamma^*\gamma = 1 + (A + \bar A + \bar A A\,\rho^*\rho)\rho\rho^* = 1 + \bigl(\overline{(1+A)}(1+A) - 1\bigr)\rho\rho^* = 1.$$

The other two claims follow from $\gamma x = x + A(\rho^*x)\rho$. $\square$

**Lemma (The columns of $\gamma$ are neighbour vectors).** For each row index $m$, let $x$ be column $m$ of $\gamma$ and $c = c_m$. Then:

1. $\delta c = c$;
2. $x_i$ is integral for $i \neq e, e''$;
3. $\bar\pi x_i$ is integral for every $i$;
4. $c - \pi^{-1}x_e$ is integral;
5. $\bar\eta c - \pi^{-1}x_{e''}$ is integral.

These five conditions define the predicate `IsNeighbourVector` $\pi\ \delta\ c\ x$.

Lean: `New.Seesaw.IsNeighbourVector`, `New.Seesaw.isNeighbourVector_col_neighbourMatrix`.

*Proof.* Column $m$ is $x_i = [i = m] + A\rho_i\bar\rho_m$. (1) $c$ has a factor $j$ or $\bar j$, and $\delta = 1$ above $N$. (2) For $i \neq e, e''$ we have $\rho_i = 0$, so $x_i = [i = m]$. (3) $\bar\pi$ is integral, and $\bar\pi A = j\bar\pi(\pi - 1) + \bar j(1 - \bar\pi)$ is integral. The entries of $\rho$ are integral. (4) and (5): put $\varpi' = j + (1 - j)\pi^{-1}$. It is integral, since $\pi$ is a unit off $P$. A direct computation with $j\bar j = 0$, $\bar j^2 = \bar j$ and $\bar\eta\eta = -1$ gives

$$c_m - \pi^{-1}x_e = -\varpi'[m = e], \qquad \bar\eta c_m - \pi^{-1}x_{e''} = -\varpi'[m = e''].$$

For example, if $m = e$ then $x_e = 1 + A$, and $A - A\bar j = j(\pi - 1)$. So $c_e - \pi^{-1}x_e = -\pi^{-1}(1 + j(\pi - 1)) = -\varpi'$. $\square$

**Lemma (γ commutes with κ).** $\gamma\,\mathrm{diag}(\kappa) = \mathrm{diag}(\kappa)\,\gamma$.

Lean: `New.Seesaw.commute_neighbourMatrix_diagonal`.

*Proof.* $A\kappa_b = A$ for every $b$, since $A$ is supported above $N$ and $\kappa_b = 1$ there. So both products have entries $[i = m]\kappa_m + A\rho_i\bar\rho_m$. $\square$

The diagonal matrix of $\kappa$ is unitary, since $\kappa\bar\kappa = 1$.

Lean: `New.Seesaw.scalingUnitary`.

### The lattice

**Definition (The neighbour lattice).** The lattice unitary is $(\gamma\,\mathrm{diag}\,\kappa)\otimes 1$, acting on matrices column by column. The neighbour lattice $L$ is the image of the integral matrices under it. The away lattice $L^\circ$ is the set of $x \in L$ that vanish at the places above $N$. The away quotient $Q$ is $L^\circ$ modulo its integral points.

Lean: `New.Seesaw.latticeUnitary`, `New.Seesaw.neighbourLattice`, `New.Seesaw.vanishingAbove`, `New.Seesaw.awayLattice`, `New.Seesaw.AwayLatticeQuotient`.

The quotient $Q$ is finite, since the integral points of $L$ have finite index in $L$.

**Lemma (The lattice away from $N$).** Let $x$ vanish above $N$. Then $(\gamma\kappa\otimes 1)x$ is the matrix with rows $\kappa_b x_b$. So $x \in L$ if and only if $\bar\kappa_b x_{b,a}$ is integral for all $b$ and $a$.

Lean: `New.Seesaw.latticeUnitary_smul_of_mem_vanishingAbove`, `New.Seesaw.mem_neighbourLattice_iff_of_mem_vanishingAbove`.

*Proof.* $A x_{b,a} = 0$, since $A$ is supported above $N$. So $\gamma$ acts trivially on $x$ and on $\kappa x$. For the second claim, $(\gamma\kappa\otimes 1)(\bar\kappa x) = x$, because $\kappa\bar\kappa = 1$. The lattice unitary is injective, so $x$ is the image of an integral matrix exactly when $\bar\kappa x$ is integral. $\square$

**Corollary (Weighted translations).** For every $n$, the away lattice lies in the weighted translations of $n$ with weights $\mathrm{selfOrConj}(\beta)$.

Lean: `New.Seesaw.awayLattice_le_weightedTranslations`.

*Proof.* Write $\mathrm{selfOrConj}(\beta)_b\,x_{b,a} = (\mathrm{selfOrConj}(\beta)_b\,\kappa_b)(\bar\kappa_b x_{b,a})$. The first factor is integral by condition (6) of the scaling, and the second by the lemma. So the product is integral at every place, in particular at those prime to $n$. $\square$

**Proposition (The order of the away quotient).** The order of $Q$ divides the number of matrices with entries in $\hat{\mathcal O}/(\beta)$.

Lean: `New.Seesaw.card_awayLatticeQuotient_dvd`.

*Proof.* For $x \in L^\circ$ the matrix $\bar\kappa x$ is integral. Send $x$ to the reduction of $\overline{\bar\kappa x}$ modulo $\beta$. This is an additive map. Let $x$ be in its kernel, so $\overline{\bar\kappa_b x_{b,a}} = \beta z$ with $z$ integral. Then $x_{b,a} = \kappa_b\bar\beta\bar z$, and this is integral by condition (5). So the kernel lies in the integral points. The order of $Q$ divides the index of the kernel, which is the order of the image. $\square$

### Above $N$

The translations $n(y)$ represent $L$ modulo integral points at the places above $N$. The key step is a statement about one adele.

**Lemma (One residue).** Let $t$ be a finite adele. There is $y_0 : P \to \mathbb Z/N$ such that, for every $y$, the adele $\bar j(\bar\pi^{-1}t + \eta\,\overline{y/N})$ is integral if and only if $\bar j t$ is integral and $y = y_0$.

Lean: `New.Seesaw.exists_class_star_idem_mul_mem_iff`.

*Proof.* The map $w \mapsto \eta\bar w$ preserves integrality in both directions, since $\eta$ is integral and $\eta\,\overline{\eta\bar w} = -w$. It carries $\bar j(\bar\pi^{-1}t + \eta\,\overline{y/N})$ to $j(z - y/N)$, where $z = \eta\pi^{-1}\bar t$. By [the residue lemma for split levels](/decl/New.IsSplitLevel.exists_sub_residueOverN_mem_iff/), there is $y_0$ such that $j(z - y/N)$ is integral exactly when $jNz$ is integral and $y = y_0$. Now $Nz = \eta\bar\pi\,\bar t$. At $P$ the idele $\bar\pi$ is a unit, since $\pi$ is a unit at $\bar P$. So $jNz$ is integral exactly when $j\bar t$ is integral, that is, when $\bar j t$ is integral. $\square$

**Lemma (Translations at the conjugate places).** For every matrix $x$ there is $y_0 : X' \to P \to \mathbb Z/N$ such that, for every $y$, the matrix $(\gamma\otimes 1)x + n(y)$ is integral at $\bar P$ if and only if $x$ is integral at $\bar P$ and $y = y_0$.

Lean: `New.Seesaw.exists_add_neighbourTranslation_mem_iff`.

*Proof.* Fix a column $a$ and write $x$ for that column. We have $\bar jA = \bar j(\bar\pi^{-1} - 1)$ and $\bar j\rho^*x = \bar jx_e$. At $\bar P$ the translation is $n(y) = \eta\,\overline{y/N}\,\rho$, since $\rho_{e''} = \bar\eta\bar j$ and $\bar\eta\eta = -1$. Hence

$$\bar j(\gamma x + n(y)) = \bar jx + \rho\bigl(\bar j(\bar\pi^{-1}x_e + \eta\,\overline{y_a/N}) - \bar jx_e\bigr).$$

Let $y_0(a)$ be the residue of the previous lemma for $t = x_e$. Suppose the left side is integral. Row $e$ of the right side is $\bar j(\bar\pi^{-1}x_e + \eta\,\overline{y_a/N})$, since $\rho_e = 1$. So it is integral, and the lemma gives that $\bar jx_e$ is integral and $y_a = y_0(a)$. The other rows of $\bar jx$ then differ from integral entries by integral multiples of $\rho$, so $\bar jx$ is integral. The converse is the same computation read backwards. $\square$

**Proposition (The translations lie in $L$).** $n(y) \in L$ for every $y$.

Lean: `New.Seesaw.neighbourTranslation_mem_neighbourLattice`.

*Proof.* Since $\gamma$ is invertible, write $-n(y) = (\gamma\otimes 1)x$. Then $(\gamma\otimes 1)x + n(y) = 0$ is integral, so $x$ is integral at $\bar P$ by the lemma. Put $x_0 = -\bar jx$, an integral matrix. Then $\kappa x_0 = x_0$, since $\bar j\kappa = \bar j$. As $\gamma$ is linear, $(\gamma\kappa\otimes 1)x_0 = -\bar j(\gamma\otimes 1)x = \bar j\,n(y) = n(y)$. $\square$

**Proposition (One translation for each element above $N$).** For each $x \in L$ there is exactly one $y$ such that $x + n(y)$ is integral at all places above $N$.

Lean: `New.Seesaw.existsUnique_add_neighbourTranslation_mem`.

*Proof.* Write $x = (\gamma\otimes 1)z$ with $z = \kappa x_0$ and $x_0$ integral. Above $N$ we have $\kappa = 1$, so $z$ is integral there. At $P$, $n(y)$ vanishes and $jA = j(\pi - 1)$ is integral, so $j(x + n(y))$ is integral for every $y$. At $\bar P$, the previous lemma applies to $z$: since $z$ is integral at $\bar P$, $x + n(y)$ is integral there for exactly one $y$. $\square$

### Coset representatives

**Definition (Coset representatives).** For $y : X' \to P \to \mathbb Z/N$ and $q \in Q$, put $r(y, q) = n(y) + \tilde q$, where $\tilde q \in L^\circ$ is the chosen representative of $q$.

Lean: `New.Seesaw.neighbourCosetRep`.

The representative $\tilde q$ is a `Quotient.out` choice. Any other choice gives a representative that differs by an integral matrix, so nothing below depends on it.

**Theorem (Coset representatives of the neighbour lattice).** Each $r(y, q)$ lies in $L$. Each $z \in L$ differs from $r(y, q)$ by an integral matrix for exactly one pair $(y, q)$.

Lean: `New.Seesaw.neighbourCosetRep_mem_neighbourLattice`, `New.Seesaw.existsUnique_sub_neighbourCosetRep_mem`.

*Proof.* The first claim holds since $n(y) \in L$ and $\tilde q \in L^\circ \subseteq L$. For the second, let $\epsilon$ be the idempotent of the places above $N$. $L$ is stable under multiplication by integral adeles, since the lattice unitary is linear. So $\epsilon z \in L$, and $z' = z - \epsilon z$ lies in $L^\circ$. By the previous proposition applied to $-z$, there is exactly one $y_0$ such that $\epsilon(-z + n(y_0))$ is integral. Now $\epsilon\,n(y) = n(y)$ and $\epsilon\tilde q = 0$, so

$$z - r(y, q) = -\epsilon\bigl(-z + n(y)\bigr) + \bigl(z' - \tilde q\bigr).$$

The first term is supported above $N$ and the second vanishes there. So the sum is integral exactly when both terms are. The first term is integral exactly when $y = y_0$. The second is integral exactly when $q$ is the class of $z'$. $\square$

So $L$ modulo its integral points is in bijection with $(X' \to P \to \mathbb Z/N) \times Q$. The first factor has $N^{|X'||P|}$ elements and lives above $N$. The second lives at the places of $\beta$.

### Example: rank two

Let $X = X'' = \emptyset$ and $X' = \{a\}$, so the matrices are vectors with entries at $e$ and $e''$. Let $\kappa = 1$. Fix a place $w \in P$.

At $w$, $\rho = e$ and $A = \pi - 1$. So $\gamma$ multiplies the $e$ entry by $\pi$ and fixes the $e''$ entry. The lattice $L_w$ is $\pi\mathcal O_w \oplus \mathcal O_w$.

At $\bar w$, $\rho = e + \bar\eta e''$ and $\rho^*x = x_e$ there, because $j(\bar w) = 0$. So $\gamma e'' = e''$ and $\gamma e = \bar\pi^{-1}e + (\bar\pi^{-1} - 1)\bar\eta e''$. Modulo integral vectors, $\gamma e \equiv \bar\pi^{-1}(e + \bar\eta e'')$. Since $\pi$ is a unit at $\bar w$, $\bar\pi^{-1} = \pi/N$ there. So $L_{\bar w}$ modulo $\mathcal O_{\bar w}^2$ is the set of classes of $(k/N)\rho$, $k \in \mathbb Z/N$. The translation $n(y)$ is $\eta\,\overline{y/N}\,\rho$ there, which runs over the same classes. This is the local picture of the model case of Section 1: the lattice shrinks at $w$, grows at $\bar w$, and $L/(L \cap \hat{\mathcal O}^2)$ has $N$ elements per place of $P$.
