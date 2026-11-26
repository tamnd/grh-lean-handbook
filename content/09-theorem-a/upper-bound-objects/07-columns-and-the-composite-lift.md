---
title: Columns and the composite lift
lean:
  - New/UpperBound/Objects/Columns.lean
decls:
  - New.Data.levelX
  - New.Data.principalLevel_le_levelX
  - New.Data.classAut_levelX_zero_eq_bot
  - New.Data.SourceForm
  - New.Data.IsBranchingMap
  - New.Data.branching
  - New.Data.restrictToY
  - New.Data.liftKernel
  - New.Data.translateDatum
  - New.Data.restrictedChain
  - New.Data.gluedDoubleLiftDatum
  - New.Data.gluedTensor
  - New.Data.IsChainDatum
  - New.Data.IsWeakChainDatum
  - New.Data.compositeLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Columns and the composite lift

This section builds the first of the two maps of the proof. A source form on $X_0$ is lifted $m$ times up the upper chain, with data that are translates of the integral vacuum, glued in pairs. The result is a form on $X_m$, and it is restricted to $Y_m$ by a branching matrix.

### A model case: one tuple

Take a single tuple $x = (x_j)$ of finite adelic translations, with coefficient $1$. Each $x_j$ is a matrix with rows $X_{j+1}$ and columns $X_j$. The datum of lift $j + 1$ is the integral vacuum of $\mathrm{Hom}(X_j, X_{j+1})$ moved by the Heisenberg operator of $x_j$. Group the $m$ data in $\varrho + 1$ pairs. Replace each pair $v_{2i} \otimes v_{2i+1}$ by its glued form, a sum of translates with simple poles above $N$. Lift $\varphi$ through the $\varrho + 1$ double lifts with these glued data, and restrict the result to $Y_m$. A general chain datum $\Psi$ is a finite combination of such tuples, with conditions on the coefficients.

### Levels and source forms

**Definition (Level of stage j).** The level $K_j$ on $X_j$ is the set of elements of the chosen level whose last row is congruent to $(0, \dots, 0, 1)$ modulo $\pi$, where $\pi\bar\pi = N$.

Lean: `New.Data.levelX` (New/UpperBound/Objects/Columns.lean).

**Lemma.** The principal congruence subgroup of level $\pi_M \pi$ lies in $K_j$. So $K_j$ is open, and it is a level.

Lean: `New.Data.principalLevel_le_levelX` (New/UpperBound/Objects/Columns.lean).

*Proof.* An element of level $\pi_M\pi$ has level $\pi_M$, so it lies in the chosen level by [the lemma of Section 6](/decl/New.Data.principalLevel_le_chosenLevel/). It has level $\pi$, so every row, and in particular the last one, is the row of the identity modulo $\pi$. $\square$

**Lemma.** The level $K_0$ is free.

Lean: `New.Data.classAut_levelX_zero_eq_bot` (New/UpperBound/Objects/Columns.lean).

*Proof.* $K_0$ lies in the chosen level, and $|X_0| = n_0 \le 2 n_m$. Apply [the freeness lemma](/decl/New.Data.classAut_eq_bot_of_le_chosenLevel/). $\square$

**Definition (Source forms).** A source form is an algebraic form on $X_0$ of weight $(\kappa, e_0)$, the column numbers of Section 3 and the determinant exponent $e_0$, that is fixed by $K_0$.

Lean: `New.Data.SourceForm` (New/UpperBound/Objects/Columns.lean).

### Restriction to Y_m

The index set of $Y_m$ is in bijection with $\mathrm{InitIndex}_m$ by a chosen bijection; the two sets have $n_m - 1$ elements (Section 1). This gives the embedding $h \mapsto \mathrm{diag}(h, 1)$ of $\mathrm{U}(Y_m)$ in $\mathrm{U}(X_m)$. The weight on $X_m$ and the weight on $Y_m$ interlace (Section 3), so by [the branching theorem](/decl/New.exists_branching_matrix/) of [integral Weyl modules and branching](/chapter/weyl-modules/) there is an integral branching matrix between their Weyl modules.

**Definition (Branching map).** An integer matrix $\mathrm{br}$ from the Weyl module of the weight on $X_m$ to that on $Y_m$ is a branching map if:

1. over every field $R$ of characteristic $0$, for $y = \mathrm{diag}(g, z)$, it carries the action of $y$ to $\prod_\tau z_\tau^{n_\tau}$ times the action of $g$, where $n_\tau$ is the sum of the entries of the weight on $X_m$ at $\tau$ less that of the weight on $Y_m$;
2. the square of its operator norm is at most $\exp(x^{70})$;
3. every complex matrix that is equivariant for the elements $\mathrm{diag}(g, 1)$, $g$ unitary, is a multiple of it.

Lean: `New.Data.IsBranchingMap` (New/UpperBound/Objects/Columns.lean).

**Definition (The branching matrix).** The matrix `branching` is a branching map, taken by choice from the existence statement.

Lean: `New.Data.branching` (New/UpperBound/Objects/Columns.lean).

The norm bound comes from a count of boxes: $l = f n_m^2 \Delta$ bounds the boxes, and the size conditions give $(l^l)^6 \le \exp(x^{70})$.

**Definition (Restriction to Y_m).** For a form $F$ on $X_m$, the form $\mathrm{res}\,F$ on $Y_m$ is
$$(\mathrm{res}\,F)(h) = \prod_\tau \tau(\bar\pi)^{-n_\tau} \cdot \mathrm{br}\big(F(\mathrm{diag}(h, 1))\big).$$
Here $\tau$ runs over the infinite places, read as embeddings of the CM type.

Lean: `New.Data.restrictToY` (New/UpperBound/Objects/Columns.lean).

The form $\mathrm{res}\,F$ is smooth, because $h \mapsto \mathrm{diag}(h,1)$ is continuous. It transforms correctly under the rational points, because $\mathrm{br}$ intertwines $\mathrm{diag}(\gamma, 1)$ with $\gamma$, and the character $\prod_\tau z_\tau^{n_\tau}$ is $1$ at $z = 1$. The factor $\prod_\tau \tau(\bar\pi)^{-n_\tau}$ is a normalisation. [The chain valuation](/chapter/chain-valuation/) uses it.

### Kernels and data

**Definition (Lift kernel).** For a tame character $\vartheta$, the kernel of lift $j + 1$ is the theta kernel of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) from $X_j$ to $X_{j+1}$, with level $K_j$ on $X_j$. Its two characters are the twists by the ranks $n_j$ and $n_{j+1}$ of the chain character $\chi_{j+1}\vartheta^{j+1}$. Derivatives are scaled by $\pi_M$ times the period $P.\mathrm{jetScale}$.

Lean: `New.Data.liftKernel` (New/UpperBound/Objects/Columns.lean).

The weight $(\kappa, e_j)$ to $(\kappa, e_{j+1})$ is a lift weight in the sense of that chapter: $n_j < n_{j+1}$, no column has a height strictly between them, and $e_j$ is the exponent $\lfloor n_{j+1}/2 \rfloor - \kappa_{j+1}$ plus the number of columns of height $n_j$.

**Definition (Translated datum).** For a tuple $x$ of translations, the $j$-th datum is the normalised integral vacuum of $\mathrm{Hom}(X_j, X_{j+1})$, of [the integral vacuum](/chapter/integral-vacuum/), translated by the finite Heisenberg operator of $x_j$.

Lean: `New.Data.translateDatum` (New/UpperBound/Objects/Columns.lean).

**Definition (Restricted chain).** For a finitely supported $\Psi$ on tuples of translations, the restricted chain is $\varphi \mapsto \mathrm{res}\big(\sum_x \Psi(x)\, \mathrm{chain}(\text{translated data of } x)_m \varphi\big)$.

Lean: `New.Data.restrictedChain` (New/UpperBound/Objects/Columns.lean).

**Definition (Glued datum).** For data $v_j$, the glued datum of the double lift $X_{2i} \to X_{2i+1} \to X_{2i+2}$ is the sum `doubleLiftGluing` of translates of $v_{2i} \otimes v_{2i+1}$, with simple poles at the places $w \mid \pi$ in the first factor and at their conjugates in the second.

Lean: `New.Data.gluedDoubleLiftDatum` (New/UpperBound/Objects/Columns.lean).

**Definition (Glued tensor).** The glued tensor of $\Psi$ is $\sum_x \Psi(x) \bigotimes_{i \le \varrho} \mathrm{Glue}(v_{x,2i} \otimes v_{x,2i+1})$, where $v_{x,j}$ is the translated datum.

Lean: `New.Data.gluedTensor` (New/UpperBound/Objects/Columns.lean).

### Chain data and the composite lift

The conditions on $\Psi$ use a notion from [the first seesaw identity](/chapter/seesaw-identity-1/). Its file comes later in the order of the volume, but Columns.lean imports it, because the conditions on a chain datum are stated through it. That chapter uses the objects of this one, so this chapter states the notion here once.

**Definition (Admissible coefficients).** Let $A$ be a set, $n, d$ natural numbers, $p$ a proposition and $B$ a real number. A finitely supported $r : X \to \mathbb{C}$ has admissible coefficients if its support lies in $A$, every $d \cdot r(x)$ is integral away from $n$, and, if $p$ holds, $\sum_x |\sigma(r(x))| \le B$ for every field automorphism $\sigma$ of $\mathbb{C}$. Here $z$ is integral away from $n$ if $|\iota(z)| \le 1$ for every prime $l$ prime to $n$ and every ring homomorphism $\iota : \mathbb{C} \to \mathbb{C}_l$.

Lean: `New.Seesaw.IsAdmissibleCoeffs` (New/UpperBound/Seesaw/AdmissibleCombinations.lean).

**Definition (Chain datum).** Let $\vartheta$ be a twist with set of places $Q$, and let $q$ be the product of the norms of the places of $Q$. Then $\Psi$ is a chain datum for $\vartheta$ if:

1. it has admissible coefficients with $A$ the set of tuples $x$ such that $\bar\pi_M x_j$ is integral at the places prime to $q$ and $x_j$ vanishes at the places prime to $Mq$, with $n = q$, $d = 1$, $p$ the statement $Q = \emptyset$, and $B = M^{3 f m n_m^2}$;
2. the glued tensor of $\Psi$ is fixed by $K_0 \times \dots \times K_{m-1}$, with the identity on $X_m$, under the Weil actions for $\vartheta$.

Lean: `New.Data.IsChainDatum` (New/UpperBound/Objects/Columns.lean).

**Definition (Weak chain datum).** $\Psi$ is a weak chain datum for $\vartheta$ if it has admissible coefficients with $A$ the tuples for which $\bar\pi_M x_j$ is integral at the places prime to $qN$, with $n = q$, $d = 1$, $p$ the statement $Q = \emptyset$ and $B = \exp(x^{60})$, and if the plain family $(\Psi(x), \text{translated data of } x)$ is jointly invariant at stage $m$ in the sense of Section 6.

Lean: `New.Data.IsWeakChainDatum` (New/UpperBound/Objects/Columns.lean).

**Definition (Composite lift).** For a tame character $\vartheta$, a finitely supported $\Psi$ and a source form $\varphi$, the composite lift $B_{\vartheta,\Psi}\varphi$ is the chain of $\varrho + 1$ double lifts of $\varphi$ with the glued tensor of $\Psi$ as data, followed by restriction to $Y_m$.

Lean: `New.Data.compositeLift` (New/UpperBound/Objects/Columns.lean).

The proof expands a glued tensor into plain translates in [the chain valuation](/chapter/chain-valuation/): for a chain datum $\Psi$, there is a weak chain datum $\Psi'$ whose restricted chain is the composite lift of $\Psi$. Then the proposition of Section 6 applies to $\Psi'$.

**Remark (Formalization).** Several objects here are choices. The matrix `branching` is taken by `Exists.choose`, so no particular branching map is fixed; property 3 says that any two differ by a scalar. The bijection `lastIndexEquiv` is `Fintype.equivOfCardEq`, which is not canonical. The composite lift lands on $X_{2\varrho+2}$, and Lean must transport it to $X_m$ along the proof of $m = 2\varrho + 2$; this is the map `restrictToYOfEq`. The zero function is a chain datum: its support is empty, $0$ is integral, $0 \le B$, and the zero tensor is invariant. Its composite lift is $0$. So the definition alone does not give a nonzero composite lift. The seesaw identity of [the first seesaw identity](/chapter/seesaw-identity-1/) gives, for every twist, a chain datum whose composite lift is a unit multiple of the lower chain of the Poincaré image. The research notes on the source record that this identity may hold with both sides $0$. The nonvanishing that the argument needs comes from other results, which later chapters treat.
