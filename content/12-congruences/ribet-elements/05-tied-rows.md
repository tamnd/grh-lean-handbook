---
title: Tied rows
lean:
  - New/Congruences/FirstOrder/RibetMatrices.lean
  - New/Congruences/FirstOrder/FittingBlock.lean
decls:
  - New.Selmer.polyAction
  - New.Selmer.polyAction_single
  - New.Selmer.polyAction_aeval
  - New.Selmer.polyChar
  - New.Selmer.polyChar_single
  - New.Selmer.polyActionAtZero
  - New.Selmer.polyActionAtZero_single
  - New.Selmer.polyActionAtZero_X_smul
  - New.Selmer.C_algebraMap_trace
  - New.Selmer.coordRows
  - New.Selmer.coordRows_apply
  - New.Selmer.polyChar_coordRows
  - New.Selmer.polyActionAtZero_coordRows
  - New.Selmer.rowValue
  - New.Selmer.rowValue_apply
  - New.Selmer.evalRowAtChar
  - New.Selmer.evalRowAtChar_apply
  - New.Selmer.ribetGenerators
  - New.Selmer.AreCoordinates
  - New.Selmer.polyAction_rowValue_coordRows
  - New.Selmer.polyAction_rowValue_coordRows_of_areCoordinates
  - New.Selmer.rowValue_mem_augmentationIdeal
  - New.Selmer.augmentationIdeal
  - New.Selmer.tieIdeal
  - New.Selmer.ker_le_tieIdeal
  - New.Selmer.map_augmentationIdeal_le_tieIdeal
  - New.Selmer.tie_mem_tieIdeal
  - New.Selmer.mul_mem_tieIdeal
  - New.Selmer.tiedRows
  - New.Selmer.mem_tiedRows
  - New.Selmer.mem_tiedRows_of_forall_eq_zero
  - New.Selmer.coordRows_cocycle_mem_tiedRows
  - New.Selmer.coordRows_gen_sub_single_mem_tiedRows
  - New.Selmer.coordRows_linearCombination_mem_tiedRows
  - New.Selmer.smul_mem_tiedRows
  - New.Selmer.coordRows_tau_sub_mem_tiedRows
  - New.Selmer.normaliserRow
  - New.Selmer.tiedNormaliser
  - New.Selmer.polyAction_rowValue_normaliserRow
  - New.Selmer.sub_one_smul_normaliserRow_mem_tiedRows
  - New.Selmer.single_mem_tiedRows
  - New.Selmer.IsTraceIdeal
  - New.Selmer.traceLeftIdeal
  - New.Selmer.mem_traceLeftIdeal_of_forall
  - New.Selmer.smul_one_mem_traceLeftIdeal
  - New.Selmer.tie_mem_traceLeftIdeal
  - New.Selmer.tieIdeal_le
  - New.Selmer.exists_mem_tiedRows_polyActionAtZero_eq
  - New.Selmer.coboundary_eq_zero_of_apply_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tied rows

The theorem of [Ribet's method for tied rows](/chapter/ribet-elements/#ribets-method-for-tied-rows) takes a square matrix of tied rows as given. This section makes the rows concrete.

### The set-up

Let $O$ be a commutative ring and $G$ a group. For each $x$ in a set $Y$, let $u_x : G \to M_\sigma(O)$ be a matrix representation. Let $J$ be a set of variables, and let $R = O[X_j : j \in J]$. Each pair $k = (j, b)$ with $j \in J$ and $b \in \{\mathrm{true}, \mathrm{false}\}$ carries two group elements $\tau_k$ and $\varphi_k$. Each $j$ carries a polynomial $\varepsilon_j \in O[X]$. Fix an element $p \in O$.

In the application, $\tau_{(j, \mathrm{true})}$ is a tame generator at a new place $j$, and $\varphi_{(j, \mathrm{true})}$ is a Frobenius element at $j$. The elements $\tau_{(j, \mathrm{false})}$ and $\varphi_{(j, \mathrm{false})}$ are the inverses of their conjugates. The element $p$ is a power $\ell^\nu$. See [The chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) for the role of these choices.

### The actions of the group algebra

The group algebra $R[G]$ acts through each representation and each character over $O$.

**Definition (Actions of $R[G]$).** For a representation $\rho : G \to M_n(O)$, let $\tilde\rho : R[G] \to M_n(R)$ be the map of $R$-algebras with $\tilde\rho(g) = \rho(g)$. For a character $\xi : G \to O^\times$, let $\tilde\xi : R[G] \to R$ be the map of $R$-algebras with $\tilde\xi(g) = \xi(g)$. Let $\tilde\rho_0 : R[G] \to M_n(O)$ be $\tilde\rho$ followed by the substitution $X_j = 0$ for all $j$. This is a map of $O$-algebras.

Lean: `New.Selmer.polyAction`, `New.Selmer.polyChar`, `New.Selmer.polyActionAtZero` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Lemma.** Let $c \in R$, $g \in G$, $P \in O[X]$ and $w \in R[G]$. Then:

1. $\tilde\rho(c\,g) = c\,\rho(g)$ and $\tilde\rho(P(g)) = P(\rho(g))$;
2. $\tilde\xi(c\,g) = c\,\xi(g)$;
3. $\tilde\rho_0(g) = \rho(g)$ and $\tilde\rho_0(X_j w) = 0$;
4. for a matrix $A$ over $O$, the trace of $A$ read in $R$ is the trace of the image of $A$ in $M_n(R)$.

Lean: `New.Selmer.polyAction_single`, `New.Selmer.polyAction_aeval`, `New.Selmer.polyChar_single`, `New.Selmer.polyActionAtZero_single`, `New.Selmer.polyActionAtZero_X_smul`, `New.Selmer.C_algebraMap_trace` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Statements 1 and 2 hold on the basis elements $g$ by the definition, and both maps are $R$-linear. The map $\tilde\rho$ is a ring map, so it commutes with the evaluation of $P$. For 3, the substitution $X_j = 0$ fixes the constants and kills $X_j$. Statement 4 holds because the trace is a sum of diagonal entries, and the map $O \to R$ is additive. $\square$

### Rows and their values

Rows are vectors over $R[G]$, indexed by a finite set $\iota$. A family of generators $\mathrm{gen} : \iota \to G$ turns a row into one element of $R[G]$.

**Definition (Row value).** For a row $r \in R[G]^\iota$, its value is $\langle r \rangle = \sum_{i \in \iota} r_i(\mathrm{gen}_i - 1)$. For a vector $m \in O^\iota$, its row is $\underline{m} = (m_i \cdot 1)_i$.

Lean: `New.Selmer.rowValue`, `New.Selmer.rowValue_apply`, `New.Selmer.coordRows`, `New.Selmer.coordRows_apply` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Definition (Coordinates).** The functions $z : G \to O^\iota$ are coordinates for $\mathrm{gen}$ if $u_x(g) - 1 = \sum_i z(g)_i\,(u_x(\mathrm{gen}_i) - 1)$ for all $g \in G$ and all $x \in Y$.

Lean: `New.Selmer.AreCoordinates` (New/Congruences/FirstOrder/RibetMatrices.lean).

In the application the index set is $\iota = W \sqcup s_0 \sqcup s$. Here $W$ indexes the tame generators $\delta_w$ at the old places, and $s_0$ and $s$ are finite subsets of $G$. The generators are the $\delta_w$, then the elements of $s_0$, then the elements of $s$.

**Definition (Ribet generators).** For $\delta : W \to G$ and finite sets $s_0, s \subseteq G$, the Ribet generators are the family on $W \sqcup s_0 \sqcup s$ that is $\delta$ on $W$ and the inclusion on $s_0$ and on $s$.

Lean: `New.Selmer.ribetGenerators` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Definition (Reading a row on a character).** For a character $\xi$ and a row $r$ on $W \sqcup \iota'$, let $\xi_*(r) \in R^{\iota'}$ be the vector $(\tilde\xi(r_i))_{i \in \iota'}$. It forgets the coordinates in $W$.

Lean: `New.Selmer.evalRowAtChar`, `New.Selmer.evalRowAtChar_apply` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Lemma.** Let $m \in O^\iota$, $g \in G$ and $r \in R[G]^\iota$. Then:

1. $\tilde\xi(\underline{m}_j) = m_j$ and $\tilde\rho_0(\underline{m}_j) = m_j \cdot 1$;
2. $\tilde u_x(\langle \underline{m} \rangle) = \sum_i m_i (u_x(\mathrm{gen}_i) - 1)$;
3. if $z$ are coordinates, then $\tilde u_x(\langle \underline{z(g)} \rangle) = u_x(g) - 1$;
4. $\langle r \rangle$ lies in the augmentation ideal, the kernel of the trivial character.

Lean: `New.Selmer.polyChar_coordRows`, `New.Selmer.polyActionAtZero_coordRows`, `New.Selmer.polyAction_rowValue_coordRows`, `New.Selmer.polyAction_rowValue_coordRows_of_areCoordinates`, `New.Selmer.rowValue_mem_augmentationIdeal` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Statement 1 holds as both maps send $1$ to $1$. For 2, apply $\tilde u_x$ term by term and use $\tilde u_x(m_i \cdot 1) = m_i$. Statement 3 is 2 with $m = z(g)$ and the definition of coordinates. For 4, the trivial character sends each $\mathrm{gen}_i - 1$ to $0$. $\square$

### The tie ideal

Write $I$ for the augmentation ideal of $R[G]$. All ideals here are left ideals of $R[G]$.

**Definition (Augmentation ideal).** $I$ is the kernel of $\tilde 1 : R[G] \to R$, the map of the trivial character.

Lean: `New.Selmer.augmentationIdeal` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Definition (Tie ideal).** Let $\rho_0 \in R[G]$. The tie ideal $\mathfrak{t}(\rho_0)$ is the left ideal spanned by four sets:

1. the elements $w$ with $\tilde u_x(w) = 0$ for all $x \in Y$;
2. the elements $w\,p$ with $w \in I$;
3. the ties $\tau_k - 1 - X_j\,\varepsilon_j(\varphi_k)(\varphi_k - 1)$ for $k = (j, b)$;
4. the elements $w\,\rho_0$ with $w \in I$.

Lean: `New.Selmer.tieIdeal`, `New.Selmer.ker_le_tieIdeal`, `New.Selmer.map_augmentationIdeal_le_tieIdeal`, `New.Selmer.tie_mem_tieIdeal`, `New.Selmer.mul_mem_tieIdeal` (New/Congruences/FirstOrder/RibetMatrices.lean).

The four lemmas on this Lean line say that each of the four sets lies in $\mathfrak{t}(\rho_0)$. The tie is the first order form of the local condition at $j$. To first order in $X_j$, it says that $\tau_k$ acts as $1 + X_j\,\varepsilon_j(\varphi_k)(\varphi_k - 1)$.

**Definition (Tied rows).** A row $r \in R[G]^\iota$ is tied for $\rho_0$ if $\langle r \rangle \in \mathfrak{t}(\rho_0)$. The tied rows form a left $R[G]$-submodule $N(\rho_0)$ of $R[G]^\iota$.

Lean: `New.Selmer.tiedRows`, `New.Selmer.mem_tiedRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

### The trace ideal

**Definition (Trace ideal hypothesis).** Let $S$ be an $O$-algebra of functions from $Y$ to $L[X_j]$, and let $\mathcal{J}$ be an $S$-module of such functions. Then $\mathcal{J}$ is a trace ideal for the $u_x$, $p$, the ties and $\varepsilon$ if:

1. $S$ contains the constant functions $X_j$;
2. $S$ contains the coefficients of the characteristic polynomials of the $u_x(g)$, as functions of $x$;
3. $\mathcal{J}$ contains $x \mapsto p \operatorname{tr} u_x(g)$ for every $g$;
4. $\mathcal{J}$ contains $x \mapsto \operatorname{tr}\big((u_x(\tau_k) - 1) u_x(g)\big) - X_j \operatorname{tr}\big(((X - 1)\varepsilon_j)(u_x(\varphi_k))\, u_x(g)\big)$ for every $g$ and $k = (j, b)$.

Lean: `New.Selmer.IsTraceIdeal` (New/Congruences/FirstOrder/FittingBlock.lean).

**Definition (Left trace ideal).** $\mathfrak{a}_0$ is the left ideal of $R[G]$ spanned by the $w$ with $x \mapsto \operatorname{tr}\big(\tilde u_x(w)\,u_x(g)\big)$ in $\mathcal{J}$ for every $g \in G$.

Lean: `New.Selmer.traceLeftIdeal`, `New.Selmer.mem_traceLeftIdeal_of_forall` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Proposition.** Suppose $\mathcal{J}$ is a trace ideal. Then $p \in \mathfrak{a}_0$, every tie lies in $\mathfrak{a}_0$, and $\mathfrak{t}(\rho_0) \subseteq \mathfrak{a}_0 + I\rho_0$.

Lean: `New.Selmer.smul_one_mem_traceLeftIdeal`, `New.Selmer.tie_mem_traceLeftIdeal`, `New.Selmer.tieIdeal_le` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* The trace of $\tilde u_x(p)\,u_x(g)$ is $p \operatorname{tr} u_x(g)$, which lies in $\mathcal{J}$ by 3. So $p \in \mathfrak{a}_0$. For a tie, $\tilde u_x$ of the tie times $u_x(g)$ has the trace of item 4, by the lemma on actions. So every tie lies in $\mathfrak{a}_0$. Now check the four sets of the tie ideal. An element $w$ that every $\tilde u_x$ kills has trace $0$ against every $g$, and $0 \in \mathcal{J}$. An element $w\,p$ with $w \in I$ lies in $\mathfrak{a}_0$, as $\mathfrak{a}_0$ is a left ideal and $p \in \mathfrak{a}_0$. The ties lie in $\mathfrak{a}_0$. The last set is $I\rho_0$. $\square$

So the value of each tied row is $b + m\rho_0$ with $b \in \mathfrak{a}_0$. This is the hypothesis on rows in Ribet's method. [The main lemma](/chapter/ribet-elements/#the-main-lemma) makes this step for whole matrices.

### Rows that are tied

A row whose value every $\tilde u_x$ kills is tied, by item 1 of the tie ideal.

**Lemma.** If $\tilde u_x(\langle r \rangle) = 0$ for all $x$, then $r \in N(\rho_0)$.

Lean: `New.Selmer.mem_tiedRows_of_forall_eq_zero` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* The value $\langle r \rangle$ lies in the first set of the tie ideal. $\square$

**Proposition (Tied rows from coordinates).** Let $z$ be coordinates for $\mathrm{gen}$, and let $\rho_0$ be any element. These rows are tied:

1. (cocycle rule) $\underline{z(gh) - z(g)} - g\,\underline{z(h)}$ for $g, h \in G$;
2. $\underline{z(\mathrm{gen}_i)} - e_i$, with $e_i$ the unit vector at $i$;
3. $\underline{\sum_g \theta_g z(g)}$, for a finite family $\theta$ in $O$ with $\sum_g \theta_g (u_x(g) - 1) = 0$ for all $x$;
4. $p\,r$ for every row $r$;
5. (ties) $\underline{z(\tau_k)} - X_j\,\varepsilon_j(\varphi_k)\,\underline{z(\varphi_k)}$ for $k = (j, b)$.

Lean: `New.Selmer.coordRows_cocycle_mem_tiedRows`, `New.Selmer.coordRows_gen_sub_single_mem_tiedRows`, `New.Selmer.coordRows_linearCombination_mem_tiedRows`, `New.Selmer.smul_mem_tiedRows`, `New.Selmer.coordRows_tau_sub_mem_tiedRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* For 1, by the lemma on rows the value acts under $\tilde u_x$ as $(u_x(gh) - 1) - (u_x(g) - 1) - u_x(g)(u_x(h) - 1)$, which is $0$. For 2, the value of $e_i$ is $\mathrm{gen}_i - 1$, and the value of $\underline{z(\mathrm{gen}_i)}$ acts as $u_x(\mathrm{gen}_i) - 1$. For 3, the value acts as $\sum_g \theta_g(u_x(g) - 1) = 0$. In these three cases the basic test applies. For 4, the value of $p\,r$ is $\langle r \rangle p$, as $p$ is central, and $\langle r \rangle \in I$. This lies in the second set. For 5, the value of $\underline{z(g)}$ is $g - 1$ plus an element $n_g$ that every $\tilde u_x$ kills. So the value of the row is the tie plus $n_{\tau_k} - X_j\,\varepsilon_j(\varphi_k)\,n_{\varphi_k}$. The first term lies in the third set, and the correction lies in the first set, as it is a left multiple of elements of that set. $\square$

### The normaliser

The element $\rho_0$ that the chapter uses depends on an element $\gamma$ that acts on the main summand as a scalar $y$ with $y - 1$ a unit, and on one more element $a$. Let $c_1 \in O$ and write $n = c_1(\gamma - 1)$.

**Definition (Tied normaliser).** $\rho_0 = n + (1 - n)(a - 1)$ in $R[G]$. Its row is $\nu = c_1\,\underline{z(\gamma)} + (1 - n)\,\underline{z(a)}$.

Lean: `New.Selmer.tiedNormaliser`, `New.Selmer.normaliserRow` (New/Congruences/FirstOrder/RibetMatrices.lean).

On the main summand, $\gamma$ acts as $y$ and $c_1(y - 1) = 1$, so $n$ acts as $1$ and $\rho_0$ acts as $1$. On a character $\xi$ with $\xi(\gamma) = 1$, $n$ acts as $0$ and $\rho_0$ acts as $\xi(a) - 1$. This is the shape that Ribet's method needs.

**Lemma.** Let $z$ be coordinates. Then $\tilde u_x(\langle \nu \rangle) = \tilde u_x(\rho_0)$ for all $x$, and $(g - 1)\,\nu$ is tied for $\rho_0$ for every $g \in G$.

Lean: `New.Selmer.polyAction_rowValue_normaliserRow`, `New.Selmer.sub_one_smul_normaliserRow_mem_tiedRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* By the lemma on rows, $\langle \underline{z(\gamma)} \rangle$ acts as $u_x(\gamma) - 1$ and $\langle \underline{z(a)} \rangle$ acts as $u_x(a) - 1$. So $\langle \nu \rangle$ acts as $c_1(u_x(\gamma) - 1) + (1 - \tilde u_x(n))(u_x(a) - 1) = \tilde u_x(\rho_0)$. Thus $\langle \nu \rangle = \rho_0 + n'$ with $n'$ killed by every $\tilde u_x$. The value of $(g - 1)\nu$ is $(g - 1)\rho_0 + (g - 1)n'$. The first term lies in $I\rho_0$, and the second in the first set of the tie ideal. $\square$

The old places give one more kind of row. Suppose the generators on $W$ are the $\delta_w$, and that a polynomial $o_w(X)(X - 1)$ kills $u_x(\delta_w)$ for all $x$.

**Lemma.** The row with the entry $o_w(\delta_w)$ at $w$ and $0$ elsewhere is tied.

Lean: `New.Selmer.single_mem_tiedRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Its value is $o_w(\delta_w)(\delta_w - 1)$, which acts under $\tilde u_x$ as $(o_w(X)(X - 1))(u_x(\delta_w)) = 0$. The basic test applies. $\square$

### The row of $\gamma$ at $X = 0$

The next lemma is the base of the block of the main summand. After the substitution $X_j = 0$, the row of $z(\gamma)$ becomes a tied row.

**Lemma.** Let $\rho : G \to M_r(O)$ be a representation with $\rho(\gamma) = y \cdot 1$ and $c_1(y - 1) = 1$. Let $z$ be coordinates. Then there is a row $t \in N(\rho_0)$ with $\tilde\rho_0(t_j) = \tilde\rho_0(\underline{z(\gamma)}_j)$ for every $j$.

Lean: `New.Selmer.exists_mem_tiedRows_polyActionAtZero_eq` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Take $t = (\gamma - 1)\nu$. It is tied by the lemma on the normaliser. Under $\tilde\rho_0$, $\gamma - 1$ acts as $(y - 1) \cdot 1$ and $1 - n$ acts as $1 - c_1(y - 1) = 0$. So $\tilde\rho_0(t_j) = (y - 1)c_1\,z(\gamma)_j \cdot 1 = z(\gamma)_j \cdot 1$. This is $\tilde\rho_0(\underline{z(\gamma)}_j)$ by the lemma on rows. $\square$

The element $\gamma$ also lets cocycles stand for classes.

**Lemma.** Let $\rho(\gamma) = y \cdot 1$ with $y - 1$ a unit, and let $m$ be a vector in a module over $O$. If $\rho(\gamma)m - m = 0$, then $\rho(g)m - m = 0$ for all $g$.

Lean: `New.Selmer.coboundary_eq_zero_of_apply_eq_zero` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* $\rho(\gamma)m - m = (y - 1)m$. As $y - 1$ is a unit, $m = 0$. So $\rho(g)m - m = 0$. $\square$

So a coboundary that vanishes at $\gamma$ is zero. This is why the modules of cocycles in the next section ask for $c(\gamma) = 0$.

**Remark (Formalization).** The rows are vectors over the noncommutative ring $R[G]$, and the ideals are left ideals, that is, submodules of $R[G]$ over itself. The value $\langle r \rangle$ puts the entries of $r$ on the left of $\mathrm{gen}_i - 1$. The map $\xi_*$ forgets the coordinates in $W$. The map $\tilde\rho_0$ is only $O$-linear, because the substitution $X_j = 0$ is not $R$-linear.
