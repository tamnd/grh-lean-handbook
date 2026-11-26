---
title: Glued lattices
lean:
  - New/OneLift/ComparisonOperator/GluedLattices.lean
decls:
  - New.Rows.DividedSplitting.stackOverGenScalar
  - New.Rows.rowFixingLevel
  - New.Rows.rowFixingLevel_le_levelOf
  - New.Rows.DividedSplitting.IsBlockNormalised
  - New.Rows.DividedSplitting.IsGlued
  - New.Rows.DividedSplitting.IsGlued.indicator_eq_sum
  - New.Rows.DividedSplitting.glueMatrix
  - New.Rows.DividedSplitting.isBlockNormalised_iff
  - New.Rows.DividedSplitting.reducedInverse_mul_eq_iff
  - New.Rows.DividedSplitting.mul_congruenceGroup_eq_smul_iff
  - New.Rows.DividedSplitting.isBlockNormalised_mul_iff
  - New.Rows.DividedSplitting.exists_divisor_assoc_stackOverGenScalar
  - New.Rows.DividedSplitting.exists_genResidue_mul_stackOverGenScalar_eq_zero
  - New.Rows.DividedSplitting.exists_mul_glueMatrix_eq
  - New.Rows.DividedSplitting.exists_isGlued
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Glued lattices

Fix a divided splitting $V$ of $O$ with $\varepsilon : N \sqcup m \simeq n$, $e = \mathrm{fixedEmb} : r \hookrightarrow N$ and $z : r \hookrightarrow m$ (see [Section 2](/chapter/comparison-operator-1/#divided-lattices)). Fix an $a \times N$ matrix $s$ modulo $\varpi^2$. The rows of $s$ are linear forms on $V''$ on which we impose a finer congruence. We now find a divided lattice $\gamma$ on which the congruence $\gamma^{-1}x \equiv (1;0)$ modulo $\varpi$ becomes two conditions, one on each block of $x$.

### The block conditions

**Definition (Stacked rows).** Let $w_s$ be the $(a \sqcup N) \times N$ matrix modulo $\varpi^2$ that has the rows of $s$ above the rows of $\bar\varpi\cdot 1$.

Lean: `New.Rows.DividedSplitting.stackOverGenScalar` (New/OneLift/ComparisonOperator/GluedLattices.lean).

So $w_s X = w_s X'$ says $sX \equiv sX'$ modulo $\varpi^2$ and $X \equiv X'$ modulo $\varpi$.

**Definition (Row fixing level).** For a $c \times m$ matrix $w$ modulo $\varpi^2$ and $e : r \hookrightarrow m$, the *row fixing level* is the group of $k \in K_0$ whose reduction modulo $\varpi^2 Q$ has the columns of the identity off $e$, and whose reduction $A$ modulo $\varpi^2$ has $wA = w$.

Lean: `New.Rows.rowFixingLevel` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Lemma (The row fixing level is small).** For every $s$, the row fixing level of $w_s$ and $e$ in $U(N)$ lies in the level $\mathrm{levelOf}(w_i, \bot)$ of the points that reduce to $1$ at every chosen place.

Lean: `New.Rows.rowFixingLevel_le_levelOf` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Let $k$ be in the row fixing level and let $A$ be its reduction. The lower rows of $w_s$ are $\bar\varpi 1$, and $w_sA = w_s$ gives $\bar\varpi A = \bar\varpi 1$. By the lemma on multiplication by $\varpi$ of Section 2, with $u = \mathrm{id}$, the matrix $k$ reduces to $1$ at every chosen place. $\square$

**Definition (Block normalised).** An $n \times r$ matrix $x$ modulo $\varpi^2$ is *block normalised* for $s$ if two conditions hold:

1. its block on $V^\circ$ is $\iota_z$: $x_{\varepsilon(\mathrm{inr}\,\cdot)} = \iota_z$;
2. its block $u = x_{\varepsilon(\mathrm{inl}\,\cdot)}$ on $V''$ satisfies $w_s u = w_s\iota_e$.

Lean: `New.Rows.DividedSplitting.IsBlockNormalised` (New/OneLift/ComparisonOperator/GluedLattices.lean).

Condition 2 says that $u \in \iota_e + \varpi L''_s$ with $L''_s = \{u : su \equiv 0 \text{ modulo } \varpi\}$. Both conditions are of the kind that a product datum on $V'' \oplus V^\circ$ can impose.

**Definition (Glued lattice).** A divided lattice $L$ with point $\gamma$ is *glued* for $s$ if three things hold.

1. If $\bar G_L x = \bar\varpi\,\iota_{O.\mathrm{incl}}$, then there is exactly one $Y \in \Gamma$ such that $xY$ is block normalised.
2. Conversely, if $xY$ is block normalised for some $Y \in \Gamma$, then $\bar G_L x = \bar\varpi\,\iota_{O.\mathrm{incl}}$.
3. Some $K \in \mathrm{GL}_N$ modulo $\varpi^2$ has $\bar\varpi\,(\bar G_L|_{V''}K)_{xy} = 0$ for all $x \in n$ and all $y \in N$ outside the range of $\mathrm{dividedEmb}$. Here $\bar G_L|_{V''}$ is the matrix of the columns $\varepsilon(\mathrm{inl}\,\cdot)$ of $\bar G_L$.

Lean: `New.Rows.DividedSplitting.IsGlued` (New/OneLift/ComparisonOperator/GluedLattices.lean).

Recall that $\bar G_L x = \bar\varpi\,\iota_{O.\mathrm{incl}}$ is the congruence $\gamma^{-1}x \equiv (1;0)$ modulo $\varpi$, multiplied by $\varpi$. Property 3 says that, after a change of basis of $V''$, the vectors of $V''$ outside $\mathrm{dividedEmb}$ are not divided: $\gamma^{-1}$ is integral on them. It controls the denominator in Section 4.

**Lemma (The indicator as a sum).** Let $L$ be glued for $s$. For every $x$ and $c \in \mathbb{C}$,
$$[\bar G_L x = \bar\varpi\,\iota_{O.\mathrm{incl}}]\,c = \sum_{Y \in \Gamma}[xY \text{ is block normalised}]\,c.$$

Lean: `New.Rows.DividedSplitting.IsGlued.indicator_eq_sum` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* If the congruence holds, property 1 gives a unique $Y$ with $xY$ block normalised, so the sum has exactly one term $c$. If it fails, property 2 shows that no $xY$ is block normalised, so the sum is $0$. $\square$

### The glue matrix

We construct $\gamma$ through $\varpi\gamma^{-1}$, by the lemma on divided lattices with a given reduced inverse of Section 2.

**Definition (Glue matrix).** For $e : r \hookrightarrow N$ and an integral $N \times N$ matrix $D$, the *glue matrix* is
$$G_D = \begin{pmatrix} D & -D\iota_e\iota_z^{T} \\ 0 & \Delta \end{pmatrix},\qquad \Delta = \mathrm{diag}(\varpi \text{ on } z(r),\ 1 \text{ elsewhere}).$$

Lean: `New.Rows.DividedSplitting.glueMatrix` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Lemma (Block normalised through the glue matrix).** Suppose that $w_sX = w_sX'$ if and only if $\bar DX = \bar DX'$, for all $N \times r$ matrices $X$, $X'$ modulo $\varpi^2$. Then $x$ is block normalised if and only if $x_{\varepsilon(\mathrm{inr}(z\,\cdot))} = 1$ and $\bar G_D\,x_{\varepsilon(\cdot)} = \bar\varpi\,\iota_{\mathrm{inr}\circ z}$.

Lean: `New.Rows.DividedSplitting.isBlockNormalised_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Write $x_{\varepsilon(\cdot)} = (u; v)$ with $u$ on $N$ and $v$ on $m$. Then $\iota_z^Tv = v_z$, the rows $z$ of $v$, and
$$\bar G_D\begin{pmatrix}u\\ v\end{pmatrix} = \begin{pmatrix}\bar Du - \bar D\iota_e v_z \\ \bar\Delta v\end{pmatrix}.$$
The target $\bar\varpi\,\iota_{\mathrm{inr}\circ z}$ is $(0; \bar\varpi\iota_z)$. Suppose $v_z = 1$. The top block says $\bar Du = \bar D\iota_e$, which is $w_su = w_s\iota_e$ by the hypothesis. The bottom block says $\bar\varpi v_{z(i)} = \bar\varpi e_i$ in the rows $z(i)$, which holds as $v_z = 1$, and $v_k = 0$ in the other rows $k$. So under $v_z = 1$ the bottom block says $v = \iota_z$. Conversely $v = \iota_z$ gives $v_z = 1$. $\square$

**Lemma (Reordering the rows).** Let $\varepsilon' : N \sqcup m \simeq n$ with $\varepsilon'(\mathrm{inr}(z\,i)) = O.\mathrm{incl}\,i$, and let $\bar G_L$ be the reduction of an integral $G$ with rows ordered by $\varepsilon'$ and columns ordered by $\varepsilon$. Then $\bar G_Lx = \bar\varpi\,\iota_{O.\mathrm{incl}}$ if and only if $\bar G\,x_{\varepsilon(\cdot)} = \bar\varpi\,\iota_{\mathrm{inr}\circ z}$.

Lean: `New.Rows.DividedSplitting.reducedInverse_mul_eq_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Reindex both sides by $\varepsilon'^{-1}$ in the rows. This is a bijection on matrices. The left side becomes $\bar G\,x_{\varepsilon(\cdot)}$, as the sum over $n$ is a sum over $N \sqcup m$ through $\varepsilon$. The inclusion matrix of $O.\mathrm{incl}$ becomes that of $\mathrm{inr}\circ z$, by the hypothesis on $\varepsilon'$. $\square$

**Lemma (Right multiplication by $\Gamma$).** For $A$, $B$ of size $n \times r$ and $Y \in \Gamma$, $AY = \bar\varpi B$ if and only if $A = \bar\varpi B$.

Lean: `New.Rows.DividedSplitting.mul_congruenceGroup_eq_smul_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* As $\bar\varpi Y = \bar\varpi 1$, we have $\bar\varpi BY = \bar\varpi B$. So $AY = \bar\varpi B$ says $AY = (\bar\varpi B)Y$. Cancel the invertible $Y$. $\square$

**Lemma (Translates by $\Gamma$).** Let $D$ be as in the lemma on the glue matrix, let $\varepsilon'$ be as in the lemma on reordering, and let $\bar G_L$ be the reduction of $G_D$ reordered by $\varepsilon'$ and $\varepsilon$. For $Y \in \Gamma$, the matrix $xY$ is block normalised if and only if $x_{\varepsilon(\mathrm{inr}(z\,\cdot))} = Y^{-1}$ and $\bar G_Lx = \bar\varpi\,\iota_{O.\mathrm{incl}}$.

Lean: `New.Rows.DividedSplitting.isBlockNormalised_mul_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The rows $z$ of $xY$ are $x_{\varepsilon(\mathrm{inr}(z\,\cdot))}Y$, and they are $1$ exactly when $x_{\varepsilon(\mathrm{inr}(z\,\cdot))} = Y^{-1}$. By the lemma on the glue matrix, the second condition for $xY$ is $\bar G_D(xY)_{\varepsilon(\cdot)} = \bar\varpi\,\iota_{\mathrm{inr}\circ z}$. By reordering it is $\bar G_L xY = \bar\varpi\,\iota_{O.\mathrm{incl}}$. By right multiplication by $\Gamma$ it is $\bar G_Lx = \bar\varpi\,\iota_{O.\mathrm{incl}}$. $\square$

### The construction

**Lemma (A divisor for the stacked rows).** There are integral $N \times N$ matrices $B$, $D$ and matrices $P$, $Q$ modulo $\varpi^2$ with $BD = \varpi\cdot 1$, $w_s = P\bar D$ and $\bar D = Qw_s$.

Lean: `New.Rows.DividedSplitting.exists_divisor_assoc_stackOverGenScalar` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Lift $s$ to an integral matrix $t$. The ring $\hat{\mathcal{O}}$ of integral finite adeles has Hermite forms: there is an invertible $U$ over $\hat{\mathcal{O}}$ and an $N \times N$ matrix $D$ with
$$\begin{pmatrix} t \\ \varpi 1\end{pmatrix} = U\begin{pmatrix}0\\ D\end{pmatrix},\qquad D = (U^{-1})_{\mathrm{inr},\cdot}\begin{pmatrix} t \\ \varpi 1\end{pmatrix}.$$
The rows $N$ of the first equation give $\varpi 1 = U_{22}D$, so put $B = U_{22}$. Reduce modulo $\varpi^2$. The stacked matrix reduces to $w_s$. So $w_s = P\bar D$ with $P$ the reduction of the columns $\mathrm{inr}$ of $U$, and $\bar D = Qw_s$ with $Q$ the reduction of the rows $\mathrm{inr}$ of $U^{-1}$. $\square$

With these $P$ and $Q$, $w_sX = w_sX'$ if and only if $\bar DX = \bar DX'$. This is the hypothesis of the lemma on the glue matrix.

**Lemma (Clearing columns).** Some $K \in \mathrm{GL}_N$ modulo $\varpi^2$ has $\bar\varpi\,(w_sK)_{iy} = 0$ for every row $i$ and every $y \in N$ outside the range of $\mathrm{dividedEmb}$.

Lean: `New.Rows.DividedSplitting.exists_genResidue_mul_stackOverGenScalar_eq_zero` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The ring modulo $\varpi^2$ is a valuation pair in the sense of the library (`isValuationPair_residueRing`), so it allows column reduction. Column operations bring the $a \times N$ matrix $s$ to a matrix $sK$ that is $0$ in the columns outside $\mathrm{dividedEmb}$, since $\mathrm{dividedEmb}$ has $\#a$ columns. This gives the rows $a$. The rows $N$ of $w_sK$ are $\bar\varpi K$, and $\bar\varpi^2 = 0$ modulo $\varpi^2$. $\square$

**Lemma (A left inverse of the glue matrix).** If $BD = \varpi\cdot 1$, then $C\,G_D = \varpi\cdot 1$ for
$$C = \begin{pmatrix} B & \iota_e\iota_z^T \\ 0 & \Delta'\end{pmatrix},\qquad \Delta' = \mathrm{diag}(1 \text{ on } z(r),\ \varpi \text{ elsewhere}).$$

Lean: `New.Rows.DividedSplitting.exists_mul_glueMatrix_eq` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Multiply by blocks. The top left block is $BD = \varpi$. The bottom left block is $0$. The bottom right block is $\Delta'\Delta = \varpi$. The top right block is $-BD\iota_e\iota_z^T + \iota_e\iota_z^T\Delta$. Here $BD = \varpi$, and $\iota_z^T\Delta = \varpi\iota_z^T$ since the rows $z$ of $\Delta$ are $\varpi$ times those of $1$. So the block is $0$. $\square$

**Theorem (Glued lattices exist).** For every $a \times N$ matrix $s$ modulo $\varpi^2$ there is a divided lattice $L$ that is glued for $s$.

Lean: `New.Rows.DividedSplitting.exists_isGlued` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Take $B$, $D$, $P$, $Q$ from the lemma on a divisor, and put $G = G_D$. Then $w_sX = w_sX'$ if and only if $\bar DX = \bar DX'$. The lemma on a left inverse gives $C$ with $CG = \varpi 1$. Choose a permutation $\sigma$ of $n$ with $\sigma(\varepsilon(\mathrm{inr}(z\,i))) = O.\mathrm{incl}\,i$, and put $\varepsilon' = \sigma\circ\varepsilon$. Reorder $C$ by $\varepsilon$ in the rows and $\varepsilon'$ in the columns, and $G$ by $\varepsilon'$ and $\varepsilon$. The product is still $\varpi 1$. The lemma on divided lattices with a given reduced inverse gives $L$ with $\bar G_L$ equal to the reordered $\bar G$. Now check the three properties.

Property 2. If $xY$ is block normalised, the lemma on translates by $\Gamma$ gives $\bar G_Lx = \bar\varpi\,\iota_{O.\mathrm{incl}}$.

Property 1. Let $\bar G_Lx = \bar\varpi\,\iota_{O.\mathrm{incl}}$. By reordering, $\bar G\,x_{\varepsilon(\cdot)} = \bar\varpi\,\iota_{\mathrm{inr}\circ z}$. Read the rows $\mathrm{inr}(z\,i)$: they give $\bar\varpi\,v_{z(i)} = \bar\varpi\,e_i$, so $\bar\varpi(1 - v_z) = 0$. The lemma on inverses of the form $1 - Y$ of Section 2 gives $Y \in \Gamma$ with $Y^{-1} = 1 - (1 - v_z) = v_z$. By the lemma on translates, $xY$ is block normalised. If $xY'$ is block normalised for $Y' \in \Gamma$, the same lemma gives $Y'^{-1} = v_z = Y^{-1}$, so $Y' = Y$.

Property 3. Take $K$ from the lemma on clearing columns. The columns of $\bar G$ on $N$ are $(\bar D; 0)$. For $y$ outside the range of $\mathrm{dividedEmb}$, $\bar\varpi(\bar DK)_{xy} = \sum_i Q_{xi}\,\bar\varpi(w_sK)_{iy} = 0$. Reordering the rows by $\varepsilon'$ does not change this. $\square$

### Example: the case without rows

Let $r = N = m = 1$ and let $a$ be empty, so $s$ has no rows and $w_s = \bar\varpi$. One can take $D = \varpi$ and $B = 1$. Then
$$G_D = \begin{pmatrix}\varpi & -\varpi\\ 0 & \varpi\end{pmatrix},\qquad C = \begin{pmatrix}1 & 1\\ 0 & 1\end{pmatrix},\qquad CG_D = \varpi\cdot 1.$$
At the chosen places $\gamma = \varpi G_D^{-1} = C$, up to the order of the basis. Here $C$ is invertible over $\mathcal{O}$, so $\gamma\mathcal{O}^2 = \mathcal{O}^2$, and $\gamma$ only changes the basis: the vector $e_1 + e_2$ joins the two summands. For $x = (u; v)$ the congruence $\bar G_D x = (0;\bar\varpi)$ says $\varpi(u - v) \equiv 0$ and $\varpi v \equiv \varpi$, that is $u \equiv v \equiv 1$ modulo $\varpi$. The unique $Y$ is $v^{-1}$, and $xY = (uv^{-1}; 1)$ is block normalised. Now let $\#a = 1$ and let $s$ be a unit. Then one can take $D = 1$ and $B = \varpi$, so the first column of $C$ is $\varpi e_1$. The lattice $\gamma\mathcal{O}^2$ is spanned by $\varpi e_1$ and $e_1 + e_2$, and the direction of $V''$ is divided. If $m$ has an index $k$ outside $z(r)$, the entry $\Delta'_{kk} = \varpi$ divides the direction $e_k$ of $V^\circ$ in the same way.

**Remark (Formalization).** The lattice of the theorem is given by an existence statement, through a Hermite form and a permutation $\sigma$ chosen by `Equiv.Perm.exists_extending_pair`. It is not canonical. Only the three properties of a glued lattice are used later. The scalar $c_\gamma$ of Section 2 and the exponent of Section 4 are read off from $L$, so they are not canonical either. The second part uses them only through these properties.
