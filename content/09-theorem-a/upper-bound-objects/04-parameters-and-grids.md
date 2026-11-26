---
title: Parameters and grids
lean:
  - New/UpperBound/Objects/InsertBlock.lean
  - New/UpperBound/Objects/Parameters.lean
decls:
  - New.CentreSystem
  - New.CentreSystem.IsSeparated
  - New.CentreSystem.IsParam
  - New.CentreSystem.IsParam.isBlockRule_insert_of_down
  - New.CentreSystem.IsParam.isBlockRule_neg_insert_of_up
  - New.Data.GridIndex
  - New.Data.gridSigns
  - New.Data.gridParam
  - New.Data.signsY
  - New.Data.paramY
  - New.Data.card_gridIndex
  - New.Data.negCount_gridSigns
  - New.Data.gridDiagEquiv
  - New.Data.gridParam_interlace
  - New.Data.gridCentres
  - New.Data.isSeparated_gridCentres
  - New.Data.isParam_gridParam
  - New.Data.paramsCorrespond_grid_succ_left
  - New.Data.paramsCorrespond_grid_succ_right
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Parameters and grids

The lower chain $Y_0 \subset Y_1 \subset \dots \subset Y_m$ is a chain of theta lifts between indefinite unitary groups. A theta lift of a discrete series form is nonzero, and of discrete series type, only if the two Harish-Chandra parameters match. The rule that says when they match is the block rule of [local theta in the Fock model](/chapter/local-theta/) ([IsBlockRule](/decl/New.IsBlockRule/)): for spaces of ranks $n \le n'$, with characters of weights $\gamma - n/2$ and $\gamma' - n'/2$, both parameters have a large gap, the longer parameter after a shift is the shorter one together with one block centred at $0$, and the signs of a common entry agree if the entry is positive and differ if it is negative.

All parameters in the source are built in one way, so that each step of every chain inserts one block. This section gives that construction and the two grids of spaces built from it.

### Centre systems

**Definition (Centre system).** A centre system consists of a finite set $C$ of centres, and for each centre $c$ a value $c \in \mathbb{Z}$, a length $l_c$ and a kind, up or down; and a finite set $S \subset \mathbb{Z}$, the doubled entries of the stem. For $B \subseteq C$, the doubled entries of $\lambda^+_B$ are $S$ together with the blocks $2c + 2[l_c]$, $c \in B$. The rank is $n_B = \#S + \sum_{c \in B} l_c$. The doubled lowering is $1$ if $\#S$ and $\#B$ are odd, and $0$ otherwise. A centre $c$ *counts for* a doubled entry $y$ if $c$ is down and $y < 2c$, or $c$ is up and $y > 2c$. The sign of $y$ is $(-1)$ to the number of centres outside $B$ that count for $y$.

Lean: `New.CentreSystem` (New/UpperBound/Objects/InsertBlock.lean).

**Definition (Separated system; parameter of a set).** The system is *separated* with bound $h$ if all lengths have the parity of $\#S$, each $y + \#S$ with $y \in S$ is odd, and every centre $c$ has distance at least $h + l_c$ from $2c$ to each entry of the stem and of the blocks of the other centres. A vector $l = 2\lambda$ on a space with signs $s$ is the *parameter of $B$ with sign $\sigma$* if the space has rank $n_B$, the entries $l_x$ plus the lowering are exactly the doubled entries of $\lambda^+_B$, and $s_x = \sigma \cdot \mathrm{sign}(l_x + \mathrm{lowering})$.

Lean: `New.CentreSystem.IsSeparated` (New/UpperBound/Objects/InsertBlock.lean).

Lean: `New.CentreSystem.IsParam` (New/UpperBound/Objects/InsertBlock.lean).

**Theorem (Inserting a block).** Let the system be separated with bound $h$. Let $B \subseteq C$, let $c \in C \setminus B$ and $B' = B \cup \{c\}$. Let $l$ and $l'$ be parameters of $B$ and of $B'$ with the same sign $\sigma$, on spaces of ranks $n$ and $n'$. Suppose that $h \ge 500(n + n')^3$.

1. If $c$ is down, then $l$ and $l'$ satisfy the block rule with $\gamma = c + \lfloor n/2 \rfloor$ and $\gamma' = c + \lfloor n'/2 \rfloor$.
2. If $c$ is up, then $-l$ and $-l'$ satisfy the block rule with $\gamma = -c + \lceil n/2 \rceil$ and $\gamma' = -c + \lceil n'/2 \rceil$.

Lean: `New.CentreSystem.IsParam.isBlockRule_insert_of_down` (New/UpperBound/Objects/InsertBlock.lean).

Lean: `New.CentreSystem.IsParam.isBlockRule_neg_insert_of_up` (New/UpperBound/Objects/InsertBlock.lean).

*Idea of the proof.* The entries of $\lambda^+_{B'}$ are those of $\lambda^+_B$ and the new block around $c$. The lowerings of $B$ and $B'$ differ by the parity change of $\#B$, and the shift in the block rule absorbs this difference and moves the new block to $0$. The separation gives each parameter a gap of at least $h$ (`New.CentreSystem.IsParam.hasGap`), which the block rule needs. For the signs: the centre $c$ stops counting once it is in $B'$. So the sign of an entry changes exactly when $c$ counts for it, that is, for a down centre, when the entry lies below $2c$. After the shift by $-2c$ these are the negative entries, and the block rule asks for a change of sign exactly there. For an up centre, the centre counts for the entries above it, so one negates both parameters. $\square$

*Example.* Take a stem $S = \{0\}$, one down centre of value $c = -10^5$ and length $1$. The system is separated with bound $h = 2 \cdot 10^5 - 1$. For $B = \emptyset$ the parameter is $l = (0)$ on a space of rank $1$. For $B' = \{c\}$ the lowering is $1$, so $l' = (-1, -2\cdot 10^5 - 1)$ on a space of rank $2$. With $\gamma = -10^5$ and $\gamma' = -10^5 + 1$, the shifted entries $l - 2\gamma' + n'$ and $l' - 2\gamma + n$ are $\{2 \cdot 10^5\}$ and $\{2\cdot 10^5, 0\}$. The second is the first plus the block of length $1$ at $0$. As $500 \cdot 3^3 \le h$, the theorem applies.

### The two grids

The source uses two grids of spaces with nodes $(i, j)$. A flag $z$ selects the grid: $z = \text{false}$ for $Y$, $z = \text{true}$ for $\tilde Y$. The node $(i, j)$ of grid $Y$ is the space $Y^i_j$: the $r$ rows, $i$ blocks of length $t$ of one kind and $j$ blocks of length $t$ of the other. In grid $\tilde Y$ the base has $r + 1$ indices and the blocks have lengths $t + 1$ and $t - 1$. The lower chain is the edge $i = 0$ of grid $Y$. The other nodes are used by the seesaw identity in [the seesaw identity, part 1](/chapter/seesaw-identity-1/).

**Definition (Grid nodes).** At the node $(i, j)$ with offset $o$:

1. the index set `D.GridIndex z i j` is the base, then $i$ blocks of length $t + z$, then $j$ blocks of length $t - z$;
2. the signs are $+1$ on the added blocks, and on the base index of number $n$ they are given by the parity rule `New.Data.entrySign` $o\ j\ (n + 1 - k)$;
3. the doubled parameter in grid $Y$ is twice the target parameter on the base, with blocks of length $t$ centred at $\kappa_l$ for $1 \le l \le i$ and at $-\kappa_{o+l}$ for $1 \le l \le j$, all lowered by $1$ if $i + j$ is odd. In grid $\tilde Y$ it is the negative of the parameter of $\tilde Y^j_i$.

The space $Y_j$ has signs `New.Data.signsY j` and parameter `New.Data.paramY j`, the node $(0, j)$ of grid $Y$ with offset $0$.

Lean: `New.Data.GridIndex` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.gridSigns` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.gridParam` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.signsY` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.paramY` (New/UpperBound/Objects/Parameters.lean).

**Lemma (Ranks and signatures).** The node $(i, j)$ has rank $r + z + i(t + z) + j(t - z)$. With offset $0$ it has $\lfloor (m - j + z)/2 \rfloor$ negative signs, with $m - j$ truncated at $0$.

Lean: `New.Data.card_gridIndex` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.negCount_gridSigns` (New/UpperBound/Objects/Parameters.lean).

*Proof.* The rank is a count of the blocks. The negative signs lie on the base, and with offset $0$ the rule gives the sign $-1$ exactly to the base indices with $n + 1 - k \in \{j+1, j+3, \dots\}$. As $n < r + z$ and $r + 1 - k = m$, there are $\lfloor (m - j + z)/2 \rfloor$ of them. $\square$

So $Y_0$ has $m/2$ negative signs, and $Y_j$ is definite for $j \ge m$. This matches Section 1.

**Definition (The diagonal bijection).** For each $j$, `New.Data.gridDiagEquiv j` is a bijection from the index set of $Y^j_j$ plus one point to that of $\tilde Y^j_j$. It is the identity for $j = 0$. For $j \ge 1$ it is a bijection that matches the signs, chosen by `Exists.choose`.

Lean: `New.Data.gridDiagEquiv` (New/UpperBound/Objects/Parameters.lean).

**Proposition (Interlacing at the corner).** At each infinite place $\tau$ and for every integer $x$, the number of doubled entries above $x$ of the parameter of $\tilde Y^m_m$, less the number for $Y^m_m$, is $0$ or $1$. So the two parameters interlace, the first entry coming from $\tilde Y$.

Lean: `New.Data.gridParam_interlace` (New/UpperBound/Objects/Parameters.lean).

The proof counts block by block and inducts on $m$, with a bound sharper than the claim.

### Every step inserts a block

**Definition (The centres of a grid).** At $\tau$, grid $z$ has the up centres $\kappa_{l+1}(\tau)$ and the down centres $-\kappa_{l+1}(\tau)$ for $l < m$, of lengths $t + z$ and $t - z$. The stem is twice the target parameter on the base, plus $z$.

Lean: `New.Data.gridCentres` (New/UpperBound/Objects/Parameters.lean).

**Lemma.** The system of centres of each grid is separated with bound $\Delta - t - 2$. If $o + j \le m$ and ($o = 0$ or $i = 0$), the parameter of the node $(i, j)$ with offset $o$ is the parameter, with sign $(-1)^o$, of the set of the up centres $l < i$ and the down centres $o \le l < o + j$.

Lean: `New.Data.isSeparated_gridCentres` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.isParam_gridParam` (New/UpperBound/Objects/Parameters.lean).

The proof of the separation uses that consecutive lift weights differ by $\Delta$, that the entries $-(\kappa_i - \Delta/2)$ of the target parameter lie halfway between two of them, and that $k + t + 1 \le \Delta/2$. The bound $\Delta - t - 2$ is at least $500(N + N')^3$ for the ranks $N, N'$ of any two nodes with indices at most $m$ (`New.Data.mul_card_gridIndex_add_pow_three_le`), as $\Delta = 2r^8$ while the ranks are at most $2n_m$.

**Theorem (Neighbours correspond).** Let $N$ be the rank of a node. Put $\lfloor N/2 \rfloor - \kappa_{l+1}(\tau)$ or $\lceil N/2 \rceil - \kappa_{l+1}(\tau)$ for its weight in a step with centre $\pm\kappa_{l+1}$ (`New.Data.gridWeight`).

1. For $i + 1 \le m$ and $j \le m$, with offset $0$, the negated parameters of the nodes $(i, j)$ and $(i + 1, j)$ correspond at every infinite place.
2. For $i \le m$, $j + 1 + o \le m$ and ($o = 0$ or $i = 0$), the parameters of the nodes $(i, j)$ and $(i, j+1)$ correspond at every infinite place.

Lean: `New.Data.paramsCorrespond_grid_succ_left` (New/UpperBound/Objects/Parameters.lean).

Lean: `New.Data.paramsCorrespond_grid_succ_right` (New/UpperBound/Objects/Parameters.lean).

*Proof.* The step $(i, j) \to (i+1, j)$ adds the up centre $\kappa_{i+1}$, and the step $(i, j) \to (i, j+1)$ adds the down centre $-\kappa_{o+j+1}$. Apply the theorem on inserting a block to the parameters of the previous lemma. In grid $\tilde Y$ the ranks are even, so the two roundings of $N/2$ agree. $\square$

In particular the parameters of $Y_j$ and $Y_{j+1}$ correspond for $j < m$. This is what the lower chain of Section 8 needs.

**Remark (Formalization).** A correspondence of parameters (`New.ParamsCorrespond`) is the block rule at every infinite place. It says nothing about nonvanishing of a lift. The bijection `New.Data.gridDiagEquiv` is a choice; any bijection that matches the signs serves, and no statement depends on which one is chosen. The parameters are functions to $\mathbb{Z}$ that are doubled, so a parameter in $\tfrac12 + \mathbb{Z}$ is an odd integer here.
