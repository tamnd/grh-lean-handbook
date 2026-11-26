---
title: The first path datum
lean:
  - New/Determinant/AuxiliaryForms/GridFirstColumns.lean
decls:
  - New.Data.map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel
  - New.Data.firstPointDatum_invariant
  - New.Data.fintypeQuotientNodeLevel
  - New.Data.LevelCosets
  - New.Data.LevelCosets.out
  - New.Data.LevelCosets.family
  - New.Data.firstPathDatum
  - New.Data.firstPathDatum_invariant
  - New.Data.card_levelCosets_le
  - New.Data.isPathDatum_firstPathDatum
  - New.Data.sum_firstPathDatum_mul
  - New.Data.card_levelCosets_eq
  - New.Data.exists_diagonalPeriodForm_transposedChain_eq
  - New.Data.exists_isPathDatum_diagonalPeriodForm_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The first path datum

This section finishes Step 1 of the plan. The function $\Psi^1$ of the previous section is not a path datum: it is fixed only by families in the levels. We average it over cosets of the levels.

**Lemma.** Let $k$ be in the level at $(z, 0, i)$. Then $k$ reduces to $1$ modulo $\mathfrak{t}_z$, and the character of every edge $e_{z,b}$ is $1$ at $\det k$. If every $g(z, 0, i)$, $i \leq m$, is in the level of its node, then $\varepsilon(g, \mathrm{first})\, \Psi^1(g \cdot S) = \Psi^1(S)$.

Lean: `New.Data.map_eq_one_and_edgeChar_eq_one_of_mem_nodeLevel`, `New.Data.firstPointDatum_invariant` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* For $z = \mathrm{false}$ the level is trivial, so $k = 1$. For $z = \mathrm{true}$ the level is the kernel of reduction modulo $\mathfrak{b} = \mathfrak{t}_{\mathrm{true}}$. The character of a column edge in this grid has no twist. It is the character of `gridTamePart` at the trivial twist, read at the integral lift $k_0$ of $k$ (`gridChar_det`). So it may be computed modulo the modulus of the trivial twist, which is $\mathfrak{b}$, where $k_0$ is $1$. For the second claim, each factor of $\varepsilon$ is $1$. The reduction of $g(q)^{-1} S(e)\, g(p)$ modulo $\mathfrak{t}_z$ is the reduction of $S(e)$, so $\Psi^1$ does not change. $\square$

**Definition.** $\mathrm{LevelCosets}(\vartheta)$ is the set of families $x$ of a coset $x(z, i)$ of the level in $\mathrm{GL}$ at $(z, 0, i)$, for $z \in \{\mathrm{false}, \mathrm{true}\}$ and $i < m$. Its node family $x.\mathrm{out}$ takes a representative of $x(z, i)$ at $(z, 0, i)$ and $1$ at all other nodes. The family $x.\mathrm{family}$ is $x.\mathrm{out}$ with the value at $(\mathrm{true}, 0, 0)$ replaced by $x.\mathrm{out}(\mathrm{false}, 0, 0) \oplus 1$. Then
$$\Psi^0(S) = \sum_{x \in \mathrm{LevelCosets}(\vartheta)} \varepsilon(x.\mathrm{family}, \mathrm{first})\ \Psi^1(x.\mathrm{family} \cdot S).$$

Lean: `New.Data.fintypeQuotientNodeLevel`, `New.Data.LevelCosets`, `New.Data.LevelCosets.out`, `New.Data.LevelCosets.family`, `New.Data.firstPathDatum` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

**Remark (Formalization).** The representatives come from `Quotient.out`, a choice. The coset at $(\mathrm{true}, 0, 0)$ does not act, so each translate is counted equally often.

**Theorem.** $\Psi^0$ is a path datum on the first path for the bound $B^{2m}$, with $B$ = `edgeMatrixCountBound` $\vartheta$.

Lean: `New.Data.firstPathDatum_invariant`, `New.Data.card_levelCosets_le`, `New.Data.isPathDatum_firstPathDatum` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* Condition 1: $\Psi^1(x.\mathrm{family} \cdot S)$ depends only on $S$ on the column edges, by claim 3 of the lemma on point data in the previous section.

Condition 2: let $g$ be admissible. Left multiplication by $g(z, 0, i)$ permutes the cosets at $(z, 0, i)$; call the permutation of $\mathrm{LevelCosets}$ $\sigma$. Reindex the sum by $\sigma$. We claim that $h = (\sigma x).\mathrm{family}^{-1}\, g\, x.\mathrm{family}$ is in the levels at all nodes $(z, 0, i)$, $i \leq m$. For $i < m$ and $(z, i) \neq (\mathrm{true}, 0)$ this is the definition of $\sigma$. At $i = m$ both families are $1$ and $g(z, 0, m)$ is in the level by admissibility. At $(\mathrm{false}, 0, 0)$ the level is trivial, so the component of $h$ is $1$. At $(\mathrm{true}, 0, 0)$ all three factors are block matrices $\cdot \oplus 1$ (for $g$ by admissibility), so the component is $1 \oplus 1 = 1$. Now the lemma gives $\Psi^1(x.\mathrm{family}\cdot S) = \varepsilon(h)\, \Psi^1(h \cdot (x.\mathrm{family} \cdot S))$. The action is a right action and $\varepsilon$ is multiplicative in the family. Collecting the factors gives $\varepsilon(g, \mathrm{first})\, \Psi^0(g \cdot S) = \Psi^0(S)$.

Condition 3: let $\Psi^0(S) \neq 0$ and let $e$ be a vertical edge of the first path. The vertical edges of the first path are the $e_{\mathrm{false}, i}$. Some term is nonzero, so $P_{\mathrm{false}}(i)$ is nonzero at $(x.\mathrm{family} \cdot S)(e)$. By claim 4 of the same lemma this matrix has a left inverse $L$. Then $x.\mathrm{family}(0, i)\, L\, x.\mathrm{family}(0, i+1)^{-1}$ is a left inverse of $S(e)$.

Condition 4: each term is a root of unity times $0$ or $1$, so $\Psi^0(S)$ is a sum of at most $|\mathrm{LevelCosets}|$ roots of unity. There are $2m$ cosets in a family, and each set of cosets is at most $|\mathrm{GL}| \leq |M_r(O_E/\mathfrak{m})| \leq B$ for a rank $r \leq 2 n_m$. So $|\mathrm{LevelCosets}| \leq B^{2m}$. $\square$

### The period of the first path

**Theorem.** For every twist $\vartheta$, real point $g$, conjugate form $y'$ on $Y_m$ and form $\varphi$ on $\tilde Y^m_0$:

1. $\sum_S \Psi^0(S)\, \mathrm{diag}_g(S) = |\mathrm{LevelCosets}(\vartheta)| \sum_S \Psi^1(S)\, \mathrm{diag}_g(S)$, where $\mathrm{diag}_g(S)$ is the diagonal pairing of $\mathrm{formMap}(S)\, y'$ and $\mathrm{formMap}(S)\, \varphi$ and $S$ runs over $\mathrm{tuples}(\mathrm{first})$;
2. $|\mathrm{LevelCosets}(\vartheta)| = \prod_{i < m} [\mathrm{GL}(Y_i) : \mathrm{nodeLevel}]\ n_{\mathrm{true}}(i)$;
3. there is $C \in \mathbb{C}$, the same for all $\vartheta$, $g$, $y'$, $\varphi$, with
$$\mathrm{diag}_g\big(\mathrm{chain}^{\vartheta}_{\mathrm{false}}(0)\, y', \mathrm{chain}^{1}_{\mathrm{true}}(0)\, \varphi\big) = C \cdot I(\Psi^0; g)(\vartheta, y', \varphi).$$

Lean: `New.Data.sum_firstPathDatum_mul`, `New.Data.card_levelCosets_eq`, `New.Data.exists_diagonalPeriodForm_transposedChain_eq` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* For claim 1, expand $\Psi^0$ and exchange the sums. Fix $x$. The family $x.\mathrm{family}$ is $1$ at both ends $(z, 0, m)$, since $m \neq 0$ and the cosets have $i < m$, and it is a block matrix at $(\mathrm{true}, 0, 0)$. So the second translation lemma of the previous section gives $\mathrm{diag}_g(x.\mathrm{family} \cdot S) = \varepsilon(x.\mathrm{family})\, \mathrm{diag}_g(S)$. Substitute $S \mapsto x.\mathrm{family} \cdot S$ in the sum over tuples. This gives $\sum_S \varepsilon\, \Psi^1(x.\mathrm{family}\cdot S)\, \mathrm{diag}_g(S) = \sum_S \Psi^1(S)\, \mathrm{diag}_g(S)$, the same for every $x$. For claim 2, the number of cosets at a node is the index of the level. At $(\mathrm{true}, 0, i)$ the index is $n_{\mathrm{true}}(i)$ (`levelIndex_eq_card_GL_untwisted`). For claim 3, apply the last theorem of the previous section with $B = \mathrm{diag}_g$. Write $n_{\mathrm{false}}(i) = C_i \cdot [\mathrm{GL}(Y_i) : \mathrm{nodeLevel}]$ by the counting lemma of the previous section. Then $\prod_i n_{\mathrm{false}}(i)\, n_{\mathrm{true}}(i) = (\prod_i C_i)\, |\mathrm{LevelCosets}|$, and claim 1 turns the sum with $\Psi^1$ into $I(\Psi^0; g)$. Put $C = \prod_{i < m} C_i$. $\square$

**Corollary.** There are $C \in \mathbb{C}$ and, for each twist $\vartheta$, a path datum $\Psi_\vartheta$ on the first path for the bound $B^{2m}$, such that the period of the transposed chains at every $g$ is $C \cdot I(\Psi; g)(\vartheta, y', \varphi)$.

Lean: `New.Data.exists_isPathDatum_diagonalPeriodForm_eq` (New/Determinant/AuxiliaryForms/GridFirstColumns.lean).

*Proof.* Take $\Psi = \Psi^0$ and the two theorems of this section. $\square$

**Remark (Formalization).** The statement does not say $C \neq 0$. From the proof, $C = \prod_i C_i$ with $C_i = (|O_E/\varpi| / |O_E/\varpi^{b_0}|)^{r_i^2} > 0$. A user who needs $C \neq 0$ must use the proof, not the statement.

This is Step 1. The constant $C$ and the datum $\Psi^0$ are used in the next chapter, together with the transfer of Section 7 and the proportionality of Section 9.
