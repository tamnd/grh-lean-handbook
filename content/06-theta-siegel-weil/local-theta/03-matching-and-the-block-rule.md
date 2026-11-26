---
title: Matching parameters and the block rule
lean:
  - Lib/DiscreteSeries/Theta/FockDualPair.lean
  - Lib/DiscreteSeries/Theta/FockJointHarmonics.lean
  - Lib/DiscreteSeries/Theta/BlockRule.lean
decls:
  - New.FockDualPair.IsMatchedPair
  - New.IsMatch
  - New.FockDualPair.IsTermwiseHarmonic
  - New.FockDualPair.IsJointHighest
  - New.IsJointHarmonic
  - New.IsJointHarmonic.swap
  - New.IsMatch.col_eq_of_isMatchedPair
  - New.IsMatch.hasLargeGap
  - New.HCParam.HasGap.two_mul_relWeight
  - New.IsMatch.relWeight_eq_neg
  - New.IsMatch.sign_mul_relWeight_nonneg
  - New.IsBlockRule
  - New.isBlockRule_iff_isMatch
  - New.IsBlockRule.symm
  - New.IsBlockRule.shift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Matching parameters and the block rule

This section defines when a row parameter and a column parameter match, and what a joint harmonic is. It proves the facts about weights that the later sections use. Then it proves that matching is the block rule for the correspondence of discrete series parameters. The block rule is the form that the global argument uses, in [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/).

Fix dual pair data $T$ as in Section 2, with $n$ rows and $n'$ columns, sign $\sigma$ and integers $\gamma$, $\gamma'$. Let $l = 2\lambda$ be a parameter for the signs $\varepsilon$ of the rows and $l' = 2\lambda'$ a parameter for the signs $\varepsilon'$ of the columns. Write $\xi_r = l_r - 2\gamma + n'$ for the centred parameter of row $r$ and $\xi'_c$ for the centred parameter of column $c$ for the swap, that is, $\xi'_c = l'_c - 2\gamma' + n$. Write $\eta_{rc} = \sigma\varepsilon_r\varepsilon'_c$ for the sign of the variable $X_{rc}$.

### Matching

**Definition (Matched pair).** Row $r$ is *matched* with column $c$ if
$$\xi_r = -\xi'_c \quad \text{and} \quad |n - n'| < \eta_{rc}\,\xi_r.$$

Lean: `New.FockDualPair.IsMatchedPair` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

**Definition (Matching parameters).** The parameters $l$ and $l'$ *match* for $T$ if the following hold.
1. Both $l$ and $l'$ have gap $500(n+n')^3$.
2. Every row $r$ is matched with a column, or $|\xi_r| < n - n'$.
3. Every column $c$ is matched with a row, or $|\xi'_c| < n' - n$.

Lean: `New.IsMatch` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The fields are `New.IsMatch.hasGap_row`, `New.IsMatch.hasGap_column`, `New.IsMatch.left` and `New.IsMatch.right`.

The gap condition is that of [discrete series through one matrix coefficient](/chapter/discrete-series/): the entries of $l$ are distinct, each has the parity of $n - 1$, and $|l_i - l_j| \geq 2h$ when $\varepsilon_i \neq \varepsilon_j$. So $|\lambda_i - \lambda_j| \geq h$ across the signs. If $n \geq n'$, the unmatched rows have small centred parameters, and every column is matched. If $n \leq n'$, it is the other way. If $n = n'$, everything is matched. The matched pairs give a partial bijection between rows and columns:

**Lemma.** If $l$ and $l'$ match, a row is matched with at most one column, and a column with at most one row.

Lean: `New.IsMatch.col_eq_of_isMatchedPair` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean). The statement for columns is `New.IsMatch.row_eq_of_isMatchedPair`.

*Proof.* If $r$ is matched with $c$ and with $d$, then $\xi'_c = -\xi_r = \xi'_d$. The entries of $l'$ are distinct, so $c = d$. The other statement is the same with $l$. $\square$

**Lemma.** If $l$ and $l'$ match, then $l$ has gap $500n^3 + A$ for every $A \leq |\iota| = nn'$.

Lean: `New.IsMatch.hasLargeGap` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* $500(n+n')^3 \geq 500n^3 + 1500n^2n' \geq 500n^3 + nn'$ if $n \geq 1$, and $nn' = 0$ if $n = 0$. $\square$

The analytic theorems of Volume 5 need the gap $500n^3 + A$, where $A$ is the growth exponent, here $|\iota|$ (Section 8).

**Definition (Joint harmonic).** A polynomial $P$ is *termwise harmonic* if $\partial_{ac}\partial_{bc}P = 0$ for all columns $c$ and all rows $a, b$ with $\varepsilon_a \neq \varepsilon_b$. It is *jointly highest* of weights $\nu$, $\nu'$ if $P \neq 0$, $P$ is termwise harmonic for $T$ and for the swap, $P$ is $K$-highest of weight $\nu$ for the row action and the order of $l$, and $P$ is $K$-highest of weight $\nu'$ for the column action and the order of $l'$. A *joint harmonic* is a jointly highest polynomial of the weights $\Lambda$ and $\Lambda'$ of the lowest $K$-types of $l$ and $l'$, for matching $l$ and $l'$.

Lean: `New.FockDualPair.IsTermwiseHarmonic` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The other two are `New.FockDualPair.IsJointHighest` and `New.IsJointHarmonic`.

Termwise harmonic for $T$ means that no monomial of $P$ contains two variables of one column from rows of opposite signs. Termwise harmonic for the swap is the same with rows and columns exchanged. Then the Laplacians $\sum_c \partial_{ac}\partial_{bc}$, which are the lowering part of the noncompact operators, kill $P$.

**Theorem.** If $\Phi$ is a joint harmonic for $T$, $l$, $l'$, then $\Phi$ is a joint harmonic for the swap, $l'$, $l$.

Lean: `New.IsJointHarmonic.swap` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* The swap of the swap is $T$, the matched pairs of the swap are the matched pairs of $T$ with the factors exchanged, and the conditions of a jointly highest polynomial are symmetric. $\square$

### Weights relative to the vacuum

Let $\Lambda = \lambda + \rho - 2\rho_c$ be the lowest $K$-type of $l$, and let $w_r = \Lambda_r - v(\varepsilon_r)$ be the weight relative to the vacuum (Section 2).

**Lemma.** Let $l$ have a gap. Then
$$2w_r = l_r + \sum_{j \in R}\varepsilon_r\varepsilon_j\operatorname{sign}(l_j - l_r) - 2\gamma + n' - \sum_{c \in C}\eta_{rc}.$$

Lean: `New.HCParam.HasGap.two_mul_relWeight` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* The entry $2\rho_r$ is $\sum_j \operatorname{sign}(l_r - l_j)$, and $2(\rho_c)_r$ is the same sum over the $j$ with $\varepsilon_j = \varepsilon_r$. So $2\rho_r - 4(\rho_c)_r = \sum_j(-\varepsilon_r\varepsilon_j)\operatorname{sign}(l_r - l_j)$. The parity condition makes $l_r + 2\rho_r$ even, so the rounding in the definition of $\lambda + \rho$ is exact. The vacuum weight is $\gamma$ minus the number of negative variables in row $r$, that is, $2v(\varepsilon_r) = 2\gamma - n' + \sum_c\eta_{rc}$. $\square$

**Theorem.** Let $l$ and $l'$ match, and let row $r$ be matched with column $c$. Then $w_r = -w'_c$, where $w'_c$ is the weight relative to the vacuum of column $c$ for the swap.

Lean: `New.IsMatch.relWeight_eq_neg` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Apply the lemma to $r$ and, for the swap, to $c$. Since $\xi_r = -\xi'_c$, the claim reduces to an equation $\sum_{d}G_d = \sum_j F_j$ between a sum over columns and a sum over rows. Here $F_j$ compares the sign of $l_j - l_r$ with the sign of the variable $(j, c)$, and $G_d$ compares the sign of $l'_d - l'_c$ with that of $(r, d)$. The terms of a matched pair $(j, d)$ agree, and the terms of unmatched rows and columns are $0$, since their centred parameters are small. The source proves the equation as two inequalities, with `New.IsMatch.sum_cols_le_sum_rows` applied to $(F, G)$ and to $(-F, -G)$. $\square$

**Theorem.** Let $l$ and $l'$ match, let $s$ be a sign, and let $n' - n < s\,\xi_r$. Then $0 \leq s\,w_r$.

Lean: `New.IsMatch.sign_mul_relWeight_nonneg` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* The numbers $s\xi_j + n - n'$ are odd and distinct. Write them as $2v_j + 1$, so that $v_r \geq 0$. At most $v_r + 1$ rows have $0 \leq v_j \leq v_r$. Compare the formula of the lemma termwise with a sum over columns, as in the last proof. The column terms are at most $0$, the rows with $v_j \in [0, v_r]$ contribute at least $0$, and the other rows have the term of their column or a term $0$ by the gap. The result is $2s\,w_r \geq 2v_r + 1 - 2(v_r + 1) = -1$. As $s\,w_r$ is an integer, $s\,w_r \geq 0$. $\square$

Sections 4 and 5 use this sign lemma.

### The block rule

The global argument states the correspondence of parameters at a real place in the form of Li and Paul. Let $S$ and $T$ be hermitian spaces of ranks $n$ and $n'$, with signs $s$ and $t$ and doubled parameters $l = 2\lambda$ and $l' = 2\lambda'$. Let $\gamma = \operatorname{wt}\chi_S + n/2$ and $\gamma' = \operatorname{wt}\chi_T + n'/2$, where $\chi_S$ and $\chi_T$ are the characters that define the splitting of the metaplectic cover. The *shifted entries* are $l_c - 2\gamma' + n'$ for $S$ and $l'_r - 2\gamma + n$ for $T$. For an integer $d \geq 0$ the *block* $[d]$, doubled, is $\{d - 1, d - 3, \ldots, 1 - d\}$.

**Definition (Block rule).** The parameters satisfy the *block rule* for $\gamma$, $\gamma'$ if the following hold.
1. Both $l$ and $l'$ have gap $500(n+n')^3$.
2. If $n \leq n'$, the shifted entries for $T$ are those for $S$ together with the block $[n' - n]$.
3. If $n' \leq n$, the shifted entries for $S$ are those for $T$ together with the block $[n - n']$.
4. If a shifted entry for $S$ at $c$ equals one for $T$ at $r$ and is positive, then $s_c = t_r$.
5. If such a common entry is negative, then $s_c = -t_r$.

Lean: `New.IsBlockRule` (Lib/DiscreteSeries/Theta/BlockRule.lean).

In the textbook, the parameter of the lift is obtained from the parameter of the given discrete series by adding the block $[n'-n]$ to the shifted entries, and the signs of the common entries follow a rule of the same kind. This is the description of the correspondence of discrete series parameters in the stable range by Li, and in general by Paul (Li, Duke Math. J. 61 (1990); Paul, Canad. J. Math. 51 (1999), both as the source cites them in [BlockRule.lean](lean:Lib/DiscreteSeries/Theta/BlockRule.lean#L1)). This book has not compared either source.

**Theorem.** The block rule holds for $\gamma$, $\gamma'$, $l$, $l'$ if and only if $l'$ and $-l$ match for the standard data with rows for $T$, columns for $S$, row integer $\gamma$ and column integer $-\gamma' + n'$:
$$\text{block rule}(\gamma, \gamma', l, l') \iff \text{match}(\operatorname{std}(t, s, \gamma, -\gamma'), l', -l).$$

Lean: `New.isBlockRule_iff_isMatch` (Lib/DiscreteSeries/Theta/BlockRule.lean).

*Proof.* For the standard data, the centred parameter of row $r$ is $l'_r - 2\gamma + n$, the shifted entry for $T$. The centred parameter of column $c$ for the swap, for the parameter $-l$, is $-l_c - 2(-\gamma' + n') + n' = -(l_c - 2\gamma' + n')$, minus the shifted entry for $S$. So a matched pair is a common shifted entry $x$ with $|n' - n| < t_r s_c\,x$ (`New.isMatchedPair_std_iff`). Since $|t_r s_c x| = |x|$, the inequality says that $|x| > |n' - n|$ and that $t_r s_c$ is the sign of $x$ (`New.lt_sign_mul_iff`). That is conditions 4 and 5. Let $n \leq n'$ and $d = n' - n$. The entries of the block are the integers of modulus less than $d$ with the parity of $d - 1$. So "the entries for $T$ are those for $S$ together with the block" is equivalent to "each row is matched or has modulus less than $d$, and each column is matched" (`New.exists_matched_of_entries_eq` and `New.entries_eq_of_exists_matched`). The case $n' \leq n$ follows from the first case by the symmetry of both sides (`New.IsBlockRule.symm`, `New.IsMatch.std_symm`). $\square$

The signs of $-l$ in this theorem need care. The theorem is stated for $-l$ with the signs $s$ of $S$, not for the reversed signs. This is the form that the global lift uses: the chosen joint harmonic at a real place $w$ is a joint harmonic for $\operatorname{std}(t, s, \gamma_w, -\gamma'_w)$, $l'_w$ and $-l_w$ (`New.jointHarmonicAt`, Lib/Weil/Lift.lean).

**Proposition.** The block rule has three symmetries. It is symmetric in the two spaces: the rule for $\gamma$, $\gamma'$, $l$, $l'$ implies the rule for $\gamma'$, $\gamma$, $l'$, $l$. It is kept under negation of the parameters with the inverse characters. It is kept when $\gamma$, $\gamma'$ are raised by integers $u$, $u'$ and the parameters $l$, $l'$ by $2u'$, $2u$.

Lean: `New.IsBlockRule.symm` (Lib/DiscreteSeries/Theta/BlockRule.lean). The other two are `New.IsBlockRule.neg` and `New.IsBlockRule.shift`.

*Proof.* The definition is symmetric under the exchange of the two spaces, with conditions 2 and 3 exchanged and conditions 4 and 5 read from the other side. A shift of $\gamma'$ by $u'$ and of $l$ by $2u'$ does not change the shifted entries $l_c - 2\gamma' + n'$. Negation of the parameters and of the signs of $S$, with $\gamma$, $\gamma'$ replaced by $n - \gamma$, $n' - \gamma'$, negates the shifted entries. The block is symmetric under negation, and conditions 4 and 5 exchange. $\square$

**Example (The pair $U(1,1) \times U(1)$).** Take two rows with signs $(1, -1)$, one column with sign $1$, $\sigma = 1$, and the standard data with integers $\gamma$ and $\gamma'$. Here $n = 2$, $n' = 1$, and the column integer is $\gamma' + 2$. The variable $X_1$ of row 1 is positive and the variable $X_2$ of row 2 is negative. The parity condition makes $l_1$, $l_2$ odd. The column must be matched, since $n' < n$. It is matched with one row only. Let it be row 1, so that row 2 is free. Then $|\xi_2| < 1$, so $\xi_2 = 0$ and $l_2 = 2\gamma - 1$. Row 1 has $\xi_1 = 2k$ with $2k > 1$, so $k \geq 1$ and $l_1 = 2\gamma + 2k - 1$. The column has $\xi' = -2k$, so $l' = 2\gamma' + 2 - 2k$. The gap condition asks $|l_1 - l_2| = 2k \geq 2 \cdot 500 \cdot 27$, so $k \geq 13500$. In the language of the block rule, the shifted entries of the rows are $\{2k, 0\}$, those of the column are $\{2k\}$, and $\{0\}$ is the block $[1]$. The common entry $2k$ is positive, and the signs of row 1 and the column are equal, as condition 4 asks.

The lowest $K$-types are computed as follows. There are no compact roots, since the signs of the rows differ. So $\Lambda = \lambda + \rho = (\gamma + k, \gamma - 1)$. The vacuum weights are $v(1) = \gamma$ and $v(-1) = \gamma - 1$, so $w = (k, 0)$. For the column, $\Lambda' = \lambda' = \gamma' + 1 - k$. Section 4 gives the joint harmonic $X_1^k$.
