---
title: The Fock model of a dual pair
lean:
  - Lib/DiscreteSeries/Theta/FockDualPair.lean
  - Lib/Weil/Fock/Basic.lean
decls:
  - New.Fock.raiseOp
  - New.Fock.lowerOp
  - New.Fock.canonical_commutation
  - New.Fock.glOp_commutator
  - New.Fock.glOp_neg
  - New.FockDualPair
  - New.FockDualPair.oscRowsUnit
  - New.FockDualPair.oscRowsUnit_commutator
  - New.FockDualPair.oscRows
  - New.FockDualPair.swap
  - New.FockDualPair.swap_swap
  - New.FockDualPair.swap_indexSign
  - New.FockDualPair.swap_oscRows_E
  - New.FockDualPair.vacuumWeight
  - New.FockDualPair.std
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Fock model of a dual pair

This section defines the algebraic data of a dual pair of unitary groups in the Fock model. The data are a polynomial ring with signed variables, two commuting actions of general linear Lie algebras on it, and a few integers that the later sections use.

### Raising and lowering operators

Let $\iota$ be a finite set and let $\eta : \iota \to \{\pm 1\}$ be a sign for each variable. The polynomial ring is $\mathbb{C}[X_i : i \in \iota]$, and $\partial_i$ is the partial derivative in $X_i$.

**Definition (Raising and lowering operators).** For $i \in \iota$ put
$$A_i = X_i, \quad B_i = \partial_i \quad \text{if } \eta_i = 1, \qquad A_i = -\partial_i, \quad B_i = X_i \quad \text{if } \eta_i = -1.$$
Here $X_i$ is the operator of multiplication by $X_i$. The operator $A_i$ is the *raising operator* and $B_i$ is the *lowering operator* of the variable $i$. Put $E_{ij} = A_i B_j$.

Lean: `New.Fock.raiseOp` (Lib/Weil/Fock/Basic.lean). The lowering operator is `New.Fock.lowerOp` and $E_{ij}$ is `New.Fock.glOp`.

The names follow the weight, not the degree.

**Theorem (Canonical commutation relations).** For all $i, j \in \iota$,
$$A_i A_j = A_j A_i, \qquad B_i B_j = B_j B_i, \qquad B_i A_j = A_j B_i + \delta_{ij}.$$

Lean: `New.Fock.canonical_commutation` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* Multiplications by variables commute, and partial derivatives commute, and a multiplication commutes with a derivative in another variable. So only the case $i = j$ of the third relation needs a check. If $\eta_i = 1$, then $\partial_i X_i = X_i \partial_i + 1$. If $\eta_i = -1$, then $B_i A_i = -X_i \partial_i$ and $A_i B_i = -\partial_i X_i = -X_i\partial_i - 1$, so again $B_i A_i = A_i B_i + 1$. $\square$

**Theorem.** The operators $E_{ij} = A_i B_j$ satisfy the relations of the matrix units:
$$E_{ij}E_{km} - E_{km}E_{ij} = \delta_{jk} E_{im} - \delta_{im} E_{kj}.$$

Lean: `New.Fock.glOp_commutator` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* By the third relation, $E_{ij}E_{km} = A_i A_k B_j B_m + \delta_{jk} A_i B_m$. The quartic term is symmetric in the two pairs by the first two relations. So the commutator is $\delta_{jk}E_{im} - \delta_{mi}E_{kj}$. $\square$

**Theorem.** If all the signs are reversed, the operators change as follows:
$$E^{-\eta}_{ij} = s_{ij}\, B_i A_j, \qquad s_{ij} = -1 \text{ if } \eta_i = \eta_j, \quad s_{ij} = 1 \text{ if not}.$$
Here $A$ and $B$ on the right are those of $\eta$.

Lean: `New.Fock.glOp_neg` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* For $-\eta$ the raising operator of $i$ is $-B_i$ if $\eta_i = 1$ and $B_i$ if $\eta_i = -1$. The lowering operator of $j$ is $A_j$ if $\eta_j = 1$ and $-A_j$ if $\eta_j = -1$. Multiply the four cases. $\square$

### Dual pair data

Let $R$ and $C$ be finite sets with signs $\varepsilon : R \to \{\pm1\}$ and $\varepsilon' : C \to \{\pm1\}$. Put $n = |R|$ and $n' = |C|$. The elements of $R$ are the *rows* and those of $C$ are the *columns*.

**Definition (Dual pair data).** The data of a dual pair in the Fock model for $\varepsilon$, $\varepsilon'$ are a sign $\sigma$, two integers $\gamma$ and $\gamma'$, and a bijection $R \times C \to \iota$, which names the variable $X_{rc}$ of row $r$ and column $c$. The variable $X_{rc}$ has the sign $\eta_{rc} = \sigma\,\varepsilon_r\,\varepsilon'_c$.

Lean: `New.FockDualPair` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The fields are `New.FockDualPair.globalSign`, `New.FockDualPair.rowShift`, `New.FockDualPair.columnShift` and `New.FockDualPair.varEquiv`. The sign of the variable is `New.pairSign` and `New.FockDualPair.varSign`.

**Definition (Row action).** For rows $a, b$ let $s_{ab} = 1$ if $\varepsilon_a = \varepsilon_b$ and $s_{ab} = \sigma$ if not. The matrix unit $E_{ab}$ of $\mathfrak{gl}_R$ acts on polynomials by
$$\rho(E_{ab}) = s_{ab} \sum_{c \in C} A_{ac} B_{bc} + \gamma\,\delta_{ab}.$$

Lean: `New.FockDualPair.oscRowsUnit` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

**Theorem.** The operators $\rho(E_{ab})$ satisfy $[\rho(E_{ab}), \rho(E_{cd})] = \delta_{bc}\rho(E_{ad}) - \delta_{ad}\rho(E_{cb})$. So $X \mapsto \sum_{a,b} X_{ab}\,\rho(E_{ab})$ is a representation of $\mathfrak{gl}_R(\mathbb{C})$ on the polynomial ring.

Lean: `New.FockDualPair.oscRowsUnit_commutator` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The representation is `New.FockDualPair.oscRows`, a `New.GlModule`.

*Proof.* Put $S_{ab} = \sum_c E_{(a,c),(b,c)}$. By the commutation rule of the $E_{ij}$ and $\delta_{(b,c),(c',d)} = \delta_{bc'}\delta_{cd}$, the $S_{ab}$ satisfy the rule of the matrix units. The signs satisfy $s_{ab}s_{bd} = s_{ad}$, because $\sigma^2 = 1$ and the number of sign changes along $a, b, d$ has the parity of $[\varepsilon_a \neq \varepsilon_d]$. The constants $\gamma\delta_{ab}$ are central. $\square$

For $\varepsilon_a = \varepsilon_b$ the operator $\rho(E_{ab})$ keeps the degree: each term is $X\partial$ or $\partial X$ up to sign. These are the operators of the complexified Lie algebra of the maximal compact subgroup $U(p) \times U(q)$. For $\varepsilon_a \neq \varepsilon_b$, the variables $X_{ac}$ and $X_{bc}$ have opposite signs. Then $A_{ac}B_{bc}$ is a product of two multiplications or of two derivatives. So the noncompact part acts by multiplication by quadratic polynomials and by second order operators.

### The swap and the column action

**Definition (Swap).** The swap of the data $T$ is the data for the signs $\varepsilon'$, $\varepsilon$ with sign $-\sigma$, integers $\gamma'$ and $\gamma$ in this order, and the variable of $(c, r)$ equal to that of $(r, c)$. The *column action* of $T$ is the row action of its swap.

Lean: `New.FockDualPair.swap` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

In Lean the column action of `T` is `T.swap.oscRows`.

**Theorem.** The swap of the swap is the original data. The signs of the variables for the swap are the negatives of those for $T$.

Lean: `New.FockDualPair.swap_swap` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The second statement is `New.FockDualPair.swap_indexSign`.

*Proof.* The first statement holds because $-(-\sigma) = \sigma$ and two exchanges of the factors of $R \times C$ give the identity. For the second, the sign of the variable $(c,r)$ for the swap is $(-\sigma)\varepsilon'_c\varepsilon_r = -\eta_{rc}$. $\square$

The global sign $\sigma$ makes the class of data closed under the swap. So each theorem about rows gives a theorem about columns.

**Theorem (Column action).** For columns $a, b$ let $s'_{ab} = 1$ if $\varepsilon'_a = \varepsilon'_b$ and $s'_{ab} = \sigma$ if not. Then the column action is
$$\rho'(E_{ab}) = s'_{ab}\Bigl(-\sum_{r \in R} B_{ra}A_{rb}\Bigr) + \gamma'\,\delta_{ab},$$
where $A$ and $B$ are the operators for the signs $\eta$ of $T$.

Lean: `New.FockDualPair.swap_oscRows_E` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* The swap has the signs $-\eta$. By the formula for reversed signs, each term of the sum for the swap is $\mp B_{ra}A_{rb}$, with the minus sign when the variables $(r,a)$ and $(r,b)$ have equal signs, that is, when $\varepsilon'_a = \varepsilon'_b$. The sign of the swap is $-\sigma$. In both cases the factor in front of $-\sum_r B_{ra}A_{rb}$ is $s'_{ab}$. $\square$

The two actions commute, by the canonical relations. The source does not state this as an algebraic lemma. It uses only the commutation of the group representations, a field of an oscillator pair (Section 8).

### The vacuum and the centred parameters

**Definition (Vacuum weight).** For a sign $s$ put
$$v(s) = \gamma - \#\{c \in C : \sigma\,s\,\varepsilon'_c \neq 1\}.$$
For a parameter $l = 2\lambda$ on the rows, the *weight relative to the vacuum* of row $r$ is $w_r = \Lambda_r - v(\varepsilon_r)$, where $\Lambda$ is the lowest $K$-type of $l$. The *centred parameter* of row $r$ is $\xi_r = l_r - 2\gamma + n'$.

Lean: `New.FockDualPair.vacuumWeight` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The other two are `New.FockDualPair.relWeight` and `New.FockDualPair.centredParam`.

The constant polynomial $1$ is the *vacuum*. It has the weight $v(\varepsilon_r)$ for $E_{rr}$. Indeed, $A_{rc}B_{rc}1 = X_{rc}\partial_{rc}1 = 0$ if the variable is positive, and $A_{rc}B_{rc}1 = -\partial_{rc}(X_{rc}) = -1$ if it is negative. The centred parameter is twice $\lambda_r - w$ with $w = \gamma - n'/2$. The number $w$ is the *centre* of the row action, `New.FockDualPair.centre`. It is the weight of the determinant character by which the row action is twisted (Section 6).

**Remark (Formalization).** In the textbook the diagonal operators of the oscillator representation of $\mathfrak{u}(p,q)$ carry a shift by $\pm n'/2$ from the metaplectic cover, and a twist by a character adds an integer. The source puts the whole shift into one integer $\gamma$. The half-integer appears only in the centre $w = \gamma - n'/2$. So all weights in the source are integers, and the parity conditions of the parameters take the place of the metaplectic cover.

**Definition (Standard data).** For signs $\varepsilon$, $\varepsilon'$ and integers $\gamma$, $\gamma'$, the *standard data* have $\sigma = 1$, row integer $\gamma$, column integer $\gamma' + n$, and variables indexed by $R \times C$ itself.

Lean: `New.FockDualPair.std` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

For the standard data, $E_{ab}$ acts on the rows by $\sum_c A_{ac}B_{bc} + \gamma\delta_{ab}$. By the column formula and $B_{ra}A_{rb} = A_{rb}B_{ra} + \delta_{ab}$, it acts on the columns by $-\sum_r A_{rb}B_{ra} + \gamma'\delta_{ab}$. The term $+n$ in the column integer cancels the $n$ constants of the reordering. These are the actions $h \mapsto (\det h)^\gamma\omega(x \mapsto hx)$ and $g \mapsto (\det g)^{\gamma'}\omega(x \mapsto xg^{-1})$ of Section 8.

**Example (One row and one column).** Let $n = n' = 1$, with both signs $1$, and take the standard data. There is one variable $X$, and it is positive. The row action is $E = X\partial + \gamma$ and the column action is $E' = -X\partial + \gamma'$. The monomial $X^k$ has row weight $\gamma + k$ and column weight $\gamma' - k$. So the row weight determines the column weight by $\nu + \nu' = \gamma + \gamma'$. This is the theta correspondence for $U(1) \times U(1)$.
