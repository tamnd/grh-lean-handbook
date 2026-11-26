---
title: The Casimir elements of the two groups
lean:
  - Lib/DiscreteSeries/Theta/CasimirComparison.lean
decls:
  - New.three_mul_sum_range_two_mul_sub_sq
  - New.three_mul_sum_sq_of_injOn
  - New.three_mul_sum_twoRho_sq
  - New.sum_twoRho_eq_zero
  - New.HCParam.HasGap.two_mul_sum_lowestKType
  - New.HCParam.HasGap.casimirValue_sub_centre
  - New.GlModule.centredCasimir
  - New.GlModule.centredCasimir_apply
  - New.FockDualPair.centre
  - New.FockDualPair.quarticOp
  - New.FockDualPair.quadraticOp
  - New.FockDualPair.lower_mul_raise
  - New.sum_mul_eq_normal_order
  - New.FockDualPair.oscRows_E_sub_centre
  - New.FockDualPair.swap_oscRows_E_sub_centre
  - New.FockDualPair.centredCasimir_oscRows
  - New.FockDualPair.centredCasimir_swap_oscRows
  - New.FockDualPair.centredCasimir_swap_oscRows_eq_add
  - New.FockDualPair.sum_centredParam_sq
  - New.IsMatch.three_mul_sum_sq_sub
  - New.IsMatch.centred_casimirValue_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Casimir elements of the two groups

The joint harmonic $\Phi$ is highest of weight $\Lambda'$ for the column action. To show that the second group fixes $\pi(e_\lambda)\Phi$ in Section 8, the source uses the fixed vector theorem of [discrete series through one matrix coefficient](/chapter/discrete-series/). That theorem needs the Casimir element of the second group to act by the Casimir value $\kappa_{\lambda'}$. The first group gives the Casimir value $\kappa_\lambda$ on the image of $\pi(e_\lambda)$. This section relates the two Casimir elements on the Fock space, and the two Casimir values for matching parameters. With the centres removed, both differ by the same constant $nn'(n - n')/4$.

In the textbook, this is a case of the correspondence of infinitesimal characters under the theta correspondence. The source cites it as "compare A. Paul, First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999), Theorem 2.11". The source proves it by a direct computation with the operators of the Fock model.

### Sums of squares

**Lemma.** For an integer $c$ and $d \geq 0$,
$$3\sum_{k < d}(2k - c)^2 = 2d(d - 1)(2d - 1) - 6cd(d - 1) + 3dc^2.$$

Lean: `New.three_mul_sum_range_two_mul_sub_sq` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* Induction on $d$. $\square$

**Lemma.** Let $f$ take $d$ distinct integer values on a set $s$ of size $d$, each of modulus less than $d$ and of the parity of $d - 1$. Then $3\sum_{i \in s} f(i)^2 = d(d^2 - 1)$.

Lean: `New.three_mul_sum_sq_of_injOn` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* The integers of modulus less than $d$ and of the parity of $d - 1$ are $1 - d, 3 - d, \ldots, d - 1$. There are $d$ of them, so the image of $f$ is this set. Apply the last lemma with $c = d - 1$. $\square$

Recall from [discrete series through one matrix coefficient](/chapter/discrete-series/) the vector $2\rho^{(r)}(l)$ for a relation $r$ on the indices: its entry $i$ is the number of $j$ with $r(i, j)$ and $l_j < l_i$, minus the number of $j$ with $r(i, j)$ and $l_i < l_j$. For the full relation it is $2\rho$, for the relation $\varepsilon_i = \varepsilon_j$ it is $2\rho_c$, and the lowest $K$-type is $\Lambda = \lambda + \rho - 2\rho_c$.

**Lemma.** Let the entries of $l$ be distinct, and let $N$ be the number of indices.
1. $3\sum_i (2\rho_i)^2 = N(N^2 - 1)$, that is, $|\rho|^2 = N(N^2 - 1)/12$.
2. For a symmetric relation $r$, the entries of $2\rho^{(r)}(l)$ sum to $0$.
3. If $l$ has a gap, then $2\sum_i \Lambda_i = \sum_i l_i$.

Lean: `New.three_mul_sum_twoRho_sq` (Lib/DiscreteSeries/Theta/CasimirComparison.lean). The other parts are `New.sum_twoRho_eq_zero` and `New.HCParam.HasGap.two_mul_sum_lowestKType`.

*Proof.* For part 1, the entry $2\rho_i$ is $\#\{j : l_j < l_i\} - \#\{j : l_i < l_j\}$, and the two counts add up to $N - 1$. So the entries are distinct, of modulus less than $N$ and of the parity of $N - 1$, and the last lemma applies. For part 2, both counts run over the same pairs of the relation, ordered by $l$. For part 3, write $\Lambda$ through the rounded vector $(l + 2\rho)/2$ and $2\rho_c$. The gap makes the entries of $l + 2\rho$ even, so there is no rounding. Part 2 for the full relation and for $\varepsilon_i = \varepsilon_j$ removes the terms of $\rho$ and $\rho_c$. $\square$

**Theorem.** Let $l = 2\lambda$ have a gap, with Casimir value $\kappa = |\lambda|^2 - |\rho|^2$ and lowest $K$-type $\Lambda$. Let $w$ be a complex number and $n$ the number of indices. Then
$$\kappa - 2w\sum_a \Lambda_a + nw^2 = \sum_a(\lambda_a - w)^2 - \frac{n(n^2 - 1)}{12}.$$

Lean: `New.HCParam.HasGap.casimirValue_sub_centre` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* Here $\kappa = \frac14\sum_a(l_a^2 - (2\rho_a)^2)$. Expand $(\lambda_a - w)^2$ and use parts 1 and 3 of the last lemma. $\square$

### Centred Casimir elements

**Definition (Centred Casimir element).** For a module $\rho$ of $\mathfrak{gl}_n$ and a scalar $w$, the *centred Casimir element* is
$$\Omega_w = \sum_{a,b}\bigl(\rho(E_{ab}) - w\delta_{ab}\bigr)\bigl(\rho(E_{ba}) - w\delta_{ba}\bigr).$$

Lean: `New.GlModule.centredCasimir` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

**Lemma.** If $\rho(E_{aa})v = \nu_a v$ for every $a$, then $\Omega_w v = \Omega v - 2w\bigl(\sum_a\nu_a\bigr)v + nw^2v$, where $\Omega = \sum_{a,b}\rho(E_{ab})\rho(E_{ba})$.

Lean: `New.GlModule.centredCasimir_apply` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* Expand the product. The cross terms give $-2w\sum_a\rho(E_{aa})$, and the constant is $nw^2$. $\square$

In Lean $\Omega$ is `ρ.casimirK 1`, the operator `New.GlModule.casimirK` for the signs all equal to $1$, so that every pair of indices counts.

**Definition (Centre).** The *centre* of the row action is $c_T = \gamma - n'/2$, where $\gamma$ is the integer on the diagonal of the row action and $n'$ is the number of columns. The centre of the column action is that of the swap, $c_{T'} = \gamma' - n/2$.

Lean: `New.FockDualPair.centre` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

Write $x_{rc}$ for the raising operator of the variable $(r, c)$ and $d_{rc}$ for its lowering operator: $x_{rc} = X_{rc}$ and $d_{rc} = \partial_{rc}$ for a positive variable, $x_{rc} = -\partial_{rc}$ and $d_{rc} = X_{rc}$ for a negative one. In Lean these are `New.FockDualPair.raise` and `New.FockDualPair.lower`.

**Lemma.** The operators satisfy $d_{rc}x_{r'c'} = x_{r'c'}d_{rc} + \delta_{rr'}\delta_{cc'}$, and the $d_{rc}$ commute.

Lean: `New.FockDualPair.lower_mul_raise` (Lib/DiscreteSeries/Theta/CasimirComparison.lean). The second part is `New.FockDualPair.lower_mul_lower`.

*Proof.* This is the canonical commutation relation of Section 2. $\square$

**Definition.** Put $D_4 = \sum_{a,b,c,c'} x_{ac}x_{bc'}d_{bc}d_{ac'}$ and $D_2 = \sum_{r,c} x_{rc}d_{rc}$.

Lean: `New.FockDualPair.quarticOp` (Lib/DiscreteSeries/Theta/CasimirComparison.lean). The second is `New.FockDualPair.quadraticOp`.

**Lemma (Normal ordering).** Let $x$, $d$ be arrays in a complex algebra with $d_{rc}x_{rc'} = x_{rc'}d_{rc} + \delta_{cc'}$. Then
$$\sum_{a,b}\Bigl(\sum_c x_{ac}d_{bc} + \tfrac{n'}{2}\delta_{ab}\Bigr)\Bigl(\sum_c x_{bc}d_{ac} + \tfrac{n'}{2}\delta_{ab}\Bigr) = D_4 + (n + n')D_2 + \frac{nn'^2}{4}.$$

Lean: `New.sum_mul_eq_normal_order` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* Move $d_{bc}$ past $x_{bc'}$ in the product of the two sums. The commutators give $nD_2$. The scalar $n'/2$ gives $n'D_2$ and the constant $n \cdot n'^2/4$. $\square$

**Lemma.** For rows $a$, $b$, let $s_{ab} = 1$ if $\varepsilon_a = \varepsilon_b$ and $s_{ab} = \sigma$ otherwise. Then
$$\rho(E_{ab}) - c_T\delta_{ab} = s_{ab}\Bigl(\sum_c x_{ac}d_{bc} + \tfrac{n'}{2}\delta_{ab}\Bigr).$$
For columns $a$, $b$, with $s'_{ab}$ defined in the same way from $\varepsilon'$,
$$\rho'(E_{ab}) - c_{T'}\delta_{ab} = -s'_{ab}\Bigl(\sum_r x_{rb}d_{ra} + \tfrac{n}{2}\delta_{ab}\Bigr).$$

Lean: `New.FockDualPair.oscRows_E_sub_centre` (Lib/DiscreteSeries/Theta/CasimirComparison.lean). The second part is `New.FockDualPair.swap_oscRows_E_sub_centre`.

*Proof.* The row action of $E_{ab}$ is $s_{ab}\sum_c x_{ac}d_{bc} + \gamma\delta_{ab}$, and $\gamma - c_T = n'/2$. For the columns, the column action of $E_{ab}$ is $-s'_{ab}\sum_r d_{ra}x_{rb} + \gamma'\delta_{ab}$, and $d_{ra}x_{rb} = x_{rb}d_{ra} + \delta_{ab}$. $\square$

**Theorem.** With the centres removed, the Casimir elements of the row action and of the column action are
$$\Omega_{c_T} = D_4 + (n + n')D_2 + \frac{nn'^2}{4}, \qquad \Omega'_{c_{T'}} = D_4 + (n + n')D_2 + \frac{n^2n'}{4}.$$
So $\Omega'_{c_{T'}} = \Omega_{c_T} + \frac{nn'(n - n')}{4}$.

Lean: `New.FockDualPair.centredCasimir_oscRows` (Lib/DiscreteSeries/Theta/CasimirComparison.lean). The others are `New.FockDualPair.centredCasimir_swap_oscRows` and `New.FockDualPair.centredCasimir_swap_oscRows_eq_add`.

*Proof.* Insert the last lemma into the definition of $\Omega_w$. The signs drop out, since $s_{ab}s_{ba} = 1$ (`New.FockDualPair.sign_mul_sign`). Normal ordering gives the first formula. For the columns, apply normal ordering with rows and columns exchanged. The quartic term is again $D_4$, because the $d_{rc}$ commute (`New.FockDualPair.sum_columns_eq_quarticOp`), and the quadratic term is again $D_2$. The two minus signs cancel in the products. The difference of the constants is $nn'(n - n')/4$. $\square$

The operators $D_4$ and $D_2$ are the same for the two groups. So the two centred Casimir elements differ by a scalar on the whole polynomial ring, not only on the joint harmonics.

### The Casimir values of matching parameters

**Lemma.** The centred parameters satisfy $\sum_r \xi_r^2 = 4\sum_r(\lambda_r - c_T)^2$.

Lean: `New.FockDualPair.sum_centredParam_sq` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* $\xi_r = l_r - 2\gamma + n' = 2(\lambda_r - c_T)$. $\square$

**Theorem.** Let $l$ and $l'$ match, and let $d_0 = n - n'$. Then
$$3\Bigl(\sum_r\xi_r^2 - \sum_c\xi'^2_c\Bigr) = d_0(d_0^2 - 1).$$

Lean: `New.IsMatch.three_mul_sum_sq_sub` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* First let $n' \leq n$ (`New.IsMatch.three_mul_sum_sq_sub_of_le`). Every column is matched, with a row $m(c)$, and $\xi_{m(c)} = -\xi'_c$. The map $m$ is injective, so the matched rows contribute $\sum_c\xi'^2_c$. The other $d_0$ rows are free: their $\xi_r$ are distinct, of modulus less than $d_0$, and of the parity of $d_0 - 1$. The lemma on sums of squares gives $3\sum\xi_r^2 = d_0(d_0^2 - 1)$ over them. For $n < n'$, apply this case to the swap. The right side $d_0(d_0^2 - 1)$ changes sign with $d_0$. $\square$

**Theorem (Comparison of Casimir values).** Let $l = 2\lambda$ and $l' = 2\lambda'$ match. Put $u = \lambda - c_T$ and $u' = \lambda' - c_{T'}$. Then
$$|u|^2 - \frac{n(n^2 - 1)}{12} + \frac{nn'(n - n')}{4} = |u'|^2 - \frac{n'(n'^2 - 1)}{12}.$$

Lean: `New.IsMatch.centred_casimirValue_eq` (Lib/DiscreteSeries/Theta/CasimirComparison.lean).

*Proof.* By the last two results, $12(|u|^2 - |u'|^2) = d_0(d_0^2 - 1)$. What remains is the identity $n^3 - n'^3 - d_0^3 = 3nn'd_0$, with $d_0 = n - n'$. $\square$

Section 8 uses the two theorems to pass from $\kappa_\lambda$ on the rows to $\kappa_{\lambda'}$ on the columns.

**Remark (Formalization).** All the identities of this section are equalities of operators on `MvPolynomial ι ℂ` or of complex numbers. The centres are complex numbers. Their values are integers or half integers, by the parity of $n'$ and $n$.
