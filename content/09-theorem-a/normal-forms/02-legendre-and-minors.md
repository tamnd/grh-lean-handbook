---
title: Legendre's bound, minors and the chain rule
lean:
  - New/Derivatives/Divisibility/Count.lean
decls:
  - New.norm_prod_factorial_le
  - New.norm_jet_le_of_isHomogeneous
  - New.minorProd
  - New.DirectionVar
  - New.card_directionVar_le
  - New.directionSubst
  - New.columnDetProd
  - New.isHomogeneous_columnDetProd
  - New.jet_columnDetProd_subst
  - New.norm_jet_columnDetProd_subst
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Legendre's bound, minors and the chain rule

This section collects the three tools of the count that do not involve the normal form. The first is a lower bound for the valuation of a jet of an integral series. The second is the polynomial along which the jets are taken: a product of minors. The third is a change of variables that turns this product of minors into a product of determinants of new variables, together with the chain rule for jets under the change.

### Legendre's bound

Legendre's formula gives $v_p(m!) = (m - s_p(m))/(p-1)$, where $s_p(m)$ is the sum of the digits of $m$ in base $p$. A number $m < p^{K}$ has at most $K$ digits, each at most $p - 1$, so

$$\frac{m}{p-1} - (1 + \lfloor \log_p m \rfloor) \le v_p(m!) \le \frac{m}{p-1}.$$

The source has this as `New.padicValNat_factorial_mem_Icc` in the algebra of [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/). For a multi-index we apply it to each exponent.

**Lemma (Legendre's bound).** Let $\sigma$ be a finite set and $\alpha \colon \sigma \to \mathbb{N}$ a multi-index of degree $l = \sum_x \alpha_x$. Then

$$v\Big(\prod_{x \in \sigma} \alpha_x!\Big) \ge \frac{l}{p-1} - |\sigma|\,(\lfloor \log_p l \rfloor + 1).$$

Lean: `New.norm_prod_factorial_le` (New/Derivatives/Divisibility/Count.lean).

*Proof.* For each $x$ we have $\alpha_x \le l < p^{\lfloor \log_p l\rfloor + 1}$, so the bound above gives $\alpha_x/(p-1) - v_p(\alpha_x!) \le \lfloor \log_p l \rfloor + 1$. Add over the $|\sigma|$ elements $x$; the sum of the $\alpha_x$ is $l$. The norm of $\prod_x \alpha_x!$ in $\mathbb{C}_p$ is $p$ to the power $-\sum_x v_p(\alpha_x!)$. $\square$

**Lemma (Legendre's bound for jets).** Let $G$ be a power series over $\mathbb{C}_p$ in the variables $\sigma$ whose coefficients of degree $l$ are integral. Let $Q$ be a homogeneous polynomial of degree $l$ with integral coefficients. Then

$$v\big(\mathrm{jet}(Q)(G)\big) \ge \frac{l}{p-1} - |\sigma|\,(\lfloor \log_p l \rfloor + 1).$$

Lean: `New.norm_jet_le_of_isHomogeneous` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The jet is $\sum_\alpha Q_\alpha\, \alpha!\, G_\alpha$, a sum over the monomials of $Q$, all of degree $l$. Each term has valuation at least $v(\alpha!)$, since $Q_\alpha$ and $G_\alpha$ are integral. The valuation of a sum is at least the least valuation of its terms. The previous lemma bounds $v(\alpha!)$. $\square$

Two features of this bound matter later. Only the coefficients of degree exactly $l$ have to be integral, and the loss is proportional to the number $|\sigma|$ of variables, not to the degree. The count arranges that the number of variables does not depend on the degree $B$: it is at most $fN^3$.

### Products of minors

Let $\Phi$ be a finite set of places, and let $n$ and $n'$ be finite sets with $N = |n'|$. The variables are the entries $z_{\tau,b,a}$ of matrices $z_\tau$ of size $n' \times n$, one for each place. A *diagram* at $\tau$ is given by the numbers $\kappa_\tau(h)$ of its columns of height $h$. A standard filling $i'$ of the diagrams by elements of $n'$ ([integral Weyl modules and branching](/chapter/weyl-modules/)) puts a row $i'_\tau(h, j, b) \in n'$ into the box $b < h$ of the column $j < \kappa_\tau(h)$ of height $h$.

**Definition (Product of minors).** Let $y_\tau$ be matrices with rows indexed by $n$ and columns indexed by $\mathbb{N}$, with entries in a ring $R$. The *product of minors* is

$$P_y = \prod_{\tau \in \Phi}\ \prod_{h < N}\ \prod_{j < \kappa_\tau(h)} \det\Big( \sum_{a \in n} y_{\tau,a,k}\, z_{\tau,\, i'_\tau(h,j,b),\, a} \Big)_{b,k < h}.$$

So the factor of a column of height $h$ is the minor of $z_\tau y_\tau$ on the $h$ rows of the column and on the first $h$ columns.

Lean: `New.minorProd` (New/Derivatives/Divisibility/Count.lean).

**Remark (Formalization).** The product runs over the heights $h < N$ only. A column of height $N$ or more is not part of $P_y$, and its boxes are not counted in $B$. In the applications the diagrams satisfy $|n| \le |n'|$ and have no column of height strictly between $|n|$ and $|n'|$ (Section 5), so the columns that are left out have the full height $N$.

### New variables

The count substitutes for the variables $z$ linear forms in new variables. There is one new variable $s_{\tau,h,k,b}$ for each place $\tau$, each height $h < N$, each direction $k < h$ and each row $b \in n'$. The set of these indices is the *direction set*.

Lean: `New.DirectionVar` (New/Derivatives/Divisibility/Count.lean).

**Lemma (Size of the direction set).** The direction set has at most $f N^3$ elements, where $f = |\Phi|$ and $N = |n'|$.

Lean: `New.card_directionVar_le` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The pairs $(h, k)$ with $k < h < N$ number $\sum_{h<N} h \le N \cdot N$. Multiply by $|\Phi| = f$ and $|n'| = N$. $\square$

This is the source of the factor $N^3$ in the loss of the count. The exact number of pairs is $N(N-1)/2$, so the true count of new variables is $fN^2(N-1)/2$; the source uses the simpler bound.

**Definition (The substitution).** Let $c_{\tau,h,b}$ be row factors and $\beta_{\tau,h,k}$ vectors in $R^n$, the *directions*. The substitution $z(s)$ sets

$$z_{\tau,b,a} = \sum_{h < N}\ \sum_{k < h} c_{\tau,h,b}\, \beta_{\tau,h,k,a}\, s_{\tau,h,k,b}.$$

So the row $b$ of $z_\tau$ is a combination of the directions, and only the new variables of the same place and the same row enter.

Lean: `New.directionSubst` (New/Derivatives/Divisibility/Count.lean).

The transposed substitution of polynomials, `New.linSubst`, sends $s_{\tau,h,k,b}$ to $c_{\tau,h,b} \sum_a \beta_{\tau,h,k,a}\, z_{\tau,b,a}$; this is `New.linSubst_directionSubst_X`. The jets of a linearly substituted series are the jets of the series along the transposed polynomial (`New.jet_subst_linearSeries`, in [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/)).

**Definition (Product of column determinants).** The polynomial $P_*$ in the new variables is

$$P_* = \prod_{\tau}\ \prod_{h < N}\ \prod_{j < \kappa_\tau(h)} \det\big(s_{\tau,h,k,\, i'_\tau(h,j,b)}\big)_{b,k<h}.$$

Lean: `New.columnDetProd` (New/Derivatives/Divisibility/Count.lean).

**Lemma.** The polynomial $P_*$ is homogeneous of degree $B = \sum_\tau \sum_{h<N} h\,\kappa_\tau(h)$, the number of boxes in the columns of height below $N$. Its coefficients are integers.

Lean: `New.isHomogeneous_columnDetProd` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Each determinant of size $h$ in the variables is a sum of signed products of $h$ variables, so it is homogeneous of degree $h$. A product of homogeneous polynomials is homogeneous, of the sum of the degrees. $\square$

### The chain rule

The new directions in the count are combinations of the given directions $y_\tau$. For each place $\tau$ and height $h$ let $g_{\tau,h}$ be an $h \times h$ matrix, and set

$$\beta_{\tau,h,k,a} = \sum_{k' < h} (g_{\tau,h})_{k,k'}\, y_{\tau,a,k'}.$$

These are the *new directions* (`New.newDirection`, Section 3).

**Lemma (Chain rule).** Let $F$ be a power series in the variables $z$ over a ring $R$. With the substitution $z(s)$ for the row factors $c$ and the new directions $\beta$ above,

$$\mathrm{jet}(P_*)\big(F(z(s))\big) = \Big(\prod_\tau \prod_{h<N} \prod_{j<\kappa_\tau(h)} \det(g_{\tau,h}) \prod_{b<h} c_{\tau,h,i'_\tau(h,j,b)}\Big) \cdot \mathrm{jet}(P_y)(F).$$

Lean: `New.jet_columnDetProd_subst` (New/Derivatives/Divisibility/Count.lean).

*Proof.* By the rule for linear substitutions, the left side is the jet of $F$ along the transposed polynomial, which is $P_*$ with each $s_{\tau,h,k,b}$ replaced by $c_{\tau,h,b} \sum_a \beta_{\tau,h,k,a} z_{\tau,b,a}$. Take one column, of height $h$ at $\tau$, with rows $I(b) = i'_\tau(h,j,b)$. Its matrix $(s_{\tau,h,k,I(b)})_{b,k}$ goes to

$$\mathrm{diag}\big(c_{\tau,h,I(b)}\big)_b \cdot \Big(\sum_a y_{\tau,a,k}\, z_{\tau,I(b),a}\Big)_{b,k} \cdot g_{\tau,h}^{T},$$

because $\sum_a \beta_{\tau,h,k,a} z_{\tau,I(b),a} = \sum_{k'} (g_{\tau,h})_{k,k'} \sum_a y_{\tau,a,k'} z_{\tau,I(b),a}$. The determinant of this product is $\prod_b c_{\tau,h,I(b)}$ times the minor of the column times $\det g_{\tau,h}$. Take the product over all columns and use the linearity of the jet in the polynomial. $\square$

In the count, $R$ is the ring $\mathcal{O}$, the row factors are powers $p^{w}$ of $p$ (the charges), and the substitution is also scaled by the number $\varpi$ of the normal form. In norms the chain rule then reads as follows.

**Lemma (Chain rule in norms).** Let $w_{\tau,h,b} \in \mathbb{N}$, let $g_{\tau,h}$ be integral matrices, $y$ integral directions, $\varpi \in \mathbb{C}_p$ and $F$ a series over $\mathbb{C}_p$. Let $G = F(\varpi z(s))$ for the row factors $p^{w}$ and the new directions. Then

$$\|\mathrm{jet}(P_*)(G)\| = \|\varpi\|^{B}\, p^{-m} \prod_\tau \prod_{h<N} \|\det g_{\tau,h}\|^{\kappa_\tau(h)} \cdot \|\mathrm{jet}(P_y)(F)\|,$$

where $m = \sum_\tau \sum_{h<N} \sum_{j<\kappa_\tau(h)} \sum_{b<h} w_{\tau,h,i'_\tau(h,j,b)}$ is the *filling charge*.

Lean: `New.norm_jet_columnDetProd_subst` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The factor $\varpi$ is a row factor of every box, so it gives $\varpi^B$. Each box contributes $p^{w}$ for its row, and the product of these has norm $p^{-m}$. The determinant of $g_{\tau,h}$ appears once for each of the $\kappa_\tau(h)$ columns of height $h$. Apply the chain rule and take norms. $\square$

The filling charge is `New.fillingCharge`. It depends only on the values $w_{\tau,h,b}$ at the heights that occur in the diagrams (`New.fillingCharge_congr`), and it is $0$ for $w = 0$ (`New.fillingCharge_zero`).

### What remains

The plan of the count is now visible. If the coefficients of degree $B$ of $G = F(\varpi z(s))$ are integral, then Legendre's bound gives

$$v\big(\mathrm{jet}(P_*)(G)\big) \ge \frac{B}{p-1} - fN^3(\lfloor\log_p B\rfloor + 1),$$

and the chain rule in norms turns this into a lower bound for $v(\mathrm{jet}(P_y)(F))$, after subtracting $B\rho_p$, the charge $m$ and the valuations of the determinants. The integrality of $G$ in degree $B$ comes from the normal form, once the couplings of $z(s)$ are divisible by $\pi_p$. Section 3 chooses the matrices $g_{\tau,h}$ that make this true, and bounds their determinants.
