---
title: From Schur entries to products of minors
lean:
  - New/Derivatives/Divisibility/Count.lean
decls:
  - New.exists_norm_le_norm_sum_mul_eval
  - New.minorProd_eq_sum
  - New.exists_norm_schurJet_le_norm_jet_minorProd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## From Schur entries to products of minors

The later chapters need the divisibility of the jets along the entries of a Schur matrix, not along products of minors. This section shows that each such jet is bounded by the jet along one product of minors $P_y$, with integral $y$. Then the count of Section 4 applies to it.

### The Schur matrix

Recall from [integral Weyl modules and branching](/chapter/weyl-modules/) the Schur matrix $S_\kappa(z)$ of a family of matrices $z_\tau$ of size $n' \times n$. Its rows are indexed by the standard fillings $i'$ of the diagrams $\kappa$ by the rows $n'$, and its columns by the standard fillings $i$ by $n$. Let $b'_{i'}$ be the product of minors for the filling $i'$ and $b_i$ the same for $i$, both as polynomials in a matrix of variables $y$. Let $\det^{d}$ be the product over the places of the determinant of the first $|n|$ columns of $y_\tau$ to the power $d_\tau$, where $d_\tau = \kappa_\tau(|n|)$ if $|n| < |n'|$ and $d_\tau = 0$ otherwise. The row $i'$ of $S_\kappa(z)$ holds the coordinates of $b'_{i'}(zy)$ in the family $b_i(y) \det^{d}(y)$:

$$b'_{i'}(zy) = \sum_i S_\kappa(z)_{i',i}\; b_i(y)\, \det{}^{d}(y).$$

This holds under the condition `FitsRanks`: $|n| \le |n'|$, and $\kappa$ has no column of height strictly between $|n|$ and $|n'|$ (`New.sum_schur_smul_nablaBasis`, in the same chapter). The matrix of jets is $\mathrm{schurJet}_\kappa(F)_{i',i} = \mathrm{jet}(S_\kappa(z)_{i',i})(F)$ (`New.schurJet`).

**Remark (Formalization).** The Lean definition `New.schur` picks the coordinates with `Function.invFun`. Without the condition `FitsRanks` the coordinates need not exist, and the row is then a value that the source does not specify. All statements of this section assume `FitsRanks`, under which the coordinates exist and are unique, since the family $b_i \det^d$ is linearly independent.

### The expansion of a product of minors

**Lemma (Expansion).** Assume `FitsRanks`. For the filling $i'$ and any $y$ with entries in a commutative ring,

$$P_y = \sum_i \big(b_i\det{}^{d}\big)(y)\; S_\kappa(z)_{i',i},$$

where $P_y$ is the product of minors of Section 2, a polynomial in the variables $z$.

Lean: `New.minorProd_eq_sum` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The product of minors $P_y$ is $b'_{i'}$ evaluated at the matrix $zy$, with the given $y$ as constants: the minor of $z_\tau y_\tau$ on the rows of a column and its first $h$ columns is the minor of $b'_{i'}$ at that column. Evaluate the identity that defines the Schur matrix at $y$. $\square$

So, as $F$ is fixed and $y$ varies, the jet along $P_y$ is a combination of the entries of the row $i'$ of the matrix of jets:

$$\mathrm{jet}(P_y)(F) = \sum_i \mathrm{schurJet}_\kappa(F)_{i',i}\; \big(b_i\det{}^{d}\big)(y).$$

To bound a single entry by such a combination, choose $y$ so that the other entries cannot cancel the one wanted.

### Choosing the point

**Lemma (A point where a combination is large).** Let $b_t$, for $t$ in a finite set, be polynomials over $\mathcal{O}$ whose reductions are linearly independent over the residue field $k$ of $\mathcal{O}$. For all $\alpha_t \in \mathbb{C}_p$ and every index $t_1$, there is an integral point $y$ with

$$\|\alpha_{t_1}\| \le \Big\|\sum_t \alpha_t\, b_t(y)\Big\|.$$

Lean: `New.exists_norm_le_norm_sum_mul_eval` (New/Derivatives/Divisibility/Count.lean).

*Proof.* Choose $t_0$ with $\|\alpha_{t_0}\|$ largest. If $\alpha_{t_0} = 0$, all $\alpha_t$ are zero and any $y$ will do. Otherwise put $\beta_t = \alpha_t/\alpha_{t_0}$; these are integral and $\beta_{t_0} = 1$. The polynomial $\sum_t \beta_t b_t$ has a reduction modulo the maximal ideal that is not zero, because the reductions of the $b_t$ are linearly independent and the coefficient of $b_{t_0}$ reduces to $1$. The residue field $k$ is algebraically closed, because $\mathbb{C}_p$ is algebraically closed and $\mathcal{O}$ is integrally closed in it. So $k$ is infinite, and a polynomial over $k$ that is not zero has a point $x$ where its value is not zero. Lift $x$ to an integral point $y$. Then $\sum_t \beta_t b_t(y)$ is a unit of $\mathcal{O}$, and

$$\Big\|\sum_t \alpha_t b_t(y)\Big\| = \|\alpha_{t_0}\| \cdot \Big\|\sum_t \beta_t b_t(y)\Big\| = \|\alpha_{t_0}\| \ge \|\alpha_{t_1}\|. \qquad \square$$

The point $y$ depends on the numbers $\alpha_t$. In the application they are the jets of a fixed series $F$, so this is not a problem.

### The Schur entries

**Theorem (A Schur entry is bounded by a product of minors).** Assume `FitsRanks`. For every power series $F$ in the variables $z_{\tau,b,a}$ over $\mathbb{C}_p$ and every pair of fillings $(i', i)$ there are integral matrices $y_\tau$ with

$$\big\|\mathrm{schurJet}_\kappa(F)_{i',i}\big\| \le \big\|\mathrm{jet}(P_y)(F)\big\|.$$

In valuations, $v(\mathrm{schurJet}_\kappa(F)_{i',i}) \ge v(\mathrm{jet}(P_y)(F))$.

Lean: `New.exists_norm_schurJet_le_norm_jet_minorProd` (New/Derivatives/Divisibility/Count.lean).

*Proof.* The polynomials $b_t \det^{d}$ are linearly independent over every commutative ring (`New.GL.linearIndependent_nablaBasis_mul_detPow`, in [integral Weyl modules and branching](/chapter/weyl-modules/)), in particular over $k$. Their reductions are the same polynomials over $k$, since their coefficients are integers. Apply the previous lemma to $\alpha_t = \mathrm{schurJet}_\kappa(F)_{i',t}$ and $t_1 = i$. This gives integral $y$ with $\|\alpha_i\| \le \|\sum_t \alpha_t (b_t \det^d)(y)\|$, and the sum is $\mathrm{jet}(P_y)(F)$ by the expansion. $\square$

**Remark (Formalization).** The matrices $y_\tau$ of the theorem are only asserted to exist, and they depend on $F$ and on $(i', i)$. Every bound of Section 4 holds for all integral $y$, so the choice does not matter there. The variables of $y$ in Lean are indexed by a place, a coordinate of $n$ and a natural number $k$, the column of $y_\tau$. Only the columns $k < |n'|$ enter $P_y$, so the other columns are free.

### The use in the count

Combine the theorem with the count of Section 4. For $F$ with the normal form and every entry,

$$v\big(\mathrm{schurJet}_\kappa(F)_{i',i}\big) \ge D_p(\kappa) - fN^3\big(1 + \log_p \max(B,1)\big),$$

and the same with charges. The bound is uniform in $(i', i)$, because the bound of the count is uniform in $y$. Section 8 states it for the theta series of standard data, after the normal form is proved for them in Section 7.

**Example.** Let $|n| = 1$, $|n'| = 2$, and let $\kappa$ have $B$ columns of height one at one place $\tau$ and nothing else. The condition `FitsRanks` holds, since no height lies strictly between $1$ and $2$. Only heights below $|n| = 1$ count for $n$, so there is one filling $i$ and $b_i = 1$, while $d_\tau = \kappa_\tau(1) = B$ and $\det^d(y) = y_0^B$, with $y_0$ the first entry of $y_\tau$. A filling $i'$ by the two rows puts row $1$ into $j$ boxes and row $2$ into $B - j$ boxes. With $z_\tau = (z_1, z_2)^T$, the product of minors is $P_y = (z_1 y_0)^j (z_2 y_0)^{B-j}$, so the entry of the Schur matrix is $z_1^j z_2^{B-j}$, and the jet along $P_y$ is $y_0^B$ times the Schur entry. The lemma chooses $y_0$ to be a unit, and then the two norms are equal.
