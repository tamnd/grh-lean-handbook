---
title: Edges and halfway lattices
lean:
  - New/UpperBound/ElementaryDivisors/Edges.lean
  - New/UpperBound/ElementaryDivisors/InvariantAverage.lean
decls:
  - New.ParahoricCosets
  - New.FrobeniusCycle.depthScaling
  - New.FrobeniusCycle.exists_depthScaling_mul_letterRep_eq
  - New.FrobeniusCycle.allEdgesForms
  - New.FrobeniusCycle.IsEdgePairing
  - New.Average.exists_isAdjointWeight
  - New.FrobeniusCycle.exists_isEdgePairing
  - New.FrobeniusCycle.edgeRestriction
  - New.FrobeniusCycle.originFunctions
  - New.exists_mul_inv_eq_mul_diagonal
  - New.card_le_mul_finrank_of_dual_rows
  - New.prod_dvd_pow_sum_card
  - New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd
  - New.FrobeniusCycle.mulVec_mulVec_eq_self_of_mem_originFunctions
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Edges and halfway lattices

An edge $L' \subseteq L$ has a lattice between $L'$ and $L$ after one adjoins $w = \sqrt p$: the forms integral for $L' + wL$. This section puts these halfway lattices in coordinates, pairs them with the halfway lattices of the dual edge, and proves the first colength bound: the integral functions on origins have small colength in the functions on edges that depend only on the origin.

### Edges in coordinates

**Definition (Parahoric cosets).** $\mathrm{ParahoricCosets}(W, k, r)$ is the set of left cosets of $\mathrm{parahoric}(\mathrm{twoBlock}(k, r))$ in $\mathrm{GL}_k(W)$.

Lean: `New.ParahoricCosets` (New/UpperBound/ElementaryDivisors/Edges.lean).

The parahoric subgroup is the stabilizer of the sublattice $\mathfrak m_W^r \oplus W^{k-r}$ of $W^k$, which contains $\mathfrak m_W W^k$ with quotient of dimension $r$. So for $r \le k$ the cosets index the edges into $W^k$. Since matrices act transposed, the same cosets index the edges from a lattice, and that is how they are used. Over $k_W$ with $q$ elements their number is the Gaussian binomial $\binom{k}{r}_q$ ([finite general linear groups](/chapter/finite-gln/)).

Choose a basis $z$ of the origin $L'$ adapted to the edge. The forms that are integral for $L' + wL$, times $w^{-Nn/2}$, have the basis $w^{-\mathrm{depth}(\beta)} z^\beta$. This module is the halfway lattice of the edge. The chapter works with coefficients in these normalized monomials.

**Definition (Depth scaling).** $\Delta$ is the diagonal matrix on $\mathrm{Exp}$ with entries $w^{\mathrm{depth}(\beta)}$.

Lean: `New.FrobeniusCycle.depthScaling` (New/UpperBound/ElementaryDivisors/Edges.lean).

So $\Delta h$ are the normalized coefficients of the integral form $h$. The matrix $\Delta$ is the Kronecker product over the letters of the symmetric powers of the diagonal matrices with $w$ at the deep variables and $1$ elsewhere (`New.FrobeniusCycle.depthScaling_eq_kroneckerPi`).

**Lemma (The stabilizer keeps the halfway lattice).** If $u \in \mathrm{parahoric}(\mathrm{twoBlock}(k, r))$, then $\Delta\rho(u) = A\Delta$ for a matrix $A$ over $O$.

Lean: `New.FrobeniusCycle.exists_depthScaling_mul_letterRep_eq` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* Work in one letter $s$, with $D_s$ the diagonal matrix with $w^{\epsilon(b)}$, $\epsilon$ the deep indicator. The entry $(i, j)$ of $D_su_s$ is $w^{\epsilon(i)}(u_s)_{ij}$. It is divisible by $w^{\epsilon(j)}$: this is clear if $\epsilon(j) \le \epsilon(i)$. If $\epsilon(j) = 1 > \epsilon(i) = 0$, then $j$ is deep and $i$ is not. For $s$ even this means $i < r \le j$, so $u_{ij} \in \mathfrak m_W$; for $s$ odd it means $j < r \le i$, so the entry $(j, i)$ of $u^{-1}$ is in $\mathfrak m_W$, as $u^{-1}$ is also parahoric. In both cases $(u_s)_{ij} = \iota_s(y)$ with $y \in \mathfrak m_W$, and $p \mid \iota_s(y)$ (`New.FrobeniusCycle.p_dvd_embedding_of_mem_maximalIdeal`). For this, go once around the cycle: $p \mid \iota_s(y) - \iota_s(y)^q$. Then $\iota_s(y) - \iota_s(y)^q = \iota_s(y)\,\iota_s(1 - y^{q-1})$, and $1 - y^{q-1}$ is a unit of $W$. So $w^2 \mid (u_s)_{ij}$. Write $D_su_s = A_sD_s$ with $A_s$ integral. Then $\Delta\rho(u) = \bigotimes_s \mathrm{Sym}^n(D_su_s) = \bigotimes_s\mathrm{Sym}^n(A_s)\cdot\Delta$. $\square$

In the same way, $\Delta$ commutes with $\rho(g)$ for $g$ in the Levi subgroup, because then $(g_s)_{ij} = 0$ unless $i$, $j$ lie in the same block (`New.FrobeniusCycle.commute_depthScaling_letterRep`).

**Definition (Forms in all halfway lattices).** $\mathrm{allEdgesForms}(k, n, r)$ is the set of $v : \mathrm{Exp} \to O$ such that for some $m$ and some $h : \mathrm{Exp} \to O$ one has $w^m v = \Delta h$ and $w^m \mid (\Delta\rho(g)h)_\beta$ for all $g \in \mathrm{GL}_k(W)$ and all $\beta$.

Lean: `New.FrobeniusCycle.allEdgesForms` (New/UpperBound/ElementaryDivisors/Edges.lean).

Read $v$ as the normalized coefficients, in one edge, of the form $w^{-m}h$. Every edge from the origin has an adapted basis in which the form becomes a translate by some $g$, and the condition says that all these normalized coefficients are integral. Every $\Delta h$ with $h$ integral lies in this module (take $m = 0$).

### The pairing of an edge with its dual

**Definition (Edge pairing).** Weights $b, b' : \mathrm{Exp} \to O$ form an edge pairing if $b_\beta\,\rho(g^{\mathsf T})_{\beta\alpha} = b_\alpha\,\rho(g)_{\alpha\beta}$ for all $g, \alpha, \beta$, and $b_\beta b'_\beta = p^{Nc_0}$ for all $\beta$.

Lean: `New.FrobeniusCycle.IsEdgePairing` (New/UpperBound/ElementaryDivisors/Edges.lean).

For $\langle h, h'\rangle = \sum_\beta h'_\beta b_\beta h_\beta$ the first condition says $\langle\rho(g)h, h'\rangle = \langle h, \rho(g^{\mathsf T})h'\rangle$, and the second that every linear form, times $p^{Nc_0}$, is a pairing with a vector (`New.FrobeniusCycle.IsEdgePairing.dotProduct_letterRep_mulVec`, `New.FrobeniusCycle.IsEdgePairing.pairing_mul_eq_pow_mul_dotProduct`).

The textbook pairing on polynomials is the apolar pairing $\langle x^\alpha, x^\beta\rangle = [\alpha = \beta]\,\alpha!$, for which substitution by $A$ and by $A^{\mathsf T}$ are adjoint. Its restriction to the divided powers is perfect. Over $O$ one wants a pairing that is perfect up to a bounded power of $p$, so one divides by the multinomial coefficient instead of multiplying by a factorial.

**Lemma (Adjoint weights).** Let $O$ be a valuation domain of characteristic zero, $p$ a prime that is not a unit of $O$, $\sigma$ a finite set and $f \in \mathbb N$. There are weights $\eta(\gamma) \in O$ on monomials in $\sigma$ such that $p^{|\sigma| f} = \binom{|\gamma|}{\gamma}\eta(\gamma)$ whenever $|\gamma| < p^f$, and such that for every matrix $A$ and all $\alpha$, $\beta$:

$$\mathrm{coeff}_\alpha\big(A\cdot x^\beta\big)\,\eta(\alpha) = \eta(\beta)\,\mathrm{coeff}_\beta\big(A^{\mathsf T}\cdot x^\alpha\big).$$

Lean: `New.Average.exists_isAdjointWeight` (New/UpperBound/ElementaryDivisors/InvariantAverage.lean).

*Proof.* A multinomial coefficient of degree below $p^f$ with $|\sigma|$ parts is a product of $|\sigma|$ binomial coefficients $\binom{m}{j}$ with $m < p^f$, and each divides $p^f$ in $O$ (Kummer: its $p$-adic valuation is the number of carries, at most $f$). So put $\eta(\gamma) = p^{|\sigma| f}/\binom{|\gamma|}{\gamma}$ for $|\gamma| < p^f$ and $\eta(\gamma) = 0$ otherwise. The apolar identity $\alpha!\,\mathrm{coeff}_\alpha(Ax^\beta) = \beta!\,\mathrm{coeff}_\beta(A^{\mathsf T}x^\alpha)$ holds over $\mathbb Z$ (`New.Average.prod_factorial_mul_coeff_linSubst`). Both sides vanish unless $|\alpha| = |\beta|$. For $|\alpha| = |\beta| = d < p^f$, divide by $d!$ and multiply by $p^{|\sigma|f}$; division is allowed since $O$ is a domain of characteristic zero. For $d \ge p^f$ both sides are $0$. $\square$

**Remark (Formalization).** The value $\eta(\gamma) = 0$ in degree at least $p^f$ is a junk value. It makes the adjointness trivial there. Only degrees $n < q$ are used, and there $\eta$ is the true quotient.

**Lemma (Existence of the pairing).** If $p$ is not a unit of $O$ and $n < q$, an edge pairing exists.

Lean: `New.FrobeniusCycle.exists_isEdgePairing` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* Take $\eta = b_0$ from the lemma with $\sigma = \{0,\dots,k-1\}$ and $f$ replaced by $fN$, so $p^{fN} = q > n$. Put $u = p^{(k-1)kfN}$, $b_\beta = \prod_s u\,b_0(\beta_s)$ and $b'_\beta = \prod_s\binom{n}{\beta_s}$. Then $u\,b_0(\beta_s)\binom{n}{\beta_s} = p^{(k-1)kfN + kfN} = p^{c_0}$, and the product over the $N$ letters is $p^{Nc_0}$. For adjointness, $g^{\mathsf T}$ has letter matrix $(g_s)^{\mathsf T}$ in both parities. The lemma gives the identity in each letter, and the Kronecker product multiplies them. $\square$

### Functions on edges

Let $X$ be a finite set (the origins) and $E$ a finite set of edges, with origin $\mathrm{src}(e) \in X$ and a basis change $g(e) \in \mathrm{GL}_k(W)$ to a basis adapted to $e$.

**Definition (Restriction to edges).** The matrix $\mathrm{edgeRestriction}$ from $X \times \mathrm{Exp}$ to $E \times \mathrm{Exp}$ sends $\varphi$ to $e \mapsto \Delta\rho(g(e))\varphi(\mathrm{src}(e))$.

Lean: `New.FrobeniusCycle.edgeRestriction` (New/UpperBound/ElementaryDivisors/Edges.lean).

**Definition (Origin functions).** $\mathrm{originFunctions}$ is the module of $\psi$ on $E \times \mathrm{Exp}$ such that $w^m\psi = \mathrm{edgeRestriction}\,\varphi$ for some $m$ and some integral $\varphi$.

Lean: `New.FrobeniusCycle.originFunctions` (New/UpperBound/ElementaryDivisors/Edges.lean).

If every edge occurs, that is, $e \mapsto (\mathrm{src}(e), g(e)^{-1}\,\mathrm{parahoric})$ is onto $X \times \mathrm{ParahoricCosets}$, then each value $\psi(e)$ of an origin function lies in $\mathrm{allEdgesForms}$ (`New.FrobeniusCycle.apply_mem_allEdgesForms`). The proof writes any $\gamma$ as $u\,g(e)$ with $u$ parahoric and $\mathrm{src}(e)$ the given origin, and uses the lemma on the stabilizer.

### Three facts of linear algebra

**Lemma (Elementary divisors of a tall matrix).** Let $O$ be a valuation domain and $J$ a matrix with rows $I'$ and columns $I$, with an embedding $I \hookrightarrow I'$. There are $Q$ (shape of $J$), $R$ with $RQ = 1$, $P \in \mathrm{GL}_I(O)$ and $t : I \to O$ with $JP^{-1} = Q\,\mathrm{diag}(t)$.

Lean: `New.exists_mul_inv_eq_mul_diagonal` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* The Hermite form gives $U \in \mathrm{GL}_{I'}(O)$ and a square $D$ with $J = U|_{I}D$, where $U|_I$ keeps the columns of $U$ in the image of $I$. The Smith form gives $D = K\,\mathrm{diag}(t)P$ with $K$, $P$ invertible. Put $Q = U|_IK$ and $R = K^{-1}(U^{-1})|^I$, the rows of $U^{-1}$ in the image of $I$. Then $RQ = K^{-1}K = 1$ and $JP^{-1} = Q\,\mathrm{diag}(t)$. $\square$

The textbook Smith form over a principal ideal domain gives $D = K\,\mathrm{diag}(t)P$ with $t_1 \mid t_2 \mid \cdots$ (Lang, *Algebra*, Chapter III, Section 7).

**Remark (Formalization).** The Smith form of the source (`New.IsValuationPair.smith_normal_form`) states no divisibility among the $t_i$. This is finding F-063 of the [register of findings](/chapter/register-of-findings/). The argument of this chapter does not need the chain $t_1 \mid t_2 \mid \cdots$: it uses each $t_i$ alone, through the divisibilities $t_i \mid w^x$ and the count of the $t_i$ with $t_i \nmid w^\delta$ below.

**Lemma (Dual rows).** Let $O$ be local, $Q$ a matrix with rows $X \times I$ and columns $E$, and $R$ with columns $X \times I$. Let $s \subseteq E$ be such that column $j \in s$ of $RQ$ is the $j$-th unit vector, and that for each $j \in s$ and $x \in X$ the block $i \mapsto Q_{(x,i),j}$ reduces into a subspace $S$ over the residue field. Then $|s| \le |X|\dim S$.

Lean: `New.card_le_mul_finrank_of_dual_rows` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* The reductions of the columns $j \in s$ lie in $S^X$. They are independent: from $\sum_j c_j\bar Q_{\cdot j} = 0$, pair with the reduction of row $i$ of $R$ and get $c_i = 0$. $\square$

**Lemma (Counting divisibilities).** If $t_i \mid w^x$ for all $i$, then $\prod_i t_i \mid w^l$ with $l = \sum_{\delta < x}\#\{i : t_i \nmid w^\delta\}$.

Lean: `New.prod_dvd_pow_sum_card` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* Let $l_i$ be the least $l$ with $t_i \mid w^l$; then $l_i \le x$ and $l_i = \#\{\delta < l_i\} \le \#\{\delta < x : t_i \nmid w^\delta\}$. Multiply over $i$ and exchange the sums. $\square$

### Origin functions form a summand of small colength

**Theorem.** Let $O$ be a valuation domain. Assume every edge occurs, and all depths are at most $x$. There are $Q$, $R$, $d$ with $Q\varphi \in \mathrm{originFunctions}$ for every $\varphi$, $RQ = 1$, $Qd = \mathrm{edgeRestriction}$, and

$$\det d \;\Big|\; w^{\,|X|\sum_{\delta < x}\dim \mathrm{deepForms}(k,n,r,\delta+1)},$$

where the deep forms are taken for the Frobenius cycle reduced to the residue field of $O$.

Lean: `New.FrobeniusCycle.exists_originFunctions_factorization_det_dvd` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* Every origin has an edge, so $X \times \mathrm{Exp}$ embeds in $E \times \mathrm{Exp}$. Apply the lemma on tall matrices to $J = \mathrm{edgeRestriction}$: $JP^{-1} = Q\,\mathrm{diag}(t)$ with $RQ = 1$. Put $d = \mathrm{diag}(t)P$, so $Qd = J$.

*Step 1.* Column $i$ of $JP^{-1}$ is $t_i$ times column $i$ of $Q$, so $t_i$ divides every coefficient of $J$ applied to column $i$ of $P^{-1}$. As every edge occurs, $t_i$ divides $w^{\mathrm{depth}(\beta)}(\rho(\gamma)P^{-1}_{(y,\cdot),i})_\beta$ for all $y$, $\gamma$, $\beta$.

*Step 2.* With $\gamma = 1$: $t_i \mid w^{\mathrm{depth}(\beta)}P^{-1}_{(y,\beta),i}$, hence $t_i \mid w^xP^{-1}_{(y,\beta),i}$ for all $(y, \beta)$. Summing against row $i$ of $P$ gives $t_i \mid w^x$.

*Step 3.* Write $w^x = t_it'_i$. Then $w^xQ\varphi = Q\,\mathrm{diag}(t)\,\mathrm{diag}(t')\varphi = J(P^{-1}\mathrm{diag}(t')\varphi)$, so $Q\varphi$ is an origin function.

*Step 4.* If $t_j \nmid w^\delta$, then column $j$ of $P^{-1}$, as a function of $y$, is deep of depth $\delta + 1$ modulo $\mathfrak m_O$: at any $\beta$ with $\mathrm{depth}(\beta) \le \delta$, a unit value of $(\rho(\gamma)P^{-1}_{(y,\cdot),j})_\beta$ would give $t_j \mid w^{\mathrm{depth}(\beta)} \mid w^\delta$ by Step 1. Since $PP^{-1} = 1$, the lemma on dual rows gives $\#\{j : t_j \nmid w^\delta\} \le |X|\dim\mathrm{deepForms}(\delta + 1)$.

*Step 5.* $\det d$ is a unit times $\prod t_j$. Counting divisibilities and Step 4 give the bound. $\square$

**Lemma.** Let $O$ be a domain of characteristic zero, $RQ = 1$ and $Qd = \mathrm{edgeRestriction}$. Then $QR\psi = \psi$ for every origin function $\psi$.

Lean: `New.FrobeniusCycle.mulVec_mulVec_eq_self_of_mem_originFunctions` (New/UpperBound/ElementaryDivisors/Edges.lean).

*Proof.* If $w^m\psi = Qd\varphi$, then $w^mQR\psi = QRQd\varphi = Qd\varphi = w^m\psi$. Cancel $w^m \ne 0$. $\square$

So the origin functions are the direct summand $Q(O^{X\times\mathrm{Exp}})$, and the integral functions on origins, mapped in by $\mathrm{edgeRestriction} = Qd$, have colength dividing $\det d$ in it. Section 4 bounds the exponent.
