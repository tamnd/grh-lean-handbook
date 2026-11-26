---
title: Existence of joint harmonics
lean:
  - Lib/DiscreteSeries/Theta/LocalCorrespondence.lean
decls:
  - New.derivation_prod_det
  - New.IsLayering
  - New.IsLayering.polarisation_prod_det
  - New.IsLayering.isKHighest_and_isTermwiseHarmonic
  - New.IsLayering.isJointHighest_prod_det
  - New.IsMatch.exists_isMatchedPair_of_relWeight_ne_zero
  - New.IsMatch.exists_isMatchedPair_of_outer
  - New.FockDualPair.Layer
  - New.IsMatch.isLayering
  - New.IsMatch.exists_isJointHarmonic
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Existence of joint harmonics

This section builds a joint harmonic for every pair of matching parameters. The joint harmonic is a product of minors of the matrix of variables. Each minor belongs to a *layer*, a set of matched pairs of rows and columns. The layers are chosen so that the product has the right weight and is killed by the compact raising operators.

Fix data $T$ and matching parameters $l$, $l'$ as in Section 3. Write $w_r$ for the weight of row $r$ relative to the vacuum and $\eta_{rc}$ for the sign of the variable $X_{rc}$.

### Polarisations

**Definition (Polarisation).** For rows $a$, $b$, a sign $s$ and a polynomial $P$, the *polarisation* from row $b$ to row $a$ in the variables of sign $s$ is
$$D^s_{ab}P = \sum_{c\,:\,\eta_{bc} = s} X_{ac}\,\partial_{bc}P.$$

Lean: `New.FockDualPair.polarisation` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

The operator $D^s_{ab}$ is a derivation of the polynomial ring. On a matrix of variables it replaces the entries $X_{bc}$ of row $b$ with $\eta_{bc} = s$ by the entries $X_{ac}$ of row $a$. For rows of equal sign, the row action is a difference of two polarisations:
$$\rho(E_{ab})P = D^{+}_{ab}P - D^{-}_{ba}P + \delta_{ab}\,v(\varepsilon_a)\,P \qquad (\varepsilon_a = \varepsilon_b).$$
This is `New.Fischer.oscRows_E_eq_polarisation_sub`. For a positive variable, $A_{ac}B_{bc} = X_{ac}\partial_{bc}$. For a negative variable, $A_{ac}B_{bc} = -\partial_{ac}X_{bc} = -X_{bc}\partial_{ac} - \delta_{ab}$, and the constants $-\delta_{ab}$ add up to the vacuum weight.

**Lemma.** Let $D$ be a derivation of a polynomial ring, and let $M_t$ be finitely many square matrices of polynomials. Suppose that $D$ acts on the columns of each $M_t$ by a matrix $N_t$: $D(M_t)_{ki} = \sum_j (N_t)_{ij}(M_t)_{kj}$. Then
$$D\Bigl(\prod_t \det M_t\Bigr) = \Bigl(\sum_t \operatorname{tr} N_t\Bigr)\prod_t \det M_t.$$

Lean: `New.derivation_prod_det` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* By the Leibniz rule, $D(\det M)$ is the sum over $i$ of the determinant with column $i$ replaced by its image under $D$. That image is a combination of the columns, and only its component along column $i$ survives in the determinant. So $D(\det M_t) = (\operatorname{tr} N_t)\det M_t$. The Leibniz rule for the product gives the claim. $\square$

### Layerings

**Definition (Layering).** A *layering* of weight $\nu$ for $l$ is a finite family of layers $t$. Each layer is a finite set $I_t$ with maps $\rho_t : I_t \to R$ and $\kappa_t : I_t \to C$, and the following hold.
1. The rows $\rho_t(i)$ of a layer are distinct.
2. If two layers $t$, $u$ share a row, then all columns of $t$ and of $u$ have one sign.
3. A layer is *closed*: if it contains the row $\rho = \rho_t(i)$ and the variable $(\rho, \kappa_t(i))$ has sign $s$, then it contains every row $r$ with $\varepsilon_r = \varepsilon_\rho$ and $s(l_r - l_\rho) > 0$.
4. For every row $r$, $\nu_r = v(\varepsilon_r) + \sum \eta_{r\kappa_t(i)}$, the sum over all $(t, i)$ with $\rho_t(i) = r$.

Lean: `New.IsLayering` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

The *minor* of a layer $t$ is $\det\bigl(X_{\rho_t(i)\kappa_t(j)}\bigr)_{i,j \in I_t}$.

**Lemma.** Let $(\rho, \kappa)$ be a layering of weight $\nu$, and let $P$ be the product of the minors of its layers. Let $\varepsilon_a = \varepsilon_b$, and let $a = b$ or $s\,l_b < s\,l_a$. Then $D^s_{ab}P = N\,P$, where $N$ is the number of pairs $(t, i)$ with $\rho_t(i) = a = b$ and $\eta_{b\kappa_t(i)} = s$.

Lean: `New.IsLayering.polarisation_prod_det` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* The polarisation is a derivation, so the lemma on derivations of products of determinants applies, with the minors written as transposed matrices. In each layer, $D^s_{ab}$ sends the row $b$ of the minor to the row $a$ if the variables of row $b$ in the layer have sign $s$, and it kills the other rows. If $a \neq b$ and row $b$ is in the layer with sign $s$, then row $a$ is further out than $b$ in the direction $s$, so row $a$ is in the layer by closedness. The new matrix has two equal rows, and its determinant is $0$. If $a = b$, the polarisation multiplies the minor by the number of its rows equal to $b$ of sign $s$. $\square$

**Theorem.** Let $(\rho, \kappa)$ be a layering of weight $\nu$ for $l$, and let $P$ be the product of the minors of its layers. Then $P$ is $K$-highest of weight $\nu$ for the row action and the order of $l$, and $P$ is termwise harmonic for the swap.

Lean: `New.IsLayering.isKHighest_and_isTermwiseHarmonic` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Let $\varepsilon_a = \varepsilon_b$. By the formula for $\rho(E_{ab})$, the operator is $D^{+}_{ab} - D^{-}_{ba}$ plus the vacuum term. If $l_b < l_a$, the lemma applies to $D^{+}_{ab}$ and to $D^{-}_{ba}$ (since $-l_a < -l_b$), and both counts are $0$ because $a \neq b$. So $\rho(E_{ab})P = 0$. For $a = b$, the two counts differ by the sum of the signs $\eta_{a\kappa_t(i)}$ over the pairs with $\rho_t(i) = a$, so $\rho(E_{aa})P = \nu_a P$ by condition 4. A monomial of $P$ with two variables in one row from columns of opposite signs would come from two layers that share a row and have columns of opposite signs. Condition 2 excludes this. $\square$

**Theorem.** Let $(\rho, \kappa)$ be a layering of weight $\nu$ for $l$ and $T$, and let $(\kappa, \rho)$ be a layering of weight $\nu'$ for $l'$ and the swap. Then the product of the minors of the layers is jointly highest of weights $\nu$, $\nu'$.

Lean: `New.IsLayering.isJointHighest_prod_det` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* The last theorem applies to both layerings. The minors of the swap are the transposes of those of $T$, so the products agree. Each minor is the generic determinant in distinct variables, so it is not zero, and the product is not zero. $\square$

### The layers of a matching

**Lemma.** Let $l$ and $l'$ match. If $w_r \neq 0$, then row $r$ is matched with a column $c$, and $\eta_{rc}$ is the sign of $w_r$.

Lean: `New.IsMatch.exists_isMatchedPair_of_relWeight_ne_zero` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* If $r$ is not matched, then $|\xi_r| < n - n'$, so both $n' - n < \xi_r$ and $n' - n < -\xi_r$. By the sign lemma of Section 3, $w_r \geq 0$ and $-w_r \geq 0$, so $w_r = 0$. If $r$ is matched with $c$, then $\eta_{rc}\xi_r > |n - n'| \geq n' - n$, so $\eta_{rc}w_r \geq 0$ by the same lemma. $\square$

**Lemma.** Let row $r$ be matched with column $c$ and let $w_r \neq 0$. Let $r'$ be a row with $\varepsilon_{r'} = \varepsilon_r$ and $\eta_{rc}(l_{r'} - l_r) > 0$. Then $r'$ is matched with a column $c'$ with $\varepsilon'_{c'} = \varepsilon'_c$, and $|w_r| \leq |w_{r'}|$.

Lean: `New.IsMatch.exists_isMatchedPair_of_outer` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* By the first lemma, $\eta_{rc}$ is the sign of $w_r$. The gap condition makes the lowest $K$-type dominant for the order of $l$, so $\Lambda_{r'} \geq \Lambda_r$ if $l_{r'} > l_r$, and $\Lambda_{r'} \leq \Lambda_r$ if $l_{r'} < l_r$. The rows have the same sign, so they have the same vacuum weight, and $\eta_{rc}w_r \leq \eta_{rc}w_{r'}$. So $w_{r'}$ is not zero, it has the sign of $w_r$, and $|w_r| \leq |w_{r'}|$. The first lemma applied to $r'$ gives a column $c'$ matched with $r'$, with $\eta_{r'c'}$ the sign of $w_{r'}$. So $\eta_{r'c'} = \eta_{rc}$. As $\varepsilon_{r'} = \varepsilon_r$, this gives $\varepsilon'_{c'} = \varepsilon'_c$. $\square$

**Definition (Layers of a matching).** Give the variable $X_{rc}$ the height $h_{rc} = |w_r|$ if $(r, c)$ is matched and $h_{rc} = 0$ if not. Fix a permutation $\tau$ of the set of pairs of signs. For a level $m$ below the largest height and a pair of signs $(u, u')$, the layer of $(m, u, u')$ is the set of variables $X_{rc}$ with $m < h_{rc}$ and $\tau(\varepsilon_r, \varepsilon'_c) = (u, u')$. Its rows and columns are those of its variables.

Lean: `New.FockDualPair.Layer` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean). The rows and columns are `New.FockDualPair.layerRow` and `New.FockDualPair.layerCol`.

A layer contains only matched pairs, all in one quadrant of signs. The layers of one quadrant are nested.

**Theorem.** Let $l$ and $l'$ match. Then for every permutation $\tau$ of the pairs of signs, the layers of the matching form a layering of weight $\Lambda$, the lowest $K$-type of $l$.

Lean: `New.IsMatch.isLayering` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Condition 1 holds since a row is matched with at most one column. For condition 2, a row $r$ lies only in layers that contain its matched variable $(r, c)$, so all these layers have columns of the sign of $c$. Condition 3 is the second lemma: an outer row $r'$ is matched with a column of the same sign, and its height is at least that of $r$, so it lies in every layer of $r$. For condition 4, a matched row $r$ lies in exactly $|w_r|$ layers, those of levels $m < |w_r|$. Each contributes the sign $\eta_{rc}$, which is the sign of $w_r$ by the first lemma. So the sum is $w_r$, and $v(\varepsilon_r) + w_r = \Lambda_r$. A row with $w_r = 0$ lies in no layer. $\square$

**Theorem (Existence of joint harmonics).** If $l$ and $l'$ match for $T$, there is a joint harmonic $\Phi$ for $T$, $l$, $l'$.

Lean: `New.IsMatch.exists_isJointHarmonic` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Take the heights of the matching and $\tau = 1$. The layers form a layering of weight $\Lambda$ for the rows. The matching for the swap has the same matched pairs, and the heights agree, because $|w_r| = |w'_c|$ for a matched pair by `New.IsMatch.relWeight_eq_neg`. The swap reads the pair of signs as $(\varepsilon'_c, \varepsilon_r)$, so with $\tau$ the exchange of the two signs, the same layers form a layering of weight $\Lambda'$ for the columns. The product of the minors is jointly highest of weights $\Lambda$ and $\Lambda'$. $\square$

The docstring of the theorem calls it "the existence part of the known correspondence of discrete series by joint harmonics". The source builds them by hand.

**Remark (Formalization).** The source states the lemma on polarisations of products of minors with the transposed matrices, because the lemma on derivations acts on columns. The existence theorem states only the existence of $\Phi$. The global argument takes a joint harmonic by `Classical.epsilon` in `New.jointHarmonicAt` (Lib/Weil/Lift.lean), an arbitrary polynomial if none exists. By Section 5, the chosen polynomial is a nonzero multiple of the product of minors when the parameters correspond.

### Example

**Example (The pair $U(1,1) \times U(1)$).** Continue the example of Section 3. Row 1 is matched with the column and has height $w_1 = k$. Row 2 is free. So there are $k$ layers, each with the single variable $X_1$, and $\Phi = X_1^k$. The row operators are $E_{11} = X_1\partial_1 + \gamma$ and $E_{22} = -X_2\partial_2 - 1 + \gamma$, so $\Phi$ has row weight $(\gamma + k, \gamma - 1) = \Lambda$. The column operator is $E' = X_2\partial_2 - X_1\partial_1 + \gamma' + 1$, so $\Phi$ has column weight $\gamma' + 1 - k = \Lambda'$. There are no compact raising operators, since the two rows have opposite signs and there is one column. The polynomial has no variable of row 2, so it is termwise harmonic.
