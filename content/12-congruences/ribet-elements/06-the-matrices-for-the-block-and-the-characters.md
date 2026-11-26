---
title: The matrices for the block and the characters
lean:
  - New/Congruences/FirstOrder/FittingBlock.lean
  - New/Congruences/FirstOrder/RibetMatrices.lean
decls:
  - New.Selmer.ribetCocyclesVanishingOn
  - New.Selmer.mem_ribetCocyclesVanishingOn
  - New.Selmer.exists_block_rows
  - New.Selmer.exists_tiedRows_addVal_det_le
  - New.Selmer.rankOneRep
  - New.Selmer.IsCharacterCocycle
  - New.Selmer.IsDetectedBy
  - New.Selmer.isCharacterCocycle_of_mem_formsMod
  - New.Selmer.isCharacterCocycle_of_tiedRows
  - New.Selmer.mem_map_tiedRows_iff
  - New.Selmer.tie_mem_map_tiedRows
  - New.Selmer.exists_unit_row
  - New.Selmer.exists_common_unit_row
  - New.Selmer.exists_unit_rows_mem_tiedRows
  - New.Selmer.exists_row_apply_eq_zero
  - New.Selmer.exists_mem_fittingIdeal_character
  - New.Selmer.exists_sum_mul_det_of_mem_fittingIdeal_evalRowAtChar
  - New.Selmer.exists_rows_det_eq_pow_mul_det
  - New.Selmer.exists_relations_det_eq_pow_mul_det
  - New.Selmer.det_map_polyChar_tame_rows
  - New.Selmer.CharacterRows
  - New.Selmer.nonempty_characterRows
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The matrices for the block and the characters

The Ribet element of a matrix $B$ of tied rows has the value $\mu_0 \det(\tilde\psi_x B) \prod_e \det(\tilde\eta_e B)$ on $\mathcal{X}$. This section makes the two kinds of factor small. For the main summand $\rho$, it finds tied rows whose determinant at $X = 0$ has valuation at most the length $b_0$ of a module of cocycles. For each character $\xi_e$, it finds tied rows whose determinants combine to $\Gamma_e \prod_{\mathrm{ty}(j) = e} X_j$, with $v(\Gamma_e(0))$ at most the triangle cost. The notation is that of [Tied rows](/chapter/ribet-elements/#tied-rows).

### Background for the matrices

- For an $O$-module $B$, $\mathrm{Coc}(\rho, B)$ is the $O$-module of the $c : G \to B^r$ with $c(gh) = c(g) + \rho(g)c(h)$ for all $g, h$, and with $\sum_g \theta_g c(g) = 0$ for every finitely supported $\theta : G \to O$ with $\sum_g \theta_g(u_x(g) - 1) = 0$ for all $x$. For $B = O/p$ it is written $\mathrm{Coc}(\rho, p)$. The definition lives in [The main summands of the attached Galois representations](/chapter/main-summands/), a later chapter, because that chapter uses the same modules for the local loss.
- Let $O$ be a discrete valuation ring with fraction field $K$, and $\psi : A \to M_d(O)$ a surjective map of $O$-algebras. If an $O$-module of vectors over $(K/O)^d$ of length at most $b$ contains every vector that $\psi(N)$ kills, then some square matrix $B$ with rows in $N$ has $v(\det \psi(B)) \leq b$ ([Block determinants](/chapter/fitting-ideals/#block-determinants)).
- The forms modulo $p$, the triangle cost and the Fitting bound with the factor $\prod_{j \in I} X_j$ are in [Fitting ideals and the triangle cost](/chapter/ribet-elements/#fitting-ideals-and-the-triangle-cost).

### The block of the main summand

**Definition (Cocycles vanishing on a set).** For a set $T \subseteq G$ and $\gamma \in G$, $\mathrm{Coc}_T(\rho, B)$ is the set of $c \in \mathrm{Coc}(\rho, B)$ with $c(g) = 0$ for $g \in T$ and $c(\gamma) = 0$.

Lean: `New.Selmer.ribetCocyclesVanishingOn`, `New.Selmer.mem_ribetCocyclesVanishingOn` (New/Congruences/FirstOrder/FittingBlock.lean).

**Theorem (Rows for the block).** Let $O$ be a discrete valuation ring and $\rho : G \to M_r(O)$ a representation whose matrices span $M_r(O)$. Let $\psi_0 : A \to M_r(O)$ be a map of $O$-algebras with $\psi_0(g) = \rho(g)$, and let $m \mapsto \underline{m}$ send $O^\iota$ to $A^\iota$ with $\psi_0(\underline{m}_j) = m_j$. Let $N \subseteq A^\iota$ be a submodule that contains the rows of the cocycle rule, the rows $\underline{z(\mathrm{gen}_i)} - e_i$ and the rows $\underline{\sum_g \theta_g z(g)}$ of the linear relations. Suppose also that for each $k$ and for $\gamma$, some row of $N$ has the same image under $\psi_0$ as $\underline{z(\tau_k)}$, and as $\underline{z(\gamma)}$. If $\operatorname{len} \mathrm{Coc}_{\{\tau_k\}}(\rho, K/O) \leq b_0$, then some square matrix $B_0$ with rows in $N$ has $v(\det \psi_0(B_0)) \leq b_0$.

Lean: `New.Selmer.exists_block_rows` (New/Congruences/FirstOrder/FittingBlock.lean).

*Proof.* The map $\psi_0$ is onto, as its image contains the $\rho(g)$. Apply the divisible form of the background. Let $w \in ((K/O)^r)^\iota$ be killed by $\psi_0(N)$, and let $\Psi(m) = \sum_j m_j w_j$. A row $t \in N$ with $\psi_0(t) = \psi_0(\underline{m})$ gives $\Psi(m) = 0$. The rows of the cocycle rule give $\Psi(z(gh)) = \Psi(z(g)) + \rho(g)\Psi(z(h))$. The rows $\underline{z(\mathrm{gen}_i)} - e_i$ give $\Psi(z(\mathrm{gen}_i)) = w_i$. The linear relations give $\sum_g \theta_g \Psi(z(g)) = 0$. The last hypothesis gives $\Psi(z(\tau_k)) = 0$ and $\Psi(z(\gamma)) = 0$. So $\Psi \circ z \in \mathrm{Coc}_{\{\tau_k\}}(\rho, K/O)$, and $w$ is its restriction to the generators. The module of these restrictions has length at most $b_0$. $\square$

**Corollary.** In the set-up of tied rows, let $\rho(\gamma) = y \cdot 1$ with $c_1(y - 1) = 1$, let $z$ be coordinates, and let $\rho_0$ be the tied normaliser. If $\operatorname{len} \mathrm{Coc}_{\{\tau_k\}}(\rho, K/O) \leq b_0$, then some square matrix $B_0$ of tied rows has $v(\det \tilde\rho_0(B_0)) \leq b_0$.

Lean: `New.Selmer.exists_tiedRows_addVal_det_le` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Take $A = R[G]$, $\psi_0 = \tilde\rho_0$ and $N$ the tied rows. The rows of the theorem are tied by the proposition on tied rows from coordinates. At $X = 0$, the tie row $\underline{z(\tau_k)} - X_j\,\varepsilon_j(\varphi_k)\,\underline{z(\varphi_k)}$ has the image of $\underline{z(\tau_k)}$. The row of $\gamma$ is the lemma on the row of $\gamma$ at $X = 0$. $\square$

### Cocycles for a character

Fix a character $\xi$ with $\xi(\gamma) = 1$, and generators $\delta_w$ on $W$ and $\mathrm{gen}'_i$ on $\iota'$.

**Definition (Character cocycle).** Let $\xi$ be a character, viewed as a representation of degree $1$. A function $c : G \to O/p$ is a character cocycle for $\xi$, $\delta$, $\gamma$ and $a$ if $c \in \mathrm{Coc}(\xi, O/p)$, $c(\delta_w) = 0$ for all $w$, and $c(\gamma) = 0$ implies $(\xi(g) - 1)c(a) = 0$ for all $g$. A module $Z$ of functions is detected by a finite set $s$ if each $c \in Z$ that vanishes on $s$ is $0$.

Lean: `New.Selmer.rankOneRep`, `New.Selmer.IsCharacterCocycle`, `New.Selmer.IsDetectedBy` (New/Congruences/FirstOrder/FittingBlock.lean).

**Lemma.** Let $\Phi : O^n \to R'^{\iota}$ be linear and $N$ a submodule. Suppose $N$ contains the images under $\Phi$ of $z(gh) - z(g) - \xi(g)z(h)$, of the $z(\delta_w)$, of the linear relations, and of $(\xi(g) - 1)(c_1 z(\gamma) + z(a))$. Then every form modulo $p$ for $\Phi$, $z$ and $N$ is a character cocycle.

Lean: `New.Selmer.isCharacterCocycle_of_mem_formsMod` (New/Congruences/FirstOrder/FittingBlock.lean).

*Proof.* Let $c = \Psi \circ z$ with $\Psi$ zero on $\Phi^{-1}(N)$. Apply $\Psi$ to each vector. This gives the cocycle rule, $c(\delta_w) = 0$ and the relations. The last vector gives $(\xi(g) - 1)(c_1 c(\gamma) + c(a)) = 0$, which is the third condition when $c(\gamma) = 0$. $\square$

**Proposition.** Read the tied rows on $\xi$, forgetting the coordinates in $W$, and apply a linear map $A$. Let $K$ contain the image. Then every form modulo $p$ that kills the vectors sent into $K$ is a character cocycle. Also, a row $b$ on $\iota'$ lies in the image of the tied rows if and only if $\langle (0, b) \rangle$ lies in the sum of the tie ideal, the values of the rows with entries in $\ker\tilde\xi$, and the values of the rows supported on $W$.

Lean: `New.Selmer.isCharacterCocycle_of_tiedRows`, `New.Selmer.mem_map_tiedRows_iff` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Apply the lemma with $\Phi = A \circ \xi_* \circ \underline{\cdot}$. On $\xi$ the cocycle row $\underline{z(gh) - z(g)} - g\,\underline{z(h)}$ becomes $z(gh) - z(g) - \xi(g)z(h)$. The row $\underline{z(\delta_w)} - e_w$ is tied, and $\xi_*$ forgets $e_w$. On $\xi$, the row $(g - 1)\nu$ becomes $(\xi(g) - 1)(c_1 z(\gamma) + z(a))$, as $\xi(\gamma) = 1$. For the second claim, a row differs from one of the form $(0, b)$, with the same image, by a row with entries in $\ker\tilde\xi$ off $W$ and arbitrary entries on $W$. $\square$

**Lemma (Ties on a character).** If $p$ divides $\varepsilon_j(\xi(\varphi_k)) - 1$, then $A\xi_*\underline{z(\tau_k)} - X_j\,A\xi_*\underline{z(\varphi_k)}$ lies in the image of the tied rows.

Lean: `New.Selmer.tie_mem_map_tiedRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* On $\xi$ the factor $\varepsilon_j(\varphi_k)$ is $1 + pc$. The tie row reads as the claimed vector minus $pc\,X_j\,\xi_*\underline{z(\varphi_k)}$. The row $p\,c\,X_j\,\underline{z(\varphi_k)}$ is tied, as $p$ times a row. Add it. $\square$

### Unit rows

The coordinates on $s_0$ are eliminated by rows that are unit vectors there.

**Lemma (Unit rows).** Let $\eta$ be a character of $A$, $p \neq 0$, and let $N$ contain $p$ times every row and the rows $\underline{z(\mathrm{gen}_i)} - e_i$, where $\mathrm{gen}$ is the inclusion on $s$. Suppose the forms modulo $p$ for the $s_0$-part of the image are detected by $s$. Then for each $i \in s_0$ some row of $N$ is, under $\eta$, the unit vector $i$ on $s_0$. If this holds for finitely many characters $\eta_e$ separately, then one row does it for all $e$ at once.

Lean: `New.Selmer.exists_unit_row`, `New.Selmer.exists_common_unit_row` (New/Congruences/FirstOrder/FittingBlock.lean).

*Proof.* For the first claim, take a form $\Psi$ that kills the image. For $g \in s$ the unit row at $g$ has no $s_0$-coordinates, so $\Psi(z(g)) = 0$. By detection $\Psi \circ z = 0$, so $\Psi$ kills $z(\mathrm{gen}_i)$. By duality, the image of $\underline{z(\mathrm{gen}_i)}$ lies in that of $N$. Modulo $N$ this row is $e_i$. For the second claim, correct the row one character at a time. If $w$ works for the earlier characters and $w'$ for $\eta_e$, a combination of $w$, $w'$ and the earlier unit rows, with coefficients chosen on $\eta_e$, keeps the earlier values. $\square$

**Corollary.** If every module of character cocycles for each $\xi_e$ is detected by $s$, there are tied rows $\nu_i$, $i \in s_0$, with $\tilde\xi_e(\nu_i)$ the unit vector $i$ on $s_0$ for every $e$. Subtracting multiples of the $\nu_i$ turns any $w \in N$ into a $w' \in N$ that is zero on $s_0$ under $\eta$ and whose $s$-part is $(\eta w)_s - \sum_i (\eta w)_i (\eta \nu_i)_s$.

Lean: `New.Selmer.exists_unit_rows_mem_tiedRows`, `New.Selmer.exists_row_apply_eq_zero` (New/Congruences/FirstOrder/RibetMatrices.lean, New/Congruences/FirstOrder/FittingBlock.lean).

*Proof.* The forms modulo $p$ are character cocycles by the proposition above, so $s$ detects them. Apply the lemma on unit rows. For the second claim, put $w' = w - \sum_i \eta(w_i)\,\nu_i$. $\square$

### The Fitting block of one character

Let the generators be the Ribet generators on $W \sqcup s_0 \sqcup s$. Give each $j \in J$ a type $\mathrm{ty}(j) \in \{0, \ldots, t - 1\}$, monotone in $j$. Let $\mathfrak{n}$ be the ideal of the monomials that do not divide $\prod_j X_j$.

**Theorem (Fitting block of one character).** Let $O$ be a discrete valuation ring and $p \neq 0$. Suppose $\xi_e(\gamma) = 1$, $p \mid \varepsilon_j(\xi_e(\varphi_k)) - 1$ for all $k$, and every module of character cocycles for $\xi_e$ has triangle cost $b_e$ along $\{j : \mathrm{ty}(j) = e\}$ with the constant $C$. Let $\nu_i$ be any rows, and let $K_e$ be the image of the tied rows on $\xi_e$, with the $s_0$-part eliminated by the $\nu_i$. Then some $\Gamma_e \in R$ with $v(\Gamma_e(0)) \leq b_e + (\#\{\mathrm{ty}(j) = e\} + \#s)v(C)$ has $\Gamma_e \prod_{\mathrm{ty}(j) = e} X_j \in \operatorname{Fitt}\big(K_e + (\mathfrak{n} : \prod_{\mathrm{ty}(j) < e} X_j) R^s\big)$.

Lean: `New.Selmer.exists_mem_fittingIdeal_character` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Apply the Fitting bound with $I = \{\mathrm{ty}(j) = e\}$ to the module $K$ in the statement. Its forms are character cocycles, so the triangle cost holds. The multiples of $p$ lie in $K$. The unit rows on $s$ are tied. The ties hold by the lemma on ties on a character. For $i < j$ with $\mathrm{ty}(j) = e$, either $\mathrm{ty}(i) = e$, or $\mathrm{ty}(i) < e$ and $X_i$ lies in the colon ideal, so $X_i R^s \subseteq K$. $\square$

**Lemma.** An element $d$ of the Fitting ideal of $K_e$ is $\sum_i w_i \det B_i$, where each row of each $B_i$ lifts to a tied row that is zero on $s_0$ under $\xi_e$ and is that row on $s$.

Lean: `New.Selmer.exists_sum_mul_det_of_mem_fittingIdeal_evalRowAtChar` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Write $d$ as a combination of determinants of matrices with rows in $K_e$. Lift each row to a tied row, and clear its $s_0$-part by the corollary on unit rows. $\square$

### Gluing the characters

Elements $\pi_e$ that separate the characters do this.

**Proposition (Gluing).** Let $\chi_e : A \to \Lambda$ be characters and $\pi_e \in A$ with $\chi_{e'}(\pi_e) = \mu_e$ if $e' = e$ and $0$ otherwise. Let $N \subseteq A^{\iota_0 \sqcup \iota}$, let some row of $N$ be under each $\chi_e$ the unit vector $i$ on $\iota_0$, and let each row of $B_e$ be the $\iota$-part under $\chi_e$ of a row of $N$ that is zero on $\iota_0$. Then a square matrix $M$ with rows in $N$ has $\det \chi_e(M) = \mu_e^{\#\iota} \det B_e$ for all $e$. The same holds for relations among generators $y$ of a module modulo $\ker\chi_e$.

Lean: `New.Selmer.exists_rows_det_eq_pow_mul_det`, `New.Selmer.exists_relations_det_eq_pow_mul_det` (New/Congruences/FirstOrder/FittingBlock.lean).

*Proof.* The rows on $\iota_0$ are common unit rows, by the lemma on unit rows. The row $l$ on $\iota$ is $\sum_e \pi_e w_{e,l}$, where $w_{e,l}$ gives row $l$ of $B_e$. Under $\chi_e$ this row is $\mu_e$ times row $l$ of $B_e$, and zero on $\iota_0$. So $\chi_e(M)$ is block triangular with diagonal blocks $1$ and $\mu_e B_e$. For relations, the relations are the kernel of $f \mapsto \sum_k f_k y_k$, and an element of $\ker(\chi_e) \cdot C$ is such a sum with coefficients in $\ker\chi_e$. $\square$

**Example (Two characters, one row).** Let $\iota_0$ be empty and $\iota$ one point. Let $w_1, w_2 \in N$ with $\chi_1(w_1) = b_1$ and $\chi_2(w_2) = b_2$. Put $M = (\pi_1 w_1 + \pi_2 w_2)$. Then $\chi_1(M) = \mu_1 b_1$, since $\chi_1(\pi_2) = 0$. In the same way $\chi_2(M) = \mu_2 b_2$. One row of $N$ has the two values that the characters ask for.

**Lemma.** Let $\xi(\delta_w) = 1$ for all $w$. Complete rows $L_k$ by the rows with the entry $o_w(\delta_w)$ at $w$ and $0$ elsewhere. Then the determinant on $\xi$ is $\prod_w o_w(1)$ times the determinant on $\xi$ of the $L_k$ without the coordinates in $W$.

Lean: `New.Selmer.det_map_polyChar_tame_rows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* On $\xi$ the added rows are $o_w(1)$ times unit vectors, so the matrix is block triangular. $\square$

**Definition (Character rows).** Character rows consist of: weights $w_{e,i} \in R$ and matrices $B_{e,i}$ over $R$ on $s$, for $i < n_e$; a matrix $M_\mathbf{i}$ of tied rows on $W \sqcup s_0 \sqcup s$ for each choice $\mathbf{i} = (i_e)_e$; and $\Gamma_e$, $d_e$, $\zeta_e \in R$. They satisfy $\det \tilde\xi_e(M_\mathbf{i}) = c_0 \det B_{e, i_e}$ with $c_0 = C^{\#s} \prod_w o_w(1)$, $\sum_i w_{e,i} \det B_{e,i} = d_e$, $d_e + \zeta_e = \Gamma_e \prod_{\mathrm{ty}(j) = e} X_j$, $\zeta_e \in (\mathfrak{n} : \prod_{\mathrm{ty}(j) < e} X_j)$, and $v(\Gamma_e(0)) \leq b_e + (\#\{\mathrm{ty}(j) = e\} + \#s)v(C)$.

Lean: `New.Selmer.CharacterRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

**Theorem (Character rows exist).** Suppose the hypotheses of the Fitting block hold for every $e$, $\xi_e(\delta_w) = 1$, $o_w(X)(X - 1)$ kills every $u_x(\delta_w)$, every module of character cocycles is detected by $s$, and $q_e \in R[G]$ has $\tilde\xi_{e'}(q_e) = C$ if $e' = e$ and $0$ otherwise. Then character rows exist.

Lean: `New.Selmer.nonempty_characterRows` (New/Congruences/FirstOrder/RibetMatrices.lean).

*Proof.* Take the unit rows $\nu_i$ of the corollary. For each $e$, the Fitting block gives $\Gamma_e$, and the colon ideal gives $\zeta_e$ with $d_e = \Gamma_e \prod X_j - \zeta_e$ in the Fitting ideal of $K_e$. The lemma on the Fitting ideal of $K_e$ gives the $w_{e,i}$ and $B_{e,i}$, with lifts to tied rows. For a choice $\mathbf{i}$, the $\nu_i$ and the lifts meet the hypotheses of gluing with $\pi_e = q_e$, $\mu_e = C$, without the coordinates in $W$. This gives rows with determinant $C^{\#s} \det B_{e,i_e}$ on $\xi_e$. Complete them by the tied rows at the $\delta_w$. The last lemma adds the factor $\prod_w o_w(1)$. $\square$

**Remark (Formalization).** Character rows are data, and the theorem only states that such data exist. The proof of the main lemma takes one instance by choice. The matrices $M_\mathbf{i}$ are indexed by all functions $\mathbf{i}$, one index for each character.
