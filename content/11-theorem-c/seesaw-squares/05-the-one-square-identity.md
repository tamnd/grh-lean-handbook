---
title: The one square identity
lean:
  - New/Determinant/Exchange/OneSquare.lean
decls:
  - New.Exchange.exists_integral_upIntegrand_eq_mul_integral_lift
  - New.Exchange.ne_zero_of_norm_sq_eq
  - New.Exchange.IsSquare
  - New.Exchange.exists_sum_pairLift_comp_pairTransposedLift_eq_smul
  - New.Exchange.equivariant_and_exists_sum_eq_of_areMatched
  - New.Exchange.one_square_identity_of_isEdgeFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The one square identity

This section proves the theorem of [Section 1](/chapter/seesaw-squares/#what-the-chapter-proves). The notation is that of [Section 4](/chapter/seesaw-squares/#the-kernels-of-a-square). We use two results of chapter 6 of this volume.

1. The exchange identity for data modulo an ideal (`New.Exchange.exchange_identity`, [the exchange identity, part 2](/chapter/exchange-identity-2/)). Let $W$, $V$, $V'$ have index sets $n$, $a$, $b$ with $\sigma \colon b \sqcup a \simeq n$, $|a| = |b| + 2e$, $\operatorname{neg}(W) = \operatorname{neg}(V) + \operatorname{neg}(V')$, $2\operatorname{neg}(W) + 2 \leq |n| \leq 2\mu_\tau + 2\operatorname{neg}(W)$. Let $v$ be a Schwartz vector for $(V', W)$. Then there are $C > 0$ and a Schwartz vector $x$ for $(W, V)$ such that every $\nu$ tame for $(\mathfrak{m}, \mu, \chi)$ has a number $c$ with $|c|^2 = C L_{\mathfrak{m}}(\nu, e) \neq 0$ and this property. For all $\alpha$, $\alpha'$ whose space characters in ranks $|a|$ and $|b|$ multiply to the inverse base change $\tilde\nu^{-1}$, for all $\Phi$, $\Psi$ matched for $\chi$, and for all $g$, the theta integral over $[U(V)]$ of $\theta^{W, V}_{\operatorname{rankTwist}(\nu^{-1}, n), \alpha}(\varphi_\Phi(x))$ at $g$ is $c$ times $\int_{[U(V')]} \theta^{V', W}_{\alpha', \operatorname{rankTwist}(\nu^{-1}, n)}(\varphi_\Psi(v))(h, g)\, dh$.
2. If $|N| = p + q$ is even, then $\alpha_p\,\alpha'_q = \tilde\nu^{-1}$ for the space characters if and only if $\alpha\alpha' = \operatorname{rankTwist}(\nu^{-1}, N)$ (`New.Exchange.spaceChar_mul_spaceChar_eq_iff`, same chapter).

The vector $x$ of item 1 is produced by the identity. We do not choose it.

### One constant for the side of $A$

**Lemma.** Let $(U_1, A)$ be an edge $e_1 \to e$ for $(a_1, b_1, P_1)$ and $(U_2, A)$ an edge $\bar e_2 \to \bar e$ for $(a_2, b_2, P_2)$. Let $b_2(i)\nu_0(i) = b_1(i)$ and let $\mathfrak{m}_i$ have a place, for all $i$. Let $w$ be a Schwartz vector. Then there is one number $\kappa$ with this property. For all $i$, all $x$ with $x^{\mathsf{T}}$ left invertible, all $f_1$ of type $e_1$ and all $f_2$ of type $\bar e_2$,
$$\int \mathrm{up}_i(x, w) = \kappa \int_{[U_2]} f_2 \cdot \mathcal{L}^{\mathsf{T}}_{U_2 \to A}(\delta_{x_2})\big(\mathcal{L}_{U_1 \to A}(\delta_{x_1}) f_1\big).$$
Here $\mathrm{up}_i$ is formed with $\nu_0(i)$ and the characters $a_1(i)a_2(i)$, $b_1(i)$.

Lean: `New.Exchange.exists_integral_upIntegrand_eq_mul_integral_lift` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* A *case* $j$ is a tuple $(i, x, f_1, f_2)$ as in the claim. Put $\mathrm{path}(j) = \int_{[A]} \mathcal{L}(\delta_{x_1}) f_1 \cdot \mathcal{L}(\delta_{x_2}) f_2$, the second lift being that of $(U_2, A)$ from $\bar e_2$ to $\bar e$. Forms of a cusp type are of rapid decay. So, by Section 4, $\mathrm{up}_j(v_Q)$ is integrable for every polynomial $Q$.

First, for each polynomial $Q$ in the variables of $n' \times (n_1 \sqcup n_2)$, we find $r$ with $\int \mathrm{up}_j(v_Q) = r\,\mathrm{path}(j)$ for all $j$. Such $Q$ is a sum of products $Q_1Q_2$, with $Q_1$ in the variables of the first column block and $Q_2$ in those of the second. Both sides are additive in $Q$, so it is enough to treat one product. By [edges and arrows](/chapter/theta-lifts-seesaw/#edges-and-arrows) (`IsPairEdge.exists_lift_eq_realConv`) there is $\alpha_1$, fixed by the real data, such that the lift with $Q_1$ is $\alpha_1 * \mathcal{L}(P_1)$, the right convolution by $\alpha_1$ on the real group of $A$. The same gives $\alpha_2$ for $Q_2$. The types $e$ and $\bar e$ are conjugate cusp types. For such types there is one $r$ with $\int (\alpha_1 * y)(\alpha_2 * y') = r \int y y'$ for all forms $y$, $y'$ (`exists_integral_realConv_mul_realConv`, [Seesaw.lean](lean:Lib/Weil/Seesaw.lean#L323)). By the up integral lemma of Section 4, $\int \mathrm{up}_j(v_{Q_1Q_2})$ is the integral over $[A]$ of the product of the two lifts with $Q_1$ and $Q_2$. So it is $r\,\mathrm{path}(j)$.

Second, for each $j$ the map $v \mapsto \int \mathrm{up}_j(v)$ is Lipschitz for one moment, by Section 4. The polynomial vector lemma of Section 4 then gives $\kappa$ with $\int \mathrm{up}_j(w) = \kappa\,\mathrm{path}(j)$ for all $j$.

Last, background item 5 of Section 4, applied to the arrow $(U_2, A)$ and its swap, turns $\mathrm{path}(j)$ into $\int_{[U_2]} f_2 \cdot \mathcal{L}^{\mathsf{T}}(\delta_{x_2})(\mathcal{L}(\delta_{x_1}) f_1)$. $\square$

The constant $\kappa$ comes from the density argument. The proof gives no formula for it.

**Lemma.** If $|c|^2 = r$ and $r \neq 0$, then $c \neq 0$.

Lean: `New.Exchange.ne_zero_of_norm_sq_eq` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* If $c = 0$, then $r = 0$. $\square$

### Squares

**Definition (Square).** Fix types $e'$, $e$, $e_1$, $e_2$ on $A'$, $A$, $U_1$, $U_2$. Fix families of characters $(a_1, b_1)$, $(a_2, b_2)$, $(b_1', a_1')$, $(b_2', a_2')$ on the pairs $(U_1, A)$, $(U_2, A)$, $(A', U_1)$, $(A', U_2)$, and polynomials $P_1$, $P_2$, $P_1'$, $P_2'$. Let $t \in \mathbb{N}$, $\mu$ a weight, and $\mathfrak{m}_i$, $\nu_i$, $\chi_i$ for $i \in I$. The data form a *square* if these hold.

1. $\operatorname{neg}(s_1 \oplus s_2) = \operatorname{neg}(s') + \operatorname{neg}(s)$, $|n'| = |n| + 2t$, $2\operatorname{neg}(s_1 \oplus s_2) + 2 \leq |n_1 \sqcup n_2|$, and $|n_1 \sqcup n_2| \leq 2\mu_\tau + 2\operatorname{neg}(s_1 \oplus s_2)$ for all $\tau$.
2. $\nu_i$ is tame for $(\mathfrak{m}_i, \mu, \chi_i)$.
3. The pairs are edges $e_1 \to e$, $\bar e_2 \to \bar e$, $\bar e' \to \bar e_1$ and $e' \to e_2$.
4. The space characters satisfy $a_1(i)_{|n_1|}\,a_2(i)_{|n_2|} = a_1'(i)_{|n_1|}\,a_2'(i)_{|n_2|} = \tilde\nu_i^{-1}$ and $b_1(i)_{|n'|}\,b_1'(i)_{|n|} = b_2(i)_{|n'|}\,b_2'(i)_{|n|} = \tilde\nu_i^{-1}$.

Lean: `New.Exchange.IsSquare` (New/Determinant/Exchange/OneSquare.lean).

For the rest of the section let $\Theta_i(x) = \mathcal{L}^{\mathsf{T}}_{U_2 \to A}(\delta_{x_2}) \circ \mathcal{L}_{U_1 \to A}(\delta_{x_1})$ and $\Theta'_i(y) = \mathcal{L}_{A' \to U_2}(\delta_{y_2}) \circ \mathcal{L}^{\mathsf{T}}_{A' \to U_1}(\delta_{y_1})$, with the characters and polynomials of the square. Both send forms of type $e_1$ to forms of type $e_2$.

**Theorem.** Let the data form a square and let $\sigma \colon n \sqcup n' \simeq n_1 \sqcup n_2$. There are $C > 0$ and $\kappa$ such that for every $i$ there is $c$ with $|c|^2 = C L_{\mathfrak{m}_i}(\nu_i, t) \neq 0$ and
$$\sum_y \Psi'(y)\,\Theta'_i(y) = \frac{\kappa}{c} \sum_x \Psi(x)\,\Theta_i(x)$$
for all $\Psi$, $\Psi'$ matched over $O_E/\mathfrak{m}_i$ for $\chi_i$ and $\sigma$.

Lean: `New.Exchange.exists_sum_pairLift_comp_pairTransposedLift_eq_smul` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* We have $|n_1 \sqcup n_2| = |n'| + |n| = 2(|n| + t)$, which is even.

*The characters.* By item 2 above, condition 4 gives $a_1a_2 = a_1'a_2' = \operatorname{rankTwist}(\nu_i^{-1}, n_1 \sqcup n_2)$. It also gives $b_1b_1' = b_2b_2'$, since both equal the same rank twist. Put $\nu_0 = b_1/b_2$. Then $b_2\nu_0 = b_1$ and $b_1'\nu_0 = b_1'b_1/b_2 = b_2'$. Tameness gives that each $\mathfrak{m}_i$ has a place.

*The exchange identity.* Let $v = v_{P_1'P_2'}$, with $P_1'$ and $P_2'$ read in the variables of the two row blocks. It is a Schwartz vector. Apply item 1 to $W = U_1 \oplus U_2$, $V = A$, $V' = A'$, with $e = t$. This gives $C > 0$ and a Schwartz vector $w$. The first lemma of this section, with this $w$ and $\nu_0$, gives $\kappa$. Fix $i$. Item 1 gives $c$ with $|c|^2 = C L_{\mathfrak{m}_i}(\nu_i, t) \neq 0$, so $c \neq 0$.

*Reduction to pairings.* Fix $\Psi$, $\Psi'$ matched and a form $f_1$. Two forms of type $e_2$ are equal if their inner products with every form $z$ of type $e_2$ agree. The inner product of $z$ with $L$ is $\int_{[U_2]} f_2 L$, with $f_2 = \bar z$ of type $\bar e_2$. Forms of cusp type are of rapid decay, so $f_1$ and $f_2$ are.

*The identity at a point.* Let $F_x = \mathrm{up}(x, w)$ with $\nu_0$, $a_1a_2$, $b_1$, and $F'_y = \mathrm{down}(y, v)$ with $\nu_0$, $a_1'a_2'$, $b_1'$. Use item 1 with $\alpha = b_1$ and $\alpha' = b_1'$. The condition on space characters is condition 4. At $g_1 \oplus g_2$ it gives the hypothesis of the last integration lemma of Section 4, with $a = \operatorname{rankTwist}(\nu_i^{-1}, n_1 \sqcup n_2)$. So for each $g = (g_1, g_2)$,
$$\int_{[A]} \sum_x \Psi(x) F_x(g, h)\, dh = c \int_{[A']} \sum_y \Psi'(y) F'_y(g, h)\, dh.$$

*The side of $A$.* If $\Psi(x) \neq 0$, then $x^{\mathsf{T}}$ has a left inverse. So $F_x$ is integrable, and by the first lemma its integral is $\kappa\,\langle z, \Theta_i(x) f_1\rangle$. The integration lemma for sums gives $\int_{U_1 \times U_2}\int_A \sum_x \Psi(x) F_x = \sum_x \Psi(x)\,\kappa\,\langle z, \Theta_i(x) f_1\rangle$.

*The side of $A'$.* If $\Psi'(y) \neq 0$, then $y$ has a left inverse. The last lemma of Section 4, with $b_1'\nu_0 = b_2'$, gives $\int_{U_1 \times U_2}\int_{A'} \sum_y \Psi'(y) F'_y = \sum_y \Psi'(y)\,\langle z, \Theta'_i(y) f_1\rangle$.

*Conclusion.* Integrate the identity at a point over $[U_1] \times [U_2]$. Then $\kappa \sum_x \Psi(x)\langle z, \Theta_i(x) f_1\rangle = c \sum_y \Psi'(y)\langle z, \Theta'_i(y) f_1\rangle$. Divide by $c$. The inner product is linear in its second argument, so $\langle z, (\sum_y \Psi'(y)\Theta'_i(y)) f_1\rangle = \langle z, ((\kappa/c) \sum_x \Psi(x)\Theta_i(x)) f_1\rangle$ for all $z$. $\square$

**Theorem.** Let the data form a square and let $\sigma$ be as above.

1. $\Theta_i(gx) = \chi_i(\det g)\,\Theta_i(x)$ for $g \in GL_{n'}(O_E/\mathfrak{m}_i)$, and $\Theta'_i(yg) = \chi_i(\det g)\,\Theta'_i(y)$ for $g \in GL_n(O_E/\mathfrak{m}_i)$.
2. The conclusion of the previous theorem holds.

Lean: `New.Exchange.equivariant_and_exists_sum_eq_of_areMatched` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* For claim 1, condition 4 and item 2 give $a_1a_2 = \operatorname{rankTwist}(\nu_i^{-1}, n_1 \sqcup n_2)$. By the tameness lemma of Section 4, $(a_1a_2)^{-1}$ is tame for $(\mathfrak{m}_i, \mu', \chi_i)$ for some $\mu'$. The equivariance lemma of Section 4 gives the claim for $\Theta_i$. The claim for $\Theta'_i$ is the same with $a_1'a_2'$. Claim 2 is the previous theorem. $\square$

### Proof of the one square identity

We now prove the theorem of Section 1.

Lean: `New.Exchange.one_square_identity_of_isEdgeFamily` (New/Determinant/Exchange/OneSquare.lean).

*Proof.* We have $|n'| + |n| = |n_1| + |n_2|$, and $|n_1 \sqcup n_2|$ is even. By condition 8 and item 2, $a_i(p)_{|p|}\,b_i(q)_{|q|} = \tilde\nu_i^{-1}$ whenever $|p| + |q| = |n_1| + |n_2|$. By commutativity also $b_i(p)_{|p|}\,a_i(q)_{|q|} = \tilde\nu_i^{-1}$.

We build a square with $e_1 = k_1(\neg d)$, $e_2 = k_2(\neg d)$, $e = k(\neg d)$ and $e' = k'(\neg d)$, and with $(a_1, b_1) = (a(n_1), a(n'))$, $(a_2, b_2) = (b(n_2), b(n'))$, $(b_1', a_1') = (b(n), b(n_1))$ and $(b_2', a_2') = (a(n), a(n_2))$. Conditions 1 and 2 of a square are conditions 3 to 7 of the theorem. For condition 3 we use the edge families. The family $(a, k_1, k, \neg d, \Phi_1)$ gives an edge $k_1(\neg d) \to k(\neg d)$. The family $(b, k_2, k, d, \Phi_2)$ gives an edge $k_2(d) \to k(d)$. Since $k(\neg d) = \overline{k(d)}$ for an edge family, this is an edge $\bar e_2 \to \bar e$. In the same way, $(b, k', k_1, d, \Phi_1')$ gives $\bar e' \to \bar e_1$, and $(a, k', k_2, \neg d, \Phi_2')$ gives $e' \to e_2$. For condition 4 we use the products above with $(p, q) = (n_1, n_2)$ twice and $(p, q) = (n', n)$ twice.

The previous theorem gives $\Theta_i(gx) = \chi_i(\det g)\Theta_i(x)$, the same for $\Theta'_i$, and $C$, $\kappa$ and, for each $i$, $c$ with $|c|^2 = C L_{\mathfrak{m}_i}(\nu_i, t) \neq 0$ and the identity of sums. By the lemma above, $c \neq 0$. Fix $f$ and $l$. Apply $L \mapsto l(L f)$ to the three identities of maps. This gives the three conditions of the square law. $\square$

### Why $\kappa$ may vanish

The theorem of Section 1 gives $c \neq 0$, but no information on $\kappa$. So the square law may be the trivial law $\sum \Psi' L' = 0$. The book records this as finding F-069 in [constants that may vanish](/chapter/register-of-findings/#constants-that-may-vanish).

The proof shows where the information is lost. The exchange identity produces the vector $w$ on the side of $A$. The up path is computed with a polynomial vector, and the density argument passes from polynomial vectors to $w$. The limit of the multiples $r$ is $\kappa$. Nothing in the argument keeps these multiples away from $0$.

Three more points weaken the statement of Section 1 against the theorem for squares.

1. The theorem for squares gives $C > 0$. The theorem of Section 1 drops this, so $C$ has no sign there.
2. The index set $I$ may be empty. Then the statement holds with any $C$ and $\kappa$.
3. The constant $\kappa/c$ depends on $i$ only through $c$.

The source applies the identity three times: in [ChainNorms.lean](lean:New/Determinant/Chain/ChainNorms.lean#L180) at lines 180 and 284, and in [Turns.lean](lean:New/Determinant/AuxiliaryForms/Turns.lean#L769) at line 769. [The plan](/chapter/theorem-c-plan/#constants-that-may-vanish) says that the source uses the identity only for the squares of a triangle. The use in `Turns.lean` is for a square of a grid, so that sentence of the plan is not complete. For the triangle, the nonvanishing of the factors of a chain is argued from the injectivity of the maps of the chain, through `IsTriangle.ne_zero_of_chainCommutes`. The lemma `IsTriangle.ne_zero_of_squareCommutes` is not used (finding F-121). Whether the nonvanishing of $\kappa$ is recovered in every use is the open question Q-06 of the register. This chapter does not settle it.

**Remark (Formalization).** The statement in Lean is an existence statement with $\kappa \in \mathbb{C}$. There is no `choose` in the proof of the identity itself. The lifts $\mathcal{L}$ and $\mathcal{L}^{\mathsf{T}}$ are chosen maps `formLift`; on arrows they equal the theta integrals, and all uses here are on arrows.
