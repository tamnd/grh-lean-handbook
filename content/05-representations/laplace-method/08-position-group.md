---
title: The group of a position and the restriction bound
lean:
  - New/Appendix/DiscreteSeries/PositionGroup.lean
decls:
  - New.DiscreteSeries.LowersFlag.inv
  - New.DiscreteSeries.positionGroup
  - New.DiscreteSeries.positionSum
  - New.DiscreteSeries.IsPosition.positionSum_mul
  - New.DiscreteSeries.IsPosition.isClosed_positionGroup
  - New.DiscreteSeries.IsPosition.inducesOn
  - New.DiscreteSeries.IsPosition.formAdjoint_conj_mul
  - New.DiscreteSeries.IsPosition.inducedHom
  - New.DiscreteSeries.IsPosition.inducedHom_eq
  - New.DiscreteSeries.IsPosition.periodIntegrand
  - New.DiscreteSeries.IsPosition.exists_inducedHom_eq
  - New.DiscreteSeries.IsStationary.isLaplaceDatum
  - New.DiscreteSeries.IsStationary.integrable_periodIntegrand_and_measure_le
  - New.DiscreteSeries.IsStationary.period_lower_bound_of_surjective
  - New.DiscreteSeries.IsPosition.gram_fromCols
  - New.DiscreteSeries.norm_conj_inl_le
  - New.DiscreteSeries.lowersFlag_conj_inl_sub_one
  - New.DiscreteSeries.inducesOn_conj_inl_sub_one
  - New.DiscreteSeries.IsPosition.exists_conj_inl_eq
  - New.DiscreteSeries.IsSteep.lowestKType_neg_mem
  - New.DiscreteSeries.sq_norm_fromCols_le
  - New.DiscreteSeries.IsSteep.exists_isStationary_conjTranspose_mul_mul_eq_one
  - New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The group of a position and the restriction bound

This section turns a stationary position into a Laplace datum. The group $S$ is the group $R$ of elements of $U(\varepsilon)$ that lower the flag of the position. The map to $U(\eta)$ is the compression $g \mapsto i_0^\dagger g i_0$. The phase is $\sigma - \overline{\sigma}$, where $\sigma$ is the sum of the entries next to the diagonal. Then the theorem of Laplace's method of [section 6](/chapter/laplace-method/) gives a lower bound for the period over $R$. The restriction bound of the opening section is the case of one vector.

Throughout, $(v, i_0)$ is a position of $U(\eta)$ in $U(\varepsilon)$ with $d + 1$ vectors, and $A$ is the span of $v_1, \dots, v_d$. All norms in this section are operator norms.

### The group

**Definition (Group of a position).** Let $R$ be the set of $g \in U(\varepsilon)$ such that $g - 1$ lowers the flag of $v$, for some sum $\sigma$.
Lean: `New.DiscreteSeries.positionGroup` (New/Appendix/DiscreteSeries/PositionGroup.lean).

The set $R$ contains $1$, with $\sigma = 0$. It is closed under products by the lemma on products of section 7. It is closed under inverses. Indeed, if $g - 1$ lowers the flag, then $g$ acts on $A$ by a unipotent upper triangular matrix $T$. So $g^{-1}$ acts on $A$ by $T^{-1}$, and $g^{-1} - 1 = -g^{-1}(g - 1)$ lowers the flag with the matrix $-T^{-1}N$.
Lean: `New.DiscreteSeries.LowersFlag.inv` (New/Appendix/DiscreteSeries/PositionGroup.lean).

**Definition (The sum).** For $g \in R$, $\sigma(g)$ is a sum $\sigma$ for which $g - 1$ lowers the flag.
Lean: `New.DiscreteSeries.positionSum` (New/Appendix/DiscreteSeries/PositionGroup.lean).

**Lemma (Additivity).** $\sigma(g_1 g_2) = \sigma(g_1) + \sigma(g_2)$. The group $R$ is closed in $U(\varepsilon)$.
Lean: `New.DiscreteSeries.IsPosition.positionSum_mul` (New/Appendix/DiscreteSeries/PositionGroup.lean), `New.DiscreteSeries.IsPosition.isClosed_positionGroup` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* Additivity is the lemma on products, with the uniqueness of the sum in a position. For closedness, take $Z$ with $Z(v_1, \dots, v_d) = 1$ and $Z i_0 = 0$. Then $g \in R$ if and only if $(g - 1)v = (v_1, \dots, v_d) Z (g - 1) v$ and the matrix $Z(g - 1)v$ vanishes on and below the diagonal. These are closed conditions. $\square$

**Remark (Formalization).** The source defines $\sigma(g)$ by a choice from the existence statement in the definition of $R$. In a position the choice does not matter, by the uniqueness lemma of section 7. Outside positions the definition of $R$ still makes sense, but $\sigma$ may depend on the choice.

### The compression

**Lemma (Induced action).** For $g \in R$, $g - 1$ induces $i_0^\dagger g i_0 - 1$ on the image of $i_0$.
Lean: `New.DiscreteSeries.IsPosition.inducesOn` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* Put $Y = g - 1$. Then $Y^\dagger = g^{-1} - 1$, which maps $v$ into $A$. So $\langle v_b, Y i_0 x\rangle_\varepsilon = \langle Y^\dagger v_b, i_0 x\rangle_\varepsilon = 0$, and the columns of $Yi_0$ are orthogonal to all $v_b$. In particular they lie in $A^\perp$. So $Y i_0 = i_0 T_1 + v T_2$. Pairing with $v_{d+1}$, whose norm is $\pm 1$ and which is orthogonal to the other $v_b$ and to $i_0$, shows that the last row of $T_2$ vanishes. Pairing with $i_0$ gives $T_1 = i_0^\dagger Y i_0$. $\square$

**Lemma (Compression is a homomorphism).** For $g_1, g_2 \in R$, $i_0^\dagger g_1 g_2 i_0 = (i_0^\dagger g_1 i_0)(i_0^\dagger g_2 i_0)$, and $i_0^\dagger g i_0 \in U(\eta)$.
Lean: `New.DiscreteSeries.IsPosition.formAdjoint_conj_mul` (New/Appendix/DiscreteSeries/PositionGroup.lean), `New.DiscreteSeries.IsPosition.inducedHom` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* By the induced action, $g_2 i_0 = i_0 g'_2 + (\text{columns in } A)$. Apply $i_0^\dagger g_1$. Since $g_1 A \subseteq A$ and $i_0^\dagger A = 0$, the second term vanishes. So $i_0^\dagger g_1 g_2 i_0 = i_0^\dagger g_1 i_0\, g'_2$. Unitarity follows from the same identity with $g_1 = g_2^{-1}$. $\square$

The compression is determined by the induced action. If $g - 1$ induces $y - 1$ for some $y \in U(\eta)$, then $i_0^\dagger g i_0 = y$.
Lean: `New.DiscreteSeries.IsPosition.inducedHom_eq` (New/Appendix/DiscreteSeries/PositionGroup.lean).

The compression is onto. For $y \in U(\eta)$ the element
$$ g = 1 + i_0(y - 1)i_0^\dagger $$
is in $U(\varepsilon)$. It is $y$ on the image of $i_0$ and the identity on the orthogonal complement. It lies in $R$ with $\sigma(g) = 0$, and $i_0^\dagger g i_0 = y$.
Lean: `New.DiscreteSeries.IsPosition.exists_inducedHom_eq` (New/Appendix/DiscreteSeries/PositionGroup.lean).

For $g \in R$ write $g' = i_0^\dagger g i_0$. The *period integrand* is
$$ \theta(g) = c_l(g)\,\overline{c_k(g')}\,\exp\big(\overline{\sigma(g)} - \sigma(g)\big). $$
Lean: `New.DiscreteSeries.IsPosition.periodIntegrand` (New/Appendix/DiscreteSeries/PositionGroup.lean).

### The Laplace datum

**Theorem (Stationary positions give Laplace data).** Let $(v, i_0)$ be stationary for $l$ and $k$, with $e : X \sqcup \{0, \dots, M - 1\} \cong n$ and $e' : X \sqcup \{0, \dots, M' - 1\} \cong m$. Let $l$ be steep for $(B, e)$. Let $\eta = 1$ and $\mu' = 0$ on $e'(X)$. Let $\mu' \geq 0$, and let $\mu'_i \leq 3B$ whenever $\eta$ is not constant. Then $g \mapsto (g, g')$ on $R$, with $\tau = e'|_X$ and $\varphi = \sigma - \overline{\sigma}$, is a Laplace datum.
Lean: `New.DiscreteSeries.IsStationary.isLaplaceDatum` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* By additivity, $\sigma(g^{-1}) = -\sigma(g)$. So $Y = g - 1$ lowers the flag with sum $\sigma(g)$, and $Y^\dagger = g^{-1} - 1$ lowers it with sum $-\sigma(g)$. By the induced action, $Y$ induces $g' - 1$. The theorem on two traces of section 7 gives condition 2 and
$$ \Phi(g - 1, g' - 1) = \sigma(g) + \overline{-\sigma(g)} = \sigma(g) - \overline{\sigma(g)}, $$
which is condition 1. Condition 3 is additivity of $\sigma$, and condition 4 holds since $\sigma - \overline\sigma$ is imaginary. Conditions 5 and 6 are hypotheses. For condition 7, let $u \in U(X)$. Let $y \in U(\eta)$ be $u$ on the coordinates $e'(X)$ and the identity elsewhere; this needs $\eta = 1$ on $e'(X)$. Take $g = 1 + i_0(y - 1)i_0^\dagger$. Since $i_0$ is the identity from $e'(X)$ to $e(X)$, the element $g$ is $u$ on the coordinates $e(X)$ and the identity elsewhere. $\square$

**Theorem (Period over the group of a position).** Let the hypotheses of the previous theorem hold with $B \geq 1$. Let $l$ and $k$ have large gap $h$ and entries at most $L$ in absolute value. Let $\beta \geq 10^{12}$, $\#n + \#m + L \leq \beta$ and $h \geq 10^{30}((\#n + \#m)^2\log\beta)^3$. Let $\nu$ be a right invariant measure on $R$ that is finite on compact sets. Then $\theta$ is integrable and
$$ \nu\{g \in R : \|g\| \leq \beta + 1,\ \|g'\| \leq \beta + 1\} \leq \beta^{20(\#n + \#m)^2}\left|\int_R \theta\,d\nu\right|. $$
Lean: `New.DiscreteSeries.IsStationary.integrable_periodIntegrand_and_measure_le` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* The integrand $\theta$ is the Laplace integrand of the datum, since $e^{-\varphi} = e^{\overline\sigma - \sigma}$. The inclusion of $R$ in $U(\varepsilon)$ is proper, as $R$ is closed. The compression is continuous. Apply the theorem of Laplace's method. $\square$

**Theorem (Period over a group that maps onto $R$).** Keep the hypotheses on $l$, $k$, $(v, i_0)$, $B$, $L$, $\beta$ and $h$. Let $S$ be a topological group with a right invariant Borel measure $\nu$ that is finite on compact sets. Let $j : S \to U(\varepsilon) \times U(\eta)$ be a homomorphism, $j(s) = (g, g')$, and let $\sigma : S \to \mathbb{C}$. Assume that $s \mapsto g$ is proper with image containing $R$, that $g - 1$ lowers the flag with sum $\sigma(s)$, and that $g - 1$ induces $g' - 1$. Then
$$ \nu\{s : \|g\| \leq \beta + 1,\ \|g'\| \leq \beta + 1\} \leq \beta^{20(\#n + \#m)^2}\left|\int_S c_l(g)\,\overline{c_k(g')}\,e^{\overline{\sigma(s)} - \sigma(s)}\,d\nu(s)\right|. $$
Lean: `New.DiscreteSeries.IsStationary.period_lower_bound_of_surjective` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* The map $f : s \mapsto g$ is a proper homomorphism onto $R$. The image measure $f_*\nu$ is right invariant on $R$, since $f$ is onto. It is finite on compact sets, since $f$ is proper. By the induced action, $g' = i_0^\dagger g i_0$, and by uniqueness, $\sigma(s) = \sigma(g)$. So the integrand is $\theta \circ f$. Apply the previous theorem to $f_*\nu$ and change variables. $\square$

**Remark (Formalization).** The previous theorem does not state that the integrand on $S$ is integrable. It is, since $\theta$ is integrable for $f_*\nu$, but the source only records the inequality.

### One vector

This part treats the restriction theorem of the opening section. Let $n' = n \sqcup \{\ast\}$ and $\varepsilon' = \varepsilon \oplus 1$. A position of $U(\varepsilon)$ in $U(\varepsilon')$ with $d = 0$ is a vector $v_1$ and an isometry $i_0$ of $(\mathbb{C}^n, \varepsilon)$ into $v_1^\perp$. Here $A = 0$. So $R$ is the stabilizer of $v_1$, and $\sigma = 0$.

**Lemma (A frame).** If $\langle v_1, v_1\rangle_{\varepsilon'} = 1$, the square matrix $w = (i_0, v_1)$ is in $U(\varepsilon')$.
Lean: `New.DiscreteSeries.IsPosition.gram_fromCols` (New/Appendix/DiscreteSeries/PositionGroup.lean).

Then $w(g \oplus 1)w^{-1}$ fixes $v_1 = we_\ast$, so it lies in $R$, and it acts on the image of $i_0$ as $g$.
Lean: `New.DiscreteSeries.lowersFlag_conj_inl_sub_one` (New/Appendix/DiscreteSeries/PositionGroup.lean), `New.DiscreteSeries.inducesOn_conj_inl_sub_one` (New/Appendix/DiscreteSeries/PositionGroup.lean).

Conversely, every element of $R$ has this form: if $r \in R$ and $y = i_0^\dagger r i_0$, then $r = w(y \oplus 1)w^{-1}$.
Lean: `New.DiscreteSeries.IsPosition.exists_conj_inl_eq` (New/Appendix/DiscreteSeries/PositionGroup.lean).

If $\|g - 1\| \leq 1$, then $\|w(g \oplus 1)w^{-1}\| \leq 1 + \|w\|^2$. Indeed $w(g\oplus1)w^{-1} - 1 = w((g - 1) \oplus 0)w^{-1}$ and $\|w^{-1}\| = \|w\|$, since $w^{-1} = J_{\varepsilon'}w^*J_{\varepsilon'}$.
Lean: `New.DiscreteSeries.norm_conj_inl_le` (New/Appendix/DiscreteSeries/PositionGroup.lean).

If all entries of $i_0$ and $v_1$ are at most $R_0$, then $\|w\|^2 \leq (\#n + 1)^4R_0^2$.
Lean: `New.DiscreteSeries.sq_norm_fromCols_le` (New/Appendix/DiscreteSeries/PositionGroup.lean).

**Lemma (Weight of the negative).** If $l$ is steep for $(B, e)$ and has a large gap, then every entry of the weight of $-l$ lies in $[0, 3B]$.
Lean: `New.DiscreteSeries.IsSteep.lowestKType_neg_mem` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* With a gap, the weight of $-l$ is $-\mu$. The steep weight $\mu$ is $0$ on $X$ and in $[-3B, -B]$ elsewhere. $\square$

**Lemma (Stationary position with one vector).** Let $M$ be even, $B \geq 1$, $l$ steep for $(B, e)$ with $M$ indices outside $X$, and $-l'$ steep for $(B, e')$ with $M + 1$ indices outside $X$. Let $l$ have a large gap. Then $-l'$ and $-l$ have a stationary position $(v, i_0)$ of $U(\varepsilon)$ in $U(\varepsilon')$ with one vector, with $\langle v_1, v_1\rangle_{\varepsilon'} = 1$, and with all entries of $v_1$ and $i_0$ at most $(6B)^{M+1}$.
Lean: `New.DiscreteSeries.IsSteep.exists_isStationary_conjTranspose_mul_mul_eq_one` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof.* Apply the theorem on the stationary position of section 7 to $-l'$ and $-l$, with $L = M + 1$, $L' = M$, $d = 0$ and $B' = 3B$. The weight of $-l$ is $-\mu$. It is $0$ on $X$, strictly increasing off $X$, and in $[0, 3B]$. The signs of $\varepsilon$ off $X$ alternate, by steepness of $l$. The norm of $v_1$ is $(-1)^M = 1$, and $3B + B' = 6B$. $\square$

We now prove the restriction theorem.
Lean: `New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff` (New/Appendix/DiscreteSeries/PositionGroup.lean).

*Proof of the restriction theorem.* Take the stationary position of the previous lemma, and put $w = (i_0, v_1) \in U(\varepsilon')$ and $y = w^{-1}$. Then $\|y\|^2 = \|w\|^2 \leq (\#n + 1)^4(6B)^{2M + 2} \leq \beta$. Let $S = U(\varepsilon)$ with its Haar measure, and
$$ j(g) = \big(w(g \oplus 1)w^{-1},\ g\big). $$
The first component is proper, since conjugation is a homeomorphism and $g \mapsto g \oplus 1$ is a closed embedding. Its image is $R$. For every $g$ it lowers the flag with sum $0$ and induces $g - 1$. Apply the theorem on groups that map onto $R$, with the parameters $-l'$ for $U(\varepsilon')$ and $-l$ for $U(\varepsilon)$. The hypotheses on the second weight hold by the lemma on the weight of the negative. Here $\#n' + \#n = 2\#n + 1$.

The integrand is $c_{-l'}(w(g\oplus1)w^{-1})\,\overline{c_{-l}(g)}$. By the conjugation formula, this is $c_l(g)\,\overline{c_{l'}(y^{-1}(g \oplus 1)y)}$. If $\|g - 1\| \leq 1$, then $\|g\| \leq 2 \leq \beta + 1$ and $\|w(g\oplus1)w^{-1}\| \leq 1 + \beta$. So the unit ball lies in the set whose volume the theorem bounds. $\square$

The proof exchanges the roles of the two groups. The larger group $U(\varepsilon')$ carries the steep parameter $-l'$, and $U(\varepsilon)$ is the group of the position. The weight of $-l$ is then nonnegative, as condition 6 of a Laplace datum asks.

**Remark (Formalization).** The source states the restriction theorem with the Haar measure on $U(\varepsilon)$ that it builds from Lebesgue measure through a Cayley chart. Only right invariance and finiteness on compact sets enter the proof. The statement only asserts that some $y$ exists, with $\|y\|^2 \leq \beta$. The proof takes $y = w^{-1}$, with $w$ built from the stationary position of section 7.
