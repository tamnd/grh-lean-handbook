---
title: Positions and the stationary position
lean:
  - New/Appendix/DiscreteSeries/Positions.lean
  - New/Appendix/DiscreteSeries/StationaryPosition.lean
decls:
  - New.DiscreteSeries.formAdjoint
  - New.DiscreteSeries.IsPosition
  - New.DiscreteSeries.LowersFlag
  - New.DiscreteSeries.InducesOn
  - New.DiscreteSeries.IsStationary
  - New.DiscreteSeries.IsPosition.exists_mul_eq_zero_and_mul_eq_one
  - New.DiscreteSeries.IsPosition.trace_mul_eq_of_mul_initCols_eq_zero
  - New.DiscreteSeries.IsPosition.trace_mul_eq_trace_add_sum_of_inducesOn
  - New.DiscreteSeries.IsPosition.lowersFlag_unique
  - New.DiscreteSeries.LowersFlag.mul
  - New.DiscreteSeries.IsStationary.gram_pow_mulVec
  - New.DiscreteSeries.IsStationary.trace_eq_and_phase_eq
  - New.DiscreteSeries.AreOppositeNodes
  - New.DiscreteSeries.polyVec
  - New.DiscreteSeries.alternatingSignForm
  - New.DiscreteSeries.AreOppositeNodes.alternatingSignForm_polyVec
  - New.DiscreteSeries.AreOppositeNodes.alternatingSignForm_polyVec_nodal_erase
  - New.DiscreteSeries.AreOppositeNodes.isometryScale_mul_alternatingSignForm
  - New.DiscreteSeries.positionVec
  - New.DiscreteSeries.positionIsometry
  - New.DiscreteSeries.exists_intDiagonal_mul_positionIsometry
  - New.DiscreteSeries.IsPosition.formAdjoint_mul_mul_eq
  - New.DiscreteSeries.IsSteep.exists_isStationary
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Positions and the stationary position

Laplace's method needs a group $S$ and a map $j$ on which the phase difference $\operatorname{tr}\mu(g - 1) - \operatorname{tr}\mu'(g' - 1)$ is additive. This section finds such groups. They are stabilizers of flags of vectors $v_1, \dots, v_{j_0}$ in $\mathbb{C}^n$, together with an isometry $i_0$ of a smaller hermitian space into the orthogonal complement of the flag. Groups of this kind occur in the Bessel case of the Gan-Gross-Prasad problem for unitary groups (Gan, Gross and Prasad, *Astérisque* 346, 2012). The second half of the section builds the vectors from polynomials.

### Positions

For signs $\varepsilon$ on $n$ and $\eta$ on $m$ and a matrix $A$ of size $n \times m$, the adjoint for the two forms is
$$ A^\dagger = J_\eta A^* J_\varepsilon. $$
Lean: `New.DiscreteSeries.formAdjoint` (New/Appendix/DiscreteSeries/Positions.lean).

So $\langle Ax, y\rangle_\varepsilon = \langle x, A^\dagger y\rangle_\eta$, where $\langle x, y\rangle_\varepsilon = x^* J_\varepsilon y$. On $U(\varepsilon)$ we have $g^\dagger = g^{-1}$. If $A^\dagger A = 1$, then $A$ is an isometry.

**Definition (Position).** Let $d \geq 0$ and $j_0 = d + 1$. A *position* of $U(\eta)$ in $U(\varepsilon)$ is a pair $(v, i_0)$ of an $n \times j_0$ matrix $v$, with columns $v_1, \dots, v_{j_0}$, and an $n \times m$ matrix $i_0$, such that:

1. $\#n = \#m + 2d + 1$;
2. the vectors $v_1, \dots, v_{j_0}$ are linearly independent;
3. $\langle v_a, v_b\rangle_\varepsilon = 0$ unless $a = b = j_0$, and $\langle v_{j_0}, v_{j_0}\rangle_\varepsilon = \pm 1$;
4. $i_0^* J_\varepsilon i_0 = J_\eta$;
5. $i_0^* J_\varepsilon v = 0$.

Lean: `New.DiscreteSeries.IsPosition` (New/Appendix/DiscreteSeries/Positions.lean).

Let $A$ be the span of $v_1, \dots, v_d$. Then $A$ is isotropic, $A^\perp$ is spanned by $A$, $v_{j_0}$ and the image of $i_0$, and $\mathbb{C}^n$ is spanned by $A^\perp$ and $d$ more vectors. The count in condition 1 is $\#n = d + 1 + \#m + d$.

For $j \leq j_0$ let $A_{\leq j}$ be the span of $v_1, \dots, v_j$.

**Definition (Lowering the flag).** A matrix $Y$ *lowers the flag* with sum $\sigma$ if there is a $d \times j_0$ matrix $N$ with $N_{ab} = 0$ for $b \leq a$, with
$$ Y v_b = \sum_{a < b} N_{ab}\, v_a \quad (1 \leq b \leq j_0), $$
and with $\sum_{a = 1}^{d} N_{a, a+1} = \sigma$.
Lean: `New.DiscreteSeries.LowersFlag` (New/Appendix/DiscreteSeries/Positions.lean).

So $Y A_{\leq j} \subseteq A_{\leq j - 1}$ for every $j \leq j_0$, and $\sigma$ is the sum of the entries next to the diagonal.

**Definition (Induced map).** A matrix $Y$ *induces* $Y'$ on the image of $i_0$ if $Y i_0 = i_0 Y' + vC$ for a matrix $C$ whose columns are combinations of $v_1, \dots, v_d$. That is, $Y i_0 \equiv i_0 Y'$ modulo $A$.
Lean: `New.DiscreteSeries.InducesOn` (New/Appendix/DiscreteSeries/Positions.lean).

**Definition (Stationary position).** Let $e : X \sqcup \{0, \dots, M - 1\} \cong n$ and $e' : X \sqcup \{0, \dots, M' - 1\} \cong m$. A position $(v, i_0)$ is *stationary* for the parameters $l$ and $k$ if:

1. $\mu v_a = v_{a + 1}$ for $1 \leq a \leq d$;
2. $i_0^\dagger \mu i_0 = \mu'$;
3. $i_0$ sends the basis vector at $e'(x)$ to the basis vector at $e(x)$, for $x \in X$.

Lean: `New.DiscreteSeries.IsStationary` (New/Appendix/DiscreteSeries/Positions.lean).

By condition 1, $v_{a + 1} = \mu^a v_1$. The whole flag is the Krylov flag of $v_1$ under $\mu$. Since $\mu$ is self-adjoint for $\langle\cdot,\cdot\rangle_\varepsilon$, we get $\langle\mu^a v_1, \mu^b v_1\rangle_\varepsilon = \langle v_1, \mu^{a+b}v_1\rangle_\varepsilon$. So for $a + b \leq 2d$ this pairing is $\langle v_{j_0}, v_{j_0}\rangle_\varepsilon$ if $a + b = 2d$, and $0$ otherwise.
Lean: `New.DiscreteSeries.IsStationary.gram_pow_mulVec` (New/Appendix/DiscreteSeries/Positions.lean).

### Two traces

**Lemma (Coordinates).** In a position there is a matrix $Z$ with $Z i_0 = 0$ and $Z v = 1$.
Lean: `New.DiscreteSeries.IsPosition.exists_mul_eq_zero_and_mul_eq_one` (New/Appendix/DiscreteSeries/Positions.lean).

*Proof.* The columns of $i_0$ and $v$ are independent. Indeed, if $i_0 x + v z = 0$, then pairing with the image of $i_0$ gives $J_\eta x = 0$, by conditions 4 and 5. So $x = 0$, and then $z = 0$ by condition 2. A left inverse of the matrix $(i_0, v)$ gives $Z$. $\square$

**Lemma (Trace on the middle).** Let $(v, i_0)$ be a position. Let $Y$ map each $v_b$ into $A$ and induce $Y'$ on the image of $i_0$. Let $M$ vanish on $A$, with image in $A^\perp$. Then $\operatorname{tr}(MY) = \operatorname{tr}(i_0^\dagger M i_0\, Y')$.
Lean: `New.DiscreteSeries.IsPosition.trace_mul_eq_of_mul_initCols_eq_zero` (New/Appendix/DiscreteSeries/Positions.lean).

*Proof.* The columns of $M$ lie in $A^\perp$, so $M = i_0 T_1 + v T_2$ for some matrices $T_1$ and $T_2$. Since $MA = 0$ and the columns of $i_0$ and $v$ are independent, $T_1$ and $T_2$ vanish on $A$. So
$$ \operatorname{tr}(MY) = \operatorname{tr}(T_1 Y i_0) + \operatorname{tr}(T_2 Y v) = \operatorname{tr}(T_1 i_0 Y'), $$
since $Yv$ and $Yi_0 - i_0Y'$ have their columns in $A$. Finally $i_0^\dagger M i_0 = T_1 i_0$, since $i_0^\dagger i_0 = 1$ and $i_0^\dagger v = 0$. $\square$

**Lemma (Splitting a trace).** Let $(v, i_0)$ be a position and let $\mu$ satisfy $\mu^\dagger = \mu$ and $\mu v_a = v_{t(a)}$ for $a \leq d$, where $t$ is any map. Let $Y v = vN$ and $Y^\dagger v = vN'$, with $N$ and $N'$ supported in the first $d$ rows, and let $Y$ induce $Y'$ on the image of $i_0$. Then
$$ \operatorname{tr}(\mu Y) = \operatorname{tr}(i_0^\dagger\mu i_0\, Y') + \sum_{a=1}^{d} N_{a, t(a)} + \overline{\sum_{a=1}^{d} N'_{a, t(a)}}. $$
Lean: `New.DiscreteSeries.IsPosition.trace_mul_eq_trace_add_sum_of_inducesOn` (New/Appendix/DiscreteSeries/Positions.lean).

*Proof.* Take $Z$ from the lemma on coordinates, restricted to the first $d$ rows, so that $Z$ vanishes on $i_0$ and is the identity on $v_1, \dots, v_d$. Put $\mu_1 = \mu \cdot (v_1, \dots, v_d) \cdot Z$. This is $\mu$ on $A$ and $0$ on the image of $i_0$. The image of $\mu_1$ lies in the span of the $v_b$, which is orthogonal to $A$ and to the image of $i_0$. So $\mu_1^\dagger$ vanishes on $A$ and on the image of $i_0$. Write
$$ \mu = M + \mu_1 + \mu_1^\dagger. $$
The matrix $M$ is self-adjoint and vanishes on $A$. So its image is orthogonal to $A$, and $M i_0 = \mu i_0$. The lemma on the middle gives $\operatorname{tr}(MY) = \operatorname{tr}(i_0^\dagger\mu i_0 Y')$. The trace of $\mu_1 Y$ is the trace of $Y\mu_1$, which sends $v_a$ to $Y v_{t(a)}$ and is $0$ on a complement. Its trace is $\sum_a N_{a, t(a)}$. Finally $\operatorname{tr}(\mu_1^\dagger Y) = \overline{\operatorname{tr}(Y^\dagger\mu_1)}$, which is the conjugate of the same sum for $N'$. $\square$

**Lemma (Uniqueness and products).** In a position, the sum $\sigma$ of a matrix that lowers the flag is unique. If $g_1 - 1$ and $g_2 - 1$ lower the flag with sums $\sigma_1$ and $\sigma_2$, then $g_1 g_2 - 1$ lowers the flag with sum $\sigma_1 + \sigma_2$.
Lean: `New.DiscreteSeries.IsPosition.lowersFlag_unique` (New/Appendix/DiscreteSeries/Positions.lean), `New.DiscreteSeries.LowersFlag.mul` (New/Appendix/DiscreteSeries/Positions.lean).

*Proof.* Uniqueness follows from the independence of the $v_b$, which determines $N$. For the product, $g_1 g_2 - 1 = (g_1 - 1) + (g_2 - 1) + (g_1 - 1)(g_2 - 1)$. The last term lowers the flag by two steps, so it has no entries next to the diagonal. $\square$

**Theorem (Two traces).** Let $(v, i_0)$ be a stationary position. Let $Y$ and $Y^\dagger$ lower the flag with sums $\sigma$ and $\sigma'$, and let $Y$ induce $Y'$ on the image of $i_0$. Then
$$ \operatorname{tr} Y = \operatorname{tr} Y', \qquad \operatorname{tr}(\mu Y) - \operatorname{tr}(\mu' Y') = \sigma + \overline{\sigma'}. $$
Lean: `New.DiscreteSeries.IsStationary.trace_eq_and_phase_eq` (New/Appendix/DiscreteSeries/Positions.lean).

*Proof.* For the first identity apply the splitting lemma with $\mu = 1$ and $t(a) = a$. Then $i_0^\dagger i_0 = 1$, and the two sums vanish, since $N_{aa} = N'_{aa} = 0$. For the second apply it with the weight $\mu$ and $t(a) = a + 1$, by condition 1 of a stationary position. Condition 2 gives $i_0^\dagger\mu i_0 = \mu'$. The two sums are $\sigma$ and $\sigma'$. $\square$

In section 8 the theorem is applied to $Y = g - 1$ with $g$ in the stabilizer of the flag. Then $Y^\dagger = g^{-1} - 1$, and $\sigma' = -\sigma$. So the phase difference is $\sigma - \overline{\sigma}$, which is imaginary and additive in $g$.

### Polynomials and residues

We now build a stationary position for weights on opposite sides of $0$. Let $\mu_0 > \mu_1 > \dots > \mu_{L-1}$ and $\mu'_0 < \mu'_1 < \dots < \mu'_{L'-1}$ be reals with $\mu_i < \mu'_j$ for all $i$ and $j$.
Lean: `New.DiscreteSeries.AreOppositeNodes` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

Let $p(t) = \prod_i (t - \mu_i)$ and $q(t) = \prod_j (t - \mu'_j)$, and let $q_j = q/(t - \mu'_j)$. For a real polynomial $F$, put
$$ [F]_i = \frac{F(\mu_i)}{\sqrt{|p'(\mu_i)\, q(\mu_i)|}} \qquad (0 \leq i < L). $$
Lean: `New.DiscreteSeries.polyVec` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

On $\mathbb{R}^L$ we use the form $\langle x, y\rangle = \sum_i (-1)^i x_i y_i$.
Lean: `New.DiscreteSeries.alternatingSignForm` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

Multiplication by $\mu$ is multiplication by $t$: $\mu_i [F]_i = [tF]_i$. This is why polynomials are the natural coordinates.

**Lemma (The form as a sum of residues).** For real polynomials $F_1$ and $F_2$,
$$ \langle [F_1], [F_2]\rangle = (-1)^{L'} \sum_{i} \frac{(F_1F_2)(\mu_i)}{p'(\mu_i)\, q(\mu_i)}. $$
Lean: `New.DiscreteSeries.AreOppositeNodes.alternatingSignForm_polyVec` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

*Proof.* Since the $\mu_i$ decrease, $p'(\mu_i) = \prod_{i' \neq i}(\mu_i - \mu_{i'})$ has exactly $i$ negative factors. Since every $\mu_i$ is below every $\mu'_j$, $q(\mu_i)$ has sign $(-1)^{L'}$. So $|p'(\mu_i)q(\mu_i)| = (-1)^{i + L'}p'(\mu_i)q(\mu_i)$. $\square$

The right side is the sum of the residues of $F_1F_2/(pq)$ at the roots of $p$. By Lagrange interpolation, if $R$ is a polynomial of degree at most $L - 1$, then $\sum_i R(\mu_i)/p'(\mu_i)$ is the coefficient of $t^{L-1}$ in $R$.

**Lemma (The columns of the isometry).** Let $L = L' + 2d + 1$. Then $\langle [q_j], [q_{j'}]\rangle = 0$ for $j \neq j'$, and
$$ \langle [q_j], [q_j]\rangle = (-1)^{L'+1}\,\frac{q'(\mu'_j)}{p(\mu'_j)}. $$
Lean: `New.DiscreteSeries.AreOppositeNodes.alternatingSignForm_polyVec_nodal_erase` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

*Proof.* The function $q_j q_{j'}/(pq) = q_j/((t - \mu'_{j'})p)$ is a rational function of degree at most $-2$. So the sum of all its residues is $0$. Its only pole besides the roots of $p$ is at $\mu'_{j'}$, and this pole is cancelled by $q_j$ unless $j = j'$. If $j = j'$, the residue there is $q_j(\mu'_j)/p(\mu'_j) = q'(\mu'_j)/p(\mu'_j)$. $\square$

Put $s_j = |p(\mu'_j)/q'(\mu'_j)|^{1/2}$. Since $p(\mu'_j) > 0$ and $q'(\mu'_j)$ has sign $(-1)^{L' - 1 - j}$, the vectors $s_j[q_j]$ are orthogonal and $\langle s_j[q_j], s_j[q_j]\rangle = (-1)^j$.
Lean: `New.DiscreteSeries.AreOppositeNodes.isometryScale_mul_alternatingSignForm` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

### The construction

Let $e : X \sqcup \{0, \dots, L-1\} \cong n$ and $e' : X \sqcup \{0, \dots, L'-1\} \cong m$. Let $\mu_i$ be the weight of $l$ at $e(i)$ and $\mu'_j$ the weight of $k$ at $e'(j)$. Define
$$ v_{a+1} = [t^a q] \quad (0 \leq a \leq d), $$
on the coordinates $e(i)$, and $0$ on $e(X)$.
Lean: `New.DiscreteSeries.positionVec` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

Define $i_0$ as the identity from $e'(X)$ to $e(X)$, and as $s_j[q_j]$ on the basis vector at $e'(j)$.
Lean: `New.DiscreteSeries.positionIsometry` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

Then $\mu v_{a+1} = [t^{a+1}q] = v_{a+2}$, and $\mu [q_j] = [t q_j] = \mu'_j[q_j] + [q]$, since $tq_j = \mu'_j q_j + q$. So $\mu i_0 = i_0\mu' + v_1 c$ for a row $c$, provided the weights vanish on $X$.
Lean: `New.DiscreteSeries.exists_intDiagonal_mul_positionIsometry` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

In a position, $Mi_0 = i_0 M' + vC$ implies $i_0^\dagger M i_0 = M'$, since $i_0^\dagger i_0 = 1$ and $i_0^\dagger v = 0$.
Lean: `New.DiscreteSeries.IsPosition.formAdjoint_mul_mul_eq` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

**Theorem (The stationary position).** Let $l$ be steep for $(B, e)$ with $B \geq 1$ and $L$ indices outside $X$. Let $L = L' + 2d + 1$. For $k$, let $\eta = 1$ and the weight $\mu' = 0$ on $e'(X)$. Let $\eta_{e'(j)} = (-1)^j$, and let $\mu'_{e'(j)}$ increase strictly in $j$ and lie in $[0, B']$, with $B' \geq 0$. Then there is a stationary position $(v, i_0)$ with $d + 1$ vectors. In it $\langle v_{j_0}, v_{j_0}\rangle_\varepsilon = (-1)^{L'}$, and the entries of $v$, of $i_0$ and of $\mu^a v_1$ for $a \leq 2d$ have modulus at most $(3B + B')^L$.
Lean: `New.DiscreteSeries.IsSteep.exists_isStationary` (New/Appendix/DiscreteSeries/StationaryPosition.lean).

*Proof.* The steep weights decrease in $[-3B, -B]$, and the weights $\mu'$ increase in $[0, B']$. So they are opposite nodes. Take $v$ and $i_0$ as above. On the coordinates outside $X$ the form $\langle\cdot,\cdot\rangle_\varepsilon$ is the alternating form, by steepness.

Independence: the vectors $[t^a q]$ for $a \leq d < L$ are the values of $t^a$ at $L$ distinct points, times the nonzero numbers $q(\mu_i)/\sqrt{|p'(\mu_i)q(\mu_i)|}$.

Pairings of the $v$: by the residue lemma, $\langle [t^a q], [t^b q]\rangle = (-1)^{L'}\sum_i \mu_i^{a+b}q(\mu_i)/p'(\mu_i)$. The polynomial $t^{a+b}q$ has degree $a + b + L' \leq 2d + L' = L - 1$. So the sum is the coefficient of $t^{L-1}$, which is $1$ if $a + b = 2d$ and $0$ otherwise. This gives condition 3 of a position, with $\langle v_{j_0}, v_{j_0}\rangle_\varepsilon = (-1)^{L'}$.

The isometry: on $e(X)$ the sign is $+1$, so $i_0$ is isometric there; off $X$ it is isometric by the scaled lemma on the columns, since $\eta_{e'(j)} = (-1)^j$. The two parts have disjoint supports. Orthogonality: $\langle [q_j], [t^a q]\rangle$ is a sum of residues of $t^a q_j/p$, a polynomial of degree $a + L' - 1 < L - 1$ divided by $p$. So it is $0$.

Stationarity follows from the identities for $\mu$ above. The bounds use that all the nodes are integers. So two distinct nodes differ by at least $1$, and every $|p'(\mu_i)|$, $|q(\mu_i)|$ and $|q'(\mu'_j)|$ is at least $1$. The numerators are at most products of $L$ factors of size at most $3B + B'$. $\square$

**Remark (Formalization).** The statement only asks the weights of $k$ to lie in $[0, B']$ off $X$. It does not ask that $\mu' \leq 3B$, which the Laplace datum needs; section 8 adds this hypothesis separately. For $d = 0$ and $L'$ even, $v_1$ has norm $+1$.
