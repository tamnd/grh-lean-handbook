---
title: Branching and duality
lean:
  - Lib/GLn/Branching/IntegralMap.lean
  - Lib/GLn/Branching/NormBound.lean
  - Lib/GLn/Dual.lean
decls:
  - New.SpansBranchingMaps
  - New.GL.branchVector
  - New.GL.exists_smul_weylKernel_mul_eq_toPoly
  - New.GL.exists_int_branching_of_weylKernel
  - New.GL.weylNormSq_mulVec_le_of_equivariant
  - New.GL.exists_cyclic_lower_triangular
  - New.GL.spansBranchingMaps_of_equivariant
  - New.exists_branching_matrix
  - New.GL.exists_star_matrix
  - New.GL.exists_int_duality_matrix
  - New.GL.IsDualIsometry
  - New.exists_isDualIsometry
  - New.exists_dual_isometry
  - New.GL.exists_weylGram_mul_eq_hookNumber_dual_smul
  - New.GL.exists_toPoly_eq_hookNumber_dual_smul
  - New.mixedWeight
  - New.GL.MixedCartanEmbedding
  - New.nonempty_mixedCartanEmbedding
  - New.mixedCartan
  - New.IsDualPairing
  - New.exists_isDualPairing_of_isHCParam
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Branching and duality

This section gives the maps between Weyl modules that the source uses: the branching map from $GL_{n+1}$ to $GL_n \times GL_1$, the duality with the reversed weight, the Cartan embedding of a mixed weight, and an invariant pairing between the parameters $l$ and $-l$. All four are integer matrices.

### The branching rule

The textbook statement is the branching rule with multiplicity one. The restriction of the irreducible representation $V_\lambda$ of $GL_{n+1}(\mathbb C)$ to $GL_n(\mathbb C)$ is the direct sum of the $V_\mu$ over the $\mu$ with $\lambda_1 \ge \mu_1 \ge \lambda_2 \ge \cdots \ge \mu_n \ge \lambda_{n+1}$, each once. See Goodman and Wallach, *Symmetry, Representations, and Invariants*, 2009, Theorem 8.1.1, and Zhelobenko, *Compact Lie Groups and their Representations*, 1973, Chapter X. The corner $GL_1$ acts on $V_\mu$ by $s^{|\lambda| - |\mu|}$.

The source does not state the decomposition. For one interlacing pair it constructs an integer matrix that is equivariant, bounds its norm and shows that every equivariant map is a multiple of it.

The pair is given in terms of columns. Let $N_\tau$ be the rows $n_\tau$ with one new row added, by an equivalence $\iota_\tau : n_\tau \sqcup \{\ast\} \simeq N_\tau$. Write $\kappa = \gamma + \kappa'$: of the $\kappa_\tau(h)$ columns of height $h$, there are $\gamma_\tau(h)$ that lose a box and $\kappa'_\tau(h)$ that keep theirs. The weight $\kappa_0$ for $n$ is
$$\kappa_0(\tau, h) = \kappa'_\tau(h) + \gamma_\tau(h + 1), \qquad 0 < h < |n_\tau|.$$
The columns of height $|n_\tau|$ that keep their box are full columns for $n$. They become powers of the determinant: $e_0(\tau) = e(\tau) + \kappa'_\tau(|n_\tau|)$. The choice of $\gamma$ and $\kappa'$ is the interlacing condition in the language of columns. The matrix `New.GL.blockScalar` $\iota\, g\, s$ is the block matrix $\operatorname{diag}(g_\tau, s_\tau)$ along $\iota$.

**Definition.** A complex matrix $A$ from coordinates of weight $\kappa$ for $N$ to those of weight $\kappa_0$ for $n$ *spans the branching maps* if the following holds. Let $T$ be a complex matrix such that for every unitary family $g$ the matrix $x = \operatorname{diag}(g, 1)$ satisfies $T \rho_{\kappa, e}(x) = \rho_{\kappa_0, e_0}(g) T$. Then $T = aA$ for some $a \in \mathbb C$.

Lean: `New.SpansBranchingMaps` (Lib/GLn/Branching/IntegralMap.lean).

**Theorem (branching matrix).** Assume the relations above, and let $\kappa'_\tau(i) = 0$ for $i < q$. Then there is an integer matrix $br$ with three properties.

1. Over every field $R$ of characteristic $0$, for invertible families $g$, units $s$ and $x = \operatorname{diag}(g, s)$,
$$br \cdot \rho_{\kappa, e}(x) = \Big(\prod_\tau s_\tau^{\mu_\gamma(\tau, 0) + e_\tau}\Big) \cdot \rho_{\kappa_0, e_0}(g) \cdot br,$$
where $\mu_\gamma(\tau, 0)$ is the diagram weight of $\gamma$ at row $0$, the number of columns of $\gamma$.
2. If $\sum_\tau \sum_{q \le h < |n_\tau|} h \, \kappa_0(\tau, h) \le L$, then $\|br\, \xi\|^2 \le \big((L^L)^3\big)^2 \|\xi\|^2$ for every complex $\xi$.
3. $br$ spans the branching maps.

Lean: `New.exists_branching_matrix` (Lib/GLn/Branching/IntegralMap.lean).

The sum in item 2 is the number of boxes of $\kappa_0$ in the columns of height at least $q$. So the operator norm of $br$ is at most $L^{3L}$. For $q = 0$ the hypothesis on $\kappa'$ is empty.

**Remark (Formalization).** The theorem does not state that $br \neq 0$. With $br = 0$, item 3 would say that every equivariant map is $0$, which is the opposite of the textbook rule. The proof shows $br \neq 0$ as the local fact `value_ne` inside the proof of `New.GL.spansBranchingMaps_of_equivariant`, but no exported lemma states it. A user who needs it must repeat the construction below and use item (a) of `New.GL.exists_int_branching_of_weylKernel`.

The proof has three parts.

*The branch vector.* Let `New.GL.branchVector` be the product of the leading minors to the powers $\gamma$, read with the new row first, times the product of the leading minors to the powers $\kappa'$, read with the new row last. It plays the role of a highest weight vector of the summand $V_\mu$. The lemma `New.GL.exists_smul_weylKernel_mul_eq_toPoly` gives an integer $c$ with $0 < c \le (L^L)^3$ and an integer vector $\eta$ such that
$$c \cdot \operatorname{kernel}_\gamma(P_1) \cdot \operatorname{kernel}_{\kappa'}(P) = \operatorname{toPoly}_{\kappa_0}(\eta),$$
where $P$ is the permutation array of the fixed numbering of the rows and $P_1$ is the same array shifted cyclically by one. The number $c$ is a hook number, and the bound is the one of Section 5. The hook number clears the denominators of the inverse Gram matrix.

*The integral matrix.* The lemma `New.GL.exists_int_branching_of_weylKernel` turns $\eta$ into an integer matrix $B$. Its row vector at the kernel of $\kappa_0$ has the polynomial $c$ times the branch vector. And over every field of characteristic $0$,
$$B \, S_{\gamma + \kappa'}(\operatorname{diag}(g, s)) = \Big( \prod_\tau s_\tau^{\mu_\gamma(\tau, 0)} \det(g_\tau)^{\kappa'_\tau(|n_\tau|)} \Big) S_{\kappa_0}(g) B.$$
The matrix $B$ is read off from the coefficients of a kernel in two arrays, as the Gram matrix was in Section 5. So it has integer entries by construction, and the equivariance is a substitution of rows.

*Norm and uniqueness.* The lemma `New.GL.weylNormSq_mulVec_le_of_equivariant` shows $\|B\xi\|^2 \le c^2 \|\xi\|^2$, which is item 2. The lemma `New.GL.exists_cyclic_lower_triangular` gives a vector $v$ whose images under $S_\kappa(\operatorname{diag}(g, 1))$, for lower triangular $g$, span. So an equivariant $T$ is determined by one number $x\, T\, v$. The lemma `New.GL.spansBranchingMaps_of_equivariant` applies this to $T - aB$, with $a$ chosen so that this number is $0$, which needs $c \neq 0$. $\square$

Lean: `New.GL.branchVector` (Lib/GLn/Branching/NormBound.lean), `New.GL.exists_smul_weylKernel_mul_eq_toPoly`, `New.GL.weylNormSq_mulVec_le_of_equivariant` (Lib/GLn/Branching/NormBound.lean), `New.GL.exists_int_branching_of_weylKernel`, `New.GL.exists_cyclic_lower_triangular`, `New.GL.spansBranchingMaps_of_equivariant` (Lib/GLn/Branching/IntegralMap.lean).

The source cites Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, arXiv:math/0211289, for the Gelfand-Tsetlin theory that iterates this rule.

### Duality

The textbook fact is that the dual of the irreducible representation of highest weight $(\lambda_1, \dots, \lambda_n)$ has highest weight $(-\lambda_n, \dots, -\lambda_1)$. In terms of columns, the column counts are reversed and a power of the determinant is added. The source proves this as a statement about an integer matrix, through the Hodge star of each column and Jacobi's identity for complementary minors (Grinberg, *An Introduction to Algebraic Combinatorics*, Theorem 6.4.48).

Let $e_\tau$ be an enumeration of the rows of $n_\tau$, and let $e'$ be the reversed enumeration. Let $\kappa'_\tau(h) = \kappa_\tau(|n_\tau| - h)$ for $1 \le h < |n_\tau|$.

**Lemma (star).** There is an integer matrix $P$ from the basis tensors of $\kappa'$ to those of $\kappa$ with $P^{\mathsf T} P = 1$, such that the following holds over every commutative ring. If the square part $g$ of an array $y$ for $e$ is invertible and the square part of an array $z$ for $e'$ is $g^{-\mathsf T}$, then $P$ sends the tensor of $y$ to $\prod_\tau \det(g_\tau)^{\lambda_\tau}$ times the tensor of $z$, where $\lambda_\tau$ is the diagram weight of $\kappa$ at $(\tau, 0)$.

Lean: `New.GL.exists_star_matrix` (Lib/GLn/Dual.lean).

*Proof.* A basis tensor is a filling of the columns. Replace each column, a set of $h$ rows, by its complement, a set of $|n| - h$ rows. This is a bijection of fillings (`New.fillingComplement`). The sign is the sign of the complementary minor in Jacobi's identity: a minor of $g^{-\mathsf T}$ is $\pm \det(g)^{-1}$ times the complementary minor of $g$. $\square$

**Lemma (duality matrix).** There are $P$ as above and an integer matrix $J$, from coordinates of weight $\kappa'$ to those of weight $\kappa$, with $F_\kappa J = P F_{\kappa'}$ for the tensor embeddings $F$ of Section 4. Over every commutative ring and for every invertible $g$,
$$J\, S_{\kappa'}(g) \operatorname{ev}_e = \prod_\tau \det(g_\tau)^{\lambda_\tau} \cdot S_\kappa(g^{-\mathsf T}) \operatorname{ev}_{e'}.$$

Lean: `New.GL.exists_int_duality_matrix` (Lib/GLn/Dual.lean).

*Proof.* Put $J = Q P F_{\kappa'}$, with $Q$ the integer left inverse of $F_\kappa$ of Section 4. The identity $F_\kappa J = P F_{\kappa'}$ needs that $P$ maps the image of $F_{\kappa'}$ into the image of $F_\kappa$. The source checks this with the star lemma on the translates of evaluation vectors. $\square$

**Definition.** An integer matrix $J$ is a *dual isometry* for $e$ if:

1. $J$ has a two-sided integer inverse;
2. $J^{\mathsf T} G_\kappa J = G_{\kappa'}$;
3. over every field of characteristic $0$, $J \operatorname{ev}_{e} = \operatorname{ev}_{e'}$, the evaluation vectors at the permutation arrays;
4. over every field of characteristic $0$, $S_\kappa(g^{-\mathsf T}) J = J \rho_{\kappa', -d}(g)$, where $d_\tau = \sum_{1 \le h < |n_\tau|} \kappa_\tau(h)$.

Lean: `New.GL.IsDualIsometry` (Lib/GLn/Dual.lean).

**Theorem (duality).** If $\kappa'_\tau(h) = \kappa_\tau(|n_\tau| - h)$ for $1 \le h < |n_\tau|$, then for every enumeration $e$ there is a dual isometry $J$.

Lean: `New.exists_isDualIsometry`, and the same statement as one conjunction, `New.exists_dual_isometry` (Lib/GLn/Dual.lean).

*Proof.* Take $J$ from the duality matrix lemma, and $K$ from the same lemma with $e$ and $e'$ exchanged. Then $JK$ and $KJ$ commute with all $S(g)$ on the evaluation vectors, which span. So $JK = 1$ and $KJ = 1$. The isometry follows from $G = F^{\mathsf T} F$ and $P^{\mathsf T} P = 1$. $\square$

**Remark (Formalization).** The matrix $J$ identifies the lattice of weight $\kappa'$ with that of weight $\kappa$ composed with $g \mapsto g^{-\mathsf T}$. Over $\mathbb Q$ this is the dual representation. Over $\mathbb Z$ it is not the dual lattice, since $G$ is not unimodular.

**Corollary.** For the reversed weight $\kappa'$:

1. there is an integer matrix $B$ with $G_\kappa B = \operatorname{hook}(\kappa') \cdot 1$;
2. for every semi-invariant $f$ of weight $\kappa$ over a commutative ring, $\operatorname{hook}(\kappa') f = \operatorname{toPoly}(\zeta)$ for some coordinate vector $\zeta$.

Lean: `New.GL.exists_weylGram_mul_eq_hookNumber_dual_smul`, `New.GL.exists_toPoly_eq_hookNumber_dual_smul` (Lib/GLn/Dual.lean).

*Proof.* Take $B = J H' J^{\mathsf T}$, with $H'$ the Fock matrix of $\kappa'$. Then $G_\kappa B = K^{\mathsf T} (J^{\mathsf T} G_\kappa J) H' J^{\mathsf T} = K^{\mathsf T} G_{\kappa'} H' J^{\mathsf T}$, and $G_{\kappa'} H' = \operatorname{hook}(\kappa') \cdot 1$ by Section 5. For item 2 take $\zeta = B c$, with $c$ the coordinates of $f$. $\square$

### The mixed Cartan embedding

A *mixed weight* has a positive part $k_p$ and a negative part $k_m$. The source defines `New.mixedWeight` as the weight with $k_p(\tau, i) + k_m(\tau, |n| - i)$ columns of height $i$. It is the Cartan component of the tensor product of the representation of weight $k_p$ and the dual of the representation of weight $k_m$ (Fulton and Harris, *Representation Theory: A First Course*, 1991, Section 15.5).

Lean: `New.mixedWeight` (Lib/GLn/Dual.lean).

**Remark (Formalization).** The subtraction $|n| - i$ is truncated subtraction of natural numbers. For $0 < i < |n|$ it is the usual difference. For $i \ge |n|$ it gives $0$, so the value is $k_p(\tau, i) + k_m(\tau, 0)$. At $i = 0$ the value is $k_p(\tau, 0) + k_m(\tau, |n|)$. These values at the ends have no textbook meaning.

**Definition.** A *mixed Cartan embedding* for weights $k_p$, $k_m$ and $l$ is an integer matrix $M$ from coordinates of weight $l$ to pairs of coordinates of weights $k_p$ and $k_m$ such that:

1. $M$ has an integer left inverse;
2. $M^{\mathsf T} (G_{k_p} \otimes G_{k_m}) M = G_l$;
3. over every field of characteristic $0$, $M$ sends the evaluation vector of $l$ at the identity frame to the tensor of the evaluation vector of $k_p$ at the identity and that of $k_m$ at the reversed frame;
4. over every field of characteristic $0$, $M \rho_{l, -d}(g) = (S_{k_p}(g) \otimes S_{k_m}(g^{-\mathsf T})) M$, with $d_\tau = \sum_{1 \le i < |n|} k_m(\tau, i)$.

Lean: `New.GL.MixedCartanEmbedding` (Lib/GLn/Dual.lean).

**Theorem.** A mixed Cartan embedding exists for $l = $ `New.mixedWeight` $k_p\, k_m$.

Lean: `New.nonempty_mixedCartanEmbedding`, and the chosen one `New.mixedCartan` (Lib/GLn/Dual.lean).

*Proof.* Let $k_c$ be $k_m$ with reversed columns. Then the mixed weight is $k_p + k_c$. Take $M = (1 \otimes J)\, C$, where $C$ is the coproduct matrix of Section 6 for $k_p$ and $k_c$, and $J$ is the dual isometry from $k_c$ to $k_m$. Each property of $M$ follows from the matching properties of $C$ and of $J$. $\square$

**Remark (Formalization).** `New.mixedCartan` is chosen by `Nonempty.some`. Only the four properties of the structure are available about it.

### The dual pairing

The last result connects the duality with the automorphic forms of the source. Let $E$ be a CM field, and let $l$ list twice the Harish-Chandra parameter of $(\kappa, e)$ at each infinite place, in the sense of `New.IsHCParam` of Section 6.

**Definition.** An integer matrix $A$ is a *dual pairing* for $(\kappa, e)$, $(\kappa', e')$ and $l$ if:

1. the bilinear pairing $v'^{\mathsf T} A v$ is invariant under $\rho_{\kappa', e'}(g) \times \rho_{\kappa, e}(g)$, over every field of characteristic $0$;
2. for every algebraic form $\eta$ of weight $(\kappa', e')$, the function `New.ofAlgForm` at $-l$ is the pairing of the value of $\eta$ with the translate of the highest vector of $l$;
3. there is an integer matrix $C$ with $CA = \operatorname{hook}(\kappa') \cdot 1$;
4. for every $v$ there is $v'$ with $\|v'\| = \|v\|$ and $u^{\mathsf T} A v = \langle v', u \rangle$ for all $u$.

Lean: `New.IsDualPairing` (Lib/GLn/Dual.lean).

**Theorem.** If $l$ lists twice the Harish-Chandra parameter of $(\kappa, e)$ and $-l$ that of $(\kappa', e')$, a dual pairing exists.

Lean: `New.exists_isDualPairing_of_isHCParam` (Lib/GLn/Dual.lean).

*Proof.* Number the rows by decreasing $l$, so that $\kappa'$ is the reversed weight of $\kappa$. Put $A = G_{\kappa'} J$ with $J$ the dual isometry. Invariance follows from item 4 of the dual isometry, with the determinant power computed by `New.IsHCParam.add_eq_neg_sum_of_neg`. Item 3 follows from $G_{\kappa'} H' = \operatorname{hook}(\kappa') \cdot 1$. Item 4 holds with $v' = \overline{Jv}$, by $J^{\mathsf T} G_{\kappa'} J = G_\kappa$. $\square$

The theorem is used in `New/Determinant/AuxiliaryForms/LastPath.lean` in the proof of Theorem C.
