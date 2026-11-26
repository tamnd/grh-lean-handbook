---
title: Equal traces and equal multiplicities
lean:
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
  - Lib/Adelic/TraceFormula/CuspidalComparison.lean
  - Lib/Adelic/TraceFormula/CuspidalType.lean
  - Lib/Adelic/TraceFormula/LineDeterminant.lean
decls:
  - New.IsAllowedPolynomial
  - New.IsPrimitivePolynomial
  - New.goodTuples
  - New.mem_goodTuples
  - New.Data.goodTupleFamilies
  - New.Data.mem_goodTupleFamilies
  - New.Data.e₀
  - New.Data.exists_isPrimitivePolynomial
  - New.Data.trace_heckeOnGood_eq_sum
  - New.trace_eq_of_isCuspidalAt
  - New.isCuspidalAt_convIndicator_tupleIdem
  - New.Data.trace_mul_tupleIdem_eq
  - New.Data.trace_heckeOnGood_eq
  - New.charpoly_eq_of_trace_pow_eq
  - New.Data.charpoly_heckeOnGood_eq
  - New.Data.det_heckeOnGood_eq
  - New.Data.trace_heckeOnGood_eq_finrank
  - New.Data.finrank_goodForms_inf_eigenPart_eq
  - New.Data.goodForms_inf_eigenPart_eq_bot_of_eq_bot
  - New.Data.targetDim_eq_finrank_goodForms_spaceW
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Equal traces and equal multiplicities

This section proves the main comparison of the chapter. Let $V$ and $V'$ be hermitian spaces of rank $r$ with signs $s$ and $s'$, and suppose that the doubled parameter $l$ has gap $\Delta$ for $s$ and for $s'$. Then every $T \in \mathcal{H}$ has the same trace on $\mathcal{G}(V)$ and on $\mathcal{G}(V')$. Equal dimensions, equal characteristic polynomials and equal multiplicities of eigensystems follow. In this section the gap hypothesis is always this one, and we do not repeat it.

### Good families

We recall the labels of [Green's characters](/chapter/finite-gln/#greens-characters-with-squarefree-labels). Let $k$ be a finite field with $q$ elements. A *label* of degree $r$ is a monic squarefree $c \in k[X]$ of degree $r$ with $c(0) \neq 0$ (`New.IsLabel`). To a label $c$ Green's theory attaches a class function $\Xi_c$ on $\mathrm{GL}_r(k)$, and the element

$$e_c = \sum_{g \in \mathrm{GL}_r(k)} \frac{\Xi_c(1)}{|\mathrm{GL}_r(k)|}\,\overline{\Xi_c(g)}\; g \in \mathbb{C}[\mathrm{GL}_r(k)]$$

(`New.labelIdem`). For a family $c = (c_x)$ of labels over several fields $k_x$, $e_c$ is the tensor product of the $e_{c_x}$ in the group algebra of $\prod_x \mathrm{GL}_r(k_x)$ (`New.tupleIdem`). [Finite general linear groups](/chapter/finite-gln/#greens-characters-with-squarefree-labels) proves that the $e_c$ are orthogonal central idempotents.

**Definition (Allowed and primitive polynomials).** Let $M \geq 1$. A polynomial $c \in k[X]$ is *allowed* for $M$ and $r$ if it is a label of degree $r$ and has no root $z \in k$ with $z^M = 1$. It is *primitive* of degree $r$ if it is a label of degree $r$, it is irreducible, and it has a root in an algebraic closure of order exactly $q^r - 1$.

Lean: `New.IsAllowedPolynomial`, `New.IsPrimitivePolynomial` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

A primitive polynomial is the minimal polynomial over $k$ of a generator of $\mathbb{F}_{q^r}^\times$. It need not be allowed: its roots are not in $k$ when $r \geq 2$, so it is allowed exactly when it is a label, which it is.

**Definition (Good tuples and good families).** Let $(k_w)_{w}$ be a finite family of finite fields. A tuple $c = (c_w)$ with $c_w \in k_w[X]$ monic of degree $r$ is *good* for $M$ and $r$ if every $c_w$ is allowed and at least one $c_w$ is primitive. A family $c = (c_x)$ indexed by the chosen places is a *good family* if, for $i = 0$ and $i = 1$, the tuple $(c_{(i,w)})_w$ over the chosen places above $p_i$ is good for $M = q_2$ and $r$. Finally

$$e_0 = \sum_{c \text{ good family}} e_c.$$

Lean: `New.goodTuples`, `New.mem_goodTuples`, `New.Data.goodTupleFamilies`, `New.Data.mem_goodTupleFamilies`, `New.Data.e₀` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Here $q_2$ is the number `q₂ towerExp` of [the data](/chapter/data-and-sizes/). This chapter does not use the condition on roots of unity. In this chapter only one property of a good family matters.

**Lemma (A primitive member).** Every good family $c$ has a chosen place $x$ at which $c_x$ is primitive.

Lean: `New.Data.exists_isPrimitivePolynomial` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* The tuple above $p_0$ is good, so it has a primitive member. Lean takes $x$ above $p_0$. $\square$

### The trace on good forms as a sum

**Lemma (Trace on good forms).** For $T \in \mathcal{H}$,

$$\operatorname{tr}\big(T \mid \mathcal{G}(V)\big) = \sum_{c \text{ good family}} \operatorname{tr}\big(T_V\, e_c \mid \mathcal{A}_M(V)\big).$$

Lean: `New.Data.trace_heckeOnGood_eq_sum` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

The lemma needs only the gap for $V$. In Lean the gap enters through the type class arguments, not through the proof.

*Proof.* Let $e$ be the action of $e_0$ on $\mathcal{A}_M(V)$. It is idempotent, since $e_0$ is ([`New.Data.isCentralProj_e₀`](/decl/New.Data.isCentralProj_e₀/)). So $\mathcal{G}(V)$ is the range of $e$, and $e$ is the identity on it. The operator $T_V e$ maps all of $\mathcal{A}_M(V)$ into $\mathcal{G}(V)$, as $T_V e y = e T_V y$, and it agrees with $T$ on $\mathcal{G}(V)$. For an operator $A$ that maps the whole space into a subspace $U$, the trace of $A$ equals the trace of its restriction to $U$: in a basis that extends a basis of $U$ the matrix of $A$ has zero rows below $U$. So $\operatorname{tr}(T \mid \mathcal{G}(V)) = \operatorname{tr}(T_V e)$. Finally $T_V e = \sum_c T_V e_c$ by the definition of $e_0$, and the trace is linear. $\square$

### The comparison for one good family

The comparison of traces is the main theorem of [the simple trace formula](/chapter/trace-formula/#the-comparison-of-traces). We state it in the form used here.

**Theorem (Comparison of traces).** Let $E$ have an even number of infinite places, let $r \geq 2$, and let $l$ have gap $500r^3 + 10r^5$ for $s$ and for $s'$ at every infinite place. Let $K$ be a level, let $a$ be in the universal level algebra of $K$, and let $w$ be a split place such that the test function $a \star 1_K$ is cuspidal at $w$. If $T$ and $T'$ act as $a$ on the $K$-fixed forms of type $e_{l,s}$ on $V$ and of type $e_{l,s'}$ on $V'$, then $T$ and $T'$ have the same trace.

Lean: `New.trace_eq_of_isCuspidalAt` (Lib/Adelic/TraceFormula/CuspidalComparison.lean).

The theorem also has the standing hypotheses on $E$ of that chapter: $E$ has a CM type (`CMType E`) and contains the $5040$th roots of unity (`HasPrimitiveRoot5040 E`). The field of the data satisfies them by instances.

The cuspidal test functions come from Green's idempotents. [Test functions and cuspidality](/chapter/trace-formula/#test-functions-and-cuspidality) proves the following.

**Theorem (Cuspidal idempotents).** Let $(w_x)_x$ be a family of finite places such that no place of the family is equal or conjugate to another, or conjugate to itself. Let $c$ be a family of polynomials over their residue fields such that $c_x$ is an irreducible label of degree $r$ for one $x$. Then for every $b \in \mathbb{C}[G_f]$ the test function $(b \cdot \tilde e_c) \star 1_{J}$ is cuspidal at $w_x$, where $\tilde e_c$ is the lift of $e_c$ and $J$ is the kernel of reduction at the places $w_x$.

Lean: `New.isCuspidalAt_convIndicator_tupleIdem` (Lib/Adelic/TraceFormula/CuspidalType.lean).

The reason is that $\Xi_c$ for an irreducible $c$ is, up to sign, the character of a cuspidal representation of $\mathrm{GL}_r(\mathbb{F}_x)$, and the sum of a cuspidal matrix coefficient over a coset of the unipotent radical of a proper parabolic subgroup is $0$. The chosen places satisfy the hypothesis on the family $(w_x)$ (the class `IsConjApart` of Lean), and $J = J_M$.

**Lemma (Equal traces for one family).** For $T \in \mathcal{H}$ and a good family $c$,

$$\operatorname{tr}\big(T_V\, e_c \mid \mathcal{A}_M(V)\big) = \operatorname{tr}\big(T_{V'}\, e_c \mid \mathcal{A}_M(V')\big).$$

Lean: `New.Data.trace_mul_tupleIdem_eq` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Let $a \in \mathcal{S}$ give $T$, and let $x$ be a chosen place with $c_x$ primitive, by the lemma on a primitive member. Let

$$\phi = a \cdot \tilde e_c \in \mathbb{C}[G_f],$$

where $a$ is read in $\mathbb{C}[G_f]$. We check the hypotheses of the comparison with $K = J_M$, the element $\phi$ and the place $x$.

1. $\phi$ lies in the universal level algebra of $J_M$. Both factors do: $a$ by the definition of $\mathcal{S}$, and $\tilde e_c$ by the lemma on lifts. The universal level algebra is a subalgebra.
2. $\phi$ acts as $T_V e_c$ on $\mathcal{A}_M(V)$ for every $V$. Indeed $e_c$ acts as $\rho_V(\tilde e_c)$, by the definition of the action of $\bar G$, and $T_V$ acts as $\rho_V(a)$.
3. The test function $\phi \star 1_{J_M}$ is cuspidal at $x$. The label $c_x$ is primitive, hence an irreducible label of degree $r$, and the theorem on cuspidal idempotents applies with $b = a$.
4. The sizes. The number $f$ of infinite places of $E$ is even ([`New.Data.f_even`](/decl/New.Data.f_even/)). The rank is $r \geq 2$, and $500r^3 + 10r^5 \leq \Delta$. Both inequalities are among the size inequalities of the data and are proved by the size automation `HasLogBound` of [the data and their sizes](/chapter/data-and-sizes/). Since the gap condition is monotone in the gap, gap $\Delta$ gives gap $500r^3 + 10r^5$.

So the comparison of traces gives the equality. $\square$

**Theorem (Equal traces).** For every $T \in \mathcal{H}$,

$$\operatorname{tr}\big(T \mid \mathcal{G}(V)\big) = \operatorname{tr}\big(T \mid \mathcal{G}(V')\big).$$

Lean: `New.Data.trace_heckeOnGood_eq` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Write both sides as sums over good families by the lemma on the trace on good forms, and compare the terms by the previous lemma. $\square$

This is the place where the good forms are needed. On all of $\mathcal{A}_M(V)$ the trace of $T$ is a sum over all types of $\bar G$, including those whose test function is not cuspidal at any place. For those types the trace formula has Eisenstein and residual terms, and the two traces can differ. The idempotent $e_0$ keeps only types with a primitive label at some chosen place.

**Remark (Formalization).** The trace is Mathlib's `LinearMap.trace`, which is $0$ on a module that is not finite and free. Here $\mathcal{A}_M(V)$ is finite-dimensional by an instance (New/UpperBound/Objects/Rows.lean), and so are $\mathcal{G}(V)$ and every eigenpart, as subspaces. So all traces of this section are honest traces. The same holds for `Module.finrank`, which is $0$ on a module of infinite rank.

### Characteristic polynomials and determinants

**Theorem (Equal characteristic polynomials).** For every $T \in \mathcal{H}$, $T|_{\mathcal{G}(V)}$ and $T|_{\mathcal{G}(V')}$ have the same characteristic polynomial and the same determinant.

Lean: `New.Data.charpoly_heckeOnGood_eq`, `New.Data.det_heckeOnGood_eq` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Since $T \mapsto T|_{\mathcal{G}(V)}$ is multiplicative, $(T|_{\mathcal{G}(V)})^n = T^n|_{\mathcal{G}(V)}$, and $T^n \in \mathcal{H}$. So the theorem on equal traces gives $\operatorname{tr}(A^n) = \operatorname{tr}(A'^n)$ for $A = T|_{\mathcal{G}(V)}$, $A' = T|_{\mathcal{G}(V')}$ and all $n \geq 0$. By the next lemma $A$ and $A'$ have the same characteristic polynomial. The determinant is $(-1)^d$ times the constant coefficient, with $d$ the degree of the characteristic polynomial, so it is determined by the characteristic polynomial. $\square$

**Lemma (Traces of powers).** Let $A$ and $A'$ be endomorphisms of finite-dimensional complex vector spaces with $\operatorname{tr}(A^n) = \operatorname{tr}(A'^n)$ for all $n \geq 0$. Then $A$ and $A'$ have the same characteristic polynomial.

Lean: `New.charpoly_eq_of_trace_pow_eq` (Lib/Adelic/TraceFormula/LineDeterminant.lean).

*Proof.* We give the proof of the source. Let $\mu \in \mathbb{C}$ and let $B_\mu$ be the generalized eigenspace of $A$ for $\mu$. For a polynomial $P$, $\operatorname{tr} P(A) = \sum_\mu \dim B_\mu\, P(\mu)$, and the same holds for $A'$. The two sums agree for every $P$ by linearity. Choose $P$ with $P(\mu) = 1$ and $P(\nu) = 0$ at the other eigenvalues $\nu$ of $A$ and $A'$. Then $\dim B_\mu = \dim B'_\mu$, after the cast from $\mathbb{N}$ to $\mathbb{C}$, which is injective. These dimensions are the multiplicities of the roots of the characteristic polynomials, which are monic and split over $\mathbb{C}$. $\square$

The case $n = 0$ is used: $\operatorname{tr}(A^0) = \dim$. Without it, the traces of positive powers determine the characteristic polynomial only up to a power of $X$. The proof also uses that $\mathbb{N} \to \mathbb{C}$ is injective, so it uses characteristic $0$. The research notes describe this step by Newton's identities. The source does not use them.

### Multiplicities

**Lemma (The trace of a projector).** Let $q$ be an eigensystem and let $T \in \mathcal{H}$ satisfy, for every eigensystem $d$ and $y \in \mathcal{A}_M(V)_d$, $T_V y = y$ if $d = q$ and $T_V y = 0$ otherwise. Then

$$\operatorname{tr}\big(T \mid \mathcal{G}(V)\big) = \dim\big(\mathcal{G}(V) \cap \mathcal{A}_M(V)_q\big).$$

Lean: `New.Data.trace_heckeOnGood_eq_finrank` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* The eigenparts span $\mathcal{A}_M(V)$, and $T_V$ maps each of them into $\mathcal{A}_M(V)_q$. So $T_V$ maps $\mathcal{A}_M(V)$ into $\mathcal{A}_M(V)_q$, and $T|_{\mathcal{G}(V)}$ maps $\mathcal{G}(V)$ into $\mathcal{G}(V) \cap \mathcal{A}_M(V)_q$. It is the identity on that subspace. So $T|_{\mathcal{G}(V)}$ is a projection onto $\mathcal{G}(V) \cap \mathcal{A}_M(V)_q$, and the trace of a projection is the dimension of its range. $\square$

**Theorem (Equal multiplicities).** For every eigensystem $q$,

$$\dim\big(\mathcal{G}(V) \cap \mathcal{A}_M(V)_q\big) = \dim\big(\mathcal{G}(V') \cap \mathcal{A}_M(V')_q\big).$$

In particular, if $q$ does not occur in the good forms of $V'$, it does not occur in those of $V$.

Lean: `New.Data.finrank_goodForms_inf_eigenPart_eq`, `New.Data.goodForms_inf_eigenPart_eq_bot_of_eq_bot` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* Let $F$ be the set of eigensystems $d$ with $\mathcal{A}_M(V)_d \neq 0$ or $\mathcal{A}_M(V')_d \neq 0$. It is finite by the lemma on finitely many eigensystems. The theorem on projectors gives $T \in \mathcal{H}$ that is $1$ on the $q$-part and $0$ on the $d$-part for $d \in F$, $d \neq q$, on both spaces. For $d \notin F \cup \{q\}$ the $d$-parts are $0$ on both spaces, so $T$ satisfies the hypothesis of the previous lemma on $V$ and on $V'$. The two traces are equal by the theorem on equal traces. So the two dimensions are equal in $\mathbb{C}$, hence in $\mathbb{N}$. The second statement is the case where the right side is $0$. $\square$

This is the analogue of the Jacquet-Langlands correspondence in the form that the source needs: an equality of multiplicities of Hecke eigensystems away from the level, restricted to the good types at the level. It says nothing about the representations at the chosen places or at the real places beyond their types.

### Equal dimensions

**Theorem (Equal dimensions).** For each lift index $j$, $d_T = \dim \mathcal{G}(W_j)$.

Lean: `New.Data.targetDim_eq_finrank_goodForms_spaceW` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

*Proof.* The parameter $l$ has gap $\Delta$ for the signs of $Y_0$ and of $W_j$; these are the instances `New.Data.hasGap_signsY_paramW` and `New.Data.hasGap_paramW`. Apply the theorem on equal traces with $V = Y_0$, $V' = W_j$ and $T = 1$. The trace of the identity is the dimension, and $d_T = \dim \mathcal{G}(Y_0)$ by definition. $\square$

### An example

The role of cuspidality shows already for $\mathrm{GL}_2$ in the model case of the opening section. On the definite side the constant function on the class set is a form of weight $2$ with the eigenvalue $\ell + 1$ of $T_\ell$. On the side of $\Gamma_0(p)$ the corresponding form is the Eisenstein series, which is not a cusp form. Eichler's identity $h = \dim S_2(\Gamma_0(p)) + 1$ has the term $1$ for this reason. In the unitary setting the analogous forms are the one-dimensional representations, which factor through the determinant. At a chosen place $x$ such a form transforms under $\mathrm{GL}_r(\mathbb{F}_x)$ by a character $\chi \circ \det$. That is an irreducible constituent of a representation induced from the Borel subgroup, so it is not cuspidal, and $e_c$ with $c_x$ irreducible of degree $r \geq 2$ kills it. So no correction term appears in the theorem on equal dimensions.
