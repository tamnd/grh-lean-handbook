---
title: Eigensystems and projectors
lean:
  - New/Spanning/Multiplicities/HeckeEigensystems.lean
  - Lib/Weil/Unramified/SplitHecke.lean
decls:
  - New.Data.eigenPart
  - New.Data.mem_eigenPart
  - New.Data.hasHeckePolynomial_of_mem_eigenPart
  - New.Data.smul_mul_heckeOperator_sub_smul_apply
  - New.Data.exists_hecke_proj_eigenPart
  - New.Data.principalRep_mem_eigenPart
  - New.Data.iSupIndep_eigenPart
  - New.Data.finite_setOf_inf_eigenPart_ne_bot
  - New.Data.exists_mem_eigenPart_of_heckeSplit_eq_smul
  - New.Data.iSup_eigenPart_eq_top
  - New.IsUnitary.le_span_hecke_eigenvectors
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Eigensystems and projectors

A trace is a sum over eigenvalues. To pass from traces to multiplicities one needs operators that pick out one eigensystem. This section splits $\mathcal{A}_M(V)$ into the parts of the joint eigensystems of the operators $T_x$, proves that the parts are independent and that they span, and builds, for one eigensystem $q$ and finitely many others, an element of $\mathcal{H}$ that is $1$ on the $q$-part and $0$ on the others. The element is the same for all spaces $V$. This uniformity is what makes the projector useful in the comparison of traces.

Let $\mathcal{X}$ be the set of pairs $x = (w, i)$ of a finite place $w$ of $E$ and a natural number $i$. An *eigensystem* is a function $q : \mathcal{X} \to \mathbb{C}$.

### Eigenparts

**Definition (Eigenpart).** For an eigensystem $q$, the $q$-part of $\mathcal{A}_M(V)$ is

$$\mathcal{A}_M(V)_q = \bigcap_{x \in \mathcal{X}} \ker\big(T_{x,V} - q(x)\big) = \{y \in \mathcal{A}_M(V) : T_{x,V}\,y = q(x)\,y \text{ for all } x \in \mathcal{X}\}.$$

Lean: `New.Data.eigenPart`, `New.Data.mem_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

At a pair $x = (w, i)$ with $w$ not split away from the level, $T_x = 0$, and the condition is $q(x)\,y = 0$. So $\mathcal{A}_M(V)_q = 0$ unless $q$ vanishes at all such pairs. The remark on $T_x$ in [the previous section](/chapter/equal-multiplicities/#hecke-operators-away-from-the-level) explains this junk value.

The eigenvalues at one place determine the Satake parameters there. [Iwahori and Satake](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials) defines, for a split place $w$ with residue field of $q_w$ elements and a sequence $t_0, \dots, t_r$, the value

$$P_w(t; X) = \sum_{i = 0}^{r} (-X)^i\, q_w^{\binom{i}{2}}\, t_i,$$

and says that a vector $y$ *has Hecke polynomial* $p$ at $w$ if $y$ is spherical at $w$ and $P_w(T_{w,\bullet}; X)\,y = p(X)\,y$ for every $X \in \mathbb{C}$. Lean names: `New.heckePolyEval`, `New.HasHeckePolynomial`.

**Lemma (Hecke polynomial of an eigenform).** Let $y \in \mathcal{A}_M(V)_q$ and let $w$ be split away from the level. Then $y$ has the Hecke polynomial $X \mapsto P_w(q(w, \bullet); X)$ at $w$.

Lean: `New.Data.hasHeckePolynomial_of_mem_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The form $y$ is spherical at $w$ by the lemma on spherical forms, and $T_{w,i}\,y = q(w, i)\,y$ for each $i$. Apply $P_w$ term by term. $\square$

Outside this chapter the lemma is used in New/Determinant/Norms/AdjointThetaLift.lean, which belongs to [Theorem C](/chapter/theorem-c-plan/). Inside this chapter the eigensystem itself is enough.

### Independence and spanning

**Lemma (Independence).** The family $(\mathcal{A}_M(V)_q)_q$ of subspaces is independent: each part meets the sum of the others in $0$.

Lean: `New.Data.iSupIndep_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* For one operator $T_{x,V}$, eigenspaces for distinct eigenvalues are independent. If $q \neq q'$ then $q(x) \neq q'(x)$ for some $x$, and $\mathcal{A}_M(V)_q$ lies in the $q(x)$-eigenspace of $T_{x,V}$. An intersection over $x$ of independent families of eigenspaces is again independent; in Lean this is `iSupIndep.iInf`. $\square$

**Lemma (Finitely many eigensystems).** For every subspace $N$ of $\mathcal{A}_M(V)$, the set of eigensystems $q$ with $N \cap \mathcal{A}_M(V)_q \neq 0$ is finite.

Lean: `New.Data.finite_setOf_inf_eigenPart_ne_bot` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The spaces $N \cap \mathcal{A}_M(V)_q$ are independent by the previous lemma. In a finite-dimensional space, an independent family has at most $\dim$ nonzero members. $\square$

The Lean statement has the hypothesis that $\mathcal{A}_M(V)$ is finite over $\mathbb{C}$. It is an instance for every $V$ (New/UpperBound/Objects/Rows.lean), so at the points of use it is supplied without comment.

**Lemma (Joint eigenvectors).** Let $y \in \mathcal{A}_M(V)$ be an eigenvector of $T_{w,i}$ for every $w$ split away from the level and every $i$. Then $y \in \mathcal{A}_M(V)_q$ for some eigensystem $q$.

Lean: `New.Data.exists_mem_eigenPart_of_heckeSplit_eq_smul` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Let $q(w, i)$ be the eigenvalue of $T_{w,i}$ on $y$ if $w$ is split away from the level, and $q(w, i) = 0$ otherwise. At the other places $T_x = 0$ and $T_x y = 0 = q(x)\,y$. Lean picks the eigenvalues by choice. $\square$

The next result is the spectral theorem for the operators $T_{w,i}$, from [Iwahori and Satake](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials). It is background, and we state it without proof.

**Theorem (Joint eigenvectors of Hecke operators).** Let $\pi$ be a representation of $G_f$, unitary for a positive definite hermitian form, let $P$ be a set of split places closed under conjugation, and let $U$ be a finite-dimensional subspace that is spherical at every $w \in P$ and stable under every $T_{w,i}$, $w \in P$. Then $U$ is spanned by the vectors of $U$ that are eigenvectors of all $T_{w,i}$, $w \in P$.

Lean: `New.IsUnitary.le_span_hecke_eigenvectors` (Lib/Weil/Unramified/SplitHecke.lean).

The proof there uses that $T_{w,i}$ and $T_{\bar w,i}$ commute and are adjoint, so each $T_{w,i}$ is normal on $U$, and a commuting family of normal operators on a finite-dimensional space has a basis of joint eigenvectors.

**Theorem (The eigenparts span).** $\sum_q \mathcal{A}_M(V)_q = \mathcal{A}_M(V)$. With the independence lemma, $\mathcal{A}_M(V) = \bigoplus_q \mathcal{A}_M(V)_q$, with finitely many nonzero summands.

Lean: `New.Data.iSup_eigenPart_eq_top` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The representation $\rho_V$ of $G_f$ on forms is unitary for the Petersson inner product. Apply the spectral theorem with $P$ the set of places split away from the level, which is closed under conjugation, and $U = \mathcal{A}_M(V)$. The hypotheses hold by the lemma on spherical forms. So $\mathcal{A}_M(V)$ is spanned by joint eigenvectors of the $T_{w,i}$. By the previous lemma each of them lies in some $\mathcal{A}_M(V)_q$. $\square$

**Lemma ($\bar G$ keeps eigenparts).** For $\xi \in \mathbb{C}[\bar G]$ and $y \in \mathcal{A}_M(V)_q$, also $\xi y \in \mathcal{A}_M(V)_q$.

Lean: `New.Data.principalRep_mem_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* $T_{x,V}\,\xi y = \xi\,T_{x,V}\,y = q(x)\,\xi y$, since $\mathcal{H}$ commutes with $\bar G$. $\square$

So $e_0$ maps $\mathcal{A}_M(V)_q$ into itself, and $\mathcal{G}(V) = \bigoplus_q \big(\mathcal{G}(V) \cap \mathcal{A}_M(V)_q\big)$. The dimension of $\mathcal{G}(V) \cap \mathcal{A}_M(V)_q$ is the *multiplicity* of $q$ in the good forms of $V$. The section on equal traces compares these multiplicities.

### Projectors

The projector is a product of Lagrange factors. If $T$ acts on a form $y$ of eigensystem $d$ by a scalar, then $T T_x - b T$ acts on $y$ by that scalar times $d(x) - b$. One factor of this kind kills one eigensystem and keeps another.

**Lemma (One factor).** Let $T \in \mathcal{H}$, $x \in \mathcal{X}$, $a, b \in \mathbb{C}$, and $y \in \mathcal{A}_M(V)_d$. Then

$$\big(a(T T_x - bT)\big)_V\, y = a\,(d(x) - b)\; T_V\, y.$$

Lean: `New.Data.smul_mul_heckeOperator_sub_smul_apply` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* $T_V T_{x,V}\,y = d(x)\,T_V\,y$, since $T_{x,V}\,y = d(x)\,y$. $\square$

**Theorem (Projector onto one eigensystem).** Let $q$ be an eigensystem and $F$ a finite set of eigensystems. There is $T \in \mathcal{H}$ such that, for every hermitian space $V$ of rank $r$ and every $d \in F \cup \{q\}$,

$$T_V\, y = \begin{cases} y & \text{if } d = q, \\ 0 & \text{if } d \neq q, \end{cases} \qquad \text{for } y \in \mathcal{A}_M(V)_d.$$

Lean: `New.Data.exists_hecke_proj_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* Induction on $F$. For $F = \emptyset$ take $T = 1$. Suppose $T$ works for $F$, and let $e \notin F$. If $e = q$ the same $T$ works for $F \cup \{e\}$. Otherwise choose $x$ with $q(x) \neq e(x)$ and put

$$T' = \big(q(x) - e(x)\big)^{-1}\big(T T_x - e(x)\, T\big) \in \mathcal{H}.$$

Let $y \in \mathcal{A}_M(V)_d$ with $d \in F \cup \{e, q\}$. By the lemma, $T'_V y = \frac{d(x) - e(x)}{q(x) - e(x)}\, T_V y$. If $d = e$ the factor is $0$. If $d = q$ the factor is $1$ and $T_V y = y$. If $d \in F$ and $d \neq q$, then $T_V y = 0$. In each case $T'_V y$ has the required value. $\square$

The element $T$ does not depend on $V$, because $T_x$ and the scalars do not. The theorem gives no control of $T$ on eigenparts outside $F \cup \{q\}$. In the use below, $F$ contains every eigensystem that occurs in either of the two spaces, so all other parts are $0$.

**Remark (Formalization).** The induction is over the Lean type `Finset`, with decidable equality of eigensystems supplied by classical logic. The choice of $x$ with $q(x) \neq e(x)$ is by `Function.ne_iff`. No property of $x$ beyond $q(x) \neq e(x)$ is used. If $x$ is a pair where $T_x = 0$, the factor is still correct: then the $e$-part and the $q$-part can be nonzero only if $e(x) = q(x) = 0$, which is excluded, so one of them is $0$.

### An example

Let $\mathcal{A}_M(V) = \mathbb{C}y_1 \oplus \mathbb{C}y_2 \oplus \mathbb{C}y_3$ with $y_k$ in the part of $d_k$, and suppose $d_1, d_2, d_3$ are distinct and differ at $x_{12}$, $x_{13}$: $d_1(x_{12}) \neq d_2(x_{12})$ and $d_1(x_{13}) \neq d_3(x_{13})$. With $q = d_1$ and $F = \{d_2, d_3\}$ the proof builds, in two steps,

$$T = \frac{T_{x_{13}} - d_3(x_{13})}{d_1(x_{13}) - d_3(x_{13})}\cdot\frac{T_{x_{12}} - d_2(x_{12})}{d_1(x_{12}) - d_2(x_{12})}.$$

On $y_1$ both factors are $1$. On $y_2$ the second factor is $0$. On $y_3$ the first factor is $0$. The trace of $T$ on any subspace that is a sum of eigenparts is the dimension of its $d_1$-part. This is the use in the next section, where the subspace is $\mathcal{G}(V)$.
