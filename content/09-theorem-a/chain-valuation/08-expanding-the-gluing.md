---
title: Expanding the gluing
lean:
  - New/UpperBound/Divisibility/ChainDatumExpansion.lean
decls:
  - New.Data.TameChar.normQ_notMem_of_N_mem
  - New.Data.TameChar.M_mul_normQ_notMem_of_N_mem
  - New.Data.vacuumProjFinPart_translateDatum
  - New.Data.eq_zero_of_poleColumn_mem_integralBox
  - New.Data.vacuumProjFinPart_gluedDoubleLiftDatum
  - New.Data.heisenbergFinPart_translateDatum_of_disjoint
  - New.Data.gluedDoubleLiftDatum_translateDatum
  - New.Data.GluingClasses
  - New.Data.gluingTuple
  - New.Data.gluingTuple_two_mul
  - New.Data.gluingTuple_two_mul_add_one
  - New.Data.gluingTuple_mem_supportedTranslations
  - New.Data.card_gluingClasses_le
  - New.Data.ungluedVacuum
  - New.Data.plainTensor_eq_sum_ungluedVacuum
  - New.Data.gluedVacuum_eq_sum_translates
  - New.Data.add_mem_admissibleTranslations_mul_N
  - New.Data.isAdmissibleCombination_sum_ungluedVacuum
  - New.Data.isJointlyInvariant_of_plainTensor
  - New.Data.IsChainDatum.gluedTensor_eq_sum_translates
  - New.Data.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq
  - New.Data.IsChainDatum.isInvariant_plainTensor
  - New.Data.IsChainDatum.isWeakChainDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Expanding the gluing

The composite lift of a chain datum $\Psi$ uses the glued tensor $\mathrm{Glue}\,\varphi^\flat$ as data for $\varrho + 1$ double lifts. The bounds of Section 6 are for chains of single lifts with translated data. This section connects the two in two ways.

1. *Expanding.* The gluing is a finite sum of translates by poles $-y/N$. Expanding it writes $\mathrm{Glue}\,\varphi^\flat$ as a plain tensor $\varphi^\flat_{\Psi'}$ of a weak chain datum $\Psi'$. So the composite lift of $\Psi$ is the restricted chain of $\Psi'$. This form serves for sums of norms and for the primes $p \ne N$.
2. *Projecting.* The projection on vacua above $N$ kills every term of the gluing except $y = 0$. So it maps $\mathrm{Glue}\,\varphi^\flat$ to $\varphi^\flat$, and $\varphi^\flat$ is invariant. So $\Psi$ itself is a weak chain datum. This form serves for $p = N$.

### Notation

The data have $m = 2\varrho + 2$ lifts. The index set of $X_j$ is $\mathrm{Init}_j \sqcup \{\ast\}$, with the last index $\ast$. For a tuple $x$, $v_{x,j}$ is the translated datum. For a vector $y$ on $X_{2i+1}$ of classes modulo $N$ at each $w \in \Pi_N$, $\mathrm{pc}(y)$ is the matrix whose last column is $-y/N$ at the places $w \in \Pi_N$, with all other entries $0$. The matrix $\mathrm{pr}(y)$ has last row $-\bar y/N$ at the conjugate places, with all other entries $0$. The glued datum of the double lift $i$ is

$$\mathrm{Glue}_i(v) = \sum_y \varrho_f(\mathrm{pc}(y))\,v_{2i} \otimes \varrho_f(\mathrm{pr}(y))\,v_{2i+1},$$

the sum over all such $y$ ([Definition](/decl/New.Data.gluedDoubleLiftDatum/)). The plain and glued tensors of $\Psi$ are

$$\varphi^\flat = \sum_x \Psi(x) \bigotimes_{i \le \varrho} v_{x,2i}\otimes v_{x,2i+1}, \qquad \mathrm{Glue}\,\varphi^\flat = \sum_x \Psi(x) \bigotimes_{i\le\varrho} \mathrm{Glue}_i(v_x).$$

A tensor $w$ of double-lift data is *invariant* if every tuple $b_j \in K_j$ with $b_m = 1$ fixes it, acting on factor $i$ by $\omega(b_{2i}, b_{2i+1}) \otimes \omega(b_{2i+1}, b_{2i+2})$. A chain datum asks that $\mathrm{Glue}\,\varphi^\flat$ is invariant ([Definition](/decl/New.Data.IsChainDatum/)).

### The places above N

**Lemma.** Let $\vartheta$ be a tame character with $q = \mathrm{N}Q$, and let $w$ be a place with $N \in w$. Then $q \notin w$ and $Mq \notin w$.

Lean: `New.Data.TameChar.normQ_notMem_of_N_mem`, `New.Data.TameChar.M_mul_normQ_notMem_of_N_mem` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* The number $q$ is prime to $N$ by the definition of a tame character, so $q \notin w$. Neither $w$ nor $\bar w$ is chosen, since a chosen place has norm a prime $p_i < N$ (`New.Data.not_isChosen_of_N_mem`, in [short columns and the gain](/chapter/short-columns-gain/)). As $M = \pi_M\bar\pi_M$, $M \notin w$. Since $w$ is prime, $Mq \notin w$. $\square$

### Projecting away the gluing

Let $P_N$ be the projection on vacua at the places of $\Pi_N$ and their conjugates, on the finite part of the Weil representation (`New.Space.vacuumProjFinPart`). It is the operator $P^S$ of Section 6 with $S = \Pi_N$.

**Lemma.** Let $t$ be admissible for $q = \mathrm{N}Q$. Then $P_N v_{t,j} = v_{t,j}$ for all $j$.

Lean: `New.Data.vacuumProjFinPart_translateDatum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* By the lemma on projections of Section 6, it suffices that $t_j \in \mathrm{Int}(1, \Pi_N \cup \bar\Pi_N)$. Every place $w$ of $\Pi_N \cup \bar\Pi_N$ has $N \in w$. So $q \notin w$, and $\bar w$ is not chosen, by the proof of the last lemma. Apply the lemma on admissible tuples of Section 6 with $\delta = 1$. $\square$

**Lemma.** Let $y$ be a vector of classes modulo $N$ such that $\mathrm{pc}(y)$ is integral at every place of $\Pi_N \cup \bar\Pi_N$. Then $y = 0$.

Lean: `New.Data.eq_zero_of_poleColumn_mem_integralBox` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Let $k$ be an index and $w \in \Pi_N$. The last entry of row $k$ of $\mathrm{pc}(y)$ at $w$ is $-\hat y/N$, where $\hat y$ is the fixed lift of the class $y_k(w)$. By hypothesis this entry is integral at $w$. Since $N \in w$ and $w$ has degree one over $N$, this forces $\hat y \in w$, so $y_k(w) = 0$. The level $\Pi_N$ is split, so a vector of classes is $0$ if and only if it is $0$ at each $w \in \Pi_N$. So $y_k = 0$. $\square$

**Lemma.** Let $t$ be admissible for $q = \mathrm{N}Q$, and $i \in \mathbb N$. Then $(P_N \otimes P_N)\,\mathrm{Glue}_i(v_t) = v_{t,2i} \otimes v_{t,2i+1}$.

Lean: `New.Data.vacuumProjFinPart_gluedDoubleLiftDatum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* By the lemma before last, $P_N$ fixes $v_{t,j}$. By the projection rule of Section 6, $P_N\varrho_f(z)v_{t,j}$ is $\varrho_f(z)v_{t,j}$ if $z$ is integral at $\Pi_N \cup \bar\Pi_N$, and $0$ otherwise. In the term $y$ of the gluing, the first factor is $\varrho_f(\mathrm{pc}(y))v_{t,2i}$. By the last lemma it is killed unless $y = 0$. For $y = 0$ both pole matrices are $0$, and the term is $v_{t,2i}\otimes v_{t,2i+1}$. $\square$

### Expanding the gluing

**Lemma.** Let $t$ vanish at the places above $N$. Let $z$ vanish at the places outside $\Pi_N \cup \bar\Pi_N$. Then $\varrho_f(z)\,v_{t,j} = \varrho_f(z + t_j)\,v_{0,j}$.

Lean: `New.Data.heisenbergFinPart_translateDatum_of_disjoint` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* By definition $v_{t,j} = \varrho_f(t_j)v_{0,j}$. By the composition rule of Section 6, $\varrho_f(z)\varrho_f(t_j) = \chi(\overline{t_j}\cdot z)\,\varrho_f(z + t_j)$. Each product $\overline{t_j(k)}\,z(k)$ is $0$: at a place above $N$, $\bar w$ is also above $N$ and $t_j$ vanishes there; at a place not above $N$, neither $w$ nor $\bar w$ lies in $\Pi_N$ (the places of $\Pi_N \cup \bar\Pi_N$ are exactly those above $N$), and $z$ vanishes. So the phase is $\chi(0) = 1$. $\square$

**Lemma.** Let $t$ vanish at the places above $N$. Then

$$\mathrm{Glue}_i(v_t) = \sum_y \varrho_f(\mathrm{pc}(y) + t_{2i})\,v_{0,2i} \otimes \varrho_f(\mathrm{pr}(y) + t_{2i+1})\,v_{0,2i+1}.$$

Lean: `New.Data.gluedDoubleLiftDatum_translateDatum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* The matrix $\mathrm{pc}(y)$ vanishes outside $\Pi_N$, and $\mathrm{pr}(y)$ vanishes outside $\bar\Pi_N$. Apply the last lemma to each factor of each term. $\square$

**Definition (Gluing classes).** A gluing class is a family $y = (y_i)_{i \le \varrho}$, where $y_i$ is a vector on $X_{2i+1}$ with values in $\mathbb Z/N$ at each $w \in \Pi_N$.

Lean: `New.Data.GluingClasses` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

**Definition (Gluing tuple).** The gluing tuple of $y$ is the tuple of translations $z(y)$ with $z(y)_{2i} = \mathrm{pc}(y_i)$, $z(y)_{2i+1} = \mathrm{pr}(y_i)$ for $i \le \varrho$, and $z(y)_j = 0$ for $j \ge m$.

Lean: `New.Data.gluingTuple` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

**Lemma.** $z(y)_{2i} = \mathrm{pc}(y_i)$ and $z(y)_{2i+1} = \mathrm{pr}(y_i)$ for $i \le \varrho$.

Lean: `New.Data.gluingTuple_two_mul`, `New.Data.gluingTuple_two_mul_add_one` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* The source defines $z(y)$ as a sum over $i'$ of two tuples supported at the positions $2i'$ and $2i'+1$. At position $2i$, only $i' = i$ contributes, since $2i \ne 2i'$ for $i' \ne i$ and $2i \ne 2i' + 1$ always. Position $2i+1$ is the same. $\square$

**Lemma.** Every gluing tuple is supported on $N$: it vanishes at the places $w$ with $N \notin w$.

Lean: `New.Data.gluingTuple_mem_supportedTranslations` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* If $N \notin w$, then $w \notin \Pi_N$ and $\bar w \notin \Pi_N$. So $\mathrm{pc}$ and $\mathrm{pr}$ vanish at $w$, and so does every summand of $z(y)$. $\square$

**Lemma.** There are at most $N^{f m n_m/2}$ gluing classes.

Lean: `New.Data.card_gluingClasses_le` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* For each $i$, the number of vectors $y_i$ is $N^{n_{2i+1}\cdot\#\Pi_N} = N^{f n_{2i+1}}$, since $\#\Pi_N = f$. As $n_{2i+1} \le n_m$, this is at most $N^{f n_m}$. There are $\varrho + 1$ values of $i$, so the number of classes is at most $N^{f n_m(\varrho+1)}$. Since $m = 2(\varrho + 1)$, the exponent is $f m n_m/2$. $\square$

**Definition (Unglued vacuum).** For a tuple $t$, the unglued vacuum is $u(t) = \bigotimes_{i \le \varrho} v_{t,2i}\otimes v_{t,2i+1}$.

Lean: `New.Data.ungluedVacuum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

**Lemma.** $\varphi^\flat = \sum_x \Psi(x)\,u(x)$.

Lean: `New.Data.plainTensor_eq_sum_ungluedVacuum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* This is the definition of $\varphi^\flat$. $\square$

**Lemma.** Let $t$ vanish at the places above $N$. Then the glued tensor of $t$ alone is $\bigotimes_i \mathrm{Glue}_i(v_t) = \sum_y u(t + z(y))$, the sum over all gluing classes.

Lean: `New.Data.gluedVacuum_eq_sum_translates` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Expand each factor by the lemma on $\mathrm{Glue}_i(v_t)$. The tensor product of $\varrho + 1$ sums over $y_i$ is the sum over the families $y$ of the tensor products. In the term $y$, factor $i$ is $\varrho_f(\mathrm{pc}(y_i) + t_{2i})v_{0,2i} \otimes \varrho_f(\mathrm{pr}(y_i) + t_{2i+1})v_{0,2i+1}$. By the lemma on gluing tuples, this is $v_{t+z(y), 2i}\otimes v_{t+z(y),2i+1}$. $\square$

**Lemma.** If $t$ is admissible for $q$ and $z$ is supported on $N$, then $t + z$ is admissible for $qN$.

Lean: `New.Data.add_mem_admissibleTranslations_mul_N` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Let $qN \notin w$. Then $q \notin w$ and $N \notin w$. So $z$ vanishes at $w$, and $\bar\pi_M(t + z)_j = \bar\pi_M t_j$ is integral at $w$. $\square$

### Admissible combinations

For a family of vectors $(v(x))_{x}$, a set $A$, numbers $n, d$, a proposition $P$ and $B \in \mathbb R$, a vector $z$ is an *admissible combination* if $z = \sum_x r(x)v(x)$ with $r$ admissible coefficients: supported in $A$, with $d\,r(x)$ integral away from $n$, and, if $P$ holds, $\sum_x |\sigma r(x)| \le B$ for every automorphism $\sigma$ of $\mathbb C$ ([Definition](/decl/New.Seesaw.IsAdmissibleCombination/)). Substitution is the rule of [the first seesaw identity](/chapter/seesaw-identity-1/): if $z$ is an admissible combination of the $v(x)$ with $(A, n, d, P, B)$, and each $v(x)$, $x \in A$, is one of the $v'(y)$ with $(A', n, d', P, B')$, then $z$ is one of the $v'(y)$ with $(A', n, e, P, C)$ for every $e$ divisible by $dd'$ and every $C$ with $B|B'| \le C$ when $P$ holds ([Lemma](/decl/New.Seesaw.IsAdmissibleCombination.bind/)).

**Lemma.** Let $t$ be admissible for $q$, and let $P$ be a proposition. Then $\sum_y u(t + z(y))$ is an admissible combination of the unglued vacua $u(x)$, with $A$ the tuples admissible for $qN$, $n = q$, $d = 1$, the proposition $P$, and $B = N^{f m n_m}$.

Lean: `New.Data.isAdmissibleCombination_sum_ungluedVacuum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* As a combination of the vectors $u(t + z(y))$ indexed by $y$, the sum has all coefficients $1$. These are integral, and the sum of their absolute values is the number of classes, at most $N^{fmn_m/2} \le N^{fmn_m}$. Each $u(t+z(y))$ is the single vector $u(x)$ with $x = t + z(y)$, and $x$ is admissible for $qN$ by the last two lemmas. This is an admissible combination with $B' = 1$ and $d' = 1$. Substitution gives the claim. $\square$

### The two conclusions

**Theorem (Expanding the gluing).** Let $\Psi$ be a chain datum for the twist $\vartheta$. Then:

1. $\mathrm{Glue}\,\varphi^\flat = \sum_x \Psi(x) \sum_y u(x + z(y))$, the inner sum over all gluing classes;
2. there are at most $N^{fmn_m/2}$ gluing classes;
3. every gluing tuple is supported on $N$.

Lean: `New.Data.IsChainDatum.gluedTensor_eq_sum_translates` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Parts 2 and 3 are the lemmas above. For part 1, let $x \in \mathrm{supp}\,\Psi$. A chain datum has $x$ supported on $Mq$. If $N \in w$, then $Mq \notin w$ by the first lemma, so $x$ vanishes at $w$. So $x$ vanishes at the places above $N$, and the lemma on the glued tensor of $t$ applies. $\square$

**Lemma.** Let $\varphi^\flat_\Psi$ be invariant. Then the family $(\Psi(x)\cdot\mathrm{id}, (v_{x,j})_j)_{x \in \mathrm{supp}\,\Psi}$ is jointly invariant at stage $m$ for the lift kernels, in the sense of Section 5.

Lean: `New.Data.isJointlyInvariant_of_plainTensor` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Let $T$ be the linear map that regroups the $\varrho + 1$ pairs of factors into $2(\varrho + 1) = m$ single factors, so $T(\bigotimes_i f_{2i}\otimes f_{2i+1}) = f_{m-1}\otimes\dots\otimes f_0$. Let $b$ be a tuple with $b_j \in K_j$ and $b_j = 1$ for $j \ge m$, and let $\beta$ be a linear map to $V_m$. The action of $b$ on pairs, followed by $T$, is $T$ followed by the action of $b$ on single factors. Apply $\beta\circ T$ to the invariance identity of $\varphi^\flat$. $\square$

**Theorem.** Let $\Psi$ be a chain datum for $\vartheta$. Then there is a weak chain datum $\Psi'$ for $\vartheta$ such that, for every source form $\varphi$,

$$B_{\vartheta, \Psi}\,\varphi = \mathrm{res}\big(\mathrm{CC}(\vartheta, \Psi', v, m)\,\varphi\big).$$

Lean: `New.Data.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* *Step 1: an outer combination.* By part 1 of the theorem above, $\mathrm{Glue}\,\varphi^\flat$ is an admissible combination of the vectors $\sum_y u(x + z(y))$, with coefficients $\Psi$, $A$ the tuples admissible for $q$ and supported on $Mq$, $n = q$, $d = 1$, the proposition $Q = \emptyset$ and $B = M^{3fmn_m^2}$. This holds since $\Psi$ has admissible coefficients for these parameters.

*Step 2: substitution.* By the last lemma of the previous part, each inner sum is an admissible combination of unglued vacua with $B' = N^{fmn_m}$. By the table of sizes, $M^{3fmn_m^2}N^{fmn_m} \le \exp(x^{60})$. Substitution gives $\Psi'$, admissible coefficients for the tuples admissible for $qN$, with $n = q$, $d = 1$, $Q = \emptyset$ and $B = \exp(x^{60})$, and $\mathrm{Glue}\,\varphi^\flat_\Psi = \sum_x \Psi'(x)u(x) = \varphi^\flat_{\Psi'}$.

*Step 3: invariance.* Since $\varphi^\flat_{\Psi'} = \mathrm{Glue}\,\varphi^\flat_\Psi$ is invariant, the last lemma shows that $\Psi'$ is jointly invariant. So $\Psi'$ is a weak chain datum.

*Step 4: the lifts.* The composite lift applies $\varrho + 1$ double lifts with the data $\varphi^\flat_{\Psi'}$. A double lift with a pure tensor datum $f_{2i}\otimes f_{2i+1}$ is the composite of two single lifts. So the chain of double lifts with $\varphi^\flat_{\Psi'}$ is $\mathrm{CC}(\vartheta, \Psi', v, 2(\varrho+1))$. The transport along $m = 2\varrho + 2$ in the definition of the composite lift is the identity on this value. $\square$

**Lemma.** Let $\Psi$ be a chain datum for $\vartheta$. Then $\varphi^\flat_\Psi$ is invariant.

Lean: `New.Data.IsChainDatum.isInvariant_plainTensor` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* Let $\mathrm{pr}$ be $P_N \otimes P_N$ on each pair of factors. By the lemma on projecting away the gluing, applied to each $x$ in the support (which is admissible for $q$), $\mathrm{pr}(\mathrm{Glue}\,\varphi^\flat) = \varphi^\flat$. The levels $K_j$ lie in the standard maximal compact subgroup. For such $a, b$, the operator $\omega(a, b)$ of the Weil representation commutes with $P_N$ (`New.Space.omega_projOn`). So the action of a tuple $b$ commutes with $\mathrm{pr}$, and

$$b\cdot\varphi^\flat = b\cdot\mathrm{pr}(\mathrm{Glue}\,\varphi^\flat) = \mathrm{pr}(b\cdot\mathrm{Glue}\,\varphi^\flat) = \mathrm{pr}(\mathrm{Glue}\,\varphi^\flat) = \varphi^\flat. \qquad\square$$

**Theorem.** Every chain datum for $\vartheta$ is a weak chain datum for $\vartheta$.

Lean: `New.Data.IsChainDatum.isWeakChainDatum` (New/UpperBound/Divisibility/ChainDatumExpansion.lean).

*Proof.* *Support.* A tuple admissible for $q$ is admissible for $qN$: if $qN \notin w$, then $q \notin w$. *Integrality.* The condition is the same. *Size.* By the table of sizes, $\log M^{3fmn_m^2} \le x^{60}$, so the bound $M^{3fmn_m^2}$ implies the bound $\exp(x^{60})$. *Invariance.* By the last lemma and the lemma on joint invariance. $\square$

**Remark.** The two theorems give two weak chain data for one chain datum $\Psi$: the expansion $\Psi'$, whose restricted chain is the composite lift, and $\Psi$ itself, whose restricted chain is a different form. At $p \ne N$ the bounds of Section 6 apply to $\Psi'$. At $p = N$ the poles $-y/N$ of $\Psi'$ are not integral above $N$, and [divisibility prime by prime](/chapter/divisibility/) works with $\Psi$ and the projection.

**Remark (Formalization).** The gluing classes are functions to $\mathbb Z/N$, and the pole matrices use a fixed lift of each class (`New.residueOverN`). The weak chain datum $\Psi'$ is given by an existence statement; its coefficients come from the substitution rule, and Lean does not name them. The size bound of a weak chain datum is asked only when $Q = \emptyset$.
