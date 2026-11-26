---
title: Eigensystems and main summands
lean:
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial
  - New.Selmer.isRepOfType_one
  - New.Selmer.exists_isMainSummand_mainPair
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Eigensystems and main summands

The twisting theorem makes the Selmer groups of finitely many representations short at once. So the proof first needs a finite list of representations that does not depend on the twist. This section gives the list. It has two parts. The first part has one main summand of rank $r$ for each lift index $j$ and each eigensystem that occurs in the good forms on $W_m$. The second part has one main summand of rank one for each main pair. The section also proves that the space of lifts is spanned by forms that lift the eigensystems of the first part. All three results are in the top file.

### The space of lifts is spanned by lifts of eigensystems

Fix a twist $\vartheta$ and $1 \leq j \leq m$. Let $O = D.\mathrm{descentPair}(\vartheta, j)$ and let $Z = Z_{\vartheta, j}$ be the range of `D.goodLift ϑ j`, the space of lifts. Call a form $y \in Z$ *split* if it has two properties.

1. There is a tuple $c$ of labels, one polynomial over the residue field at each chosen place of $O$, such that $y$ lies in the range of $\mathrm{typeProjection}(O, c)$, the tuple $c$ is a lift setting for $O$ and $\vartheta$, and the range of $\mathrm{typeProjection}(O, c)$ lies in the image of the idempotent $e_0$ = `D.e₀`.
2. There is a system $q : \mathrm{FinPlace}(E) \times \mathbb{N} \to \mathbb{C}$ with $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0$, such that $y$ has the Hecke polynomials of the lift of $(w, i) \mapsto q(w, i)$ for $O$.

**Theorem (Splitting, pairs of rank $r$).** The space $Z$ lies in the span of its split forms.

Lean: `New.Selmer.range_goodLift_le_span_hasLiftHeckePolynomial` (New/Congruences/FitTwistsExist.lean).

*Proof.* Let $N$ be the span of the split forms. Apply the lemma on the range of the good lift (Section 2) to $N$. It is enough to show this. Let $y$ be a good Hecke eigenform on $W_j$, with the system $q$, and let $c$ be a good tuple family such that $\Theta_{j,\vartheta}\,y$ lies in the range of $e_c$. Then $\Theta_{j,\vartheta}\,y \in N$.

If $y = 0$, then $\Theta_{j,\vartheta}\,y = 0 \in N$. Let $y \neq 0$. Let $j_{\max} = m$, which is a lift index since $1 \leq m$ (`nat_le_of_hasLogBound`). Suppose that $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q = 0$. By equal multiplicities in the vanishing form, applied to $V = W_j$ and $V' = W_m$, also $\mathcal{G}(W_j) \cap \mathcal{A}(W_j)_q = 0$. But $y$ lies in this space and $y \neq 0$. This is a contradiction. So $q$ occurs in the good forms on $W_m$.

The form $y$ is good and lies in the eigenpart of $q$. So $\Theta_{j,\vartheta}\,y$ = `D.singleLift ϑ j y` is the image of $y$ under the good lift, and it lies in $Z$. By the theorem on the Hecke polynomials of the single lift, it has the Hecke polynomials of the lift of $(w, i) \mapsto q(w, i)$. By the theorem on the lift settings of the lifts, $c$ is a lift setting for $O$ and $\vartheta$. By the lemma on the pieces of the good idempotent, the range of $e_c$ lies in that of $e_0$. So $\Theta_{j,\vartheta}\,y$ is split, and it lies in $N$. $\square$

The proof uses $W_m$ and not $W_j$ in property 2 for one reason. The set of systems that occur on $W_m$ does not depend on $j$ or $\vartheta$. So one finite list of main summands serves for all $j$ and all twists.

**Remark (Formalization).** The set
$$\mathcal{S} = \{q \mid \mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0\}$$
is finite by the lemma on finitely many eigensystems (Section 2). The theorem above does not state this. Section 5 proves it as the instance `Finite systems`, and the twisting theorem needs it.

### The trivial representation of rank one

The main pairs need representations of rank one. The source takes the trivial representation $1$ of the Galois group of $E$, with the one-point index type `Unit`. This lemma checks that it has the type of the labels $X - 1$.

**Lemma (The trivial representation has the type of $X - 1$).** Let $O$ be a descent pair with the source index type `Unit` and a finite index type $n$. Then the trivial representation $1$ of rank one is of type $(O, c)$ with $c_i = X - 1$ at every chosen place, with twist $1 - \#\mathrm{Unit} = 0$, the jumps $\{0\}$ at every embedding $E \to \mathbb{C}$, and the empty level.

Lean: `New.Selmer.isRepOfType_one` (New/Congruences/FitTwistsExist.lean).

*Proof.* Fix a place $A$ of the closure. The trivial representation is the scalar representation of the character $\mu = 1$. The image of the inertia group under $\mu$ is $\{1\}$, a finite set, and $\mu$ is continuous. The lemma on the local conditions of a character (Section 2) gives three facts at $A$: the representation is of finite type at $A$, its only jump is $0$, and $X - \mu(s) = X - 1$ kills every $s$.

A representation of a type is a conjugate self-dual representation of a level with one more clause. The clauses are these.

1. Continuity. The trivial representation is constant, so it is continuous.
2. Nondegeneracy of the trace form. On matrices of size $1 \times 1$ the trace is the identity, so the trace form is nondegenerate.
3. Conjugate self-duality with twist $0$. Both sides of the trace identity are $1$.
4. The local conditions at each place $v$ off the empty level. Finite type and the jumps $\{0\}$ are the first two facts above. Good reduction (`IsGoodAt`) asks finite type and that $X - 1$ kills every $s$. These are the first and the third fact.
5. The labels. At each chosen place the clause asks that each root of the label kills the inertia elements. The roots of $X - 1$ over $\overline{\mathbb{Q}}_\ell$ are the multiset $\{1\}$ (`aroots_X_sub_C`). The third fact says that $X - 1$ kills $s$.

So all the clauses hold. $\square$

### The main summands of the main pairs

A main pair for $j$ is a critical pair $p = (\nu, z)$ with $m < z \leq r$, tame part $\omega^j$ for the fixed family $\omega$ = `D.chiMLocal`, and $w_j + r - t \leq c_v \leq w_j$ at every infinite place, where $-c$ is the weight of $\nu$ and $w_j$ = `D.liftWeight j`. The datum `p.lValueData _ ϑ` is the theta lift of $\nu\vartheta$ from $U(1)$ to the definite space of rank $2z$. Write $O_p(\vartheta)$ for its descent pair. Its source index type is `Unit` and its target index type has $2z$ elements, so its rank difference is $2z - 1$.

**Lemma (Main summands of the main pairs).** Let $p = (\nu, z)$ be a main pair for some $j$. Then there is a representation $T$ of rank one that is a main summand for the untwisted pair $O_p(1)$ and the constant system $1$.

Lean: `New.Selmer.exists_isMainSummand_mainPair` (New/Congruences/FitTwistsExist.lean).

The argument of the lemma is an element of the subtype of pairs $(p, j)$ with $p$ a main pair for $j$. This is the index type $B$ of the main pairs in Section 5. It is finite, since there are finitely many critical pairs (`New.Data.finite_criticalPair`, [chosen places, residue characters and sizes](/chapter/field-at-primes/#chosen-places-residue-characters-and-sizes)) and finitely many lift indices.

*Proof.* Apply the theorem on main summands from a representation of a type (Section 2), with these arguments.

1. The lift setting is $O_p(1)$ with the labels $X - 1$. It is a lift setting for the trivial twist by the theorem on the lift settings of the main pairs, at $\vartheta = 1$.
2. The values are $b = 1$, the constant system.
3. The jumps are $J_\sigma = \{0\}$ and the representation is $R = 1$.
4. The type is given by the lemma on the trivial representation.
5. The trace condition holds, since $\mathrm{tr}\,1 = 1$ and $\iota_\ell(b(w, 1)) = \iota_\ell(1) = 1$ for every $w$. The limit of a constant sequence is the constant.

It remains to check the weights. Here $\#r = 1$ and $O.\mathrm{rankDiff} = 2z - 1$, with $z \geq 2$ (`hasLiftRank`). The shift is
$$\frac{\#r - O.\mathrm{rankDiff}}{2} = \frac{1 - (2z - 1)}{2} = 1 - z,$$
with exact division, since $1 - (2z - 1) = 2 - 2z$ is even. The weight of $O_p(1)$ at $v$ unfolds to an expression in $c_v - z + \lfloor 2z/2 \rfloor$, and this equals $c_v$, since $\lfloor 2z/2 \rfloor = z$. So the jump $0$ at $\sigma$ is lowered to
$$0 - \big(1 - z - \epsilon_\sigma \cdot (-c_v)\big) = z - 1 - \epsilon_\sigma c_v .$$
By the theorem on the weights of the main pairs (Section 2), these jumps are main summand weights for $(1, 2z - 1)$. This is the last hypothesis. $\square$

**Remark (Formalization).** The source does the computation of the weights with `simpa only` and four rewrite lemmas: `h_weight` for the weight, `h_shift` for the division, `h_jump` for the jump, and the cardinality $2z$ of `RankOneIndex z`. The natural number $2z - 1$ is cast to an integer. The subtraction is truncated in $\mathbb{N}$, but $2z \geq 4$, so the cast is exact.

### What the list is

The list of representations for one prime $\ell$ and one $\iota$ has two parts.

1. For each pair $a = (j, q)$ with $1 \leq j \leq m$ and $q \in \mathcal{S}$, a main summand $R_a$ of rank $r$ for $D.\mathrm{descentPair}(1, j)$ and $q$. It comes from the theorem on the main summands of the lifts.
2. For each $b = (p, j)$ with $p$ a main pair for $j$, a main summand $R'_b$ of rank one for $O_p(1)$ and $1$. It comes from the lemma above.

Both index types are finite. Both families are chosen by `choose`, so the representations are not definite. They depend on $\ell$ and $\iota$, since main summands are $\ell$-adic. The first field of `IsMainSummand` says that each one is like a main summand for some $t$ and $J$. This is the hypothesis of the twisting theorem.
