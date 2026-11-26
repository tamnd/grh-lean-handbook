---
title: The constants
lean:
  - New/Congruences/FirstOrder/TraceRelations.lean
decls:
  - New.Selmer.oddClassBound
  - New.Selmer.oddClassBound_ne_zero
  - New.Selmer.oddClassBound_le
  - New.Selmer.eventually_length_shaOdd_le
  - New.Selmer.localDefectBound
  - New.Selmer.denominatorError
  - New.Selmer.denominatorError_eq_natCast
  - New.Selmer.denominatorError_ne_top
  - New.Selmer.clearingBound
  - New.Selmer.add_denominatorError_le_mul_clearingBound
  - New.Selmer.mul_padicValNat_add_le_add_denominatorError
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The constants

Ribet's method loses a fixed amount of $\ell$-adic valuation at each step. This section names the amounts. Each constant depends only on the data $D$ and the prime $\ell$. None depends on the coefficient ring, the descent pair or the level of the auxiliary places. This independence is what makes the later sum over all primes $\ell$ possible, in [the denominator budget](/chapter/regular-families-plan/#the-denominator-budget).

Throughout, $N$ is `D.chosenGroupOrder`, $v = v_\ell(N)$ is its $\ell$-adic valuation as a natural number, $f$ is the number `D.f` of infinite places of $E$, $t = 5r$ and $h_{\mathrm{gap}} = r^8$ ([the data](/chapter/notation/#the-scales-the-ranks-the-weights-and-the-primes)). Recall from [the main summands](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) the twist allowance
$$e'_\ell = \mathrm{twistError}(\ell, D) = (4f + 3)\, r\, v + 2^{-\ell}.$$

### The odd class bound

The Selmer groups of the characters $O(-e)$ for $0 \leq e < t$ enter the cost of each character in Ribet's element. [The odd part and the uniform bound](/chapter/odd-classes/) proves one bound for all primes at once: [Theorem](/decl/New.exists_length_shaOdd_le/) gives a nonzero integer $X \leq 2^{4(N_E + t + 3)^{27}} h_E$ whose valuation bounds the length of the odd classes, where $N_E$ is the conductor of a cyclotomic field that contains $E$ and $h_E$ is the class number.

**Definition (The odd class bound).** The number $\mathrm{odd} = \mathrm{oddClassBound}(D)$ is the integer $X$ of [Theorem](/decl/New.exists_length_shaOdd_le/) for the conductor `D.cyclotomicConductor`, the number $t$ and the field $E$.

Lean: `New.Selmer.oddClassBound` (New/Congruences/FirstOrder/TraceRelations.lean).

**Lemma (Properties of the odd class bound).**

1. $\mathrm{oddClassBound}(D) \neq 0$.
2. $\mathrm{oddClassBound}(D) \leq 2^{4(N_E + t + 3)^{27}}\, h_E$, with $N_E$ = `D.cyclotomicConductor` and $h_E$ the class number of $E$.
3. For every large coefficient ring $O$, for all $e < t$ and all $\nu$, the length of the odd classes $\mathrm{shaOdd}(\ell, E, O, e, \nu)$ in $(O/\ell^\nu)(-e)$ is at most the normalized valuation $\mathrm{addVal}_O(\mathrm{oddClassBound}(D))$.

Lean: `New.Selmer.oddClassBound_ne_zero` (New/Congruences/FirstOrder/TraceRelations.lean), `New.Selmer.oddClassBound_le` (New/Congruences/FirstOrder/TraceRelations.lean), `New.Selmer.eventually_length_shaOdd_le` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Parts 1 and 2 are the first two parts of the specification of the chosen integer. For part 3, the theorem gives the bound for every coefficient ring that contains a primitive root of unity of the needed order. Such rings form an eventual set along `atTop` (`New.CoeffRing.eventually_exists_isPrimitiveRoot`), and the bound passes to the eventual set by monotonicity. $\square$

**Remark (Formalization).** The integer $\mathrm{oddClassBound}(D)$ is chosen by `choose` from an existence statement. The reader must treat it as some integer with the three properties, not as an explicit product. The proof of the existence theorem itself takes choices for each $e$ ([the odd part](/chapter/odd-classes/)). Nothing later uses more than the three properties. The valuation in part 3 is the valuation of $O$, normalized so that a uniformizer has valuation $1$. It is larger than the valuation $v_\ell$ by the ramification index of $O$. The method compares it with lengths over $O$, which carry the same normalization. The constants of this section use $v_\ell(\mathrm{odd}) = $ `padicValNat ℓ (oddClassBound D)`, and part 1 makes this valuation finite and meaningful.

The comment of the definition says that, for $e = 0$, the bound covers the length of the unramified homomorphisms. This is what the existence theorem gives for the trivial character. The method uses only part 3 as stated.

### The local loss and the error term

**Definition (The local loss).** $\mathrm{loc}_\ell = \mathrm{localDefectBound}(D, \ell) = 4 f \cdot \mathrm{defect}_\ell$, where $\mathrm{defect}_\ell = \mathrm{defectBound}(D, \ell)$ is the number of [the constants of the defect bound](/chapter/main-summands/#the-constants-of-the-defect-bound).

Lean: `New.Selmer.localDefectBound` (New/Congruences/FirstOrder/TraceRelations.lean).

The number $\mathrm{defect}_\ell$ is $10^6\, (m/k)\, (b\, v_\ell(M) + \mathrm{crystallineLoss}(h_{\mathrm{gap}}, b, \ell))$ in `NNReal`, with $b$ = `D.natB` and $M$ the principal level. It bounds the defect at one place above $\ell$ per unit of rank. The factor $4f$ is the cost of all places above $\ell$ and of the two blocks of a lattice; [the local defect bound](/chapter/denominator-bound/#local-defects) explains it. The number may be $0$. The crystalline loss is the valuation $v_\ell$ of $(2b)!$ times a power of a product of integers at most $b + 30 h_{\mathrm{gap}}^3$. So $\mathrm{defect}_\ell = 0$ for every $\ell > 2b + 30 h_{\mathrm{gap}}^3$ that does not divide $M$. Then the local loss is free, and the bounds below still hold.

**Definition (The error term).** In $[0, \infty]$,
$$e_\ell = \mathrm{denominatorError}(D, \ell) = t\, v_\ell(\mathrm{odd}) + 8 f t\, v + 2v + \big((4t+1)\, h_{\mathrm{gap}}^{22} + h_{\mathrm{gap}}\big)\, v.$$

Lean: `New.Selmer.denominatorError` (New/Congruences/FirstOrder/TraceRelations.lean).

The four terms have four sources. The term $t\, v_\ell(\mathrm{odd})$ pays for the odd classes of the $t$ characters. The term $8ft\, v$ pays for the tame places above $p_0 p_1$, once for each character. The term $2v$ pays for the idempotent and the automorphisms of the level structure: the operator is multiplied by $N^2$ in [the operator at one system](/chapter/denominator-bound/#the-operator-at-one-base-system). The last term pays for the congruences between the characters $O(-e)$, which are separated by the triangle of primes only modulo $\ell^{h_{\mathrm{gap}} h}$ with $h \leq v$.

**Lemma (The error term is finite).** $e_\ell$ is the cast of the natural number given by the same formula. In particular $e_\ell \neq \infty$.

Lean: `New.Selmer.denominatorError_eq_natCast` (New/Congruences/FirstOrder/TraceRelations.lean), `New.Selmer.denominatorError_ne_top` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Each term is a product of natural number casts, and the cast from $\mathbb{N}$ to $[0, \infty]$ is a semiring map. A cast of a natural number is not $\infty$. $\square$

**Remark (Formalization).** The term $h_{\mathrm{gap}}^{22} = r^{176}$ is large. It enters because the triangle of primes of [first-order deformations](/chapter/first-order-deformations/#the-triangle-of-primes) has up to $h_{\mathrm{gap}}^{22}$ test points, each with separation $h_{\mathrm{gap}} h$. The finding F-094 of the plan asks whether this term fits the budget. [The error terms are negligible](/chapter/regular-families-plan/#the-denominator-budget) answers it in the source: the real values of $e_\ell$ are negligible with exponent $4000$, since $h_{\mathrm{gap}}^{22} v$ summed over $\ell$ with the weights $\log \ell$ is at most $h_{\mathrm{gap}}^{22} \log N$, a power of $x$ times $\log N$. So the term is harmless for the budget, but it is not small.

### The clearing bound

**Definition (The clearing bound).** In `NNReal`,
$$\beta_\ell = \mathrm{clearingBound}(D, \ell) = \mathrm{loc}_\ell + (1 + 2t)\, e'_\ell + e_\ell^{\mathbb{R}} + v,$$
where $e_\ell^{\mathbb{R}}$ is `(denominatorError D ℓ).toNNReal`.

Lean: `New.Selmer.clearingBound` (New/Congruences/FirstOrder/TraceRelations.lean).

**Remark (Formalization).** The map `toNNReal` sends $\infty$ to $0$. This junk value never occurs here, since $e_\ell \neq \infty$ by the lemma above. So $\beta_\ell$ is the sum of the four real numbers in the formula.

The clearing bound is the cost per unit of rank. A descent pair with $\#r$ ranks and $t'$ characters costs $\mathrm{sel} + 2t'\,\mathrm{ram} + \#r\,\mathrm{loc}_\ell + e_\ell$ by the bound for denominators. One more $v$ pays for the factor $N$ of [the determinant bound](/chapter/denominator-bound/#the-bound-for-denominators). The next lemma checks that $\#r\, \beta_\ell$ pays for all of this.

**Lemma (The clearing bound pays for one descent pair).** Let $1 \leq r' \leq r$ and $t' \leq t$. Let $\mathrm{sel}, \mathrm{ram} \in [0, \infty]$ with $\mathrm{sel} \leq e'_\ell$ and $\mathrm{ram} \leq e'_\ell$. Then
$$\mathrm{sel} + 2t'\,\mathrm{ram} + r'\,\mathrm{loc}_\ell + e_\ell + v \leq r'\, \beta_\ell.$$

Lean: `New.Selmer.add_denominatorError_le_mul_clearingBound` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Write $\varepsilon = e'_\ell$. By the hypotheses and $t' \leq t$, the left side is at most
$$\varepsilon + 2t\varepsilon + r'\,\mathrm{loc}_\ell + e_\ell + v = r'\,\mathrm{loc}_\ell + 1 \cdot \big((1 + 2t)\varepsilon + e_\ell + v\big).$$
Since $1 \leq r'$, the factor $1$ can be replaced by $r'$. This gives $r'\big(\mathrm{loc}_\ell + (1+2t)\varepsilon + e_\ell + v\big)$. Since $e_\ell \neq \infty$, the cast of $e_\ell^{\mathbb{R}}$ to $[0, \infty]$ is $e_\ell$, and the last sum is $r' \beta_\ell$. $\square$

The proof spends the factor $r' \geq 1$ on terms that do not grow with the rank. This is crude, but the budget has room for it.

### The cost of the characters

Ribet's element in [Ribet elements](/chapter/ribet-elements/#ribets-element-for-galois-representations) is a product over $t'$ characters. Each character costs its odd classes, the tame places, and a detection cost; a final term is paid once. The next lemma adds these costs and compares them with $e_\ell$. It is pure arithmetic, but it is where the formula for $e_\ell$ comes from.

**Lemma (The cost of the characters).** Let $t' \leq t$ and $h \leq v$, and put $\mathrm{sep} = h_{\mathrm{gap}}\, h$. Let $k$, $n_{\mathrm{test}}$ and $n_{\mathrm{detect}}$ be natural numbers with
$$(k + n_{\mathrm{test}})\,\mathrm{sep} \leq h_{\mathrm{gap}}^{22}\, h, \qquad n_{\mathrm{detect}} \leq 2(k + n_{\mathrm{test}}).$$
Let $\mathrm{tame}, \mathrm{ram} \in [0, \infty]$ with $\mathrm{tame} \leq 2\,\mathrm{ram} + 8 f v$. Then
$$t'\, v_\ell(\mathrm{odd}) + t'\big(\mathrm{tame} + 2 n_{\mathrm{detect}}\, \mathrm{sep}\big) + (k + 1)\,\mathrm{sep} + 2v \leq 2t'\,\mathrm{ram} + e_\ell.$$

Lean: `New.Selmer.mul_padicValNat_add_le_add_denominatorError` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* First bound the multiples of $\mathrm{sep}$ in $\mathbb{N}$. By $t' \leq t$, $n_{\mathrm{detect}} \leq 2(k + n_{\mathrm{test}})$ and $k \leq k + n_{\mathrm{test}}$,
$$t' \cdot 2 n_{\mathrm{detect}}\, \mathrm{sep} + (k+1)\,\mathrm{sep} \leq t \cdot 4(k + n_{\mathrm{test}})\,\mathrm{sep} + (k + n_{\mathrm{test}} + 1)\,\mathrm{sep}.$$
The right side is $(4t + 1)(k + n_{\mathrm{test}})\,\mathrm{sep} + h_{\mathrm{gap}} h$. By the first hypothesis and $h \leq v$ it is at most $(4t+1)\, h_{\mathrm{gap}}^{22}\, v + h_{\mathrm{gap}}\, v$.

Now cast to $[0, \infty]$ and regroup the left side as
$$t'\, v_\ell(\mathrm{odd}) + t'\,\mathrm{tame} + 2v + \big(t' \cdot 2 n_{\mathrm{detect}}\,\mathrm{sep} + (k+1)\,\mathrm{sep}\big).$$
Replace $\mathrm{tame}$ by $2\,\mathrm{ram} + 8fv$ and the last group by the bound above. The result is
$$2t'\,\mathrm{ram} + \Big(t'\, v_\ell(\mathrm{odd}) + 8 f t' v + 2v + \big((4t+1) h_{\mathrm{gap}}^{22} + h_{\mathrm{gap}}\big) v\Big).$$
Finally $t' \leq t$ in the first two terms of the bracket gives $2t'\,\mathrm{ram} + e_\ell$. $\square$

**Example.** Take $t' = 1$, $h = 0$ and $\ell \nmid N$. Then $v = 0$ and $\mathrm{sep} = 0$. The lemma says $v_\ell(\mathrm{odd}) + \mathrm{tame} \leq 2\,\mathrm{ram} + t\, v_\ell(\mathrm{odd})$ for $\mathrm{tame} \leq 2\,\mathrm{ram}$. For a prime $\ell$ that divides neither $N$ nor the odd class bound, the characters cost only the ramification of the twist. This is the usual case: only finitely many primes $\ell$ have $e_\ell \neq 0$.
