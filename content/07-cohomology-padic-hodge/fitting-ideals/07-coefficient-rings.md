---
title: Coefficient rings
lean:
  - Lib/General/NumberTheory/CoefficientRings.lean
  - Lib/General/NumberTheory/PadicLimitsValuation.lean
  - Lib/General/NumberTheory/CoefficientInclusion.lean
  - Lib/General/NumberTheory/LargeResidueField.lean
decls:
  - New.card_eq_pow_length
  - New.length_eq_top_of_infinite
  - New.length_le_of_card_le
  - New.length_le_of_card_dvd
  - New.length_le_of_card_dvd_or_le
  - New.CoeffRing
  - New.CoeffRing.exists_mem_iff
  - New.CoeffRing.dvd_iff_norm_le
  - New.CoeffRing.exists_mem_of_mem_adjoin
  - New.CoeffRing.eventually_mem
  - New.ellVal
  - New.ellVal_mul_le
  - New.ellVal_pow
  - New.CoeffRing.isUnit_iff_norm_eq_one
  - New.CoeffRing.uniformizer
  - New.CoeffRing.normLength
  - New.CoeffRing.normLength_addVal
  - New.CoeffRing.normLength_natCast_of_irreducible
  - New.CoeffRing.eventually_exists_isPrimitiveRoot
  - New.CoeffRing.toIntQpBar
  - New.CoeffRing.dvd_of_toIntQpBar_dvd
  - New.CoeffRing.eventually_exists_toIntQpBar_eq
  - New.Selmer.pow_dvd_geom_sum
  - New.Selmer.frequently_lt_card_residueField
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Coefficient rings

Sections 2 to 6 work over an abstract discrete valuation ring $O$. In Volume 12, $O$ is the ring of integers of a finite extension of $\mathbb{Q}_\ell$, and the argument must often pass to a larger ring: to get a root of unity, to get a large residue field, or to make the entries of a matrix over $\bar{\mathbb{Z}}_\ell$ integral over one fixed ring. Lengths over different rings are not comparable, so the source also rescales them. This section describes the coefficient rings and the rescaling. The files are in `Lib/General/NumberTheory/`.

### Lengths and cardinalities

Let $R$ be a discrete valuation ring with finite residue field $k$. A module $X$ of finite length $n$ has a composition series with $n$ quotients, each isomorphic to $k$. So $\# X = (\# k)^n$ (Serre, *Local Fields*, Chapter I, Section 1, for the structure of $R$). The source proves this for its class of $\ell$-adic integer rings.

**Lemma.** Let $R$ be an $\ell$-adic integer ring with residue field $k$, and let $X$ be an $R$-module.

1. If $\operatorname{len}_R X < \infty$, then $\# X = (\# k)^{\operatorname{len}_R X}$.
2. If $X$ is infinite, then $\operatorname{len}_R X = \infty$.
3. If $X$ is finite and $\# X \leq \# Y$, then $\operatorname{len}_R X \leq \operatorname{len}_R Y$.
4. If $\# X$ divides $\# Y$, then $\operatorname{len}_R X \leq \operatorname{len}_R Y$.

Lean: `New.card_eq_pow_length`, `New.length_eq_top_of_infinite`, `New.length_le_of_card_le`, `New.length_le_of_card_dvd` (Lib/General/NumberTheory/CoefficientRings.lean). The lemma `New.length_le_of_card_dvd_or_le` takes the disjunction of the hypotheses of 3 and 4.

Here `New.PadicIntegerRing R ℓ` says that $R$ is a discrete valuation ring of characteristic $0$, finite and free over $\mathbb{Z}_\ell$, with finite quotients by nonzero ideals. Section 2 introduced it.

*Proof.* Part 1 is by induction on a composition series. Each simple quotient is $R/\mathfrak{m} = k$, and $\# M = \# (M/N) \cdot \# N$. For part 2, if the length were finite, part 1 would make $\# X$ a positive power of $\# k$, while Lean's $\# X$ is $0$. For part 3, $Y$ is finite since $\# Y \geq \# X > 0$, and the exponents compare since $\# k > 1$. For part 4, if $Y$ is infinite, then $\operatorname{len} Y = \infty$. If $Y$ is finite, then $\# X \neq 0$, so $X$ is finite, and part 3 applies. $\square$

**Remark (Formalization).** These statements use `Nat.card`, which is $0$ for an infinite type. This junk value explains the form of the hypotheses. In part 3 the hypothesis `[Finite X]` is necessary. Without it, an infinite $X$ has $\# X = 0 \leq \# Y$ for every $Y$, but $\operatorname{len} X = \infty$. In part 4 no finiteness hypothesis is needed. If $Y$ is infinite, then $\# Y = 0$ and every number divides it, but then $\operatorname{len} Y = \infty$ and the conclusion holds. If $Y$ is finite and nonzero in cardinality, then $\# X$ divides a positive number, so $\# X \neq 0$ and $X$ is finite. The use in `New/Congruences/LocalLoss/TateDualBound.lean` is through part 4, and the use in `New/Congruences/Selmer/Count.lean` is through part 3.

### The rings inside $\bar{\mathbb{Q}}_\ell$

Let $\bar{\mathbb{Q}}_\ell$ be an algebraic closure of $\mathbb{Q}_\ell$ with its norm, `PadicAlgCl ℓ` in the source.

**Definition (Coefficient rings).** A coefficient ring at $\ell$ is a $\mathbb{Z}_\ell$-subalgebra of $\bar{\mathbb{Q}}_\ell$ of the form
$$O_K = \{ x \in K : \| x \| \leq 1 \},$$
where $K \subseteq \bar{\mathbb{Q}}_\ell$ is a finite Galois extension of $\mathbb{Q}_\ell$. The type `New.CoeffRing ℓ` is the set of these subalgebras, ordered by inclusion.

Lean: `New.CoeffRing` (Lib/General/NumberTheory/CoefficientRings.lean). The lemma `New.CoeffRing.exists_mem_iff` recovers a field $K$ from $O$.

The textbook facts are in Serre, *Local Fields*, Chapter II, Section 2: the ring of integers of a finite extension of $\mathbb{Q}_\ell$ is a complete discrete valuation ring, finite over $\mathbb{Z}_\ell$, with finite residue field.

**Proposition.** Let $O$ be a coefficient ring.

1. For $x, y \in O$, $x \mid y$ if and only if $\| y \| \leq \| x \|$.
2. $O$ is a discrete valuation ring, a finite $\mathbb{Z}_\ell$-module, compact, and an $\ell$-adic integer ring.
3. $x \in O$ is a unit if and only if $\| x \| = 1$.
4. The coefficient rings are directed by inclusion. For each finite $s \subseteq \bar{\mathbb{Q}}_\ell$, some $O$ contains every element of $\mathbb{Q}_\ell(s)$ of norm at most $1$.
5. Every $x \in \bar{\mathbb{Q}}_\ell$ with $\|x\| \leq 1$ lies in every sufficiently large coefficient ring.

Lean: `New.CoeffRing.dvd_iff_norm_le` (Lib/General/NumberTheory/CoefficientRings.lean) for 1; instances of `New.DVR`, `Module.Finite` (Mathlib) and `CompactSpace` (Mathlib) in the same file, and `New.PadicIntegerRing` (Lib/General/NumberTheory/PadicLimitsValuation.lean) for 2; `New.CoeffRing.isUnit_iff_norm_eq_one` (Lib/General/NumberTheory/PadicLimitsValuation.lean) for 3; an instance of `IsDirectedOrder` (Mathlib) and `New.CoeffRing.exists_mem_of_mem_adjoin` for 4; `New.CoeffRing.eventually_mem` for 5 (Lib/General/NumberTheory/CoefficientRings.lean).

*Proof.* For 1, $y/x$ lies in $K$ and has norm at most $1$. For 2, $O$ is integral over $\mathbb{Z}_\ell$ and contained in a finite extension, so it is a finite $\mathbb{Z}_\ell$-module and Noetherian. By 1, divisibility is total, so $O$ is a valuation ring. Its maximal ideal lies over $\ell \mathbb{Z}_\ell \neq 0$, so it is not a field. Compactness comes from finiteness over the compact ring $\mathbb{Z}_\ell$. Quotients by nonzero ideals are finite, since these ideals are open and $O$ is compact. Part 3 follows from 1 with $y = 1$. For 4, take the integers of the Galois closure of $\mathbb{Q}_\ell(s)$. Part 5 is 4 with $s = \{x\}$. $\square$

In Lean the phrase "every sufficiently large $O$" is the filter `Filter.atTop` on the directed set `CoeffRing ℓ`. Statements of the form "for all large $O$" combine by `filter_upwards`, since a finite intersection of such conditions again holds for all large $O$.

**Remark (Formalization).** The file `CoefficientRings.lean` has, at line 30, the declaration `attribute [instance 10]` for six instances on subalgebras: `instSMulSubtypeMem`, `instMulActionSubtypeMem`, `moduleLeft`, `instDistribMulActionSubtypeMem`, `instSMulWithZeroSubtypeMem` and `instMulActionWithZeroSubtypeMem`. The attribute is not `local` and not `scoped`. So it lowers the priority of these Mathlib instances in every file that imports this one, not only in this file. The comment says that the aim is "so that other instances are tried first". This is a global change to instance search, made in a file about $\ell$-adic rings. It does not change any statement. It can change which proof of a `SMul` instance Lean finds, and so it can change elaboration times in files that import it. This handbook records it as a finding of the review.

### The valuation and normalized length

The rings $O$ have different uniformizers, so $\operatorname{addVal}_O$ is not the same on different rings: $\operatorname{addVal}_O(\ell) = e(O)$, the ramification index. The source uses the valuation of $\bar{\mathbb{Q}}_\ell$ normalized by $v(\ell) = 1$.

**Definition (The valuation $v$).** For $x \in \bar{\mathbb{Q}}_\ell$,
$$v(x) = \begin{cases} \infty & \text{if } \|x\| = 0, \\ \max(0, -\log_\ell \|x\|) & \text{otherwise.} \end{cases}$$

Lean: `New.ellVal` (Lib/GaloisRep/Main/SelmerModules.lean). The source writes the second case as `ENNReal.ofReal (-Real.logb ℓ ‖x‖)`, and `ENNReal.ofReal` (Mathlib) sends negative numbers to $0$.

**Remark (Formalization).** The value $v(x)$ for $\|x\| > 1$ is a junk value: the textbook valuation would be negative there, and the source gives $0$, because the values lie in $[0, \infty]$. For this reason $v$ is only subadditive on products in general. The source states $v(x y) \leq v(x) + v(y)$.

Lean: `New.ellVal_mul_le`, `New.ellVal_pow` (Lib/General/NumberTheory/PadicLimitsValuation.lean).

 The inequality is strict for $x = \ell^{-1}$ and $y = \ell$: $v(xy) = v(1) = 0$, while $v(x) + v(y) = 0 + 1 = 1$. For $\|x\|, \|y\| \leq 1$ equality holds, and every use in a coefficient ring is of this kind. The rule $v(x^k) = k\, v(x)$ holds for all $x$, since $\|x^k\| = \|x\|^k$ and the truncation commutes with multiplication by $k \geq 0$.

**Definition (Normalized length).** Let $\varpi_O$ be the uniformizer of $O$ given by `(exists_irreducible O).choose`. The normalized length is the additive map $\lambda_O \colon \mathbb{N} \cup \{\infty\} \to [0, \infty]$ with $\lambda_O(n) = n\, v(\varpi_O)$ and $\lambda_O(\infty) = \infty$.

Lean: `New.CoeffRing.uniformizer`, `New.CoeffRing.normLength` (Lib/General/NumberTheory/PadicLimitsValuation.lean).

**Proposition.** Let $O$ be a coefficient ring.

1. For $x \in O$, $\lambda_O(\operatorname{addVal}_O(x)) = v(x)$.
2. For every uniformizer $\varpi$ of $O$ and $n \in \mathbb{N}$, $\lambda_O(n) = n\, v(\varpi)$.

Lean: `New.CoeffRing.normLength_addVal`, `New.CoeffRing.normLength_natCast_of_irreducible` (Lib/General/NumberTheory/PadicLimitsValuation.lean).

*Proof.* Write $x = u \varpi_O^n$ with $u$ a unit. Then $\|u\| = 1$, so $v(x) = n\, v(\varpi_O) = \lambda_O(n)$. For $x = 0$ both sides are $\infty$. Part 2 is part 1 for $x = \varpi^n$. $\square$

So $\lambda_O(\operatorname{len}_O M)$ is the length of $M$ measured in units of $v(\ell) = 1$. For $M = O/\ell$, $\lambda_O(\operatorname{len} M) = e(O) \cdot (1/e(O)) = 1$ for every $O$. This makes lengths over different coefficient rings comparable. The Selmer bounds of [the main summands](/chapter/main-summands/) and of `New/Congruences/FirstOrder/RibetElement.lean` are stated with $\lambda_O$.

**Remark (Formalization).** The uniformizer $\varpi_O$ comes from `choose`, so it is a fixed but unspecified element. Part 2 shows that $\lambda_O$ does not depend on this choice, since any two uniformizers differ by a unit and have the same norm. The docstring of `normLength` says this. No statement of the source depends on which uniformizer `choose` gives.

### Passing to a larger ring

Four results let the argument enlarge $O$.

**Proposition.**

1. For $k \neq 0$, every sufficiently large $O$ contains a primitive $k$-th root of unity.
2. Let $\bar{\mathbb{Z}}_\ell$ be the ring of $x \in \bar{\mathbb{Q}}_\ell$ with $\|x\| \leq 1$, `intQpBar ℓ` in the source. The inclusion $O \to \bar{\mathbb{Z}}_\ell$ reflects divisibility: if $z \mid z'$ in $\bar{\mathbb{Z}}_\ell$, then $z \mid z'$ in $O$.
3. For a finite family $x \colon \sigma \to \bar{\mathbb{Z}}_\ell$, every sufficiently large $O$ contains all $x_j$.
4. For each $c \in \mathbb{N}$ and each $O_0$, there is $O \supseteq O_0$ with $c \cdot e(O) + 1 < \# (O/\mathfrak{m}_O)$, where $e(O) = \operatorname{addVal}_O(\ell)$.

Lean: `New.CoeffRing.eventually_exists_isPrimitiveRoot` (Lib/General/NumberTheory/PadicLimitsValuation.lean); `New.CoeffRing.toIntQpBar`, `New.CoeffRing.dvd_of_toIntQpBar_dvd`, `New.CoeffRing.eventually_exists_toIntQpBar_eq` (Lib/General/NumberTheory/CoefficientInclusion.lean); `New.Selmer.frequently_lt_card_residueField` (Lib/General/NumberTheory/LargeResidueField.lean).

*Proof.* For 1, a root of unity has norm $1$, so this is part 5 of the proposition on the rings. Part 2 is part 1 of that proposition read in both rings. Part 3 is again part 5, applied to each of the finitely many $x_j$. For 4, let $K_0$ have degree $d$ over $\mathbb{Q}_\ell$. Choose $k > 0$ with $c d k + 1 < \ell^k - 1$, and adjoin a primitive root of unity $\zeta$ of order $\ell^k - 1$. The new field has degree at most $d k$, so $e(O) \leq d k$. The powers of $\zeta$ have distinct residues, since their differences are units, so $\#(O/\mathfrak{m}) \geq \ell^k - 1$. $\square$

The docstring of `LargeResidueField.lean` states that the extension in 4 is unramified but that the proof does not use this. The statement is "frequently" in the filter, not "eventually": not every large $O$ has a large residue field relative to $e(O)$, since ramified extensions raise $e(O)$ without raising $\#(O/\mathfrak{m})$. The source uses 4 in [the twisting theorem](/chapter/twisting-theorem/). There the hypothesis `IsTorsionLevel` of `New/Congruences/Selmer/GeneralTheorem.lean` asks for a residue field with more than $2 \operatorname{rank} \cdot a + 1$ elements, and part 4 gives rings with this property.

**Lemma (Geometric sums).** Let $O$ be a commutative ring with a ring map $f \colon O \to \bar{\mathbb{Z}}_\ell$ that reflects divisibility. Let $r \in \mathbb{Q}_{\geq 0}$ with $r \leq 1$, let $M, N \in \mathbb{N}$ with $M \leq N r$, and let $\alpha \in O$ with $r \leq v(f(\alpha - 1))$. Then
$$\ell^M \ \Big|\ \sum_{i < \ell^N} \alpha^i .$$

Lean: `New.Selmer.pow_dvd_geom_sum` (Lib/General/NumberTheory/CoefficientInclusion.lean).

*Proof.* Since $f$ reflects divisibility, it suffices to show $M \leq v\bigl(\sum_{i < \ell^N} f(\alpha)^i\bigr)$ in $\bar{\mathbb{Z}}_\ell$. Put $\beta = f(\alpha)$. The sum over $i < \ell^N$ is the product over $m < N$ of the sums $\sum_{i < \ell} \beta^{\ell^m i}$. Each factor is congruent to $\ell$ modulo $\beta - 1$, since $\beta - 1$ divides $\beta^j - 1$ for every $j$. So each factor has $v \geq \min(v(\ell), v(\beta - 1)) \geq \min(1, r) = r$, and the product has $v \geq N r \geq M$. $\square$

The step "each factor has valuation at least $r$" is the lemma `New.Selmer.le_ellVal_geom_sum` of `Lib/General/NumberTheory/GaussValuation.lean`. The source uses the geometric sum lemma in `New/Congruences/Selmer/Line.lean`, to show that $\ell^M$ divides $\sum_{j < \ell^N} \alpha^j$ for every $\alpha$ with $y \mid \alpha - 1$, for a fixed element $y$.

**Remark (Formalization).** The hypothesis $r \leq 1$ is needed. For $\alpha = 1$ the sum is $\ell^N$, of valuation exactly $N$, while $v(f(\alpha - 1)) = v(0) = \infty$ allows any $r$. With $r = 2$ and $M = 2N$ the conclusion $\ell^{2N} \mid \ell^N$ would be false for $N \geq 1$. The bound $\min(1, r)$ per factor comes from $v(\ell) = 1$.
