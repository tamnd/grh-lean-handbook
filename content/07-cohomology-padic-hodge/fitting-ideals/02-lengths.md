---
title: Discrete valuation rings and relative lengths
lean:
  - Lib/General/Algebra/FittingIdealsAndLengths.lean
decls:
  - New.DVR
  - New.QuotSpan
  - New.PadicIntegerRing
  - New.length_quot_span_eq_addVal
  - New.relLength
  - New.relLength_add_length_inf
  - New.relLength_iInf_le
  - New.relLength_le_of_mapsTo
  - New.Lift.relLength_trans
  - New.Lift.relLength_le_of_relations
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Discrete valuation rings and relative lengths

This section fixes the rings and the measure of size. The rings are discrete valuation rings, and in the applications they are rings of integers of finite extensions of $\mathbb{Q}_\ell$. The measure of size is the length of a module, with values in $\mathbb{N} \cup \{\infty\}$. A Selmer group is a submodule of a module of cocycles, and its size is often known only modulo a second submodule. So the section introduces the length of one submodule modulo another, and it proves the rules that the later chapters use: additivity, a bound for an intersection, functoriality, transitivity, and a bound from linear relations.

### The rings

A discrete valuation ring is a principal ideal domain with exactly one nonzero prime ideal (Atiyah and Macdonald, Chapter 9; Serre, *Local Fields*, Chapter I, Section 1). Fix a uniformizer $\varpi$, a generator of the maximal ideal. Each nonzero $x$ is $u \varpi^k$ for a unit $u$ and a unique $k \geq 0$. Put $v(x) = k$ and $v(0) = \infty$. This is the normalized valuation. It does not depend on the choice of $\varpi$.

**Definition (Discrete valuation ring).** A commutative ring $O$ satisfies `DVR` if it is an integral domain and a discrete valuation ring. For $a \in O$, write $O/a$ for the quotient ring $O/aO$.

Lean: `New.DVR` (Lib/General/Algebra/FittingIdealsAndLengths.lean). The quotient is `New.QuotSpan` (Lib/General/Algebra/FittingIdealsAndLengths.lean). The valuation is `IsDiscreteValuationRing.addVal` (Mathlib), with values in $\mathbb{N}_\infty = \mathbb{N} \cup \{\infty\}$.

**Definition ($\ell$-adic integer ring).** Let $\ell$ be a prime. A commutative ring $O$ is an $\ell$-adic integer ring if it is a $\mathbb{Z}_\ell$-algebra, a discrete valuation ring of characteristic $0$, free and finite as a $\mathbb{Z}_\ell$-module, and if $O/I$ is finite for every nonzero ideal $I$.

Lean: `New.PadicIntegerRing` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

The ring of integers of a finite extension of $\mathbb{Q}_\ell$ is an $\ell$-adic integer ring (Serre, *Local Fields*, Chapter II, Section 2). Conversely, such a ring $O$ is a lattice in the field $O \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$, which is a finite extension of $\mathbb{Q}_\ell$, and $O$ is its ring of integers. The source does not need the converse. Section 7 proves that each coefficient ring of the source is an $\ell$-adic integer ring. The condition on finite quotients is part of the class because the source does not derive it from the other conditions.

### Length

A module $X$ over a ring $A$ has finite length $n$ if it has a chain $0 = X_0 \subsetneq X_1 \subsetneq \dots \subsetneq X_n = X$ of submodules with simple quotients. By the Jordan-Hölder theorem, $n$ does not depend on the chain (Atiyah and Macdonald, Proposition 6.7). If $X$ has no such chain, its length is $\infty$. The length is additive: for an exact sequence $0 \to X' \to X \to X'' \to 0$ the length of $X$ is the sum of the lengths of $X'$ and $X''$ (Atiyah and Macdonald, Proposition 6.9, which extends to $\mathbb{N}_\infty$ at once). The source uses the length `Module.length` of Mathlib, which is defined for every module and takes values in $\mathbb{N}_\infty$.

Over a discrete valuation ring the only simple module is the residue field $O/\varpi$. So a module of finite length is a finite direct sum of modules $O/\varpi^k$, and its length is the sum of the exponents. The basic computation is the length of a cyclic module.

**Lemma.** Let $O$ be a discrete valuation ring and $a \in O$. Then the length of $O/a$ is $v(a)$.

Lean: `New.length_quot_span_eq_addVal` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

*Proof.* For $a = 0$ both sides are $\infty$: the module $O$ has the infinite chain $\varpi^k O$. For $a = u\varpi^k$ the chain $\varpi^k O \subset \varpi^{k-1} O \subset \dots \subset O$ has $k$ steps, and each quotient is $O/\varpi$. The source quotes the lemma `Ring.ord_eq_addVal` of Mathlib. $\square$

A companion lemma `New.addVal_prod` says that $v(\prod_i f_i) = \sum_i v(f_i)$ for a finite product. With the lemma above it gives the length of a product of cyclic modules.

### Relative length

**Definition (Relative length).** Let $A$ be a ring, $M$ an $A$-module, and $S$, $T$ submodules of $M$. The *length of $S$ modulo $T$* is
$$\operatorname{len}(S \bmod T) = \operatorname{length}_A \bigl(S / (S \cap T)\bigr) \in \mathbb{N}_\infty .$$

Lean: `New.relLength` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

The module $S/(S \cap T)$ is the image of $S$ in $M/T$. The source records this as `New.relLength_eq_length_map_mkQ`. In the same way, for a linear map $f$ the length of $S$ modulo $\ker f$ is the length of $f(S)$ (`New.relLength_ker`), and the length of $S$ modulo $f^{-1}(T')$ is the length of $f(S)$ modulo $T'$ (`New.relLength_comap`). The length of $S$ modulo $T$ is $0$ exactly when $S \subseteq T$ (`New.relLength_eq_zero`), and the length of $S$ modulo $0$ is the length of $S$ (`New.relLength_bot`).

Why do the Selmer bounds need this notion? A Selmer group is cut out of a module of cocycles by local conditions. The source often controls a Selmer group only up to a submodule that it bounds in another way. For instance, a module of cocycles with values in $O/\varpi^M$ can have a part on which a condition holds automatically and a part on which it costs a definite length. The relative length measures the second part.

**Lemma.** Let $S$, $T$ be submodules of $M$. Then
$$\operatorname{len}(S \bmod T) + \operatorname{length}(S \cap T) = \operatorname{length}(S).$$

Lean: `New.relLength_add_length_inf` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

*Proof.* Apply additivity of length to $0 \to S \cap T \to S \to S/(S \cap T) \to 0$. $\square$

**Lemma.** Let $T_1, \dots, T_m$ be submodules of $M$, finitely many. Then
$$\operatorname{len}\Bigl(S \bmod \bigcap_{i} T_i\Bigr) \leq \sum_{i} \operatorname{len}(S \bmod T_i).$$

Lean: `New.relLength_iInf_le` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

*Proof.* The map $S \to \prod_i S/(S \cap T_i)$ has kernel $S \cap \bigcap_i T_i$. So $S / (S \cap \bigcap_i T_i)$ embeds in the product. A submodule has length at most that of the module, and the length of a finite product is the sum of the lengths. $\square$

This is the lemma that adds up local conditions. If a Selmer group is the intersection of the conditions at finitely many places, the cost of all conditions is at most the sum of the costs of each.

**Lemma.** Let $f \colon M \to M'$ be linear, $S$, $T$ submodules of $M$ and $S'$, $T'$ submodules of $M'$. Suppose that $f(S) \subseteq S'$, and that every $x \in S$ with $f(x) \in T'$ lies in $T$. Then $\operatorname{len}(S \bmod T) \leq \operatorname{len}(S' \bmod T')$.

Lean: `New.relLength_le_of_mapsTo` (Lib/General/Algebra/FittingIdealsAndLengths.lean). The case $f = \mathrm{id}$, with $S \subseteq S'$ and $T' \subseteq T$, is `New.relLength_mono`.

*Proof.* Let $K = S \cap f^{-1}(T')$. Then $K \subseteq S \cap T$, so $S/(S \cap T)$ is a quotient of $S/K$. The map $f$ induces an injective map $S/K \to S'/(S' \cap T')$. Lengths do not grow under quotients and injective maps. $\square$

### Two lemmas over $\mathbb{Z}_p$

The last two lemmas are stated for submodules $L$, $L'$, $L''$ of a $\mathbb{Z}_p$-module $V$, with $p$ prime. The source uses them for lattices of cocycles in the chapter on [cup products](/chapter/cup-products/).

**Lemma (Transitivity).** If $\operatorname{len}(L \bmod L') \leq m$ and $\operatorname{len}(L' \bmod L'') \leq n$ for natural numbers $m$, $n$, then $\operatorname{len}(L \bmod L'') \leq m + n$.

Lean: `New.Lift.relLength_trans` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

*Proof.* Work in $V/L''$ and write $\bar L$, $\bar L'$ for the images of $L$, $L'$. By the lemma on intersections above, the length of $\bar L$ is the length of $\bar L$ modulo $\bar L'$ plus the length of $\bar L \cap \bar L'$. The second term is at most the length of $\bar L'$, which is $\operatorname{len}(L' \bmod L'')$. The first term is the length of $L$ modulo the preimage of $\bar L'$, and that preimage contains $L'$, so it is at most $\operatorname{len}(L \bmod L')$. $\square$

The proof uses nothing about $\mathbb{Z}_p$. The lemma holds over every ring, with the same proof.

**Lemma (Bound from relations).** Let $t$, $m$ be natural numbers. Suppose that $p^t x \in L'$ for every $x \in L$. Suppose that for any $m + 1$ elements $x_0, \dots, x_m$ of $L$ with $p x_j \in L'$ for all $j$, there are $a_0, \dots, a_m \in \mathbb{Z}_p$ and an index $j$ with $a_j = 1$ and $\sum_i a_i x_i \in L'$. Then $\operatorname{len}(L \bmod L') \leq t m$.

Lean: `New.Lift.relLength_le_of_relations` (Lib/General/Algebra/FittingIdealsAndLengths.lean). The case $t = 1$, for a submodule $T$ with $p T \subseteq L'$, is `New.Lift.relLength_le_of_prime_smul_mem`.

*Proof.* First let $t = 1$, so $Q = L/(L \cap L')$ is killed by $p$. Then $Q$ is a vector space over $\mathbb{F}_p$, and its length is its dimension. Take $m + 1$ classes in $Q$. The hypothesis gives a relation among them whose coefficient $a_j = 1$ is nonzero modulo $p$. So any $m + 1$ classes are linearly dependent, and the dimension is at most $m$. This is the case $t = 1$.

For $t = 0$ the hypothesis says $L \subseteq L'$, and the length is $0$. For $t \geq 2$, induct on $t$. Let $T = \{x \in L : p x \in L'\}$. The case $t = 1$ applies to $T$ and gives $\operatorname{len}(T \bmod L') \leq m$. For $L$ modulo $T$: if $x \in L$, then $p^{t-1}(p x) \in L'$, so $p^{t-1} x \in T$. And if $x_0, \dots, x_m \in L$ have $p x_j \in T$, then $p x_j \in L$ and $p (p x_j) \in L'$. The hypothesis, applied to the $p x_j$, gives $a$ with $a_j = 1$ and $p \sum_i a_i x_i \in L'$, so $\sum_i a_i x_i \in T$. So the induction hypothesis applies to $L$ and $T$ with $t - 1$, and gives $\operatorname{len}(L \bmod T) \leq (t-1) m$. Transitivity gives $t m$. $\square$

**Example.** Let $L = \mathbb{Z}_p^m$ and $L' = p^t \mathbb{Z}_p^m$. Then the hypothesis holds: elements $x$ with $p x \in L'$ lie in $p^{t-1} \mathbb{Z}_p^m$, and $m + 1$ vectors in a module of rank $m$ modulo $p^t$ have a relation with a unit coefficient. The bound $t m$ is the exact length. So the lemma is sharp.

**Remark (Formalization).** The lemma is the standard bound of the length of a module killed by $p^t$ by $t$ times the dimension of its $p$-torsion. The source states it in a form that needs no quotient module: the hypothesis on relations speaks of elements of $L$ only. The proof in the source filters by $T$ as above. The relative length takes values in $\mathbb{N}_\infty$, so the lemma also proves that the length is finite.
