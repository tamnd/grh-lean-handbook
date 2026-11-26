---
title: Limits of crystalline representations
lean:
  - Lib/PadicHodge/Limit/CrystallineLimit.lean
  - Lib/PadicHodge/Limit/TraceLimit.lean
decls:
  - New.Period.IsCrystallineUpTo
  - New.Period.PadicRep
  - New.Lift.uniform_period_bound
  - New.Period.IsFiniteGroupRingQuotient
  - New.Period.exists_finite_groupRing_quotient
  - New.Period.isCrystalline_of_trace_limit
  - New.Period.exists_uniform_trace_sum_eq_jump
  - New.GaloisRep.tateTwistHom
  - New.GaloisRep.IsTraceLimit
  - New.GaloisRep.IsTraceLimit.exists_isCrystallineUpTo_tateTwistHom
  - New.GaloisRep.IsTraceLimit.isGoodAt
  - New.GaloisRep.IsTraceLimit.tendsto_jump
  - New.GaloisRep.IsTraceLimit.polyKillsAt
  - New.GaloisRep.local_clauses_of_trace_limit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Limits of crystalline representations

This section treats `Lib/PadicHodge/Limit`. Its main result says that a $p$-adic limit of crystalline representations with jumps in a fixed interval is crystalline. The key input is one period that bounds the denominators of all such lattices at the same time. The section ends with the passage of the local conditions of a Galois representation to a limit of traces.

### The classical theorem

Berger proved that the set of crystalline representations of $G_K$ with Hodge-Tate weights in a fixed interval $[0, h]$ is closed. The statement is for $\mathbb{Q}_p$-representations: if $V$ is a $p$-adic limit of such representations, in a sense made precise there, then $V$ is crystalline with weights in $[0, h]$. The reference is L. Berger, Limites de représentations cristallines, Compositio Math. 140 (2004) 1473-1498. Liu proved a version for torsion representations and lattices in T. Liu, Torsion $p$-adic Galois representations and a conjecture of Fontaine, Ann. Sci. ENS 40 (2007) 633-674. The docstring of `Lib/PadicHodge/Limit/TraceLimit.lean` cites both. It also cites P. Wake and C. Wang-Erickson, Deformation conditions for pseudorepresentations, Forum Math. Sigma 7 (2019), for the passage from traces to the image of the group ring.

The source does not formalize Berger's theorem or Liu's theorem in their original form. It proves a limit theorem of its own, stated with traces on a group ring.

### Bounded jumps

**Definition.** Let $\rho$ be a representation of $\Gamma$ on $T$ over a ring $R$. For $h \geq 0$, $\rho$ is *crystalline up to $h$* if $\rho$ is crystalline and, for every $\gamma : R \to \mathbb{C}_p$ and every $k \in \mathbb{Z}$ with nonzero jump multiplicity at $\gamma$, $0 \leq k \leq h$.

Lean: `New.Period.IsCrystallineUpTo` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

Here "crystalline" is `New.Period.IsCrystalline`: the invariants of $B_{\max} \otimes T$ span it over $B_{\max}$. The jump multiplicity is `New.Period.jump` of [Period rings and crystalline representations](/chapter/period-rings/).

**Definition.** A *$p$-adic matrix representation* of a group $\Gamma$ is a finite type $m$ with decidable equality and a homomorphism $\Gamma \to \mathrm{GL}_m(\overline{\mathbb{Q}}_p)$.

Lean: `New.Period.PadicRep` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

### The uniform period bound

**Theorem (Uniform period bound).** Let $\Gamma$ be a group with a homomorphism to $G_{\mathbb{Q}_p}$ of open image, and let $h \geq 0$. There is $a \in A_{\max}$, a unit in $B_{\max}$, with the following property. Let $T$ be a $\mathbb{Z}_p$-module with a finite basis $e$, and let $\rho$ be a representation of $\Gamma$ on $T$ that is crystalline up to $h$. Then:

1. for every $t \in T$, $a \otimes t$ is in the $A_{\max}$-span of the invariants of $A_{\max} \otimes T$;
2. there are matrices $U$, $U'$ over $A_{\max}$ with $UU' = a \cdot 1$ and $\rho(g)\, g(U) = U$ for all $g \in \Gamma$, where $\rho(g)$ is the matrix of $\rho(g)$ in $e$.

Lean: `New.Lift.uniform_period_bound` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

*Proof.* The source outlines the proof as follows. Take the Kummer chart $k$ of `New.Lift.exists_kummerChart` for $\Gamma$, and let $l$ be the least integer with $3e \leq p^l$ ($l = \lceil \log_p 3e \rceil$). Let $\alpha : A_{\inf} \to A_{\max}$ be $\varphi^l$ followed by the inclusion. Put $a = \alpha(E\tau)^h$. It is a unit of $B_{\max}$ because $E\tau$ divides $\mu$. For a given $\rho$, a period matrix of $\rho$ has entries in $B^+$. The radius lemma `New.Lift.Chart.radius_lemma` then gives, after $\varphi^l$, a change of basis fixed by $\Gamma$ that moves it into $A_{\max}$, with the factor $a$. $\square$

The point is the order of quantifiers. The element $a$ depends only on $\Gamma$ and $h$. It does not depend on $T$, on its rank, or on $\rho$. The docstring calls this result "Dwork's trick (an integral crystalline comparison with a uniform denominator)".

**Remark (Formalization).** The theorem is an existence statement. Users obtain $a$ by `obtain`, so the element is fixed for each $\Gamma$ and $h$ but is not given by a formula in the statement. The formula $a = \alpha(E\tau)^h$ is visible only in the proof. The basis $e$ is part of the hypotheses, so the statement is for free $\mathbb{Z}_p$-modules of finite rank. The theorem is used in `New.Period.isCrystalline_of_trace_limit`, in `New.Period.exists_uniform_trace_sum_eq_jump` and in `New.GaloisRep.IsTraceLimit.isKilledBy`.

### The image of the group ring

**Definition.** Let $\tau_s$, for $s$ in a type $\kappa$, be $p$-adic matrix representations of a compact group $G$. A *finite group ring quotient* for them is a $\mathbb{Z}_p$-algebra $T$ with a surjective algebra map $q : \mathbb{Z}_p[G] \to T$ and algebra maps $u_s$ from $T$ to matrices, such that:

1. $T$ is free and finitely generated over $\mathbb{Z}_p$;
2. $u_s \circ q$ is the linear extension of $\tau_s$ to $\mathbb{Z}_p[G]$, for every $s$;
3. $q(y) = 0$ if and only if the extension of every $\tau_s$ kills $y$;
4. for every $h$ and every multiplicative map $w : \Delta \to \mathbb{Z}_p[G]$, if every $\tau_s$ read along $w$ is crystalline up to $h$, then $\Delta$ acting on $T$ by left multiplication with $q(w(g))$ is crystalline up to $h$.

Lean: `New.Period.IsFiniteGroupRingQuotient` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

**Lemma.** Let $G$ be a compact topological group, and let $\tau_s$, for $s$ in a finite type $\kappa$, be continuous $p$-adic matrix representations of $G$. Then a finite group ring quotient for them exists.

Lean: `New.Period.exists_finite_groupRing_quotient` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

*Proof.* The source outlines the proof as follows. $T$ is the image of $\mathbb{Z}_p[G]$ in the product of the matrix algebras. Each $\tau_s$ is conjugate to a representation over the integers of a finite extension of $\mathbb{Q}_p$. So the image lies in a finite $\mathbb{Z}_p$-module. It has no torsion, since it lies in matrices over $\overline{\mathbb{Q}}_p$, so it is free. For property 4, the columns of the maps $u_s$ are jointly injective equivariant maps from $T$ to the $\tau_s$. The crystalline property passes to subrepresentations of finite direct sums (`New.Period.IsAdmissible.of_jointly_injective`), and every jump of $T$ is a jump of some $\tau_s$. $\square$

The map $w$ allows twists. For a decomposition group $\Delta$ and the map $g \mapsto \chi(g)^{-d}[g]$, the representation $\tau_s$ read along $w$ is the Tate twist of the restriction of $\tau_s$ to $\Delta$. The source defines this map as `New.GaloisRep.tateTwistHom`.

### The limit theorem

**Theorem (Limit theorem).** Let $G$ be a compact topological group. Let $\Delta$ be a group with a homomorphism to $G_{\mathbb{Q}_p}$ of open image, and let $w : \Delta \to \mathbb{Z}_p[G]$ be multiplicative. Let $R$ be a continuous $p$-adic matrix representation of $G$ with non-degenerate trace form. Let $X_\eta$, for $\eta$ in a type $I$, be finite families of continuous $p$-adic matrix representations of $G$. Assume that every member of every $X_\eta$, read along $w$, is crystalline up to $h$. Assume that for every $\varepsilon > 0$ there is $\eta$ such that every $y \in \mathbb{Z}_p[G]$ killed by all members of $X_\eta$ has $\lVert \mathrm{tr}\, R(y) \rVert \leq \varepsilon$. Then $R$ read along $w$ is crystalline.

Lean: `New.Period.isCrystalline_of_trace_limit` (Lib/PadicHodge/Limit/CrystallineLimit.lean).

*Proof.* The source outlines the proof as follows. Let $T$ be the image of $\mathbb{Z}_p[G]$ under $R$. For each $k$, let $T'_k$ be the image under the families $X_{\eta_0}, \ldots, X_{\eta_k}$, with $\eta_j$ chosen so that the kernel of $\mathbb{Z}_p[G] \to T'_k$ goes to $p^k T$. This uses the trace hypothesis and the non-degenerate trace form. Each $T'_k$ is a finite group ring quotient, so it is crystalline up to $h$. The uniform period bound gives one $\delta$ with $\delta \otimes 1$ in the $A_{\max}$-span of the invariants of every $A_{\max} \otimes T'_k$. Traces control divisibility by $p^k$ in $T$. So the source gets elements of $A_{\max} \otimes T$ that are invariant modulo $p^k$ for every $k$, and an element that is invariant modulo every $p^k$ is invariant. This gives $\delta \otimes 1$ in the span of the invariants of $A_{\max} \otimes T$. Since $\delta$ is a unit of $B_{\max}$, $T$ is crystalline, and so is $R$. $\square$

The conclusion is crystalline, without a bound on the jumps. The source gets the bound by a separate step, see `New.GaloisRep.isCrystallineUpTo_tateTwistHom` below.

**Remark (Formalization).** The classical theorem has a limit of representations of a fixed dimension, with convergence of lattices or of characters. The source asks for less. The families $X_\eta$ can have any finite number of members of any dimension, and convergence is a bound on traces of $R$ on the group ring elements that the family kills. The source says that this is Liu's theorem applied to the image of the group ring. The hypothesis "trace form non-degenerate" is `New.IsTraceNondeg`: an element $x$ of the span of $R(G)$ with $\mathrm{tr}(x R(g)) = 0$ for all $g$ is $0$.

### Jumps from traces

**Lemma.** Let $\Gamma$ be a group with a homomorphism to $G_{\mathbb{Q}_p}$ of open image. Let $n \geq 0$ and $w \in \mathbb{Z}$. There is $t \in \mathbb{C}_p$ with the following property. Let $T$ have a finite basis $\varepsilon$ over $\mathbb{Z}_p$, let $\rho$ on $T$ be crystalline up to $n$, and let $x \in T$. Then there is $z$ with $\lVert z_s \rVert \leq 1$ for all $s$, such that for every $\gamma$, every $p$-adic matrix representation $r$ of $\Gamma$ that is potentially crystalline, and every $\mathbb{Z}_p$-linear map $u$ from $T$ to matrices with $u(gy) = r(g)u(y)$ and $u(x) = 1$, the multiplicity of the jump $w$ of $r$ at $\gamma$ is $t \sum_s z_s\, \gamma(\mathrm{tr}\, u(\varepsilon_s))$.

Lean: `New.Period.exists_uniform_trace_sum_eq_jump` (Lib/PadicHodge/Limit/TraceLimit.lean).

The constant $t$ depends only on $\Gamma$, $n$ and $w$. This is the reason that multiplicities of jumps pass to limits. The proof uses the uniform period bound to get a common denominator for the Hodge-Tate projectors. The lemma does not state that $t \neq 0$. That follows from the case of the trivial representation of rank one, where the multiplicity of the jump $0$ is $1$.

### Limits of traces of Galois representations

The rest of the section works with Galois representations of a number field $E$, a place $A$ of $\Omega$ and a prime $\ell$. A representation is *good* at $A$ (`New.GaloisRep.IsGoodAt`) if it is trivial on inertia at $A$ when $\ell$ is a unit at $A$, and its restriction to the decomposition group is crystalline for every embedding that induces $A$.

**Definition (Trace limit).** Let $r$ be a Galois representation, $A$ a place, $F$ a filter on a type $I$, $a_{\eta, i}$ coefficients in $\overline{\mathbb{Q}}_\ell$ and $\rho_{\eta, i}$ $\ell$-adic matrix representations, with $i$ in a finite type $\iota_\eta$. Then $r$ is a *trace limit* of the $\rho_{\eta,i}$ if:

1. $r$ is continuous and has non-degenerate trace form;
2. each $\rho_{\eta, i}$ is continuous and good at $A$;
3. $I$ is finite, or there are multisets $J$ such that all $\rho_{\eta, i}$ have jumps $J$ at $A$;
4. the functions $g \mapsto \sum_i a_{\eta, i}\, \mathrm{tr}\, \rho_{\eta, i}(g)$ converge uniformly along $F$ to $g \mapsto \mathrm{tr}\, r(g)$.

Lean: `New.GaloisRep.IsTraceLimit` (Lib/PadicHodge/Limit/TraceLimit.lean).

**Lemma.** Let $r$ be a trace limit of the $\rho_{\eta, i}$ along a nontrivial filter, and fix an embedding that induces $A$. Then there is $d$ such that $r$ and all $\rho_{\eta, i}$, read along `tateTwistHom A d`, are crystalline up to $2d$.

Lean: `New.GaloisRep.IsTraceLimit.exists_isCrystallineUpTo_tateTwistHom` (Lib/PadicHodge/Limit/TraceLimit.lean).

*Proof.* The jumps of $r$ and of all $\rho_{\eta, i}$ form a finite set. For $r$ this holds because $r$ is continuous. For the $\rho_{\eta, i}$ it is property 3. Take $d$ above their absolute values. The twist by $\chi^{-d}$ moves the jumps into $[0, 2d]$. The twists of the $\rho_{\eta, i}$ are crystalline as twists of crystalline representations. The twist of $r$ is crystalline by the limit theorem. $\square$

**Theorem.** A trace limit, along a nontrivial filter, of representations good at $A$ is good at $A$.

Lean: `New.GaloisRep.IsTraceLimit.isGoodAt` (Lib/PadicHodge/Limit/TraceLimit.lean).

**Theorem.** Let $r$ be a trace limit along a nontrivial filter $F$, and fix an embedding that induces $A$. For every $\gamma$ and $w$, the multiplicity of the jump $w$ of $r$ at $\gamma$ is the limit along $F$ of $\sum_i a_{\eta, i}$ times the multiplicity of $w$ for $\rho_{\eta, i}$.

Lean: `New.GaloisRep.IsTraceLimit.tendsto_jump` (Lib/PadicHodge/Limit/TraceLimit.lean).

**Theorem.** Let $r$ be a trace limit along a nontrivial filter. Let polynomials $Q_{\eta, i}$ kill $s$ at $A$ for $\rho_{\eta, i}$, let $P$ and all $Q_{\eta, i}$ have degree less than $n$, and let the traces weighted by each coefficient converge: for every $l$, $\sum_i a_{\eta,i}\, (Q_{\eta,i})_l\, \mathrm{tr}\,\rho_{\eta,i}$ converges uniformly to $P_l\, \mathrm{tr}\, r$. Then $P$ kills $s$ at $A$ for $r$.

Lean: `New.GaloisRep.IsTraceLimit.polyKillsAt` (Lib/PadicHodge/Limit/TraceLimit.lean).

"$P$ kills $s$ at $A$" is `New.GaloisRep.PolyKillsAt`. When $\ell$ is a unit at $A$, it says $P(r(s)) = 0$. Above $\ell$, it says `New.Period.IsKilledBy` for every Weil pair: the restriction is potentially crystalline and $P$ kills the linearized Frobenius `New.Period.linearFrob`.

**Theorem (Local clauses at a trace limit).** Let $r$ be a trace limit along a nontrivial filter. Let the $\rho_{\eta, i}$ have jumps related by $R'$ to multisets $J'_{\eta, i}$. Assume that a number $n$ is related by $R$ to the multiplicity in $J$ whenever numbers $x_{\eta, i}$ are related by $R'$ to the multiplicities in $J'_{\eta, i}$ and $\sum_i a_{\eta, i} x_{\eta, i}$ tends to $n$. Then $r$ is good at $A$, the jumps of $r$ are related by $R$ to $J$, and the conclusion of the previous theorem holds for all $s$, $n$, $P$ and $Q$.

Lean: `New.GaloisRep.local_clauses_of_trace_limit` (Lib/PadicHodge/Limit/TraceLimit.lean).

*Proof.* The three clauses are `isGoodAt`, `jumpsRelAt` and `polyKillsAt`. $\square$

**Remark (Formalization).** The structure `IsTraceLimit` bundles its hypotheses. A user must prove all six fields, including non-degeneracy of the trace form and the alternative "finite or same jumps". The relations $R$ and $R'$ are arbitrary, so the theorem covers both exact jumps ($R$ is equality) and inclusion of jumps. Only the passage to limits is proved. The source does not prove local-global compatibility for automorphic Galois representations. It takes $r$ as given. In place of the Weil-Deligne representation the source uses `New.Period.linearFrob`, a chosen $B_{\max}$-linear endomorphism, and the monodromy operator does not enter.

**Example.** Let $I$ be a one-point type, let $r$ be continuous, good at $A$ and with non-degenerate trace form, let $\rho$ be $r$ as a matrix representation, and let $a = 1$. Then $r$ is a trace limit of $\rho$: property 3 holds since $I$ is finite, and the convergence is an equality. The theorems give back the local clauses of $r$. This case only tests the statements. In `Lib/GaloisRep/Main` the structure is used with families of representations attached to automorphic forms.
