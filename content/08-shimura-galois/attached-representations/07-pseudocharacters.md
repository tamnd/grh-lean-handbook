---
title: Representations from traces
lean:
  - Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean
  - Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean
decls:
  - New.HasSemiprimeSpan
  - New.exists_wedderburn
  - New.IsTraceNondeg.hasSemiprimeSpan
  - New.IsTraceNondeg.exists_conj_of_trace_eq
  - New.IsTraceNondeg.comp
  - New.IsTraceNondeg.continuous_of_trace
  - New.twistByChar
  - New.IsTraceNondeg.twist
  - New.IsTraceNondeg.exists_cancel_chars
  - New.newtonPoly
  - New.eval_newtonPoly
  - New.exists_rep_of_trace_identities
  - New.uniformClosure
  - New.mem_uniformClosure
  - New.IsApproximatingMonoid
  - New.exists_isApproximatingMonoid_of_mem_uniformClosure
  - New.GaloisRep.exists_continuous_isTraceNondeg_of_tendsto_trace
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Representations from traces

Section 4 defines "attached" through traces and the non-degenerate trace form. This section gives the tools with which the source works with that notion. There are three groups. First, two representations with a non-degenerate trace form and equal traces are conjugate (Brauer-Nesbitt). Second, a function that satisfies all trace identities is a trace (a weak form of the theorem of Procesi and Taylor). Third, a limit of traces is again a trace. The third result is the one with which [Building the representations](/chapter/building-representations/) makes an attached representation from a congruence limit.

Throughout, $k$ is a field, $G$ is a group, $n$ is a finite set, and $r : G \to \mathrm{GL}_n(k)$ is a homomorphism. Recall from Section 4 that $r$ has a *non-degenerate trace form* (Lean `New.IsTraceNondeg`) if every $x$ in the $k$-span of $r(G)$ with $\mathrm{tr}(x\, r(g)) = 0$ for all $g$ is $0$. Over a field of characteristic $0$ this holds if and only if $r$ is semisimple (Section 4).

### Semiprime spans and Wedderburn

**Definition (Semiprime span).** A homomorphism $\rho : G \to B$ into a $k$-algebra $B$ has *semiprime span* if every $x$ in the span of $\rho(G)$ with $x\, \rho(g)\, x = 0$ for all $g$ is $0$.

Lean: `New.HasSemiprimeSpan` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

The span $A$ of $\rho(G)$ is a subalgebra, since $\rho$ is multiplicative. The condition says that $x A x = 0$ implies $x = 0$ for $x \in A$. That is, $A$ is a semiprime algebra. A finite-dimensional semiprime algebra has zero radical, so it is semisimple.

**Lemma.** If $r$ has a non-degenerate trace form, then $r$ has semiprime span.

Lean: `New.IsTraceNondeg.hasSemiprimeSpan` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

*Proof.* Let $x$ be in the span and $x\, r(g)\, x = 0$ for all $g$. Then $(x\, r(g))^2 = 0$, so $x\, r(g)$ is nilpotent and $\mathrm{tr}(x\, r(g)) = 0$. By non-degeneracy, $x = 0$. $\square$

**Theorem (Wedderburn, in the form used).** Let $k$ be algebraically closed of characteristic $0$, let $B$ be a finite-dimensional $k$-algebra, let $\rho : G \to B$ have semiprime span, and let $f : H \to G$ be a homomorphism with normal range. Then there are natural numbers $d_1, \ldots, d_b$, a homomorphism $s : H \to \prod_i M_{d_i}(k)$ whose image spans the product, and an algebra map $F : \prod_i M_{d_i}(k) \to B$ with $F(s(h)) = \rho(f(h))$ for all $h$ and $F(E_i) \neq 0$ for each $i$, where $E_i$ is the matrix unit $e_{00}$ in factor $i$.

Lean: `New.exists_wedderburn` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

For $f$ the identity, this is the Wedderburn theorem for the semisimple algebra spanned by $\rho(G)$, over an algebraically closed field. The normal range is the part due to Clifford: the span of $\rho(f(H))$ is again semiprime, since conjugation by $\rho(G)$ keeps it, and its radical is then a nilpotent ideal stable under conjugation.

**Lemma (Clifford).** Let $k$ be algebraically closed of characteristic $0$. If $r$ has a non-degenerate trace form and $f : H \to G$ has normal range, then $r \circ f$ has a non-degenerate trace form.

Lean: `New.IsTraceNondeg.comp` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

The textbook form is Clifford's theorem: the restriction of a semisimple representation to a normal subgroup is semisimple. The source uses this lemma in `Lib/GaloisRep/Main/OddRank.lean`, to restrict to the kernel of a character.

### Equal traces give conjugate representations

The textbook form for finite groups is Serre, *Linear Representations of Finite Groups*, Section 2.3, Theorem 4, Corollary 2: two representations of a finite group over $\mathbb{C}$ with the same character are isomorphic. For semisimple representations of any group over a field of characteristic $0$, the same holds; this is the theorem of Brauer and Nesbitt in characteristic $0$.

**Theorem (Brauer-Nesbitt).** Let $k$ be algebraically closed of characteristic $0$. Let $r : G \to \mathrm{GL}_n(k)$ have a non-degenerate trace form, let $\rho : G \to B$ have semiprime span in a finite-dimensional algebra $B$, and let $\varphi : B \to M_n(k)$ be an algebra map. If $\mathrm{tr}\, r(g) = \mathrm{tr}\, \varphi(\rho(g))$ for all $g$, then there is $P \in \mathrm{GL}_n(k)$ with $r(g) P = P \varphi(\rho(g))$ for all $g$.

Lean: `New.IsTraceNondeg.exists_conj_of_trace_eq` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

*Proof.* The pair $g \mapsto (r(g), \rho(g))$ maps $G$ to $M_n(k) \times B$. Its span is semiprime: the span lies in the product of the two spans, and a product of semiprime spans is semiprime, componentwise. Wedderburn gives $s : G \to \prod_i M_{d_i}(k)$ with spanning image and $F$ with $F(s(g)) = (r(g), \rho(g))$. Let $F_1$ be the first component of $F$, and $F_2 = \varphi \circ (\text{second component of } F)$. Then $\mathrm{tr} \circ F_1$ and $\mathrm{tr} \circ F_2$ are linear and agree on $s(G)$, which spans, so they agree everywhere. Each $E_i$ is idempotent, so $F_1(E_i)$ and $F_2(E_i)$ are idempotent matrices. The trace of an idempotent matrix is its rank. So $F_1(E_i)$ and $F_2(E_i)$ have the same rank. Two algebra maps from $\prod_i M_{d_i}(k)$ to $M_n(k)$ that agree on the ranks of the $F(E_i)$ are conjugate, by the structure of modules over a product of matrix algebras. The conjugating matrix is $P$. $\square$

**Remark (Formalization).** The theorem asks for a non-degenerate trace form on one side only. The other side needs only a semiprime span, and $B$ may be any finite-dimensional algebra. The theorem says nothing about the uniqueness of $P$. The source uses it in `Lib/GaloisRep/Main/OddRank.lean` and in two files under `New/Congruences/`.

### Continuity from the trace

**Lemma.** Let $k$ be a topological field, let $G$ be a topological group, and let $r$ have a non-degenerate trace form. If $g \mapsto \mathrm{tr}\, r(g)$ is continuous, then $r$ is continuous.

Lean: `New.IsTraceNondeg.continuous_of_trace` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

*Proof.* Let $S$ be the span of $r(G)$. It is finite-dimensional. By non-degeneracy, the bilinear form $(x, y) \mapsto \mathrm{tr}(xy)$ on $S$ is non-degenerate, so every linear form on $S$ is $x \mapsto \mathrm{tr}(x y)$ for some $y \in S$. Write $y = \sum_j c_j r(g_j)$. Each matrix entry is a linear form on $S$, so the entry of $r(g)$ is $\sum_j c_j \mathrm{tr}(r(g) r(g_j)) = \sum_j c_j \mathrm{tr}\, r(g g_j)$. This is continuous in $g$, since right translation is continuous. $\square$

**Remark (Formalization).** The lemma needs no algebraic closure and no hypothesis on the characteristic. Continuity is condition 1 of the definition of "attached" in Section 4. The lemma is how the source proves that condition for a representation made from traces: the trace is continuous, so the representation is continuous. Finding F-054 of the [register of findings](/chapter/register-of-findings/) is about `GalRep` of Section 5, which has no continuity clause; the lemma does not apply there, since `GalRep` does not ask for a non-degenerate trace form.

### Twists and cancellation of characters

**Definition (Twist).** For a character $\mu : G \to k^\times$, the twist of $R : G \to \mathrm{GL}_m(k)$ is $g \mapsto \mu(g) R(g)$.

Lean: `New.twistByChar` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

**Lemma.** If $R$ has a non-degenerate trace form, so has its twist by $\mu$.

Lean: `New.IsTraceNondeg.twist` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

*Proof.* Each $\mu(g) R(g)$ is in the span of $R(G)$, so the span of the twist is in the span of $R(G)$. If $\mathrm{tr}(x \mu(g) R(g)) = 0$ for all $g$, then $\mathrm{tr}(x R(g)) = 0$, since $\mu(g) \neq 0$. So $x = 0$. $\square$

**Theorem (Cancellation of characters).** Let $k$ be algebraically closed of characteristic $0$, and let $m$, $n$, $t$ be finite sets with $|m| = |n| + |t|$. Let $r_0, r_1 : G \to \mathrm{GL}_m(k)$ have non-degenerate trace forms, and let $\psi_{i,j}$ for $i \in \{0, 1\}$ and $j \in t$ be characters of $G$ with $\psi_{0,j} \neq \psi_{1,j'}$ for all $j, j'$. Let $T : G \to k$ satisfy
$$\mathrm{tr}\, r_i(g) = T(g) + \sum_{j \in t} \psi_{i,j}(g)$$
for $i = 0, 1$ and all $g$. Then there is $s : G \to \mathrm{GL}_n(k)$ with a non-degenerate trace form and $T = \mathrm{tr}\, s$.

Lean: `New.IsTraceNondeg.exists_cancel_chars` (Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean).

*Proof.* Let $\rho(g) = (r_i(g), (\psi_{i,j}(g))_j)_{i = 0, 1}$. Its span is semiprime: on the matrix components by the lemma above, and on the character components by $g = 1$, since $x^2 = 0$ implies $x = 0$ in $k$. Wedderburn gives $s : G \to \prod_c M_{d_c}(k)$ with spanning image and $F$ with $F \circ s = \rho$. For $i = 0, 1$ let $\tau_i(y)$ be the trace of the matrix component $i$ of $F(y)$ minus the sum of its character components. On $s(G)$ both $\tau_0$ and $\tau_1$ equal $T$, so $\tau_0 = \tau_1$. Also $\tau_0(xy) = \tau_0(yx)$ and $\tau_0(1) = |m| - |t| = |n|$. Fix a factor $c$ and suppose that $\tau_0(E_c)$ is not a natural number. If no character component $i$ of $F(E_c)$ were nonzero, then $\tau_i(E_c)$ would be the trace of an idempotent matrix, a natural number. So for each $i$ some $\psi_{i,j_i}$ is nonzero on $E_c$. From $E_c\, s(g)\, E_c = s(g)_{c,00} E_c$ it follows that $\psi_{i,j_i}(g) = s(g)_{c,00}$ for $i = 0$ and $i = 1$. Then $\psi_{0,j_0} = \psi_{1,j_1}$, which the hypothesis excludes. So each $\tau_0(E_c)$ is a natural number, and `New.exists_rep_of_trace` (step 8 of the proof below) gives $s$. $\square$

The textbook form is the uniqueness of the decomposition of a semisimple representation into simple ones. The source uses the theorem in `Lib/GaloisRep/Main/AllRanks.lean`.

### All trace identities

Taylor (Duke Math. J. 63 (1991), Theorem 1) and Rouquier (J. Algebra 180 (1996)) show that a pseudo-representation of dimension $d$ over an algebraically closed field of characteristic $0$ is the trace of a semisimple representation, unique up to conjugacy. A pseudo-representation is a central function $T$ with $T(1) = d$ that satisfies one identity of degree $d + 1$, the Frobenius identity. That the Frobenius identity implies all other trace identities is the theorem of Procesi in invariant theory. The source avoids this step: it asks for all identities.

**Definition (Newton polynomials).** The polynomials $N_{j,m}$ in variables $X_0, X_1, \ldots$ over $k$ are defined by $N_{0,m} = 1$ and
$$N_{j+1,m} = X_m N_{j,1} - j N_{j,m+1}.$$

Lean: `New.newtonPoly` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

**Lemma (Newton's identities).** For a finite multiset $S$ in $k$, put $p_m = \sum_{a \in S} a^m$. Then $N_{j,1}(p) = j!\, e_j(S)$, where $e_j$ is the $j$-th elementary symmetric function.

Lean: `New.eval_newtonPoly` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

For the eigenvalues $S$ of an $n \times n$ matrix $x$, $p_m = \mathrm{tr}(x^m)$ and $e_{|n|+1}(S) = 0$. So $N_{|n|+1,1}(\mathrm{tr}\, x^0, \mathrm{tr}\, x, \mathrm{tr}\, x^2, \ldots) = 0$ for every $x$. This is one trace identity.

**Theorem (Procesi and Taylor, weak form).** Let $k$ be algebraically closed of characteristic $0$, and let $T : G \to k$. Suppose that every polynomial $B$ in variables indexed by $G$ that vanishes at $(\mathrm{tr}\, x(g))_g$ for every homomorphism $x : G \to \mathrm{GL}_n(k)$ also vanishes at $(T(g))_g$. Then there is $r : G \to \mathrm{GL}_n(k)$ with a non-degenerate trace form and $\mathrm{tr}\, r(g) = T(g)$ for all $g$.

Lean: `New.exists_rep_of_trace_identities` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

*Proof.* Extend $T$ linearly to a linear form $t$ on the group algebra $k[G]$. The identities pass from $G$ to $k[G]$, since a polynomial in the values on $k[G]$ is a polynomial in the values on $G$.

1. The identity $X_{xy} - X_{yx}$ holds for traces of matrices, so $t(xy) = t(yx)$.
2. Let $I$ be the set of $x$ with $t(xy) = 0$ for all $y$. It is a two-sided ideal, by step 1. Let $\tau$ be the form induced by $t$ on $A = k[G]/I$.
3. Let $x \in A$ and $l \in k$ with $x^{m+1} = l^m x$ for all $m$. The Newton polynomial of degree $|n| + 1$ is a trace identity. Evaluated at the powers of $x$, it is $\prod_{i \leq |n|} (\tau(x) - i l)$, up to a nonzero factor. So $\tau(x) = j l$ for a natural number $j$.
4. The quotient $A$ is finite-dimensional. A determinant identity of trace values in $|n|^2 + 1$ elements shows that any $|n|^2 + 1$ elements of $A$ are linearly dependent modulo $I$.
5. The algebra $A$ is semiprime. If $x g x = 0$ for all $g$, then $(x g)^2 = 0$ for all $g$. Step 3 with $l = 0$ gives $\tau(xg) = 0$, so $x \in I$, so $x = 0$ in $A$.
6. Wedderburn, applied to $G \to A$, gives $s : G \to \prod_i M_{d_i}(k)$ with spanning image and an algebra map $F$ to $A$ with $F \circ s$ the map $G \to A$.
7. Each $F(E_i)$ is idempotent, so step 3 with $l = 1$ makes $\tau(F(E_i))$ a natural number $c_i$. Also $\tau(1) = T(1) = |n|$, by the identity $X_1 - |n|$.
8. A linear form $\tau'$ on $\prod_i M_{d_i}(k)$ with $\tau'(xy) = \tau'(yx)$ is $\sum_i \tau'(E_i) \mathrm{tr}_i$. Apply this to $\tau' = \tau \circ F$ (Lean `New.exists_rep_of_trace`). So $\tau \circ F \circ s$ is the trace of the representation with $c_i$ copies of the $i$-th factor. Its dimension is $\sum_i c_i d_i = \tau(1) = |n|$, and its trace form is non-degenerate since its span is the product of the factors that occur. $\square$

**Remark (Formalization).** The hypothesis "every identity" is a universal statement over all polynomials in infinitely many variables. In the textbook it is a theorem that one identity suffices. The source does not prove this, and it does not need it: in every application $T$ is a limit of traces, and a limit of functions that satisfy an identity satisfies it. The theorem gives existence; uniqueness up to conjugacy is the Brauer-Nesbitt theorem above. The source also uses this theorem in `Lib/GaloisRep/Main/CuspidalTypes.lean`.

### Limits of traces

The source states the limit step of the congruence method in this abstract form.

**Definition (Uniform closure).** For a set $S$ of functions $\iota \to K$, with $K$ a normed field, the *uniform closure* of $S$ is the closure of the span of $S$ in the topology of uniform convergence. A function $f$ lies in it if and only if for every $\varepsilon > 0$ there is $g$ in the span of $S$ with $\lVert f(x) - g(x) \rVert \leq \varepsilon$ for all $x$.

Lean: `New.uniformClosure`, `New.mem_uniformClosure` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

**Definition (Approximating monoid).** Let $s(\eta) \in \mathbb{N}$ and $c_{\eta, i} \in K$ for $\eta > 0$ and $i < s(\eta)$. A submonoid $N$ of pairs $(t, \varphi)$, with $t \in K$ and $\varphi$ a family indexed by the pairs $(\eta, i)$, is *approximating* if it is closed and $\sum_i c_{\eta,i}\, \varphi(\eta, i) \to t$ as $\eta \to 0$, uniformly over $(t, \varphi) \in N$.

Lean: `New.IsApproximatingMonoid` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

**Lemma.** Let $f \neq 0$ be in the uniform closure of $S$. Then there are $s$, $c$, an approximating monoid $N$, and functions $y(\eta, i) \in S$, with this property: if a linear operator that does not increase the sup norm has $f$ as eigenfunction with eigenvalue $t$ and each $y(\eta, i)$ as eigenfunction with eigenvalue $\varphi(\eta, i)$, then $(t, \varphi) \in N$.

Lean: `New.exists_isApproximatingMonoid_of_mem_uniformClosure` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

In `Lib/GaloisRep/Main/SplitCase.lean`, $f$ is a $p$-adic model of an eigenform and the operators are Hecke operators. The hypothesis $f \neq 0$ is needed to read off $t$ from $Tf = tf$.

**Theorem (A limit of traces is a trace).** Let $K$ be an algebraically closed normed field of characteristic $0$, let $G$ be a topological group, and let $N$ be an approximating monoid. For each $g \in G$ let $\mathcal{F}_g$ be a non-trivial filter on $N$. Let $L \subseteq K$ be complete, let $t \in L$ for most $(t, \varphi)$ along each $\mathcal{F}_g$, and let $r_x : G \to \mathrm{GL}_n(K)$ be continuous for each index $x = (\eta, i)$. Suppose that $\varphi(x) \to \mathrm{tr}\, r_x(g)$ along $\mathcal{F}_g$ for all $g$ and $x$. Then there is a continuous $R : G \to \mathrm{GL}_n(K)$ with a non-degenerate trace form such that $(\mathrm{tr}\, R(g), (\mathrm{tr}\, r_x(g))_x) \in N$ for all $g$.

Lean: `New.GaloisRep.exists_continuous_isTraceNondeg_of_tendsto_trace` (Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean).

*Proof.* Fix $g$.

1. For each $\eta$ the finite sum $\sum_i c_{\eta,i} \varphi(\eta, i)$ converges along $\mathcal{F}_g$. The sums tend to $t$ uniformly on $N$. So the first components $t$ form a Cauchy filter. They lie eventually in the complete set $L$, so they have a limit $T(g)$.
2. The pair $(T(g), (\mathrm{tr}\, r_x(g))_x)$ is a limit of points of $N$ along $\mathcal{F}_g$, and $N$ is closed. So it lies in $N$.
3. By step 2 and the uniform convergence, $T$ is a uniform limit of the functions $g \mapsto \sum_i c_{\eta,i} \mathrm{tr}\, r_{(\eta,i)}(g)$. These are continuous, so $T$ is continuous.
4. Let $D$ be a trace identity for dimension $n$. The approximation of the definition also holds after evaluation of $D$: the sums $\sum_i c_{\eta,i}\, D\bigl((\mathrm{tr}\, r_{(\eta,i)}(g))_g\bigr)$ tend to $D(T)$ (Lean `New.IsApproximatingMonoid.tendstoUniformly_eval`; this uses that $N$ is a monoid). Each term is $0$, since $D$ vanishes on the traces of $r_{(\eta,i)}$. So $D(T) = 0$.
5. The weak Procesi and Taylor theorem gives $R$ with a non-degenerate trace form and trace $T$. By the continuity lemma above, $R$ is continuous. $\square$

**Remark (Formalization).** The limit $T(g)$ is obtained by `choose` from the Cauchy property, and $R$ by `choose` from the existence theorem. So $R$ is determined only up to conjugacy, and only its trace is determined. The non-triviality of each $\mathcal{F}_g$ is a hypothesis. The theorem says nothing about local conditions. The source uses it once, in `Lib/GaloisRep/Main/SplitCase.lean`, line 176, and the matching lemma on approximating monoids at line 638 of the same file. The proof that the result is attached in the sense of Section 4 is in [Building the representations](/chapter/building-representations/).

