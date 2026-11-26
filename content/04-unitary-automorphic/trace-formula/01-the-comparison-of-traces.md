---
title: The comparison of traces
lean:
  - Lib/Adelic/TraceFormula/CuspidalComparison.lean
  - Lib/Adelic/TraceFormula/TraceComparison.lean
decls:
  - New.trace_eq_of_isCuspidalAt
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The comparison of traces

This chapter proves one theorem. Two hermitian spaces $V$ and $V'$ of the same rank $N \geq 2$ over a CM field $E$ can have different signatures at the infinite places. One of them can be definite and the other indefinite. The theorem says that a Hecke operator of a fixed level has the same trace on the forms of a fixed type on $V$ and on $V'$, if the test function is cuspidal at one split place and the type is a discrete series with a large gap. The proof is a simple trace formula of the kind of Flicker and Kazhdan, with no truncation and no endoscopy. This section states the theorem, says where it sits in the argument and what it uses, and gives a sketch of the proof.

### Where the theorem sits

[The plan](/chapter/theorem-and-plan/) reduces the Generalized Riemann Hypothesis, as the source claims, to a main inequality, and the main inequality to three theorems A, B and C on one lattice of automorphic forms. [Theorem B](/chapter/theorem-b-plan/) needs the dimension of a space of forms on a unitary group of an indefinite hermitian space, or at least the multiplicity of a Hecke eigensystem in it. On a definite space the real group is compact and the multiplicities can be counted. The comparison of traces moves the count from the indefinite space to a definite one. The argument uses the comparison only through the theorem below, in [equal multiplicities](/chapter/equal-multiplicities/).

### The objects

We fix the notation of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). The field $E$ is a CM field with totally real subfield $F$. It satisfies the standing condition: it contains a primitive $5040$th root of unity. The index set $n$ has $N$ elements. A *space* $V = (J, x)$ with signs $s \in \{\pm 1\}^n$ is a matrix $J$ over $E$ and an adelic frame $x$ in which the form $J$ is the identity at every finite place and $\varepsilon_s = \operatorname{diag}(s)$ at every infinite place. The adelic group is $G = G_\infty \times G_f$. Here $G_\infty = \prod_{v} U(\varepsilon_s)$, a product over the infinite places $v$ of $E$ of copies of the real group $U(p, q)$ with $p$ and $q$ the numbers of signs $+1$ and $-1$. The group $G_f$ is the unitary group of the identity form over the finite adeles. The rational points of $U(J)$ embed in $G$ through the frame, with image $\Gamma = \Gamma_V$.

A *level* is an open subgroup $K$ of $K_0 = G_f \cap \mathrm{GL}_N(\hat{\mathcal{O}}_E)$. Section 3 defines the forms of type $e$ and the space $\mathcal{A}(V, e)^K$ of those fixed by $K$. The group algebra $\mathbb{C}[G_f]$ acts too, and $a \in \mathbb{C}[G_f]$ keeps the $K$-fixed vectors of every representation exactly if $a$ lies in the *universal level algebra* of $K$. For a family $l = (l_v)$ of integer vectors indexed by the infinite places, $e_l = \prod_v e_{l_v}$ is the product of the discrete series kernels of [discrete series](/chapter/discrete-series/). The vector $l_v = 2\lambda_v$ is a doubled Harish-Chandra parameter. It has *gap* $h$ for the signs $s$ if its entries are distinct, each entry has the parity of $N - 1$, and $|\lambda_{v,i} - \lambda_{v,j}| \geq h$ whenever $s_i \neq s_j$. The theorem asks for the gap $500 N^3 + 10 N^5$.

Two more notions concern the finite part. For $a \in \mathbb{C}[G_f]$ and a level $K$, the *test function* $a \star 1_K$ is $\sum_b a(b)\, 1_{bK}$, a locally constant function of compact support on $G_f$. A test function is *cuspidal* at a split finite place $w$ if all its translates have sum zero over each coset of the unipotent radical of each proper parabolic subgroup of $\mathrm{GL}_N$ over the residue field at $w$. [Test functions](/chapter/trace-formula/#test-functions-and-cuspidality) gives the exact definition.

### The theorem

**Theorem (Comparison of traces).** Let $E$ be a CM field that contains a primitive $5040$th root of unity and has an even number of infinite places. Let $N \geq 2$ and let $V$ and $V'$ be spaces of rank $N$ over $E$ with signs $s$ and $s'$. Let $l$ be a family of integer vectors such that, at every infinite place $v$, the vector $l_v$ has gap $500 N^3 + 10 N^5$ for the signs $s$ and also for the signs $s'$. Let $K$ be a level, let $a$ lie in the universal level algebra of $K$, and let $w$ be a split finite place such that $a \star 1_K$ is cuspidal at $w$. Let $T$ be an endomorphism of $\mathcal{A}(V, e_l)^K$ and $T'$ an endomorphism of $\mathcal{A}(V', e_l)^K$ such that $T y = a \cdot y$ and $T' y' = a \cdot y'$ for all $y$ and $y'$. Then
$$\operatorname{tr}\big(T \mid \mathcal{A}(V, e_l)^K\big) = \operatorname{tr}\big(T' \mid \mathcal{A}(V', e_l)^K\big).$$
Lean: `New.trace_eq_of_isCuspidalAt` (Lib/Adelic/TraceFormula/CuspidalComparison.lean).

The proof is in [the line stabiliser](/chapter/trace-formula/#the-line-stabiliser-and-the-proof). It needs the rest of the chapter.

Three points of the statement need a comment. First, the traces are traces of endomorphisms of complex vector spaces. Both spaces are finite-dimensional, by the finite dimension theorem of [automorphic forms](/chapter/automorphic-forms/), and the proof uses this. Second, the hypothesis that the number of infinite places is even follows from the standing condition, as Exercise 2 of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) shows. Third, for a definite space the signs are all $+1$, so the gap condition for $V'$ asks only that the entries of $l_v$ are distinct and have the right parity.

**Remark (Formalization).** The trace in the statement is `LinearMap.trace` of Mathlib. It is defined on every module and it is $0$ on a module that is not finite and free. So a comparison of such traces could be empty. Here it is not: the first step of the proof, [Theorem](/decl/New.Space.volume_mul_trace_eq/), proves that $\mathcal{A}(V, e)^K$ is finite-dimensional for every cusp kernel $e$, through `New.Space.finite_levelSpace`, before it computes the trace. This answers the point that finding F-035 of the notes raises.

### What the chapter uses

The chapter uses the following results of other chapters.

1. The adelic groups, the spaces and Landherr's theorem, from [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).
2. The quotient measure on $\Gamma \backslash G$ and the finite volume, from [reduction theory](/chapter/reduction-theory/).
3. The forms of type $e$, the cusp kernels, their decay and the finite dimension of $\mathcal{A}(V, e)^K$, from [automorphic forms](/chapter/automorphic-forms/).
4. Harish-Chandra's formulas for the formal degree and for the elliptic orbital integrals of a discrete series kernel, from [discrete series](/chapter/discrete-series/).
5. The change of signs at the infinite places, which rests on class field theory (Section 6).

### A sketch of the proof

The proof has two parts. The first part is [Theorem](/decl/New.trace_comparison/). It asks for one more hypothesis: at a second finite place $w'$, every point $g$ of the support of $a \star 1_K$ has integral entries at $w'$, and $0$ is a simple root of the characteristic polynomial of $g_{w'}$ modulo $w'$. Under this hypothesis the proof runs as follows.

1. *The trace as an integral.* The trace of $a$ times $\operatorname{vol}(K)$ is the integral over $\Gamma \backslash G$ of the kernel $\sum_\gamma (e_l \otimes \varphi)(x^{-1} \gamma x)$, $\varphi = a \star 1_K$. The sum splits by the characteristic polynomial $R$ of $\gamma$ (Section 3).
2. *Reducible $R$.* The simple zero at $w'$ excludes proper powers, so $R$ has coprime factors. Cuspidality at $w$ kills the term of $R$ by a descent to a block diagonal subgroup (Section 4).
3. *Irreducible $R$ with a root off the unit circle.* The orbital integrals vanish by the Selberg principle for the idempotent $e_l$ (Section 5).
4. *Irreducible $R$ with all roots on the unit circle.* A change of signs matches the classes of $V$ with those of a definite space, and Harish-Chandra's formula evaluates the real factors. The result does not depend on $V$ (Section 6).

The second part removes the condition at $w'$ (Section 7). At an auxiliary split place $v$ the level is cut down to the stabiliser of a line. The positive powers of a Hecke operator $T^+$ have the simple zero at $v$ on their support, and a linear algebra lemma recovers the trace of $a$ at level $K$ from the traces of $a^{l+1} (T^+)^{m+1}$ at the smaller level.

