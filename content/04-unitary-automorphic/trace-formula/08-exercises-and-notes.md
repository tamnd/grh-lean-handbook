---
title: Exercises and notes
lean:
  - Lib/Adelic/TraceFormula/TraceComparison.lean
  - Lib/Adelic/TraceFormula/LineStabiliser.lean
  - Lib/Adelic/TraceFormula/LineDeterminant.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $E$ be a CM field that contains a primitive $5040$-th root of unity. Show that $\varphi(5040) = 1152$, that $1152$ divides $[E : \mathbb{Q}]$, and that the number of infinite places of $E$ is divisible by $576$. Deduce that the hypothesis "the number of infinite places is even" in [the comparison of traces](/decl/New.trace_comparison/) and in [the main theorem](/decl/New.trace_eq_of_isCuspidalAt/) follows from the other hypotheses. Compare with Exercise 2 of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

*Hint.* $5040 = 2^4 \cdot 3^2 \cdot 5 \cdot 7$, so $\varphi(5040) = 8 \cdot 6 \cdot 4 \cdot 6$. The field $\mathbb{Q}(\zeta_{5040})$ lies in $E$. A CM field has no real places, so it has $[E : \mathbb{Q}]/2$ infinite places.

**Exercise 2.** Find where the hypothesis $N \geq 2$ is used in the proof of [the comparison of traces](/decl/New.trace_comparison/). Show that $13 N^3 \leq 10 N^5$ fails for $N = 1$. For $N = 1$, check the relation of [the theorem on $T^+ T^-$](/decl/New.lineRaise_lineLower/) directly: here $J = \mathcal{O}^\times$, and both sides act on $J$-fixed vectors as $\rho(\varpi)\rho(\varpi)^{-1} = 1$.

*Hint.* For $N = 1$ the right side is $q^{-1}(1 + (q - 1))$. The cut level is then the level itself.

**Exercise 3.** Let $k$ be a field of $q$ elements, $N \geq 2$, and $z \in k^N$ a vector that is not on the line of $e_i$. Show that exactly $q^{N-2}$ vectors $\xi \in k^N$ satisfy $\xi_i = 1$ and $\xi \cdot z = 1$. Show also that the index of the line stabiliser $J$ in $\mathrm{GL}_N(\mathcal{O})$ is $(q^N - 1)/(q - 1)$.

*Hint.* Write $\xi \cdot z = z_i + \sum_{j \neq i} \xi_j z_j$. Some $z_j$ with $j \neq i$ is nonzero, so the condition is one nontrivial affine equation in $N - 1$ unknowns. For the index, $\mathrm{GL}_N(\mathcal{O})$ acts transitively on the lines of $k^N$, and $J$ is the stabiliser of one line.

**Exercise 4.** Let $N = 2$, $i$ the first index, and $t = \operatorname{diag}(\varpi, 1)$. Show that the $q$ matrices $\begin{pmatrix} \varpi & a \\ 0 & 1 \end{pmatrix}$, $a$ running over lifts of $k$, represent the cosets in $J t J / J$. Show that each element of $J t J$ has reduction $\begin{pmatrix} 0 & * \\ 0 & u \end{pmatrix}$ with $u \neq 0$, and that its characteristic polynomial modulo $\varpi$ is $X(X - u)$. Conclude that $T^+$ is supported on elements with a simple zero, as in [the support theorem](/decl/New.lineHecke_pow_mem_spanOn/).

*Hint.* $J$ consists of the matrices that are upper triangular modulo $\varpi$. Multiply $t$ on both sides by such matrices and reduce.

**Exercise 5.** Let $A, T^+, T^-, e$ satisfy [the line relations](/decl/New.LineRelation/) on a finite-dimensional space $B$. Show that $A$ commutes with $e$. Show that $|\det T^+|^2 = d^{\dim B} (1 + c)^{\operatorname{rank} e}$. Give an example with $c = 0$ where two systems with the same traces of $A^{l+1} (T^+)^{j+1}$ have $e$ of different ranks.

*Hint.* $T^-$ is the adjoint of $T^+$, so $|\det T^+|^2 = \det(T^+ T^-)$. On the range of $e$ the operator $1 + c\, e$ is $1 + c$, and on the kernel it is $1$. For the example, take $B = \mathbb{C}$, $A = T^+ = T^- = 1$, $d = 1$, and compare $e = 0$ with $e = 1$.

## Notes and references

The comparison of simple trace formulas for inner forms of unitary groups that differ only at the real places is classical. The source cites Labesse, *Changement de base CM et séries discrètes* (2011), Theorems 5.4 and 5.5 and their proofs, and Arthur and Clozel, *Simple algebras, base change, and the advanced theory of the trace formula* (1989), Chapter 1, Lemmas 2.4 to 2.6. For the simple trace formula with a cuspidal component at one place, the source cites Harris and Labesse (2004), Proposition 1.10.5. `REFERENCES.md` of the source marks these three citations as compared, with the place confirmed. The source also cites Flicker and Kazhdan (1988) for the simple trace formula and Knightly and Li, *Traces of Hecke operators* (2006), for integrable test functions; it gives no place in these works.

The treatment here differs from the classical one in three ways. First, the test function at infinity is not a pseudo-coefficient but the kernel $e_\lambda$, which is integrable and idempotent, and a cusp kernel under the gap condition. Second, there is no truncation and no endoscopy. Cuspidality at a split place kills the non-elliptic terms (Section 4), and the Selberg principle kills the irreducible terms with roots off the unit circle (Section 5). Third, the hypothesis that $E$ contains a primitive $5040$-th root of unity replaces the local analysis of the classical proofs at several points: in Landherr's theorem, in the change of signs, and in the choice of a split auxiliary place.

For the character of the discrete series on the compact Cartan subgroup, and so for the elliptic orbital integrals of Section 6, the source cites Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966), Theorem 16, with part I, Acta Math. 113 (1965), Theorem 3, and Knapp, *Representation theory of semisimple groups* (1986), Theorem 12.7. For the Selberg principle, the source cites Harish-Chandra, *Discrete series II*, Theorem 11, Blanc and Brylinski (1992), and Hochs and Wang (2019), Corollary 4.8. `REFERENCES.md` does not mark these as compared. The source proves the form that it uses, for $U(p, q)$ and for its kernels, in [the discrete series](/chapter/discrete-series/).

The relation $T^+ T^- = q^{N-2}(1 + (q^N - 1) e_{\mathrm{sph}})$ is a relation in the Hecke algebra of a parahoric subgroup of $\mathrm{GL}_N$. The source proves it by a direct count of cosets, as in Section 7, and gives no reference. The use of a line stabiliser at an auxiliary place to force the simple zero, and the recovery of the trace on spherical vectors from the determinant of $T^+$, are specific to the source. The source claims that the comparison of traces holds as stated; this chapter explains the argument, and Lean accepts it, if the reported checks hold.

Two points of the plan are confirmed here. Finding F-140, that the parity hypothesis is redundant, holds, by Exercise 1. The hypothesis that $a$ lies in the universal level algebra is needed only in the main theorem.

Status: drafted by a model. No person has checked this chapter against the Lean source.
