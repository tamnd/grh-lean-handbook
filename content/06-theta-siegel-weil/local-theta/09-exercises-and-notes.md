---
title: Exercises and notes
lean:
  - Lib/DiscreteSeries/Theta/LocalCorrespondence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $n = n' = 1$, with both signs $1$, and take the standard data with integers $\gamma$, $\gamma'$. Show that $l$ and $l'$ match exactly when $l$ and $l'$ are even, $\xi = l - 2\gamma + 1 > 0$ and $\xi' = -\xi$. Show that the joint harmonic is $X^w$ with $w = (\xi - 1)/2$, and that its column weight is $\Lambda' = \lambda'$.

*Hint.* For $n = 1$ the gap condition asks only for the parity of $n - 1$, and $\Lambda = \lambda$. The vacuum weight is $\gamma$. Use the formula $\xi' = l' - 2(\gamma' + 1) + 1$ for the column, and the column operator $-X\partial + \gamma'$ of Section 2.

**Exercise 2.** In the pair $U(1,1) \times U(1)$ of Section 3, with row 1 matched, show that $X_1^kX_2^m$ with $m > 0$ is not $K$-highest of weight $\Lambda$ for the row action. Conclude again that the joint harmonic is a multiple of $X_1^k$.

*Hint.* The operator $E_{22} = -X_2\partial_2 - 1 + \gamma$ gives the weight $\gamma - 1 - m$ on row 2.

**Exercise 3.** Check the identity $n^3 - n'^3 - (n - n')^3 = 3nn'(n - n')$, which ends the comparison of Casimir values in Section 6. Then check the lemma on sums of squares for $d = 3$: the values are $-2$, $0$, $2$.

*Hint.* Expand $(n - n')^3$. For $d = 3$ both sides are $24$.

**Exercise 4.** For one variable $X$, compute the Fischer inner products $\langle X^2, X^2\rangle$ and $\langle X, \partial X^2\rangle$, and check the adjointness lemma of Section 5 in this case.

*Hint.* Both numbers are $2$. In general $\langle X^a, X^a\rangle = a!$.

**Exercise 5.** Suppose that $c_\lambda$ is not square integrable. Then the formal degree is the junk value $0$ in Lean, and the kernel $e_\lambda$ is $0$. Show that the conclusion of the positivity theorem of Section 8 is then false. Conclude that the hypotheses of that theorem exclude this case, and name the hypothesis that does this.

*Hint.* The operator of the zero function is $0$, since the zero operator agrees with the integral. Matching gives the large gap.

**Exercise 6.** In Howe's argument, suppose that hypothesis 3 is dropped. Find the step of the proof that fails, and explain why the uniqueness theorem can then not be applied to $Q$.

*Hint.* Without hypothesis 3 the vector $Q$ need not have the row weight $\Lambda$, and a pre-joint harmonic has row weight $\Lambda$ by definition.

## Notes and references

The chapter follows Lib/DiscreteSeries/Theta in the source, at the pin of this book. The source proves the local results by explicit algebra in the Fock model and by the analytic theorems of [discrete series through one matrix coefficient](/chapter/discrete-series/). It does not prove Howe duality. In its place it proves the smoothing statement of Section 8 by Howe's argument of Section 7, and it proves the uniqueness of the joint harmonic of Section 5. The global use of these results is in [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). The construction of the oscillator pair is in [the Weil representation from a vacuum](/chapter/weil-representation/).

The textbook account of the theta correspondence for real unitary pairs uses these works, which the source cites.
1. R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989).
2. J.-S. Li, *Theta lifting for unitary representations with nonzero cohomology*, Duke Math. J. 61 (1990). Li describes the correspondence of discrete series in the stable range.
3. A. Paul, *First occurrence for the dual pairs* $(U(p,q), U(r,s))$, Canad. J. Math. 51 (1999). The source cites Theorem 2.7 for the block rule and Theorem 2.11 for the comparison of Casimir values.
4. M. Kashiwara and M. Vergne, *On the Segal-Shale-Weil representations and harmonic polynomials*, Invent. Math. 44 (1978). This is the classical account of harmonic polynomials in the Fock model.

For the Fock model and its analytic form, the source cites G. B. Folland, *Harmonic Analysis in Phase Space* (1989), chapters 1 and 4, M. G. Davidson, Pacific J. Math. 129 (1987), and H. Reiter, *Metaplectic Groups and Segal Algebras*, LNM 1382 (1989). The source works in an $L^1$ space of vacuum coefficients, not in the Hilbert Fock space (Section 8).

This book has not compared the cited places with the source. The identification of matching with the block rule is a theorem of the source (Section 3). The claim that the block rule is the correspondence of Li and Paul is a citation, not a theorem of the source.

The choices of the formalization (`Classical.epsilon`, `Function.invFun` and the junk formal degree $0$) are discussed in Sections 4, 5 and 8.

The source claims the results of this chapter. Lean accepts them, if the reported checks hold. This chapter does not claim that the proof of the main theorem is correct.

Status: drafted by a model. No person has checked this chapter against the Lean source.
