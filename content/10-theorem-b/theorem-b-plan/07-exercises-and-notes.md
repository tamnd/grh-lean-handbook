---
title: Exercises
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/Unfolding/AmplitudeSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Prove the integral of the unfolding in the model case: for $m \geq 1$ and $k \geq 4$, $\int_0^\infty e^{-4\pi m y}\, y^{k - 2}\, dy = \Gamma(k - 1)(4\pi m)^{1 - k}$. Then show that $\langle f, P_m\rangle = 0$ for all $m \geq 1$ implies $f = 0$.

*Hint.* Substitute $t = 4\pi m y$. For the second part, use that $\Gamma(k - 1)(4\pi m)^{1 - k} \neq 0$ and that a cusp form with all Fourier coefficients $0$ is $0$.

**Exercise 2.** In the model case, let $L = \lfloor (k - 1)/(4\pi e)\rfloor$. Compute $L$ and $\dim S_k$ for $k = 12$, $100$ and $1000$. For which of these $k$ does the bound of the section on the model case give a nonzero almost orthonormal block?

*Hint.* Use the formula for $\dim S_k$ from Serre, Chapter VII, §3, and $4\pi e \approx 34.16$. For $k = 12$ the block is empty.

**Exercise 3.** Let $G$ be a finite group with an irreducible unitary representation $\rho$ on $V$. Let $B$ be an isometry from a space $S$ into $V$. Prove that

$$\sum_{s \in G}\|B^*\rho(s)B\|^2 = \frac{\#G\,(\dim S)^2}{\dim V},$$

where the norm is the Hilbert-Schmidt norm. Compare this with the moment hypothesis of [Theorem](/decl/New.isSpread_of_second_moment/) for $\varepsilon = 0$.

*Hint.* Write $\|B^*\rho(s)B\|^2 = \sum_{i, j}|\langle\rho(s)Be_j, Be_i\rangle|^2$ for an orthonormal basis $e_i$ of $S$. Apply the orthogonality relations of Schur to each pair $(i, j)$.

**Exercise 4.** Let $\varepsilon = (8b^2)^{-1}$. Show that $5b^{-4} \leq \varepsilon$ if and only if $b^2 \geq 40$, and that $9b^{-4} \leq \varepsilon$ if and only if $b^2 \geq 72$. Then show that $16\varepsilon = 2/b^2$, and explain how the two losses $16\varepsilon$ and $2/b^2$ in the proof of Theorem B give the share $1 - 4/b^2$.

*Hint.* Multiply through by $8b^4$. The second loss is the bound for the share of the ramified forms in [the section on Theorem B](/chapter/theorem-b-plan/#theorem-b-and-its-input).

**Exercise 5.** In Lean, let $a_n = (-1)^n$ for $n \in \mathbb{N}$. Show that the family is not summable in $\mathbb{R}$, so its sum `tsum` is $0$, and that the statement $\sum_n a_n \leq 0$ is then true. Which theorem of the source rules out this effect for the amplitude sums? Which hypothesis does that theorem need, and where does the source prove it for the data $D$?

*Hint.* See [the section on conventions](/chapter/theorem-b-plan/#conventions-that-change-the-meaning). The hypothesis is the class of standing hypotheses.

**Exercise 6.** One field of the standing hypotheses says $(N^k/b)^f \leq [H : K]$ for a relative index $[H : K]$, and Lean gives the relative index the value $0$ when it is infinite. Show that the field implies that the index is finite.

*Hint.* $N \geq 5$ and $b \geq 1000$ give $(N^k/b)^f > 0$.

## Notes and references

The spanning theorem of Petersson, in the form of Section 2, is in H. Petersson, *Über die Entwicklungskoeffizienten der automorphen Formen*, Acta Mathematica 58 (1932). The Petersson formula in the normalization of Section 2 is Proposition 14.5 of H. Iwaniec and E. Kowalski, *Analytic Number Theory*, American Mathematical Society Colloquium Publications 53 (2004). The dimension of $S_k$ for $\mathrm{SL}_2(\mathbb{Z})$ is in J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Chapter VII, §3. The bound for $J_\nu$ is equation 10.14.4 of the NIST Digital Library of Mathematical Functions.

The source names related work in the files of this volume. For the spanning theorem it names Petersson (1932), Benedetto and Fickus, *Finite normalized tight frames* (2003), for the link between the least second moment and tight frames, and Muić, *Spectral decomposition of compactly supported Poincaré series and existence of cusp forms* (2010). For few translates it names Welch (1974) for rank bounds from second moments, and Wolsey (1982), on the greedy algorithm for the submodular set covering problem, for greedy covering with a logarithmic loss. For the Bessel functions it names, among others, Baruch on Bessel distributions on the open cell, Miličić (1977) on the decay of matrix coefficients of the discrete series, and Wallach, *Real Reductive Groups II* (1992). This book has not compared these citations with the statements of the source.

The four layers and their order follow the source. The statements in this chapter are those of Lean, read in the conventions of Section 5. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument proves Theorem B in the sense of a refereed proof, and it does not claim that the Generalized Riemann Hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
