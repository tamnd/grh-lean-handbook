---
title: Exercises and notes
lean:
  - New/Determinant/Exchange/TheoremForPartners.lean
  - New/Determinant/Exchange/ExplicitMatching.lean
decls:
  - New.Exchange.exchange_identity
  - New.Rows.exists_stdClassSum_eq_mul_integral_modKernel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

These exercises use the exchange identity of Section 1 and the explicit form of Section 7.

Lean: `New.Exchange.exchange_identity` (New/Determinant/Exchange/TheoremForPartners.lean), `New.Rows.exists_stdClassSum_eq_mul_integral_modKernel` (New/Determinant/Exchange/ExplicitMatching.lean).

**Exercise 1.** Let $|n| = 6$, $\operatorname{neg}(s) = 2$ and $\mu_\tau = 1$ at every place. Check hypotheses 3 and 4 of the exchange identity. Then compute $k = |n|/2 - \operatorname{neg}(s)$ and the number of planes that the proof of the value of the equal rank ratio adds.

*Hint.* $2 \cdot 2 + 2 = 6$ and $6 \leq 2 + 4$. Then $k = 1$, and the induction adds $q = 2$ planes to $H \oplus J$ with $\operatorname{rk} J = 2$.

**Exercise 2.** Suppose that hypothesis 3 is weakened to $2\operatorname{neg}(s) \leq |n|$, and that $\mu_\tau \geq 1$ is assumed at every place. Go through the proof of the exchange theorem in Section 5 and find each place where hypothesis 3 is used. Show that the proof still works.

*Hint.* Hypothesis 3 gives $k$ as a natural number, which needs only $2q \leq |n|$. It gives the positive weight of $\mathfrak{c}$ through hypothesis 4; with $\mu_\tau \geq 1$ assumed, this use goes away.

**Exercise 3.** In the lemma "the identity used twice", show that $L_*(k)\,L_*(-k) = 1$ follows from the definition $L_*(e) = L(e^+)/L((-e)^+)$.

*Hint.* For $k \geq 0$, $L_*(k) = L(k)/L(0)$ and $L_*(-k) = L(0)/L(k)$, and $L(k) > 0$.

**Exercise 4.** Let $W$ have rank $2$ with signs $(1, -1)$, so $\operatorname{neg}(s) = 1$. Show that no $V$, $V'$ satisfy all hypotheses of the exchange identity. Then explain why the explicit exchange of Section 7 needs $s_0 \geq 1$.

*Hint.* Hypothesis 3 asks $2 + 2 \leq 2$. In Section 7, $|n| = 2|l| + 2s_0$ and $\operatorname{neg}(W) = |l|$, so hypothesis 3 is $s_0 \geq 1$.

**Exercise 5.** Let $C$ be the constant of the exchange theorem of Section 5, before the final step. Show that if one tame character exists, then $C > 0$. Explain why the exchange identity can still state $C > 0$ when no tame character exists.

*Hint.* $|c|^2 > 0$ and $L_{\mathfrak{m}}(\nu, e) > 0$. With no tame character the conclusion is a statement about the empty set, so any $C$ works, and the proof takes $C = 1$.

**Exercise 6.** In the lemma on row stabilizers of Section 6, let $c = \emptyset$, so that the condition $w\varphi(A) = w$ is empty. Describe $H$ and the datum $\Phi_0$.

*Hint.* $H$ is the group of invertible matrices that agree with $1$ off the columns $e$. Then $\mathrm{col}(\sigma) = \chi(\det\sigma_{e,\cdot})$ always.

**Exercise 7.** Show that the rank zero example of Section 7 is the case $b = \emptyset$ of the corollary there, and compute the constant $C$ in terms of $c'$ and the constant of the theorem.

*Hint.* The corollary sets $C = |c'|^2/C_0$, where $C_0$ is the constant of the theorem.

## Notes and references

**The statement.** The exchange identity says that theta integrals over $U(V)$ and $U(V')$ agree on matched ramified data, up to a nonzero constant $c$. The sizes are complementary: $\operatorname{rk} V + \operatorname{rk} V' = \operatorname{rk} W$. Only $|c|^2$ is given. It is a constant $C$, which is not computed, times the conductor factor and the partial L-values $|L^S(z, \nu)|^2$ for $z = 1, \ldots, e$. The constant $C$ does not depend on the tame character, and this is what [the plan](/chapter/theorem-c-plan/) uses. The proof does not show that the constant $c'$ of the explicit form is nonzero. The [register of findings](/chapter/register-of-findings/) lists such constants.

**The method.** The proof follows the docstring of the source file. It builds a large triple with Witt's theorem at the real places, removes hyperbolic planes one at a time with the constant term of [the tower](/chapter/rallis-inner-product/), and computes the equal rank ratio by applying the identity twice. The first term identity of the regularized Siegel-Weil formula plays the same role in the literature.

**Errors in the research notes.** Research note e §4.3 states hypothesis 3 with the margin $+2$, as the source does. The source proof uses this margin only for the positive weight of the split tame character. Note e also calls matched functions "roughly a partial Fourier transform". In the source the matching is a condition on supports and a factor $\chi(\det k)$, with no Fourier transform. Note e says that the explicit matching uses explicit polynomial vectors on both sides. It uses products of determinants on the real side, and the finite data $\Phi$, $\Psi$ remain arbitrary matched functions. Note e §5.2 says that the one exchange of Section 6 applies the identity three times. The three applications are in a later file of the source, and Section 6 gives one.

**Literature.** For theta lifts of characters between complementary groups, see Snitz, *Theta correspondence of automorphic characters*, J. Number Theory 122 (2007), and Erez, *Morphisms of global theta lifts of non-trivial automorphic characters of orthogonal groups* (2024). For the regularized Siegel-Weil formula, the second term identity and the Rallis inner product formula, see Gan, Qiu and Takeda (2014), after Kudla and Rallis (1994) and Ichino (2004). For harmonic polynomials and determinants, see Kashiwara and Vergne (1978) and Böcherer and Schulze-Pillot (1991).

**Dependencies.** No file of this chapter imports a file that the plan puts in a later chapter of this volume.
