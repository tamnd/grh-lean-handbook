---
title: Exercises and notes
lean:
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
decls:
  - New.FrobeniusCycle.elementary_divisors
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $O$ be a discrete valuation ring with uniformizer $\varpi$ and $y = \mathrm{diag}(\varpi^{e_1}, \dots, \varpi^{e_d})$ on $O^d$. Show that the length of $O^d/(yO^d + \varpi^mO^d)$ is $\sum_i \min(e_i, m)$. Deduce that a bound $(3c + \theta m)d$ for all $m$ means: at most about $\theta d$ of the $e_i$ are large, and the others have mean at most about $3c$.

*Hint.* The quotient is a direct sum. For the second part, let $m$ grow and count the $i$ with $e_i \ge m$.

**Exercise 2.** Show that $\mathrm{ColengthDvd}(M, N, z)$ and $\mathrm{ColengthDvd}(N, P, z')$ imply $\mathrm{ColengthDvd}(M, P, zz')$, from the definition in Section 1.

*Hint.* Combine a family by $m$ into $N$, then the results by $m'$ into $P$. The product matrix is $m'm$.

**Exercise 3.** In the theorem on few generators of Section 8, take $E$ with one element, $X \times I$ with one element, $Q = R = 1$, $B = 1$ and $A = a + u$. Find $U$, $t$ and $s$, and check the count $|E| + |s| \le |X|\dim S$ when $S$ is the residue field. Why is $S = 0$ not possible here?

*Hint.* Here $B - QRB = 0$, so $t = 0$ and $J$ is empty. The image of $Q$ lies in $C$, so $u \cdot 1 \in C$.

**Exercise 4.** Let $w \in \mathfrak m$ and $a\,O^E \subseteq G + aw\,O^E$. Give a direct proof that $a\,O^E \subseteq G$ when $a$ is not a zero divisor, by Nakayama's lemma applied to $(a\,O^E + G)/G$.

*Hint.* The module $(aO^E + G)/G$ is finitely generated and equals $w$ times itself.

**Exercise 5.** Check the bound of the factored operator in the trivial case $\theta$ close to $0$: if $s$ is empty, the chain lemma with $z = 0$ shows that the colength of the image of $\mathcal A$ itself divides $p^{|V|\Delta + 2Nc_0|V||\mathrm{Exp}|}$. Why can the theorem not take $s$ empty in general?

*Hint.* The dimension of $S$ times the index exceeds $|\mathrm{Exp}|$ by up to $\theta|\mathrm{Exp}|$, and only the count bounds $|s|$.

**Exercise 6.** Verify the identity $\mathrm{pairingMap}(u, b, Q'd') = d'^{\mathsf T}\,\mathrm{pairingMap}(u, b, Q')$ used in Section 8, and explain why the two ends of the chain contribute $\det d'$ and $\det d$ and not their squares.

*Hint.* Transpose a product. Each end is one inclusion of lattices.

## Notes and references

The chapter follows the file New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean and the files it imports in the same folder. The plan of the proof is in Section 1, and its use is in [the divisibility chapter](/chapter/divisibility/). The size of the operator, which this chapter does not need, is in [the archimedean size](/chapter/archimedean-size/), and the gain from short columns is in [short columns gain](/chapter/short-columns-gain/).

Nakayama's lemma in the form used in Section 8 is Corollary 2.7 of M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, 1969. Elementary divisors over rings that are not noetherian, in particular over valuation rings, go back to I. Kaplansky, *Elementary divisors and modules*, Trans. Amer. Math. Soc. 66 (1949), 464 to 491. The polynomial method behind the root lemma of Section 5 is that of Stepanov, in the form of E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*, Séminaire Bourbaki, exposé 430, 1973.

The colength $\mathrm{ColengthDvd}$ replaces the length because $O$ need not be discrete. It needs no inclusion of the two modules and no bases. Over a discrete valuation ring it gives the length bound of the corollary in Section 8. The constants are explicit: $c_{\mathrm{div}} = Nn(1/P^{2r} + r^2/(kP))$ and the precision $c = 5Nc_0$. The theorem is a statement about one Hecke operator. It says nothing about the eigenvalues of the operator, and it does not by itself give Theorem A.
