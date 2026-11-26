---
title: Exercises and notes
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
  - New/Reduction/Lattices/Colength.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** In the standard twisted lattice with $V = \mathbb{C}$, let $y = 3/2$. Find the least $c$ such that $y$ has covolume at most $c$, and the least $\delta$ such that $y$ has index at most $\delta$. Show that $c + 2\delta = 2\log 3$. Do the same for $y = \sqrt 2/2$, and show that the inequality of Section 6 is an equality.

*Hint.* For $y = 3/2$ every $\sigma$ fixes $y$, so $c = 2\log(3/2)$, and $\delta = \log 2$. For $y = \sqrt 2/2$, $|\sigma y|^2 = 1/2$ for all $\sigma$. At $\iota \mid 2$, $\|\iota\sqrt 2\| = 2^{-1/2}$, so the matrix $(\sqrt 2)$ carries $y$ into $\mathcal{O}_\iota$ with loss $1/2$.

**Exercise 2.** Let $z \in \mathbb{C}$. Suppose that the constant family $z$ has height at most $c$ for some $c$. Show that $z$ is algebraic.

*Hint.* Take $H$ from the definition. The bound at $\ell = 2$ makes $Hz$ algebraic, by the algebraicity criterion. The bound $|\sigma H| \leq e^\alpha$ for all automorphisms $\sigma$ makes $H$ algebraic: a transcendental number can be sent to any transcendental number by an automorphism of $\mathbb{C}$.

**Exercise 3.** Show that the constant family $1/2$ has height at most $c$ if and only if $c \geq \log 2$. Then find all $c$ such that the constant family $2$ has height at most $c$.

*Hint.* Use the corollary at the end of Section 3 for one direction. For the family $2$, the answer is $c \geq -\log 2$.

**Exercise 4.** Let $\mathcal{L} \subset \mathbb{R}^2$ be the lattice $\mathbb{Z}^2$ and let $v_1 = (1/2, 0)$, $v_2 = (0, 1)$. In the standard twisted lattice on $\mathbb{C}^2$, find the least covolume bound and the least index bound for $v$, and check the inequality of Section 6 with $n' = 0$.

*Hint.* $\det \mathrm{Gram}(v) = 1/4$, so $c = -2\log 2$. The matrix $\operatorname{diag}(2, 1)$ gives index at most $\log 2$. The inequality is an equality.

**Exercise 5.** Let $O$ be a valuation domain and $a \in O$. Prove the case $\#I = 1$ of the corollary on multiples of the whole module directly from the definition of colength: every finite family $\Phi_1, \dots, \Phi_n$ in $O$ is carried into $aO$ by a matrix with determinant $a$.

*Hint.* Some $\Phi_p$ divides all the others. Subtract multiples of $\Phi_p$ from the others, which makes them $0$, and multiply $\Phi_p$ by $a$.

**Exercise 6.** Show that a family of index at most $\delta$ has $\delta \geq 0$. Show that the empty family has index at most $0$ and covolume at most $0$. Then explain why the theorem of Section 6 with $n = 0$ is a statement about the auxiliary vectors $z$ alone.

*Hint.* Take $U = \emptyset$. The determinant of the empty matrix is $1$.

## Notes and references

Liouville's inequality for algebraic numbers dates from 1844. The product formula is in Neukirch, *Algebraic Number Theory*, Chapter III, §1, and heights of algebraic numbers are in Bombieri and Gubler, *Heights in Diophantine Geometry*, Chapter 1. The list of references of the source gives the place in Bombieri and Gubler at second hand. Minkowski's lattice point theorem is in Neukirch, Chapter I, §4. Hadamard's and Fischer's inequalities are in Horn and Johnson, *Matrix Analysis*, Section 7.8. The docstring of the source calls its Hadamard inequality a weaker form of the one in Horn and Johnson, without the case of equality. The elementary divisor theorem over a principal ideal domain is in Lang, *Algebra*, Chapter III, §7. The source proves the Smith normal form over a valuation domain in its library.

The source files cite three works as related to the method of this chapter: Bost, *Algebraic leaves of algebraic foliations over number fields* (2001); Laurent, *Linear forms in two logarithms and interpolation determinants* (1994); and Gaudron, *Pentes des fibrés vectoriels adéliques sur un corps global* (2006). The method of interpolation determinants bounds a determinant above by its size and below by the product formula. The slope method of Bost and Gaudron puts such bounds in the language of adelic vector bundles. The list of references of the source gives no place in these works, and this book has not compared them with the source.

The notions of this chapter differ from those of the literature in three ways. The places are the automorphisms of $\mathbb{C}$ and the isomorphisms $\mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. Heights are bounds for families indexed by these isomorphisms, so the multiplier is common but the number may change with $\iota$. And the integral structure is given at each $\iota$ through several twists, with the covolume only for the trivial twist. The second point lets the source use a different twist at each prime.

The research notes of this book describe the inequality as "covolume $+ 2 \cdot$ index $\geq 0$". The Lean statement has three more terms, $n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}}$, for the auxiliary vectors and the change of twist. The short form holds only when these terms are $0$, as in the rank-one example of Section 6.

Status: drafted by a model. No person has checked this chapter against the Lean source.
