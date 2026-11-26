---
title: Exercises
lean:
  - Lib/General/Combinatorics.lean
  - Lib/Shimura/IntegralModel/TowerExistence.lean
  - Lib/Shimura/Eigenspace.lean
  - Lib/General/LinearAlgebra/Eigenvalues.lean
  - Lib/Shimura/Transfer/WeightOccurs.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Check the [q-binomial theorem](/decl/New.q_binomial_submodule/) for $W = k^2$ by a direct count. The subspaces are $0$, the $q + 1$ lines and $k^2$. Show that the left side is $1 - (q + 1) X + q X^2$, and factor it.

*Hint.* The coefficient of a line is $(-X)^1 q^0$, and the coefficient of $k^2$ is $(-X)^2 q^1$. The product is $(1 - X)(1 - qX)$.

**Exercise 2.** Let $n = 3$ and let $W = L_0$ be a line in $k^3$. Find the classes of subspaces $A$ under the relation $A + L_0 = A' + L_0$, and check directly that the coefficients $\mu(A) = (-1)^{\dim A} q^{\binom{\dim A}{2}}$ add up to $0$ on each class, as the [Möbius cancellation](/decl/New.Variety.cancels_moebius_of_factorsThrough_sup/) claims.

*Hint.* The classes are indexed by the subspaces $B \supseteq L_0$. For $B = L_0$ the class is $\{0, L_0\}$, with total $1 - 1$. For a plane $B \supset L_0$ the class is $B$ together with the $q$ lines of $B$ other than $L_0$, with total $q - q$. For $B = k^3$ the class is $k^3$ together with the $q^2$ planes that do not contain $L_0$, with total $-q^3 + q^2 \cdot q$.

**Exercise 3.** Show by an example that the hypothesis $W \neq 0$ in the Möbius cancellation cannot be dropped. Take $n = 1$ and $v(A) = A$.

*Hint.* With $W = 0$ the map $A \mapsto A + W$ is the identity, and $[0] - [k] \neq 0$ in the free abelian group.

**Exercise 4.** Let $V = \mathbb{Q}_\ell^3$ with $\Gamma$ trivial and two commuting operators $T_1 = \operatorname{diag}(1, 1, 2)$ and $T_2 = \operatorname{diag}(3, 5, 5)$. For $\theta = (1, 5)$, compute the [eigenquotient](/decl/New.Variety.IsEigenQuotient/) and its dimension $N$. Then do the same for $\theta = (2, 3)$.

*Hint.* The span $S$ is the sum of the images of $T_1 - \theta_1$ and $T_2 - \theta_2$. For $\theta = (1, 5)$ the images are the third and the first coordinate line, so $N = 1$. For $\theta = (2, 3)$ the images together span everything, so $N = 0$.

**Exercise 5.** In the lemma on joint eigenvectors of Section 4, take $W = k^2$, one letter $s$, $\Phi([s]) = \operatorname{diag}(1, 2)$ and $\eta(s) = 3$. Find explicit scalars $c_L$ with $\sum_L c_L \eta(L) = 1$ and $\sum_L c_L \Phi(L) = 0$.

*Hint.* The polynomial $p(x) = (x - 1)(x - 2)/((3 - 1)(3 - 2))$ has $p(3) = 1$ and $p(\Phi([s])) = 0$. Expand it in the words $[\,]$, $[s]$ and $[s, s]$, with $\Phi(L) = \Phi([s])^{|L|}$. You get $c_{[\,]} = 1$, $c_{[s]} = -3/2$ and $c_{[s,s]} = 1/2$.

**Exercise 6.** Show that the [nilpotence lemma](/decl/New.Variety.isNilpotent_of_trace_pow_succ_eq_zero/) fails over a field of characteristic $p$, and say which step of the proof breaks.

*Hint.* Take the identity of $\mathbb{F}_p^p$. In Newton's identities $k e_k = \cdots$ one cannot divide by $k = p$.

**Exercise 7.** Carry out the proof of Eichler-Shimura away from $\ell$ in Section 6 for $a = 1$. Write the relation on points with the two subspaces $0$ and $k_w$ only, and deduce that $r(s)$ acts on the eigenquotient by $t_1 / t_0$ when $t_0 \neq 0$.

*Hint.* For $a = 1$ the subspaces are $0$ and $k_w$, with $\mu = 1$ and $-1$ and exponents $f$ and $0$. Then $P_w(X) = t_0 X - t_1$.

## Notes and references

The classical congruence relation for modular curves is due to Eichler and Shimura. Deligne, *Formes modulaires et représentations l-adiques*, Séminaire Bourbaki 355 (1969), used it to attach Galois representations to modular forms of higher weight, through the cohomology of Kuga-Sato varieties. Diamond and Shurman, *A First Course in Modular Forms*, Chapter 8, give an account for weight 2. The form for unitary Shimura varieties used here, with the coefficients $(-1)^j q^{\binom{j}{2}}$ of the Hecke polynomial, is in Wedhorn, *Congruence relations on some Shimura varieties*, J. reine angew. Math. 524 (2000), 43 to 71, and in Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), Chapters III and VII. The source names these works in its docstrings. It also names Katz and Mazur, *Arithmetic moduli of elliptic curves* (1985), Chapter 13, for the method of the pointwise step.

The occurrence of eigensystems in Section 5 replaces the comparison of trace formulas of Harris and Labesse, Asian J. Math. 8 (2004), Theorem 2.1.2, and Labesse, *Changement de base CM et séries discrètes* (2011), Theorem 5.4. The source proves only occurrence, by a comparison of two finite counts, in the spirit of Shimura, Acta Math. 132 (1974), and of Goresky and MacPherson (2003). The Weil-Deligne point of view on the crystalline Frobenius is due to Fontaine, Astérisque 223 (1994), Exposé VIII. Tate's theorem on the invariants of $\mathbb{C}_\ell(m)$ is in Tate, *p-divisible groups* (1967).

The source states its theorem in a weaker form than the textbook one. The representation is a quotient of the total cohomology, with no control of its dimension, and the Hodge-Tate weights are controlled at one embedding only. Section 6 lists the differences. This book has not compared the proofs of the source with the cited works, and it does not claim that the source follows any of them in detail.

Lean accepts the theorems of this chapter, if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).

Status: drafted by a model. No person has checked this chapter against the Lean source.
