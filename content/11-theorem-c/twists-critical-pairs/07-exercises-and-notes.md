---
title: Exercises
lean:
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $m = 4$ and let $w$ be a place with $q_w = 13$. Find the number of characters $\psi_w$ of $\mathbb{F}_{13}^\times$ with $\psi_w^n \neq 1$ for $1 \leq n \leq 4$. Then find the smallest prime $q$ for which $\mathbb{F}_q^\times$ has such a character for $m = 12$.

*Hint.* By the example on the order condition in Section 2, the character must have order $d \mid 12$ with $d > 4$, so $d \in \{6, 12\}$. There are $\varphi(6) + \varphi(12) = 2 + 4 = 6$ such characters. For $m = 12$ you need a divisor of $q - 1$ larger than $12$. The prime $q = 13$ fails, since its largest divisor of $q - 1$ is $12$. Check that $q = 17$ works.

**Exercise 2.** Show that $\mathrm{ratio}(p, \mathbf{1}, s) = 1$ for every critical pair $p$ and both signs $s$.

*Hint.* Use [the lemmas on the trivial twist](/decl/New.Data.toAutChar_one_and_toTwist_one_and_Q_one/): the modulus of $\mathbf{1}$ is empty and its character is $1$, so $1^s = 1$ and the numerator and the denominator of [the ratio](/decl/New.Data.CriticalPair.ratio/) are the same number. Then use that the denominator is not zero, by the proof of [the non-vanishing of the ratio](/decl/New.Data.CriticalPair.ratio_ne_zero/). Without that step the conclusion would fail for the junk value $0/0 = 0$.

**Exercise 3.** Show that the type [RankOneIndex](/decl/New.Data.RankOneIndex/) $z$ has $2z$ elements if and only if $z \geq 10$. Conclude that the first condition of a [main pair](/decl/New.Data.CriticalPair.IsMainPair/) holds if and only if $z \geq 10$, and that it follows from the second condition $z > m$ when $m \geq 10$.

*Hint.* The type has $12 + 4 + 4 + (2z \mathbin{\dot-} 20)$ elements. For $z < 10$ this is $20$, and $2z < 20$. For $z \geq 10$ it is $2z$, and then $2 \leq z$ holds.

**Exercise 4.** In the model case of Section 1, put $y = L(2, \chi_5)/\zeta(2) = 24/(25\sqrt 5)$. Find all primes $\ell$ with $|y^{-1}|_\ell > 1$ for some embedding of $\mathbb{Q}(\sqrt 5)$ into $\overline{\mathbb{Q}}_\ell$, and compute $|y^{-1}|_\ell$ for them. Then find a rational exponent $e$ such that $5^e y$ is an integer, and explain why the factor $5^e$ does not change $|y|_\ell$ for $\ell \neq 5$.

*Hint.* $y^{-1} = 25\sqrt 5/24$. The number $\sqrt 5$ is a unit at every $\ell \neq 5$. So the primes are $2$ and $3$, with $|y^{-1}|_2 = 8$ and $|y^{-1}|_3 = 3$. At $\ell = 5$ the inverse is small. Since $25\sqrt 5 = 5^{5/2}$, the exponent $e = 5/2$ gives $5^{5/2} y = 24$. The exponent is not an integer, which is why [the lemma on powers of units](/decl/New.HeightLe.rpow_mul/) allows rational exponents, and why [the theorem on products of ratios](/decl/New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod/) has the exponent $e/2$. For $\ell \neq 5$, $5^{5/2}$ is an $\ell$-adic unit, because its square $5^5$ is one.

**Exercise 5.** Write out [the factorization of $L_*$](/decl/New.Data.CriticalPair.lValueProd_eq_mul_prod_ratio_sq/) for $z = 3$. Show that

$$\frac{L_*(S \cup Q, (\nu\vartheta)^{-1}, 3)}{L_*(S, \nu^{-1}, 3)} = (\mathrm{Nm}\,Q)^9 \prod_{z'=1}^{3} \frac{|L^{S\cup Q}(z', (\nu\vartheta)^{-1})|^2}{|L^S(z', \nu^{-1})|^2},$$

and explain why the denominator on the left is not zero.

*Hint.* The norm factor of $L_*$ splits because $S$ and $Q$ are disjoint ([disjointness](/decl/New.Data.TameChar.disjoint_isChosen_Q/)). For the denominator use the non-vanishing of $L^S(z', \nu^{-1})$ at $z' = 1, 2, 3$ and $\prod_{w \in S} q_w \geq 1$.

**Exercise 6.** Check the identity $k \cdot \log b \cdot \mathrm{denominatorBudget} = f a \log^4 b/m$ from the definition of [the budget](/decl/New.Data.denominatorBudget/) and the error unit $f a \log^3 b$. Use it to derive [the theorem on single lifts at good twists](/decl/New.Data.exists_hasSmallRatios_heightLe_liftDeterminant_div/) from [the theorem on one lift determinant](/decl/New.Data.heightLe_liftDeterminant_ratio/). Say where you use $k \neq 0$.

*Hint.* Expand $d \cdot k \cdot (\log b \cdot \mathrm{denominatorBudget} - \mathrm{directionAmount})$. The cancellation of $k$ against the $k$ in $m k$ needs $k \neq 0$ as a real number; the sizes of the data give $k > 0$.

## Notes and references

The model case of Section 1 uses the classical values $\zeta(2) = \pi^2/6$ and $L(2, \chi_5) = 4\pi^2/(25\sqrt 5)$. The values of Dirichlet $L$-functions at the critical points in terms of generalized Bernoulli numbers are in Washington, *Introduction to Cyclotomic Fields*, Chapter 4. The non-vanishing $L(1, \chi) \neq 0$ for a nontrivial Dirichlet character, the model of the case $z = 1$ in Section 3, is the central step of Dirichlet's theorem; see Serre, *A Course in Arithmetic*, Chapter VI. In the source the non-vanishing on $\mathrm{Re}\,s \geq 1$ of Hecke $L$-functions is the input of [the theorem on non-vanishing](/decl/New.AutChar.HasWeight.L_ne_zero/), from Volume 3.

The expression of critical Hecke $L$-values of CM fields as squared norms of theta lifts from $U(1)$ to a definite unitary group is the subject of the file `Lib/SiegelWeil/RallisInner/SharpData.lean`. Its docstring names the sources: Shimura, *On some arithmetic properties of modular forms of one and several variables*, Ann. of Math. 102 (1975); for the method, T. Yang, *Theta liftings and Hecke L-functions*, J. reine angew. Math. 485 (1997); Harris, Li and Skinner, *The Rallis inner product formula and p-adic L-functions* (2005); and Finis, Ann. of Math. 163 (2006). The Rallis inner product formula itself is treated in [the Rallis inner product formula](/chapter/rallis-inner-product/).

For the regular families, the docstring of `New/Congruences/FitTwistsExist.lean` names related work: Prasanna, *Integrality of a ratio of Petersson norms* (2006), after Ribet (1976) and Wiles; Klosin, *Congruences among modular forms on U(2,2) and the Bloch-Kato conjecture* (2009); and Mazur and Rubin, *Ranks of twists of elliptic curves* (2010). This book has not compared these works with the source, and it does not claim that the source follows any of them.

Two remarks on the planning notes of the handbook. First, the notes derive the non-vanishing of the ratio from the positivity of the algebraic part. The source proves it directly from the non-vanishing of Hecke $L$-values, and the formula with algebraic parts holds only for the sign $s = 1$ and $z \geq 2$ (Section 3 and Section 4). Second, the notes ask whether the lower bound of a main pair is $w_j + r - t \leq c$. The source states $w_j + r \leq c + t$, without subtraction, which is the same bound over $\mathbb{Z}$. The docstrings of `HasLiftRank` and of `IsMainPair` say $2 \leq z$, while for the type `RankOneIndex z` the condition forces $z \geq 10$ (Exercise 3). The docstring of `RankOneIndex` itself states the correct range.

The file `New/Determinant/Twist/FitTwists.lean` imports `New.OneLift.HeckeValues.CharacterLiftNorm` and `New.OneLift.TestedForms`. Both files belong to the later chapter [character lifts and tested forms](/chapter/character-lifts/) of this volume. The dependence is through the definitions: the main pairs use `HasLiftRank` and the lift data, and the denominators use test forms and false lifts. No theorem of that chapter is used in the proofs of Sections 2, 3 and 5. Section 4 states one theorem of that chapter in full: the norm formula of its Section 6.

Status: drafted by a model. No person has checked this chapter against the Lean source.
