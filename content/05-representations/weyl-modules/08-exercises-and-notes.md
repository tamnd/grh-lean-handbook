---
title: Exercises and notes
lean:
  - Lib/GLn/SchurModule/GramMatrix.lean
  - Lib/GLn/SchurModule/SchurNorm.lean
  - Lib/GLn/Dual.lean
decls:
  - New.hookNumber
  - New.weylNormSq_schur_le
  - New.weylNormSq_le_mul_of_toPoly_eq
  - New.exists_isDualIsometry
  - New.mixedWeight
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of the chapter. Write $x_{ai}$ for the variable $X(a, i - 1)$, so that the leading $h \times h$ minor is the determinant of $(x_{ai})_{a, i \le h}$.

**Exercise 1.** Take one place, three rows, and the weight with one column of height $1$ and one column of height $2$, that is, the diagram $(2, 1)$. Show that the product of the leading minors is
$$f = x_{11}(x_{11} x_{22} - x_{12} x_{21}) = x_{11}^2 x_{22} - x_{11} x_{12} x_{21},$$
and that the hook number $\langle f, f \rangle$ is $3$. Compare with the product of the hook lengths of the diagram $(2, 1)$.

Lean: `New.hookNumber` (Lib/GLn/SchurModule/GramMatrix.lean).

*Hint.* Distinct monomials are orthogonal for the Fock pairing, and $\langle x^d, x^d \rangle = d!$ for a multi-index $d$. So $\langle f, f \rangle = 2! \cdot 1! + 1! \cdot 1! \cdot 1!$. The hook lengths of $(2, 1)$ are $3$, $1$ and $1$.

**Exercise 2.** In the model case of Section 1, let $z = \operatorname{diag}(a, b)$ with $|a| \ge |b|$. Show that $S(z)$ is diagonal in the basis $b_j = x_1^j x_2^{k-j}$, and that $\|S(z)\xi\|^2 \le |a|^{2k} \|\xi\|^2$. Find numbers $\rho_0$ and $\rho_1$ that satisfy both items of the norm bound of Section 6 for this $z$.

Lean: `New.weylNormSq_schur_le` (Lib/GLn/SchurModule/SchurNorm.lean).

*Hint.* The entry of $S(z)$ at $b_j$ is $a^j b^{k-j}$, and $|a^j b^{k-j}|^2 \le |a|^{2k}$. Take $\rho_0 = |a|^2$ and $\rho_1 = |b|^2$. For one row the diagram weight is $k$ in row $0$ and $0$ in row $1$.

**Exercise 3.** In the model case with $k = 1$ and $k = 2$, let $\xi$ and $\eta$ be vectors of weight $\operatorname{Sym}^1$ and let $\zeta$ be the vector of weight $\operatorname{Sym}^2$ with $\operatorname{toPoly}(\zeta) = \operatorname{toPoly}(\xi)\operatorname{toPoly}(\eta)$. Compute $\zeta$ and check that $\|\zeta\|^2 \le \|\xi\|^2 \|\eta\|^2$. When does equality hold?

Lean: `New.weylNormSq_le_mul_of_toPoly_eq` (Lib/GLn/SchurModule/GramMatrix.lean).

*Hint.* For $k = 1$ the Gram matrix is $1$. For $k = 2$ it is $\operatorname{diag}(1, 2, 1)$ in the basis $x_1^2, x_1 x_2, x_2^2$. The middle coordinate of $\zeta$ is $(\xi_1 \eta_2 + \xi_2 \eta_1)/2$. The inequality reduces to $|u + v|^2 \le 2|u|^2 + 2|v|^2$.

**Exercise 4.** Let $n$ have two rows and $\kappa(1) = 1$, so that the module is the standard representation $\mathbb C^2$ with $G = 1$. Show that $\kappa'(1) = \kappa(2 - 1) = 1$, and that the integer matrix $J = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}$ satisfies $J^{\mathsf T} J = 1$ and $g^{-\mathsf T} J = \det(g)^{-1} J g$ for every invertible $g$. Compare with the four items of a dual isometry in Section 7.

Lean: `New.exists_isDualIsometry` (Lib/GLn/Dual.lean).

*Hint.* For a $2 \times 2$ matrix, $g^{-1} = \det(g)^{-1} \operatorname{adj}(g)$, and $J g J^{-1} = \operatorname{adj}(g)^{\mathsf T}$. The entries of the adjugate are the complementary $1 \times 1$ minors, which is Jacobi's identity in the smallest case. The order of the basis may change the signs in $J$.

**Exercise 5.** Let $n$ have three rows, and let $k_p$ and $k_m$ each be one column of height $1$. Compute `New.mixedWeight` $k_p\, k_m$ at all heights $i \ge 0$. Show that the result is the diagram $(2, 1)$ and that its Weyl module has dimension $8$. Explain this as the Cartan component of $\mathbb C^3 \otimes (\mathbb C^3)^\ast$ twisted by $\det$.

Lean: `New.mixedWeight` (Lib/GLn/Dual.lean).

*Hint.* The value at $i$ is $k_p(i) + k_m(3 - i)$, with truncated subtraction. It is $1$ at $i = 1$ and $i = 2$ and $0$ elsewhere. The tensor product is $\mathfrak{gl}_3 = \mathfrak{sl}_3 \oplus \mathbb C$, and the highest weight of $\mathfrak{sl}_3$ is $(1, 0, -1)$. Adding $(1, 1, 1)$ gives $(2, 1, 0)$. The number of semistandard tableaux of shape $(2, 1)$ with entries in $\{1, 2, 3\}$ is $8$.

## Notes and references

The objects of this chapter are classical. The source cites the Weyl character formula in the form of Fulton and Harris, *Representation Theory: A First Course*, 1991, Theorem 6.3. The branching rule is in Goodman and Wallach, *Symmetry, Representations, and Invariants*, 2009, Theorem 8.1.1, and in Zhelobenko, *Compact Lie Groups and their Representations*, 1973, Chapter X. Molev, arXiv:math/0211289, treats the iterated rule. The duality and the Cartan component are in Fulton and Harris, Section 15.5. The source files also cite Jantzen, *Representations of Algebraic Groups*, 2nd ed., 2003.

The choices in the chapter are these: `New.BasisTableau` by `Classical.epsilon` (Section 3); coordinates by `Function.invFun`, always at points of the range (Sections 4 to 6); the numbers $\rho_\tau(i)$ by `choose` (Section 6); `New.mixedCartan` by `Nonempty.some` (Section 7). The junk value of `New.weightMinors` at a singular matrix is $1$ (Section 6).

The register of findings has two entries on this chapter. Entry F-051 lists `BasisTableau` as an `epsilon` object that need not be semistandard; Section 3 explains why only its existence properties are needed. Entry F-073 asks where the nonvanishing of the branching matrix is used and proved. It is proved as the local fact `value_ne` in the proof of `New.GL.spansBranchingMaps_of_equivariant`, and no exported statement contains it. The callers of `New.exists_branching_matrix` in `New/UpperBound/Objects/Columns.lean` and `New/Determinant/AuxiliaryForms/LastPath.lean` use only its three items. So no proof in the source uses $br \neq 0$. It matters for the meaning: a statement that every period is a multiple of a fixed one carries information only if the fixed one is not zero.

The module docstring of `Lib/GLn/SchurModule/GramMatrix.lean` says "It treats weights with one row at each place." Only one part of the file does: the formula `New.hookNumber_one_row`. The other results of the file, the identity $GH = h_\kappa \cdot 1$, the bound for $h_\kappa$ and the norm, hold for all weights. The sentence describes one subsection, not the file.

Status: drafted by a model. No person has checked this chapter against the Lean source.
