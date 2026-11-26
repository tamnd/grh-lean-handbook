---
title: Exercises and notes
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Unitary/Defs.lean
  - Lib/Adelic/Witt/WittTheorem.lean
  - Lib/Adelic/TraceFormula/TraceComparison.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 6. Throughout, $E$ is a CM field with maximal real subfield $F$.

**Exercise 1.** Let $\eta$ be a primitive seventh root of unity in $E$ and put $\omega = -(\eta + \eta^2 + \eta^4)$. Show that $\omega + \bar\omega = 1$ and $\omega\bar\omega = 2$. Deduce that no finite place of $E$ above $2$ is fixed by conjugation.

*Hint.* Use $\bar\eta = \eta^{-1}$ and $1 + \eta + \dots + \eta^6 = 0$, and expand the product into nine powers of $\eta$. For the second part, a place above $2$ divides $\omega\bar\omega$ but cannot divide both $\omega$ and $\bar\omega$, since $\omega + \bar\omega = 1$.

**Exercise 2.** Suppose that $E$ satisfies the standing condition, `New.HasPrimitiveRoot5040`. Show that $E/F$ is unramified at every finite place, and that $[F : \mathbb{Q}]$ is even. Deduce that the hypothesis `hE`, that the number of infinite places of $E$ is even, in the comparison of traces `New.trace_comparison` follows from the instance argument `[HasPrimitiveRoot5040 E]` of the same theorem.

*Hint.* For the first part, $E = F(i) = F(\omega)$, and the discriminants of $X^2 + 1$ and $X^2 - X + 2$ are $-4$ and $-7$. For the second part, evaluate the quadratic character of $E/F$ at the idele $-1$: it is trivial on $F^\times$, it is $-1$ at each real place, and it is $1$ at each finite place, where it is unramified. Section 4 has the argument.

**Exercise 3.** Let $w$ be a split finite place of $E$ and let $g \in \mathrm{GL}_n(E_w)$. Check that the element `New.ofSplitPlace` of $G_f$, with component $g$ at $w$, the conjugate of $(g^*)^{-1}$ at $\bar w$ and $1$ elsewhere, satisfies $h^* h = 1$. Show that every element of $G_f$ that is $1$ outside $\{w, \bar w\}$ has this form. So the part of $G_f$ at a split pair is a copy of $\mathrm{GL}_n(E_w)$.

*Hint.* The involution of $\mathbb{A}_{E,f}$ exchanges the components at $w$ and at $\bar w$. Write $h^* h = 1$ at $w$ and at $\bar w$ separately.

**Exercise 4.** Let $J$ be hermitian and invertible over a field $R$ with involution, let $v \in R^n$ and let $\sigma$ be a unit with $\sigma + \bar\sigma = v^* J v$. Show that the quasi-reflection $x \mapsto x - \sigma^{-1}(v^* J x)\, v$ preserves the form $x^* J y$. Show that it is the identity on the orthogonal complement of $v$ and that it sends $v$ to $-\sigma^{-1}\bar\sigma\, v$.

*Hint.* Expand $(x - \sigma^{-1} h(v, x) v)^* J (y - \sigma^{-1} h(v, y) v)$. The terms with $h(v, x)\overline{h(v,y)}$ cancel by the relation for $\sigma$. For $v$, use $1 - \sigma^{-1}(\sigma + \bar\sigma) = -\sigma^{-1}\bar\sigma$.

**Exercise 5.** Let $(J, x)$ and $(J, x')$ be two spaces with the same matrix $J$ and signs $s$. Show that $x' = x g$ for a unique $g \in G$, and that the two groups of rational points are conjugate: $\Gamma_{(J, x')} = g^{-1} \Gamma_{(J, x)}\, g$. Compare this with `New.Space.exists_x_eq_and_ratEmbed_conj_eq` when the matrices differ.

*Hint.* Put $g = x^{-1} x'$. Then $g^* \varepsilon_s g = x'^* J x' = \varepsilon_s$, so $g \in U(\varepsilon_s)$, which is $G$ by `New.G.toUnitary`. For the second part, compute $x'^{-1}\gamma x'$.

**Exercise 6.** Show that the index `New.stdLevelIndex` of a level $K$ is finite and positive, and that it equals $1/\operatorname{vol}(K)$ for the Haar measure with $\operatorname{vol}(K_0) = 1$. Show that the trivial subgroup of $G_f$ has the junk index $0$.

*Hint.* A level is open in the compact group $K_0$, so its cosets form a finite open cover. For the last part, $K_0$ is infinite, so the trivial subgroup has infinite index, and the relative index of Mathlib is then $0$.

## Notes and references

The adeles of a number field follow Weil, *Basic Number Theory*, Chapter IV, and Cassels in Cassels and Fröhlich, *Algebraic Number Theory*, Chapter II. The self-dual measure and the standard character follow Tate's thesis, Section 4, in the same book. The local classification of hermitian spaces is in Jacobowitz, *Hermitian forms over local fields*, Amer. J. Math. 84 (1962). Landherr's theorem is in W. Landherr, Abh. Math. Sem. Hamburg 11 (1936), 245 to 248, and in Kneser, *Lectures on Galois cohomology of classical groups*, Tata Institute Lectures 47 (1969), Section 5.5. Witt's theorem for fields is in Dieudonné, *La géométrie des groupes classiques* (1955). The source cites U. A. First, J. Pure Appl. Algebra 219 (2015), Corollary 4.9, for Witt's theorem, and J. Tits, Proc. Sympos. Pure Math. 33 (1979), part 1, 3.3.2 and 3.8.1, for the Iwasawa decomposition at the finite places. The list of references of the source records that these two places were compared. For Jacobowitz and Dieudonné it records the work but no place. The citations in the files on adeles, strong approximation, weak approximation and Landherr's theorem were not part of that check. The facts on adelic groups are in Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, Chapter 5.

The chapter found three points where the notes of the plan or the source can be made more exact.

First, the background notes and finding F-057 describe a space of the source as a hermitian matrix $J$ with a point $x$. The structure `New.Space` has only the fields $J$, $x$ and the identity $x^* J x = \varepsilon_s$. That $J$ is hermitian is the theorem `New.Space.isHermitian_J`, and that $J$ is invertible is `New.Space.isUnit_J`. The description is true of every space, but it is a consequence, not part of the data. The rest of F-057 agrees with the source.

Second, the standing condition implies that the number of infinite places of $E$ is even (Section 4 and Exercise 2). So the hypothesis `hE` of `New.trace_comparison` follows from its other hypotheses. The source does not note this. The hypothesis is harmless, and it could be removed from the statement.

Third, the standing condition is not needed for Witt's theorem over $E$. The statement `New.Space.witt` uses `New.exists_isUnit_sub_star`, which holds for every CM field. The condition is needed for Witt's theorem over $\hat{\mathcal{O}}_E$, for the signed spaces, and for Landherr's theorem in the form of the source. Finding F-058 says that the constant $5040$ has no source in the documents. This chapter uses only its divisors $4$ and $7$.

The volume plan and the links to Theorems A, B and C are in Section 1. CM fields and their places are in [CM fields](/chapter/cm-fields/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
