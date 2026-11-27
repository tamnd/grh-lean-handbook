---
title: The plan checked against the source
lean:
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The plan checked against the source

[Theorem A and its plan](/chapter/theorem-a-plan/) makes claims about the assembly of Theorem A. This section compares each claim with part A of New/Reduction/ShortAndEnough.lean. It also compares the short form of the proof in [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-a-short-forms-of-small-index) of Volume 1. The first list gives the claims that agree with the source. The second list gives the differences. None of the differences changes the statement of Theorem A.

### Claims that agree

1. The statements of parts (a) and (b), with the constants $\exp(\mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b)$ and $\#t\cdot\dim\mathrm{src}\cdot 2 f a\log^3 b$, agree with `span_short_integralRamified_eq_top` and `indexLe_normalizedPoincare`.
2. The gain factor is $c_B = \prod_{\ell\in\mathcal{S}\cup\{N\}}\ell^{-g_\ell}$ with $g_\ell = \lfloor\mathrm{gain}_\ell - \mathrm{err}(\ell)\rfloor$, as in `invGainFactor` and `gainExponent`.
3. The bound $\log c_B \leq -\sum_{\mathcal{S}}\mathrm{gain}_\ell\log\ell + f a\log^3 b + b$ agrees with `log_invGainFactor_le`. Its proof uses $\mathrm{gain}_N = 0$, as $x_1 \leq N$, and $\lceil x_1\rceil x_1 + \log N \leq b$, as the source does.
4. The value $\|c_B\| = \ell^{g_\ell}$ at every prime $\ell$, with $1$ outside the product, agrees with `norm_invGainFactor`.
5. The exponent total $\mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4 f a\log^3 b + 2b$ and its bound by $f a\log^4 b$ agree with the source. The factor $2$ of the gains cancels exactly against $2\log c_B$.
6. The exponent $e(\ell) = D_X\,\mathrm{err}(\ell)$ and the bound $D_X \leq 2\dim\mathrm{src}$, from $f/(N-1) \leq b^{-8} \leq 1/2$, agree with the source.
7. The index is defined over finite sets of primes, as in `New.TwistedLattice.IndexLe`.
8. Part (a) uses only the trivial twist, and part (b) uses every $m$-fold twist of level prime to $\ell$.
9. The coefficients of $\#\bar G\,e_0$ are algebraic integers with $|\sigma e_0(t)| \leq 1$, and $\exp(x^{30})(\#\bar G)^4 \leq \exp(x^{99})$. These are the facts that the two lemmas on the good part use.
10. The downstream index $5\,d_T\log(1 + 2b^2)\cdot 2 f a\log^3 b \leq 30\,d_T f a\log^4 b$ is the bound used in the main inequality.
11. The remark that the witness of the errors is never unfolded agrees with the use of `choose` in `divisibilityError`.
12. The remark on the seesaw constant, chosen by `choose` and possibly the value of a degenerate case, agrees with `seesawConst`.

### Differences

The differences are listed as (a) to (g).

(a) *The dependency table.* [The chapters of Volume 9](/chapter/theorem-a-plan/) gives the line "15 proof-of-theorem-a <- 11, 12, 14". The source uses more chapters. It uses chapter 2 for the composite lift and the chain data, chapter 9 for the short forms, the gain and the dimension of the source, and chapter 10 for the integral source forms. It also uses Volume 1 for the colength, the index and the target lattice, Volume 10 for $\mathcal{P}$, $\#\bar G\,e_0\,s$ and the good Poincaré map, and Volume 11 for $\Theta_\vartheta$. The file ShortAndEnough.lean imports New/Spanning/SecondMoment/SpanningTheorem.lean, a file of Volume 10. So the claim of the same section that "each file of a chapter imports only files of earlier chapters, with three exceptions in chapter 2" does not hold for this chapter, if the order of the volumes is the order of the files.

(b) *The places.* The plan says that $\iota$ is "a field isomorphism $\mathbb{C} \cong \mathbb{C}_\ell$". In the source, $\iota$ is a `New.PrimePadicIso`: a prime $\ell$ with a ring isomorphism from $\mathbb{C}$ to the algebraic closure $\overline{\mathbb{Q}}_\ell$. The place of $\iota$ is the induced embedding into $\mathbb{C}_\ell$. This chapter uses the source form.

(c) *Property 4 of the errors.* The plan states property 4 with $S \subseteq L$. The theorem on the divisibility has this conjunct, but the lemma `exists_colengthDvd_gaugeLe_divisibilityError` of the file drops it. The proof of part (b) does not use it.

(d) *The proof of the index lemma.* The plan proves the index of one translate in one step: the colength in the source and the integrality of the images give the index "by the same matrix". The source needs two more steps. The colength lives in the space of all source forms, and the integrality lives in $T$. So the source pulls the colength back to $\mathrm{src}$ along the inclusion and then pushes it forward to $T$ along $s\mathfrak{p}$, with the module $M$ of ramified forms integral at $\iota$ and its image $s\mathfrak{p}(M)$. Section 7 gives these steps. The constant is the same.

(e) *Volume 1.* [Theorems A, B and C](/chapter/theorems-a-b-c/) says that the gain is defined in [the archimedean size](/chapter/archimedean-size/). In the source the gain `New.Data.gain` is defined in New/UpperBound/Size/ShortColumns.lean, the file of [short columns and the gain](/chapter/short-columns-gain/). The vanishing lemma is in Estimates.lean, which the archimedean size explains. The same chapter of Volume 1 refers to "Chapters 7 to 12 of Volume 9" for the divisibility, an older numbering of the chapters.

(f) *The seesaw identity.* [The seesaw identity, part 1](/chapter/seesaw-identity-1/) says that "every tame character $\vartheta$ has a chain datum". The source quantifies over the type `D.Twist` of twists: a twist is a tame character with a nontrivial tame part. The chain datum condition is stated for the twist, and the lower chain is taken for its tame character. Part (b) applies the identity to the underlying twist of an $m$-fold twist.

(g) *One map.* The plan says that "Theorem A says two things about one linear map". The source has a family of maps $s\mathfrak{p}$, one for each $s \in \bar G$. The lemma on translates shows that $s\mathfrak{p}$ is the translate by $s$ of $1\mathfrak{p}$, so the family is determined by one map. Part (a) holds for every $s$, and part (b) is stated for a set $t$ of translates.

### What the differences mean

The differences (b), (c), (f) and (g) are differences of wording. In each case the source is more precise, and the statement of the plan follows from the statement of the source. Difference (d) is a gap in the proof of the plan, not in its conclusion: the steps are formal, and Section 7 supplies them. Differences (a) and (e) are errors in the cross references. The table of dependencies should list chapters 2, 9 and 10 and the files of Volumes 1, 10 and 11, and Volume 1 should point to short columns and the gain for the definition of the gain.

The plan also has claims that this chapter does not check, as they are not about the assembly: the motivation, the model case and the description of chapters 2 to 14.

**Remark (Formalization).** The comparison is with the pinned source. A difference in this list does not mean that the plan proves a false statement. It means that the plan and the source say different things, and that the source is the reference.

**Example (Reading difference (d)).** Let $\ell$ be a prime and suppose that the colength in the source gives $j = 2$. The plan reads this as: the images of the integral ramified forms are carried into the integral target forms by a matrix with determinant dividing $\ell^2$. To get this, the source first restricts the colength from all source forms to $\mathrm{src}$, which keeps $j = 2$, and then applies $s\mathfrak{p}$, which keeps $j = 2$ again. Each step uses one rule of [colength](/chapter/twisted-lattices/#colength). The loss stays $2\log\ell$ in the index.
