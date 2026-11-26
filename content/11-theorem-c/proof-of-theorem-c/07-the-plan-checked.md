---
title: The plan checked against the source
lean:
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The plan checked against the source

The plan of the volume, [Theorem C and the height argument](/chapter/theorem-c-plan/), makes claims about the assembly of Theorem C. The outline chapter [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-c-long-forms) of Volume 1 makes some more. This section compares each claim with the source at the pinned version. First it lists the claims that agree. Then it lists the differences. No difference changes the statement of Theorem C or its constants.

### The claims that agree

The plan states these facts, and the source agrees with each.

1. The statement. The plan gives Theorem C with the four hypotheses (linear independence, $(1 - 4/b^2)d \leq n$, index at most $\delta$, covolume at most $c$) and the conclusion $d(\mathrm{mainAmount} - 3fa\log^4 b) \leq c + 2\delta$ ([the statement of Theorem C](/chapter/theorem-c-plan/#the-statement-of-theorem-c)). This is `New.Data.integral_forms_long` at [line 214](lean:New/Determinant/Twist/LongForms.lean#L214).
2. The error. The plan says that the error is $3fa\log^4 b = 3\log b\cdot\mathrm{err}_0$ per dimension. This holds, as $\mathrm{err}_0 = fa\log^3 b$.
3. The five steps. The plan's proof has the steps twists, auxiliary forms, the three bounds, the frame and the cost of completion. The source proof has the same steps in the same order. Section 5 gives them.
4. The three constants. The plan gives $b_{\mathrm{short}} = 2x_1^2b^2$, $b_{\mathrm{denom}} = b$ and $b_{\mathrm{volume}} = d(b + fa\log^4 b - \mathrm{mainAmount})$. These are the arguments of the frame in the source.
5. The denominator bound. The plan says that the family $|\gamma(\theta(\iota))|^{-2}$ is the square of a family of height at most $m\,m\,(t\,x_1)$, and that $2m^2tx_1 \leq b$. The source proves exactly this, with `HeightLe.pow 2` and `le_of_hasLogBound`.
6. The budget identity. The plan says $k\log b\cdot\mathrm{denominatorBudget} = fa\log^4 b/m$. The source proves it in `exists_hasSmallRatios_heightLe_liftDeterminant_div` by `field_simp`.
7. The completion. The plan gives $n'(2x_1^2b^2 + b) \leq d\,b$ from $n' \leq 4d/b^2$ and $4(2x_1^2 + b^{-1}) \leq b$. This is the proof of `mul_completion_cost_le`.
8. The factorization. The plan states the inverted factorization with the product over $0 < i < j \leq m$ and the power $-d$ ([the four inputs](/chapter/theorem-c-plan/#the-four-inputs)). The source has `Ioc 0 D.m` and `Ioc i D.m`, and the power `D.targetDim` of an inverse. These agree.
9. The scalar of the chain. The plan says that the scalar has height at most $m^2tx_1 \leq b$ for a family with small ratios. The source has the bound $m\,m\,(t\,x_1)$ and the size $m\,m\,(t\,x_1) \leq b$.
10. The existence theorem. The plan states the three conditions of a regular family, the twist error $(4f + 3)\,r\,v_\ell(n_{\mathrm{Aut}}) + 2^{-\ell}$, and the use of `choose`. The source agrees.
11. The height of one lift. The plan states the bound $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$ and the constant $C \neq 0$ of property 2. The source agrees.
12. The normalization. The plan says $\gamma(1) = 1$. The source proves it, as $\gamma = c/c(1)$. The proof of Theorem C does not use it.

### The differences

The source does not agree with the plan or the outline at these points.

**(a) The outline on turn ratios.** The outline ([Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-c-long-forms), Section 5 of that chapter) says: "The turn ratios are products of ratios of Hecke values. Their logarithmic sizes are at most $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$." In the source this bound is not a bound for the turn ratios. It bounds the logarithm of the squared norm $\|\Theta_1 z\|_\sigma^2$ of an auxiliary form. The spanning theorem gives $x^{202}b^2$ for the forms on $Y_0$, the good part adds $x^{99}$, and the size $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$ gives $b_{\mathrm{short}}$. The turn ratios enter only through $|\gamma|$, and their cost is the height $m\,m\,(t\,x_1)$ of Step 4.

**(b) The plan on chapter 11.** The plan ([the chapters of the volume](/chapter/theorem-c-plan/), item 11) says that chapter 11, "with chapter 10", proves the theorem on auxiliary forms. In the source, chapter 11 proves `New.Data.exists_span_short_lifts_eq_top`. That theorem is about forms of principal level on $Y_0$, not about target forms. Two more steps are needed, and both are in LongForms.lean, so in this chapter. The first step applies the good part `goodProjTranslate 1` of Volume 9 and costs the term $x^{99}$. The second step takes $\gamma = c/c(1)$, which already appears in the integrality condition of chapter 11, and computes $|\gamma|$ exactly with `HasAbsUpToNormPower.exists_norm_div_eq` of chapter 8. Chapter 11 gives $|c|$ only up to a constant and a power of the norm. The plan does not mention the term $x^{99}$ or the use of Volume 9.

**(c) The plan on $b_{\mathrm{denom}}$.** The plan ([the height argument](/chapter/theorem-c-plan/)) says that $b_{\mathrm{denom}}$ "bounds the height of the factors that make the twisted lifts of the $z_i$ integral". In the source, $b_{\mathrm{denom}}$ bounds the height of the family $(|\gamma(\theta(\iota))|^2)^{-1}$, the inverse of the squared absolute value of these factors. The description is not exact, but it names the right quantity.

**(d) The plan's table of errors.** The plan gives the sizes per dimension $fa\log^4 b$, $b$ and $b$ for the denominators, the quotient ratios and the completion. These sizes are correct. The row "completion" holds two costs: the length $2x_1^2b^2$ and the denominators $b$ of the auxiliary forms. The table names only the length. The final constant $3$ uses $b \leq fa\log^4 b$ twice. The plan says this in Step 5.

**(e) The plan on the dependencies.** The plan's table of dependencies gives "17 proof-of-theorem-c <- 11, 16". The file LongForms.lean imports five files: FitTwistsExist (Volume 12), SpanningForms (chapter 11), LiftVolumeHeight (chapter 16), IntegralTargetForms (Volume 1) and ArchimedeanSize (Volume 9). The proof uses chapter 2 (small ratios, regular families), chapter 8 (ratios, factorization, heights of products) and chapter 10 (turn ratios) directly. The plan names Volume 12 in its text, but the table does not show chapters 2, 8 and 10 or Volumes 1 and 9.

**(f) The plan on the content of this chapter.** The plan (item 17) says that this chapter gives "the theorem on a twist for each prime, the cost of completion, and the inverse ratio lemma". This chapter states and proves all three. But the theorem on a twist for each prime is `New.TwistedLattice.covolume_add_index_nonneg` of Volume 1, at [line 477](lean:New/Reduction/Lattices/TwistedLattice.lean#L477), not a declaration of LongForms.lean. The plan also says that LongForms.lean is the file of the outline chapter of Volume 1. This holds for Theorem C only.

### What the differences mean

The differences (a) to (f) are in the descriptions, not in the mathematics. Every statement that the plan gives with a `Lean:` line agrees with the source. Every constant in the plan's proof agrees with the source. A reader who follows the plan gets the right theorem and the right proof. The reader must add the step through the good part of Volume 9, which the plan leaves out.

**Remark.** The comparison uses the source at the pinned version, and the texts of the plan and the outline as merged. The source claims the proofs of all the declarations named here, and Lean accepts them, if the reported checks hold.
