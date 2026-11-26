---
title: The proof of Theorem C
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
decls:
  - New.Data.integral_forms_long
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The proof of Theorem C

This section joins the inputs of Sections 2 to 4. It restates Theorem C, gives the proof in the order of the source, and lists every constant with its origin.

**Theorem (Theorem C, integral forms are long).** Let $n \in \mathbb{N}$, let $y : \{1, \dots, n\} \to D.\mathtt{targetForms}$, and let $\delta, c \in \mathbb{R}$. Suppose that:

1. $y$ is linearly independent over $\mathbb{C}$;
2. $(1 - 4/b^2)\,d \leq n$;
3. $y$ has index at most $\delta$ in the target lattice;
4. $y$ has covolume at most $c$ in the target lattice.

Then

$$d\,\bigl(\mathrm{mainAmount} - 3\,(f a\log^4 b)\bigr) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

*Proof.* The proof has seven steps.

*Step 1: the twists.* By [the theorem on single lifts at good twists](/chapter/proof-of-theorem-c/#a-twist-for-each-prime-and-the-inverse-ratio) take a family $\theta$ of $m$-fold twists with small ratios such that, for every $1 \leq j \leq m$, the family $\iota \mapsto Z_j(1)/Z_j(\theta(\iota))$ has height at most $d(fa\log^4 b/m - k\cdot\mathrm{directionAmount})$.

*Step 2: the scalar and the auxiliary forms.* By [the theorem on auxiliary forms](/chapter/proof-of-theorem-c/#auxiliary-forms-and-the-cost-of-completion) take $e \in \mathbb{Z}$ and $\gamma$ with $\gamma(\vartheta) \neq 0$ for every $\vartheta$, with

$$|\gamma(\vartheta)| = \mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{i<m}\prod_{j<m}\mathrm{turnRatio}_{ij}(\vartheta),$$

and such that the forms auxiliary for $\gamma$ span the target. The property $\gamma(1) = 1$ is not used.

*Step 3: completion.* The target is finite dimensional, $y$ is linearly independent, and the auxiliary forms span. By [completion to a basis](/chapter/proof-of-theorem-c/#the-frame) there are $n' \in \mathbb{N}$ and auxiliary forms $z_1, \dots, z_{n'}$ such that $(y, z)$ is linearly independent and $d = n + n'$. Each $z_i$ is auxiliary for $\gamma$. So two facts hold.

1. For every $i$, every $\iota$ and every $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to the prime of $\iota$, the form $\gamma(\vartheta)\,\Theta_\vartheta z_i$ is integral at the place of $\iota$. This is the lattice of the target lattice at $\vartheta$ and $\iota$, and the condition on $\vartheta$ is "allowed at the prime of $\iota$".
2. For every $i$ and every $\sigma$, the norm of $z_i$ in the target lattice is $\|\Theta_1 z_i\|_\sigma^2$ by [the norm in the target lattice](/decl/New.Data.normSqAt_targetLattice/), and so it is at most $\exp(2x_1^2b^2)$.

*Step 4: the denominators.* The family $\iota \mapsto (|\gamma(\theta(\iota))|^2)^{-1}$ is the square of the family of [the scalar of the auxiliary forms](/decl/New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio/), by the formula for $|\gamma|$. That family has height at most $m\,m\,t\,x_1$, because $\theta$ has small ratios. So the square has height at most $2\,(m\,m\,t\,x_1)$. The sizes give $2(m\,m\,t\,x_1) \leq b$. So the family has height at most $b$.

*Step 5: the volume.* The volume of the target lattice at $\vartheta$ is $Z(\vartheta)$ ([the volume is the chain determinant](/decl/New.Data.volume_targetLattice/)). So the family $\iota \mapsto \mathrm{vol}(1)/\mathrm{vol}(\theta(\iota))$ is the family $Z(1)/Z(\theta(\iota))$. By [the inverse ratio](/decl/New.Data.heightLe_chainDeterminant_one_div/), with Step 1, it has height at most $d(b + fa\log^4 b - \mathrm{mainAmount})$.

*Step 6: the frame.* Apply [the theorem on a twist for each prime](/decl/New.TwistedLattice.covolume_add_index_nonneg/) to the target lattice, with these inputs:

- the lifts are injective ([the lifts are injective](/decl/New.Data.injective_lift_targetLattice/));
- $(y, z)$ is linearly independent and $d = n + n'$ (Step 3);
- $\theta(\iota)$ is allowed at the prime of $\iota$, by the first condition of small ratios;
- $y$ has covolume at most $c$ and index at most $\delta$ (hypotheses 3 and 4);
- $\gamma(\xi) \neq 0$ (Step 2), and the integrality of $\gamma(\xi)\Theta_\xi z_i$ (Step 3);
- $b_{\mathrm{short}} = 2x_1^2b^2$ (Step 3), $b_{\mathrm{denom}} = b$ (Step 4) and $b_{\mathrm{volume}} = d(b + fa\log^4 b - \mathrm{mainAmount})$ (Step 5).

It gives

$$0 \leq c + 2\delta + n'\,(2x_1^2b^2 + b) + d\,\bigl(b + fa\log^4 b - \mathrm{mainAmount}\bigr).$$

*Step 7: the arithmetic.* By [the cost of completion](/decl/New.Data.mul_completion_cost_le/), with hypothesis 2 and $d = n + n'$, we have $n'(2x_1^2b^2 + b) \leq d\,b$. The sizes give $b \leq fa\log^4 b$, and $d \geq 0$, so $d\,b \leq d\,fa\log^4 b$. Insert both bounds:

$$0 \leq c + 2\delta + d\,b + d\,b + d\,fa\log^4 b - d\cdot\mathrm{mainAmount} \leq c + 2\delta + 3\,d\,fa\log^4 b - d\cdot\mathrm{mainAmount}.$$

This is $d(\mathrm{mainAmount} - 3fa\log^4 b) \leq c + 2\delta$. In the source the last step is `linarith`. $\square$

### The constants

The table lists every constant of the proof, its value and the result that supplies it.

| Constant | Value | Source |
|---|---|---|
| $b_{\mathrm{short}}$ | $2x_1^2b^2$ | auxiliary forms, from $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$ |
| $b_{\mathrm{denom}}$ | $b$ | $(\lvert\gamma\rvert^2)^{-1}$: height $2m^2tx_1 \leq b$ |
| $b_{\mathrm{volume}}$ | $d(b + fa\log^4 b - \mathrm{mainAmount})$ | the inverse ratio |
| scalar of the chain | height $m^2tx_1 \leq b$, power $d$ | quotient ratios |
| one lift | $d(fa\log^4 b/m - k\cdot\mathrm{directionAmount})$ | the height of one lift |
| completion | $n'(2x_1^2b^2 + b) \leq d\,b$ | $n' \leq 4d/b^2$ and $4(2x_1^2 + b^{-1}) \leq b$ |
| absorption | $d\,b \leq d\,fa\log^4 b$ | $b \leq fa\log^4 b$ |

The error $3d\,fa\log^4 b$ has three parts. One part $d\,fa\log^4 b$ is the sum of the $m$ denominator budgets, each $d\,fa\log^4 b/m$. One part $d\,b \leq d\,fa\log^4 b$ is the scalar of the chain. One part $d\,b \leq d\,fa\log^4 b$ is the completion, which holds both the length $2x_1^2b^2$ and the denominators $b$ of the $n'$ auxiliary forms. The first part is the true error. The other two parts are much smaller than $d\,fa\log^4 b$, since $fa\log^4 b \geq x b\log^4 b$. The source spends them in the constant $3$ for a simple statement.

### The size inequalities

The proof uses five size inequalities. The source proves each with `New.Data.le_of_hasLogBound` ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)). A reader can check them by hand from $m^2 \leq 4x$, $r \leq 3x^5$, $t = 5r$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$, $f \geq 1$, $a = xb$ and $\log b \geq 1$.

1. $x^{99} + x^{202}b^2 \leq 2x_1^2b^2$, in the theorem on auxiliary forms. Here $x^{202} \leq x_1^2$, and $x^{99} \leq x_1^2b^2$.
2. $m\,m\,(t\,x_1) \leq b$, in the inverse ratio. The left side is at most $4x\cdot 15x^5\cdot x_1 = 60x^6x_1$.
3. $2\,(m\,m\,(t\,x_1)) \leq b$, in Step 4. The left side is at most $120x^6x_1$.
4. $4\,(2x_1^2 + b^{-1}) \leq b$, in the cost of completion. The left side is at most $8x_1^2 + 4$.
5. $b \leq fa\log^4 b$, in Step 7. The right side is at least $x\,b$.

**Remark (Formalization).** Step 1 and Step 2 each produce objects by `obtain`. The family $\theta$ comes from `choose` in Volume 12, the scalar $\gamma$ comes from the units of the spanning theorem, and the forms $z_i$ come from a choice of a basis of a quotient. The statement of Theorem C does not mention any of them. So the theorem does not depend on these choices. The integer $e$ of Step 2 is not the integer $e$ of the inverted factorization in Step 5. The two proofs take them from different theorems, and each bound holds for every integer $e$.

**Remark (Formalization).** All quotients in the proof are true quotients. The twisted lattice gives $\mathrm{vol}(\theta(\iota)) \neq 0$ from the injectivity of the lifts, and $\gamma \neq 0$ is a hypothesis of the frame. The quotients $Z_j(1)/Z_j(\theta(\iota))$ have $Z_j(\theta(\iota)) > 0$ by the factorization theorem. The proof of Theorem C does not use this positivity: the inverted factorization is an identity in Lean also with junk values, and the frame uses only $\mathrm{vol}(\theta(\iota)) \neq 0$.
