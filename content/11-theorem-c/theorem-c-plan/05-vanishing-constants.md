---
title: Constants that may vanish
lean:
  - New/Determinant/Exchange/OneSquare.lean
  - New/Determinant/Exchange/TheoremForPartners.lean
  - New/Determinant/Chain/TriangleNorms.lean
  - New/Determinant/Chain/NormOfChain.lean
  - New/Determinant/Chain/ChainNorms.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - Lib/ClassField/Avatar/HeckeBaseChange.lean
  - New/OneLift/ComparisonOperator/GluingMaps.lean
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
decls:
  - New.Exchange.one_square_identity_of_isEdgeFamily
  - New.Exchange.exchange_identity
  - New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct
  - New.Exchange.SquareCommutes
  - New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero
  - New.Exchange.IsTriangle.ne_zero_of_squareCommutes
  - New.Data.CriticalPair.algPart_pos
  - New.Data.CriticalPair.ratio_eq_algPart_div
  - New.AutChar.HasWeight.L_ne_zero
  - New.Data.CriticalPair.ratio_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Constants that may vanish

Section 2 showed that a height bound says nothing about a number that may be $0$. So the reader must track which numbers are proved to be nonzero. Many identities of the volume have the form "$A = \kappa B$ for some constant $\kappa$", and the existence statement alone allows $\kappa = 0$. The rule is this: an identity with a constant that may be $0$ is used only in a direction where $0$ does no harm, or the nonvanishing is proved separately from injectivity or from $L$-values.

### The constants of the square identity

The basic identity of the volume compares two composites of theta lifts around a square of spaces: from $U_1$ to $U_2$ through $A$, and from $U_1$ to $U_2$ through $A'$. The chapter [seesaw squares](/chapter/seesaw-squares/) states it in full. Its conclusion has this shape.

**Theorem (One square identity, the conclusion).** Under the hypotheses of the chapter on seesaw squares there are $C \in \mathbb{R}$ and $\kappa \in \mathbb{C}$ such that for every index $i$ there is $c \in \mathbb{C}$ with $c \neq 0$ and $|c|^2 = C\cdot L_{\mathfrak{m}_i}(\nu_i, t)$, where $L_{\mathfrak{m}_i}(\nu_i, t)$ is a product of $L$-values, and such that for every form $f$ and every functional $l$ the two composites satisfy the square law with constant $\kappa/c$.

Lean: `New.Exchange.one_square_identity_of_isEdgeFamily` (New/Determinant/Exchange/OneSquare.lean).

The square law with constant $\kappa/c$ says that $\sum_y \Psi(y)L'(y) = (\kappa/c)\sum_x \Phi(x)L(x)$ for all matched functions $\Phi$, $\Psi$ modulo $\mathfrak{m}_i$, where $L$ and $L'$ are the values of the two composites.

**Remark (Formalization).** Nothing in the statement says $\kappa \neq 0$. If $\kappa = 0$, the law says that the sums of the second composite vanish, and it gives no comparison of the two composites. The constant $C$ has no sign condition in the statement. For $i$ in the index set, $c \neq 0$ forces $C\cdot L_{\mathfrak{m}_i}(\nu_i, t) > 0$. If the index set is empty, $C$ and $\kappa$ are arbitrary. The source uses the identity in two places. It shows that the squares of a triangle commute up to some scalar, and it gives the square law for a square of the grid ([line 769](lean:New/Determinant/AuxiliaryForms/Turns.lean#L769), in [grids, columns and turns](/chapter/grids-paths-turns/)). For the triangle, the nonvanishing of the scalar comes back from injectivity, as below.

The same pattern appears in the exchange identity.

**Theorem (The exchange identity, the constant).** Under the hypotheses of [the exchange identity, part 2](/chapter/exchange-identity-2/), there are $C > 0$ and a Schwartz vector $x$ such that every character $\nu$ that is tame for $(\mathfrak{m}, \chi)$ has a number $c$ with $|c|^2 = C\cdot L_{\mathfrak{m}}(\nu, e) \neq 0$ by which the two theta integrals differ.

Lean: `New.Exchange.exchange_identity` (New/Determinant/Exchange/TheoremForPartners.lean).

**Remark (Formalization).** The condition $C > 0$ is real content only when some tame pair exists. In the case $C \leq 0$ the proof takes $C = 1$, and the statement holds because its universal part is empty. A reader should not conclude from $C > 0$ alone that an $L$-value is positive.

### The constant of the chain

The factorization of Input 3 comes from an operator identity.

**Theorem (The chain operator).** There are $C \in \mathbb{R}$, an integer $e$ and numbers $c(\vartheta) \in \mathbb{C}$, one for each $m$-fold twist, such that $C > 0$, $|c(\vartheta)| = C\cdot\mathrm{Nm}\,Q(\vartheta)^{e/2}\prod_{0 < i < j \leq m}\mathrm{quotientRatio}_{ij}(\vartheta)$ for every $\vartheta$, and

$$\Theta_\vartheta^*\Theta_\vartheta = c(\vartheta)\,c_Q(\vartheta)^m\,R(\vartheta)$$

on the target forms, where $c_Q(\vartheta)$ is the twist factor of the first lift and $R(\vartheta)$ is the product of the $m$ series of Rallis' formula.

Lean: `New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct` (New/Determinant/Chain/NormOfChain.lean).

*Proof.* A Gram identity gives numbers $c(\vartheta)$ with the operator identity and with $|c(\vartheta)/c(1)|$ of the stated form when $c(1) \neq 0$. If $c(1) \neq 0$, take $C = |c(1)|$. If $c(1) = 0$, then $\langle\Theta_1 y, \Theta_1 y\rangle = 0$ for every target form $y$. The lift $\Theta_1$ is injective (`New.Data.lowerChainAtLevel_injective`), so every target form is $0$. Then every operator on the target is $0$, and the identity holds with $C = 1$, $e = 0$ and $c(\vartheta)$ the product of the quotient ratios. $\square$

**Remark (Formalization).** In the case $c(1) = 0$ the theorem holds for a trivial reason, and the numbers $c(\vartheta)$ of the conclusion are not those of the Gram identity. What Theorem C uses is the quotient $Z(1)/Z(\vartheta)$, and $Z(\vartheta) > 0$ for every $\vartheta$ by injectivity (`New.Data.chainDeterminant_pos`). So the division in Input 3 is a real division.

### Nonvanishing from injectivity

The chain of lifts is a triangle of spaces $F_{i,n}$ with arrows $a$ along the rows and maps $d$ down the rows. Each square commutes up to a scalar.

**Definition (A square commutes up to β).** The square at $(i, n)$ *commutes up to $\beta$* if for every parameter $t$ and every $y \in F_{i, n+1}$,

$$w_t(n)\,a(d\,y) = \frac{w_t(n+2)}{\overline{\beta(t)}}\,d(a\,y).$$

Lean: `New.Exchange.SquareCommutes` (New/Determinant/Chain/TriangleNorms.lean).

**Remark (Formalization).** The scalar on the right is a quotient, and in Lean $x/0 = 0$. So if $\beta(t) = 0$, the condition says only that $w_t(n)\,a(d\,y) = 0$. A square that "commutes up to $\beta$" with a zero of $\beta$ gives no relation between the two composites.

**Theorem (Chains are injective).** Let the triangle have nonzero weights. If $i + n \leq m$ and the weighted composite of the first $n$ arrows of row $i$ kills $j_i(y)$, then $y = 0$.

Lean: `New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* Induction on $n$. For $n = 0$ the map $j_i$ is an isometry. For $n + 1$, the chain commutes up to a scalar with the chain of row $i + 1$ after $d \circ a$, so the shorter chain kills $j_{i+1}(x)$, where $j_{i+1}(x) = d(a(j_i y))$. By induction $x = 0$, and $d \circ a$ is injective on the image of $j_i$, so $y = 0$. $\square$

**Theorem (The scalars of the squares are not zero).** Let the triangle have nonzero weights and $V \neq 0$. Let $i + (n + 1) < m$, and let the square at $(i, n)$ commute up to $\beta'$. Then $\beta'(t) \neq 0$ for every $t$.

Lean: `New.Exchange.IsTriangle.ne_zero_of_squareCommutes` (New/Determinant/Chain/TriangleNorms.lean).

*Proof.* The chain of length $n$ from row $i$ commutes with row $i + 1$ up to some $\beta$. Adding the square gives a chain relation with scalar $\beta\beta'$. If $\beta(t)\beta'(t) = 0$, then the quotient by $0$ is $0$, so the chain of row $i + 1$ kills the image of a nonzero $y$, against injectivity. So $\beta(t)\beta'(t) \neq 0$, and $\beta'(t) \neq 0$. $\square$

The lemma that the source applies is the chain form, `New.Exchange.IsTriangle.ne_zero_of_chainCommutes`: it is used in the computation of the Gram form of a chain. The square form above is not applied elsewhere in the source. The injectivity of the chain gives `New.Data.lowerChainAtLevel_injective`, and the injectivity of one lift (`New.Data.singleLift_injective`) comes from Rallis' inner product formula.

### Nonvanishing from L-values

The ratio of a pair (Section 4) is a quotient of absolute values of partial $L$-values, and in Lean $x/0 = 0$. If the denominator vanished, the ratio would be $0$. Then its inverse would be $0$ too, as $0^{-1} = 0$ in Lean, and the height bound in the definition of small ratios would hold for any family. Two results exclude this.

**Theorem (Nonvanishing on the line Re s ≥ 1).** Let $\nu$ be a Hecke character of $U(1)$ of weight $e \neq 0$, with a tame part, and let $S$ be a finite set of finite places. Then the $L$-function of $x \mapsto \nu(x/\bar{x})$, without the Euler factors at $S$ and its conjugates, does not vanish at any real $s \geq 1$.

Lean: `New.AutChar.HasWeight.L_ne_zero` (Lib/ClassField/Avatar/HeckeBaseChange.lean).

The textbook form is Hecke's theorem that the $L$-function of a nontrivial Grössencharacter does not vanish on the line $\mathrm{Re}\,s = 1$. The source proves the case it needs: the square of the base change has a nonzero type at infinity, so it is not trivial, and the Euler product does not vanish.

**Remark (Formalization).** At $s = 1$ the value is defined as the limit from the right of the Euler product. This is a convention of the source, and the statement at $s = 1$ is about that limit.

**Theorem (The ratio is not zero).** For every critical pair $p$, every tame character $\vartheta$ and every sign $s$, $p.\mathrm{ratio}(\vartheta, s) \neq 0$.

Lean: `New.Data.CriticalPair.ratio_ne_zero` (New/OneLift/HeckeValues/TwistedRatio.lean).

*Proof.* The character $\nu$ has a nonzero weight, and $\vartheta$ has weight $0$. So both $(\nu\vartheta^s)^{-1}$ and $\nu^{-1}$ have nonzero weight. The point $z$ satisfies $z \geq 1$. The last theorem gives that neither $L$-value is $0$. $\square$

A second route gives more: the ratio is a quotient of positive numbers. For a pair with a lift of rank $2z$ the algebraic part is $\mathrm{algPart}(\vartheta) = \|\phi_\vartheta\|^2/\mathrm{Nm}\,Q(\vartheta)^{2z-1}$, where $\phi_\vartheta$ is the scaled lift of $\nu\vartheta$.

**Theorem (The algebraic part is positive).** For a critical pair $p$ with a lift of rank $2z$, $z \geq 2$, and a tame character $\vartheta$, $0 < \mathrm{algPart}(\vartheta)$.

Lean: `New.Data.CriticalPair.algPart_pos` (New/OneLift/HeckeValues/TwistedRatio.lean).

**Theorem (The ratio as algebraic parts).** For such a pair and every tame character $\vartheta$, $p.\mathrm{ratio}(\vartheta) = \mathrm{algPart}(\vartheta)/\mathrm{algPart}(1)$.

Lean: `New.Data.CriticalPair.ratio_eq_algPart_div` (New/OneLift/HeckeValues/TwistedRatio.lean).

*Proof.* The algebraic part is $A$ times the $L$-value for a constant $A$ that does not depend on $\vartheta$. As the algebraic part is positive, $A \neq 0$, and $A$ cancels in the quotient. $\square$

So the ratio is a quotient of two positive real numbers, each a normalized squared norm of a lift. The height bounds of [Hecke values of character lifts](/chapter/hecke-values/) and the class sums of Volume 12 work with this form. The nonvanishing alone comes from the $L$-values. In the comparison operator the same care appears once more: property 1 of Input 4 says that $\rho_j(\vartheta) \neq 0$, and the proof of the height of one lift uses it to show that the determinant $\Delta(\vartheta)$ is not $0$.

### A setting of the elaborator

Four declarations of the volume are elaborated with the option `backward.isDefEq.respectTransparency` set to false: the gluing map `New.Rows.glue`, the period formula `New.Rows.inner_adjoint_glue` and the lemma `New.Rows.thetaKernelPairing_adjoint_glue_eq_zero` in [GluingMaps.lean](lean:New/OneLift/ComparisonOperator/GluingMaps.lean#L344), and the lemma `New.Rows.algFormRep_conj_block_apply_eq_self` in [PeriodsOfFalseLifts.lean](lean:New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean#L549), where a comment says that it is "for rewriting products in `Gf`".

**Remark (Formalization).** When Lean elaborates a proof, it often checks that two terms are equal by unfolding definitions. Each definition has a transparency, and by default this check does not unfold definitions past the transparency of the current setting. With the option set to false, the check may unfold more, as older versions of Lean did. The option changes only how the elaborator finds a proof term. It does not change any statement, and it adds no axiom. The kernel checks the final term independently, and the kernel does not use transparency settings. So the mathematics of the statements is the same as without it. The same option appears in other files of the source, mostly in `Lib`, outside Volume 11.
