---
title: What the chapter proves
lean:
  - New/Determinant/Chain/NormOfChain.lean
  - New/UpperBound/Objects/RowChain.lean
decls:
  - New.Data.Θ
  - New.Data.chainDeterminant
  - New.Data.liftDeterminant
  - New.Data.rallisProduct
  - New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct
  - New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Theorem C is a lower bound for the covolume of the integral target forms ([the plan of the main theorem](/chapter/theorem-and-plan/)). This covolume is measured by the chain determinant $Z(\vartheta)$, the volume of a chain of $m$ theta lifts at a twist $\vartheta$ ([the volume and the chain determinant](/chapter/integral-target-forms/#the-volume-and-the-chain-determinant)). This chapter proves the factorization of $Z(\vartheta)/Z(1)$ that [the plan of Theorem C](/chapter/theorem-c-plan/) calls the third input. The factors are a scalar, which is a product of ratios of Hecke values, and the determinants $Z_j(\vartheta)$ of the single lifts of [single theta lifts and their norms](/chapter/single-theta-lifts/).

The chain is mostly outside the range of Rallis' inner product formula. So its norm cannot be computed in one step. The source puts the lifts in a triangle of spaces, and it moves the norm of the chain down the triangle one row at a time. Each row costs one application of Rallis' formula to a single lift and one commutation relation for each square of the row. The commutation relations come from the seesaw squares of [the previous chapter](/chapter/seesaw-squares/).

### The objects

We use the data $D$ of [the outline of Theorem C](/chapter/theorem-c-plan/). The integers $m$, $r$ and $t = 5r$ are those of [the data and their sizes](/chapter/data-and-sizes/), with $r \geq 3$. The hermitian spaces $Y_0, Y_1, \dots, Y_m$ have growing rank. The space $Y_j$ has the basis of $Y_0$ and $j$ further blocks of $t$ vectors each. An $m$-fold twist is a tame character $\vartheta$ whose tame part $\psi$ has $\psi_w^n \neq 1$ for every place $w$ of its modulus $Q$ and every $1 \leq n \leq m$. Write $\mathrm{Nm}\,Q$ for the product of the norms $q_w$ over $w \in Q$.

For an $m$-fold twist $\vartheta$, the map $\iota_\vartheta$ is the composite of the $m$ theta lifts from forms on $Y_{j-1}$ to forms on $Y_j$, $1 \leq j \leq m$ (`New.Data.lowerChainAtLevel`, [the target forms and the chain](/chapter/integral-target-forms/#the-target-forms-and-the-chain)). Its source is the space of forms of principal level at the chosen places on $Y_0$. Its target is the space of forms on $Y_m$ of the level $J_\vartheta$, which is block upper triangular at the places of $Q$. The *target forms* $T$ are the good forms on $Y_0$. They have dimension $d_T$.

**Definition (The chain on the target forms).** For an $m$-fold twist $\vartheta$, $\Theta_\vartheta$ is the restriction of $\iota_\vartheta$ to the target forms $T$.

Lean: `New.Data.Θ` (New/Determinant/Chain/NormOfChain.lean).

**Definition (Chain determinant).** The chain determinant is $Z(\vartheta) = \det(\Theta_\vartheta^*\Theta_\vartheta)$, the square of the norm determinant of $\Theta_\vartheta$.

Lean: `New.Data.chainDeterminant` (New/Determinant/Chain/NormOfChain.lean).

For $1 \leq j \leq m$, let $\Theta_{j,\vartheta}$ be the single lift from forms on $W_j$ for the twist $\vartheta$, from [single theta lifts and their norms](/chapter/single-theta-lifts/). The *good lift* is its restriction to the good forms on $W_j$ (`New.Data.goodLift`).

**Definition (Lift determinant).** For $1 \leq j \leq m$, the lift determinant $Z_j(\vartheta)$ is the square of the norm determinant of the good lift at $j$ for the twist $\vartheta^j$.

Lean: `New.Data.liftDeterminant` (New/Determinant/Chain/NormOfChain.lean).

Let $R_{j,\vartheta}$ be the series of Rallis' formula for the $j$-th lift at $\vartheta$. On the good forms it acts as an element of the spherical Hecke algebra ([the Rallis operator as a Hecke operator](/chapter/equal-multiplicities/)). So it acts on $T$ too (`New.Data.rallisOnGood`).

**Definition (Product of the Rallis operators).** For an $m$-fold twist $\vartheta$, $R(\vartheta) = R_{1,\vartheta} R_{2,\vartheta^2} \cdots R_{m,\vartheta^m}$ on $T$, the product in the order $j = 1, \dots, m$.

Lean: `New.Data.rallisProduct` (New/Determinant/Chain/NormOfChain.lean).

The constant $c_Q$ is the twist factor of the first lift ([injectivity and the norm of one lift](/chapter/single-theta-lifts/)):
$$c_Q = (\mathrm{Nm}\,Q)^{rt}\prod_{w \in Q}\ \prod_{i = t+1}^{t+r}(1 - q_w^{-i}).$$
It depends only on $Q$. The powers $\vartheta^j$ for $1 \leq j \leq m$ have the same modulus $Q$, so they have the same $c_Q$.

For $0 < i < j \leq m$ the quotient ratio $\rho_{ij}(\vartheta)$ is the product over $1 \leq z \leq t$ of the ratios of Hecke values of the character $\mu_j/\mu_i$ at the twist $\vartheta^{j-i}$. Here $\mu_j$ is the character of the $j$-th lift at the trivial twist. Section 3 gives the definition in full.

### The two main results

**Theorem (Norm of the chain).** There are a real $C > 0$, an integer $e$ and complex numbers $c(\vartheta)$ such that for every $m$-fold twist $\vartheta$
$$|c(\vartheta)| = C\,(\mathrm{Nm}\,Q)^{e/2}\prod_{0 < i < j \leq m}\rho_{ij}(\vartheta), \qquad \Theta_\vartheta^*\Theta_\vartheta = c(\vartheta)\,c_Q^m\,R(\vartheta).$$

Lean: `New.Data.exists_adjoint_chain_comp_eq_smul_rallisProduct` (New/Determinant/Chain/NormOfChain.lean).

**Theorem (Factorization of the determinant).** There is an integer $e$ such that for every $m$-fold twist $\vartheta$ the numbers $Z(\vartheta)$ and $Z_j(\vartheta)$, $1 \leq j \leq m$, are positive, and
$$\frac{Z(\vartheta)}{Z(1)} = \Big((\mathrm{Nm}\,Q)^{e/2}\prod_{0 < i < j \leq m}\rho_{ij}(\vartheta)\Big)^{d_T}\ \prod_{j=1}^{m}\frac{Z_j(\vartheta)}{Z_j(1)}.$$

Lean: `New.Data.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq` (New/Determinant/Chain/NormOfChain.lean).

Section 6 proves the first theorem, and Section 7 proves the second. Section 7 also proves the height bound for the scalar that [the plan of Theorem C](/chapter/theorem-c-plan/) uses: for a family with small ratios, the inverse of the scalar has height at most $m \cdot m \cdot (t \cdot x_1)$.

**Remark (Formalization).** The volumes have the type of complex numbers. The statement $0 < Z(\vartheta)$ uses the partial order on $\mathbb{C}$ in which $0 < z$ means that $z$ is a positive real number. The exponent $e/2$ is a real power of the positive integer $\mathrm{Nm}\,Q$, so it is defined for odd $e$ too.

### The model cases

For $m = 1$ the chain is one lift, from $Y_0$ to $Y_1$. The pair $(Y_0, Y_1)$ is in the range of Rallis' formula, and the formula gives the Gram form of the lift directly. There are no pairs $0 < i < j \leq 1$, so the product of the quotient ratios is $1$. The theorem on the norm of the chain is then the operator identity of one lift, up to the index of the level.

For $m = 2$ the chain is $Y_0 \to Y_1 \to Y_2$. The second lift starts from forms on $Y_1$, which have no Rallis formula in this range. The triangle replaces the pair $(Y_1, Y_2)$ by a pair one row lower. There, the first block of $Y_1$ is removed by a descent $d$. One square relates the two composites
$$F_{0,1} \xrightarrow{\ d\ } F_{1,0} \xrightarrow{\ a\ } F_{1,1}, \qquad F_{0,1} \xrightarrow{\ a\ } F_{0,2} \xrightarrow{\ d\ } F_{1,1}.$$
They differ by a scalar $\beta(\vartheta)$. Its modulus is the single quotient ratio $\rho_{12}(\vartheta)$, up to a power of $\mathrm{Nm}\,Q$. Section 2 shows how the scalars of all squares multiply, and why the product over $0 < i < j \leq m$ comes out.

### The plan of the chapter

Section 2 proves the abstract results on a triangle of inner product spaces: chains are injective, and their Gram forms are products of the constants of the squares. Section 3 defines the moduli of the constants and proves the facts on ratios of Hecke values that the moduli need. Section 4 builds the triangle of theta lifts and computes the Gram form of the first lift of each row. Section 5 proves the two commutation relations in the squares and checks that the lifts form a triangle. Section 6 compares $\iota_\vartheta$ with the chain of the triangle and proves the theorem on the norm of the chain. Section 7 takes determinants and passes from the operator identity to the good forms. Section 8 has exercises and notes.

The chapter imports no file that the plan of the volume puts in a later chapter.
