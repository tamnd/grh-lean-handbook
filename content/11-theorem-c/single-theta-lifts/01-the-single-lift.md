---
title: The single lift and its place in the argument
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
  - New/Determinant/Norms/VectorKernel.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/Determinant/Chain/NormOfChain.lean
decls:
  - New.Data.singleLift
  - New.Data.goodLift
  - New.Data.liftDeterminant
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The single lift and its place in the argument

This chapter is about one theta lift. Fix the data of the source, a tame character $\vartheta$ and an index $1 \leq j \leq m$. The single lift $\Theta_{j,\vartheta}$ takes the forms of level $J_M$ on the hermitian space $W_j$, of rank $r$, to algebraic forms on the definite space $V_j = I_{r+t}$, of rank $r + t$. The chapter defines this lift, finds its adjoint, proves that it is injective, and computes its Gram form $\langle\Theta_{j,\vartheta}x, \Theta_{j,\vartheta}y\rangle$ as a sum over cosets. It also gives the Hecke polynomials of the lifted forms.

The plan of the whole proof is in [the theorem and its plan](/chapter/theorem-and-plan/). The plan of this volume is in [Theorem C and the height argument](/chapter/theorem-c-plan/). The twists $\vartheta$ and their sets $Q$ are in [twists, critical pairs and regular families](/chapter/twists-critical-pairs/).

### Why one lift matters

Theorem C is a lower bound for the covolume of the integral target forms. The volume of the target lattice at a twist $\vartheta$ is $Z(\vartheta) = \det(\Theta_\vartheta^*\Theta_\vartheta)$, where $\Theta_\vartheta$ is a chain of $m$ theta lifts. The chapter [the chain determinant and its factorization](/chapter/chain-determinant/) factors $Z(\vartheta)$ into the determinants $Z_j(\vartheta)$ of single lifts and a scalar. This chapter supplies the single lifts and three facts about them.

1. Each single lift is injective. So the Gram determinant $Z_j(\vartheta)$ is not $0$, and the chain is injective.
2. For each $j$ there is one constant $c_j \neq 0$ such that $\Theta_{j,\vartheta}^*\Theta_{j,\vartheta} = c_j\,c_Q(\vartheta)\,R_{j,\vartheta}$ for every tame $\vartheta$. Here $c_Q(\vartheta)$ is an explicit number of the places of $\vartheta$, and $R_{j,\vartheta}$ is the series of Rallis' inner product formula. The constant $c_j$ does not depend on $\vartheta$. So it cancels in the ratios $Z(1)/Z(\vartheta)$ that Theorem C bounds.
3. The lifted forms have known Hecke polynomials. At $X = (\alpha q^{t-1})^{-1}$ the Hecke polynomial operator kills every lift. The chapter [the height of one lift determinant](/chapter/lift-volume-height/) uses this to separate the lifts from other forms.

**Definition (The single lift).** For a tame character $\vartheta$ and $j \in \mathbb{N}$, the single lift $\Theta_{j,\vartheta}$ is a linear map from the forms of level $J_M$ on $W_j$ to the forms on $V_j$ of the $j$-th descent pair at $\vartheta$. For $1 \leq j \leq m$ it is the restriction of the lift $\Theta_W$ of that pair. For other $j$ it is $0$.

Lean: `New.Data.singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

**Remark (Formalization).** Lean defines `D.singleLift ϑ j` for every natural number $j$ by a `dite` on $j \in \mathrm{LiftIndex} = [1, m]$. The value $0$ outside this range is a junk value. Every theorem of this chapter takes $j$ in `D.LiftIndex`, so the junk value never enters a statement.

**Definition (The good lift and its determinant).** The good lift is the single lift restricted to the good forms on $W_j$, the image of the idempotent $e_0$ on the forms of level $J_M$. For an $m$-fold twist $\vartheta$, the determinant $Z_j(\vartheta)$ is the square of the determinant norm of the good lift at the twist $\vartheta^j$.

Lean: `New.Data.goodLift` (New/Determinant/Twist/FitTwists.lean), `New.Data.liftDeterminant` (New/Determinant/Chain/NormOfChain.lean).

This chapter works with the single lift on all forms of level $J_M$, not only on the good forms. The results restrict to the good forms with no change. The volume uses them in that form.

### The model case

Here is the shape of the argument in the simplest case. Let $W$ be a positive definite hermitian space of rank $r$ over $\mathbb{Q}(i)$, and let $V$ be the standard space of rank $n = r + t$ with $n > 2r$. A theta kernel $\theta(g, h)$ on $U(W) \times U(V)$ is made from a Schwartz function $\phi$ on $\mathrm{Hom}(W, V)$. The lift of a form $y$ on $W$ is

$$\Theta y(h) = \int_{[U(W)]} y(g)\,\theta(g, h)\,dg.$$

Its adjoint is the descent $\theta\Xi(g) = \int_{[U(V)]} \overline{\theta(g, h)}\,\Xi(h)\,dh$, read with the right conjugations. Rallis' inner product formula says that

$$\langle\Theta y', \Theta y\rangle = C\cdot\langle y', \mathcal{E}\,y\rangle,$$

where $\mathcal{E}$ is an operator built from the local matrix coefficients of $\phi$. When $\phi$ is the vacuum at almost all places, $\mathcal{E}$ is a convergent sum of Hecke operators. If $\phi$ is chosen at the bad places so that its matrix coefficient is the indicator function of one open compact group $J$, then on forms fixed by $J$ the formula becomes exact and $\mathcal{E}$ is injective. Then $\Theta y = 0$ forces $y = 0$.

The source follows this model. The space $V$ is definite, so the forms on $V$ are functions on a finite set of classes. The integral over $[U(V)]$ becomes a finite class sum. The datum $\phi$ is the block datum $\Psi_{\mathrm{bl}}$ at the places of $M$ and $Q$, and the vacuum elsewhere. Section 4 proves that $\Psi_{\mathrm{bl}}$ is sharp for $J_M$: its matrix coefficient is a constant times the indicator of $J_M$.

### What this chapter takes from other volumes

The descent pair, its spaces, its characters $\nu_W$ and $\nu_V$, its datum and its descent are defined in [the objects of the upper bound](/chapter/upper-bound-objects/). Section 2 recalls them in short form.

The theta lift of forms, edges and arrows are in [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/).

Rallis' inner product formula for sharp data, the vacuum coefficients and the Rallis series are in [the Rallis inner product formula](/chapter/rallis-inner-product/). Section 5 states the one result that this chapter applies.

The file of this chapter imports the file of [character lifts and tested forms](/chapter/character-lifts/), the next chapter of this volume, because two general lemmas on descent pairs are stated there. Section 3 uses the first, which turns the class sum on $V$ into a Petersson product. Section 6 uses the second, which says that the Hecke polynomial at the root of a lift kills every form with the Hecke polynomials of a lift. Neither lemma depends on the results of this chapter.

### The sketch

1. Section 2 recalls the descent pair $(W, V)$ and builds the vector kernel $\theta_W(g, \cdot)$, a form on $V$ for each point $g$ of $U(W)$. The descent $\theta\Xi(g)$ is the inner product of $\theta_W(g, \cdot)$ with $\Xi$.
2. Section 3 defines $\Theta_W$ and the single lift. It proves that the descent is the adjoint of the lift and that the lift is the integral of $y(g)\,\theta_W(g, \cdot)$. The lift commutes with the finite group $\prod_{w \in M}\mathrm{GL}_r(k_w)$.
3. Section 4 counts the block datum. Its squared norm is $|\prod_Q\mathrm{GL}_r(k_w)|\,(\mathrm{Nm}\,Q)^{tr}$, it is sharp for $J_M$, and its mass factors into a part from $M$ and the twist factor $c_Q$.
4. Section 5 applies Rallis' formula. It gets the injectivity of $\Theta_{j,\vartheta}$, the Gram form as a sum of coset terms, and the operator identity $\Theta^*\Theta = c_j c_Q R$.
5. Section 6 transfers Hecke polynomials from $W_j$ to $V_j$ and gives the root of the lift.
6. Section 7 has exercises and notes.

### Notation

The book writes $O$ for a descent pair, $W$ for its first space, of rank $r$, and $V = I_n$ for its second space, of rank $n = r + t$. It writes $M$ for the chosen places and $Q$ for the places of the twist. The modulus $\pi_M Q$ is the product of the primes of $M$ and $Q$. The level $J_M$ is the group of integral points of $U(W)$ that reduce to $1$ at every place of $M$. For a finite place $w$, $q_w$ is its norm and $k_w$ its residue field.

The book writes $\Theta_W$ for the lift of a pair, $\Theta_{j,\vartheta}$ or $\Theta_j$ for the single lift, and $\theta$ for the descent. The inner product of Mathlib is conjugate linear in the first variable. So $\langle x, y\rangle$ is linear in $y$.
