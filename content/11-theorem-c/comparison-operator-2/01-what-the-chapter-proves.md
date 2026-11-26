---
title: What the chapter proves
lean:
  - New/OneLift/ComparisonOperator/ThreeExchanges.lean
  - New/OneLift/ComparisonOperator/ProductsSpan.lean
  - New/OneLift/ComparisonOperator/GluingMaps.lean
decls:
  - New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn
  - New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing
  - New.Rows.twistFactor_smul_adjoint_glue_comp
  - New.Rows.twistFactor_ne_zero
  - New.Rows.normSqAt_glue_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Input 4 of [the plan of Theorem C](/chapter/theorem-c-plan/) asks for a comparison operator $U_\vartheta = n_{\mathrm{Aut}}\,h_j^2\,\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*$ on the forms on $V_j$. [The first part](/chapter/comparison-operator-1/) gave the tools: glued lattices, the descent of product forms, sparse theta kernels, isolation at a peak and the first factors. This chapter puts the tools together. It builds the gluing map $\mathrm{glue}_\vartheta$ and proves the properties that the chapter [the height of one lift determinant](/chapter/lift-volume-height/) uses to show that $U_\vartheta$ is a comparison operator.

The chapter has three parts, one for each source file.

1. *Three exchanges* (Sections 2 to 4). The exchange identity of [the exchange identity, part 2](/chapter/exchange-identity-2/) is applied three times. After the first two exchanges, a class sum of twisted kernels on the space $S$ of signature $(2m, m)$ is a number times the carrier $\varphi^\circ$, the theta lift of $1$ from $U(0, m)$. After the third exchange, a double class sum of kernels is a number times the function $\mathsf{F}_i$ on $U(W_j)$, which does not depend on the twist. The modulus of the product of the three numbers is a product $\Gamma_j(\vartheta)$ of Hecke values at three pairs.
2. *Products span* (Sections 5 and 6). A good form $F$ on $W_j$ with $\int F\,\mathsf{F}_i\,\theta^\circ = 0$ for all $i$ is $0$. Here $\theta^\circ$ is the theta kernel of $(W_j, V^\circ)$.
3. *Gluing maps* (Sections 7 and 8). The first factors on $V''$ are glued to tuples of forms on $V^\circ$. This gives the linear map $\mathrm{glue}_\vartheta$. Its adjoint, applied to the good lift, is a fixed injective map $\Theta^\circ$ up to a nonzero scalar $c'_\vartheta$.

Each section has its own examples. Section 9 has the exercises and the notes.

### The main statements

We state the five results that the later chapters use. The notation is defined in the sections that prove them.

**Theorem (The three exchanges).** There are a number $C$ and a function $c$ on the twists such that for every twist $\vartheta$ we have $|c_\vartheta|^2 = C/\Gamma_j(\vartheta)$, and $c_\vartheta$ times the left side of the third exchange at $(i, g)$ is $\mathsf{F}_i(g)$, for every choice $i$ and every $g$.

Lean: `New.Data.exists_mul_thirdExchangeLeftSide_eq_choiceFn` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

The proof is in [Section 4](/chapter/comparison-operator-2/#the-third-exchange).

**Theorem (Products span).** Let $F$ be a good form on $W_j$. Suppose that $\int F(g)\,\mathsf{F}_i(g)\,\Theta(\zeta)(g)\,dg = 0$ for every choice $i$ and every family $\zeta$ of values on the classes of $U(V^\circ)$, where $\Theta(\zeta)$ is the pairing of $\zeta$ with the kernel $\theta^\circ$. Then $F = 0$.

Lean: `New.Data.eq_zero_of_integral_choiceFn_thetaKernelPairing` (New/OneLift/ComparisonOperator/ProductsSpan.lean).

The proof is in [Section 6](/chapter/comparison-operator-2/#products-span).

**Theorem (The seesaw).** For every twist $\vartheta$, $c'_\vartheta\,\mathrm{glue}_\vartheta^* \circ \Theta_{j,\vartheta} = \Theta^\circ$ as maps from the good forms on $W_j$ to the form tuples. Here $\Theta_{j,\vartheta}$ is the good lift, $c'_\vartheta$ is the twist factor and $\Theta^\circ$ is the period lift.

Lean: `New.Rows.twistFactor_smul_adjoint_glue_comp` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Theorem (The twist factor is not zero).** For every twist $\vartheta$, $c'_\vartheta \neq 0$.

Lean: `New.Rows.twistFactor_ne_zero` (New/OneLift/ComparisonOperator/GluingMaps.lean).

**Theorem (The gluing map is short).** For every form tuple $\zeta$ and every automorphism $\sigma$ of $\mathbb{C}$, the squared norm of $\mathrm{glue}_1\zeta$ at $\sigma$ is at most $\exp(2fmb\log^2 b)\,\|\zeta\|_\sigma^2$.

Lean: `New.Rows.normSqAt_glue_le` (New/OneLift/ComparisonOperator/GluingMaps.lean).

The last three are proved in [Section 8](/chapter/comparison-operator-2/#integrality-false-lifts-and-the-seesaw).

### A sketch

The source claims the following route. The adjoint of $\mathrm{glue}_\vartheta$ applied to a good lift $\Theta_{j,\vartheta}y$ is, by the seesaw, an integral of $y$ times the descent of $\mathrm{glue}_\vartheta\zeta$. The descent of a product form on a glued lattice is a sum of products of a kernel on $(W_j, V'')$ and a kernel on $(W_j, V^\circ)$, by [the descent of product forms](/chapter/comparison-operator-1/#descent-of-product-forms). The kernel on $(W_j, V'')$, paired with a first factor, is the theta series $\Xi_{\vartheta,i}$. The three exchanges show that $c'_\vartheta\,\Xi_{\vartheta, i} = c''\,\mathsf{F}_i$, where $c''$ is the scale of the first factors. So the twist enters only through the number $c'_\vartheta$. The result is $\Theta^\circ y$, a family of integrals $\int y\,\mathsf{F}_i\,\theta^\circ$.

The map $\Theta^\circ$ is injective because products span. The proof of that is by contradiction. If $F \neq 0$, pick a peak of $F$. A combination of the $\mathsf{F}_i$ is close to a fixed function $\mathsf{F}^0$ near every peak, by the sparse sums of [the first part](/chapter/comparison-operator-1/#sparse-theta-kernels). The orthogonality and the isolation estimate then force $\mathsf{F}^0(1)$ to be smaller than itself.

Injectivity gives $c'_\vartheta \neq 0$: if $c'_\vartheta = 0$, the seesaw makes $\Theta^\circ = 0$, so the space of good forms is $0$. But that space has positive dimension.

### Where the results go

The chapter [the height of one lift determinant](/chapter/lift-volume-height/) builds the comparison operator from $\mathrm{glue}_\vartheta$ and $\Theta^\circ$. Property 1 of [the definition](/chapter/theorem-c-plan/#the-four-inputs) uses $\Gamma_j(\vartheta) \neq 0$. Property 2 uses the seesaw and the injectivity of $\Theta^\circ$. Property 3 uses `New.Rows.isOrthogonalToFalseLifts_glue_periodLift`. Property 4 uses `New.Rows.glue_mem_integralForms`. Property 5 uses the bound on $\mathrm{glue}_1$. The chapter [twisting theorem](/chapter/twisting-theorem/) of Volume 12 uses the first exchange, `New.Rows.exists_mul_stdClassSum_modKernelStdSpace_eq_one`, which we prove in [Section 3](/chapter/comparison-operator-2/#the-carrier).

### Imports

`ThreeExchanges` imports the exchange identity, the explicit matching and the first factors. `ProductsSpan` imports `ThreeExchanges`, the sparse theta kernel estimates and the Bruhat theory of the complex place. `GluingMaps` imports `ProductsSpan`, the glued forms, the norm of a chain and the spanning theorem.

`GluingMaps` also imports `New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean`. `volume.yaml` puts that file in [false lifts](/chapter/false-lifts/), which comes before this chapter in the volume but is being written now. We state the two results that we use from it once, in [Section 8](/chapter/comparison-operator-2/#integrality-false-lifts-and-the-seesaw), with a link.

### Background

- Twists, critical pairs and products of $L$-values: [critical pairs and the ratio](/chapter/twists-critical-pairs/#critical-pairs-and-the-ratio).
- Good forms, good lifts and the descent: [single theta lifts](/chapter/single-theta-lifts/).
- The exchange identity and the exchange data, with $\varphi^\circ$, $\mathsf{a}$ and $\mathsf{F}_i$: [one exchange and the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data).
- The reproducing formula of theta kernels: [neighbours and reproduction](/chapter/siegel-weil/) in Volume 6.
- Holomorphic discrete series and the functions $m_u$: [discrete series](/chapter/discrete-series/) in Volume 5.
- The data and the sizes $b$, $t$, $n_*$: [the data and its sizes](/chapter/data-and-sizes/).
