---
title: What the chapter proves
lean:
  - New/OneLift/ComparisonOperator/GluedLattices.lean
  - New/OneLift/ComparisonOperator/GluedForms.lean
  - New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean
  - New/OneLift/ComparisonOperator/LineCoordinates.lean
  - New/UpperBound/Kernels/DefiniteKernelSize.lean
  - New/OneLift/ComparisonOperator/FirstFactors.lean
decls:
  - New.Rows.DividedSplitting.exists_isGlued
  - New.Rows.DividedSplitting.normalizedDescent_productForm
  - New.Rows.exists_norm_modKernel_sub_fockInner_le
  - New.Data.norm_apply_one_le_of_forall_isPeak
  - New.Data.exists_isIntegralAndSmall_leftSideSeries
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Input 4 of [the plan of Theorem C](/chapter/theorem-c-plan/) asks for a *comparison operator* $U_\vartheta$ on the forms on $V_j$, one for each twist $\vartheta$. The operator is $U_\vartheta = n_{\mathrm{Aut}}\,h_j^2\,\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*$. Here $\mathrm{glue}_\vartheta$ builds a form on $V_j$ from forms on two smaller definite spaces. This chapter and [the second part](/chapter/comparison-operator-2/) build $\mathrm{glue}_\vartheta$ and prove the five properties of the definition. This chapter gives the tools. The second part puts them together.

The tools are of four kinds.

1. *Glued lattices* (Sections 2 and 3). A form on $V = V'' \oplus V^\circ$ that is a product of a form on $V''$ and a form on $V^\circ$ lives on a lattice of $V$. The theta datum of the lift from $W$ to $V$ asks for a congruence modulo $\varpi$ on the whole lattice. We construct a lattice $\gamma\,\mathcal{O}^n$ on which this one congruence splits into two congruences, one on each block.
2. *Descent of product forms* (Section 4). On a glued lattice the descent to $W$ of a product form is a sum, over a finite congruence group, of products of two theta kernels: one for $(W, V'')$ and one for $(W, V^\circ)$. We also bound the denominator that the change of lattice costs.
3. *Archimedean estimates* (Sections 5 and 6). The Heisenberg coefficients of a homogeneous Fock vector decay fast. So a theta kernel over a lattice with no short vectors is close to one Fock coefficient. An isolation estimate for holomorphic discrete series then turns closeness at every peak into a bound at $1$.
4. *First factors* (Sections 7 and 8). We define a polynomial map $\zeta$, a datum $\Psi^{\mathrm{add}}$ and a series $\Upsilon$ of theta kernels of definite spaces. One constant $c \neq 0$ makes every first factor $\overline{c\,\Upsilon}$ integral away from the twist places and, for the trivial twist, small under every automorphism of $\mathbb{C}$.

### The main statements

We state the five results that the second part uses most. The notation is defined in the sections that prove them.

**Theorem (Glued lattices exist).** Let $V$ be a divided splitting $N \sqcup m \simeq n$ of a descent pair $O$, and let $s$ be an $a \times N$ matrix modulo $\varpi^2$. Then some divided lattice $L$ is glued for $s$.

Lean: `New.Rows.DividedSplitting.exists_isGlued` (New/OneLift/ComparisonOperator/GluedLattices.lean).

The proof is in [Section 3](/chapter/comparison-operator-1/#glued-lattices).

**Theorem (Descent of a product form).** Let $L$ be glued for $s$, and let the characters $b$, $b'$ have product $\nu_V$. The descent to $W$ of the product form of $y$ and $\eta$ at $(h, h')\gamma$ is the complex conjugate of $c_\gamma$ times a sum over the congruence group $\Gamma$ of products of a kernel for $(W, V'')$ and a kernel for $(W, V^\circ)$.

Lean: `New.Rows.DividedSplitting.normalizedDescent_productForm` (New/OneLift/ComparisonOperator/GluedForms.lean).

The exact form is in Section 4.

**Theorem (Sparse theta kernels).** If the lattice of $\mathrm{Hom}(S, T)$ at $(g, h)$ has no vectors shorter than $m$ in a suitable scale, some finite datum $\Psi$ makes the theta kernel at $(gu, hu')$ differ from the Fock coefficient $\langle v, \Omega(u, u')v\rangle$ by at most $\|u'\|^{3q}(100(d+2q)/m^2)^q\,|\langle v, v\rangle|\,\|u\|^{3q}$.

Lean: `New.Rows.exists_norm_modKernel_sub_fockInner_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

**Theorem (Isolation).** Let $F$ be holomorphic of weight $u$ with a peak, and let $K_0$ be bounded. If at every peak $x$ some $K$ within $\delta|h|^{6n_*}$ of $K_0$ has $\int \overline{F(xh)}K(h)m_{u'}(h)\,dh = 0$, then $|K_0(1)| \leq (4b^{n_*}+1)\delta$.

Lean: `New.Data.norm_apply_one_le_of_forall_isPeak` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

**Theorem (The first factors are integral and small).** For $1 \leq j \leq m$ there is $c \neq 0$ such that for every choice $i$, twist $\vartheta$ and point $h$, the vector $\overline{c\,\Upsilon_{\vartheta, j}(i, h)}$ is integral at $h$ at every prime prime to $\mathrm{Nm}\,Q(\vartheta)$. If $Q(\vartheta) = \varnothing$, every conjugate of it has squared norm at most $\exp(f m b \log^2 b)$.

Lean: `New.Data.exists_isIntegralAndSmall_leftSideSeries` (New/OneLift/ComparisonOperator/FirstFactors.lean).

The sizes $f$, $m$, $b$ and $\log b$ are those of [the data and their sizes](/chapter/data-and-sizes/).

### A sketch

The comparison operator compares the lift $\Theta_{j,\vartheta}$ with the lift $\Theta_{j,1}$. A twist by $\vartheta$ changes the theta datum at the places of $Q(\vartheta)$. The idea is to factor the target space as $V_j = V'' \oplus V^\circ$ and to write a test form as a product. The factor on $V^\circ$ carries the twist. The factor on $V''$ is the same for all twists. So a form $\varphi''$ on $V''$, the *first factor*, is fixed once, and only the factor on $V^\circ$ moves with $\vartheta$.

Two problems come up. First, the theta datum for $(W, V)$ is a congruence modulo $\varpi$ on matrices $x$ of size $n \times r$, and this congruence does not respect the splitting of $V$. Sections 2 and 3 solve this. They change the lattice at the chosen places by a matrix $\gamma$ with $\varpi\gamma^{-1}$ integral. On the lattice $\gamma\mathcal{O}^n$ the congruence becomes two block conditions modulo $\varpi^2$, up to a unique element of a congruence group $\Gamma$. Section 4 reads off the descent, and it bounds the cost of $\gamma$ in the $p$-adic gauge: a power $\|M\|^{-e}$ with an explicit exponent $e$.

Second, property 5 of the comparison operator is a size bound for every conjugate. The first factor must be small for all $\sigma \in \mathrm{Aut}(\mathbb{C})$, and integral at all good primes. Sections 7 and 8 build it from theta kernels of definite spaces, where the theta series are finite sums of explicit values. The size of a definite kernel is controlled by its normalising constant, its datum and the size of its polynomial. The polynomial is a product of determinants. Its coordinates $\zeta$ in the Weyl module have bounded norm, a fixed degree and a bounded denominator.

Sections 5 and 6 prepare the proof in the second part that the products span. A theta kernel over a sparse lattice is close to a single Fock coefficient. A mean over additive characters produces such a kernel. The isolation estimate is the last step: a holomorphic form that is orthogonal to such kernels at all its peaks forces the kernel to be small at $1$.

### Where the results go

All results of this chapter are used in [the comparison operator, part 2](/chapter/comparison-operator-2/). The glued lattices and the descent of product forms enter the construction of the gluing maps (`GluingMaps`). The estimates of Sections 5 and 6 enter the proof that the products span (`ProductsSpan`). The first factors enter the third exchange (`ThreeExchanges`), where the first factors fix the scalar between twisted and untwisted theta forms.

### Imports

No file of this chapter imports a file that `volume.yaml` puts in a later chapter of Volume 11. The files import the exchange data and determinant products of [the exchange identity, part 2](/chapter/exchange-identity-2/), the tested forms of [character lifts](/chapter/character-lifts/), the fit twists of [twists and critical pairs](/chapter/twists-critical-pairs/), files of Volume 9 and files of the library. Two merged chapters cite this chapter for results that are in the second part. We state them in [the notes](/chapter/comparison-operator-1/#notes-and-references).

### Background

The background is in Volumes 4 to 6. The adelic unitary groups and the levels are in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) and [congruence subgroups](/chapter/congruence-subgroups/). The Weil representation and the Fock model are in [the Weil representation](/chapter/weil-representation/). The Weyl modules and their Gram matrices are in [Weyl modules](/chapter/weyl-modules/). Holomorphic discrete series and formal degrees are in [discrete series](/chapter/discrete-series/). The theta kernels and the gauge are in [theta kernels and gauges](/chapter/theta-kernels-gauges/).
