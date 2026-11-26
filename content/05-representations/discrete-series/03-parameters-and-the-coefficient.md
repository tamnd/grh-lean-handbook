---
title: Parameters and the coefficient
lean:
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - Lib/DiscreteSeries/Haar/CayleyChart.lean
  - Lib/DiscreteSeries/Haar/TotalMass.lean
decls:
  - New.USign
  - New.maxCompactU
  - New.HCParam.HasGap
  - New.twoRho
  - New.HCParam.lowestKType
  - New.HCParam.casimirValue
  - New.weylDimensionPoly
  - New.two_mul_lowestKType
  - New.weightMinors
  - New.HCParam.flenstedJensen
  - New.HCParam.dsCoeff
  - New.haarU
  - New.measurePreserving_haarU
  - New.isProbabilityMeasure_haarU
  - New.HCParam.formalDegree
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Parameters and the coefficient

This section gives the source's definitions: the group and its compact subgroup, the parameters and their gap, the products of principal minors, Flensted-Jensen's integral, the coefficient $c_\lambda$, the Haar measure and the formal degree. The source works with these explicit functions. It constructs no representation of $U(p,q)$, and it does not assume that the discrete series exists. Each definition below is the textbook object of [Section 2](/chapter/discrete-series/#discrete-series-of-unitary-groups) written as a formula. The model case $U(1,1)$ runs through the section.

### The group

**Definition.** For signs $\varepsilon : \{1, \dots, n\} \to \{\pm 1\}$, let $J = \operatorname{diag}(\varepsilon)$, and let $G = U(J)$ be the subgroup of $GL_n(\mathbb C)$ of the $g$ with $g^* J g = J$. Let $K$ be the subgroup of the $g \in G$ that are unitary matrices.

Lean: `New.USign` (Lib/General/Groups/CongruenceSubgroups.lean), `New.maxCompactU` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

An element of $G$ is unitary if and only if it commutes with $J$, that is, if and only if it is block diagonal for the signs. So $K \cong U(p) \times U(q)$. The source gives $K$ its Haar measure $dk$ of mass $1$ (`New.haarK`). The *block diagonal part* $a_g$ of a matrix $g$ keeps the entries $g_{ij}$ with $\varepsilon_i = \varepsilon_j$ and puts $0$ elsewhere (`New.blockDiagPart`).

### Parameters and their gap

The source stores a parameter $\lambda$ as the integer vector $l = 2\lambda$. This avoids half integers. The root $e_i - e_j$ is positive for $l$ when $l_j < l_i$.

**Definition.** An integer vector $l$ is a *parameter of gap $h$* for the signs $\varepsilon$ if three conditions hold: the entries $l_i$ are distinct; each $l_i + n - 1$ is even; and $2h \le |l_i - l_j|$ whenever $\varepsilon_i \ne \varepsilon_j$. A parameter has *large gap* $A$ if it has gap $500n^3 + A$.

Lean: `New.HCParam.HasGap` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The large gap is `New.HCParam.HasLargeGap`, and $500n^3 + A$ is `New.gapThreshold`.

With $\lambda = l/2$, the first two conditions say that $\lambda$ is a Harish-Chandra parameter: regular, with entries in $\frac{n-1}{2} + \mathbb Z$. The third says $|\lambda_i - \lambda_j| \ge h$ for entries of opposite sign. It is a condition on the distance of $\lambda$ from the walls of the noncompact roots only. The entries of equal sign can be adjacent.

**Definition.** For an integer vector $l$ and a relation $r$ on the indices, let $(2\rho^r)_i = \#\{j : r(i,j),\ l_j < l_i\} - \#\{j : r(i,j),\ l_i < l_j\}$. Let $2\rho = 2\rho^{\top}$ for the relation that always holds, and $2\rho_c$ for the relation $\varepsilon_i = \varepsilon_j$. Define

$$(\lambda + \rho)_i = \lfloor (l_i + (2\rho)_i)/2 \rfloor, \qquad \Lambda_i = (\lambda + \rho)_i - (2\rho_c)_i,$$

$$\kappa_\lambda = \sum_i \frac{l_i^2 - (2\rho)_i^2}{4}, \qquad \dim_\lambda = \prod_{l_j < l_i} \frac{l_i - l_j}{2} \Big/ \prod_{k=0}^{n-1} k!.$$

Lean: `New.twoRho`, `New.HCParam.lowestKType`, `New.HCParam.casimirValue`, `New.weylDimensionPoly` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The vector $\lambda + \rho$ is `New.paramAddRho`.

For the relation $\top$, $2\rho^\top$ is the sum of the positive roots, so it is $2\rho$ of Section 2. So $\kappa_\lambda = |\lambda|^2 - |\rho|^2$, the Casimir eigenvalue, and $\dim_\lambda$ is Harish-Chandra's formal degree for the compatible measure. The rounding in $\lambda + \rho$ does nothing for a parameter, by the parity condition.

**Lemma.** Let $l$ be a parameter of some gap $h$. Then $2\Lambda = l + 2\rho_n - 2\rho_c$ for each index, where $2\rho_n$ is $2\rho^r$ for the relation $\varepsilon_i \ne \varepsilon_j$.

Lean: `New.two_mul_lowestKType` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The step $2(\lambda + \rho) = l + 2\rho$ is `New.two_mul_paramAddRho`.

*Proof.* The number of $j$ with $l_j < l_i$, plus the number with $l_i < l_j$, plus one, is $n$. So $(2\rho)_i \equiv n - 1 \pmod 2$, and $l_i + (2\rho)_i$ is even by the parity condition. So the floor is exact. Then $2\rho = 2\rho_n + 2\rho_c$, since each $j$ has either the same sign as $i$ or the other sign. So $2\Lambda = l + 2\rho - 4\rho_c = l + 2\rho_n - 2\rho_c$. $\square$

So $\Lambda = \lambda + \rho_n - \rho_c$ is the lowest $K$-type of Section 2.

**Example.** For $U(1,1)$ with $\varepsilon = (1, -1)$ and $l = (2w_1 + 1, 2w_2 - 1)$, $w_2 > w_1$: the only positive root is $e_2 - e_1$. So $2\rho = (-1, 1)$, $2\rho_c = 0$, $\lambda + \rho = \Lambda = (w_1, w_2)$, $\kappa_\lambda = w_1^2 + w_1 + w_2^2 - w_2$ and $\dim_\lambda = w_2 - w_1 - 1$. The gap condition $2h \le |l_1 - l_2| = 2(w_2 - w_1 - 1)$ says $h \le w_2 - w_1 - 1$.

### Products of principal minors

For a set $S$ of indices and a square matrix $g$, let $\Delta_S(g)$ be the principal minor of $g$ on $S$, the determinant of the submatrix with rows and columns in $S$. So $\Delta_\emptyset(g) = 1$ (`New.principalMinor`).

**Definition.** For an integer vector $w$ and a square matrix $g$,

$$m_w(g) = \prod_{t \in \mathbb Z} \frac{\Delta_{\{i : t \le w_i\}}(g)}{(\det g)^{[t \le 0]}},$$

where $[t \le 0]$ is $1$ if $t \le 0$ and $0$ otherwise. The product is a finite product when almost all factors are $1$.

Lean: `New.weightMinors` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

Let $g$ be invertible. For $t > \max w$ the set is empty and the factor is $1$. For $t \le \min(0, \min w)$ the set is everything and the factor is $\det g/\det g = 1$. So the product is finite. Order the indices so that $w_{(1)} \ge w_{(2)} \ge \dots \ge w_{(n)}$, and let $\Delta_k$ be the minor on the first $k$ indices in this order. Counting the values of $t$ for each set gives

$$m_w(g) = \Delta_1(g)^{w_{(1)} - w_{(2)}} \cdots \Delta_{n-1}(g)^{w_{(n-1)} - w_{(n)}}\,(\det g)^{w_{(n)}}.$$

This is the classical formula for the coefficient of a highest weight vector of $GL_n$ with highest weight $w$, extended to weights with negative entries by the power of the determinant. For $n = 1$, $m_w(g) = g^w$. For $n = 2$ and $w_1 \ge w_2$, $m_w(g) = g_{11}^{w_1 - w_2}(\det g)^{w_2}$.

**Remark (Formalization).** The product over $t$ is Mathlib's `finprod`, which is $1$ when infinitely many factors differ from $1$. For a singular matrix $g$, each factor with $t \le \min(0, \min w)$ is $0/0 = 0$ in Lean, so infinitely many factors are $0$, and the junk value of $m_w(g)$ is $1$. The source uses $m_w$ only at invertible matrices: elements of $G$ or $K$, accretive matrices, and their products with invertible block diagonal matrices. So the junk value does not enter any statement of this chapter.

### Flensted-Jensen's integral and the coefficient

**Definition.** For a parameter $l = 2\lambda$ and square matrices $a, z$, let

$$\Xi_\lambda(a, z) = \frac{1}{\int_K |m_\Lambda(k)|^2\,dk}\int_K \frac{m_\Lambda(ak)\,\overline{m_\Lambda(k)}}{m_{-(\lambda+\rho)}(k^* z k)}\,dk.$$

Lean: `New.HCParam.flenstedJensen` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The normalising integral $\int_K |m_\Lambda|^2$ is `New.HCParam.kTypeNormSq`.

**Definition.** For a parameter $l = 2\lambda$ and a square matrix $g$, let $c_\lambda(g) = \Xi_\lambda(a_g, a_g^{-1} g)$, where $a_g$ is the block diagonal part of $g$.

Lean: `New.HCParam.dsCoeff` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

The idea is this. The numerator $m_\Lambda(ak)\overline{m_\Lambda(k)}$ is a coefficient of the $K$-type $\Lambda$, extended holomorphically in $a$. The denominator is a coefficient of weight $-(\lambda + \rho)$, a lowest weight vector for the full group, evaluated at $k^* z k$. Averaging over $K$ projects to the $K$-type $\Lambda$. By Schur orthogonality for $K$, the factor $1/\int_K |m_\Lambda|^2$ is the dimension of the $K$-type $\Lambda$. For $g$ in $G$ the matrix $a_g^{-1}g$ is accretive: $z + z^*$ is positive definite. An accretive matrix has nonzero principal minors, so the integrand is continuous.

Section 4 shows that the value does not depend on the splitting $g = a \cdot (a^{-1}g)$: any $g = pzq^*$ with $p, q$ block diagonal and $z$ accretive gives the same integral ([Theorem](/decl/New.dsCoeff_eq_integral_of_eq_mul_mul_conjTranspose/)).

**Example.** Take $U(1,1)$ with $\Lambda = (w_1, w_2)$ and $w_2 - w_1 = k \ge 2$. For $u = \operatorname{diag}(e^{i\alpha}, e^{i\beta})$ in $K$, $m_\Lambda(u) = e^{i(w_1\alpha + w_2\beta)}$, so $\int_K |m_\Lambda|^2 = 1$. Let $g \in G$. Then $a_g = \operatorname{diag}(g_{11}, g_{22})$, and $z = a_g^{-1}g$ has diagonal entries $1$ and $\det z = \det g/(g_{11}g_{22})$. The numerator is $m_\Lambda(a_g u)\overline{m_\Lambda(u)} = g_{11}^{w_1}g_{22}^{w_2}$. The vector $-(\lambda + \rho) = (-w_1, -w_2)$ has $-w_1 > -w_2$, so $m_{-(\lambda+\rho)}(x) = x_{11}^{k}(\det x)^{-w_2}$. At $x = u^* z u$ this is $(\det g/(g_{11}g_{22}))^{-w_2}$. The integrand does not depend on $u$, and

$$c_\lambda(g) = g_{11}^{w_1}g_{22}^{w_2}\Big(\frac{\det g}{g_{11}g_{22}}\Big)^{w_2} = g_{11}^{-k}(\det g)^{w_2}.$$

This is the coefficient of the holomorphic discrete series of [Section 2](/chapter/discrete-series/#discrete-series-of-unitary-groups).

**Remark (Formalization).** The source has no representation $\pi_\lambda$ and no Hilbert space. The function $c_\lambda$ is defined by the integral for every integer vector $l$, also when $l$ is not a parameter. All results that give it meaning assume a gap. Classically $c_\lambda$ is the coefficient of a unit vector of the lowest $K$-type, and the source's docstrings say so. In the source this is a motivation, not a statement. In place of the representation, the source proves the properties of a coefficient for $c_\lambda$ directly, and it builds the module $U(\mathfrak g)c_\lambda$ inside $L^2(G)$ ([Theorem](/decl/New.HCParam.HasLargeGap.isUnitaryCasimirGe_dsAction/)). The later volumes use only the function $c_\lambda$, the kernel $e_\lambda$ and the formal degree.

### The Haar measure

The measure on $G$ comes from a Cayley chart. For a matrix $y$ in an open dense set of real coordinates, the chart gives an element of $U(J)$, and the measure is the image of Lebesgue measure with the Jacobian density, divided by a constant.

**Definition.** Let $\operatorname{vol}_U(n) = \prod_{i=0}^{n-1} 2\pi^{i+1}/i!$. The measure $\mu_J$ on $U(J)$ is the image under the Cayley chart of Lebesgue measure with density the Jacobian of the chart divided by $\operatorname{vol}_U(n)$.

Lean: `New.haarU` (Lib/DiscreteSeries/Haar/CayleyChart.lean). The constant is `New.volU`.

The number $2\pi^{i+1}/i!$ is the area of the unit sphere in $\mathbb C^{i+1}$, so $\operatorname{vol}_U(n)$ is the volume of $U(n)$ for the metric of the chart. The source proves the invariance and the mass.

**Theorem.** Let $J, J'$ be hermitian involutions, $a, b$ invertible matrices and $e$ a nonzero real number with $b^*(eJ)b = J'$. Let $\varphi : U(J) \to U(J')$ be a bijection with $\varphi(g) = agb$ for all $g$. Then $\varphi$ carries $\mu_J$ to $\mu_{J'}$.

Lean: `New.measurePreserving_haarU` (Lib/DiscreteSeries/Haar/CayleyChart.lean).

The cases $b = 1$, and $a = 1$ with $J' = J$, are left and right invariance. So $\mu_J$ is a Haar measure for every hermitian involution $J$, in particular for $J = \operatorname{diag}(\varepsilon)$.

**Theorem.** The measure $\mu_1$ on the compact unitary group $U(n)$ has total mass $1$.

Lean: `New.isProbabilityMeasure_haarU` (Lib/DiscreteSeries/Haar/TotalMass.lean).

*Proof.* The source computes the image of Lebesgue measure under the Gram map $Y \mapsto Y^*Y$ near the identity in two ways. One column of $Y$ ranges over a sphere, and the parts of the other columns orthogonal to it form a square matrix of size $n - 1$. Induction on $n$ gives the constant $\operatorname{vol}_U(n)/2^n$ (`New.exists_hasGramDensity`). The polar formula $Y = u\,(Y^*Y)^{1/2}$ with $u \in U(n)$ gives the same image with the factor $\mu_1(U(n))\operatorname{vol}_U(n)/2^n$. So $\mu_1(U(n)) = 1$. $\square$

The chart is the same for $U(J)$ and for $U(n)$, and the density has the same form. So $\mu_J$ is the measure *normalised by the compact dual*: it is compatible, in the sense of Section 2, with the measure of mass $1$ on $U(n)$. This is the normalisation of Harish-Chandra's formula.

**Remark (Formalization).** The source makes $\mu_J$ the `volume` of $U(J)$ by a global instance, for every matrix $J$. It is a Haar measure only when $J$ is a hermitian involution; for other $J$ the instance is still there, but no theorem uses it. For $G = U(\operatorname{diag}\varepsilon)$ it is a Haar measure by the theorem above. All integrals over $G$ in this chapter are for this measure.

### The formal degree and the kernel

**Definition.** For a parameter $l = 2\lambda$, the *formal degree* is $d_\lambda = \big(\int_G |c_\lambda(g)|^2\,dg\big)^{-1}$, and the *kernel* is $e_\lambda(g) = d_\lambda\,\overline{c_\lambda(g)}$.

Lean: `New.HCParam.formalDegree` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean). The kernel is `New.HCParam.dsKernel`.

**Remark (Formalization).** The Bochner integral in Lean is $0$ for a function that is not integrable, and $0^{-1} = 0$. So if $|c_\lambda|^2$ is not integrable, the formal degree is $0$ and the kernel is $0$. This is a junk value. The source proves $d_\lambda > 0$ for a large gap ([Theorem](/decl/New.formalDegree_pos/)), and every theorem that uses $d_\lambda$ assumes a large gap. A reader who meets `formalDegree` in a later volume should check that a gap hypothesis is present.

**Remark (Formalization).** The gap is a type class `HasGap h` whose argument $h$ is an output parameter. So Lean finds the gap from the parameter. The later volumes declare instances for their parameters (for example `New.Data.hasGap_paramW` in New/UpperBound/Objects/Rows.lean), and the results of this chapter then apply without an explicit hypothesis. The large gap `HasLargeGap A` is an abbreviation for `HasGap (500n^3 + A)`.
