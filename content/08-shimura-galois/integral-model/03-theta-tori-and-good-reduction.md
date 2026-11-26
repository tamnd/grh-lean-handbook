---
title: Theta tori and good reduction
lean:
  - Lib/Shimura/ThetaModuli/PELThetaTori.lean
  - Lib/Shimura/GoodReduction/TorsionSizes.lean
  - Lib/Shimura/GoodReduction/GaussSums.lean
  - Lib/Shimura/GoodReduction/MultiplicativeNorm.lean
decls:
  - New.ThetaTori.PeriodMap
  - New.ThetaTori.ThetaTorus
  - New.ThetaTori.PeriodMap.thetaCoord
  - New.ThetaTori.LatticeForm.sizeAt
  - New.ThetaTori.HasMultiplicativeNorm
  - New.ThetaTori.HasGoodReduction
  - New.ThetaTori.IsHermitianAction
  - New.ThetaTori.LatticeForm.HasShiftBound
  - New.ThetaTori.IsHermitianAction.hasShiftBound_one_of_ker
  - New.ThetaTori.IsHermitianAction.hasShiftBound_of_torsionAction
  - New.ThetaTori.IsHermitianAction.hasMultiplicativeNorm_of_frequently_hasShiftBound
  - New.ThetaTori.hasMultiplicativeNorm_of_expanding
  - New.ThetaTori.ThetaTorus.hasGoodReduction_and_val_card_eq_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta tori and good reduction

The construction of the model starts from complex tori. Each torus comes with theta functions, and the values of these functions at torsion points are complex numbers. The source wants to reduce these numbers modulo a prime of $E$. For this it fixes a non-archimedean valuation $v$ on $\mathbb{C}$ and asks when the theta functions have *good reduction* at $v$. This section gives the definition, which is analytic, and the theorem that the tori of a PEL datum have good reduction at every good place.

### The model case: Gauss's lemma

Let $O$ be a valuation ring with valuation $v$, and let $f = \sum a_i X^i$ be a polynomial with coefficients in its field of fractions. The *Gauss norm* is $\|f\| = \max_i v(a_i)$. Gauss's lemma says that $\|fg\| = \|f\|\,\|g\|$. In geometric terms: the reduction of $f/\|f\|$ modulo the maximal ideal is a nonzero polynomial, and a product of nonzero polynomials over a field is nonzero. So the projective line has good reduction, and its coordinates stay independent after reduction.

For a complex torus $V/L$ the source puts in place of the coefficients the values of a theta function at the torsion points, suitably normalized. It calls the torus of good reduction at $v$ when the resulting sup norm is multiplicative. This is an analytic form of the statement that the theta-null values have a good reduction, in the sense of Mumford, *On the equations defining abelian varieties I*, Invent. Math. 1 (1966), §§1 to 6, where an abelian variety with a theta structure is determined by its theta-null point.

### Theta tori

The tori of the source come from the frames of [Chapter 1](/chapter/complex-abelian-varieties/). Let $D$ be a PEL datum, $g \in \mathrm{GL}_n(\mathbb{A}_f)$ a frame, and $\ell$ a complex $n \times n$ matrix.

**Definition (Period map).** A *polarized period map* for $(g, \ell)$ on a finite-dimensional complex space $V$ consists of a matrix $\beta$ over $E$ (field `formMatrix`), a real linear isomorphism $Q : (E \otimes \mathbb{R})^n \to V$, and a form $B$ on $V$ (field `automorphyForm`), real linear in the first variable and complex linear in the second, such that: $g^{\mathsf H} \beta g$ is a scalar unit of $\hat{\mathbb{Z}}$; $Q$ is complex linear for the structure that is $i\ell$ at $v_0$ and $i$ at the other places; the real part of $B$ is symmetric; through $Q$ the Riemann form of $B$ is the trace form $(y, z) \mapsto \sum_v 2\operatorname{Re}(\Phi_v(\xi)\, z_v^{\mathsf H} \Phi_v(\beta) y_v)$; and the Riemann form is positive.

Lean: `New.ThetaTori.PeriodMap` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

The lattice of the torus is the image under $Q$ of the vectors $y \in E^n$ with $g^{-1}y$ integral. It is called the period lattice.

**Definition (Theta torus).** A *theta torus* for $(D, g, \ell)$ on $V$ is a polarized period map such that $\ell$ is a reflection, the adjoint of multiplication by $c \in \mathcal{O}_E$ for $B$ is multiplication by $\bar c$, and in suitable coordinates $V \cong \mathbb{C} \times \mathbb{C}^{n-1} \times \prod_{v \neq v_0} \mathbb{C}^n$ the element $a \in \mathcal{O}_E$ acts by $\Phi_{v_0}(a)$ on the line, by $\overline{\Phi_{v_0}(a)}$ on $\mathbb{C}^{n-1}$, and by $\Phi_v(a)$ on the factor of $v$.

Lean: `New.ThetaTori.ThetaTorus` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

The last condition is the signature $(1, n-1)$ at $v_0$. With the condition $\Phi_v(\beta) = \Phi_{v_0}(\bar\beta)$ of Section 2 it says that $\beta$ has the eigenvalue $\Phi_{v_0}(\beta)$ on a line of $V$ and $\Phi_{v_0}(\bar\beta)$ on a complement. So $\dim V = n \cdot |\{\text{infinite places}\}|$, which is `abelianDim`.

The theta functions of a theta torus are indexed by $T$, as in Mumford's theory. The theta functions of type $(B, \chi)$ for the larger lattice over the Lagrangian $L$ form a line. The source chooses a generator $\vartheta$ of this line.

**Definition (Theta coordinates).** For $t \in T$, the *theta coordinate* $\theta_t$ is the normalized translate of $\vartheta$ by the chosen lift of $t$ to $V$.

Lean: `New.ThetaTori.PeriodMap.thetaCoord` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

**Remark (Formalization).** The generator $\vartheta$ (`lagrangianTheta`) and the lifts of the classes $t$ are chosen with `choose`. Another choice multiplies every $\theta_t$ by one common nonzero constant, and multiplies each $\theta_t$ by a root of unity from the multiplier. The source uses the vector $(\theta_t)_{t \in T}$ only as homogeneous coordinates (Section 5), so the common constant has no effect. The roots of unity are part of the level structure and are fixed once the lifts are fixed.

### The sup norm and good reduction

Let $L \subset V$ be a full lattice, $B$ a form as above for $L$, and $v$ a valuation on $\mathbb{C}$ with values in $\mathbb{R}_{\geq 0}$. For a function $f$ on $V$ and a torsion point $x$ of $V/L$, the twisted translate of $f$ by $x$ (`thetaShift`) is the translate $z \mapsto f(z + x)$ times the exponential factor that makes it again a theta function, of a twisted type. Its value at $z = 0$ is $\exp(-B(x, x)/2) f(x)$.

**Definition (Size).** The *size* of $f$ at a torsion point $x$ is $v(\exp(-B(x, x)/2) f(x))$, the valuation of the value at $0$ of the twisted translate of $f$ by $x$. The *sup norm* $\|f\|_v$ is the supremum of the sizes over all torsion points. The *sizes of degree $B$* are the size functions of the theta functions of type $(B, \chi)$, for all $\chi$ such that $(L, B, \chi)$ is of ample type.

Lean: `New.ThetaTori.LatticeForm.sizeAt` (Lib/Shimura/GoodReduction/TorsionSizes.lean).

Here $(L, B, \chi)$ is of *ample type* (`New.ThetaTori.IsAmpleType`) when it is an Appell-Humbert datum with positive Riemann form and $\chi$ has finite order on $L$.

**Definition (Multiplicative norm).** The lattice $L$ has a *multiplicative norm* at $v$ when, for all forms $B, C$ and all sizes $\varphi$ of degree $B$ and $\psi$ of degree $C$, $\sup(\varphi\psi) = \sup \varphi \cdot \sup \psi$.

Lean: `New.ThetaTori.HasMultiplicativeNorm` (Lib/Shimura/GoodReduction/TorsionSizes.lean).

**Definition (Good reduction).** The triple $(B, \chi, v)$ has *good reduction* with level $r$ when $(L, B, \chi)$ is of ample type, some natural number $N$ with $v(N) = 1$ maps the dual lattice of $L$ into $L$, $v(r) = 1$, $r > 1$, and $L$ has a multiplicative norm at $v$.

Lean: `New.ThetaTori.HasGoodReduction` (Lib/Shimura/GoodReduction/TorsionSizes.lean).

The product of a size of degree $B$ and a size of degree $C$ is the size of the product function, of degree $B + C$. So the inequality $\sup(\varphi\psi) \leq \sup\varphi \sup\psi$ always holds. The content of the definition is the reverse inequality: the largest values of $f$ and of $g$ occur at a common torsion point, up to a unit. This is the analogue of Gauss's lemma.

### Expanding maps give good reduction

The source proves good reduction by a contraction argument. The tool is a hermitian action of a ring $R$ on $V/L$.

**Definition (Hermitian action).** Let $R$ be a commutative ring with involution, finite over $\mathbb{Z}$, and $\beta \in R$. A *hermitian action* of $R$ on $V/L$ for $B$ is a ring map $F : R \to \operatorname{End}_{\mathbb{C}}(V)$ such that each $F(a)$ maps $L$ into $L$, $B$ is hermitian and positive definite, $F(\bar a)$ is the adjoint of $F(a)$ for $B$, the Riemann form of $B$ is integral on $L$, and $\bar\beta = 1 - \beta$.

Lean: `New.ThetaTori.IsHermitianAction` (Lib/Shimura/GoodReduction/GaussSums.lean).

**Definition (Shift bound).** Let $w$ be a torsion point and $C \geq 0$. The form $B$ has the *shift bound* $C$ at $w$ when, for the size function $\varphi$ of every twisted theta function of degree $B$ and every torsion point $y$, $\varphi(y)^2 \leq C \cdot \sup_x \varphi(x)\varphi(x + w)$.

Lean: `New.ThetaTori.LatticeForm.HasShiftBound` (Lib/Shimura/GoodReduction/TorsionSizes.lean).

A shift bound with constant $1$ at every $w$ says that a translate of $\varphi$ by $w$ is as large as $\varphi$ itself somewhere, in the multiplicative sense. Three lemmas lead to good reduction. Fix a hermitian action $h$.

**Lemma (Constant 1 on a kernel).** Let $c \neq 0$ and $d = \bar c$ be distinct and coprime, and let $F(c)$ and $F(d)$ act as the identity on the dual lattice of $B$ modulo $L$. Let $p$ be a prime with $v(p) < 1$, let $v(\det F(d)) = 1$, and let $B - A$ have a positive Riemann form. Then every torsion point $w$ with $F(c)w \in L$ and $p^n w \in L$ has the shift bound $1$ in degree $A$.

Lean: `New.ThetaTori.IsHermitianAction.hasShiftBound_one_of_ker` (Lib/Shimura/GoodReduction/MultiplicativeNorm.lean).

**Lemma (Descent along $c$).** Let $c \neq 0$. Assume that every torsion point $y$ with $F(c)y \in L$ has the shift bound $1$ in every degree, and that $c^*B - A$ has a positive Riemann form, where $c^*B$ is the pull-back of $B$ along $F(c)$. If $F(c)w$ has the shift bound $C$ in degree $B$, then $w$ has the shift bound $C \cdot v(\#(c^{-1}L/L))^{-2}$ in degree $A$.

Lean: `New.ThetaTori.IsHermitianAction.hasShiftBound_of_torsionAction` (Lib/Shimura/GoodReduction/MultiplicativeNorm.lean).

**Lemma (Contraction).** Assume that in every neighbourhood of $0$ in $\operatorname{End}(V)$ there is a linear map $e$ that is a right inverse of $F(c)$ for some $c \neq 0$, such that every torsion point $y$ with $F(c)y \in L$ has the shift bound $1$ in every degree. Then $L$ has a multiplicative norm at $v$.

Lean: `New.ThetaTori.IsHermitianAction.hasMultiplicativeNorm_of_frequently_hasShiftBound` (Lib/Shimura/GoodReduction/MultiplicativeNorm.lean).

The plan of the source is the following. A torsion point that is not killed by $c$ is moved by $F(c)$ to another torsion point. The descent lemma transports a shift bound back along $F(c)$, with a factor $v(\#(c^{-1}L/L))^{-2}$. The kernel lemma gives the constant $1$ on the kernel of $c$. When the right inverse $e$ of $F(c)$ is close to $0$, the pull-back $c^*B$ is large, and the positivity hypothesis of the descent lemma can be met. The lemma `New.ThetaTori.IsHermitianAction.eventually_hasShiftBound` first gives every torsion point some finite shift bound. The contraction lemma then improves the bounds to the constant $1$ and deduces the reverse inequality $\sup\varphi \sup\psi \leq \sup(\varphi\psi)$. This book does not reproduce the estimates of these three proofs.

The three lemmas combine into a criterion with arithmetic hypotheses.

**Proposition (Good reduction from expanding multiplications).** Let $R$ be a domain of characteristic $0$, finite over $\mathbb{Z}$, with a hermitian action on $V/L$. Let $p$ be a prime with $v(p) < 1$, and let $n$ be prime to $p$ with $n \cdot a \in L$ for every $a$ in the dual lattice of $B$. Assume that every neighbourhood of $0$ contains a right inverse of $F(c)$ for some $c \in R$ that is not a unit, is coprime to $\bar c$, divides a power of $p$, and has $v(\det F(\bar c)) = 1$. Then $L$ has a multiplicative norm at $v$.

Lean: `New.ThetaTori.hasMultiplicativeNorm_of_expanding` (Lib/Shimura/GoodReduction/MultiplicativeNorm.lean).

*Proof.* By the contraction lemma it is enough to show the shift bound $1$, in every degree $A$, at the points killed by $c$. Take $i \equiv n \pmod p$ with $iB - A$ positive. The integer $ni$ is prime to $p$, hence to $c$, since $c \mid p^k$. So $c$ is a unit of the finite ring $R/(ni)$, and $c^{j+1} \equiv 1 \pmod{ni}$ for some $j$. Then $c^{j+1} - 1$ and its conjugate are multiples of $ni$, which maps the dual lattice of $iB$ into $L$. So $F(c^{j+1})$ and $F(\bar c^{j+1})$ act as the identity on the dual lattice of $iB$ modulo $L$. A non-unit coprime to its conjugate differs from it. Apply the kernel lemma to $iB$ and $c^{j+1}$. $\square$

### Good reduction of theta tori

The main theorem of this section applies the criterion to a theta torus at a good place.

**Theorem (Good reduction at good places).** Let $x$ be a theta torus for $(D, g, \ell)$ on $V$. Let $v$ be a valuation on $\mathbb{C}$ and $\rho : \mathcal{O}_E \to O_v$ a ring map into its valuation ring with $\rho(c) = \Phi_{v_0}(c)$ for all $c$. Assume that $D$ is good at the prime $\rho^{-1}(\mathfrak{m}_v)$. Then $(B, \chi, v)$ has good reduction with level $r = D.\mathrm{paddedNorm}$, for $B$ the form and $\chi$ the multiplier of $x$, and $v(|T|) = 1$.

Lean: `New.ThetaTori.ThetaTorus.hasGoodReduction_and_val_card_eq_one` (Lib/Shimura/GoodReduction/MultiplicativeNorm.lean).

*Proof.* Let $w = \rho^{-1}(\mathfrak{m}_v)$, and take $p$, $b$ and the second place $w'$ from condition 2 and condition 4 of goodness. The conditions $r \notin w$ and $|T| \notin w$ give $v(r) = 1$ and $v(|T|) = 1$. The dual lattice of the period lattice lies over $T$, so $|T|$ maps it into the period lattice, and $|T|$ is prime to $p$. Average $B$ over multiplication by $i$: this gives a hermitian form with the same Riemann form, so $\mathcal{O}_E$ has a hermitian action. Let $a$ generate a high power of $w'$ and be large at every complex embedding. Put $c = \bar a$. In the standard coordinates the inverse of $F(c)$ is multiplication by the numbers $\Phi_u(c)^{-1}$, which are small. So for a high enough power of $w'$ it lies in any given neighbourhood of $0$. The element $a$ divides a power of $\beta - b$, so $\bar a$ divides a power of $\bar\beta - b$, and $c$ divides a power of $p$. Since $\beta - b$ and $\bar\beta - b$ are coprime, $c$ and $\bar c$ are coprime. Since $w'$ is maximal and differs from $w$, some $t \in w'$ has $\rho(t)$ a unit of $O_v$. As $a$ generates a power of $w'$, it divides a power of $t$, so $\rho(a)$ is a unit of $O_v$. As $w' \neq \mathcal{O}_E$, $a$ is not a unit of $\mathcal{O}_E$. In the standard coordinates, $\det F(\bar c)$ is a product of powers of $\Phi_{v_0}(a)$, its conjugate, and the $\Phi_u(a)$ for $u \neq v_0$. The first is a unit, as $\rho(a)$ is. The others are units, because $\Phi_u(\beta) = \Phi_{v_0}(\bar\beta)$ by the PEL datum. So $v(\det F(\bar c)) = 1$. Now apply the proposition. $\square$

**Remark (Formalization).** The valuation $v$ is any $\mathbb{R}_{\geq 0}$-valued valuation on $\mathbb{C}$. The source does not fix an isomorphism $\mathbb{C} \cong \mathbb{C}_p$. The theorem holds for every $v$ whose valuation ring contains $\Phi_{v_0}(\mathcal{O}_E)$ and whose maximal ideal meets $\mathcal{O}_E$ in a good prime. Such valuations exist for every prime of $\mathcal{O}_E$, by the extension theorem for valuations; the source uses them in Section 6 through valuation subrings of $\mathbb{C}$.
