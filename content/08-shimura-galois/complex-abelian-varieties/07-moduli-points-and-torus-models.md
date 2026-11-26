---
title: Moduli points and torus models
lean:
  - Lib/Shimura/Uniformisation/AdelicFrames.lean
  - Lib/Shimura/Uniformisation/TorusModel.lean
  - Lib/Shimura/Uniformisation/ModelExists.lean
  - Lib/Shimura/Uniformisation/BallModel.lean
decls:
  - New.CMBase
  - New.Variety.abelianDim
  - New.Variety.IsFrameFor
  - New.Variety.IsReflection
  - New.Variety.IsSignedFrame
  - New.Variety.ModuliPoint
  - New.Variety.ModuliPoint.act
  - New.Variety.ModuliPoint.IsLevelIso
  - New.Variety.frameLattice
  - New.Variety.IsPeriodMap
  - New.Variety.IsPeriodMap.finrank_eq_abelianDim
  - New.ThetaObject.TorusModel
  - New.ThetaObject.TorusModel.exists_isTranslationLift_of_dualLattice
  - New.ThetaObject.TorusModel.multiplier_eq_canonicalMultiplier
  - New.Variety.exists_torusModel
  - New.Variety.exists_isBallFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Moduli points and torus models

The integral model of [the next chapter](/chapter/integral-model/) is a family of abelian varieties with an action of the ring of integers $\mathcal{O}_E$ of a CM field $E$. The source needs the converse of the previous sections: every complex member of the family is a complex torus given by linear algebra over $E$. This section states the linear-algebra side and the two results that connect it to the family. The family (`New.ThetaFamily`) and its objects (`New.ThetaObject`) belong to the next chapter. An object over $R$ has an abelian scheme $A$ with an action of $\mathcal{O}_E$, a linear system that embeds $A$, level points, and a ring map $\mathcal{O}_E \to R$.

### The model case

Let $E$ be an imaginary quadratic field, $n = 1$ and $L = \mathcal{O}_E \subset \mathbb{C}$. Every elliptic curve over $\mathbb{C}$ with an action of $\mathcal{O}_E$ that acts on the tangent space through $E \subset \mathbb{C}$ is $\mathbb{C}/\mathfrak{a}$ for a fractional ideal $\mathfrak{a}$, unique up to $E^\times$, and $\mathfrak{a} = E \cap x \widehat{\mathcal{O}}_E$ for an idele $x$. This is the shape of the general case: a lattice $E^n \cap x \widehat{\mathcal{O}}_E^n$ for an adelic matrix $x$, with a complex structure on $(E \otimes \mathbb{R})^n$ as the extra datum.

### CM fields and frames

**Definition (CM base).** A *CM base* is a CM field $E$ with a CM type $\Phi$, that is, one complex embedding $\Phi_v$ for each infinite place $v$, together with a base place $v_0$. The field has at least two infinite places.

Lean: `New.CMBase` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

So an imaginary quadratic field, with one infinite place, is not a CM base. The model case above shows the shape of the theory but is excluded by the definition. For a set $n$ of indices, the abelian varieties of the family have dimension
$$\dim = |n| \cdot |\{\text{infinite places of } E\}| = |n| \cdot [E : \mathbb{Q}]/2.$$

Lean: `New.Variety.abelianDim` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

**Definition (Frame).** Let $\beta$ be an $n \times n$ matrix over $E$. An invertible matrix $x$ over the finite adeles $\mathbb{A}_{f,E}$ is a *frame* for $\beta$ if $x^{\mathrm{H}} \beta x = \varepsilon \cdot 1$ for a unit $\varepsilon$ of $\widehat{\mathbb{Z}}$, where $x^{\mathrm{H}}$ is the conjugate transpose.

Lean: `New.Variety.IsFrameFor` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

**Definition (Reflection, signed frame).** A complex $n \times n$ matrix $J$ is a *reflection* if $J = u w^{\mathsf{T}} - 1$ for vectors $u, w$ with $w \cdot u = 2$. Then $J$ is $1$ on the line of $u$ and $-1$ on the kernel of $w$. A pair $(x, J)$ is a *signed frame* if $x$ is a frame for some $\beta$ over $E$ such that $\Phi_v(\beta)$ is positive definite for every infinite place $v \neq v_0$ and $\Phi_{v_0}(\beta)\,J$ is positive definite.

Lean: `New.Variety.IsReflection` and `New.Variety.IsSignedFrame` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

The positivity conditions are the source's form of the signature condition of a unitary Shimura variety: definite at all places but one, and indefinite of a fixed shape at $v_0$, where $J$ records the complex structure.

### Moduli points

**Definition (Moduli point).** A *moduli point* with $\nu$ marked vectors is a triple $(x, J, P)$: an invertible adelic matrix $x$, a reflection $J$ such that $(x, J)$ is a signed frame, and vectors $P_1, \dots, P_\nu \in (E \otimes \mathbb{R})^n$.

Lean: `New.Variety.ModuliPoint` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

The lattice of $x$ is $E^n \cap x\widehat{\mathcal{O}}_E^n$, embedded in $(E \otimes \mathbb{R})^n$ by the CM type (`New.Variety.frameLattice`). An adelic similitude $g$ with integral inverse and elements $\alpha_i \in \mathcal{O}_E$ act by $(x, J, P) \mapsto (x g, J, \alpha_i P_i)$ (`New.Variety.ModuliPoint.act`).

Lean: `New.Variety.frameLattice`, `New.Variety.ModuliPoint.act` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

**Definition (Isomorphism at level $K$).** Let $K$ be a subgroup of $GL_n(\mathbb{A}_{f,E})$ and $a = (x, J, P)$, $b = (x', J', P')$ moduli points. A matrix $z \in GL_n(E)$ is an *isomorphism from $a$ to $b$ at level $K$* if $x'^{-1} z x \in K$, $\Phi_{v_0}(z)\,J\,\Phi_{v_0}(z)^{-1} = J'$, and $z P_i - P'_i$ lies in the lattice of $x'$ for every $i$.

Lean: `New.Variety.ModuliPoint.IsLevelIso` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

This is the double coset description of points of a Shimura variety in the textbook (Milne, *Introduction to Shimura Varieties*, Section 5 and Theorem 8.17, for the PEL case), in a form adapted to a fixed group $GL_n(E)$ acting on frames.

**Definition (Period map).** Let $V$ be a complex vector space and $\ell$ a complex $n \times n$ matrix. A real isomorphism $Q \colon (E \otimes \mathbb{R})^n \to V$ is a *period map* for $\ell$ if it carries the real endomorphism that is $i \ell$ at $v_0$ and $i$ at the other infinite places to multiplication by $i$ on $V$.

Lean: `New.Variety.IsPeriodMap` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

**Proposition.** If $Q$ is a period map onto $V$, then $\dim_{\mathbb{C}} V$ is the dimension $|n| \cdot |\{\text{infinite places of } E\}|$ of the definition above.

Lean: `New.Variety.IsPeriodMap.finrank_eq_abelianDim` (Lib/Shimura/Uniformisation/AdelicFrames.lean).

The real dimension of $(E \otimes \mathbb{R})^n$ is $|n| \cdot [E : \mathbb{Q}]$, which is twice the number in the proposition. The proof does not use the period map condition beyond the existence of the real isomorphism.

### Torus models

The source packages a period map with a frame and a form $B$ as `New.ThetaTori.PeriodMap D g ℓ V`. Its period lattice is $Q$ of the lattice of the frame $g$, its automorphy form is $B$, and the Riemann form of $B$ pulls back to the polarization form of the PEL datum $D$.

**Definition (Torus model).** Let $y$ be an object of the family over a valuative arc $O$ and $Y$ a polarized period map onto $V$. A *torus model* of $y$ on $Y$ consists of:

1. the composite $\mathcal{O}_E \to O \to \mathbb{C}$ is $\Phi_{v_0}$;
2. a uniformization $u$ of the abelian scheme of $y$ by $V$, in the sense of [Section 6](/chapter/complex-abelian-varieties/);
3. a multiplier $\chi$ and theta coordinates $\theta$ for the linear system of $y$ along $u$, of type $(B, \chi)$ with $B$ the automorphy form of $Y$;
4. compatibility of $u \circ Q$ with the actions of $\mathcal{O}_E$;
5. the level points of $y$ are the images under $u$ of chosen rational vectors;
6. the kernel of $u$ is the period lattice of $Y$.

Lean: `New.ThetaObject.TorusModel` (Lib/Shimura/Uniformisation/TorusModel.lean).

The next two results link a torus model to Sections 3 and 5.

**Proposition.** Let $m$ be a torus model of $y$ on $Y$ and $b$ a vector of the dual lattice of the period lattice for the Riemann form of $B$. Then $|H|\,b$ lies in the period lattice, where $H$ is the finite index set of the coordinates. The translation by $u(b)$ has a lift $\Phi$ to the sections of the linear system, and $\Phi$ maps the $O$-span of the coordinate sections to itself.

Lean: `New.ThetaObject.TorusModel.exists_isTranslationLift_of_dualLattice` (Lib/Shimura/Uniformisation/TorusModel.lean).

This is the algebraic counterpart of the twisted translations $\Theta_b$ of [Section 2](/chapter/complex-abelian-varieties/), which preserve the space of theta functions for $b$ in the dual lattice.

**Proposition.** On the period lattice, the multiplier of a torus model is the canonical multiplier of [Section 3](/chapter/complex-abelian-varieties/): $\chi(l) = \exp(\pi i\,E(\beta l, l))$, where $\beta \in \mathcal{O}_E$ is the element of the PEL datum and acts on $V$ through the period map.

Lean: `New.ThetaObject.TorusModel.multiplier_eq_canonicalMultiplier` (Lib/Shimura/Uniformisation/TorusModel.lean).

*Proof.* The class laws of the family give $N \otimes N \otimes \beta^* N \cong (\beta + 1)^* N$. The multipliers of the two sides agree, so $\chi(l)^2 \chi(\beta l) = \chi(l + \beta l)$. The cocycle rule of Appell-Humbert data expands the right side as $\chi(l)\,\chi(\beta l)\,\exp(\pi i\,E(\beta l, l))$. Cancel $\chi(l)\,\chi(\beta l)$, which is a unit. $\square$

So the multiplier is not a free datum: the class laws force it. This is the reason why Section 3 introduced the canonical multiplier with $b + b^* = 1$, which here is $\beta + \bar\beta = 1$.

### Every complex object has a torus model

**Theorem.** Let $x$ be an object of the family over $\mathbb{C}$ whose map $\mathcal{O}_E \to \mathbb{C}$ is $\Phi_{v_0}$, and let $e$ be a full level structure on $x$, that is, a trivialization of all torsion. Then there are an adelic frame $g$, a complex matrix $\ell$, a dimension $d$, a polarized period map $Y$ for $(g, \ell)$ onto $\mathbb{C}^d$, and a torus model $m$ of $x$ on $Y$, such that the torsion points of $m$ are those of $e$ and $\ell$ is a reflection.

Lean: `New.Variety.exists_torusModel` (Lib/Shimura/Uniformisation/ModelExists.lean).

*Idea of the proof.* Uniformize the abelian scheme of $x$ by the theorem of [Section 6](/chapter/complex-abelian-varieties/), with $d$ the dimension of the family. The universal property of the uniformization lifts the action of $\mathcal{O}_E$ to a $\mathbb{C}$-linear action of $E \otimes \mathbb{R}$ on $\mathbb{C}^d$. The $2$-torsion points given by $e$ define an equivariant isomorphism $Q \colon (E \otimes \mathbb{R})^n \to \mathbb{C}^d$. The signature condition of the family shows that the complex structure pulled back by $Q$ is given by a reflection at $v_0$. The frame $g$ is found from the Weil pairing of $e$. The theorem of Appell and Humbert gives the theta coordinates. $\square$

The file imports `Lib/Shimura/HeckeTower/Model.lean`, which belongs to the next chapter, for the full level structures.

### Ball families

**Theorem.** Every moduli point $o$ has a ball family: an analytic family $f$ of theta tori whose point at parameter $0$, with the marked vectors of $o$, is $o$, which passes through every moduli point with the frame of $o$, and on whose parameters an isomorphism from a translate of $o$ to $o$ acts linearly near $0$, with local term $p(t) = p(0) \det(1 - tK)$ for the linear map $K$.

Lean: `New.Variety.exists_isBallFamily` (Lib/Shimura/Uniformisation/BallModel.lean).

The parameters are the positive lines for the hermitian form at $v_0$, which form a complex ball of dimension $|n| - 1$. The theorem is used in `Lib/Shimura/IntegralModel/BallImmersion.lean` in [the next chapter](/chapter/integral-model/), where the family of the integral model is compared with these analytic families.
