---
title: The universal family and smoothness
lean:
  - Lib/Shimura/ThetaModuli/UniversalFamily.lean
  - Lib/Shimura/IntegralModel/UniversalFamily.lean
  - Lib/Shimura/Deformation/TangentBound.lean
  - Lib/Shimura/Deformation/TangentCount.lean
  - Lib/General/Geometry/SmoothnessCriterion.lean
decls:
  - New.Variety.ThetaNull.IsGoodOver
  - New.Variety.ThetaNull.isUnit_star_sub_and_card_of_isGoodOver
  - New.Variety.UniversalFamily
  - New.Variety.ThetaNull.ThetaClosure
  - New.Variety.ThetaNull.ThetaClosure.exists_finite_isDenseFamily
  - New.Variety.ThetaNull.ThetaClosure.exists_hasThetaFibres
  - New.Variety.ThetaNull.ThetaClosure.exists_arc_isGoodAt
  - New.Variety.exists_landsIn_smoothOfRelativeDimension
  - New.Variety.drinfeld_lift
  - New.Variety.finrank_le_of_placeTorsion
  - New.Variety.finrank_tangent_le_card_index_sub_one
  - New.Variety.ThetaNull.ThetaClosure.exists_smooth_near_arc
  - New.Variety.ThetaNull.nonempty_universalFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The universal family and smoothness

The textbook moduli space is smooth because its deformation theory is unobstructed (Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties*, Lemma III.4.1). The base of the source is a closure, so it proves smoothness from two bounds. The lower bound is analytic: an analytic family of tori with $n - 1$ parameters is an immersion at each complex point. The upper bound is a first-order deformation count over the residue field. Commutative algebra then gives smoothness of relative dimension $n - 1$.

### The model case: rank one

Take $n = 1$. Then both bounds are $0$. The upper bound says that a CM abelian variety with its extra structure has no first-order deformations over the residue field, and the criterion says that the base is étale over $\operatorname{Spec} R$.

### Good rings

**Definition (Good over $R$).** Let $R$ be an $\mathcal{O}_E$-subalgebra of $E$. The datum $D$ is *good over $R$* when for every maximal ideal $\mathfrak{m}$ of $R$, $D$ is good (Section 2) at the prime $\mathfrak{m} \cap \mathcal{O}_E$.

Lean: `New.Variety.ThetaNull.IsGoodOver` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

**Lemma (Units of a good ring).** If $D$ is good over $R$, then $\bar\beta - \beta$ and $|D.\mathrm{dualTorsion}|$ are units of $R$.

Lean: `New.Variety.ThetaNull.isUnit_star_sub_and_card_of_isGoodOver` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* If the product is not a unit, it lies in a maximal ideal $\mathfrak{m}$. Let $w = \mathfrak{m} \cap \mathcal{O}_E$. Since $D$ is good at $w$, the order of the torsion is not in $w$. So $\bar\beta - \beta \in w$. Goodness gives an integer $b$ with $\beta - b \in w$ and $\beta - b$ coprime to $\bar\beta - b$. Then $\bar\beta - b = (\bar\beta - \beta) + (\beta - b) \in w$, so both lie in $w$, which contradicts coprimality. $\square$

### The universal family

**Definition (Universal family).** A *universal family* for $D$ over $R$ consists of:

1. the fact that $R$ is a Dedekind domain;
2. a scheme $S$ over $\operatorname{Spec} R$ with a theta family for $D$ over $S$ (Section 5);
3. a projective embedding of $S$ over $R$;
4. smoothness of $S$ over $R$ of relative dimension $n - 1$, with $n = |D.\mathrm{Index}|$;
5. complex points $\mathrm{obj}(f, b)$ of $S$, indexed by an analytic family of tori $f$ and a parameter $b$ in the ball of dimension $n - 1$;
6. for each pair $(f, b)$, a model of the fibre at $\mathrm{obj}(f, b)$ on the torus of $f$ at $b$;
7. holomorphy of the uniformized points in $(b, z)$ on the domain of $f$;
8. density of the points $\mathrm{obj}(f, b)$ in $S$.

Lean: `New.Variety.UniversalFamily` (Lib/Shimura/IntegralModel/UniversalFamily.lean).

The analytic families are those of [Chapter 1](/chapter/complex-abelian-varieties/).

**Remark (Formalization).** The name says "universal", but the structure asks for no universal property. It does not say that every theta family is a pull-back of this one. The only moduli statement is the rigidity field of the theta family (Section 5). The structure also does not say that the points $\mathrm{obj}(f, b)$ are all the complex points; for the covers of Section 7 the source proves this separately (`New.Variety.UniversalFamily.GraphClosure.point_surjective`).

### The closure of the level points

Each parameter of an analytic family gives a theta torus, and each level point $\omega$ gives the vector $(\theta_s(\text{lift of } \omega))_{s}$, a point of $\mathbb{P}^{T}$.

**Definition (Theta closure).** For a family $y$ of parameters, the *theta closure* is the reduced closure of the points $(\text{level point } \omega \text{ at } y_b)_{\omega}$ in the product over $\omega$ of the projective spaces $\mathbb{P}^T_R$.

Lean: `New.Variety.ThetaNull.ThetaClosure` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

Four lemmas concern the closure $C$ of all parameters.

**Lemma (Finitely many dense families).** If $D$ is good over $R$, the generic points of finitely many analytic families are dense in $C$.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_finite_isDenseFamily` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

$C$ is noetherian, so it has finitely many irreducible components. A parameter $b$ of a family is *generic* when the point at $b$ specializes to the points at all parameters of the family.

**Lemma (A theta family on the closure).** Let $R$ be the localization of $\mathcal{O}_E$ at a submonoid $M$, with $D$ good over $R$. If finitely many parameters are dense in $C$, there is a theta family $X$ over $C$ whose fibre at each complex point $b$ has a model on the theta torus at $y_b$ with the same theta coordinates.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_hasThetaFibres` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* Apply the theorem on theta families from points (Section 5). The units come from the lemma above. The coordinate bundles of the factors $\mathbb{P}^T$ embed $C$ (`isProjEmbedding_pi_coordBundle`). For the specialization hypothesis, let $t$ be a point of $C$. By the next lemma it specializes to the centre of an arc $\alpha$ over a good prime, through a complex point. Over the valuation ring $O_v$ of $\mathbb{C}$ of the arc, the theta torus has good reduction (Section 3), and the theorem on reduction of the theta points (Section 4) shows that the coordinate bundles cut out the reduced theta vectors there. The nonvanishing indices come from the theta-null lemma of Section 4, at the same valuation. $\square$

**Lemma (Arcs over good primes).** Let $R$ be noetherian with $D$ good over $R$, and let finitely many points be dense in $C$. Then every point $z$ of $C$ specializes to the centre of an arc through one of them, and the arc lies over a good prime.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_arc_isGoodAt` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

An arc is a morphism $\operatorname{Spec} V \to C$ for a valuation subring $V$ of $\mathbb{C}$. Arcs exist by a form of the valuative criterion that the source proves.

### The smoothness criterion

**Theorem (Smoothness near an arc).** Let $s : X \to \operatorname{Spec} R$ be locally of finite type, with $R$ a normal domain. Let $\varphi_w$ be a family of complex points of $X$ with $d$ parameters, and let $\mathrm{arc} : \operatorname{Spec} V \to X$ be a point with values in a valuation subring $V$ of $\mathbb{C}$. Assume:

1. the arc extends $\varphi_{w_0}$;
2. all $\varphi_w$ lie over one embedding $R \to \mathbb{C}$;
3. $\varphi_{w_0}$ specializes to $\varphi_w$ for $w$ near $w_0$;
4. $\varphi$ is a holomorphic immersion at $w_0$: it is holomorphic there and constant to first order only in the direction $0$;
5. $\vartheta : V \to k$ is a local map to a field, which gives a $k$-point $t$ at the closed point of the arc;
6. if $\tau$ is a deformation of $t$ over the square-zero extension $k \oplus M^*$, constant in $\operatorname{Spec} R$, whose pull-back to $k[\varepsilon]$ along $l \in M$ is constant only for $l = 0$, then $\dim_k M \leq d$.

Then $s$ is smooth of relative dimension $d$ on an open set through which the arc factors.

Lean: `New.Variety.exists_landsIn_smoothOfRelativeDimension` (Lib/General/Geometry/SmoothnessCriterion.lean).

*Proof.* By condition 6, the relative tangent space at $t$ has dimension at most $d$, so $d$ functions near $t$ give a map $X \to \mathbb{A}^d_R$ unramified at $t$. Locally this is a closed subscheme of a standard étale algebra. Conditions 3 and 4 make the map dominant, since the family has $d$ independent parameters. Over a normal domain, such a quotient is étale after inverting a function that is a unit on the arc (`New.Variety.exists_etale_away_of_faithful`). So $X$ is étale over $\mathbb{A}^d_R$ near the arc. $\square$

The lower bound is `New.Variety.AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt` (Lib/Shimura/IntegralModel/BallImmersion.lean). The upper bound occupies the rest of this section.

### Drinfeld's lifting lemma

Let $k$ be a field, $k[\varepsilon]$ the dual numbers, and $x, x'$ two first-order deformations over $k[\varepsilon]$ of one object $x_0$ over $k$ of a theta family. Write $A, A', A_0$ for their group schemes.

**Lemma (Drinfeld's lifting lemma).** Let $c \in \mathcal{O}_E$ kill every point of $A'$ that vanishes modulo $\varepsilon$. Then there is an additive morphism $F : A \to A'$ that reduces to multiplication by $c$ on $A_0$. In addition, $yF = c\,y'$ for all points $y$ of $A$ and $y'$ of $A'$ that agree modulo $\varepsilon$.

Lean: `New.Variety.drinfeld_lift` (Lib/Shimura/Deformation/TangentBound.lean).

This is the lemma of Drinfeld in Katz, *Serre-Tate local moduli*, LNM 868 (1981), §1. *Proof idea.* For a point $y$ of $A$, choose locally $y'$ on $A'$ with the same reduction, by smoothness, and put $F(y) = c\,y'$. Two choices differ by a point that $c$ kills. So $F$ is well defined and additive.

### Counting torsion points

The upper bound is proved on the finite group scheme of $w$-torsion, where $w$ is the kernel of the structure map $\mathcal{O}_E \to k$. For a local $k$-algebra $C$, let $\mathrm{placeTorsion}(x, C)$ be the $\mathcal{O}_E$-module of the $C$-points of $A_0$ killed by $w$.

**Lemma (Counting torsion points).** Let $k$ be algebraically closed, and let $x$ over $k$ be the reduction at a good place $w$ of an object $y$ over a valuation subring of $\mathbb{C}$ with a full level structure. Let $W$ be a $k$-vector space, and let $f$ attach to each $l \in W$ and each local $k$-algebra $C$ a function on $\mathrm{placeTorsion}(x, C)$ with values in $C$, semilinear along $\mathcal{O}_E \to k$ in the point and linear in $l$. Assume:

1. $f$ is natural in $C$;
2. $f$ vanishes on the points over $k[\varepsilon]$ that reduce to $0$;
3. only $l = 0$ gives a function that is zero on all finite local $C$.

Then $\dim_k W \leq n - 1$.

Lean: `New.Variety.finrank_le_of_placeTorsion` (Lib/Shimura/Deformation/TangentCount.lean).

The idea, from the comments in the proof: let $\mathbb{F}_q$ be the residue field $\mathcal{O}_E/w$ and $d$ the dimension of $\mathrm{placeTorsion}(x, k)$ over $\mathbb{F}_q$. Of the $q^n$ torsion sections, $q^{n-d}$ pass through $0$. The local ring of the $w$-torsion at the origin is then $k[\tau]$ with $\tau$ nilpotent of order at most $q^{n-d}$. Semilinearity makes $z \mapsto f(k, z)$ linear over $\mathbb{F}_q$, and an $\mathbb{F}_q$-linear map $a \mapsto a^i$ on $k$ has $i$ a power of $q$ (the lemma `New.Variety.mem_powers_card_of_isLinearMap_pow`). So the lowest term of $f$ on the universal point has degree $q^j$ with $0 < j < n - d$; condition 2 excludes $j = 0$. The values of $l$ on the $k$-points and the coefficients of $\tau^{q^j}$ for $0 < j < n - d$ determine $l$, by condition 3. This gives $\dim_k W \leq d + (n - d - 1) = n - 1$.

**Remark (Formalization).** The textbook upper bound uses the $p$-divisible group and the Serre-Tate theorem, or Grothendieck-Messing theory (Harris and Taylor, Lemma III.4.1). The source works "on the finite group scheme of w-torsion with Drinfeld's lifting lemma and without p-divisible groups or crystals", as its docstring says. The book does not reproduce the counting argument in full.

### The tangent bound

**Theorem (Tangent bound).** Let $k$ be algebraically closed, $M$ a $k$-vector space, $x_0$ an object of a theta family over $k$, and $x$ an object over the square-zero extension $k \oplus M^*$. Assume:

1. $D$ is good at the kernel of $\mathcal{O}_E \to k$;
2. $x_0$ is rigid (`New.ThetaObject.HasSpanningCoords`) and is the fibre of an object $w$ over a valuation subring of $\mathbb{C}$ that has a full level structure;
3. $x$ reduces to $x_0$, and $\mathcal{O}_E$ maps to $k \oplus M^*$ through $k$;
4. for $l \neq 0$ in $M$, the pull-back of $x$ along $k \oplus M^* \to k[\varepsilon]$, $(a, \phi) \mapsto a + \phi(l)\varepsilon$, is not the constant deformation of $x_0$.

Then $\dim_k M \leq |D.\mathrm{Index}| - 1$.

Lean: `New.Variety.finrank_tangent_le_card_index_sub_one` (Lib/Shimura/Deformation/TangentBound.lean).

*Proof.* Let $\mathfrak{p}$ be the kernel of $\mathcal{O}_E \to k$. Since $\mathfrak{p}$ is good, there are $c \neq 0$ in $\mathfrak{p}$ and $t \equiv 1 \pmod{\mathfrak{p}}$ with $t\mathfrak{p} \subseteq (c)$. For a point $y$ of $A_0$ killed by $\mathfrak{p}$, with values in a local algebra $C$, lift it to a point $Y(y)$ of $A$ over $C \oplus \operatorname{Hom}(M, C)$. Then $c\,Y(y)$ is infinitesimal, and its logarithm on the tangent line gives a map $f(C, y) : M \to C$. Drinfeld's lemma makes $f$ independent of the lift and natural in $C$. Points over $k[\varepsilon]$ that reduce to $0$ have logarithm $0$, and condition 4 gives the separation in $M$. The counting lemma gives $\dim_k M \leq n - 1$. $\square$

**Lemma (Smooth near each arc).** Let $X$ be the theta family on the closure, with the theta tori as fibres, and let $a$ be a generic parameter. Let $\alpha$ be an arc whose generic point is the complex point at $a$ and whose closed point lies over a good prime. Then $C$ is smooth over $\operatorname{Spec} R$ of relative dimension $n - 1$ on an open set through which $\alpha$ factors.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_smooth_near_arc` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* Apply the smoothness criterion with $d = n - 1$. The analytic family through $a$ is a holomorphic immersion, and its points near $a$ are specializations of the point at $a$, since $a$ is generic. For condition 6, the model of the generic fibre extends along the arc with a full level structure, and the closed fibre is rigid (`hasSpanningCoords_of_specMap_comp_eq`). The tangent bound applies. $\square$

### Existence

**Theorem (Existence of the universal family).** Let $M$ be a submonoid of $\mathcal{O}_E$ of nonzero divisors, let $R$ be the localization of $\mathcal{O}_E$ at $M$, and let $D$ be good over $R$. Then a universal family for $D$ over $R$ exists.

Lean: `New.Variety.ThetaNull.nonempty_universalFamily` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* $R$ is a Dedekind domain, as a localization of $\mathcal{O}_E$ (`IsLocalization.isDedekindDomain`). The level torsion is finite, since the level is not $0$. Let $C$ be the theta closure of all parameters. By the lemmas above, finitely many analytic families have dense generic points, $C$ carries a theta family $X$ with the theta tori as fibres, and every point $z$ of $C$ specializes to the centre of an arc $\alpha_z$ over a good prime through a generic point. Each arc factors through a smooth open set $U_z$ of relative dimension $n - 1$. Open sets are closed under generization, so $z \in U_z$. So the $U_z$ cover $C$, and $C$ is smooth of relative dimension $n - 1$. The points $\mathrm{obj}(f, b)$ are the points of $C$ at the parameters, dense by construction. $\square$

**Remark (Formalization).** In the use in Section 1 the maximal ideals of $R$ are the safe places, and $D$ is good over $R$ by `New.Variety.pel_good_of_safe` (Section 2).
