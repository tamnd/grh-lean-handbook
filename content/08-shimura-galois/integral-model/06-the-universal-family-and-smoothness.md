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

The moduli space of the textbook is smooth because its deformation theory is unobstructed. For the unitary groups of signature $(1, n-1)$ this is the Serre-Tate theorem together with the deformation theory of a $p$-divisible group with an action, as in Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties*, Lemma III.4.1. The base of the source is a closure, and its smoothness must be proved in a different way. The source gives a lower bound and an upper bound. The lower bound comes from complex analysis: an analytic family of tori with $n - 1$ parameters passes through each complex point and is an immersion. The upper bound comes from deformation theory over the residue field: a first-order deformation without constant directions has at most $n - 1$ parameters. A criterion of commutative algebra then gives smoothness of relative dimension $n - 1$.

### The model case

Take $n = 1$. Then both bounds are $0$. The lower bound is empty. The upper bound says that a CM abelian variety with its action and polarization has no first-order deformations over the residue field. This is a form of the rigidity of CM abelian varieties with their extra structure. The criterion then says that the base is étale over $\operatorname{Spec} R$ near each point.

### Good rings

**Definition (Good over $R$).** Let $R$ be an $\mathcal{O}_E$-subalgebra of $E$. The datum $D$ is *good over $R$* when for every maximal ideal $\mathfrak{m}$ of $R$, $D$ is good (Section 2) at the prime $\mathfrak{m} \cap \mathcal{O}_E$.

Lean: `New.Variety.ThetaNull.IsGoodOver` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

**Lemma (Units of a good ring).** If $D$ is good over $R$, then $\bar\beta - \beta$ and $|D.\mathrm{dualTorsion}|$ are units of $R$.

Lean: `New.Variety.ThetaNull.isUnit_star_sub_and_card_of_isGoodOver` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* If the product is not a unit, it lies in a maximal ideal $\mathfrak{m}$. Let $w = \mathfrak{m} \cap \mathcal{O}_E$. Since $D$ is good at $w$, the order of the torsion is not in $w$. So $\bar\beta - \beta \in w$. Goodness gives an integer $b$ with $\beta - b \in w$ and $\beta - b$ coprime to $\bar\beta - b$. Then $\bar\beta - b = (\bar\beta - \beta) + (\beta - b) \in w$, so both lie in $w$, which contradicts coprimality. $\square$

These are the hypotheses on units in the theorem on theta families from points (Section 5).

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

The analytic families are those of [Chapter 1](/chapter/complex-abelian-varieties/): families of theta tori with a fixed adelic frame over an open set of $\mathbb{C}^{n-1}$, with analytic periods and injective differential modulo $\mathbb{C}$-linear maps.

**Remark (Formalization).** The name says "universal", but the structure asks for no universal property. It does not say that every theta family over an $R$-scheme is a pull-back of this one. The only moduli statement is the rigidity field of the theta family (Section 5): a point of $S$ is determined by the coordinates of its level points. Section 7 uses this rigidity to compare points of the covers. The structure also does not say that the points $\mathrm{obj}(f, b)$ are all the complex points. For the covers of Section 7 the source proves a statement of this kind separately (`New.Variety.UniversalFamily.GraphClosure.point_surjective`).

### The closure of the level points

The base is a closure. Each parameter $a$ of an analytic family gives a theta torus, and each level point $\omega$ gives the vector of theta coordinates $(\theta_s(\text{lift of } \omega))_{s}$ of that torus. This is a point of the projective space $\mathbb{P}^{T}$ over $R$.

**Definition (Theta closure).** For a family $y$ of parameters, the *theta closure* is the reduced closure of the points $(\text{level point } \omega \text{ at } y_b)_{\omega}$ in the product over $\omega$ of the projective spaces $\mathbb{P}^T_R$.

Lean: `New.Variety.ThetaNull.ThetaClosure` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

The proof of existence has four steps, each a lemma about the closure $C$ of all parameters.

**Lemma (Finitely many dense families).** If $D$ is good over $R$, the generic points of finitely many analytic families are dense in $C$.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_finite_isDenseFamily` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

The idea is that $C$ is noetherian, so it has finitely many irreducible components, and each component contains the generic point of one analytic family. A point $b$ of the domain of a family $F$ is *generic* when the point of $C$ at $b$ specializes to the points at all parameters in the domain.

**Lemma (A theta family on the closure).** Let $R$ be the localization of $\mathcal{O}_E$ at a submonoid $M$, with $D$ good over $R$. If finitely many parameters are dense in $C$, there is a theta family $X$ over $C$ whose fibre at each complex point $b$ has a model on the theta torus at $y_b$ with the same theta coordinates.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_hasThetaFibres` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* Apply the theorem on theta families from points (Section 5). Its hypotheses are checked as follows. The units come from the lemma above. The linear systems are the coordinate bundles of the factors $\mathbb{P}^T$, and their product embeds $C$ (`isProjEmbedding_pi_coordBundle`). For the specialization hypothesis, let $t$ be a point of $C$. By the next lemma it is the centre of an arc $\alpha$ over a good prime, through a complex point. The closed point of the arc is a geometric point over the residue field of a valuation ring $O_v$ of $\mathbb{C}$. Over this valuation the theta torus has good reduction (Section 3), and the theorem on reduction of the theta points (Section 4) shows that the coordinate bundles cut out the reduced theta vectors there. The nonvanishing indices come from the theta-null lemma of Section 4, at the same valuation. $\square$

**Lemma (Arcs over good primes).** Let $R$ be noetherian with $D$ good over $R$, and let finitely many points be dense in $C$. Then every point $z$ of $C$ is the specialization of the centre of an arc through one of them, and the arc lies over a good prime.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_arc_isGoodAt` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

An arc here is a morphism $\operatorname{Spec} V \to C$ for a valuation subring $V$ of $\mathbb{C}$. Its generic point is a complex point. Such arcs exist by the valuative criterion in the form for schemes of finite type over a noetherian ring: a point in the closure of a set of complex points is the image of the closed point of a valuation ring of $\mathbb{C}$ (the source proves the form it needs).

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

*Proof.* By condition 6, the relative tangent space of $X$ at $t$ has dimension at most $d$. So there are $d$ functions near $t$ that give a map $X \to \mathbb{A}^d_R$ which is unramified at $t$. Locally, an unramified map is a closed subscheme of a standard étale algebra. Conditions 3 and 4 make the map dominant near $\varphi_{w_0}$: the complex points of the family have $d$ independent parameters, so their image is not in a proper closed subset. A quotient of a standard étale algebra over a normal domain that is dominant in this sense is étale after inverting a function that is a unit on the arc (the lemma `New.Variety.exists_etale_away_of_faithful`, which uses that the minimal polynomial over a normal domain divides the polynomial of the standard étale algebra). So $X$ is étale over $\mathbb{A}^d_R$ near the arc, hence smooth of relative dimension $d$ over $R$. $\square$

The lower bound comes from Chapter 1 and the file `Lib/Shimura/IntegralModel/BallImmersion.lean`: the points of an analytic family form a holomorphic immersion at each parameter (`New.Variety.AnalyticFamily.isHolomorphicImmersionAt_of_holomorphicAt`). The upper bound is the subject of the rest of this section.

### Drinfeld's lifting lemma

Let $k$ be a field, $k[\varepsilon]$ the dual numbers, and $x, x'$ two first-order deformations over $k[\varepsilon]$ of one object $x_0$ over $k$ of a theta family. Write $A, A', A_0$ for their group schemes.

**Lemma (Drinfeld's lifting lemma).** Let $c \in \mathcal{O}_E$ kill every point of $A'$ that vanishes modulo $\varepsilon$. Then there is an additive morphism $F : A \to A'$ that reduces to multiplication by $c$ on $A_0$. In addition, $yF = c\,y'$ for all points $y$ of $A$ and $y'$ of $A'$ that agree modulo $\varepsilon$.

Lean: `New.Variety.drinfeld_lift` (Lib/Shimura/Deformation/TangentBound.lean).

This is the lemma of Drinfeld in Katz, *Serre-Tate local moduli*, LNM 868 (1981), §1. The idea of the proof: for a point $y$ of $A$, choose locally a point $y'$ of $A'$ with the same reduction, which exists because $A'$ is smooth, and put $F(y) = c\,y'$. Two choices differ by a point that vanishes modulo $\varepsilon$, which $c$ kills. So $F$ is well defined, it glues, and it is additive.

### Counting torsion points

The upper bound is proved on the finite group scheme of $w$-torsion, where $w$ is the kernel of the structure map $\mathcal{O}_E \to k$. For a local $k$-algebra $C$, let $\mathrm{placeTorsion}(x, C)$ be the $\mathcal{O}_E$-module of the $C$-points of $A_0$ killed by $w$.

**Lemma (Counting torsion points).** Let $k$ be algebraically closed, and let $x$ over $k$ be the reduction at a good place $w$ of an object $y$ over a valuation subring of $\mathbb{C}$ with a full level structure. Let $W$ be a $k$-vector space, and let $f$ attach to each $l \in W$ and each local $k$-algebra $C$ a function on $\mathrm{placeTorsion}(x, C)$ with values in $C$, semilinear along $\mathcal{O}_E \to k$ in the point and linear in $l$. Assume:

1. $f$ is natural in $C$;
2. $f$ vanishes on the points over $k[\varepsilon]$ that reduce to $0$;
3. only $l = 0$ gives a function that is zero on all finite local $C$.

Then $\dim_k W \leq n - 1$.

Lean: `New.Variety.finrank_le_of_placeTorsion` (Lib/Shimura/Deformation/TangentCount.lean).

The idea, from the comments in the proof, is the following. Let $\mathbb{F}_q$ be the residue field $\mathcal{O}_E/w$ and $d$ the dimension of $\mathrm{placeTorsion}(x, k)$ over $\mathbb{F}_q$. The full level structure gives $q^n$ torsion sections, and they map onto the $k$-points, so $q^{n-d}$ of them pass through $0$. The local ring of the $w$-torsion at the origin is then $k[\tau]$ with $\tau$ nilpotent of order at most $q^{n-d}$. Semilinearity makes $z \mapsto f(k, z)$ linear over $\mathbb{F}_q$, and an $\mathbb{F}_q$-linear map $a \mapsto a^i$ on $k$ has $i$ a power of $q$ (the lemma `New.Variety.mem_powers_card_of_isLinearMap_pow`). So the lowest term of $f$ on the universal point has degree $q^j$ with $0 < j < n - d$; condition 2 excludes $j = 0$. The values of $l$ on the $k$-points and the coefficients of $\tau^{q^j}$ for $0 < j < n - d$ determine $l$, by condition 3. This gives $\dim_k W \leq d + (n - d - 1) = n - 1$.

**Remark (Formalization).** The textbook upper bound uses the $p$-divisible group and the Serre-Tate theorem, or Grothendieck-Messing theory (Harris and Taylor, Lemma III.4.1). The source docstring says that it works "on the finite group scheme of w-torsion with Drinfeld's lifting lemma and without p-divisible groups or crystals". The book does not reproduce the counting argument in full. It states the hypotheses and the conclusion as the source states them.

### The tangent bound

**Theorem (Tangent bound).** Let $k$ be algebraically closed, $M$ a $k$-vector space, $x_0$ an object of a theta family over $k$, and $x$ an object over the square-zero extension $k \oplus M^*$. Assume:

1. $D$ is good at the kernel of $\mathcal{O}_E \to k$;
2. $x_0$ is rigid (`New.ThetaObject.HasSpanningCoords`) and is the fibre of an object $w$ over a valuation subring of $\mathbb{C}$ that has a full level structure;
3. $x$ reduces to $x_0$, and $\mathcal{O}_E$ maps to $k \oplus M^*$ through $k$;
4. for $l \neq 0$ in $M$, the pull-back of $x$ along $k \oplus M^* \to k[\varepsilon]$, $(a, \phi) \mapsto a + \phi(l)\varepsilon$, is not the constant deformation of $x_0$.

Then $\dim_k M \leq |D.\mathrm{Index}| - 1$.

Lean: `New.Variety.finrank_tangent_le_card_index_sub_one` (Lib/Shimura/Deformation/TangentBound.lean).

*Proof.* Let $\mathfrak{p}$ be the kernel of $\mathcal{O}_E \to k$. Since $\mathfrak{p}$ is good, the source gets $c \neq 0$ in $\mathfrak{p}$ and $t \equiv 1 \pmod{\mathfrak{p}}$ with $t\mathfrak{p} \subseteq (c)$, and an integer $b$ with $\beta - b \in \mathfrak{p}$ coprime to $\bar\beta - b$. For a point $y$ of $A_0$ killed by $\mathfrak{p}$, with values in a local algebra $C$, lift it to a point $Y(y)$ of $A$ over $C \oplus \operatorname{Hom}(M, C)$. Then $c\,Y(y)$ is infinitesimal, and its logarithm on the tangent line gives a map $f(C, y) : M \to C$. Drinfeld's lemma makes $f$ independent of the lift and natural in $C$. Points over $k[\varepsilon]$ that reduce to $0$ have logarithm $0$, and condition 4 gives the separation in $M$. The counting lemma gives $\dim_k M \leq n - 1$. $\square$

**Lemma (Smooth near each arc).** Let $X$ be the theta family on the closure, with the theta tori as fibres, and let $a$ be a generic parameter. Let $\alpha$ be an arc whose generic point is the complex point at $a$ and whose closed point lies over a good prime. Then $C$ is smooth over $\operatorname{Spec} R$ of relative dimension $n - 1$ on an open set through which $\alpha$ factors.

Lean: `New.Variety.ThetaNull.ThetaClosure.exists_smooth_near_arc` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* Apply the smoothness criterion with $d = n - 1$. The family of complex points is the analytic family through $a$; it is a holomorphic immersion at $a$, and near $a$ its points are specializations of the point at $a$ because $a$ is generic. For condition 6, the model of the generic fibre extends along the arc, and it gives a full level structure over the valuation ring and rigidity of the closed fibre (`hasSpanningCoords_of_specMap_comp_eq`). The tangent bound then applies. $\square$

### Existence

**Theorem (Existence of the universal family).** Let $M$ be a submonoid of $\mathcal{O}_E$ of nonzero divisors, let $R$ be the localization of $\mathcal{O}_E$ at $M$, and let $D$ be good over $R$. Then a universal family for $D$ over $R$ exists.

Lean: `New.Variety.ThetaNull.nonempty_universalFamily` (Lib/Shimura/ThetaModuli/UniversalFamily.lean).

*Proof.* $R$ is a Dedekind domain, as a localization of $\mathcal{O}_E$ (`IsLocalization.isDedekindDomain`). The level torsion is finite, since the level is not $0$. Let $C$ be the theta closure of all parameters. By the lemmas above, finitely many analytic families have dense generic points, $C$ carries a theta family $X$ with the theta tori as fibres, and every point $z$ of $C$ lies on an arc $\alpha_z$ over a good prime through a generic point. Each arc has a smooth open neighbourhood $U_z$ of relative dimension $n - 1$. Every $z$ specializes from the centre of $\alpha_z$, and open sets are closed under generization, so $z \in U_z$. So the $U_z$ cover $C$, and $C$ is smooth of relative dimension $n - 1$. The complex points $\mathrm{obj}(f, b)$ are the points of $C$ at the parameters, with the models of $X$, and they are dense by construction of the closure. $\square$

**Remark (Formalization).** In the use in Section 1, $M$ is the intersection of the complements of the safe places, so the maximal ideals of $R$ are the safe places, and $D$ is good over $R$ by the lemma `New.Variety.pel_good_of_safe` of Section 2. The family depends on no choice that the later sections see: the proof of the existence of the model uses only the fields of the structure.
