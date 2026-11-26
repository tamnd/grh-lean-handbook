---
title: Fibre measures and hermitian quadrics
lean:
  - Lib/General/Measure/FibreMeasure.lean
  - Lib/General/Measure/QuadricDisintegration.lean
decls:
  - New.le_of_setLIntegral_le
  - New.LeFibreMeasure
  - New.LeFibreMeasure.of_coordinates
  - New.LeFibreMeasure.map
  - New.Floors.TraceOne
  - New.Floors.Place
  - New.Floors.Place.flatChart
  - New.Floors.Place.form_flatChart
  - New.Floors.Place.quadricMeasure
  - New.Floors.Place.IsDisintegration
  - New.Floors.Place.isDisintegration_quadricMeasure
  - New.Floors.Place.IsDisintegration.unique
  - New.Floors.Place.IsDisintegration.map
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Fibre measures and hermitian quadrics

Let $\pi : X \to B$ be a submersion of manifolds, and let $\mu$ and $\nu$ be smooth positive measures on $X$ and $B$. Then each fibre $\pi^{-1}(b)$ carries a measure $\mu_b$, written $d\mu/d\nu$, with two properties. First, $\int_X f \, d\mu = \int_B \int f \, d\mu_b \, d\nu(b)$ for $f \geq 0$. Second, $b \mapsto \int f \, d\mu_b$ is continuous for $f$ continuous with compact support. The two properties determine $\mu_b$ at every point $b$, and not only for almost every $b$. These are the fibre measures of Weil (*Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), no. 6). The formula of Siegel and Weil and the orbital integrals of the trace formula integrate over level sets of quadratic and hermitian forms in this way.

The source has two tools for these measures. The first is an upper bound for a fibre measure on a general space. The second is an exact construction for the level sets of a hermitian form over a "place", that is, a locally compact ring such as $\mathbb{C}$ or a finite product of completions.

### Measures below a fibre measure

The upper bound rests on a mean value principle.

**Lemma.** Let $\nu$ be a locally finite measure on $B$ that is positive on nonempty open sets. Let $A : B \to [0, \infty]$ be lower semicontinuous at $b$, and let $C \in [0, \infty]$. Assume that $\int_S A \, d\nu \leq C \, \nu(S)$ for every open set $S$ in some fixed neighbourhood of $b$. Then $A(b) \leq C$.

Lean: `New.le_of_setLIntegral_le` (Lib/General/Measure/FibreMeasure.lean).

*Proof.* Let $c < A(b)$. By lower semicontinuity, $A > c$ on a small open neighbourhood $S$ of $b$ with $0 < \nu(S) < \infty$. Then $c \, \nu(S) \leq \int_S A \, d\nu \leq C \nu(S)$, so $c \leq C$. $\square$

**Definition (Measure below a fibre measure).** Let $\mu$ be a measure on $X$, $\nu$ a measure on $B$, $\pi : X \to B$ a map and $b \in B$. A measure $l$ on $X$ is below the fibre measure of $\pi$ over $b$ if the following holds for every lower semicontinuous $K : X \to [0, \infty]$ and every $C \in [0, \infty]$. If
$$\int_{\pi^{-1}(S)} K \, d\mu \leq C \, \nu(S)$$
for every open set $S$ in some fixed neighbourhood of $b$, then $\int K \, dl \leq C$.

Lean: `New.LeFibreMeasure` (Lib/General/Measure/FibreMeasure.lean).

If the fibre measure $\mu_b$ exists, then $\mu_b$ satisfies this definition. The hypothesis says that the mean of $t \mapsto \int K \, d\mu_t$ over small sets $S$ is at most $C$. The mean value lemma then gives $\int K \, d\mu_b \leq C$, when the fibre integral is lower semicontinuous.

**Theorem.** Let $\rho$ be an s-finite measure on a space $P$. Let $V$ be a neighbourhood of $b$ in $B$, and let $\psi : B \times P \to X$ and $w : B \times P \to [0, \infty]$ be measurable. Assume:

1. for $t \in V$ and almost every $p$ with $w(t, p) \neq 0$, we have $\pi(\psi(t, p)) = t$;
2. for almost every $p$, the maps $t \mapsto \psi(t, p)$ and $t \mapsto w(t, p)$ are continuous at $b$;
3. for every measurable $K \geq 0$, $\int_V \int_P w(t, p) K(\psi(t, p)) \, d\rho(p) \, d\nu(t) \leq \int_X K \, d\mu$.

Then the image of $w(b, p) \, d\rho(p)$ under $\psi(b, \cdot)$ is below the fibre measure of $\pi$ over $b$. Here $B$ is first countable, and $\nu$ is locally finite and positive on open sets.

Lean: `New.LeFibreMeasure.of_coordinates` (Lib/General/Measure/FibreMeasure.lean).

*Proof.* Let $A(t) = \int_P w(t, p) K(\psi(t, p)) \, d\rho(p)$. By the continuity at $b$ and Fatou's lemma, $A$ is lower semicontinuous at $b$. For a small open $S$, condition 3 applied to $K \cdot 1_{\pi^{-1}(S)}$ and condition 1 give $\int_S A \, d\nu \leq \int_{\pi^{-1}(S)} K \, d\mu \leq C \nu(S)$. The mean value lemma gives $A(b) \leq C$. $\square$

The relation is kept by the usual operations. For example, if $l$ is below the fibre measure of $\pi_0 \circ \varphi$ over $b$, and $\varphi$ is continuous, then $\varphi_* l$ is below the fibre measure of $\pi_0$ for $\varphi_* \mu$.

Lean: `New.LeFibreMeasure.map` (Lib/General/Measure/FibreMeasure.lean). The source also proves the forms `New.LeFibreMeasure.trans`, `New.LeFibreMeasure.map_prod`, `New.LeFibreMeasure.smul` and `New.LeFibreMeasure.mono`.

**Remark (Formalization).** The file does not construct fibre measures. It proves only that certain measures are below them. The zero measure is below every fibre measure, because $\int K \, d0 = 0 \leq C$. So a statement that $l$ is below a fibre measure gives an upper bound for integrals against $l$, and no lower bound. The users of the relation need only upper bounds: they bound an integral over a fibre by a constant. The definition quantifies over all $C$, including $C = \infty$, for which the conclusion holds trivially.

### Places and hermitian quadrics

For exact fibre measures the source fixes a class of rings. Let $A$ be a commutative ring with an involution $x \mapsto \bar x$. An element $a$ is skew if $\bar a = -a$.

**Definition (Trace one element).** A trace one element of $A$ is an element $\tau$ with $\tau + \bar\tau = 1$.

Lean: `New.Floors.TraceOne` (Lib/General/Measure/QuadricDisintegration.lean).

**Definition (Place).** A place is a commutative ring $A$ with involution and a trace one element $\tau$, together with these data:

1. a topology that makes $A$ a locally compact Polish topological ring with continuous involution, and a Haar measure $dx$ on $A$;
2. a skew unit $\delta$, and a Haar measure $\nu$ on the group of skew elements;
3. a multiplicative map $|\cdot| : A \to [0, \infty]$, the modulus;
4. a continuous additive character $\psi : A \to \mathbb{C}$ with $|\psi| = 1$, and a bound $c \in [0, \infty]$.

The data satisfy these conditions:

1. the map $(a, b) \mapsto \tau\delta^{-1} a + b$ from pairs of skew elements to $A$ carries $\nu \times \nu$ to $dx$;
2. $|\bar x| = |x|$ and $|-x| = |x|$;
3. an $n \times n$ matrix $M$ with $\det M$ a unit maps $dx$ on $A^n$ to $|\det M|^{-1} dx$;
4. almost every element of $A$ is a unit;
5. $|u|^{-1} \leq |g(u)|^2$ on the units, for some locally integrable $g$;
6. some continuous integrable $G \geq 0$ with $G(0) = 1$ has $\int_A \left| \int_A G(v) \psi(\bar v z) \, dv \right| dz \leq c$.

Lean: `New.Floors.Place` (Lib/General/Measure/QuadricDisintegration.lean).

For $A = \mathbb{C}$ with complex conjugation, one can take $\tau = \tfrac12$, $\delta = i$, $\nu$ a multiple of Lebesgue measure on $i\mathbb{R}$, and $|x| = |x|^2_{\mathbb{C}}$. Then conditions 1 to 5 are classical facts about Lebesgue measure on $\mathbb{C}^n$.

Now let $T$ be an $m \times m$ hermitian matrix over $A$. Let $h$ be the hermitian form on $A^{2+m}$ with Gram matrix
$$J_T = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \oplus T,$$
a hyperbolic plane plus $T$. Write the vectors as $(x_1, x_2, w)$. For each skew $b$, the quadric $Q_b$ is the level set $h(x, x) = \delta^{-1} b$. The element $\delta^{-1} b$ is fixed by the involution, so every value of $h(x, x)$ has this form.

**Lemma.** Let $T$ be hermitian and let $b$ be skew. For a unit $t$, a vector $w \in A^m$ and a skew $a$, let
$$\phi_b(t, w, a) = \left( \bar t^{-1} \tau \left( \delta^{-1} b - h_T(w, w) \right) + t a, \; t, \; w \right).$$
Then $h(\phi_b(t, w, a), \phi_b(t, w, a)) = \delta^{-1} b$.

Lean: `New.Floors.Place.form_flatChart` (Lib/General/Measure/QuadricDisintegration.lean). The map itself is `New.Floors.Place.flatChart`.

*Proof.* Let $x_1$ be the first coordinate and $q = h_T(w, w)$. Then $h(x, x) = \bar x_1 t + \bar t x_1 + q$. Here $\bar t x_1 = \tau(\delta^{-1} b - q) + \bar t t a$. The element $\delta^{-1} b - q$ is fixed by the involution and $\bar a = -a$. So the sum of $\bar t x_1$ and its conjugate is $(\tau + \bar\tau)(\delta^{-1} b - q) = \delta^{-1} b - q$. Add $q$. $\square$

**Definition (Quadric measure).** The quadric measure $l_b$ is the image of $dt \, dw \, d\nu(a)$ under $\phi_b$.

Lean: `New.Floors.Place.quadricMeasure` (Lib/General/Measure/QuadricDisintegration.lean).

**Remark (Formalization).** The chart uses the ring inverse $\bar t^{-1}$, which the source defines as $0$ when $\bar t$ is not a unit. So $\phi_b$ is defined on all of $A \times A^m \times A^-$, where $A^-$ is the group of skew elements, and its value at a non-unit $t$ need not lie on $Q_b$. Condition 4 of a place says that almost every $t$ is a unit. So the non-units form a null set for $dt$, and the image measure does not see them. The proofs restrict to units at the start for this reason.

### Disintegration

**Definition (Disintegration).** Let $\mu$ be a measure on $A^n$ and $J$ an $n \times n$ matrix. A family $(l_b)$ of measures on $A^n$, indexed by the skew elements $b$, disintegrates $\mu$ along $h_J(x, x) = \bar x^t J x$ if:

1. for continuous $f \geq 0$ with compact support, $b \mapsto \int f \, dl_b$ is finite and continuous;
2. for measurable $f \geq 0$ on $A \times A^n$,
$$\int f(h_J(x, x), x) \, d\mu(x) = \int \int f(\delta^{-1} b, x) \, dl_b(x) \, d\nu(b).$$

Lean: `New.Floors.Place.IsDisintegration` (Lib/General/Measure/QuadricDisintegration.lean).

**Theorem.** Let $T$ be hermitian. Then the quadric measures $(l_b)$ disintegrate the Haar measure on $A^{2+m}$ along $h(x, x)$, for the Gram matrix $J_T$.

Lean: `New.Floors.Place.isDisintegration_quadricMeasure` (Lib/General/Measure/QuadricDisintegration.lean).

*Proof.* Both conditions are checked in the coordinates $(t, w, a)$, where one may take $t$ to be a unit. For the integral formula, change variables from $x_1$ to $(a, b)$. For fixed $t$ and $w$, the map $(a, b) \mapsto x_1$ is affine, and conditions 1 and 3 of a place compute its effect on the measures. For the continuity, the fibre integrals have a majorant that does not depend on $b$, and dominated convergence applies. $\square$

**Theorem.** Two disintegrations $(l_b)$ and $(l'_b)$ of the same measure along the same form agree at every skew $b$.

Lean: `New.Floors.Place.IsDisintegration.unique` (Lib/General/Measure/QuadricDisintegration.lean).

*Proof.* Let $f \geq 0$ be continuous with compact support. By the integral formula with $f(\delta^{-1}b, x) 1_S(b)$, the functions $b \mapsto \int f \, dl_b$ and $b \mapsto \int f \, dl'_b$ have the same integral over every measurable set $S$. So they agree almost everywhere. Both are continuous and $\nu$ is positive on open sets, so they agree everywhere. Measures that agree on such $f$ are equal. $\square$

**Theorem.** Let $(l_b)$ disintegrate $\mu$ along $h_T$. Let $M$ be a matrix with a left inverse $L$, so that $LM = 1$, and with $M^* J M = T$. Then the images $M_* l_b$ disintegrate $M_* \mu$ along $h_J$.

Lean: `New.Floors.Place.IsDisintegration.map` (Lib/General/Measure/QuadricDisintegration.lean).

*Proof.* The identity $h_J(Mx, Mx) = h_T(x, x)$ moves the integral formula. The map $x \mapsto Mx$ has the continuous left inverse $x \mapsto Lx$, so it is a closed embedding. So if $f$ has compact support, so does $f \circ M$, and the continuity condition moves too. $\square$

The three theorems together give fibre measures on all hermitian quadrics of the form "hyperbolic plane plus $T$", and on their images under the maps $M$ of the last theorem. They are exact, unlike the upper bounds of the first part.

**Remark (Formalization).** Every theorem of this part assumes the class `New.Floors.Place`. The class is a hypothesis: the file proves no theorem about a specific ring. A user must build an instance. Row F-085 of [the register of findings](/chapter/register-of-findings/) records the class, and says that the disintegration is conditional on the class. The source builds one in New/Spanning/MainTerm/FillingLevel.lean:424, for a product of completions. There the modulus is $x \mapsto \iota(x)^{-1}$, with $\iota$ the generalised index of the section on moduli. At a non-unit $\iota(x) = 0$, and the inverse in $[0, \infty]$ is $\infty$. So the modulus of a non-unit is $\infty$ there. Condition 2 holds at a non-unit for this reason, and the other conditions use the modulus only at units. So this value does not enter. The class `New.Floors.TraceOne` carries data, the element $\tau$. The file adds a global instance that takes $\tau = 2^{-1}$ in every field of characteristic $0$. A place extends `TraceOne`, so a place structure on such a field carries its own $\tau$, which need not be $2^{-1}$. Lean then has two routes to a trace one element, and they need not agree. The statements of the file use the $\tau$ of the place, so they are not affected. A statement elsewhere that mixes the two routes could be. The file also makes the field `haar` of a place an instance (line 225), so that the measure $\nu$ is a Haar measure in every proof without an explicit argument.
