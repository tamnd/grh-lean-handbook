---
title: Pairing sides and the pairing lemma
lean:
  - New/Congruences/Lifting/CupProductBound.lean
decls: [New.Lift.KummerChart.PairingSide, New.Lift.KummerChart.PairingSide.extensionLattice, New.Lift.KummerChart.PairingSide.trivialLattice, New.Lift.KummerChart.PairingSide.projTrivial, New.Lift.KummerChart.PairingSide.wittFst, New.Lift.KummerChart.PairingSide.tensorLattice, New.Lift.Pairing.tateDualSide, New.Lift.Pairing.wittPairing, New.Lift.Pairing.IsSafe, New.Lift.Pairing.IsSafeMoveFst, New.Lift.Pairing.IsSafeMoveSnd, New.Lift.Pairing.IsSafePath, New.Lift.Pairing.IsScaledCupCoboundary, New.Lift.wittFst_smul, New.Lift.Pairing.smul_wittPairing, New.Lift.Pairing.isCupCoboundary_of_eq_coboundary, New.Lift.eventually_smul_sub_mem_smallPart, New.Lift.Pairing.phi_smul_sub_mem_smallPart, New.Lift.Pairing.nsmul_modPairing_eq_coboundary, New.Lift.Pairing.IsScaledCupCoboundary.of_isSafePath]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Pairing sides and the pairing lemma

The lattices of the earlier sections now carry cocycles. A cup product of two cocycles is a class in $H^2$ with values in $\overline{\mathbb{Q}}_p^\times$. This section gives a test that a multiple $p^e$ of the class is zero. The test uses lifts of the cocycles to $W(C^\flat)$ and four moves between them. It holds on all of $\Gamma$, not only on $\Gamma'$.

### Sides

**Definition (Side).** A *side* $S$ consists of a lattice $Y$ with jump sets, a lattice $C$ with an action of $\Gamma$, and an $\mathcal{O}$-linear map $\alpha : C \to Z_f(Y)$ into the crystalline cocycles. Every jump set of the side contains $0$.

Lean: `New.Lift.KummerChart.PairingSide` (New/Congruences/Lifting/CupProductBound.lean).

The crystalline cocycles $Z_f(Y)$ are those whose extension is crystalline over $\Gamma'$ ([crystalline classes](/chapter/period-rings/)).

**Definition (The lattices of a side).** Let $S$ be a side.

1. The *extension lattice* is $Y \times C$ with $g(y, c) = (gy + \alpha(c)(g), c)$. Its jump sets at the letters are those of $S$; at the embeddings of $\mathcal{O}$ it adds $0$.
2. The *trivial lattice* is $C$ with the trivial action and the jump set $\{0\}$.
3. $\mathrm{pr}$ is the projection onto $C$. It is a map of lattice data.
4. $\mathrm{fst}$ is the $W(C^\flat)$-linear extension of the projection onto $Y$.
5. For two sides $S$, $S'$, the *tensor lattice* is $Y \otimes_{\mathcal{O}} Y'$ with jump set $U(i) + U'(i)$ at the letter $i$.

Lean: `New.Lift.KummerChart.PairingSide.extensionLattice`, `New.Lift.KummerChart.PairingSide.trivialLattice`, `New.Lift.KummerChart.PairingSide.projTrivial`, `New.Lift.KummerChart.PairingSide.wittFst`, `New.Lift.KummerChart.PairingSide.tensorLattice` (New/Congruences/Lifting/CupProductBound.lean).

The extension is crystalline because $\alpha$ takes values in $Z_f(Y)$. A nonzero jump of the extension is a jump of $Y$, and this is why the side must contain $0$ in each jump set.

A *pairing* $P$ of the lattices $Y$ and $Y'$ is an equivariant pairing $Y \times Y' \to \mathbb{Z}/p^m(1)$, the reduction of a form $\psi$ with $g\psi - \psi = p^m c_P(g)$ for a crystalline cocycle $c_P$ ([local duality](/chapter/local-duality/)).

**Definition (The third side).** For a pairing $P$, the *Tate dual side* has the lattice $\mathrm{Hom}(Y \otimes Y', \mathcal{O}(1))$, the parameter lattice $\mathcal{O}$ with $1 \mapsto c_P$, and jump sets $\{0\} \cup \{-u - u' - 1\}$ at the letters, with $u$ and $u'$ jumps of $S$ and $S'$.

Lean: `New.Lift.Pairing.tateDualSide` (New/Congruences/Lifting/CupProductBound.lean).

### Safe pairs

Let $\langle\ ,\ \rangle$ be the $W(C^\flat)$-bilinear extension of $P$, with values in $W(C^\flat) \otimes \mathbb{Z}/p^m(1)$. The *small part* is $W(\mathfrak{m}^\flat)\cdot(1 \otimes 1)$ in this module ([period rings](/chapter/period-rings/)).

**Definition (Safe).** Fix $e \in \mathbb{N}$. Let $w$ and $y$ lie in the ambient modules of the two extension lattices.

1. $(w, y)$ is *safe* if $p^e\langle \mathrm{fst}\,w, \mathrm{fst}\,y\rangle$ is small.
2. A move of the first side by $y$ with $x'$ at rest is safe if $(y, gx' - x')$ is safe for every $g \in \Gamma'$.
3. A move of the second side by $y'$ with $x$ at rest is safe if $(gx - x, gy')$ is safe for every $g \in \Gamma'$.
4. A *safe path* from $(y, y')$ to $(x, x')$ through $(w, w')$ is four safe moves: the first side by $y - w$ with $y'$ at rest, the second by $y' - w'$ with $w$ at rest, the first by $w - x$ with $w'$ at rest, and the second by $w' - x'$ with $x$ at rest.

Lean: `New.Lift.Pairing.wittPairing`, `New.Lift.Pairing.IsSafe`, `New.Lift.Pairing.IsSafeMoveFst`, `New.Lift.Pairing.IsSafeMoveSnd`, `New.Lift.Pairing.IsSafePath` (New/Congruences/Lifting/CupProductBound.lean).

**Definition (Scaled cup coboundary).** For $c \in C$ and $c' \in C'$, the pair is a *scaled cup coboundary with exponent $e$* if the cup product of $\alpha(c)$ and $p^e\alpha'(c')$ under $P$, read in $\overline{\mathbb{Q}}_p^\times$, is the coboundary of a continuous cochain.

Lean: `New.Lift.Pairing.IsScaledCupCoboundary` (New/Congruences/Lifting/CupProductBound.lean).

**Remark (Formalization).** The group $\Gamma$ has no fixed topology in the source. The definition quantifies over every topology on $\Gamma$ for which the map to $G_p$ is an open embedding. The values of the cup product go to $\overline{\mathbb{Q}}_p^\times$ through $\mathbb{Z}/p^m \to \mu_{p^m}$.

### Two rules

**Lemma.** (1) For $n \in \mathbb{Z} \times \Gamma$ and $x$ in the extension ambient module, $\mathrm{fst}(nx) = n\,\mathrm{fst}(x) + \alpha_n(n\,\mathrm{pr}(x))$, where $\alpha_n$ is the $W(C^\flat)$-linear extension of $c \mapsto \alpha(c)(g)$ for the $\Gamma$-component $g$ of $n$. (2) $n\langle x, y\rangle = \langle nx, ny\rangle$. (3) Near $1$, the group fixes each element of $W(C^\flat) \otimes \mathbb{Z}/p^m(1)$ modulo the small part.

Lean: `New.Lift.wittFst_smul`, `New.Lift.Pairing.smul_wittPairing`, `New.Lift.eventually_smul_sub_mem_smallPart` (New/Congruences/Lifting/CupProductBound.lean).

*Proof.* (1) Both sides are additive in $x$. On a pure tensor $a \otimes (y, c)$ it is the formula $g(y,c) = (gy + \alpha(c)(g), c)$. (2) $P$ is equivariant, and so is its base change. (3) Near $1$ the cyclotomic character is $1$ modulo $p^m$, so $gt - t$ is a multiple of $p^m$ for $t$ in $\mathbb{Z}/p^m(1)$. The action of $g$ on $W(C^\flat)$ changes $a$ by an element of $W(\mathfrak{m}^\flat)$ near $1$ ([period rings](/chapter/period-rings/)). $\square$

**Lemma (From $\Gamma'$ to $\Gamma$).** Let $\Gamma \to G_p$ be an open embedding, and let $a$, $a'$ be crystalline cocycles of $Y$ and $Y'$. Suppose there is $\kappa : \Gamma' \to \mathbb{Z}/p^m$ that is $0$ near $1$ with
$$P(a(g), g\,a'(h)) = \chi(g)\kappa(h) - \kappa(gh) + \kappa(g)\quad (g, h \in \Gamma').$$
Then the cup product of $a$ and $a'$, read in $\overline{\mathbb{Q}}_p^\times$, is the coboundary of a continuous cochain on $\Gamma$.

Lean: `New.Lift.Pairing.isCupCoboundary_of_eq_coboundary` (New/Congruences/Lifting/CupProductBound.lean).

*Proof.* Let $b(g,h) = P(a(g), g\,a'(h))$. Near $1$, $a$ and $a'$ take values in $p^mY$ and $p^mY'$, so $b$ is locally constant. It is a $2$-cocycle. Near $1$, $\kappa(h) = 0$ and $b(g, h) = 0$, so $\kappa(gh) = \kappa(g)$; thus $\kappa$ is locally constant. On $\Gamma'$ the class of $b$ is the coboundary of $\kappa$, so its restriction to $\Gamma'$ is $0$. By corestriction, the index $[\Gamma : \Gamma']$ kills the class ([local duality](/chapter/local-duality/)). The values lie in $\mu_{p^m}$, so $p^m$ kills it too. The index is prime to $p$. So the class is $0$. $\square$

### The pairing lemma

**Theorem (Pairing lemma).** Let $e_1 + e_2 + e_3 \leq e$. Let $x$, $w$ lie over $p^{e_1}(1 \otimes c)$ and $x'$, $w'$ over $p^{e_2}(1 \otimes c')$, that is, $\mathrm{pr}(x) = \mathrm{pr}(w) = p^{e_1}(1 \otimes c)$ and $\mathrm{pr}(x') = \mathrm{pr}(w') = p^{e_2}(1 \otimes c')$. Assume:

1. for every $h \in \Gamma'$, the move of the second side by $hx' - x'$ with $x$ at rest is safe with exponent $e_3$;
2. there is a safe path with exponent $e_3$ from $(\varphi x, \varphi x')$ through $(w, w')$ to $(x, x')$.

Then $(c, c')$ is a scaled cup coboundary with exponent $e$.

Lean: `New.Lift.Pairing.IsScaledCupCoboundary.of_isSafePath` (New/Congruences/Lifting/CupProductBound.lean).

The proof uses two steps. Let $B(z) = p^{e_3}\langle \mathrm{fst}\,z, \cdot\,\rangle$. The map $\varphi - 1$ is onto $W(C^\flat) \otimes \mathbb{Z}/p^m(1)$, by the Artin-Schreier sequence ([period rings](/chapter/period-rings/)). So there is $y$ with
$$(\varphi - 1)y = B(w)(\mathrm{fst}(\varphi x' - w')) + B(x)(\mathrm{fst}(w' - x')).$$
For $n \in \mathbb{Z} \times \Gamma$ let
$$f(n) = B(nx)(n\,\mathrm{fst}\,x') - n\bigl(B(x)(\mathrm{fst}\,x') - y\bigr) - B(x)(\mathrm{fst}(nx' - x')) - y.$$

**Lemma (Step one).** Under the hypotheses of the theorem, $\varphi f(g) - f(g)$ is small for every $g \in \Gamma'$.

Lean: `New.Lift.Pairing.phi_smul_sub_mem_smallPart` (New/Congruences/Lifting/CupProductBound.lean).

*Proof.* The element $g$ commutes with $\varphi$. Insert the equation for $y$. By the two rules and bilinearity, $\varphi f(g) - f(g)$ equals
$$\begin{aligned} &B(gw - w)(\mathrm{fst}\,g(\varphi x' - w')) - B(\varphi x - w)(\mathrm{fst}(g\varphi x' - \varphi x')) \\ &\quad - B(w - x)(\mathrm{fst}(gw' - w')) + B(gx - x)(\mathrm{fst}\,g(w' - x')).\end{aligned}$$
The four terms are the four safe moves of the path, in this order: the second side from $\varphi x'$ to $w'$, the first side from $\varphi x$ to $w$, the first side from $w$ to $x$, and the second side from $w'$ to $x'$. Each term is small, and the small part is a submodule. $\square$

**Lemma (Step two).** Let $p^e = p^{e_1+e_2+e_3}r$. Assume hypothesis (1) of the theorem. Let $\kappa : \Gamma' \to \mathbb{Z}/p^m$ satisfy: $f(g) - 1 \otimes \kappa(g)$ is small for all $g \in \Gamma'$. Then for $g, h \in \Gamma'$,
$$p^e P(\alpha(c)(g), g\,\alpha'(c')(h)) = r\bigl(\chi(g)\kappa(h) - \kappa(gh) + \kappa(g)\bigr).$$

Lean: `New.Lift.Pairing.nsmul_modPairing_eq_coboundary` (New/Congruences/Lifting/CupProductBound.lean).

*Proof.* Expand by the cocycle rule for $\alpha(c)$ and $\alpha'(c')$ and the first rule:
$$1 \otimes p^{e_1+e_2+e_3}P(\alpha(c)(g), g\,\alpha'(c')(h)) = B(gx - x)(\mathrm{fst}\,g(hx' - x')) + \bigl(g f(h) - f(gh) + f(g)\bigr).$$
Let $\delta(g) = f(g) - 1 \otimes \kappa(g)$. Then $g\delta(h) - \delta(gh) + \delta(g)$ is small, as $\Gamma$ keeps the small part. The first term on the right is small by hypothesis (1). So $1 \otimes t$ is small for $t = p^{e_1+e_2+e_3}P(\ldots) - (\chi(g)\kappa(h) - \kappa(gh) + \kappa(g))$. A constant $1 \otimes t$ is small only if $t = 0$. Multiply by $r$. $\square$

*Proof of the theorem.* Fix a topology on $\Gamma$ for which $\Gamma \to G_p$ is an open embedding. By step one, $(\varphi - 1)f(g)$ is small. If $(\varphi - 1)d$ is small, then $d$ is a constant $1 \otimes t$ modulo the small part ([period rings](/chapter/period-rings/)). Choose such a $\kappa(g)$ for each $g \in \Gamma'$. By step two, $r\kappa$ satisfies the coboundary equation for $\alpha(c)$ and $p^e\alpha'(c')$. It remains to show that $r\kappa$ is $0$ near $1$. For $h$ near $1$, $\alpha(c)(h)$ and $\alpha'(c')(h)$ are multiples of $p^m$, and $p^m$ kills the values of $B(x)$. So
$$f(h) = (hy - y) - B(x)(h\,\mathrm{fst}\,x' - \mathrm{fst}\,x').$$
Both terms are small near $1$: the first by rule (3), the second because $h$ acts on $W(C^\flat) \otimes Y'$ through multiples of $p^m$ near $1$. So $1 \otimes \kappa(h)$ is small, and $\kappa(h) = 0$. The lemma from $\Gamma'$ to $\Gamma$ applies. $\square$

**Remark (Formalization).** The values $\kappa(g)$ are chosen by `choose`. Only the existence of the constant is used, and the proof does not depend on the choice. The exponent $e_3$ is the same in both hypotheses. In the source, a move of the second side is tested on the pair $(gx - x, gy')$, with $g$ applied to the moved part.

**Example (The model case).** Let $Y = Y' = \mathbb{Z}_p(1)$ and $C = C' = \mathbb{Z}_p$. Then $\langle\ ,\ \rangle$ is a product in $W(C^\flat)$ times $1 \otimes 1$, and a pair is safe when $p^e$ times the product of the two $Y$-components lies in $W(\mathfrak{m}^\flat)$. If $x'$ is fixed by $\Gamma'$, then every $hx' - x'$ is $0$, and hypothesis (1) holds because $0$ is small. The path condition then measures how far $\varphi x$ is from $x$. This is the role of the depth steps of [Section 4](/chapter/exponent-lattices/#invariance-and-the-depth-lemma).
