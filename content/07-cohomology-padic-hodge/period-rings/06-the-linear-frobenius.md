---
title: The linear Frobenius
lean:
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/PadicHodge/Crystalline/Regularity.lean
decls:
  - New.Period.IsWeilPair
  - New.Period.IsWeilPair.smul_eq_of_fixed_nearOne
  - New.Period.linearFrob
  - New.Period.linearFrob_apply
  - New.Period.IsKilledBy
  - New.Period.linearFrob_mul
  - New.Period.IsCrystalline.linearFrob_eq_one
  - New.Period.IsPotentiallyCrystalline.eventually_linearFrob_eq_one
  - New.Period.IsPotentiallyCrystalline.isCrystalline_of_inertia_fixes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The linear Frobenius

This section builds a $B_{\max}$-linear operator on $B_{\max} \otimes T$ that does the work of the Weil-Deligne representation of a potentially crystalline representation. It proves the algebraic properties of the operator, its behaviour on inertia, and a descent theorem: a potentially crystalline representation on which inertia acts trivially, in the sense of the operator, is crystalline. The notation is that of Section 5. The source cites J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé VIII, 2.3, and O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), Sections 9.1 to 9.3.

### Weil pairs

Classically, a potentially crystalline $V$ has a Weil-Deligne representation on $D_{\mathrm{pst}}(V)$, and the local condition of Volume 12 asks that the action of a Frobenius on it is killed by a given polynomial. The source does not build $D_{\mathrm{pst}}$ or the Weil-Deligne representation. It builds an operator on $B_{\max} \otimes T$ that plays the same role.

**Definition (Weil pair).** Let $s \in G_p$ and $m \geq 0$. The pair $(s, m)$ is a *Weil pair* if $s^{-1}$ is a Frobenius element for $p^m$ on the ring of integers of $\overline{\mathbb{Q}}_p$, that is, $s^{-1}(x) \equiv x^{p^m}$ modulo the maximal ideal for every integer $x$. So $s$ acts on the residue field $\overline{\mathbb{F}}_p$ as $x \mapsto x^{1/p^m}$.

Lean: `New.Period.IsWeilPair` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.isWeilPair_zero_iff`.

The pair $(s, 0)$ is a Weil pair exactly when $s$ is in the inertia group. The group `FrobGal` of Section 2 acts on $B_{\max}$, and the pair $(m, s)$ acts by $\varphi^m \circ s$. For a Weil pair, this map is trivial on the Witt vectors $W(\overline{\mathbb{F}}_p) \subset A_{\inf}$, since $s$ acts on them as $\varphi^{-m}$.

**Theorem.** Let $(j(s), m)$ be a Weil pair, and let $b \in B_{\max}$ be fixed by all $g$ near $1$. Then $\varphi^m(j(s)(b)) = b$.

Lean: `New.Period.IsWeilPair.smul_eq_of_fixed_nearOne` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* By fixed fractions with denominator $1$, $p^n b = w$ for a Witt vector $w$ over a finite field. The map $\varphi^m \circ j(s)$ sends $w$ to a Witt vector with the same reduction, and a Witt vector over $\mathbb{F}_{p^f}$ is determined by its reduction in this sense, so $w$ is fixed. Cancel $p^n$. $\square$

**Definition (The linear Frobenius).** For $s \in \Gamma$ and $m \geq 0$, $\beta_{s,m}$ is a $B_{\max}$-linear endomorphism of $B_{\max} \otimes T$ that agrees with $(\varphi^m \circ j(s)) \otimes \rho(s)$ on $D_{\mathrm{pcris}}(\rho)$, if such a map exists.

Lean: `New.Period.linearFrob` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.linearFrob_eq_tensorAction_of_exists`, `New.Period.IsPotentiallyCrystalline.linearFrob_eq`.

**Remark (Formalization).** `New.Period.linearFrob` is `Classical.epsilon` of the property "agrees with $(\varphi^m \circ j(s)) \otimes \rho(s)$ on $D_{\mathrm{pcris}}$". If no map has the property, the value is an unspecified endomorphism, a junk value. The register records this as F-051. If $\rho$ is potentially crystalline, $D_{\mathrm{pcris}}$ spans, so there is at most one such map, and the next theorem shows that there is one for a Weil pair. So for a potentially crystalline $\rho$ and a Weil pair, $\beta_{s,m}$ is well defined. Every theorem of the source on $\beta_{s,m}$ has both hypotheses. A statement of the form "$P(\beta_{s,m}) = 0$" for a pair that is not a Weil pair says nothing about $\rho$.

**Theorem (Existence).** Let $\rho$ be potentially crystalline and let $(j(s), m)$ be a Weil pair. Then for every $d \in D_{\mathrm{pcris}}(\rho)$,
$$\beta_{s,m}(d) = \bigl((\varphi^m \circ j(s)) \otimes \rho(s)\bigr)(d).$$

Lean: `New.Period.linearFrob_apply` (Lib/PadicHodge/Crystalline/Regularity.lean), `New.Period.linearFrob_zero_apply`.

*Proof.* Take a fixed basis $(v_i)$ of $B_{\max} \otimes T$ along $\mathrm{nearOne}$, by the theorem on fixed bases. Define $\beta$ on the basis by $\beta(v_i) = ((\varphi^m \circ j(s)) \otimes \rho(s))(v_i)$ and extend linearly. Let $y \in D_{\mathrm{pcris}}$, with $y = \sum_i y_i v_i$. Each coordinate $y_i$ is fixed by all $g$ near $1$, since $y$ and the $v_i$ are, and the $v_i$ are independent. By the previous theorem, $\varphi^m \circ j(s)$ fixes $y_i$. So the semilinear map $(\varphi^m \circ j(s)) \otimes \rho(s)$ sends $y$ to $\sum_i y_i\, \beta(v_i) = \beta(y)$. Then $\beta$ has the property that defines $\beta_{s,m}$, and the epsilon picks a map with the property. $\square$

The operator $\beta_{s,m}$ is the semilinear map $(\varphi^m \circ j(s)) \otimes \rho(s)$, made linear by the choice of a fixed basis. Classically, $D_{\mathrm{pst}}$ is a vector space over $\mathbb{Q}_p^{\mathrm{nr}}$ in which the Weil group acts semilinearly, and the Weil-Deligne representation is made linear by the twist by $\varphi$ (Fontaine, Astérisque 223, Exposé VIII, 2.3, and Brinon-Conrad, Section 9.3). The source does not prove that $\beta_{s,m}$ restricted to the span of $D_{\mathrm{pcris}}$ over $W(\overline{\mathbb{F}}_p)[1/p]$ is the classical operator. It uses $\beta_{s,m}$ through its algebraic properties.

**Theorem (Properties of the linear Frobenius).** Let $\rho$ be potentially crystalline and let $(j(s), m)$ and $(j(t), k)$ be Weil pairs.

1. $\beta_{st, m+k} = \beta_{s,m}\,\beta_{t,k}$, and $\beta_{s^n, nm} = \beta_{s,m}^n$ for $n \geq 0$.
2. $\beta_{s,m}$ commutes with the action of every $a \in R$ on $B_{\max} \otimes T$.
3. If $f : T \to T'$ is equivariant near $1$ and at $s$, and $\rho'$ is potentially crystalline, then $1 \otimes f$ intertwines $\beta_{s,m}$ for $\rho$ and for $\rho'$.
4. If $\sigma = \chi^{-d}\rho$ with $d \geq 0$, then $\beta^{\sigma}_{s,m} = p^{md}\beta^{\rho}_{s,m}$.

Lean: `New.Period.linearFrob_mul` (Lib/PadicHodge/Crystalline/Regularity.lean), `New.Period.linearFrob_pow`, `New.Period.commute_coeffEnd_linearFrob`, `New.Period.baseChange_linearFrob`, `New.Period.linearFrob_twist_cyclotomicGp`.

Each claim is proved by evaluation on $D_{\mathrm{pcris}}$, which spans, and the formula of the existence theorem. For the product, the source checks that $\rho(t)$ maps $D_{\mathrm{pcris}}$ to itself: if $d$ is fixed by $t^{-1} g t$ for $g$ near $1$, then $t d$ is fixed by $g$, and conjugation by $j(t)$ keeps elements near $1$. For the twist, it uses the unit $u = t^{-c}$ of the Tate twist theorem, on which $(\varphi^m, j(s))$ acts by $p^{-mc}\chi(s)^{-c}$.

**Definition (Killed by a polynomial).** Let $P \in R[X]$. The polynomial $P$ *kills* $(s, m)$ on $\rho$ if $\rho$ is potentially crystalline and $P(\beta_{s,m}) = 0$ on $B_{\max} \otimes T$, where the coefficients of $P$ act through $R \to \mathrm{End}_{B_{\max}}(B_{\max} \otimes T)$, $a \mapsto 1 \otimes a$.

Lean: `New.Period.IsKilledBy` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.coeffEnd`, `New.Period.isKilledBy_iff`.

**Remark (Formalization).** The definition asks for potential crystallinity, so the junk value of $\beta_{s,m}$ cannot occur for a potentially crystalline $\rho$ that fails the definition. It does not ask that $(j(s), m)$ is a Weil pair. For a pair that is not a Weil pair, $\beta_{s,m}$ may be the junk value, and the condition $P(\beta_{s,m}) = 0$ then has no meaning. The condition is tested on all of $B_{\max} \otimes T$, not on $D_{\mathrm{pcris}}$. For a potentially crystalline $\rho$ the two are equivalent, since $P(\beta_{s,m})$ is $B_{\max}$-linear and $D_{\mathrm{pcris}}$ spans.

**Theorem (Subobjects for killing).** Let $(j(s), m)$ be a Weil pair, $\mathrm{nearOne} \sqcup \{s\} \leq F$, and let $f_i : T' \to S_i$ be finitely many jointly injective maps, equivariant along $F$ and semilinear along $\phi : R' \to R$. If $P = \phi(Q)$ kills $(s, m)$ on every $S_i$, then $Q$ kills $(s, m)$ on $T'$.

Lean: `New.Period.IsKilledBy.of_jointly_injective` (Lib/PadicHodge/Crystalline/Regularity.lean).

### Inertia

**Theorem (Inertia on crystalline representations).** Let $s \in \Gamma$ with $j(s)$ in inertia.

1. If $\rho$ is crystalline, then $\beta_{s,0} = 1$.
2. If $T$ is finite and free over $R$ and $\rho$ is potentially crystalline, then $\beta_{g,0} = 1$ for all $g$ near $1$ with $j(g)$ in inertia.

Lean: `New.Period.IsCrystalline.linearFrob_eq_one` (Lib/PadicHodge/Crystalline/Regularity.lean), `New.Period.IsPotentiallyCrystalline.eventually_linearFrob_eq_one`.

*Proof.* For 1, an element $d$ of $D_{\mathrm{cris}}$ is fixed by all of $\Gamma$, so $\beta_{s,0}(d) = (j(s) \otimes \rho(s))(d) = d$, and $D_{\mathrm{cris}}$ spans. For 2, write $1 \otimes v_l$, for a basis $(v_l)$ of $T$, as finite combinations of elements of $D_{\mathrm{pcris}}$. There are finitely many such elements, and all $g$ near $1$ fix all of them. For such $g$ in inertia, $\beta_{g,0}$ fixes each of them, so it fixes each $1 \otimes v_l$. It commutes with $R$ and is $B_{\max}$-linear, so it is the identity. $\square$

Classically, the first claim is one direction of the statement that a potentially semistable representation is crystalline exactly when inertia acts trivially on its Weil-Deligne representation and the monodromy is zero. The second claim says that inertia acts on the Weil-Deligne representation through a finite quotient. The converse of the first claim is the descent theorem.

**Theorem (Descent).** Let $\rho$ be potentially crystalline. Suppose that $\beta_{s,0} = 1$ for every $s \in \Gamma$ with $j(s)$ in inertia. Then $\rho$ is crystalline.

Lean: `New.Period.IsPotentiallyCrystalline.isCrystalline_of_inertia_fixes` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* Let $y \in D_{\mathrm{pcris}}$. It is enough to show that $y$ is in the span of the elements fixed by all of $\Gamma$. There is an open subgroup $V$ of $G_p$ such that every element of $V \cap j(\Gamma)$ is $j(t)$ for some $t$ that fixes $y$. Let $I$ be the inertia group, which is normal in $G_p$, and let $U = IV$, an open subgroup. Every $g$ with $j(g) \in U$ fixes $y$: write $j(g) = i\,j(t)$ with $i \in I$ and $t$ fixing $y$; then $j(g t^{-1}) = i$ is in inertia, and the hypothesis gives that $g t^{-1}$ fixes $y$, by the existence theorem. So $y$ is fixed by the preimage of $U$. Let $L$ be the integral closure of $\mathbb{Q}_p$ in $B_{\max}$, a field. Galois descent from $U$ to $j(\Gamma)$ over $L$ writes $y$ as an $L$-combination of elements fixed by $\Gamma$, provided every element of $G_p$ that fixes $L^U$ lies in $U$. The source checks this with a Kummer chart for $U$. As $U$ contains inertia, the chart is unramified, and its constants $W(\mathbb{F}_{p^f})$ lie in $L^U$. Also $E = z + p$, so $\theta(z) = -p$, which every element fixes. An element of $G_p$ that fixes the constants and $\theta(z)$ lies in $U$, since the chart is a chart for $U$. $\square$

**Remark (Formalization).** The hypothesis is on all $s$ with $j(s)$ in inertia, and it is stated through $\beta_{s,0}$. Since $\rho$ is potentially crystalline and $(j(s), 0)$ is a Weil pair, $\beta_{s,0}$ is not a junk value here. The proof uses `New.Lift.exists_kummerChart` from the Kisin folder, as the theorem on fixed fractions does. The theorem does not have the hypothesis that $T$ is finite over $R$.
