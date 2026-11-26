---
title: Lift laws modulo N
lean:
  - New/UpperBound/Objects/LiftLawsModuloN.lean
decls:
  - New.IsSplitLevel
  - New.IsSplitLevel.upOperator
  - New.IsSplitLevel.mirabolic
  - New.IsSplitLevel.ramified
  - New.IsSplitLevel.lastColDatum
  - New.IsSplitLevel.charDatum
  - New.IsSplitLevel.directDatum
  - New.IsSplitLevel.mirrorDatum
  - New.IsSplitLevel.gluedDatum_eq_sum
  - New.IsSplitLevel.primitiveVectors
  - New.IsSplitLevel.LiftLaw
  - New.IsSplitLevel.mirabolic_fix_upOperator
  - New.IsSplitLevel.upOperator_mem_ramified
  - New.IsSplitLevel.LiftLaw.mirror_eq_upOperator_direct
  - New.IsSplitLevel.LiftLaw.mirror_eq_direct_upOperator
  - New.IsSplitLevel.LiftLaw.upOperator_direct
  - New.IsSplitLevel.LiftLaw.sum_charDatum_lastColDatum
  - New.IsSplitLevel.LiftLaw.glued_eq_direct_direct_upOperator
  - New.IsSplitLevel.upOperator_compUpTo_direct
  - New.IsSplitLevel.gluedLift
  - New.IsSplitLevel.compUpTo_gluedLift_eq_smul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lift laws modulo N

The composite lift takes its $m$ lifts in pairs, and each pair is glued at the level $N$ by a datum that mixes the two lifts. The size estimate and the divisibility argument want something simpler: a chain of single lifts, each with the plainest datum. This section proves that the glued chain is a scalar times the plain chain after a power of one operator $\mathrm{Up}$. The proof uses only how a lift depends on its datum, so it is stated for an abstract chain of representations.

### Model case: rank one

Let $P$ be one place $w$ with residue field $\mathbb{Z}/N$, and let the group be $\mathrm{GL}_1(E_w) = E_w^\times$. Let $\pi$ be a character $\chi$ of $E_w^\times$ that is trivial on the units $\equiv 1 \bmod N$ but not on all units. Then the operator of this section is
$$\mathrm{Up} = \chi(N)^{-1} \sum_{y \in (\mathbb{Z}/N)^\times} \psi_N(y)\, \chi(\tilde y),$$
with $\tilde y$ a unit lift of $y$ and $\psi_N(y) = \psi(-y/N)$ for the fixed additive character $\psi$. So $\mathrm{Up}$ is a Gauss sum times a scalar. A vector is *ramified* if it lies in the range of $1 - \pi(x)$ for some unit $x$; here this holds as $\chi(x) \neq 1$ for some unit $x$. The theorems below say that, on such vectors, every glued datum can be traded for a plain datum and a factor of this kind.

### The setting

**Definition (Split level).** A finite set $P$ of finite places of $E$ is a *split level* for the prime $N$ if the conjugate of a place in $P$ is not in $P$, each residue field at $w \in P$ has $N$ elements, $N$ is a uniformiser at each $w \in P$, and the places above $N$ are exactly those in $P$ and their conjugates.

Lean: `New.IsSplitLevel` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Fix such $P$ and $N$. Write $E_P = \prod_{w \in P} E_w$, $\mathcal{O}_P$ for its integers, and $\bar{\cdot}$ for the reduction $\mathcal{O}_P \to (\mathbb{Z}/N)^P$. Index sets have the form $n \sqcup \{\ast\}$, with a last basis vector $e_\ast$. Let $D = \mathrm{diag}(1, \dots, 1, N)^{-1}$ in $\mathrm{GL}_{n \sqcup \ast}(E_P)$ (`New.IsSplitLevel.diagNInv`). It takes the standard lattice $L$ to $L^+ = L + \mathcal{O} e_\ast/N$. For $y \in (\mathbb{Z}/N)^P$, put $\psi_N(y) = \psi(-y/N)$ (`New.IsSplitLevel.psiN`). Let $\pi$ be a representation of $\mathrm{GL}_{n \sqcup \ast}(E_P)$ on a complex space.

**Definition ($\mathrm{Up}$, the mirabolic group, ramified vectors).**

1. $\mathrm{Up} = \pi(D) \sum_y \psi_N(y_\ast)\, \pi(g_y)$, where $y$ runs over the vectors modulo $N$ whose last entry $y_\ast$ is a unit, and $g_y$ is a fixed integral invertible matrix whose last column and last row are both $y$ modulo $N$ (`New.IsSplitLevel.lastRowColGL`).
2. The mirabolic group is the group of integral invertible matrices $g$ with $\bar g\, e_\ast = e_\ast$.
3. A vector $\varphi$ is ramified if for each $w \in P$ there is a unit $x \in \mathcal{O}_P^\times$, $\equiv 1 \bmod N$ at the places of $P$ other than $w$, with $\varphi$ in the range of $1 - \pi(x \cdot 1)$.

Lean: `New.IsSplitLevel.upOperator` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.mirabolic` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.ramified` (New/UpperBound/Objects/LiftLawsModuloN.lean).

**Lemma.** If $\varphi$ is fixed by the mirabolic group, so is $\mathrm{Up}\,\varphi$. The operator $\mathrm{Up}$ commutes with the integral unit scalars, so it maps ramified vectors to ramified vectors.

Lean: `New.IsSplitLevel.mirabolic_fix_upOperator` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.upOperator_mem_ramified` (New/UpperBound/Objects/LiftLawsModuloN.lean).

*Proof.* For $g$ mirabolic, $k = D^{-1} g D$ is integral with last row $e_\ast$ modulo $N$, so $\bar k y$ has the same last entry as $y$. The matrices $k g_y$ and $g_{\bar k y}$ both have last column $\bar k y$ modulo $N$, so $(D g_{\bar k y})^{-1} g\, (D g_y)$ is mirabolic and fixes $\varphi$. Thus $g$ sends the term for $y$ to the term for $\bar k y$, and it permutes the terms of the sum. A scalar commutes with $D$ and with every $g_y$. $\square$

### Data and lift laws

A lift from $\pi$ on $\mathrm{GL}_{n \sqcup \ast}$ to $\pi'$ on $\mathrm{GL}_{n' \sqcup \ast}$ depends linearly on a datum, a function on matrices $(n' \sqcup \ast) \times (n \sqcup \ast)$ over $E_P$. The data used here are functions of the reduction of an integral matrix, extended by $0$ (`New.IsSplitLevel.liftFn`).

**Definition (The data).** For integral matrices $T$:

1. the last column datum for $y$ is $1[\bar T e_\ast = y]$, the indicator of last column $y$ modulo $N$;
2. the character datum for $y$ is $\psi_N(\bar T_\ast \cdot y)$, with $\bar T_\ast$ the last row of $\bar T$;
3. the *direct datum* is the last column datum for $e_\ast$, and the *mirror datum* is the character datum for $e_\ast$;
4. a vector modulo $N$ is *primitive* if at every place of $P$ some entry is a unit.

The glued datum $\psi_N((RT)_{\ast\ast})$ of a pair of integral matrices is the sum over $y$ of the last column datum for $y$ at $T$ times the character datum for $y$ at $R$.

Lean: `New.IsSplitLevel.lastColDatum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.charDatum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.directDatum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.mirrorDatum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.gluedDatum_eq_sum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.primitiveVectors` (New/UpperBound/Objects/LiftLawsModuloN.lean).

In terms of marked lattices $(L, \varepsilon)$ and $(L', \varepsilon')$, the direct datum is $1[SL \subseteq L',\ S\varepsilon = \varepsilon']$ and the mirror datum is $1[SL \subseteq L'^+]\,\psi_N(u'(S\varepsilon))$, with $u'$ the last coordinate on $L'^+$.

**Definition (Lift law).** A lift $L$, linear in its datum, obeys the lift law with factor $\gamma \in \mathbb{C}$ if:

1. for integral invertible $a$, $b$, every function $f$ of matrices modulo $N$ and every $\varphi$, $\pi'(b)\, L_{f(\bar b\, \cdot\, \bar a)}(\pi(a)\varphi) = L_f(\varphi)$;
2. for every $\varphi$, $\pi'(D)\, L_{\mathrm{lastRow}}(\varphi) = \gamma \cdot L_{\mathrm{direct}}(\pi(D)\varphi)$, where $\mathrm{lastRow}$ is the indicator of last row $e_\ast$ modulo $N$.

Lean: `New.IsSplitLevel.LiftLaw` (New/UpperBound/Objects/LiftLawsModuloN.lean).

The first law says that integral matrices move freely between the datum and the two representations. The second says that a change of the lattices on both sides costs one fixed factor. The chapter [divisibility prime by prime](/chapter/divisibility/) proves that the lifts of the chain at the level $N$ obey both laws (`New.Data.liftLaw_liftAtN`).

### Mirror, direct and glued lifts

**Theorem (Mirror through direct).** Let $L$ obey the lift law with factor $\gamma$, and let $\varphi$ be ramified. Then
$$\pi'(D)\, L_{\mathrm{mirror}}\varphi = \mathrm{Up}\,(L_{\mathrm{direct}}\varphi) = \gamma \cdot L_{\mathrm{direct}}(\mathrm{Up}\,\varphi).$$

Lean: `New.IsSplitLevel.LiftLaw.mirror_eq_upOperator_direct` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.LiftLaw.mirror_eq_direct_upOperator` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.LiftLaw.upOperator_direct` (New/UpperBound/Objects/LiftLawsModuloN.lean).

*Idea of the proof.* The mirror datum is $\psi_N$ of the corner entry. First, on ramified $\varphi$, the terms with a nonunit corner entry give $0$ (`New.IsSplitLevel.LiftLaw.mirrorDatum_eq_unitCorner`). The reason is that such a term is invariant under the scalar $x$ of the definition of ramified, by the first law, so it kills $\varphi - x\varphi$. Then sort the remaining datum by the last column $y$ of $\bar T$. By the first law, the term for $y$ is $\pi'(g_y)$ applied to the direct lift, with the weight $\psi_N(y_\ast)$; after $\pi'(D)$ this is the definition of $\mathrm{Up}$ on the target side. For the second equality, sort instead by the last row and use the second law to move $D$ to the source. The third equality combines the two. $\square$

**Theorem (Glued lifts).** Let $L$ and $L'$ obey the lift law with factors $\gamma$ and $\gamma'$, from $\pi$ to $\pi'$ and from $\pi'$ to $\pi''$, and let $\varphi$ be ramified. Then
$$\sum_y L'_{\mathrm{char}(y)}\big(L_{\mathrm{col}(y)}\varphi\big) = \#\mathrm{Prim} \cdot L'_{\mathrm{mirror}}(L_{\mathrm{direct}}\varphi),$$
where $\mathrm{Prim}$ is the set of primitive vectors on $n' \sqcup \ast$, and
$$\pi''(D) \sum_y L'_{\mathrm{char}(y)}\big(L_{\mathrm{col}(y)}\varphi\big) = \#\mathrm{Prim}\, \gamma'\gamma \cdot L'_{\mathrm{direct}}\big(L_{\mathrm{direct}}(\mathrm{Up}\,\varphi)\big).$$

Lean: `New.IsSplitLevel.LiftLaw.sum_charDatum_lastColDatum` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.LiftLaw.glued_eq_direct_direct_upOperator` (New/UpperBound/Objects/LiftLawsModuloN.lean).

*Proof.* A term whose $y$ vanishes at some place of $P$ is $0$ on ramified vectors, by the scalar argument above. For a primitive $y$, choose an integral invertible $k$ with $\bar k e_\ast = y$. By the first law, applied to both lifts, the term for $y$ equals the term for $e_\ast$. This gives the first identity. For the second, apply the theorem on mirror through direct to $L'$ at $L_{\mathrm{direct}}\varphi$, which is ramified as the first law makes $L_{\mathrm{direct}}$ commute with unit scalars. Then move $\mathrm{Up}$ through $L$ by the third equality. $\square$

### Chains

Let $\pi_0, \pi_1, \dots$ be representations of $\mathrm{GL}_{X_j \sqcup \ast}(E_P)$, and let $L^{(j)}$ be lifts from $\pi_j$ to $\pi_{j+1}$ that obey the lift law with factors $\gamma_j$. For constants $d_i$, the $i$-th glued double lift is
$$G_i = d_i \cdot \pi_{2i+2}(D) \circ \sum_y L^{(2i+1)}_{\mathrm{char}(y)} \circ L^{(2i)}_{\mathrm{col}(y)}.$$

Lean: `New.IsSplitLevel.gluedLift` (New/UpperBound/Objects/LiftLawsModuloN.lean).

**Theorem (All lifts become direct).** On ramified $\varphi \in \pi_0$:

1. $\mathrm{Up}$ moves through the composite of the first $j$ direct lifts at the cost $\prod_{l < j} \gamma_l$;
2. the composite of the first $p$ glued double lifts is
$$G_{p-1} \circ \dots \circ G_0\, (\varphi) = \Big(\prod_{i<p} d_i \cdot \#\mathrm{Prim}(X_{2i+1} \sqcup \ast) \cdot \prod_{l < 2i+2} \gamma_l\Big)\, L^{(2p-1)}_{\mathrm{direct}} \circ \dots \circ L^{(0)}_{\mathrm{direct}}\,(\mathrm{Up}^p \varphi).$$

Lean: `New.IsSplitLevel.upOperator_compUpTo_direct` (New/UpperBound/Objects/LiftLawsModuloN.lean).

Lean: `New.IsSplitLevel.compUpTo_gluedLift_eq_smul` (New/UpperBound/Objects/LiftLawsModuloN.lean).

*Proof.* Part 1 is induction on $j$ with the third equality of the theorem on mirror through direct; each direct lift keeps ramified vectors ramified (`New.IsSplitLevel.compUpTo_direct_mem_ramified`). For part 2, induct on $p$. The glued double lift $G_p$ acts on the output of the first $2p$ direct lifts at $\mathrm{Up}^p\varphi$, which is ramified. The theorem on glued lifts turns $G_p$ into the scalar $d_p\,\#\mathrm{Prim}\,\gamma_{2p+1}\gamma_{2p}$ times two direct lifts after $\mathrm{Up}$. Part 1 moves this $\mathrm{Up}$ back through the first $2p$ direct lifts, at the cost $\prod_{l<2p}\gamma_l$. $\square$

**Remark (Formalization).** The matrices $g_y$ come from `New.IsSplitLevel.lastRowColGL`, which applies `Exists.choose` and a chosen lift from $\mathbb{Z}/N$ to $\mathcal{O}_P$. The results of this section hold for this choice. The constants $\gamma_j$ and $d_i$ are arbitrary complex numbers, and nothing here asks them to be nonzero. If one is $0$, the theorem is true and says that the glued chain vanishes on ramified vectors. The theorem is about ramified vectors only. The source forms that are ramified at the level $N$ are defined in [short columns and the gain](/chapter/short-columns-gain/); Section 8 states that definition.
