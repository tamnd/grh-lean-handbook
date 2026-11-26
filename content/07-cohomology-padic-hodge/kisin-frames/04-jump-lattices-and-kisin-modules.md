---
title: Jump lattices and Kisin modules
lean:
  - Lib/PadicHodge/Kisin/KummerChartDeRham.lean
  - Lib/PadicHodge/Kisin/Modules.lean
decls:
  - New.Lift.KummerChart.exists_derivative_dvd_p_pow
  - New.Lift.KummerChart.valueField
  - New.Lift.KummerChart.phiInvToBdR_mem_hodgeFil_one_iff
  - New.Lift.KummerChart.Coeffs
  - New.Lift.KummerChart.JumpLattice
  - New.Lift.KummerChart.JumpLattice.forms
  - New.Lift.KummerChart.JumpLattice.crysForms
  - New.Lift.KummerChart.JumpLattice.kisinAinf
  - New.Lift.KummerChart.JumpLattice.kisinModule
  - New.Lift.KummerChart.JumpLattice.jumpBound
  - New.Lift.KummerChart.JumpLattice.Hom.wittMap_mem_kisinModule
  - New.Lift.KummerChart.JumpLattice.exists_span_formsOfType_mod_pred
  - New.Lift.KummerChart.JumpLattice.formsOfType_subset_pred_of_notMem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Jump lattices and Kisin modules

The frame of the previous section is a set of matrices. It depends on a basis and on choices. This section defines the modules that the frame describes. They are cut out by conditions on linear forms with values in $B_{\mathrm{dR}}$, so they do not depend on a basis. The objects are a *jump lattice* $L$, the $A_{\inf}$-module $M$ (`kisinAinf`) and the $S$-module $N$ (`kisinModule`).

Throughout, $\Gamma$ is a group over $G_p$ and $k$ is a Kummer chart for $\Gamma$, with subgroup $\Gamma'$, ring $S$, element $E$ and exponent $e$. The source acts on $A_{\inf}$ by the group $\mathbb{Z} \times \Gamma$ (`New.Lift.FrobGroup`): the generator of $\mathbb{Z}$ acts by $\varphi$ and $g \in \Gamma$ acts through $j(g)$.

### Values in $B_{\mathrm{dR}}$

For $a \geq 0$, the map $r \mapsto \varphi^{-a}(r)$ followed by $A_{\inf} \to B_{\mathrm{dR}}^+$ is a ring map $A_{\inf} \to B_{\mathrm{dR}}$ (`New.Lift.phiInvToBdR`). Its link with the chart is the next lemma. Write $\mathrm{Fil}^n = t^n B_{\mathrm{dR}}^+$ (`New.Period.hodgeFil`).

**Lemma.** For $r \in A_{\inf}$ and $a \geq 0$, the image of $\varphi^{-a}(r)$ in $B_{\mathrm{dR}}$ is in $\mathrm{Fil}^1$ if and only if $\varphi^a(E)$ divides $r$ in $A_{\inf}$.

Lean: `New.Lift.KummerChart.phiInvToBdR_mem_hodgeFil_one_iff` (Lib/PadicHodge/Kisin/KummerChartDeRham.lean).

*Proof.* An element of $A_{\inf}$ maps into $\mathrm{Fil}^1$ if and only if it is in $\ker\theta$. So the condition is $\theta(\varphi^{-a}(r)) = 0$. By `New.Lift.frobE_dvd_iff` this holds if and only if $\varphi^a(E) \mid r$. $\square$

The values of the forms below lie in a subfield of $B_{\mathrm{dR}}$.

**Definition (The value field).** For $a \geq 0$, the field $\mathcal{K}_a$ is the subfield of $B_{\mathrm{dR}}$ generated over the field fixed by $\Gamma'$ by the products $b \cdot \varphi^{-a}(s)$, with $b \in S_B$ and $s \in S$.

Lean: `New.Lift.KummerChart.valueField` (Lib/PadicHodge/Kisin/KummerChartDeRham.lean).

Classically, the field of $\mathfrak{S}$ inside $B_{\mathrm{dR}}$ via $u \mapsto \pi$ is $K$ itself, after completion along $E$. The field $\mathcal{K}_0$ is a version of this that also contains $S_B$.

The next lemma bounds the different of the chart by a power of $p$.

**Lemma (A bound for the different).** There is a polynomial $P \in \Lambda[X]$ with $E \mid P(z)$ in $S$ such that $\theta(P'(z))$ divides $p^d$ in $\mathcal{O}_C$, where $d$ is the different bound of the chart.

Lean: `New.Lift.KummerChart.exists_derivative_dvd_p_pow` (Lib/PadicHodge/Kisin/KummerChartDeRham.lean).

*Proof.* Take $P = X^e - R$, where $R$ is the remainder of $z^e$ under Weierstrass division by $E$. If $\theta(P'(z))$ did not divide $p^{v_p(e)+1}$, then this power of $p$ would divide $P'$. But the top coefficient of $P'$ is $e$. If $e = 1$, then $P' = 1$ and $d = 0$. $\square$

### Coefficients and letters

The lattices of the source have coefficients in a finite $\mathbb{Z}_p$-algebra $\mathcal{O}$. To split them by embeddings, the source uses the Teichmüller lifts of $\mathbb{F}_q^\times$, $q = p^f$.

**Definition (Coefficients and letters).** The *letters* of the chart are the elements of $\mathbb{F}_q^\times$ (`New.Lift.KummerChart.Letter`). Each letter $i$ has its Teichmüller lift $\omega(i)$ in $\Lambda \subset S$ (`New.Lift.KummerChart.letterTeich`). A *ring of coefficients* is a $\mathbb{Z}_p$-algebra $\mathcal{O}$ that is finite and free, with an element $\zeta \in \mathcal{O}$ such that $\zeta^{q-1} = 1$.

Lean: `New.Lift.KummerChart.Coeffs` (Lib/PadicHodge/Kisin/Modules.lean).

The number of letters is $q - 1$. It is prime to $p$, so it is invertible in $\mathbb{Z}_p$. For a letter $i$, let $\lambda_i$ be multiplication by $\omega(i)^{-1}\zeta$ on $W(C^\flat) \otimes L$ (`letterOp`). The operator $\frac{1}{q-1}\sum_{n<q-1}\lambda_i^n$ (`letterProj`) is the projection onto the part where $\zeta$ acts as $\omega(i)$ (`letterPart`). These parts split $W(C^\flat) \otimes L$ by the value of $\zeta$, and so by the embeddings of $\mathcal{O}$ above each letter.

**Definition (Jump lattice).** A *jump lattice* over the Kummer chart $k$ with coefficients $\mathcal{O}$ is a finite free $\mathcal{O}$-module $L$ with an $\mathcal{O}$-linear action $\rho$ of $\Gamma$, with these data.

1. For each letter $i$, a finite set $J_i$ of integers.
2. For each embedding $\gamma : \mathcal{O} \to \mathbb{C}_p$, a finite set $J_\gamma$ of integers.
3. The restriction of $L$ to $\Gamma'$ is crystalline, and its jumps at $\gamma$ lie in $J_\gamma$.
4. If $\gamma(\zeta) = \theta(\omega(i))$, then $J_\gamma \subseteq J_i$.

Lean: `New.Lift.KummerChart.JumpLattice` (Lib/PadicHodge/Kisin/Modules.lean).

The ambient module is $W(C^\flat) \otimes L$ (`Ambient`), where $W(C^\flat)$ is `New.Period.WittCFlat`, with the diagonal action of $\mathbb{Z} \times \Gamma$. The module $A_{\inf} \otimes L$ is the $A_{\inf}$-span of the vectors $1 \otimes y$ (`ainfLattice`).

**Definition (Jump bound).** The *jump bound* of $L$ is the least $a \in \mathbb{N}$ such that every Hodge-Tate jump of $L$, as a $\mathbb{Z}_p$-representation of $\Gamma'$, lies in $[-a, a]$. It is $0$ if there is no such $a$.

Lean: `New.Lift.KummerChart.JumpLattice.jumpBound` (Lib/PadicHodge/Kisin/Modules.lean).

**Remark (Formalization).** The jump bound is defined by `sInf` on a set of natural numbers. If the set were empty, `sInf` would give the junk value $0$. For a jump lattice the set is not empty. The source proves this (`New.Period.exists_jump_bound`) and uses `Nat.sInf_mem` when it builds the frame. So in the frame theorem the junk value does not occur, and $a$ is a true bound for the jumps. The bound is symmetric: it bounds the jumps from both sides by the same $a$. A lattice with jumps in $[0, h]$ has jump bound at most $h$.

### Forms

**Definition (Forms).** A *form* on $L$ is an $A_{\inf}$-linear map $\mu : W(C^\flat) \otimes L \to B_{\mathrm{dR}}$ with $\mu(1 \otimes gt) = g \cdot \mu(1 \otimes t)$ for every $g \in \Gamma'$ and $t \in L$. A form is *crystalline* if there is a $\mathbb{Z}_p$-linear map $l : L \to B_{\max}$ with $\mu(1 \otimes t) = l(t)$ in $B_{\mathrm{dR}}$ for all $t$.

Lean: `New.Lift.KummerChart.JumpLattice.forms`, `New.Lift.KummerChart.JumpLattice.crysForms` (Lib/PadicHodge/Kisin/Modules.lean).

A form is determined by its values on the vectors $1 \otimes t$, and these values form a $\Gamma'$-equivariant map $L \to B_{\mathrm{dR}}$. So forms are de Rham periods of $L$. A crystalline form has periods in $B_{\max}$.

### The modules $M$ and $N$

Let $\mathrm{Sat}_\tau(P)$ be the set of $x$ with $\tau^n x \in P$ for some $n$ (`New.Lift.saturateBy`).

**Definition (The modules $M$ and $N$).** The $A_{\inf}$-module $M$ of $L$ is the set of $x \in \mathrm{Sat}_\tau(A_{\inf} \otimes L)$ such that $\mu(\varphi^{n+1} x) \in B_{\mathrm{dR}}^+$ for every $n \geq 0$ and every form $\mu$. The Kisin module $N$ of $L$ is the set of $x \in M$ such that $\mu(x) \in \mathcal{K}_0$ for every form $\mu$. It is an $S$-module.

Lean: `New.Lift.KummerChart.JumpLattice.kisinAinf`, `New.Lift.KummerChart.JumpLattice.kisinModule` (Lib/PadicHodge/Kisin/Modules.lean).

The condition on $M$ is a condition on all the Frobenius iterates $\varphi^{n+1}x$. The source states the condition with $B_{\mathrm{dR}}^+$, which is the completion of $A_{\inf}[1/p]$ at $\ker\theta$. The condition for $N$ says that the values of forms lie in the field generated by $S$ and $S_B$. So $N$ is the part of $M$ that is defined over the chart.

The source also defines $\varphi^l(M)$ (`frobKisinAinf`), the localization of $M$ at the elements $\varphi^a(E)$ (`kisinLocAinf`), and the $S$-module of the $x$ in an $A_{\inf}$-module $P$ with all form values in $\mathcal{K}_0$ (`valueFieldPoints`). So $N$ is `valueFieldPoints` of $M$.

**Lemma (Functoriality).** Let $F : L \to L'$ be an $\mathcal{O}$-linear map of jump lattices that commutes with $\Gamma$. Then $1 \otimes F$ maps the Kisin module of $L$ into the Kisin module of $L'$.

Lean: `New.Lift.KummerChart.JumpLattice.Hom.wittMap_mem_kisinModule` (Lib/PadicHodge/Kisin/Modules.lean).

*Proof.* The map $1 \otimes F$ commutes with $\varphi$ and keeps $A_{\inf} \otimes L$. For a form $\mu$ on $L'$, the composite $\mu \circ (1 \otimes F)$ is a form on $L$. So each condition on $x$ gives the condition on $(1 \otimes F)(x)$. $\square$

### Forms of a type

The forms are filtered by their order along the Hodge filtration at each letter. For a letter $i$ and an integer $u$, a form $\mu$ is *of type $u$ at $i$* if $\mu(\mathrm{proj}_i(1 \otimes t)) \in \mathrm{Fil}^{-u}$ for every $t$ (`formsOfType`). A form of type $u - 1$ is of type $u$. The *multiplicity* of $u$ at $i$ is the sum of the multiplicities of the jump $u$ over the embeddings $\gamma$ of $\mathcal{O}$ with $\gamma(\zeta) = \theta(\omega(i))$ (`jumpMultiplicity`).

**Proposition.** Let $i$ be a letter and $u$ an integer. There are $r$ forms $\nu_1, \ldots, \nu_r$ of type $u$ at $i$, with $r$ at most the multiplicity of $u$ at $i$, such that for every form $\mu$ of type $u$ at $i$ there are $c_1, \ldots, c_r \in \bar{\mathbb{Q}}_p$ with $\mu - \sum c_m \nu_m$ of type $u - 1$ at $i$.

Lean: `New.Lift.KummerChart.JumpLattice.exists_span_formsOfType_mod_pred` (Lib/PadicHodge/Kisin/Modules.lean).

*Proof.* The source outlines the proof as follows. The leading coefficient of $\mu$ at the letter $i$ is a map $L \to \mathbb{C}_p$, the *symbol* of $\mu$. The symbols are Hodge-Tate maps of weight $u$. The rank formula for the Hodge-Tate parts of a potentially crystalline lattice bounds the dimension of their span by the multiplicity. In a basis of symbols, the coordinates of a symbol are Galois invariant. By Ax's theorem they are in the closure of $\bar{\mathbb{Q}}_p$, and the source shows they are algebraic. $\square$

**Corollary.** If $u \notin J_i$, then every form of type $u$ at $i$ is of type $u - 1$ at $i$.

Lean: `New.Lift.KummerChart.JumpLattice.formsOfType_subset_pred_of_notMem` (Lib/PadicHodge/Kisin/Modules.lean).

*Proof.* If $u \notin J_i$, then $u$ is not a jump at any embedding above $i$, by property 4 of a jump lattice. So the multiplicity is $0$, and $r = 0$ in the proposition. $\square$

The corollary is a statement on Hodge-Tate weights of the Kisin module, per letter. The docstring of the file compares it with statements on Wach modules (Wach, Bull. SMF 124 (1996), 375-400) and with Berger, Limites de représentations cristallines, Compositio Math. 140 (2004), 1473-1498, section III. It also says what the file does not prove. It proves only bounds on the weights, not that the Galois action is trivial modulo the variable. The bounds hold per unramified embedding of the coefficients, and they are upper bounds by the multiplicity of each jump.

**Example (The trivial lattice).** Let $\mathcal{O} = \mathbb{Z}_p$, $\zeta = 1$ and $L = \mathbb{Z}_p$ with the trivial action. Take $J_\gamma = J_i = \{0\}$. The only jump is $0$, so the jump bound is $0$. A form is given by one value $\mu(1 \otimes 1) \in B_{\mathrm{dR}}^{\Gamma'}$. For $x = r \otimes 1$ with $r \in A_{\inf}$, the condition for $M$ asks that $\varphi^{n+1}(r)\,\mu(1 \otimes 1) \in B_{\mathrm{dR}}^+$ for all forms. The frame theorem of the next section gives $M = A_{\inf} \otimes L$ in this case, since $\tau^0 = 1$. Then $N$ is the set of $r \otimes 1$ in $M$ whose form values lie in $\mathcal{K}_0$, and the frame theorem gives that $N$ is free of rank one over $S$.
