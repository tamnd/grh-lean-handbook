---
title: Tied traces
lean:
  - New/Congruences/FirstOrder/TiedTraces.lean
decls:
  - New.Patching.TaylorWilesPlaces.LocalChoice
  - New.Patching.TaylorWilesPlaces.nonempty_localChoice
  - New.Patching.TaylorWilesPlaces.LocalChoice.indLine
  - New.Patching.TaylorWilesPlaces.LocalChoice.indDet
  - New.Patching.TaylorWilesPlaces.LocalChoice.diamond
  - New.Patching.TaylorWilesPlaces.LocalChoice.transfer_indLine
  - New.Patching.TaylorWilesPlaces.LocalChoice.indDet_diamond
  - New.Patching.BaseLevel.placeRep
  - New.Patching.BaseLevel.lineRep
  - New.Patching.BaseLevel.commute_heckeAction_residueRep
  - New.Patching.BaseLevel.localFormRep_apply_eq_lineRep
  - New.Patching.BaseLevel.mem_levelSpace_proIwahori
  - New.Patching.BaseLevel.mem_parahoricEigenspace_line
  - New.Patching.BaseLevel.mem_parahoricEigenspace_det
  - New.Patching.BaseLevel.heckeEigenvalues_mem_heckeAlgebra
  - New.Patching.BaseLevel.IsGalRepTwist
  - New.Patching.BaseLevel.charpoly_coeff_mem_heckeAlgebra
  - New.Patching.BaseLevel.IsCongruent
  - New.Patching.BaseLevel.exists_indicator_isCongruent
  - New.Patching.BaseLevel.traceElement
  - New.Patching.BaseLevel.tameTrace
  - New.Patching.BaseLevel.tameTrace_one
  - New.Patching.BaseLevel.tiedIdeal
  - New.Patching.BaseLevel.weightedSum_mul_heckeAction_eq_of_eigen
  - New.Patching.BaseLevel.tameTrace_smul_eq_diamond_sub_one
  - New.Patching.BaseLevel.aevalHecke
  - New.Patching.BaseLevel.tameTrace_smul_eq_aevalHecke
  - New.Patching.BaseLevel.weightedSum_indDet_mul_tameTrace
  - New.Patching.BaseLevel.norm_mul_traceElement_tameGenerator_eq_zero
  - New.Patching.BaseLevel.weightedSum_indLine_mem_levelSpace
  - New.Patching.BaseLevel.exists_aevalHecke_weightedSum
  - New.Patching.BaseLevel.map_aevalHecke_valMinAbs_mul_tameTrace
  - New.Patching.BaseLevel.lineRep_mul_eq_self
  - New.Patching.BaseLevel.heckeAction_mul_norm_mul_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tied traces

This section connects the Galois side to the automorphic side at one auxiliary place $w$, in three parts. First, traces of the Galois representations attached to the systems of eigenvalues are elements of the Hecke algebra, and so is the indicator function of a congruence class. Second, these traces define the *tied ideal*, the ideal of the tie relations. Third, at $w$ the tame generator $\gamma$ acts as a diamond operator and the Frobenius element $\varphi$ acts as a Hecke operator $U$, on the right eigenvectors. The algebra of [the last section](/chapter/tied-traces/#norms-at-one-prime) then turns these statements on eigenvectors into identities of operators, modulo $\ell^\nu/(2n!)$.

### The setting

The file works with base data $D$ for a hermitian space $V$ of dimension $n$ and a weight $\kappa$. Forms have principal level at the auxiliary places $w_j$ of a family $Q$ of Taylor-Wiles places, and maximal level at the other places off the level of $D$. No two places of $Q$ are equal or conjugate, and $\ell^\nu \mid q_j - 1$, where $q_j = \#\mathbb{F}_{w_j}$. Each $w_j$ has a Frobenius element $\varphi_j$ and a tame generator $\gamma_j$. These objects come from [Building the representations](/chapter/building-representations/), which also defines the following.

- A *system* $x$ of level $L$ is an isotypic space of forms that contains a nonzero form of level $L$. It has a Galois representation $\rho_x$ (`x.galRep`).
- The *Hecke algebra* $\mathbb{T}$ is the ring of $\ell$-adic functions $t$ on the systems such that the operator $\mathrm{heckeAction}(t)$, which scales each system $x$ by $t(x)$, keeps the integral forms.
- The group $\prod_j \mathrm{GL}_n(\mathbb{F}_{w_j})$ acts on forms of principal level through the residues (`residueRep`). The integral operators made of translations at $w_j$ form the ring of *local operators* at $w_j$, and these commute with $\mathbb{T}$.

Let $a \colon G \to \mathbb{Z}_\ell^\times$ be a character. The family $N$ is a *twist* of the Galois representations by $a$ if $N_x(g) = a(g)\,\rho_x(g)$ for all $x$ and $g$.

Lean: `New.Patching.BaseLevel.IsGalRepTwist` (New/Congruences/FirstOrder/TiedTraces.lean).

In all results at one place, $a(\gamma_j) = 1$ for all $j$. The twist is needed because [the operator at one place](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm) uses $N_x = a \otimes \rho_x$.

### Local choices

**Definition (Local choice).** A *local choice* at $w = w_j$ consists of a uniformizer $\varpi$ of $E_w$ whose Artin symbol is the class of $\varphi_j$, a unit $u$ of $O_w$ whose Artin symbol is the class of $\gamma_j$, and a homomorphism $\mathrm{ind} \colon \mathbb{F}_w^\times \to \mathbb{Z}/\ell^\nu$ with $\mathrm{ind}(\bar u) = 1$.

Lean: `New.Patching.TaylorWilesPlaces.LocalChoice` (New/Congruences/FirstOrder/TiedTraces.lean).

**Lemma.** Every place of $Q$ has a local choice.

Lean: `New.Patching.TaylorWilesPlaces.nonempty_localChoice` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Local class field theory gives a *tame unit* $u$: a unit whose Artin symbol is the class of $\gamma_j$ and whose residue generates $\mathbb{F}_w^\times$. It also gives a uniformizer $\varpi$ with Artin symbol the class of $\varphi_j$ (see [Class field theory](/chapter/class-field-theory/)). Since $\ell^\nu \mid q - 1$, the lemma on residue logarithms of [the last section](/chapter/tied-traces/#norms-at-one-prime) gives $\mathrm{ind}$ with $\mathrm{ind}(\bar u) = 1$. $\square$

A local choice gives three objects on $\mathrm{GL}_n(\mathbb{F}_w)$:

- the logarithm of the first entry $\mathrm{ind}_1 = \mathrm{ind} \circ \mathrm{firstEntry}$ on the line stabilizer $K$;
- the logarithm of the determinant $\mathrm{ind}_{\det} = \mathrm{ind} \circ \det$;
- the *diamond element* $\langle\gamma\rangle = \mathrm{diag}(\bar u, 1, \ldots, 1)$.

Lean: `New.Patching.TaylorWilesPlaces.LocalChoice.indLine`, `New.Patching.TaylorWilesPlaces.LocalChoice.indDet`, `New.Patching.TaylorWilesPlaces.LocalChoice.diamond` (New/Congruences/FirstOrder/TiedTraces.lean).

The transfer of $\mathrm{ind}_1$ from $K$ to $\mathrm{GL}_n(\mathbb{F}_w)$ is $\mathrm{ind}_{\det}$, by the theorem on the first entry, and $\mathrm{ind}_{\det}(\langle\gamma\rangle) = \mathrm{ind}(\bar u) = 1$.

Lean: `New.Patching.TaylorWilesPlaces.LocalChoice.transfer_indLine`, `New.Patching.TaylorWilesPlaces.LocalChoice.indDet_diamond` (New/Congruences/FirstOrder/TiedTraces.lean).

### The groups at one place

The action of $\mathrm{GL}_n(\mathbb{F}_{w_j})$ on forms of principal level is `placeRep`, and its restriction to $K$ is `lineRep`.

Lean: `New.Patching.BaseLevel.placeRep`, `New.Patching.BaseLevel.lineRep` (New/Congruences/FirstOrder/TiedTraces.lean).

Let the places $w_j$ be off the base level, that is, off the level of $D$, its conjugate and $\ell$, with all forms of base level Hecke eigenforms at $w_j$.

**Lemma.** Under this condition the following hold.

1. The Hecke algebra commutes with the action of $\prod_j \mathrm{GL}_n(\mathbb{F}_{w_j})$.
2. An element $k$ of the parahoric subgroup of $\mathrm{GL}_n(E_w)$ with blocks of sizes $1$ and $n - 1$ acts on forms of principal level through its reduction, which lies in $K$.
3. If the elements of $K$ with first entry $1$ and determinant $1$ fix a form $y$, then the pro-$p$ Iwahori subgroup fixes $y$.
4. If $K$ acts on $y$ by $\psi \circ \mathrm{ind}_1$ for a character $\psi$ of $\mathbb{Z}/\ell^\nu$, then $y$ is fixed by the pro-$p$ Iwahori subgroup, and the parahoric of item 2 acts on it by $k \mapsto \psi(\mathrm{ind}(\overline{k_{00}}))$.
5. If $\mathrm{GL}_n(\mathbb{F}_w)$ acts on $y$ by $\psi \circ \mathrm{ind}_{\det}$, then the maximal compact subgroup acts by $k \mapsto \psi(\mathrm{ind}(\overline{\det k}))$.

Lean: `New.Patching.BaseLevel.commute_heckeAction_residueRep`, `New.Patching.BaseLevel.localFormRep_apply_eq_lineRep`, `New.Patching.BaseLevel.mem_levelSpace_proIwahori`, `New.Patching.BaseLevel.mem_parahoricEigenspace_line`, `New.Patching.BaseLevel.mem_parahoricEigenspace_det` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* For 1, the elements that commute with $\mathrm{heckeAction}(s)$ form a monoid, and it contains each factor because the action of each factor consists of local operators. Item 2 holds because forms of principal level are fixed by the kernel of reduction. For 3, the reduction of a pro-$p$ Iwahori element has first entry $1$ and determinant $1$ by [the last section](/chapter/tied-traces/#norms-at-one-prime), and the pro-$p$ Iwahori lies in the parahoric. Items 4 and 5 follow from 2 and 3, since $\mathrm{firstEntry}$ and $\det$ commute with reduction. $\square$

### Traces in the Hecke algebra

**Proposition.** Let the places be of prime norm and off the level $L$, and let $N$ be a twist by $a$.

1. For each place $w$ of prime norm off level $L$ and each $i$, the function $x \mapsto \iota_\ell(\lambda_{w,i}(x))$, the $i$-th Hecke eigenvalue at $w$, lies in $\mathbb{T}$.
2. For each $g \in G$ and each $i$, the function $x \mapsto$ (coefficient of $X^i$ in the characteristic polynomial of $N_x(g)$) lies in $\mathbb{T}$.

Lean: `New.Patching.BaseLevel.heckeEigenvalues_mem_heckeAlgebra`, `New.Patching.BaseLevel.charpoly_coeff_mem_heckeAlgebra` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* For 1, the Hecke operator $T$ at $w$ acts on the forms of $x$ by $\lambda_{w,i}(x)$, so $\mathrm{heckeAction}$ of this function is $T$ on forms of level $L$. The operator $T$ is supported at a place not above $\ell$, so it keeps the integral forms.

For 2, the twist multiplies the coefficient by $a(g)^{n - i}$, which is integral. So it suffices to treat $\rho_x$. Since $\rho_x$ is attached to $x$, the coefficient for $\rho_x(g)$ is a limit of the coefficients of the Hecke polynomials at the places $w$ whose Frobenius elements tend to $g$. At such a $w$ off level $L$, the coefficient of $X^i$ is $\pm q_w^{\binom{n - i}{2}}\,\lambda_{w, n - i}(x)$, which lies in $\mathbb{T}$ by 1. All but finitely many places are off level $L$, and $\mathbb{T}$ is closed. $\square$

**Definition (Congruent systems).** Two systems $x$ and $x'$ are *congruent* if, for every $g$ and $i$, the coefficients of $X^i$ in the characteristic polynomials of $N_x(g)$ and $N_{x'}(g)$ differ by an element of norm less than $1$.

Lean: `New.Patching.BaseLevel.IsCongruent` (New/Congruences/FirstOrder/TiedTraces.lean).

**Proposition (The congruence idempotent).** Let $N$ be a twist, with integral characteristic polynomials on all systems of level $L$. For every system $\pi$ there is $A \in \mathbb{T}$ with $A(x) = 1$ if $x$ is congruent to $\pi$ and $A(x) = 0$ otherwise.

Lean: `New.Patching.BaseLevel.exists_indicator_isCongruent` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* For each system $x'$ not congruent to $\pi$, choose $g$ and $i$ with coefficients $b'$ at $x'$ and $b_\pi$ at $\pi$ such that $|b' - b_\pi| \geq 1$. Let $u_{x'} = b' - (\text{coefficient at } x)$, an element of $\mathbb{T}$ by the last proposition. Then $u_{x'}(x') = 0$. If $x$ is congruent to $\pi$, the ultrametric inequality gives $|u_{x'}(x)| \geq 1$. Put $s = \prod_{x'} u_{x'}$. Then $s$ vanishes at all systems not congruent to $\pi$ and has norm at least $1$ at all systems congruent to $\pi$. Put
$$A = 1 - \prod_{y \sim \pi} \bigl(1 - s(y)^{-1} s\bigr),$$
where $y$ runs over the systems congruent to $\pi$. Each $s(y)^{-1}$ is integral, so $A \in \mathbb{T}$. At $x \sim \pi$ the factor for $y = x$ is $0$, so $A(x) = 1$. At $x \not\sim \pi$, $s(x) = 0$, so $A(x) = 1 - 1 = 0$. $\square$

This is the idempotent of one local factor of a finite algebra over a henselian local ring, written down by hand.

### Traces and the tied ideal

**Definition (Trace element).** For $P \in \mathbb{Z}_\ell[X]$ and $h, g \in G$, the *trace element* $\mathrm{tr}[P(h)g] \in \mathbb{T}$ is the function $x \mapsto \mathrm{tr}(P(N_x(h))\,N_x(g))$.

Lean: `New.Patching.BaseLevel.traceElement` (New/Congruences/FirstOrder/TiedTraces.lean).

It lies in $\mathbb{T}$: the trace is minus a coefficient of the characteristic polynomial, and $P(N_x(h))N_x(g)$ is a combination of the $N_x(h^k g)$.

**Definition (Tame trace).** At $w_j$, $\mathrm{tr}[(\gamma_j - 1)g\,P(\varphi_j)] = \mathrm{tr}[P(\varphi_j)\gamma_j g] - \mathrm{tr}[P(\varphi_j) g]$. For $P = 1$ it equals $\mathrm{tr}[(\gamma_j - 1)g]$, the trace element of $X - 1$ at $\gamma_j$.

Lean: `New.Patching.BaseLevel.tameTrace`, `New.Patching.BaseLevel.tameTrace_one` (New/Congruences/FirstOrder/TiedTraces.lean).

**Definition (Tied ideal).** Let $H_j \in \mathbb{Z}_\ell[X]$ and let $\alpha_j$ be variables. The *tied ideal* $\mathfrak{a} \subseteq \mathbb{T}[\alpha_j : j \in J]$ is generated by the elements $\ell^\nu\,\mathrm{tr}[g]$ and
$$\mathrm{tr}[(\gamma_j - 1)g] - \alpha_j\,\mathrm{tr}[(\varphi_j - 1)H_j(\varphi_j)\,g]$$
for all $g \in G$ and $j \in J$.

Lean: `New.Patching.BaseLevel.tiedIdeal` (New/Congruences/FirstOrder/TiedTraces.lean).

These generators are the trace forms of the tie relations of [Auxiliary primes](/chapter/tied-traces/#auxiliary-primes), with $\alpha_j$ in place of the slope. Only the coefficients of square-free monomials $\prod_{j \in S}\alpha_j$ are read later. This has the effect of $\alpha_j^2 = 0$, so $\alpha_j$ is a first-order variable. The generators have the form $t - X_j r$ of the proposition that the family kills ties in [the last section](/chapter/tied-traces/#norms-at-one-prime).

**Remark (Formalization).** The tied ideal is an ideal of the polynomial ring `MvPolynomial J (D.heckeAlgebra Q.place)`, not of a quotient by the $\alpha_j^2$. The source does not form that quotient. It reads coefficients instead.

### From eigenvectors to operators

**Lemma (Eigenvectors to weighted sums).** Let a finite group $\Gamma$ act by local operators at $w_j$ through $\rho$, let $\chi \colon \Gamma \to \mathbb{Z}/\ell^\nu$, let $r, s \in \mathbb{T}$, and let $B$ be a linear map on forms. Fix $\mathrm{shift} \in \mathbb{Z}/\ell^\nu$ and $\mathrm{root} \in \mathbb{C}$. Suppose that $r(x)\,z = s(x)\,B z$ for every form $z$ in a system $x$ on which $\Gamma$ acts by $\psi \circ \chi$, for every character $\psi$ with $\psi(\mathrm{shift}) \neq \mathrm{root}$. Let the weight be $f(\cdot - \mathrm{shift}) - \mathrm{root}\cdot f$. Then
$$\mathrm{W}_\chi(\text{weight}) \cdot \mathrm{heckeAction}(r) = B\,\mathrm{W}_\chi(\text{weight}) \cdot \mathrm{heckeAction}(s).$$

Lean: `New.Patching.BaseLevel.weightedSum_mul_heckeAction_eq_of_eigen` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Fix $y$ in a system $x$. For a function $F$ on $\mathbb{Z}/\ell^\nu$, put $T(F) = \sum_\gamma (F(\chi(\gamma) - \mathrm{shift}) - \mathrm{root}\, F(\chi(\gamma)))\,\rho(\gamma) y$. Then $T(f)$ is the weighted sum at $y$, and $T$ is linear in $F$. The characters $\psi$ of $\mathbb{Z}/\ell^\nu$ are a basis of the functions. Shifting the summation index shows that $\Gamma$ acts on $T(\psi)$ by $\psi^{-1} \circ \chi$. Also $T(\psi) = (\psi(-\mathrm{shift}) - \mathrm{root})\sum_\gamma \psi(\chi(\gamma))\rho(\gamma)y$, so $T(\psi) = 0$ if $\psi^{-1}(\mathrm{shift}) = \mathrm{root}$. In the other case the hypothesis applies to $z = T(\psi)$ with the character $\psi^{-1}$. Both Hecke operators act on $y$ by scalars, so the identity holds at $y$. $\square$

### The tame generator is a diamond operator

**Theorem.** Let the places be off the base level, let $N$ be a twist by $a$ with $a(\gamma_j) = 1$, and fix a local choice at $w_j$. Let $y$ be a form in a system $x$ on which $\mathrm{GL}_n(\mathbb{F}_{w_j})$ acts by $\psi \circ \mathrm{ind}_{\det}$. Then
$$\mathrm{tr}[(\gamma_j - 1)g\,p(\varphi_j)](x)\cdot y = \mathrm{tr}[p(\varphi_j)g](x)\cdot(\langle\gamma\rangle - 1)y .$$

Lean: `New.Patching.BaseLevel.tameTrace_smul_eq_diamond_sub_one` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Assume $y \neq 0$. By item 5 of the lemma on the groups, the maximal compact subgroup acts on $y$ by $k \mapsto \psi(\mathrm{ind}(\overline{\det k}))$. Local-global compatibility at Iwahori level ([`isParahoricCompatible_galRep`](/decl/New.Patching.isParahoricCompatible_galRep/)) then says that $\rho_x(\gamma_j)$ is killed by $X - \psi(\mathrm{ind}(\bar u)) = X - \psi(1)$. So $N_x(\gamma_j) = \rho_x(\gamma_j) = \psi(1)$ is a scalar, and the tame trace at $x$ is $(\psi(1) - 1)\,\mathrm{tr}[p(\varphi_j)g](x)$. On the other side, $\langle\gamma\rangle y = \psi(\mathrm{ind}_{\det}\langle\gamma\rangle)y = \psi(1)y$. $\square$

**Corollary.** In the same setting, for every weight $f$,
$$\mathrm{W}_{\mathrm{ind}_{\det}}(f) \cdot \mathrm{tr}[(\gamma_j - 1)g\,p(\varphi_j)] = (\langle\gamma\rangle - 1)\,\mathrm{W}_{\mathrm{ind}_{\det}}(f)\cdot\mathrm{tr}[p(\varphi_j)g]$$
as operators, where the traces act by $\mathrm{heckeAction}$. In particular the norm $\mathrm{Nm}_j$ over $\mathrm{GL}_n(\mathbb{F}_{w_j})$ kills $\mathrm{tr}[(\gamma_j - 1)g]$.

Lean: `New.Patching.BaseLevel.weightedSum_indDet_mul_tameTrace`, `New.Patching.BaseLevel.norm_mul_traceElement_tameGenerator_eq_zero` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Apply the lemma on eigenvectors with $\mathrm{shift} = 0$, $\mathrm{root} = 0$ and $B = \langle\gamma\rangle - 1$. For the second claim, take $f = 1$ and $p = 1$. Then $\mathrm{W}(1) = \mathrm{Nm}_j$ and $(\langle\gamma\rangle - 1)\mathrm{Nm}_j = 0$. $\square$

The second claim is condition 1 of [the operator at one place](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm), and the hypothesis $\mathrm{Nm}_j\,t = 0$ of the proposition that the family kills ties.

### The Frobenius element is a Hecke operator

Let $U$ be the Hecke operator of $\mathrm{diag}(\varpi, 1, \ldots, 1)$ for the pro-$p$ Iwahori subgroup at $w_j$, and put $\tilde U = a(\varphi_j)\,U$.

**Definition.** For $p \in \mathbb{Z}_\ell[X]$, the operator $p(\tilde U)$ on forms is $p(a(\varphi_j) X)$ evaluated at $U$.

Lean: `New.Patching.BaseLevel.aevalHecke` (New/Congruences/FirstOrder/TiedTraces.lean).

**Theorem.** Let the places be off the base level, let $N$ be a twist by $a$ with $a(\gamma_j) = 1$, and fix a local choice at $w_j$. Let $y$ be a form in a system $x$ on which $K$ acts by $\psi \circ \mathrm{ind}_1$, where $\psi(n!) \neq 1$. Then
$$\mathrm{tr}[(\gamma_j - 1)g\,p(\varphi_j)](x)\cdot y = \mathrm{tr}[(\gamma_j - 1)g](x)\cdot p(\tilde U)\,y .$$

Lean: `New.Patching.BaseLevel.tameTrace_smul_eq_aevalHecke` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* By item 4 of the lemma on the groups, $y$ lies in the eigenspace of the line parahoric for the character $k \mapsto \psi(\mathrm{ind}(\overline{k_{00}}))$. The value $\psi(\mathrm{ind}(\bar u))^{n!} = \psi(n!)$ is not $1$. Under this condition, [`hecke_eq_frob_on_parahoricEigenspace`](/decl/New.Patching.hecke_eq_frob_on_parahoricEigenspace/) says that, against $T = \rho_x(\gamma_j) - 1$ inside a trace, a polynomial in $U$ acting on $y$ equals the same polynomial in $\rho_x(\varphi_j)$. Apply it to $p(a(\varphi_j)X)$, and use $N_x(\gamma_j) = T + 1$ and $N_x(\varphi_j) = a(\varphi_j)\rho_x(\varphi_j)$. $\square$

The condition $\psi(n!) \neq 1$ fails for some characters, so the theorem does not give an identity of operators at once. The weight lemma and the shift lemma of [the last section](/chapter/tied-traces/#norms-at-one-prime) handle this.

**Lemma.** Let the places be off the base level, and fix a local choice at $w_j$.

1. For every weight $f$, the values of $\mathrm{W}_{\mathrm{ind}_1}(f)$ (the sum over $K$) are fixed by the pro-$p$ Iwahori subgroup.
2. There is an additive map $B$ from weights to local operators at $w_j$ with $B(f) = p(\tilde U)\,\mathrm{W}_{\mathrm{ind}_1}(f)$.
3. For such $B$, every $k \in K$ satisfies $k\,B(1) = B(1)$.

Lean: `New.Patching.BaseLevel.weightedSum_indLine_mem_levelSpace`, `New.Patching.BaseLevel.exists_aevalHecke_weightedSum`, `New.Patching.BaseLevel.lineRep_mul_eq_self` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* For 1, an element $k$ of $K$ with first entry $1$ shifts the weight by $\mathrm{ind}_1(k) = 0$, so it fixes the values. Then item 3 of the lemma on the groups applies. For 2, the weighted sum is a local operator, and its values are pro-$p$ Iwahori fixed by 1. A result of [Building the representations](/chapter/building-representations/) then gives a local operator equal to the Hecke polynomial after it. Additivity holds because both sides are additive in $f$. For 3, lift $k$ to the parahoric. The values of $\mathrm{W}_{\mathrm{ind}_1}(1)$ lie in its fixed space, since the weight $1$ is constant, and $U$ keeps this fixed space. $\square$

**Theorem (The dictionary modulo $\ell^\nu/(2n!)$).** Let the places be off the base level, let $N$ be a twist by $a$ with $a(\gamma_j) = 1$, fix a local choice at $w_j$, and let $B$ be as in the last lemma. Let $\sigma$ be a reduction modulo $\ell^\nu/(2n!)$ on the ring of integral operators. Then
$$\sigma\bigl(B(\mathrm{valMinAbs})\cdot\mathrm{tr}[(\gamma_j - 1)g]\bigr) = \sigma\bigl(\mathcal{L}_{\mathrm{ind}_1}\cdot\mathrm{tr}[(\gamma_j - 1)g\,p(\varphi_j)]\bigr).$$

Lean: `New.Patching.BaseLevel.map_aevalHecke_valMinAbs_mul_tameTrace` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Let $\mathcal{E}(f) = B(f)\,\mathrm{tr}[(\gamma_j - 1)g] - \mathrm{W}_{\mathrm{ind}_1}(f)\,\mathrm{tr}[(\gamma_j - 1)g\,p(\varphi_j)]$. It is additive in $f$, and the claim is $\sigma(\mathcal{E}(\mathrm{valMinAbs})) = 0$. By the shift lemma with $k = n!$, it suffices to show $\mathcal{E}(f(\cdot - n!) - f) = 0$ for all $f$. Apply the lemma on eigenvectors with $\Gamma = K$, $\chi = \mathrm{ind}_1$, $\mathrm{shift} = n!$, $\mathrm{root} = 1$ and $B = p(\tilde U)$. Its hypothesis, for characters with $\psi(n!) \neq 1$, is the last theorem. $\square$

So $n!$ in $2n!$ comes from the characters that the Frobenius dictionary cannot see, and $2$ from the shift lemma.

### The root chain kills the norm

**Theorem.** Let the places be off the base level, fix a local choice at $w_j$, and let $B$ be as above with $B(1)$ a local operator at $w_j$. Let $p = (X - q_j^t)H$ and $\delta \in \mathbb{T}$. Suppose that for every system $x$ of base level with $\delta(x) \neq 0$, the Hecke polynomial of $x$ at $w_j$ has a root chain of length $t + 1$ at $a(\varphi_j)^{-1}$, with cofactor dividing $H$ (`HasRootChain`). Then
$$\mathrm{heckeAction}(\delta)\cdot\mathrm{Nm}\cdot B(1) = 0,$$
where $\mathrm{Nm}$ is the sum over $\prod_i \mathrm{GL}_n(\mathbb{F}_{w_i})$.

Lean: `New.Patching.BaseLevel.heckeAction_mul_norm_mul_eq_zero` (New/Congruences/FirstOrder/TiedTraces.lean).

*Proof.* Fix an invariant positive definite pairing $F$ on forms. Put $S = \mathrm{Nm}\cdot B(1)$. The values of $S$ have base level, because $\mathrm{Nm}$ absorbs every group element. Let $w$ be a form of base level in a system $x$ with $\delta(x) \neq 0$. The chain lemma of [Iwahori exponents, Satake and the chain lemma](/chapter/iwahori-satake/) ([`pairing_aeval_heckeCoset_eq_zero`](/decl/New.Patching.pairing_aeval_heckeCoset_eq_zero/)) gives $F(w, B(1)y) = 0$. The value $B(1)y$ is $p(\tilde U)$ applied to a pro-$p$ Iwahori fixed form, by item 1 of the last lemma. Since $w$ is fixed by the finite groups and $F$ is invariant, $F(w, S y) = 0$. Now $\mathrm{heckeAction}(\delta)$ commutes with $S$, by item 1 of the lemma on the groups and because $B(1)$ is a local operator. Hence $\delta S y$ is orthogonal to $\delta w$ for every form $w$ of base level: in systems with $\delta(x) = 0$ the scalar is $0$, and in the others the last step applies. As $\delta S y$ has base level, it is orthogonal to itself, so it is $0$ by positivity. $\square$

This is the identity $\delta\,\mathrm{Nm}\,U' = 0$ used for condition 3 of [the operator at one place](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm). With $L = \delta\,\mathrm{Nm}$ it gives the hypothesis $L\,B(1) = 0$ of the theorem that the derivative is a norm up to $n$, in [the last section](/chapter/tied-traces/#norms-at-one-prime).
