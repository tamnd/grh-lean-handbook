---
title: Tate duality and Ribet cocycles
lean:
  - New/Congruences/LocalLoss/TateDualBound.lean
decls:
  - New.Selmer.ComesFromClass
  - New.Selmer.ker_compLeft_mkQ_eq_pPowMultiples
  - New.Selmer.exists_crysCocycles_pow_smul_eq_coboundary
  - New.Selmer.relLength_le_of_comesFromClass
  - New.Selmer.comesFromClass_of_mem_ribetCocycles
  - New.Selmer.relLength_ribetCocycles_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tate duality and Ribet cocycles

The defect $\delta_{\mathcal{Q}}(L^\vee(1))$ is a statement on the dual lattice. The argument needs a bound on cocycles of $L$ modulo $\ell^m$: those that the construction of Ribet produces, modulo those that obey the crystalline relations. This section proves that the first is at most the second. The tool is local Tate duality modulo $\ell^m$ in the form of [the divisibility for reductions](/chapter/local-duality/#duality-for-crystalline-cocycles).

Here $\Gamma$ maps to $G_\ell$ by an open embedding $j$, $R$ is the ring of integers of a finite extension of $\mathbb{Q}_\ell$, $\sigma : \Gamma \to M_d(R)$, and $L = R^d$ is its matrix lattice. For submodules $S, T$ the relative length $\mathrm{relLength}(S, T)$ is the length of $S/(S \cap T)$. The class is $\mathcal{Q} = \mathrm{InClass}(F, K, U)$.

### Maps that come from the class

**Definition (Comes from the class).** A map $s : \Gamma \to (R/\ell^m)^d$ *comes from* $\mathcal{Q}$ if $s = t \circ a$ for a lattice $Y \in \mathcal{Q}$, an $R$-linear map $t : Y \to (R/\ell^m)^d$ with $t(gy) = \sigma(g)t(y)$, and a crystalline cocycle $a \in Z_f(Y)$.

Lean: `New.Selmer.ComesFromClass` (New/Congruences/LocalLoss/TateDualBound.lean).

**Lemma (Kernel of reduction).** A vector $x \in R^d$ reduces to $0$ modulo $\ell^m$ if and only if $x \in \ell^m R^d$.

Lean: `New.Selmer.ker_compLeft_mkQ_eq_pPowMultiples` (New/Congruences/LocalLoss/TateDualBound.lean).

*Proof.* Both sides say that $\ell^m$ divides every coordinate of $x$. $\square$

**Lemma (A coboundary divisible by $\ell^m$).** Let $Y, L$ be lattices over $R$ with an action of $\Gamma$, and $q : Y \to L$ an $R$-linear map with $g q(y) - q(gy) \in \ell^m L$ for all $g, y$. Let $\psi$ be the form $y \otimes \varphi \mapsto \varphi(q(y))$ on $Y \otimes L^\vee(1)$. Then there is $c \in Z_f\big((Y \otimes L^\vee(1))^\vee(1)\big)$ with $\ell^m c(g) = g\psi - \psi$ for all $g$.

Lean: `New.Selmer.exists_crysCocycles_pow_smul_eq_coboundary` (New/Congruences/LocalLoss/TateDualBound.lean).

*Proof.* Since $gqg^{-1} - q$ has values in $\ell^m L$ and $L$ is torsion free, there is a unique $\delta_g : Y \to L$ with $\ell^m \delta_g = gqg^{-1} - q$. Put $c(g)(y \otimes \varphi) = \varphi(\delta_g(y))$. Then $\ell^m c(g) = g\psi - \psi$. The map $g \mapsto g\psi - \psi$ is a coboundary, so it lies in $Z_f$. As $Z_f$ is saturated, that is, $\ell^m c \in Z_f$ implies $c \in Z_f$, we get $c \in Z_f$. $\square$

### The duality bound

**Theorem (Duality bound).** Let $j$ be an open embedding and $L \in \mathcal{Q}$. Let $N$ be a submodule of maps $\Gamma \to (R/\ell^m)^d$ each of which comes from $\mathcal{Q}$. Let $A$ be the image of $Z_f(L)$ under reduction modulo $\ell^m$. Then
$$\mathrm{relLength}(N, A) \leq \delta_{\mathcal{Q}}(L^\vee(1)).$$

Lean: `New.Selmer.relLength_le_of_comesFromClass` (New/Congruences/LocalLoss/TateDualBound.lean).

*Proof.* Step 1: a perfect pairing. There is a $\mathbb{Z}_\ell$-linear map $f : R \to \mathbb{Z}_\ell$ for which $(\varphi, x) \mapsto f(\varphi(x))$ identifies $L^\vee(1)$ with the $\mathbb{Z}_\ell$-dual of $L$. Call this identification $b$.

Step 2: the reduction. Let $\tau : R^d \to (R/\ell^m)^d$ be the reduction. It is onto, its kernel is $\ell^m L$ by the lemma on the kernel, and $\tau(gx) = \sigma(g)\tau(x)$. With the discrete topology, $(R/\ell^m)^d$ is a discrete $\Gamma$-module $V$: the reduction of a crystalline cocycle of a lattice in $\mathcal{Q}$ is continuous, since lattices in $\mathcal{Q}$ are potentially crystalline.

Step 3: orthogonality. Let $H = \mathrm{cupOrthogonal}(\mathcal{Q}, L^\vee(1))$, the cocycles of $L^\vee(1)$ whose cup products with all crystalline cocycles of the class are coboundaries. Let $s = t \circ a$ come from $\mathcal{Q}$. Lift $t$ to an $R$-linear map $q : Y \to L$ with $\tau \circ q = t$. Then $q$ is equivariant modulo $\ell^m L$. The pairing $(y, \varphi) \mapsto f(\varphi(q(y)))$ modulo $\ell^m$ is one of the pairings tested in $\mathrm{cupOrthogonal}$; the lemma on a divisible coboundary shows that it is a valid pairing of exponent $m$. So for $z \in H$ the cup product of $a$ and $z$ under it is a coboundary. This cup product is the cup product of $s$ and $z$ under $b$ modulo $\ell^m$. So $s$ is orthogonal to $H$.

Step 4: duality. Every element of $N$ is orthogonal to $H$, and so is every element of $A$, since $\tau \circ c$ comes from the class with $Y = L$ and $t = \tau$. The divisibility for reductions of [local duality](/chapter/local-duality/#duality-for-crystalline-cocycles) gives
$$[N : N \cap A] \ \big|\ [Z_f(L^\vee(1)) : Z_f(L^\vee(1)) \cap H].$$
A relative index is the cardinality of the quotient, and a divisibility of the cardinalities of two finite $R$-modules gives the inequality of their lengths. $\square$

### Ribet cocycles

Let $\eta : \Gamma \to G$ be a group map. Let $u_x : G \to M_n(R)$, $x \in X$, be a finite family, and $\rho : G \to M_d(R)$. The *Ribet cocycles* $\mathrm{ribetCocycles}(u, \rho, \ell^m)$ are the cocycles $w : G \to (R/\ell^m)^d$ for $\rho$ that obey every linear relation among the families $(u_x(g) - 1)_x$. They are defined in [main summands](/chapter/main-summands/#cocycles-relations-and-selmer-lengths).

**Lemma (Ribet cocycles come from the class).** Suppose the matrix lattice of $u_x \circ \eta$ lies in $\mathcal{Q}$ for every $x$. If $w$ is a Ribet cocycle, then $w \circ \eta$ comes from $\mathcal{Q}$ for $\rho \circ \eta$.

Lean: `New.Selmer.comesFromClass_of_mem_ribetCocycles` (New/Congruences/LocalLoss/TateDualBound.lean).

*Proof.* By [the graph subrepresentation](/chapter/main-summands/#cocycles-relations-and-selmer-lengths), there are $k$ and a subrepresentation $Y$ of $\big(\prod_x M_n(R)\big) \times (R/\ell^m)^d$ such that the first projection is injective on $Y$, and $\big((u_x(g) - 1 + \ell^{mk} v_x)_x, w(g)\big) \in Y$ for all $g \in G$ and all $v$. Then $Y$ is torsion free, so it is a lattice; give it the action through $\eta$. Let $t$ be the second projection, which is equivariant, and $a(g) = \big((u_x(\eta g) - 1)_x, w(\eta g)\big)$. Then $t \circ a = w \circ \eta$.

$Y$ is in $\mathcal{Q}$: the columns of the first component embed $Y$ in a sum of copies of the lattices of the $u_x \circ \eta$, and the class is closed under jointly injective maps. $a$ is crystalline: let $y_0 = ((\ell^{mk} \cdot 1)_x, 0) \in Y$. Since $u_x(1) = 1$, $\ell^{mk} a(g) = g y_0 - y_0$ by the injectivity of the first projection. So $\ell^{mk} a$ is a coboundary, and $a \in Z_f(Y)$ by saturation. $\square$

**Theorem (Ribet cocycle bound).** Let $j$ be an open embedding. Suppose the lattices of all $u_x \circ \eta$ lie in $\mathcal{Q}$, and the matrix lattice $L$ of $\rho \circ \eta$ lies in $\mathcal{Q}$. Let $B$ be the maps $\Gamma \to (R/\ell^m)^d$ that obey every linear relation that holds on $Z_f(L)$. Then
$$\mathrm{relLength}\big(\mathrm{ribetCocycles}(u, \rho, \ell^m),\ \{w : w \circ \eta \in B\}\big) \leq \delta_{\mathcal{Q}}(L^\vee(1)).$$

Lean: `New.Selmer.relLength_ribetCocycles_le` (New/Congruences/LocalLoss/TateDualBound.lean).

*Proof.* Let $N$ be the image of the Ribet cocycles under $w \mapsto w \circ \eta$, and $A$ the reduction of $Z_f(L)$. The relative length does not change when passing to images: the left side is $\mathrm{relLength}(N, B)$. The reduction of a crystalline cocycle obeys every relation that holds on $Z_f(L)$, so $A \subset B$ and $\mathrm{relLength}(N, B) \leq \mathrm{relLength}(N, A)$. Every member of $N$ comes from $\mathcal{Q}$ by the previous lemma, and the duality bound finishes the proof. $\square$

### The forward uses

Two results of [the denominator bound](/chapter/denominator-bound/), in the same namespace, combine this chapter over the places $v$ of $E$ above $\ell$. We state them once; they are proved there.

1. Let the local lattices of all $u_x$ and of $\rho$ at every $v$ lie in a class $\mathrm{InClass}(F_v, C_v, U_v)$. Then the crystalline colength of $\rho$ modulo $\ell^M$ is at most $\sum_v \delta_{\mathrm{InClass}(F_v, C_v, U_v)}\big((\rho_v)^\vee(1)\big)$, where $\rho_v$ is the local lattice of $\rho$ at $v$. The proof bounds the colength of an intersection over $v$ by the sum of colengths, and applies the Ribet cocycle bound at each $v$ with $\eta$ the inclusion of the decomposition group. Lean: `New.Selmer.crystallineColength_le_sum_dualDefect` (New/Congruences/FirstOrder/TraceRelations.lean).
2. For a main summand $R$ of rank $r'$ and representations $\rho_x$ of a given type, over all large $O$, there are classes at each $v$ that contain the local lattices of all $u_x$ and of the $t + 1$ summands of $u_\pi$, and the sum over the summands and over $v$ of the normalised defects is at most $r' \cdot \mathrm{localDefectBound}(\ell)$. The proof applies the defect at a place of Section 6 at each $v$, with the classes of Section 7. Lean: `New.Selmer.eventually_exists_inClass_sum_dualDefect_le` (New/Congruences/FirstOrder/TraceRelations.lean).

These are the two places where the colength bound of [main summands](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) meets the defect bound.
