---
title: Ramified places, auxiliary places and Selmer modules
lean:
  - Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean
  - Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean
  - Lib/GaloisRep/TaylorWiles.lean
  - Lib/GaloisRep/Main/SelmerModules.lean
decls:
  - New.GaloisRep.Attached.local_global_of_eigencharacter
  - New.GaloisRep.Attached.isLabelledAt
  - New.Patching.TaylorWilesPlaces
  - New.Patching.BaseLevel.exists_higman_operator
  - New.selmerModule
  - New.Selmer.shaOdd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ramified places, auxiliary places and Selmer modules

The theorem on every rank gives local information only at places where the form is spherical. Volume 12 needs more at a few split places where the form is ramified, with a tame type. It also needs an operator at auxiliary places of Taylor-Wiles type and a definition of Selmer modules. This section describes these three pieces. They live in the folders `LocalGlobal`, the file `TaylorWiles.lean` and the file `SelmerModules.lean`.

### Local-global compatibility at a ramified split place

The textbook statement is the local-global compatibility of Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), and Taylor and Yoshida, *Compatibility of local and global Langlands correspondences*, J. Amer. Math. Soc. 20 (2007), away from $\ell$. Above $\ell$, see Barnet-Lamb, Gee, Geraghty and Taylor, *Local-global compatibility for $l = p$, II* (2014), Theorem 1.1. It says that the Weil-Deligne representation of $r$ at $w$ is, after Frobenius semisimplification, the image of $\Pi_w$ under the local Langlands correspondence. The source proves a weaker statement in terms of polynomials that kill inertia and Frobenius elements, with no local Langlands correspondence.

The first case is a pro-$p$ Iwahori eigenvector. Let $w$ be split, with residue field of $q$ elements, and $N = |n|$. A form $f$ is a pro-$p$ Iwahori eigenvector at $w$ for the torus character

$$t \mapsto \prod_{i} \xi_i(t_i)\,|t_i|^{N-1-i}$$

if the pro-$p$ Iwahori subgroup fixes $f$ and the torus acts on $f$ through this character, for characters $\xi_i$ of $E_w^\times$.

**Theorem (Compatibility for a sorted Iwahori eigencharacter).** Let $r$ be attached to the eigenform $f$. Let $f$ be a pro-$p$ Iwahori eigenvector at the split place $w$ for the torus character of $\xi$, with $|\xi_i(\varpi)|$ decreasing in $i$ for the uniformizer $\varpi$. Let $A$ lie above $w$. Let $s$ be in the decomposition group at $A$, with $s^{-1}$ acting as the $q^k$-th power map on the residue field of $A$. Let $x \in E_w^\times$ have valuation $k$ and local Artin symbol $s$. Then:

1. $r$ is of finite type at $A$: trivial on an open subgroup of inertia away from $\ell$, potentially crystalline above $\ell$;
2. $r$ has the jumps of $\kappa$ at $A$;
3. $\prod_i (X - \iota_\ell(\xi_i(x)))$ kills $s$.

Lean: `New.GaloisRep.Attached.local_global_of_eigencharacter` (Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean).

*Proof.* Let $D$ be the subgroup of the $y \in E_w^\times$ such that $(|y|, \xi(y))$ is a power of $(|x|, \xi(x))$. The proof is by strong induction on the index of $D$. If the index is $1$, then $k = 1$ and every $\xi_i$ is unramified. This is the spherical case, which is the theorem on every rank. Otherwise duality for the finite group $E_w^\times / D$ gives a character $\chi$ of prime order that is trivial on $D$. Since $\chi$ is tame, the Grunwald theorem of the source gives a global character $\mu$. Its field is a cyclic step of prime degree with one place $u$ above $w$, and $\chi$ is the local component. Base change $f$ to $f'$ over the step, with eigencharacter $\xi_i \circ N$ for the local norm $N$ (Lean: `New.exists_baseChange_isIwahoriEigen`). The index for $f'$ is smaller. What holds at $A$ for the representation of $f'$ descends to $r$. Since $\chi(x) = 1$, $x$ is a norm, and $s$ fixes the step. $\square$

**Remark (Formalization).** Parts 1 and 2 of this theorem do not involve $s$, $x$ or $k$. The source docstring says that they stand in this statement because one induction proves all three parts. A reader who needs only parts 1 and 2 must still supply some $s$, $x$ and $k$ with the stated properties. For example, take $x = \varpi$, $k = 1$ and $s$ the local Artin symbol of $\varpi$, which the source treats as the inverse of a Frobenius element. Volume 12 does not use this theorem by name. It uses it through the next theorem and through the parahoric version (Lean: `New.Patching.isParahoricCompatible_galRep`).

The second case is a depth-zero type. A *product label* at a split place $w$ is a label $c$ of degree $d$ over the residue field, characters $\chi_l$ of the residue field with multiplicities $t_l$, and a faithful character $T$ of a finite extension $K$ of the residue field. The conditions are that $c \prod_l (X - x_l)$ is separable, where $x_l$ is the name of $\chi_l$ read through $T$, and that $d + \sum_l t_l = N$. The label of $f$ at $w$ is the character $\mathrm{lab}_T(c) \cdot \prod_l (\chi_l \circ \det_{t_l})$, with $\chi_l \circ \det$ on a block $\mathrm{GL}_{t_l}$ (Lean: `New.HasProductLabel`).

**Theorem (Compatibility for a product label).** Let $E$ have Weil data. Let $r$ be attached to the Hecke polynomials $P$ of an eigenform $f$ of weight $\kappa$. Let $f$ have a product label $(T, d, c, \chi, t)$ at the split place $w$, and let $A$ lie above $w$. Then:

1. $r$ is of finite type at $A$;
2. $r$ has the jumps of $\kappa$ at $A$;
3. if $\sigma$ has tame exponent $a$ at level $d!$, then $\prod_x (X - \iota_\ell(T^a(x)))$ kills $\sigma$, the product over the roots $x$ in $K$ of $c \prod_l (X - x_l)^{t_l}$, with multiplicity.

Lean: `New.GaloisRep.Attached.isLabelledAt` (Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean).

The source states that part 3 is a weak form of what the compatibility of Barnet-Lamb, Gee, Geraghty and Taylor, and of Caraiani, gives together with the description of inertial parameters of depth-zero representations of $\mathrm{GL}_n$. In plain terms, part 3 says that tame inertia acts on $r$ through the tame characters given by the roots of the label. The proof reduces to the Iwahori case by the same cyclic base change. Volume 12 uses this theorem in the file of attached representations and in the file that reads rows and columns from labels.

### Auxiliary places and Higman's criterion

The Taylor-Wiles method adds auxiliary places $w_j$ with $q_{w_j} \equiv 1 \bmod \ell^m$ and uses the fact that, at a principal level at these places, the integral forms are free over the group ring of a finite group $\Delta$. See Taylor and Wiles, *Ring-theoretic properties of certain Hecke algebras*, Ann. of Math. 141 (1995), and Clozel, Harris and Taylor, *Automorphy for some $\ell$-adic lifts of automorphic mod $\ell$ Galois representations*, Publ. Math. IHÉS 108 (2008), §3. The source proves a weaker statement: freeness up to a fixed integer, in the form of one operator.

**Definition (Taylor-Wiles places).** A family of Taylor-Wiles places for $m$, indexed by $J$, is a Frobenius datum at a finite place $w_j$ for each $j \in J$, such that no two of the places are equal or conjugate, and $m$ divides $q_{w_j} - 1$ for each $j$.

Lean: `New.Patching.TaylorWilesPlaces` (Lib/GaloisRep/TaylorWiles.lean).

Base data $\mathcal D$ fix a finite set of places, a space of forms of a fixed type there, and a common multiple $c$ of the orders of the stabilizers $\Gamma \cap gK_0g^{-1}$, where $\Gamma$ is the group of rational points and $K_0$ is the standard level. The forms of principal level at the places $w_j$ form a finite-dimensional space with a lattice of integral forms. The groups $\mathrm{GL}_N(k_{w_j})$ over the residue fields act on it (Lean: `New.Patching.BaseLevel.residueRep`).

**Theorem (Higman operator).** Let the places $w_j$ be off the base level. Let $\Delta$ be a finite group with an injective homomorphism $\varphi : \Delta \to \prod_j \mathrm{GL}_N(k_{w_j})$. Then some operator $\Psi$ on forms of principal level that keeps the integral forms satisfies

$$\sum_{g \in \Delta} \varphi(g^{-1})\,\Psi\,\varphi(g) = c.$$

Lean: `New.Patching.BaseLevel.exists_higman_operator` (Lib/GaloisRep/TaylorWiles.lean).

By Higman's criterion, the existence of such a $\Psi$ with $c = 1$ would say that the lattice is projective over $\mathbb Z_\ell[\Delta]$. With a general $c$, the statement is freeness up to $c$. If $\ell$ does not divide $c$, then $c$ is a unit of $\mathbb Z_\ell$, $\Psi/c$ satisfies Higman's criterion, and the lattice is projective.

*Proof.* Write $c$ as a sum $\sum_d u_{g^{-1}}(d)$ of values of a weight function $u$, using the stabilizer orders. The operator $\Psi$ multiplies a form by this weight. The weight is invariant under the principal level and ignores rational points, so $\Psi$ keeps forms, keeps the type at the base places and keeps the principal level. At each point the product is an integer multiple of the form, so $\Psi$ keeps integral forms. The action of $\varphi(d^{-1})$ is translation by a lift off the base places, and this turns the weight into $u_{g^{-1}}(d)$. Comparing term by term gives the identity. $\square$

**Remark (Formalization).** The source has `attribute [instance] TaylorWilesPlaces.apart` after the structure. So in every file that imports `TaylorWiles.lean`, instance search finds, for each family $Q$, the proof that its places are apart. This is not unsound. It can change which instance a later statement uses (finding F-023 of the notes). The file contains no patching, no deformation ring and no theorem of the form $R = \mathbb T$. Volume 12 uses the Higman operator at the auxiliary primes, in the file `FirstOrder/AuxiliaryPrimeTie`.

### Selmer modules

The textbook Selmer group $H^1_{\mathcal L}(E, M)$ is a set of cohomology classes with local conditions. The source works with cocycles.

**Definition (Selmer module).** Let $O$ be a ring, $B$ an $O$-module, $\rho$ a matrix representation over $O$ of size $n$, $S$ a set of finite places and $L$ a set of linear relations. The Selmer module is the $O$-module of functions $z : \operatorname{Gal}(\Omega/E) \to B^n$ such that $z$ is locally constant, $z$ is a cocycle for $\rho$, $z$ vanishes on the inertia groups above places outside $S$, and $z$ obeys every relation in $L$.

Lean: `New.selmerModule` (Lib/GaloisRep/Main/SelmerModules.lean).

The relations $L$ play the role of local conditions. The elements are cocycles, not classes modulo coboundaries, so the Selmer module is not a cohomology group.

**Definition (The odd module).** Let $\Lambda$ be a $\mathbb Z_\ell$-algebra and $\Lambda(-e)$ the Tate twist by the $e$-th power of the inverse cyclotomic character (Lean: `New.Selmer.tateTwist`). The module $\mathrm{Sha}^{\mathrm{odd}}(\ell, E, \Lambda, e, \nu)$ is the module of functions $z$ on $\operatorname{Gal}(\Omega/E)$ with values in $\Lambda/\ell^\nu$ such that $z$ vanishes on a local set above $\ell$, $z$ is odd under $g \mapsto c g c$ for complex conjugation $c$ if $e \neq 0$, and $z$ is a continuous cocycle for $\Lambda(-e)$ unramified outside $\ell$. The local set is the union of the inertia groups above $\ell$ for $e = 0$. For $e \neq 0$ it is the set of elements of the decomposition groups above $\ell$ with trivial cyclotomic character.

Lean: `New.Selmer.shaOdd` (Lib/GaloisRep/Main/SelmerModules.lean).

**Remark (Formalization).** The docstring of `shaOdd` says that for $e \neq 0$ the module describes the odd part of $Ш^1(E, \Lambda/\ell^\nu(-e))$. The source proves no comparison between `shaOdd` and $Ш^1$ (finding F-061 of the notes). The Selmer bounds of Volume 12 are bounds on this module of cocycles. A reader who wants a statement about $Ш^1$ must prove the comparison. The class `New.CMFieldWithRoot5040` in the same file bundles a CM field, an embedding into $\Omega$ and a primitive root of unity of order $5040$.
