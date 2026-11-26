---
title: The objects and their order
lean:
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
  - New/UpperBound/Objects/Columns.lean
decls:
  - New.Data.m_eq_two_mul_varrho_add_two
  - New.Data.card_X
  - New.Data.card_Y_m
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The objects and their order

Theorem A bounds the dimension of the space of target forms. Its proof compares two maps on source forms: the composite lift, which goes up a chain of theta lifts and then restricts, and the lower chain composed with the Poincaré map, which goes along a second chain. [Theorem A and its plan](/chapter/theorem-a-plan/) states the theorem, the three inputs and how they meet. The place of Theorem A in the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/). This chapter builds every object that those inputs name. It proves only the facts that hold by construction: sizes, equivariance, the shape of a weight, the way a datum changes under a change of lattice. The deep statements are left to later chapters of this volume.

The objects are many, and their definitions refer to each other. The order of the sections follows the order of need. A reader who wants the picture first can read this section and Section 7, and return to the others when a name appears.

### The data and the two chains

Fix admissible data $D$ (the data of [data and sizes](/chapter/data-and-sizes/)). The data give the CM field $E$ with its $f$ infinite places $\Phi$, the number $m$ of lifts, the rank $r$ of the target, and the derived numbers

$$k = r + 1 - m, \qquad t = 5r, \qquad n_j = k + j(t+1), \qquad \Delta/2 = r^8, \qquad \Delta = 2r^8.$$

Here $m$ is a power of $2$ with $\sqrt{x} \le m \le 2\sqrt{x}$, and $r$ is a power of $3$ with $x^5 \le r \le 3x^5$, for the length $x$ of the prime sum. So $r$ is odd, $m$ is even, $k$ is even and $t$ is odd. The number $n_j$ is the rank of the $j$-th space of the upper chain; as $k$ and $t + 1$ are even, every $n_j$ is even. Put $\varrho = m/2 - 1$.

**Lemma.** The number of lifts is $m = 2\varrho + 2$.

Lean: `New.Data.m_eq_two_mul_varrho_add_two` (New/UpperBound/Objects/Columns.lean).

*Proof.* The definition is $\varrho = \lfloor m/2 \rfloor - 1$ in natural numbers. As $m$ is even and $m \ge 2$, this is $m/2 - 1$ with no truncation, and $2\varrho + 2 = m$. $\square$

The proof uses two chains of hermitian spaces over $E$.

The *upper chain* $X_0 \subset X_1 \subset \dots \subset X_m$ consists of definite spaces. The space $X_j$ has rank $n_j$, and its basis is indexed by a set `D.X j` of the form $\mathrm{InitIndex}_j \sqcup \{\ast\}$, with $\mathrm{InitIndex}_j$ of $n_j - 1$ elements. The extra index $\ast$ is the last basis vector; the lift laws modulo the level $N$ in Section 5 act on it. Each step $X_j \to X_{j+1}$ is a theta lift between definite unitary groups. At the end, a form on $X_m$ is restricted to the subspace $Y_m$ spanned by $\mathrm{InitIndex}_m$, of rank $n_m - 1$.

**Lemma.** The index set of $X_j$ has $n_j$ elements, and the index set of $Y_m$ has $n_m - 1$ elements.

Lean: `New.Data.card_X` (New/UpperBound/Objects/Columns.lean).

Lean: `New.Data.card_Y_m` (New/UpperBound/Objects/Columns.lean).

*Proof.* The set $\mathrm{InitIndex}_j$ is $\mathrm{Fin}(n_j - 1)$, and $n_j \ge 1$, so $(n_j - 1) + 1 = n_j$. The index set of $Y_m$ is in bijection with $\mathrm{InitIndex}_m$ by a chosen bijection (`New.Data.lastIndexEquiv`), so it has $n_m - 1$ elements. $\square$

The *lower chain* $Y_0 \subset Y_1 \subset \dots \subset Y_m$ consists of spaces of growing rank: $Y_0$ has rank $r$, and $Y_j$ adds $j$ blocks of size $t$. The space $Y_0$ is not definite. Its forms are the target forms, of discrete series type at infinity. The last space $Y_m$ is definite, of rank $r + mt = n_m - 1$, and it is the space at which the two chains meet. Beside the lower chain there are diagonal spaces $W_j$ of rank $r$. They carry the descent pairs $(W_j, V_j)$, which tie the parameters of the lower chain to those of the upper chain.

### The two maps

On a source form $\varphi$, a form on $X_0$ of a fixed weight and level, the two maps of the proof are:

1. the *composite lift* $B_{\vartheta, \Psi}\varphi$: the chain of $m$ theta lifts up the upper chain, taken in $\varrho + 1$ pairs, with a glued tensor of data, followed by restriction to $Y_m$ (Section 7);
2. the *lower chain* $\iota_\vartheta$ applied to the *Poincaré image* $\mathcal{P}\varphi$: first the Poincaré map $\mathcal{P}$ sends $\varphi$ to a target form on $Y_0$, the form that represents a Bessel period of $\varphi$ (Section 9); then $\iota_\vartheta$ lifts it up the lower chain to a form on $Y_m$ (Section 8).

The seesaw identity of [Theorem A and its plan](/chapter/theorem-a-plan/) says that the two forms on $Y_m$ agree, for a suitable chain datum $\Psi$. Both are algebraic forms on the definite group of $Y_m$ of the same weight $\lambda^\circ$. That they have the same weight is a fact about column counts, proved in Section 3. That their levels and characters match is proved in Sections 7 and 8.

### What each section builds

Section 2 builds the finite group $\bar G = \prod_w \mathrm{GL}_r(\mathbb{F}_w)$ over the chosen places and its central idempotent $e_0$. The good forms, the image of $e_0$, are the forms that Theorem A counts. Section 3 gives the weights of the forms on each $X_j$ and on $Y_m$ by their numbers of columns, and proves that the two weights at the top interlace. Section 4 builds the doubled Harish-Chandra parameters of the lower chain on two grids, and proves that neighbours on a grid correspond under the block rule of local theta. Section 5 proves the lift laws modulo $N$: a chain of glued double lifts is a scalar times a chain of direct lifts after a power of the operator $\mathrm{Up}$. Section 6 treats chains of theta lifts in general, jointly invariant combinations and free levels. Section 7 sets up the levels, the source forms, the restriction to $Y_m$, the kernels and the composite lift. Section 8 treats the spaces $Y_j$ and $W_j$, the descent pairs, the good forms and the lower chain. Section 9 defines the Poincaré map.

### What this chapter does not prove

This chapter proves no inequality on the dimension. It does not prove that $e_0$ is nonzero, nor that the space of good forms is nonzero; the source proves that the target forms are nonzero in a later volume, and the remark in Section 2 returns to this. It does not prove that the composite lift of a chain datum is nonzero; the remark in Section 7 explains why the definition alone does not give this. The source claims that the objects of this chapter, with the theorems of the later chapters, give Theorem A. Lean accepts the definitions and lemmas of this chapter, if the reported checks hold.

### Background that this chapter uses

The theta lifts and the seesaw are in [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). The block rule for the correspondence of discrete series parameters is in [local theta in the Fock model](/chapter/local-theta/). The idempotents of $\mathbb{C}[\mathrm{GL}_r(\mathbb{F}_q)]$ attached to labels are in [characters of GL_n over a finite field](/chapter/finite-gln/). The Weyl modules and the branching from $\mathrm{U}(n)$ to $\mathrm{U}(n-1)$ are in [integral Weyl modules and branching](/chapter/weyl-modules/). The Bessel subgroups are in [Bessel subgroups and Bruhat measures](/chapter/bessel-bruhat/), and Bessel periods in [Bessel periods and one step of unfolding](/chapter/bessel-periods/). Levels and classes are in [quotients and reduction theory](/chapter/reduction-theory/). This chapter states those results in one line with a link and does not prove them again.
