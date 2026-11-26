---
title: The terms of a block
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Unfolding/Terms.lean
  - New/Spanning/Unfolding/BesselLevelStructure.lean
decls:
  - New.Filling.Classes
  - New.Filling.classRep
  - New.Filling.latticeStabilizer
  - New.Filling.principalLevel
  - New.Filling.reducedImage
  - New.Filling.translateByClassReps
  - New.Filling.termsOver
  - New.Filling.termsOver.mul
  - New.Filling.termsOver.inv
  - New.Filling.classUnipotent
  - New.Filling.classUnipotent₀
  - New.Filling.frameProducts
  - New.Filling.termDisc
  - New.Filling.form_frameImage_mulVec
  - New.Filling.norm_sq_middle_part_eq
  - New.Filling.map_termDisc_eq_norm
  - New.Filling.termDisc_pos_or_eq_zero
  - New.Filling.frameGram_translateByClassReps
  - New.Filling.isIntegral_frameProducts
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The terms of a block

A block of the unfolded sum is a triple $(c, s, c')$ of two classes and one element of a finite group. This section defines the terms over a block. It then attaches to each term the matrix of frame products and its discriminant, and it proves the first fact about the discriminant: it is totally nonnegative.

### Classes, levels and blocks

The finite adelic group $G(\mathbb{A}_f)$ acts on the lattices of $V$. The source writes its elements in a basis of the standard lattice $\Lambda_0$ (`latticeBasis`), so that the integral elements are the matrices over $\hat{\mathcal{O}}_E$.

**Definition (Classes).** The set of classes is the set of double cosets $U(X_0)(E) \backslash U(X_0)(\mathbb{A}_f) / L$, where $L$ is the source level `sourceLevel` of the data. For a class $c$, its representative $h_c$ is the image in $G(\mathbb{A}_f)$ of a chosen element of the double coset.

Lean: `New.Filling.Classes` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.classRep` (New/Spanning/Unfolding/Setup.lean).

**Remark (Formalization).** The representative is `c.out`, an element chosen by the axiom of choice. All statements of this chapter hold for any choice. The terms over a block depend on the choice, but the sets for two choices differ by a translation, and the bounds of layer 4 do not see it.

**Definition (Integral elements, the principal level and reduced images).** The group $K$ is the subgroup of $G(\mathbb{A}_f)$ of the matrices that are invertible over $\hat{\mathcal{O}}_E$. The reduction $K \to \bar G$ reduces the entries modulo each chosen place above $p_0$ and $p_1$. Here $\bar G = \prod_{i \in \{0, 1\}} \prod_{w} \mathrm{GL}_V(k_w)$, with $w$ over the chosen places above $p_i$ and $k_w$ the residue field at $w$. The principal level $K(M)$ is the kernel of the reduction. For a subgroup $A$ of $G(\mathbb{A}_f)$, its reduced image is the image of $A \cap K$ in $\bar G$.

Lean: `New.Filling.latticeStabilizer` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.principalLevel` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.reducedImage` (New/Spanning/Unfolding/Setup.lean).

**Definition (Terms over a block).** For classes $c, c'$ and a rational $\gamma \in G(E)$, put $\gamma_{c,c'} = h_c^{-1}\gamma h_{c'} \in G(\mathbb{A}_f)$. The terms over $(c, s, c')$ are the rational $\gamma$ such that $\gamma_{c,c'}$ lies in $K$ and has the reduction $s$.

Lean: `New.Filling.translateByClassReps` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.termsOver` (New/Spanning/Unfolding/Setup.lean).

The terms form a groupoid. The next lemma is the composition law.

**Lemma (Products and inverses of terms).** If $\gamma$ is a term over $(c, s, c')$ and $\delta$ is a term over $(c', t, c'')$, then $\gamma\delta$ is a term over $(c, st, c'')$. The inverse $\gamma^{-1}$ is a term over $(c', s^{-1}, c)$.

Lean: `New.Filling.termsOver.mul` (New/Spanning/Unfolding/BesselLevelStructure.lean). Lean: `New.Filling.termsOver.inv` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* We have $(\gamma\delta)_{c,c''} = \gamma_{c,c'}\delta_{c',c''}$, and $(\gamma^{-1})_{c',c} = (\gamma_{c,c'})^{-1}$. The group $K$ is closed under products and inverses, and the reduction is a homomorphism. $\square$

**Definition (The unipotent groups of a class).** For a class $c$, the group $\mathsf{U}_c(M)$ is the group of the rational $u \in \mathsf{U}$ with $h_c^{-1}uh_c \in K(M)$. The group $\mathsf{U}^0_c(M)$ is its subgroup of the elements of $\mathsf{U}^0$, the elements that fix every vector of the frame.

Lean: `New.Filling.classUnipotent` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.classUnipotent₀` (New/Spanning/Unfolding/Setup.lean).

The groups $\mathsf{U}$ and $\mathsf{U}^0$ are defined in [the chapter on Bessel subgroups](/chapter/bessel-bruhat/): $\mathsf{U}$ is [the group](/decl/New.Shape.Form.besselU/) of the isometries that are unitriangular for the level, and $\mathsf{U}^0$ is [its subgroup](/decl/New.Shape.Form.besselU0/) that fixes $e_0, \dots, e_{\varrho-1}$ and $z$.

### The frame products and the discriminant

Write $\gamma\mathfrak{f}$ for the columns $\gamma\mathfrak{f}_0, \dots, \gamma\mathfrak{f}_\varrho$ of $\gamma$ at the frame vectors (`frameImage`). For $y \in E^{\varrho+1}$ write $\gamma\mathfrak{f}\cdot y = \sum_b y_b\,\gamma\mathfrak{f}_b$.

**Definition (Frame products).** For a rational $\gamma$, the matrix $Z(\gamma)$ of size $\varrho + 1$ has the entries $Z(\gamma)_{ab} = h(\mathfrak{f}_a, \gamma\mathfrak{f}_b)$ for $0 \leq a, b \leq \varrho$.

Lean: `New.Filling.frameProducts` (New/Spanning/Unfolding/Setup.lean).

For $0 \leq l \leq \varrho + 1$ let $D_l = D_l(\gamma)$ be the leading principal minor of order $l$ of $Z(\gamma)$, the determinant of the block of the first $l$ rows and columns. So $D_0 = 1$ and $D_{\varrho+1} = \det Z(\gamma)$. For $x \in E$ write $|x|^2 = x\bar{x}$, an element of the totally real subfield $E^+$.

**Definition (Term discriminant).** The discriminant of $\gamma$ is $\mathsf{g}(\gamma) = |D_{\varrho+1}|^2 - N^2|D_\varrho|^2 \in E$.

Lean: `New.Filling.termDisc` (New/Spanning/Unfolding/Setup.lean).

**Remark (Formalization).** The source defines $\mathsf{g}(\gamma)$ as `frameDisc N (frameProducts γ)`. The function [frameDisc](/decl/New.frameDisc/) of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/) takes any square matrix $Z$ of size $\varrho + 1$ over a ring with an involution and returns $\det Z \cdot \overline{\det Z} - N^2 D_\varrho\overline{D_\varrho}$. So $|x|^2$ is the algebraic norm $x\bar{x}$, not a real absolute value. Its images under the embeddings are real absolute values.

Let $\Phi_v : E \to \mathbb{C}$ be the chosen embedding at the infinite place $v$. The next lemma is the reason why $\mathsf{g}$ has a sign.

**Lemma (Isometries preserve the form on the frame span).** For every $y$, $h(\gamma\mathfrak{f}\cdot y, \gamma\mathfrak{f}\cdot y) = h(\mathfrak{f}\cdot y, \mathfrak{f}\cdot y) = -N|y_\varrho|^2$.

Lean: `New.Filling.form_frameImage_mulVec` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The first equality holds because $\gamma$ is an isometry and $\gamma\mathfrak{f}\cdot y = \gamma(\mathfrak{f}\cdot y)$. The Lean statement is this equality. For the second, the vectors $e_0, \dots, e_{\varrho-1}$ are isotropic, orthogonal to each other and orthogonal to $z$. So only the term $|y_\varrho|^2 h(z, z) = -N|y_\varrho|^2$ remains. $\square$

**Lemma (The norm identity).** Let $\gamma$ be rational, $D \in E$ and $y \in E^{\varrho+1}$ with $Z(\gamma)y = (0, \dots, 0, D)$. Put $t = \gamma\mathfrak{f}\cdot y$, and write $t_0 = \sum_i t_{x_i}x_i$ for its $X_0$-part. Then:

1. the coordinates $t_{e^*_a}$ vanish for $0 \leq a < \varrho$;
2. $-Nt_z = D$;
3. at each infinite place $v$, $N\sum_{i=1}^{k}|\Phi_v(t_{x_i})|^2 = |\Phi_v(D)|^2 - N^2|\Phi_v(y_\varrho)|^2$;
4. if the left side of 3 is at most $0$ at some $v$, then $t = \mathfrak{f}\cdot x$ for some $x \in E^{\varrho+1}$.

Lean: `New.Filling.norm_sq_middle_part_eq` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The entry $a$ of $Z(\gamma)y$ is $h(\mathfrak{f}_a, t)$. For $a < \varrho$, $h(e_a, t) = t_{e^*_a}$, since $e_a$ pairs only with $e^*_a$. This entry is $0$, which gives 1. The last entry is $h(z, t) = -Nt_z = D$, which gives 2.

For 3, expand $h(t, t)$ in the basis. The hyperbolic part is $\sum_a (\overline{t_{e_a}}t_{e^*_a} + \overline{t_{e^*_a}}t_{e_a})$, and it vanishes by 1. So $h(t, t) = \sum_i |t_{x_i}|^2 - N|t_z|^2$. By the previous lemma, $h(t, t) = -N|y_\varrho|^2$. Apply $\Phi_v$. Since $E$ is a CM field, $\Phi_v(\bar{x}) = \overline{\Phi_v(x)}$, so $\Phi_v(|x|^2) = |\Phi_v(x)|^2$. Multiply by $N$ and use $N|\Phi_v(t_z)| = |\Phi_v(D)|$ from 2:

$$N\sum_i |\Phi_v(t_{x_i})|^2 = N^2|\Phi_v(t_z)|^2 - N^2|\Phi_v(y_\varrho)|^2 = |\Phi_v(D)|^2 - N^2|\Phi_v(y_\varrho)|^2.$$

For 4, a sum of squares that is at most $0$ vanishes term by term. So $t_{x_i} = 0$ for all $i$. With 1, the vector $t$ has only coordinates along $e_0, \dots, e_{\varrho-1}$ and $z$. So $t = \mathfrak{f}\cdot x$ with $x_a = t_{\mathfrak{f}_a}$. $\square$

The identity says that the $X_0$-part of $t$ measures how far $D$ is from the value $\pm Ny_\varrho$ that a vector of the frame span would give. Cramer's rule gives a canonical choice of $y$.

**Lemma (The discriminant is real and nonnegative).** For every rational $\gamma$ and every infinite place $v$, $\Phi_v(\mathsf{g}(\gamma)) = |\Phi_v(\mathsf{g}(\gamma))|$. That is, $\Phi_v(\mathsf{g}(\gamma))$ is a real number at least $0$.

Lean: `New.Filling.map_termDisc_eq_norm` (New/Spanning/Unfolding/Terms.lean).

*Proof.* Let $y$ be the last column of the adjugate of $Z = Z(\gamma)$. Since $Z\operatorname{adj}(Z) = \det Z \cdot 1$, this is Cramer's rule $Zy = (0, \dots, 0, \det Z)$. The entry $y_\varrho$ is the cofactor of the entry $(\varrho, \varrho)$ of $Z$, which is $D_\varrho$. Apply the norm identity with $D = \det Z$. Part 3 gives

$$0 \leq N\sum_i |\Phi_v(t_{x_i})|^2 = |\Phi_v(D_{\varrho+1})|^2 - N^2|\Phi_v(D_\varrho)|^2 = \Phi_v(\mathsf{g}(\gamma)).$$

So $\Phi_v(\mathsf{g}(\gamma))$ is a nonnegative real number, and it is equal to its absolute value. $\square$

**Theorem (The discriminant is totally positive or zero).** For every rational $\gamma$, one of two cases holds. Either $\Phi_v(\mathsf{g}(\gamma)) > 0$ for every infinite place $v$ and $\det Z(\gamma) \neq 0$, or $\mathsf{g}(\gamma) = 0$.

Lean: `New.Filling.termDisc_pos_or_eq_zero` (New/Spanning/Unfolding/Terms.lean).

*Proof.* Suppose $\mathsf{g}(\gamma) \neq 0$. Each $\Phi_v$ is injective, so $\Phi_v(\mathsf{g}(\gamma)) \neq 0$. By the previous lemma it is real and nonnegative, so it is positive. Suppose next that $\det Z(\gamma) = 0$. Then $\mathsf{g}(\gamma) = -N^2|D_\varrho|^2$, and at one place $v$ this gives $\Phi_v(\mathsf{g}(\gamma)) = -N^2|\Phi_v(D_\varrho)|^2 \leq 0$. With $\Phi_v(\mathsf{g}(\gamma)) \geq 0$ this gives $\Phi_v(\mathsf{g}(\gamma)) = 0$, so $\mathsf{g}(\gamma) = 0$, a contradiction. So $\det Z(\gamma) \neq 0$. $\square$

In the source the second half of the proof goes through [Lemma](/decl/New.Filling.hasCellRank_last/) of [the section on cells](/chapter/anatomy-of-a-term/#cells-and-the-discriminant). The argument there is the one above.

**Example.** Take $\gamma = 1$. Then $Z(1)$ is the diagonal matrix with entries $h(e_a, e_a) = 0$ for $a < \varrho$ and $h(z, z) = -N$. So $D_{\varrho+1} = 0$, $D_\varrho = 0$ (for $\varrho \geq 1$) and $\mathsf{g}(1) = 0$. This agrees with the theorem: the frame and its image are the same. On the big cell the discriminant is $|d|^2(|t|^2 - N^2)$, by [Theorem](/decl/New.Filling.frameDisc_weylElem_mul/) of the section on cells.

### Integrality of the frame products

The frame products of a term over a block are algebraic integers. The proof writes $Z(\gamma)$ in the lattice basis.

**Lemma (The frame products in the lattice basis).** For classes $c, c'$ and a rational $\gamma$, the Gram matrix of the frame of $\gamma_{c,c'}$ for the lattice form is the image of $Z(\gamma)$ in the finite adeles.

Lean: `New.Filling.frameGram_translateByClassReps` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The element $h_c$ lies in the image of $U(X_0)(\mathbb{A}_f)$, so it fixes $e_0, \dots, e_{\varrho-1}$ and $z$, and so does the change of basis to the lattice basis on these vectors. So the frame image of $\gamma_{c,c'}$ is the frame image of $\gamma$, written in the coordinates of the lattice $h_c\Lambda_0$. The matrix of this change of coordinates carries the rational form to the lattice form. So the products are unchanged. $\square$

**Lemma (Frame products are integral).** Let $S$ be admissible and let $\gamma$ be a term over $(c, s, c')$. Then each entry $Z(\gamma)_{ab}$ is an algebraic integer.

Lean: `New.Filling.isIntegral_frameProducts` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The matrix of $\gamma_{c,c'}$ is integral, since $\gamma_{c,c'} \in K$. The lattice form is unimodular, so its Gram matrix is integral. The entry $(a, b)$ of the Gram matrix of the frame of $\gamma_{c,c'}$ is a product of these integral matrices, so it lies in $\hat{\mathcal{O}}_E$. By the previous lemma it is the image of $Z(\gamma)_{ab}$. An element of $E$ that is integral at every finite place is an algebraic integer. $\square$

So $D_l(\gamma)$ and $\mathsf{g}(\gamma)$ are algebraic integers too. With the theorem above, a term with $\mathsf{g}(\gamma) \neq 0$ has a totally positive integral discriminant. Its norm $\prod_v \Phi_v(\mathsf{g}(\gamma))$ is then a positive integer, hence at least $1$. This is the reason why the bounds of [the section on the box](/chapter/anatomy-of-a-term/#the-box-and-the-size-of-a-near-term) carry the hypothesis $1 \leq \prod_v |\Phi_v(\mathsf{g}(\gamma))|$.
