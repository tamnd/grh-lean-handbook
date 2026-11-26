---
title: What the chapter proves
lean:
  - New/OneLift/FalseLifts/BottomOfTower.lean
  - New/OneLift/FalseLifts/HyperbolicPlaneStep.lean
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
decls:
  - New.Rows.stdClassSum_gramForm_eq_zero
  - New.DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate
  - New.SiegelWeil.descentsVanish_add_planes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Input 4 of [the plan of Theorem C](/chapter/theorem-c-plan/) is the comparison operator. Its property 3 says that its values are orthogonal to the false lifts. The chapter [character lifts](/chapter/character-lifts/) defines the false lifts and shows why this property matters: for forms orthogonal to the false lifts, the projection to the lifts does not increase the norms $\|\cdot\|_\sigma$. This chapter proves the key fact behind the orthogonality. A false lift has zero periods over the second block of a splitting $I_n = I_N \oplus I_l$, against theta kernels of the pair $(W, I_l)$. The forms that the comparison operator produces are sums of such periods. So they are orthogonal to the false lifts.

The proof is a tower of theta descents. It is a form of the classical principle that the first occurrence in a theta tower controls periods (Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984)). The steps are elementary in their idea, but each step needs exact control of data, levels and Hecke roots. The chapter gives all of it.

### The setting

We fix a descent pair $O$ as in [descent pairs and the vector kernel](/chapter/single-theta-lifts/#descent-pairs-and-the-vector-kernel). It has a hermitian space $W$ of rank $r$, the standard definite space $V = I_n$ with $n > r$, an embedding $\iota : r \hookrightarrow n$, a finite family $M$ of chosen places and a finite family $Q$ of twist places. All these places are split, and they and their conjugates are distinct. The residue characters $\psi_w = $ `O.tamePart w` are characters of $k_w^\times$. We write $O.\mathrm{places} = M \cup Q$ and $\Sigma$ for $O.\mathrm{places}$ together with the conjugate places. The forms in `O.FormV` are the algebraic forms on $U(I_n)$ of the weight and level of $O$. The theta descent $\theta^* = $ `O.normalizedDescent` sends them to functions on $U(W)(\mathbb{A})$. For a split place $w$ off $\Sigma$, of norm $q$, the Hecke polynomial is

$$H_w(X) = \sum_{i=0}^{n} (-X)^i q^{\binom{i}{2}} T_{w,i},$$

and the Hecke root of lifts is $x_w = $ `O.liftHeckeRoot w` $= (\alpha_w q^{n-r-1})^{-1}$, with $|\alpha_w| = q^{r/2}$. So $|x_w| = q^{1-n+r/2}$. The chapter [character lifts](/chapter/character-lifts/#hecke-polynomials-of-lifts) proves that every theta lift lies in the kernel of $H_w(x_w)$.

We say that a form $\Xi$ in `O.FormV` satisfies *the three conditions* at $w$ if:

1. the hyperplane sums annihilate $\Xi$ (`O.HyperplaneSumsAnnihilate Ξ`, Section 2): for rows $\lambda_v$ over the residue fields of the chosen places, with at least one $\lambda_v \neq 0$, the product over $v \in M$ of the sums $\sum_{s} \psi_v(\det s)^{-1} s$ over the invertible $s = 1 + u\lambda_v$ kills $\Xi$;
2. $\theta^* \Xi = 0$;
3. $H_w(x_w)\,\Xi = 0$, for one split place $w$ off $\Sigma$.

A false lift in the sense of [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms) satisfies conditions 2 and 3. Condition 1 replaces the condition $\Xi \in \mathrm{range}(e_0)$. In rank $r = 1$, Section 8 shows that $\Xi \in \mathrm{range}(e_0)$ implies condition 1.

### The main theorem

**Theorem (Periods of false lifts vanish).** Let $O$ fit the archimedean parameter $l_0$ on $W$ (`O.FitsParams l₀`), and let $\psi_w \neq 1$ for every twist place $w \in Q$. Let $\Xi$ satisfy the three conditions at a split place $w$ off $\Sigma$. Let $\varepsilon : N \sqcup l \simeq n$ split $I_n = I_N \oplus I_l$, and assume

$$2r + 2\,\#N + 3 < n.$$

Let $x \in U(I_n)(\mathbb{A}_f)$ be supported on $O.\mathrm{places}$, and let $h_1 \in U(I_N)(\mathbb{A}_f)$. Let $\vartheta$ be a function on $U(I_l)(\mathbb{A}_f)$ with values in a Weyl module of weight $\kappa$, such that each coordinate of $\vartheta$, moved by the real points, is a constant multiple of a conjugate theta kernel of the pair $(W, I_l)$ whose datum is the vacuum off $\Sigma$. Let $C$ be a conjugate linear map from the Weyl module of weight $\kappa$ to the values of $\Xi$ that is equivariant for the real points of $U(I_l)$. Put

$$f(h) = \langle C(\vartheta(h)), \Xi(\mathrm{diag}(h_1, h)\,x)\rangle.$$

Then $f$ is left invariant under the rational points of $U(I_l)$, and $\mathrm{classSum}_K f = 0$ for every level $K$ that fixes $f$ on the right.

Lean: `New.Rows.stdClassSum_gramForm_eq_zero` (New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean).

The proof is in [Section 7](/chapter/false-lifts/#periods-of-false-lifts). The class sum is the finite form of the integral over $[U(I_l)]$; see [class sums and Petersson products](/chapter/character-lifts/#class-sums-and-petersson-products).

**Remark (Formalization).** The rank condition $2r + 2\#N + 3 < n$ is an explicit hypothesis `h_rank` on the cardinalities of the index types. It is not part of `FitsParams`. The register of findings lists it as F-087. The later chapters must supply it when they apply the theorem.

### The plan of the proof

The proof has four steps.

1. *The bottom of the tower* (Sections 2 to 4). From conditions 1 and 2 we get that all descents of the matrix coefficients of $\Xi$ to $U(W)$ vanish, for all data that are the vacuum off $\Sigma$. Condition 2 gives this only for one datum, the block datum $\Psi_{\mathrm{bl}} \otimes \mathrm{vac}$. The hyperplane sums move the vanishing from this datum to all data. The tool is a lemma on matrices: a point $z$ without an "integral block ratio" has an annihilating row, and the row gives a shear that fixes the class of $z$.

**Theorem (The bottom of the tower).** Let $\psi_w \neq 1$ for $w \in Q$, and let the hyperplane sums annihilate the form $y$. If the descents of $\overline{\langle u, y\rangle}$ by the data $v_P \otimes \Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ vanish for all polynomials $P$, then all descents of $\overline{\langle u, y\rangle}$ to $U(W)$, twisted by $\nu_W$ and with data that are the vacuum off $\Sigma$, vanish.

Lean: `New.DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate` (New/OneLift/FalseLifts/BottomOfTower.lean).

2. *Small roots* (Section 5). A bounded function on a unitary group of rank $m$ that is spherical at $w$ and killed by $H_w(X)$ with $q^{m+1}|X| \leq 1$ is zero. The proof uses the $q$-binomial theorem and the maximum principle of Volume 6.

3. *The hyperbolic plane step* (Section 6). If the descents of $Y$ to $W$ vanish, then the descents to $W$ plus one hyperbolic plane are bounded. The Hecke transfer moves condition 3 to these descents at a point of small modulus. So by step 2 they are zero. Induction on the number of planes gives the following theorem.

**Theorem (The tower).** Let the descents of $Y$ to $W$ twisted by $a$ vanish for data that are the vacuum off $\Sigma$. Let $w$ be split off $\Sigma$, with $a$ unramified at $\bar w$, let $Y$ be spherical at $w$ and killed by $H_w(X)$, with $|X| = (q^{r/2} q^{n-r-1})^{-1}$. If $W'$ is $W$ plus $p$ hyperbolic planes and $2r + 2p + 3 < n$, then the descents of $Y$ to $W'$ twisted by $a\,\upsilon^{p}$ vanish.

Lean: `New.SiegelWeil.descentsVanish_add_planes` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

4. *Periods* (Sections 7 and 8). The descents to $W \oplus \mathbb{H}^N$ vanish (`New.Rows.descentsVanish_hyperbolicSum`). A theta kernel of $W$ is absorbed in the matrix coefficient. Then the theorem of [descents and periods](/chapter/bessel-periods/#descents-and-block-periods) turns vanishing descents to the hyperbolic space $\mathbb{H}^N$ into vanishing periods over $U(I_l)$.

### What the chapter uses

From Volume 6: the Weil representation and its data ([the Weil representation](/chapter/weil-representation/)), the zero terms along an isotropic frame ([Siegel-Weil](/chapter/siegel-weil/)), the Hecke transfer and the maximum principle ([a maximum principle at a split place](/chapter/siegel-weil/#a-maximum-principle-at-a-split-place)), and the vanishing of block periods ([Bessel periods](/chapter/bessel-periods/)). From Volume 9: the descent pair, the block datum, the level group and the hyperplane sums ([the objects of the upper bound](/chapter/upper-bound-objects/)). From this volume: the descent and its harmonic datum ([single theta lifts](/chapter/single-theta-lifts/)), point forms ([character lifts](/chapter/character-lifts/)), and divided lattices and product forms ([the comparison operator, part 1](/chapter/comparison-operator-1/)).

### Where the results are used

Section 8 gives three special cases. The case of point forms (`New.Rows.stdClassSum_period_eq_zero`) and the case of a line (`New.Rows.stdClassSum_gramForm_eq_zero_of_rank_one`) are used in [Hecke values of character lifts](/chapter/hecke-values/). The case of product forms (`New.Rows.DividedSplitting.stdClassSum_inner_productForm_eq_zero`) is used in [the comparison operator, part 2](/chapter/comparison-operator-2/), where it gives property 3 of the comparison operator: its values are orthogonal to the false lifts.
