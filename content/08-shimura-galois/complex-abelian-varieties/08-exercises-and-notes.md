---
title: Exercises and notes
lean:
  - Lib/Shimura/ComplexTheta/AppellHumbertData.lean
  - Lib/Shimura/AbelianScheme/Pairings.lean
  - Lib/Shimura/Uniformisation/AppellHumbert.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $L = \mathbb{Z} + \tau\mathbb{Z}$ with $\operatorname{Im}\tau > 0$, let $(B_0, \chi_0)$ be the data of the model case of Section 2, and let $n \geq 1$. Show that the dual lattice of $L$ for the Riemann form of $n B_0$ is $\frac{1}{n} L$. Deduce from the dimension formula of Section 3 that the space of theta functions of type $(nB_0, \chi_0^n)$ has dimension $n$, and check this against the basis $\vartheta_k$ of Section 3.

*Hint.* The Riemann form of $B_0$ is $E_0(a + b\tau, c + d\tau) = \pm(ad - bc)$, depending on the convention of Section 2. A vector $u$ is in the dual lattice of $nE_0$ if $nE_0(u, l) \in \mathbb{Z}$ for all $l \in L$. The index of $L$ in $\frac{1}{n}L$ is $n^2$.

**Exercise 2.** Let $R$ be a local ring, $A$ a commutative group object over $\operatorname{Spec} R$, and $c \in \operatorname{Pic}(A)$ a class that satisfies the parallelogram law. Show that $[-1]^* c = c$. Let $E$ be an elliptic curve over a field and $p \in E$ a rational point with $2p \neq 0$. Show that the class of $\mathcal{O}(p)$ does not satisfy the parallelogram law, although $\mathcal{O}(p)$ is ample. What does this say about the hypothesis `h_par` of `New.Uniformisation.appell_humbert`?

*Hint.* Put $x = 0$ and $y = 1_A$ in the law and use $0^* c = 0$ over a local ring. On $E$, $[-1]^*\mathcal{O}(p) = \mathcal{O}(-p)$, and $\mathcal{O}(p) \cong \mathcal{O}(-p)$ would make $p$ and $-p$ linearly equivalent. The theorem of Appell and Humbert in the source applies only to symmetric classes. The embeddings in the next chapter are of this kind.

**Exercise 3.** Let $E$ be an elliptic curve over a field $k$ and $G = E \times (\mathbb{Z}/2\mathbb{Z})_k$, the product with a constant group scheme. Show that $G$ is a smooth proper commutative group scheme over $k$ whose fibre is not connected, and that multiplication by $2$ on $G$ is not surjective. So $G$ is not an abelian scheme in the sense of `New.IsAbelianScheme`, in agreement with the argument of Section 4.

*Hint.* Multiplication by $2$ kills the second factor, so its image lies in $E \times \{0\}$.

**Exercise 4.** Let $u$ be a uniformization of $A$ by $V = \mathbb{C}$ with lattice $L = \mathbb{Z} + \tau\mathbb{Z}$. Follow the proof of `New.Uniformisation.card_torsion` for $m = 6$: write down the group $F^{-1}L/L$, its order, and the determinant $\det_{\mathbb{R}} F$.

*Hint.* $F^{-1}L = \frac{1}{6}L$, and $F$ is the real map $6 \cdot 1$ on $\mathbb{R}^2$.

**Exercise 5.** Let $V = \mathbb{C}$ and $f(z) = z^2$. Show that no function $g$ analytic at $0$ satisfies $g(2z) = 4g(z) + f(z)$ near $0$. Find the form $q$ and the function $g$ of `New.exists_analyticAt_double_eq` for this $f$. Then solve $\sigma(2z) = \sigma(z)^4$ near $0$ with $\sigma(0) \neq 0$, and find all solutions.

*Hint.* Compare the coefficients of $z^2$: $4a = 4a + 1$. The source takes $g = 0$ and $q(z, z) = -z^2$. For the second part, write $\sigma = \exp(h)$ near $0$; then $h(2z) = 4h(z) + 2\pi i k$, so $h(0) = -2\pi i k/3$ and $h(z) = h(0) + a z^2$. The solutions are $\sigma(z) = \zeta \exp(a z^2)$ with $\zeta^3 = 1$. Compare $\sigma(0)^3 = 1$ in the proof of the theorem of Appell and Humbert.

**Exercise 6.** In the rigidity theorem of Section 5, let $H$ have even order. Show that the map $s \mapsto 2s$ on $H$ is not surjective, and find the step of the proof that fails. Show that the lemma `New.Variety.IsThetaStructure.pull_eq_of_intertwines` does not need $|H|$ to be odd.

*Hint.* A group of even order has an element of order $2$, so $s \mapsto 2s$ has a nontrivial kernel. The proof obtains the intertwining relation $T(X'_t) = U_t(T(X'_0))$ only for $t$ of the form $2s$.

**Exercise 7.** Let $A$ be an abelian scheme over $\operatorname{Spec} \mathbb{C}$ of relative dimension $d$, with a projective embedding. Combine the uniformization theorem of Section 6 and `New.Uniformisation.card_torsion` to show that $A(\mathbb{C})$ has exactly $m^{2d}$ points of order dividing $m$, for every $m \geq 1$. Which hypothesis of `New.IsAbelianScheme` does the proof use beyond smoothness and properness?

*Hint.* The surjectivity of the uniformization uses the divisibility condition, and the count needs surjectivity.

## Notes and references

The analytic theory of Sections 2 and 3 is classical. The theorem of Appell and Humbert, the theta functions of type $(H, \alpha)$ and the dimension formula are in Mumford, *Abelian Varieties*, Sections 1 to 3, and in Birkenhake and Lange, *Complex Abelian Varieties*, Chapters 2 and 3. Birkenhake and Lange use the form $\pi H$ and normalize the factor of automorphy differently. Section 2 compares the two conventions. The theta group and its Heisenberg representation are in Mumford, *Abelian Varieties*, Section 23, and in Birkenhake and Lange, Chapter 6. Theta structures and the equations of abelian varieties are in Mumford, "On the equations defining abelian varieties I", Invent. Math. 1 (1966).

For abelian schemes, the definition with geometrically connected fibres is in Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, Definition 6.1. The theorem of the cube and its consequences, among them $[m]^*\mathcal{L} \cong \mathcal{L}^{(m^2 + m)/2} \otimes [-1]^*\mathcal{L}^{(m^2 - m)/2}$, are in Mumford, *Abelian Varieties*, Section 6. The results on isogenies are in Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Chapter IV, and in Bosch, Lütkebohmert and Raynaud, *Néron Models*, Sections 7.3 and 8.1. The source cites these for `Lib/Shimura/AbelianScheme/IsogenyFlatness.lean`, together with the Stacks Project, Tag 0BF9. The PEL description of complex points is in Milne, *Introduction to Shimura Varieties*, Section 8, which the source cites for Theorem 8.17 and Lemma 5.12, with Kottwitz, "Points on some Shimura varieties over finite fields", J. Amer. Math. Soc. 5 (1992), Section 8. This book has not compared the citations of the source with the cited texts.

The points of the source that differ from the textbook and that this chapter records are the following.

1. `New.IsAbelianScheme` asks for surjective multiplication by every $m \neq 0$ in place of geometrically connected fibres (finding F-062, question Q-63 of the plan). Section 4 gives an argument, not checked in Lean, that the two definitions agree for commutative group schemes. The condition is used once, for the surjectivity of the uniformization.
2. The global instance `Hom.addCommGroup` and the reducible instance `ModuleObj.homModule` in `Lib/Shimura/AbelianScheme/Basic.lean` (finding F-023) affect instance search, not the meaning of the statements.
3. The theorem of the cube is not proved. The parallelogram law is a hypothesis of the results that need it and a field of the PEL data.
4. The theorem of Appell and Humbert is proved only in its existence half, for embedding bundles whose class satisfies the parallelogram law. Uniqueness of the data is not stated.
5. The form $B$ of a theta function is $\pi \bar H$ plus a complex-bilinear symmetric form, not $\pi \bar H$ alone (Section 2).
6. The uniformization is built without an analytification. The topology on $A(\mathbb{C})$ and the notion of a holomorphic family are defined by functions on points, and the connectedness of $A(\mathbb{C})$ is not proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
