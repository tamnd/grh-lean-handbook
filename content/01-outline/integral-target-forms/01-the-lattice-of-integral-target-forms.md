---
title: The lattice of integral target forms
lean:
  - New/Reduction/IntegralTargetForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Determinant/Chain/NormOfChain.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The lattice of integral target forms

This chapter builds the one lattice of the proof. Its vectors are the *target forms*. They form a complex vector space $T$ of finite dimension $d_T$, a space of automorphic forms on the unitary group of a hermitian space $Y_0$. The space $T$ has no evident integral structure. The chapter gives it one by transport. For each $m$-fold twist $\vartheta$ there is an injective linear map $\Theta_\vartheta$ from $T$ to algebraic forms on a definite unitary group, the chain of $m$ theta lifts with the twist $\vartheta$. Algebraic forms have a notion of integrality at each prime and a positive definite inner product with rational coordinates. A target form $y$ is called integral at a prime if its lifts $\Theta_\vartheta y$ are integral there. With these data $T$ becomes a twisted lattice in the sense of [twisted lattices](/chapter/twisted-lattices/). The source calls it the *target lattice*.

The chapter proves four facts about the target lattice.

1. The pairing of two integral lifts is integral. This holds because the stabilisers of the classes of the level are trivial.
2. The integral vectors at $\iota$ are the target forms $y$ such that $\Theta_\vartheta y$ is integral at $\iota$ for every $m$-fold twist $\vartheta$ whose modulus has norm prime to the prime of $\iota$.
3. The squared norm of $y$ at an automorphism $\sigma$ of $\mathbb{C}$ is the squared norm $\|\Theta_1 y\|_\sigma^2$ of the lift for the trivial twist, computed by a class sum.
4. The volume of the lattice at a twist $\vartheta$ is the chain determinant $Z(\vartheta) = \det(\Theta_\vartheta^* \Theta_\vartheta)$. It is a positive real number.

Then the chapter explains why the short-vector bound of Theorem A and the lower bound of Theorem C can be stated in this one lattice, and why the comparison of the two bounds is possible.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) reduces the statement of the source to a bound for a weighted prime remainder. [Twisted lattices](/chapter/twisted-lattices/) gives the abstract frame: index, covolume, heights, and the lower bound
$$c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}} \geq 0$$
of [Theorem](/decl/New.TwistedLattice.covolume_add_index_nonneg/). [Theorems A, B and C](/chapter/theorems-a-b-c/) states three theorems about one twisted lattice, and this chapter defines that lattice.

The file New/Reduction/IntegralTargetForms.lean of the source is short. The depth is in the objects that it uses, and this chapter states each of them with the properties that the lattice needs.

### What the chapter uses

- The data $D$ and their sizes from [the data and its sizes](/chapter/data-and-sizes/). The chapter uses the number $m$ of lifts, the rank $r$, the numbers $k = r + 1 - m$ and $t = 5r$, the ranks $n_j = k + j(t+1)$, the degree $f$ and the primes $p_0$, $p_1$ of the principal level. All of these are rows of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).
- The tame characters, twists and $m$-fold twists of [characters and twists](/chapter/fields-places-twists/#characters-twists-and-m-fold-twists).
- The integral vectors, index, covolume and volume of [twisted lattices](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume).
- Algebraic forms on a definite unitary group, their levels and their class sums. Volume 4 treats them in [automorphic forms](/chapter/automorphic-forms/) and [congruence subgroups](/chapter/congruence-subgroups/).
- The spaces $Y_j$, the target forms and the chain of lifts. Volume 9 constructs them in [the objects of the upper bound](/chapter/upper-bound-objects/).
- The chain determinant and its factorization. Volume 11 proves it in [the chain determinant](/chapter/chain-determinant/).

### The sketch

The integral structure lives on the forms of the last space $Y_m$ of the chain. This space is definite, so a form on it is determined by its values at representatives $g_c$ of the finitely many classes $c \in \Gamma \backslash G_f / K$. The inner product is a class sum with weights $1/\#\Gamma_{g_c}$, where $\Gamma_g = \Gamma \cap g K g^{-1}$ is the stabiliser of the class.

So everything turns on the stabilisers. The level of the last space reduces to $1$ at the chosen places above $p_0$, and by a form of Minkowski's lemma every stabiliser is trivial. Then the pairing of two integral forms is integral, and the values $\varphi(g_c)$ are coordinates with the block Gram matrix $1 \otimes G$. These are the two axioms of a twisted lattice. The volume is the chain determinant by definition, and its positivity is the injectivity of the chain, which Volume 11 proves.

### The plan of the chapter

Section 2 treats the model case: forms with scalar values on a finite set of classes. Section 3 states the target forms, the twists and the chain of lifts as objects with their properties. Section 4 builds the target lattice and proves its axioms. Section 5 identifies its volume with the chain determinant and states the factorization of the ratio $Z(\vartheta)/Z(1)$. Section 6 states Theorems A and C in the lattice and explains why one lattice carries both bounds. Section 7 has the exercises and the notes.

### Notation

The letter $\iota$ runs over the pairs of a prime $\ell$ and a field isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. We write $\iota \mid \ell$, and $\mathcal{O}_\iota$ for the valuation ring of the absolute value $|\iota(\cdot)|$ on $\mathbb{C}$. The isomorphism $\bar\iota$ is $z \mapsto \iota(\bar z)$. The letter $\sigma$ runs over the field automorphisms of $\mathbb{C}$. For a twist with modulus $Q$, $\mathrm{Nm}\,Q = \prod_{w \in Q} q_w$. The trivial twist is $1$.
