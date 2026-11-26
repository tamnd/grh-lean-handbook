---
title: The chapter and its place
lean:
  - Lib/LocalGL/Green/HallAlgebra.lean
  - Lib/LocalGL/Green/CuspidalFunctions.lean
  - Lib/LocalGL/Green/TauFunctions.lean
  - Lib/LocalGL/Green/LabelCharacters.lean
  - Lib/LocalGL/Shintani/CosetRootChoice.lean
  - Lib/LocalGL/Shintani/CosetDescent.lean
  - Lib/LocalGL/Shintani/LiftingGreenCharacters.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter constructs a family of irreducible characters of $\mathrm{GL}_n(k)$, for a finite field $k$, and proves two facts about them. The first fact is Green's theorem for the characters with a squarefree label: these class functions are irreducible characters, distinct labels give orthogonal characters, and the degree has an explicit lower bound. The second fact is Shintani's lifting for these characters, along an extension $k'/k$ of prime degree. The chapter also gives the tools that the later chapters use: central idempotents in the group algebra, the vanishing of a character on certain hyperplane sums, and the twist by a character of the determinant.

### Where the chapter sits

The argument of the source reduces the Riemann hypothesis to three theorems A, B and C (see [the plan](/chapter/theorem-and-plan/)). The finite groups $\mathrm{GL}_n(k)$ occur at the finite places, where a Hermitian lattice has a reduction modulo a prime and the source works with types: representations of the finite reductive quotient of a maximal compact subgroup. The characters of this chapter are those types. Six places in the later volumes use them.

1. [The objects of the upper bound](/chapter/upper-bound-objects/) attaches a label to each index of a type. It uses the central idempotents $e_c$ of Section 5 and the vanishing of $e_c$ on hyperplane sums.
2. [Equal multiplicities](/chapter/equal-multiplicities/) bounds the number of bad types. It uses the lower bound for the degree of $\Xi_c$, [Theorem](/decl/New.labelChar_degree_bounds/).
3. [The trace formula](/chapter/trace-formula/) uses that $\Xi_c$ is an irreducible character of $\mathrm{GL}_r(k)$, [Theorem](/decl/New.IsLabel.isIrreducibleChar_labelChar/).
4. [Building representations](/chapter/building-representations/) compares labels at a prime and at a place above it. It uses the Shintani lift, [Theorem](/decl/New.shintani_lift_labelChar/), and the lift of the determinant characters, [Proposition](/decl/New.lift_detChar/).
5. [The chain determinant](/chapter/chain-determinant/) and [the denominator bound](/chapter/denominator-bound/) use the orthogonal central idempotents of a tuple of labels.
6. [The main summands](/chapter/main-summands/) uses a count of Galois conjugates of a root of unity, [Lemma](/decl/New.injOn_Iio_pow_card_pow_of_isPrimitiveRoot/).

### The model case

Let $q = |k|$. In rank $1$ the group is $\mathrm{GL}_1(k) = k^\times$, and its irreducible characters are the $q - 1$ multiplicative characters $\chi$ of $k$. The chapter names these characters by elements of $k^\times$. Fix an embedding $T$ of the multiplicative group of an algebraic closure $K$ of $k$ into $\mathbb{C}^\times$. Each $a \in k^\times$ gives a character $\theta_a$ of $k^\times$, and $a \mapsto \theta_a$ is a bijection onto the characters of $k^\times$. The label of $\chi$ is the polynomial $X - a$ with $\theta_a = \chi$.

In rank $2$ the classical character table is in Fulton and Harris, *Representation Theory*, Section 5.2. The group $\mathrm{GL}_2(k)$ has $q^2 - 1$ irreducible characters, in four families.

- The $q - 1$ characters $\chi \circ \det$, of degree $1$.
- The $q - 1$ twists of the Steinberg character, of degree $q$.
- The $(q-1)(q-2)/2$ principal series, of degree $q + 1$. They are induced from a character $\chi_1 \otimes \chi_2$ of the upper triangular group with $\chi_1 \neq \chi_2$.
- The $(q^2 - q)/2$ cuspidal characters, of degree $q - 1$. They are attached to a character $\theta$ of $\mathbb{F}_{q^2}^\times$ with $\theta \neq \theta^q$.

Green attaches a label to each irreducible character. A label of degree $2$ is a monic polynomial of degree $2$ with a nonzero constant term, together with partitions. The principal series of $(\chi_1, \chi_2)$ has the label $(X - a_1)(X - a_2)$ with $a_1 \neq a_2$. The cuspidal character of $\theta$ has the irreducible label $(X - z)(X - z^q)$, where $z$ names $\theta$. The two remaining families share the label $(X - a)^2$, and the partitions of $2$ separate them. This chapter treats the squarefree labels only. So in rank $2$ it covers the principal series and the cuspidal characters, $(q-1)(q-2)/2 + (q^2-q)/2 = (q-1)^2$ characters. It does not cover the $2(q-1)$ characters $\chi \circ \det$ and $\mathrm{St} \otimes \chi \circ \det$ of rank $2$.

The cuspidal character of rank $2$ shows the shape of the general construction. Let $\theta$ be a character of $\mathbb{F}_{q^2}^\times$ with $\theta \neq \theta^q$. Its values are these.

| class of $g$ | value |
|---|---|
| $a \cdot 1$, $a \in k^\times$ | $(q-1)\theta(a)$ |
| $a \cdot 1 + N$, $N \neq 0$ nilpotent | $-\theta(a)$ |
| eigenvalues $a \neq b$ in $k^\times$ | $0$ |
| eigenvalues $z, z^q$ with $z \notin k$ | $-(\theta(z) + \theta(z^q))$ |

The character vanishes on the split torus. This is cuspidality: the mean of the character over the unipotent radical of the Borel subgroup is zero. The value at an elliptic element is minus a sum over the eigenvalues. Green's formula in general has the same two features. Section 4 defines a class function $C_\eta$ from a sum $\beta_\eta$ of $\eta$ over the eigenvalues, proves that it is cuspidal, and computes it at the elements of a torus. An example at the end of Section 4 recovers the table above from the general formula.

### The sketch of the proof

The proof works in one commutative ring that contains the class functions of all the groups $\mathrm{GL}_n(k)$ at once. Section 2 defines it. An element is a complex function on the similarity classes of square matrices of all sizes, invertible or not. The product is parabolic induction. Section 3 proves the two rules that make the ring useful: Mackey's formula for the mean over a unipotent radical, and the adjunction between induction and this mean. A cuspidal function then acts on the ring by a derivation.

Section 4 inverts the constant function $\mathbb{1}$ of the ring. Its inverse $\mu$ is a Möbius function of the lattice of stable subspaces, and it vanishes off the semisimple classes. Green's cuspidal function is $C_\eta = (\beta_\eta \mu) * \mathbb{1}$. The section proves that it is cuspidal, computes its values at multiplication by a field generator, and writes its inner products as means over the units of a field.

Section 5 forms $\tau_P$ for a monic irreducible $P$ from $C_\eta$, with $\eta = \theta_x$ for a root $x$ of $P$, and the products $\Xi_c = \prod_{P \mid c} \tau_P$ for squarefree $c$. The inner products of Section 4 give orthonormality. A virtual lift, constructed in Section 6 from characters induced from tori, shows that $\Xi_c$ is a $\mathbb{Z}$-combination of characters. A $\mathbb{Z}$-combination of characters of norm $1$ and of positive degree is irreducible. The section ends with the idempotents and the twist.

Section 6 proves the Shintani lift. For $k'/k$ of prime degree $\ell$ and each label $c$ over $k$, one character of $\mathrm{GL}_m(k') \rtimes \mathrm{Gal}(k'/k)$ restricts to $\Xi_c$ formed over $k'$, and on the other cosets it is $\Xi_c$ at the norm. The proof builds a virtual character with the right values and then uses a norm count modulo $\ell$ to see that it is a true character.

Section 7 has exercises and the notes. The source cites J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80 (1955), Theorems 2, 9 and 12 to 14, and T. Shintani, J. Math. Soc. Japan 28 (1976), 396 to 414. Section 7 compares the treatment with these sources and with Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter IV.

Lean accepts the results of this chapter, if the checks that the source reports hold. The chapter explains them as mathematics.
