---
title: The height argument
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The height argument

This chapter opens Volume 11. The volume explains the proof of Theorem C, the lower bound for the covolume of integral target forms. This chapter states Theorem C exactly, names its four inputs, and explains the one idea that joins them: a nonzero algebraic number cannot be small at every place. It then marks the places in the argument where a constant may be $0$ and the places where the source proves that a number is not $0$. The last sections give the chapters of the volume, their order, and what they take from Volumes 6, 7, 8 and 12.

### Where Theorem C sits

The source reduces the Generalized Riemann Hypothesis to a main inequality between sums over primes. [The plan](/chapter/theorem-and-plan/) describes this reduction. The main inequality comes from three theorems about one lattice of automorphic forms, the lattice of target forms. [The three theorems](/chapter/theorems-a-b-c/) states them and shows how they combine.

1. Theorem A gives many short integral target forms. For each such family it gives an upper bound for the covolume $c$ and for the index $\delta$.
2. Theorem B says that the forms of Theorem A span almost all of the target: their number $n$ satisfies $n \geq (1 - 4/b^2)\,d$, where $d$ is the dimension of the target.
3. Theorem C gives a lower bound for $c + 2\delta$ for every such family.

The upper bound and the lower bound have the same main term, $d\cdot\mathrm{mainAmount}$. The main inequality is what is left when the two bounds are compared. So Theorem C is one of the two halves of the comparison. Its error term must be as small as the error of Theorem A, up to a fixed power of $\log b$.

### The idea in one paragraph

Let $y_1, \dots, y_d$ be a basis of $\mathbb{Q}^d$ with $Q y_i \in \mathbb{Z}^d$ for an integer $Q \geq 1$. Then $Q^d \det(y_1, \dots, y_d)$ is a nonzero integer, so its absolute value is at least $1$. If each $y_i$ is short, the determinant is small by Hadamard's inequality. So a basis cannot be short and have a small denominator at the same time. In logarithms: the covolume plus twice the index is at least $0$. Theorem C is this argument for a lattice whose volume is not $1$ but a number $Z(\xi)$ that depends on a twist $\xi$, and whose integrality is tested at each prime $\ell$ by a different twist. The volume $Z(1)/Z(\xi)$ is a product of ratios of Hecke $L$-values. Its height is negative and large, about $-d\cdot\mathrm{mainAmount}$. This negative height is the main term of the lower bound.

### The sketch of the proof

The proof has one frame and four inputs. The frame is [the theorem on a twist for each prime](/decl/New.TwistedLattice.covolume_add_index_nonneg/). Let $y$ be the family of Theorem C, with covolume at most $c$ and index at most $\delta$. Complete $y$ to a basis of the target by forms $z_1, \dots, z_{n'}$. Pick for each pair $\iota$ of a prime $\ell$ and an isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ a twist $\xi_\iota$ whose modulus is prime to $\ell$. The frame then gives

$$0 \leq c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}},$$

where $b_{\mathrm{short}}$ bounds the length of the $z_i$, $b_{\mathrm{denom}}$ bounds the height of the factors that make the twisted lifts of the $z_i$ integral, and $b_{\mathrm{volume}}$ bounds the height of the volumes $Z(1)/Z(\xi_\iota)$. The four inputs supply these numbers.

1. The auxiliary forms. These are the $z_i$. They are short, and after a known scalar $\gamma(\vartheta)$ their twisted lifts are integral. They span the target, so any family extends by them to a basis.
2. The regular twists. These are the $\xi_\iota$. Their ratios of $L$-values have small height, and their denominators stay within a fixed budget. Volume 12 constructs them.
3. The chain determinant factorization. The volume $Z(\vartheta)$ of the target lattice is the determinant of a chain of $m$ theta lifts. It factors into the determinants $Z_j(\vartheta)$ of the single lifts, times a power of a scalar made of ratios of Hecke values.
4. The heights of one lift. For each single lift, a comparison operator gives a height bound for $Z_j(1)/Z_j(\xi_\iota)$ of about $-d\,k\cdot\mathrm{directionAmount}$.

The assembly adds the bounds. The $m$ single lifts give $-d\,mk\cdot\mathrm{directionAmount} = -d\cdot\mathrm{mainAmount}$. The rest are errors of size $d f a \log^4 b$. Section 3 gives the statement, and Section 4 gives the inputs.

### What the chapter uses

The reader needs the twisted lattice of target forms and the calculus of heights from Volume 1: [twisted lattices](/chapter/twisted-lattices/), [the integral target forms](/chapter/integral-target-forms/) and [the data and its sizes](/chapter/data-and-sizes/). The rest of the chapter is a map. It states results of later chapters in full, with links, but it proves only the small lemmas that join them.

### The order of the sections

Section 2 is the model case: a nonzero algebraic integer of small size at every place, and the product formula in the form that the source uses. Section 3 states Theorem C with its sizes and shows the assembly. Section 4 states the four inputs. Section 5 lists the constants that may vanish and the places where the source proves that a number is not zero. It also explains a setting of the elaborator that appears in two files of the volume. Section 6 gives the chapters of Volume 11, with a diagram of their dependencies, and the prerequisites from other volumes. Section 7 has exercises and the notes.

**Remark.** The source claims a proof of Theorem C, and Lean accepts the proof, if the reported checks hold. This chapter does not check the proof. It explains what the statements say and how the parts fit.
