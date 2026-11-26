---
title: The data, the kernel and the lift
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
decls:
  - New.nonempty_unit_embedding
  - New.arbitraryIndexEmbedding
  - New.LValueData
  - New.LValueData.descentPair
  - New.LValueData.descentPair_colsPlus_apply
  - New.LValueData.kernelValue
  - New.LValueData.isLiftWeight
  - New.LValueData.charW_hasWeight
  - New.LValueData.charV_hasWeight
  - New.LValueData.liftKernel
  - New.LValueData.conjWeylRep_eq_one
  - New.LValueData.kernelForm
  - New.LValueData.chosenLevel
  - New.LValueData.trivialLift
  - New.LValueData.kernelForm_invariant
  - New.LValueData.trivialLift_eq_stdClassSum_translate
  - New.LValueData.kernelForm_of_rowLength_eq_zero
  - New.LValueData.hookNumber_eq_prod_factorial
  - New.LValueData.schurJet_jetSeries_eq_kernelForm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The data, the kernel and the lift

This section fixes the data of a lift from $U(1)$, builds the descent pair with a line as source, and defines the kernel and the lift. The main results are that the kernel is invariant on both sides, and that the lift does not change if the kernel is translated by a point of $U(1)$.

### The data

**Definition (Data for a lift from U(1)).** Let $n$ be a finite index set with $N = \#n > 1$. Data $X$ for a lift from $U(1)$ to the definite group of rank $N$ consist of:

- level places (`LevelPlaces E`): a finite family of chosen places $M$ and a finite family of twist places $Q$;
- a row length $\ell_\tau \in \mathbb{N}$ at each infinite place $\tau$;
- an automorphic character $\mu$ of $U(1)$ (`u1Char`) with tame parts $\psi_w$, characters of the residue fields $k_w^\times$;
- the condition that $\mu$ has weight $-(\ell_\tau + \lfloor N/2\rfloor)$ at $\tau$ and tame part $\psi$;
- the condition $1 < N$;
- the condition $\psi_w = 1$ for every finite place $w$ outside $M \cup Q$.

Lean: `New.LValueData` (New/OneLift/HeckeValues/CharacterLift.lean).

The row length $\ell_\tau$ is the number of derivatives taken at $\tau$. The shift by $\lfloor N/2\rfloor$ in the weight compensates the splitting character of the Weil representation, which has weight $\lfloor N/2 \rfloor$ in rank $N$. The background on automorphic characters and their weights is in [the Weil representation](/chapter/weil-representation/) of Volume 6.

**Lemma (An index).** Every non-empty type has an element, so it receives an embedding of the one point type. `arbitraryIndexEmbedding` is such an embedding into $n$, chosen once.

Lean: `New.nonempty_unit_embedding` (New/OneLift/HeckeValues/CharacterLift.lean), `New.arbitraryIndexEmbedding` (New/OneLift/HeckeValues/CharacterLift.lean).

**Remark (Formalization).** The embedding is `Nonempty.some`, so it is a choice. The block datum at the chosen places asks the reduction of the matrix to be the basis vector $e_{i_0}$ for this index $i_0 \in n$. The proofs of the chapter use no property of $i_0$.

### The descent pair of a line

**Definition (Descent pair of the data).** The descent pair `X.descentPair` has source the standard definite line $W$ (index type `Unit`), target $V$ of rank $N$, the level places of $X$, signs $1$, the embedding $i_0$ of the line, numbering $0$, the character $\mu$ with its weight and tame part, and the weight with $\ell_\tau$ columns of height $1$ at $\tau$ (`colsPlus τ = Pi.single 1 ℓ_τ`) and no negative columns (`colsMinus = 0`).

Lean: `New.LValueData.descentPair` (New/OneLift/HeckeValues/CharacterLift.lean).

So the weight $\kappa$ on $V$ is the partition with one row of length $\ell_\tau$ at $\tau$. The descent pairs of any rank are in [single theta lifts and their norms](/chapter/single-theta-lifts/).

**Lemma (The columns).** `X.descentPair.colsPlus τ k` is $\ell_\tau$ if $k = 1$ and $0$ otherwise.

Lean: `New.LValueData.descentPair_colsPlus_apply` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* This is the value of `Pi.single 1 ℓ_τ` at $k$. $\square$

**Lemma (Lift weight).** The weight $\kappa$ with determinant exponent $0$ in rank $1$ goes up to rank $N$ along the exponent $-\ell_\tau$ (`IsLiftWeight Unit n κ (-ℓ ·) 0`).

Lean: `New.LValueData.isLiftWeight` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* There are three conditions. The weight has no column of height strictly between $1$ and $N$: all columns have height $1$. The ranks satisfy $1 < N$. The difference of the exponents is the number of columns of height $1$, which is $\ell_\tau$. Each condition is a direct computation with `mixedWeight`. $\square$

**Lemma (Weights of the characters).** The character $\nu_W = $ `charW` has weight `detExp` and trivial tame part. The character $\nu_V = $ `charV` $= \mu\cdot\upsilon^{\lfloor N/2\rfloor}$ has weight $-\ell_\tau$ and tame part $\psi$.

Lean: `New.LValueData.charW_hasWeight` (New/OneLift/HeckeValues/CharacterLift.lean), `New.LValueData.charV_hasWeight` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The source is definite and the weight has no negative columns, so `charW` is the power $0$ of the splitting character $\upsilon$, and both exponents are $0$. The twist of $\mu$ by $\upsilon^{\lfloor N/2\rfloor}$ moves the weight from $-(\ell_\tau + \lfloor N/2\rfloor)$ to $-\ell_\tau$ and keeps the tame part (`hasWeight_rankTwist`). $\square$

**Definition (Lift kernel).** `X.liftKernel` is the theta kernel `thetaKernel` between the standard spaces of ranks $1$ and $N$, for the lift weight, the scale $1$ and the two characters above. It is a family of operators $\omega(g, h)$ of the finite points of $U(1) \times U(N)$ on Schwartz functions of $\mathrm{Hom}(W, V)(\mathbb{A}_f)$, with a jet map to vectors of the weight.

Lean: `New.LValueData.liftKernel` (New/OneLift/HeckeValues/CharacterLift.lean).

**Lemma (The line acts trivially on its weight).** For every point $x$ of the archimedean group of the line, `conjWeylRep κ 0 x = 1`.

Lean: `New.LValueData.conjWeylRep_eq_one` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* In rank $1$ the Schur matrix of the weight is a $1 \times 1$ matrix of a power of the determinant, with exponent $0$. So it is $1$ (`schur_eq_one`). $\square$

### The kernel and the lift

Let $f_0 = $ `X.descentPair.blockDatum` be the block datum: at the places of $M \cup Q$ it is the function of the residues described in the previous chapter, and at all other finite places it is the characteristic function of the integral matrices. For $c \in \mathbb{C}$ and $g \in U(1)(\mathbb{A}_f)$, $h \in G_f$ put

$$\kappa_c(f)(g, h) = S_\kappa\big(\mathrm{jet}_c\, \theta(\omega(g, h) f)\big)\cdot \mathbf{1},$$

where $\mathrm{jet}_c$ is the Taylor series of the theta function in the scaled variable and $S_\kappa$ applies the entries of the Schur matrix of $\kappa$ as differential operators at $0$. The product with the vector $\mathbf{1}$ takes the row sums. This is `X.kernelValue c f g h`, a vector indexed by `WeylIndexFamily`.

Lean: `New.LValueData.kernelValue` (New/OneLift/HeckeValues/CharacterLift.lean).

**Definition (Kernel form).** For $g \in U(1)(\mathbb{A}_f)$, the kernel form $\theta_X(g)$ is the function $h \mapsto \kappa_1(f_0)(g, h)$, as an element of `X.descentPair.FormV`.

Lean: `New.LValueData.kernelForm` (New/OneLift/HeckeValues/CharacterLift.lean).

The definition contains two proofs. First, the level $K$ of the descent pair acts by its character: for $k \in K$, $\omega(1, k) f_0 = \chi_O(\bar k) f_0$ by the law `omega_blockDatum_eq_smul` of the block datum, and the jets are linear in the datum. So the function is smooth and has the right level character. Second, it is equivariant under the rational points of $V$, by the equivariance of the theta kernel (`Kernel.equivariant`): the theta functional is invariant under the rational points of $U(1) \times U(N)$.

**Definition (Chosen level).** `X.chosenLevel` is the subgroup of $U(1)(\mathbb{A}_f)$ of integral points that reduce to $1$ at every chosen place: `levelOf X.chosenPlace ⊥`.

Lean: `New.LValueData.chosenLevel` (New/OneLift/HeckeValues/CharacterLift.lean).

**Definition (Lift of the character).** The lift of the character of $X$ is the class sum

$$\varphi_X = \sum_{[g] \in U(1)(E)\backslash U(1)(\mathbb{A}_f)/K_M} \frac{1}{\#\big(U(1)(E) \cap g K_M g^{-1}\big)}\, \theta_X(g),$$

with $K_M$ the chosen level.

Lean: `New.LValueData.trivialLift` (New/OneLift/HeckeValues/CharacterLift.lean).

The class sum is a finite sum, since $U(1)(E)\backslash U(1)(\mathbb{A}_f)/K_M$ is finite. The weights $1/\#\mathrm{Aut}$ come from the Haar measure. Section 4 shows that $\varphi_X$ is a multiple of the theta lift of the constant function $1$.

**Lemma (Invariance of the kernel).** The function $g \mapsto \theta_X(g)$ is invariant on the left under the rational points of $U(1)$, and on the right under the chosen level.

Lean: `New.LValueData.kernelForm_invariant` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Left invariance. For $\gamma \in U(1)(E)$ the equivariance of the theta kernel gives $\theta(\omega(\gamma g, h) f) = $ the value at $(g, h)$ moved by $\gamma$ on the weight of the line. The line acts trivially on its weight, so the two values are equal.

Right invariance. Let $k$ be in the chosen level, so its reduction at each chosen place is $1$. By `omega_blockDatum_eq_smul` at the point $(k, 1)$, $\omega(k, 1) f_0$ is $f_0$ times a character of the reduction of $k$, and at the reduction $1$ this character is $1$. So $\omega(k, 1) f_0 = f_0$ and $\theta_X(gk) = \theta_X(g)$. $\square$

**Lemma (Translation).** For every $z \in U(1)(\mathbb{A}_f)$,

$$\varphi_X = \sum_{[g]} \frac{1}{\#\mathrm{Aut}(g)}\, \theta_X(gz),$$

the class sum over the same double cosets.

Lean: `New.LValueData.trivialLift_eq_stdClassSum_translate` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The kernel is invariant on both sides, so its value at a representative of a class is its value at any point of the class (`apply_doubleCoset_out`). The group $U(1)(\mathbb{A}_f)$ is commutative, so conjugation by $z$ fixes the chosen level. The law of translated class sums (`classSum_eq_relIndex_smul`, in [automorphic forms on definite unitary groups](/chapter/automorphic-forms/)) then says that the class sum of $g \mapsto \theta_X(gz)$ is $[K_M : K_M]$ times the class sum of $\theta_X$. The index of a group in itself is $1$. $\square$

### Three computations

**Lemma (Scale of the jets).** For every $c \in \mathbb{C}$, $g$, $h$ and index $i$,

$$\big(S_\kappa\, \mathrm{jet}_c\,\theta(\omega(g, h) f_0)\cdot\mathbf{1}\big)_i = c^{\sum_\tau \ell_\tau}\, \theta_X(g)(h)_i.$$

Lean: `New.LValueData.schurJet_jetSeries_eq_kernelForm` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The entries of the Schur matrix are homogeneous of degree the number of boxes of the weight in rank $N$ (`schurJet_jetSeries_eq_smul`). The weight has $\ell_\tau$ boxes at $\tau$, so the degree is $\sum_\tau \ell_\tau$. A homogeneous operator of degree $d$ applied to the series in $cZ$ gives $c^d$ times its value on the series in $Z$. $\square$

Section 7 uses this lemma with $c$ a scale that a Galois automorphism introduces.

**Lemma (Hook number).** The hook number of the weight $\kappa$ in rank $N$ at every place is $\prod_\tau \ell_\tau!$.

Lean: `New.LValueData.hookNumber_eq_prod_factorial` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The weight has one row of length $\ell_\tau$ at $\tau$. For a one row weight the hook number is the factorial of the row length (`hookNumber_one_row`, which needs $1 < N$). $\square$

**Lemma (Kernel with no derivatives).** If all row lengths are $0$, then every coordinate of $\theta_X(g)(h)$ is the scalar theta kernel

$$\mathrm{modKernel}(W, V, 1, \nu_V, \mathfrak{m}, \Psi, 1)\big((1, g), (1, h)\big),$$

with $\mathfrak{m} = $ `X.levelModulus 2`, the square of the product of the chosen places times the product of the twist places, and $\Psi$ the function of matrices modulo $\mathfrak{m}$ that reduces at each place of $M \cup Q$ and applies `residueBlockDatum`.

Lean: `New.LValueData.kernelForm_of_rowLength_eq_zero` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* The coordinate $i$ is the jet along the sum of row $i$ of the Schur matrix, so it is the theta value of the datum with that polynomial (`jet_jetSeries_eq_theta`). In degree $0$ all basis polynomials are $1$, and the row of the Schur matrix sums to $1$ (`sum_schur_smul_nablaBasis`). The character $\nu_W$ is $1$. So the datum is the Fock vector of the polynomial $1$, the vacuum, tensored with the finite datum, and its theta value is the scalar kernel. $\square$

The function $\Psi$ is $0$ unless the reductions at the chosen places are the basis vector $e_{i_0}$. In that case it is the product over the twist places of the tame characters at the entry of the row $i_0$. This is the form of the kernel in the model case of Section 1, and the chapter [Hecke values of character lifts](/chapter/hecke-values/) uses it to bound heights of twisted values.
