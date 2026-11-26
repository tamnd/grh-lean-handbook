---
title: The five theorems
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The five theorems

This section states the classical conjectures, then the five theorems of the source in mathematical words, and then what the five theorems do not say. The theorems are stated in full, with proofs of the last step, in [the theorem and the plan](/chapter/theorem-and-plan/) and in [from the half-plane to the line](/chapter/half-plane-to-line/). This section links to those statements. It does not state them a third time as numbered theorems.

### The classical conjectures

Let $\zeta(s)$ be the Riemann zeta function, continued to $\mathbb{C} \setminus \{1\}$. It has zeros at $s = -2, -4, -6, \dots$, the trivial zeros. Every other zero lies in the strip $0 < \operatorname{Re} s < 1$ (Davenport, *Multiplicative Number Theory*, Chapters 8 and 13).

**Conjecture (The Riemann hypothesis).** Every zero $\rho$ of $\zeta$ with $0 < \operatorname{Re} \rho < 1$ has $\operatorname{Re} \rho = 1/2$.

Let $q \geq 1$ and let $\chi$ be a Dirichlet character modulo $q$. Let $L(s, \chi) = \sum_{n \geq 1} \chi(n) n^{-s}$ for $\operatorname{Re} s > 1$, continued to $\mathbb{C}$, with a pole at $s = 1$ when $\chi$ is principal. If $\chi$ is primitive modulo $q > 1$, the zeros of $L(s, \chi)$ outside the strip $0 < \operatorname{Re} s < 1$ are the trivial zeros at $s = -a - 2k$ for $k \geq 0$, where $a \in \{0, 1\}$ is the parity of $\chi$ (Davenport, Chapter 9). If $\chi$ is induced by a primitive character $\chi^*$, then $L(s, \chi) = L(s, \chi^*) \prod_{p \mid q} (1 - \chi^*(p) p^{-s})$, and the finite product adds zeros on the line $\operatorname{Re} s = 0$ only.

**Conjecture (The generalized Riemann hypothesis for Dirichlet L-functions).** For every $q \geq 1$ and every Dirichlet character $\chi$ modulo $q$, every zero $\rho$ of $L(s, \chi)$ with $0 < \operatorname{Re} \rho < 1$ has $\operatorname{Re} \rho = 1/2$.

By the factorization above, the conjecture for all characters is the same as the conjecture for primitive characters. The case $q = 1$ is the Riemann hypothesis.

**Remark.** The name "generalized Riemann hypothesis" has more than one meaning in the literature. Some authors use it for Dirichlet L-functions, as here. Others use it for the Dedekind zeta functions of number fields (often called the extended Riemann hypothesis), for the L-functions of Hecke characters, or for all automorphic L-functions (Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, state it for a general class of L-functions). The source claims only the case of Dirichlet L-functions. Its title, "GRH for Dirichlet L-functions" (root `README.md`, line 1), says so. A Dedekind zeta function of an abelian field over $\mathbb{Q}$ is a product of Dirichlet L-functions (Washington, *Introduction to Cyclotomic Fields*, Chapter 4), so the case of abelian fields follows from the conjecture above by a classical argument. The source does not state that consequence, and this book does not treat it.

This book states the two conjectures as conjectures. That is their status in the literature, and nothing in this book changes it. The source claims Lean proofs of forms of them, and the rest of this section says which forms.

### The five theorems in words

The source has a file of statements that imports only Mathlib. It defines four propositions and proves nothing. A second file, the file of main theorems, proves five theorems. Here they are in words. The modulus is $N \geq 1$, $\chi$ is a Dirichlet character modulo $N$, $L(s, \chi)$ is the L-function of Mathlib, and $\chi_0 = 1$ is the principal character modulo $N$.

1. **The Riemann hypothesis, in Mathlib's form.** If $\zeta(s) = 0$, $s \neq -2(n + 1)$ for every $n \in \mathbb{N}$, and $s \neq 1$, then $\operatorname{Re} s = 1/2$. See [Theorem](/decl/riemannHypothesis/).
2. **The same statement, in the notation of the file of statements.** See [Theorem](/decl/riemannZeta_eq_zero_re/).
3. **The half-plane form.** If $\operatorname{Re} s > 1/2$, and $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$. See [Theorem](/decl/LFunction_ne_zero_of_half_lt_re/).
4. **The line form.** If $0 < \operatorname{Re} s < 1$ and $L(s, \chi) = 0$, then $\operatorname{Re} s = 1/2$. See [Theorem](/decl/LFunction_eq_zero_re/).
5. **The line form for primitive characters.** The same, with the hypothesis that $\chi$ is primitive. See [Theorem](/decl/LFunction_eq_zero_re_of_isPrimitive/).

The first theorem is the classical Riemann hypothesis. The hypothesis $s \neq 1$ excludes no zero, because Mathlib gives $\zeta$ a value at $s = 1$ that is not $0$. The fourth theorem is the classical conjecture for Dirichlet L-functions, for every modulus and every character, primitive or not. The third theorem excludes zeros in the whole half-plane $\operatorname{Re} s > 1/2$. The part $\operatorname{Re} s \geq 1$ is classical, by the Euler product and the non-vanishing on the line $\operatorname{Re} s = 1$. With the functional equation, the third theorem is equivalent to the fourth. The fifth theorem is a special case of the fourth.

The argument of the source proves the third theorem. The other four come from it by the reflection of zeros under $s \mapsto 1 - s$. [From the half-plane to the line](/chapter/half-plane-to-line/) does this step in full. The third theorem is the main claim of the source, and the rest of this book explains its proof.

**Remark (Formalization).** The file of statements, at the pin, reads as follows ([Statements.lean](lean:Statements.lean#L1)).

```lean
import Mathlib

def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

The five theorems of `Main.lean` have the types `RiemannHypothesis` (a definition of Mathlib), `RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine` and `PrimitiveDirichletLZerosOnLine`. The instance `[NeZero N]` says $N \neq 0$. The character `1` is the principal character modulo $N$, for each $N$. The proof of the fifth theorem does not use its hypothesis `χ.IsPrimitive`. The second theorem is proved by the first, since the two types are equal by unfolding. The source says that this file, and the names and types of the five theorems, are taken unchanged from Alpöge's proof (`grh/NOTICE`, lines 6 and 7). [The statements](/chapter/statements/) compares each line with the definitions of Mathlib.

### What the five theorems do not say

A precise claim has limits. A reader must know them, so that the claim is not read as more than it is.

1. **Nothing about $\operatorname{Re} s \leq 0$.** The line forms speak only of the open strip. The source says this itself (`grh/README.md`, line 22). For an imprimitive $\chi$ the finite Euler product has zeros on $\operatorname{Re} s = 0$, so a statement on the closed strip would be false. The trivial zeros at negative integers are also outside the statements. The first theorem excludes the points $-2, -4, \dots$ by name, and says nothing about whether $\zeta$ vanishes there.
2. **Nothing about multiplicities.** The theorems say where the zeros are. They say nothing about the order of a zero, nothing about the simplicity of zeros, and nothing about the linear independence of their ordinates.
3. **No quantitative statement.** The theorems are qualitative. They give no zero-free region with a constant, no explicit form of the prime number theorem, and no bound for $L(1, \chi)$. The classical consequences of the generalized Riemann hypothesis, such as the bound $\psi(x; q, a) = x/\varphi(q) + O(x^{1/2} \log^2 x)$ for $(a, q) = 1$, are not stated in the source. The proof inside the source uses explicit sizes, and [the table of sizes](/chapter/sizes/) lists them, but they do not appear in the five types.
4. **No other L-functions.** As the remark above says, the claim is for Dirichlet L-functions only.
5. **No statement about the method.** The types say nothing about how the proof goes. The method that the book explains is read from the Lean files. Whether it is the method of Alpöge's original proof is a question for Section 3.
6. **The objects are those of Mathlib.** The theorems are about `riemannZeta` and `DirichletCharacter.LFunction` as Mathlib defines them at the pinned commit. Their meaning is the classical meaning exactly when these definitions are the classical functions. [The statements](/chapter/statements/) checks that they are. Section 5 explains why this check is part of the claim and not a detail.

### Where the five theorems come from in the source

The file of main theorems takes all five from one theorem, `New.grh`, which is the half-plane form. The theorem `New.grh` is the last declaration of a file of the source on the one-sided bound for a sum over primes. It is stated with the proposition of the file of statements itself, so no restatement sits between the proof and the trusted type. Above it are the five theorems and two lemmas of the last step. Below it are about 800 files. [The theorem and the plan](/chapter/theorem-and-plan/) gives the plan of the proof below `New.grh` in one page.
