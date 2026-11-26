---
title: One notation for the book
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/Magnitudes.lean
decls:
  - New.Parameters
  - New.Data
  - New.Data.HasLogBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One notation for the book

The argument of the source uses about forty letters for its main objects. Each letter names a number, a field, a set of places, a character or a space, and each of them has a Lean name. A reader who meets $\kappa_j$ in Volume 1 and `D.liftWeight j` in a Lean file must know that these are the same object, and must know its exact definition. This chapter fixes one letter for each object, gives its Lean name with the full namespace and its file, and states its definition or its size as Lean states it.

### Why one notation

The source is not one text. It has about two thousand files, and its comments do not always use the same letter for the same object. The file `New/UpperBound/Objects/Rows.lean`, for example, writes $h$ for the gap and $w_j$ for the weight of the $j$-th lift, while the file of the data writes $\Delta$ and $\kappa_j$. The notes on which this book rests have their own letters too. The book keeps one letter for each object in all volumes, and the `Lean:` line under each statement gives the Lean name. When a file of the source uses another letter, the text says so where it matters.

The letters of this chapter are the letters of the outline (Volume 1), with a small number of changes. Section 6 lists every place where the chapters of Volume 1 use one letter for two objects or two letters for one object, and it gives the choice of the book.

### How an entry is given

Each object has one entry. The entry gives the letter, the Lean name with its namespace, the file, and the definition. If Lean defines the object by a formula, the entry states the formula. If Lean asks only that the object lies in a range, the entry states the range, because a reader must not take an object to be more definite than Lean makes it. Most numbers of the data are of the second kind: the scale $x$, the number $m$ of lifts and the rank $r$ are not fixed numbers but numbers in intervals.

Two namespaces carry almost all names of this chapter. The structure `New.Parameters` holds the modulus $q_0$ and the prime $d$, and the names that depend on them alone live in `New.Parameters`. The structure `New.Data` holds the scales, the ranks, the primes and the weights, and the names that depend on the data live in `New.Data`. In a Lean file, `P` is a term of `New.Parameters` and `D` is a term of `New.Data P`. So `D.k` means `New.Data.k D`, and `P.q₂ s` means `New.Parameters.q₂ P s`.

**Definition (Parameters).** The parameters are a pair $(q_0, d)$ of natural numbers such that $18480 \mid q_0$, $d$ is prime, $q_0 \mid 2(d + 1)$ and $q_0 \nmid d + 1$.

Lean: `New.Parameters` (New/Reduction/Data/FieldsAndPlaces.lean).

**Definition (Data).** For parameters $P$, the data are the scales, ranks, places, weights and primes of Section 3, with the conditions that Section 3 states.

Lean: `New.Data` (New/Reduction/Data/AdmissibleData.lean).

### General conventions

The following conventions hold in every volume.

1. The natural numbers $\mathbb{N}$ contain $0$. Lean's type `ℕ` contains $0$.
2. The logarithm $\log$ is the natural logarithm. A power of a logarithm is written $\log^k b = (\log b)^k$. The iterated logarithm is written $\log\log b$, never $\log^2 b$.
3. The positive part of a real number $t$ is $t_+ = \max(t, 0)$. Lean writes `t⁺` (Mathlib's `posPart`).
4. The sum $\sum_{n \leq y}$ runs over the integers $1 \leq n \leq y$. Lean writes `∑ n ∈ Finset.Icc 1 ⌊y⌋₊`.
5. Intervals are written $[a, b]$ and $(a, b)$. Lean writes `Set.Icc a b` and `Set.Ioo a b`, and a membership `x ∈ Icc a b` means $a \leq x \leq b$.
6. The group of units of $\mathbb{Z}/q\mathbb{Z}$ is $(\mathbb{Z}/q\mathbb{Z})^\times$. Lean writes `(ZMod q)ˣ`. Euler's function is $\varphi(q) = \#(\mathbb{Z}/q\mathbb{Z})^\times$, and Lean writes `φ q` or `q.totient`.
7. The number of elements of a finite set $A$ is $\#A$.
8. A congruence $a \equiv b \bmod q$ is written in Lean as `a ≡ b [MOD q]` for natural numbers.
9. Complex conjugation is $z \mapsto \bar z$. Lean writes `star z` or `conj z`. On the integers of a CM field, `star` is the complex conjugation of the field.
10. Euler's constant is $\gamma = 0.5772\ldots$, and Lean writes `Real.eulerMascheroniConstant`.

### Operations with a value at every point

Lean functions are total, so some operations have a value where the textbook has none. The book notes these values where they change the meaning of a statement. Volume 0, [Reading the Lean](/chapter/reading-the-lean/), explains them in full. The list is short.

1. Division of natural numbers rounds down: in `ℕ` one has $7 / 2 = 3$. The weight $a/x_1$ of Section 3 is such a quotient. So the book writes $\lfloor a / x_1 \rfloor$ where the rounding matters.
2. Subtraction of natural numbers stops at $0$: in `ℕ` one has $2 - 5 = 0$. The rank $k = r + 1 - m$ is such a difference, and Lean proves separately that $m \leq r + 1$.
3. Division by $0$ gives $0$ in a field: $x/0 = 0$. The logarithm has $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$.
4. A sum `tsum` of a series that does not converge is $0$, and an integral of a function that is not integrable is $0$.
5. An object defined by `choose` is one object that Lean picks among those that an existence theorem gives. It has no formula. The constant `P.vacuumBoundConst` in $C_P$, the characters `D.chiZero` and `D.chiM`, and the spaces `D.spaceY j` are of this kind.

**Remark (Formalization).** A junk value never makes a theorem of the source false, since Lean checks each statement with the total function. A junk value can make a statement weaker than it seems. An example is the remainder $R_q(x)$ of Section 4. Lean defines it for every real $x$. At $x = 0$ the term $\log x/\varphi(q)$ is $0$, the division by $x$ gives $0$, and so $R_q(0) = -c_q$. No theorem of the source uses this value, but a reader who reads a statement for all real $x$ must know it. The book reads each statement with the junk values in mind, and says so where it matters.

### The principal character

A Dirichlet character modulo $q$ with the value $1$ at every unit is *principal*. Mathlib writes it `1`. The source calls it "trivial" in some files and "principal" in others. This book uses only the word *principal* for Dirichlet characters. The word *trivial* is kept for characters of other groups, for the trivial twist of Section 5, and for the trivial tame part.

### Sizes on a logarithmic scale

Most sizes of the data are bounds of the form $|F| \leq e^l$ or $e^l \leq F$, with $l$ a linear expression in $\log x$, $\log x_1$ and $\log b$. The source has one class for both forms.

**Definition (Logarithmic bound).** For data $D$, a Boolean $u$, a real number $F$ and a real number $l$, the bound `HasLogBound D u F l` holds if $|F| \leq e^l$ when $u$ is true, and if $e^l \leq F$ when $u$ is false. The bound does not depend on $D$, and $D$ is an argument only for the automation.

Lean: `New.Data.HasLogBound` (New/Reduction/Data/Magnitudes.lean).

The table of sizes in [the table of sizes](/chapter/sizes/) and in [the data and its sizes](/chapter/data-and-sizes/) gives each bound in the textbook form. This chapter gives a size only where it is needed to read a definition.

### The plan of the chapter

Section 2 gives the parameters, the fields and the places: $q_0$, $d$, $K$, $\chi_K$, $s$, $l_0$, $q_1$, $q_2$, $E$, $\zeta$, $\Phi$, $f$, $\mathrm{rd}_E$, $C_d$, $\Omega$ and $C_P$. Section 3 gives the data: the scales $x$, $x_1$, $b$ and the exponent $\varepsilon$, the ranks $m$, $r$, $k$, $t$, $n_j$, the gap $\Delta$, the long order $a$, the sets $\Phi_a$ and $\Phi_b$, the weights $\kappa$, $\kappa^{(i)}$ and $\kappa_j$, the primes $p_0$, $p_1$ and $N$, and the level bound $N_-$. Section 4 gives the characters, the $L$-functions and the prime sums. Section 5 gives the spaces $X_j$, $Y_j$, $W_j$, $V_j$, the characters of the lifts, the forms, the twisted lattices, and the normalizations of norms, measures and Fourier transforms. Section 6 lists the clashes of letters in Volume 1 and in the source, and the choices of the book. Section 7 has exercises and notes.
