---
title: The three theorems and the budget
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
decls:
  - New.Data.errorUnit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three theorems and the budget

This chapter states the three theorems that the main inequality uses, and it gives a plan of each proof. Theorem A says that the target lattice has many short vectors of small index. Theorem B says that the vectors of Theorem A fill almost all of the target. Theorem C says that every large family of target forms of small index is long. The main inequality of [the next chapter](/chapter/main-inequality/) puts the three side by side. The upper bound of A and B and the lower bound of C have the same main term, and what is left is the inequality $m \cdot \mathrm{rem} \leq f a \log^5 b$ for the total remainder. Each theorem is stated so that a reader of this volume can use it without the later volumes. The proofs take four volumes: Volume 9 for Theorem A, Volume 10 for Theorem B, Volume 11 for Theorem C, and Volume 12 for the regular families that Theorem C uses. This chapter proves each theorem from the inputs that those volumes supply, and it states each input in full.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of this volume reduces the half-plane statement to a one-sided bound for a weighted prime remainder, and [the lattice and the prime sum](/chapter/lattice-and-prime-sum/) explains the idea: one lattice of automorphic forms has a covolume that can be bounded from above, by forms that are short and divisible, and from below, by the product formula. This chapter is the interface between the deep part of the book and the short reduction at the end. [The main inequality](/chapter/main-inequality/) uses nothing else from Volumes 9 to 12.

### The objects

Fix the data $D$ of [the data and its sizes](/chapter/data-and-sizes/). It gives the scales $x$, $x_1$, $b$, with $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, the long order $a = x b$, the number $m \in [\sqrt{x}, 2\sqrt{x}]$ of lifts, the rank $r \in [x^5, 3x^5]$, the numbers $k = r + 1 - m$ and $t = 5r$, the CM field $E$ with $f$ infinite places, a prime level $N$, and the main amount $\mathrm{main}$ of [the prime sums](/chapter/prime-sums/). The theorems speak about the following objects. The later volumes construct them. This chapter uses only the properties that it states.

1. The *source* $\mathrm{src}$ is a space of ramified source forms. It lies in the space of all source forms, of dimension $D_X$.
2. The *target* $T$ is a space of good forms. Its dimension is $d_T$.
3. The finite group $\bar G$ is a product of groups $\mathrm{GL}_r(\mathbb{F}_w)$, over chosen places $w$ above the two level primes. It acts on the forms of the target.
4. For each $s \in \bar G$ there is a linear map $s\mathfrak{p} : \mathrm{src} \to T$. It is the translate by $s$ of one map $\mathfrak{p}$. Section 2 defines it.
5. For each $m$-fold twist $\vartheta$ there is an injective linear map $\Theta_\vartheta$ from $T$ to forms on a larger group, the chain of $m$ theta lifts for the twist $\vartheta$. The modulus of $\vartheta$ has norm $\mathrm{Nm}\,Q(\vartheta)$. The twist $1$ is the trivial twist, and $\Theta_1$ is its chain.
6. The letter $\iota$ runs over the pairs of a prime $\ell$ and a field isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. The letter $\sigma$ runs over the field automorphisms of $\mathbb{C}$.

A target form $y$ is *integral at* $\iota$ if $\Theta_\vartheta y$ is integral at $\iota$ for every $m$-fold twist $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to $\ell$. The forms on the larger group have coordinates, and a rational positive definite Gram matrix gives their inner product. So the number $\|\Theta_1 y\|_\sigma^2$, the squared norm of the conjugate of $\Theta_1 y$ by $\sigma$, makes sense. These data make $T$ a twisted lattice, the *target lattice* of [the lattice of integral target forms](/chapter/integral-target-forms/).

### Index, covolume and height

Three notions of [twisted lattices](/chapter/twisted-lattices/) occur in the statements. Let $y_1, \dots, y_n$ be target forms.

- The family $y$ has *index at most* $\delta$ if there are numbers $e(\ell) \geq 0$, with $\sum_{\ell \in U} e(\ell) \log \ell \leq \delta$ for every finite set $U$ of primes, such that for every $\iota$ above $\ell$ some $n \times n$ matrix with entries in the valuation ring $\mathcal{O}_\iota$ carries $y$ into the forms integral at $\iota$, with loss $e(\ell)$. The matrix does not depend on the twist.
- The family $y$ has *covolume at most* $c$ if for every $\sigma$ the Gram determinant of the conjugates $\sigma\Theta_1 y_1, \dots, \sigma\Theta_1 y_n$ has absolute value at most $e^c$. Only the trivial twist occurs here.
- A family $(u_\iota)$ of complex numbers, one for each $\iota$, has *height at most* $c$ if there are $H \neq 0$, a real $\alpha$, and $h(\ell) \geq 0$, such that $|\sigma H| \leq e^\alpha$ for every $\sigma$, $|\iota(H u_\iota)| \leq \ell^{h(\ell)}$ for every $\iota$ above $\ell$, and $\alpha + \sum_{\ell \in U} h(\ell)\log \ell \leq c$ for every finite set $U$ of primes.

The product formula turns these notions into an inequality. If $y$ completes to a basis, then a nonzero algebraic number built from the Gram determinant cannot be small at every place. [Twisted lattices](/chapter/twisted-lattices/) proves the form that Theorem C uses. Section 5 states it.

**Definition (The unit of loss).** The unit of loss is $\mathrm{err}_0 = f a \log^3 b$.

Lean: `New.Data.errorUnit` (New/Reduction/Data/AdmissibleData.lean).

All errors of the three theorems are small multiples of $f a \log^3 b$ or of $f a \log^4 b$. The main term is much larger: the main amount is at least $x^4 f a$ ([the prime sums](/chapter/prime-sums/)).

### A model case

The plan of the proof can be seen in the lattice $\mathbb{Z}^d \subset \mathbb{R}^d$. Let $y_1, \dots, y_d \in \mathbb{Z}^d$ be independent. Their determinant is a nonzero integer, so $|\det(y)| \geq 1$. Hadamard's inequality gives $|\det(y)|^2 \leq \prod_i \|y_i\|^2$. If every $\|y_i\|^2 \leq e^h$, then $0 \leq \log |\det(y)|^2 \leq d h$. Now let the $y_i$ be integral only up to a denominator: $Q y_i \in \mathbb{Z}^d$ for an integer $Q \geq 1$. Then $Q^d \det(y)$ is a nonzero integer, and $\log|\det(y)|^2 \geq -2d \log Q$. The index of the family is $\delta = d \log Q$, and the bound reads $c + 2\delta \geq 0$ with $c = d h$. The factor $2$ is the factor of Theorem C. It comes from the square in the Gram determinant.

In the twisted lattice the volume of the lattice is not $1$. The lower bound has an extra term, the height of the volume ratio $Z(1)/Z(\xi_\iota)$ of the chain determinants. Theorem C computes this height. It is about $-d_T \cdot \mathrm{main}$. So the inequality $c + 2\delta \geq 0$ becomes $c + 2\delta \geq d_T\,\mathrm{main}$, up to errors. Theorem A gives the other side: $c \leq n(\mathrm{main} - m\,\mathrm{rem})$, up to errors, for $n$ vectors. With $n$ close to $d_T$ by Theorem B, the main amounts cancel and $m \cdot \mathrm{rem}$ is bounded by the errors.

### The budget

The table lists the error of each theorem per dimension of the target, as it enters the main inequality.

| source | where | amount per dimension |
|---|---|---|
| size | Theorem A (a) | $f a \log^4 b$ |
| index | Theorems A (b) and B | $20 \log(1 + 2b^2) \cdot f a \log^3 b$ |
| covolume | Theorem C | $3 f a \log^4 b$ |

The index is $10\log(1 + 2b^2)\, f a \log^3 b$ per dimension, and it enters Theorem C as $2\delta$, so the table lists twice this amount. Theorem B has no error of its own. It controls the number of translates and the missing share $4/b^2$, which Theorem C fills at a cost absorbed in its error. The sum of the three amounts is at most $64 f a \log^4 b$, as $20\log(1 + 2b^2) \leq 60 \log b$ for $b \geq 3$. The main inequality needs only that twice the sum is at most $f a \log^5 b$, and this holds because $\log b$ is large.

### The plan of the chapter

Section 2 defines the map $\mathfrak{p}$ and its constants, two of them chosen by `choose`. Sections 3, 4 and 5 state Theorems A, B and C, prove each one from its inputs, and give a plan of the proof of the inputs. Section 6 puts the three theorems together and lists what cancels and where the nonvanishing comes from. Section 7 has the exercises and the notes.
