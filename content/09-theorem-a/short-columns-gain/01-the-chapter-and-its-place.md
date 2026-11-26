---
title: The chapter and its place
lean:
  - New/UpperBound/Size/ShortColumns.lean
  - New/Derivatives/Sharpness/NearPairs.lean
  - New/UpperBound/Divisibility/JetExponent.lean
decls:
  - New.Data.span_isShort_ramifiedSourceForms_eq_top
  - New.Data.le_divisibilityBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

Theorem A compares two sizes of one chain of theta lifts. One size is archimedean: it says how large the values of the chain are. The other size is arithmetic: it says how divisible the chain is, prime by prime. This chapter prepares both sides. On the archimedean side it proves that the source of the chain is spanned by forms whose values are integral and small. On the arithmetic side it defines the gain at a prime $p$, the divisibility that the proof asks of the chain at $p$, and it proves that the divisibility bound of the later chapters is at least the gain, less a controlled loss.

The plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/). The place of Theorem A in the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/). This chapter uses [the objects of the upper bound](/chapter/upper-bound-objects/) (chapter 2), [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/) (chapter 6), [the count and the divisibility of standard data](/chapter/normal-forms/) (chapter 7) and [theta kernels and gauges](/chapter/theta-kernels-gauges/) (chapter 8). All sizes come from [the data and its sizes](/chapter/data-and-sizes/); its section 6 has the table of sizes and explains the automation `HasLogBound`.

### What the chapter proves

The chapter proves two theorems and the facts that they need.

**Theorem (Short ramified source forms).** The ramified source forms that are $\exp(f a \log^3 b)$-short span the space $\mathrm{src}$ of ramified source forms over $\mathbb{C}$.

Lean: `New.Data.span_isShort_ramifiedSourceForms_eq_top` (New/UpperBound/Size/ShortColumns.lean).

The proof is in Section 4. A form is $B$-short if its values are integral at every $p$-adic place of $\mathbb{C}$ and every conjugate of every value has squared Weyl norm at most $B$ (Section 2).

**Theorem (Only collisions lose).** Let $p < x_1$ be a prime that does not split in $K$, let $j < m$, and let $S$ be a set of infinite places of $E$. Then
$$\frac{\mathrm{gain}_p}{m} - \mathrm{coll}_p(S) + v(\pi_p)\,\#(\Phi_a \cap S)\,\frac{a}{x_1} - \frac{f\,(\log b)^2\,a}{p\,m} \leq \mathrm{div}_p(j, S).$$

Lean: `New.Data.le_divisibilityBound` (New/UpperBound/Divisibility/JetExponent.lean).

Here $\mathrm{div}_p(j, S)$ is the divisibility bound of stage $j$ (Section 7), $\mathrm{coll}_p(S)$ is the sum over the collisions outside $S$ (Section 5), and $v(\pi_p)$ is $\frac12$ if $p = d$ and $1$ otherwise. The proof is in Section 7.

Between the two theorems the chapter bounds the loss from near pairs of $b$-places (Section 6). That bound is not used by Theorem A. It is used in Volume 11 by [the divisibility is sharp](/chapter/sharpness/), but its file sits in this volume, and its notions of weight and partner are those of the gain.

### A sketch

*Short forms.* At a free level every form is a finite sum of delta forms, one for each class. A delta form at the class of $x$ with value $v$ is $B$-short when $v$ is integral at $x$ and every conjugate of $v$ has norm at most $B$. A short basis $Y$ of the lattice at $x$, with small entries, moves the evaluation vectors of the Weyl module to vectors that are integral at $x$ and small. The evaluation vectors at arrays of roots of unity span the module. So the short delta forms span. The ramified forms are the image of the operator $\prod_w (1 - z_w)$, where $z_w$ is a scaling at a prime $w \mid \pi$. Each factor $1 - z_w$ multiplies the bound $B$ by at most $4$, by the parallelogram law. There are $f$ factors, so the cost is $4^f$.

*The gain.* The gain at $p$ is a sum of positive parts $(y/p^e - \kappa(u(-p^e)\sigma))_+$. These measure how much of a column of length $y$ at $\sigma$ survives the comparison with the partner place $u(-p^e)\sigma$ at the exponent $e$. The divisibility bound of stage $j$ has the same shape, with the true column counts of the diagrams in place of the weights. The proof compares the two series term by term. A term of the gain can exceed its partner term only in two ways. Either $\tau$ and its partner are both $a$-places outside $S$: this is a collision. Or the comparison of the low columns costs a small error, of size $x^{60}$ for each small $e$. The errors add up to a few multiples of $a/(pm)$, which is the loss.

*Near pairs.* The second part of the gain, $k F(p)$, compares weights. The weight is large, equal to $b$, only on the $b$-places. Sparseness of the $b$-places along the powers of $-p$ says that at most one exponent $e$ makes both $\tau$ and $(-p)^e\tau$ into $b$-places. So the identity $\gamma_p\sum\kappa - F(p) = v(\pi_p)\sum_\tau R_\tau$ has small terms $R_\tau$, apart from at most one near pair at each place.

### The setting

Fix parameters $P$ and data $D$ as in [the data and its sizes](/chapter/data-and-sizes/). The modulus is $q_0$ and $d \equiv q_0/2 - 1 \pmod{q_0}$ is prime, with $K = \mathbb{Q}(\sqrt{-d})$. The CM field $E$ has $f$ infinite places, and they form a group $\Phi$ isomorphic to $(\mathbb{Z}/q_1)^\times$. For an integer $\nu$ the place $u(\nu)$ is the place of the class of $\nu$ if $\nu$ is prime to $q_1$, and the identity place otherwise. The $a$-places $\Phi_a$ are the places of class $1$ modulo $q_0$. The $b$-places $\Phi_b$ are a set of places of class $-1$ modulo $q_0$ that is part of the data. The scales are $x < x_1 < b$, the long order is $a = x b$, and the weight of a place is $\kappa(\sigma) = b$ on $\Phi_b$ and $\kappa(\sigma) = a/x_1$ elsewhere. There are $m$ lifts. The ranks are $n_j = k + j(t + 1)$, and the gap is $\Delta = 2r^8$.

The level prime $N$ splits in $E$ as a product over the primes $w$ that divide a fixed integer $\pi$ with $\pi\bar\pi = N$, and their conjugates. The set of these $w$ has $f$ elements.

**Definition (The primes over N).** The set $\Pi_N$ is the set of the primes $w$ of $E$ that divide $\pi$. It has $f$ elements.

Lean: `New.Data.piNPlaces`, `New.Data.card_piNPlaces` (New/UpperBound/Objects/Columns.lean).

The level $K_j$ on $X_j$ is the set of elements of the chosen level whose last row is congruent to $(0, \dots, 0, 1)$ modulo $\pi$. A source form is an algebraic form on $X_0$ of the weight with column counts $c_\tau(h)$ that is fixed by $K_0$. These are in [the objects of the upper bound](/chapter/upper-bound-objects/), Sections 3 and 7. The space of source forms is $\mathcal{F}$. The column counts are $c_\tau(1) = a$ at the $a$-places and $0$ elsewhere, $c_\tau(k) = \kappa_1(\tau) - \lfloor (k+t+1)/2\rfloor$, $c_\tau(h) = \Delta - (t+1)$ if $h > k$ and $t + 1 \mid h - k$, and $c_\tau(h) = 0$ otherwise.

### Users and imports

The theorem on short ramified source forms is used in [the proof of Theorem A](/chapter/proof-of-theorem-a/). The short forms of Section 2 are also used in Volume 11. The bound for the divisibility bound is used in [divisibility prime by prime](/chapter/divisibility/). The scalings and the ramified forms are also used in [the objects of the upper bound](/chapter/upper-bound-objects/), Section 8, which states them once with a link to this chapter.

The three files of the chapter import only files of earlier chapters. ShortColumns.lean imports the kernels of chapter 8 and the columns of chapter 2. NearPairs.lean imports the partners of chapter 6. JetExponent.lean imports the count of chapter 7 and NearPairs.lean. No file imports a later chapter of this volume.

### The order of the sections

Section 2 treats short forms in general and proves that they span at a free level. Section 3 builds the scalings and the ramified source forms, and bounds the dimension of the forms that are not ramified. Section 4 proves the theorem on short ramified forms. Section 5 states the prime notation, the gain, the loss and the collisions. Section 6 treats near pairs and the losses at one place. Section 7 proves the bound for the divisibility bound. Section 8 has exercises and notes.
