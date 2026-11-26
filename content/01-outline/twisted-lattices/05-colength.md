---
title: Colength
lean:
  - New/Reduction/Lattices/Colength.lean
  - New/Reduction/Lattices/TwistedLattice.lean
decls:
  - New.ColengthDvd
  - New.ColengthDvd.of_le
  - New.ColengthDvd.of_dvd
  - New.ColengthDvd.trans
  - New.ColengthDvd.comap
  - New.ColengthDvd.map
  - New.ColengthDvd.of_det_dvd
  - New.colengthDvd_top_smul_top
  - New.ColengthDvd.relLength_le
  - New.IsOntoUpToColength
  - New.TwistedLattice.indexLe_of_colengthDvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Colength

The index of Section 4 is a statement about one family. Theorem A needs index bounds for all finite families in a module at once. The source states them with the notion of colength. Over a discrete valuation ring the colength of a submodule $N \subset M$ of finite colength is the length of $M/N$. The rings $\mathcal{O}_\iota$ are valuation rings that are not noetherian, and the source avoids lengths. It uses matrices.

**Definition (Colength divides).** Let $O$ be a commutative ring, $M$ and $N$ submodules of an $O$-module, and $z \in O$. *The colength of $N$ in $M$ divides $z$* if for every finite family $\Phi_1, \dots, \Phi_n$ in $M$ there is a matrix $m \in O^{n \times n}$ with $\det m \mid z$ and $\sum_k m_{ik} \Phi_k \in N$ for every $i$.

Lean: `New.ColengthDvd` (New/Reduction/Lattices/Colength.lean).

The definition does not require $N \subset M$. Over a valuation ring with valuation $v$, read it as "the colength of $N \cap M$ in $M$ is at most $v(z)$".

**Example (A lattice over a discrete valuation ring).** Let $O = \mathbb{Z}_{(p)}$, $M = O^2$, and $N = O \oplus pO$. A family $\Phi_1, \dots, \Phi_n$ in $M$ is carried into $N$ by a matrix with determinant $p$: if some $\Phi_j$ has a second coordinate of least valuation, subtract multiples of $\Phi_j$ from the others to make their second coordinates $0$, and multiply $\Phi_j$ by $p$. So the colength of $N$ in $M$ divides $p$. The length of $M/N$ is $1 = v_p(p)$.

**Lemma (The calculus of colength).** Let $M, N, P$ be submodules of an $O$-module $V$ and $z, z', a \in O$.

1. If $M \subset N$, the colength of $N$ in $M$ divides every $z$.
2. If the colength of $N$ in $M$ divides $z$ and $z \mid z'$, it divides $z'$.
3. If the colength of $N$ in $M$ divides $z$ and that of $P$ in $N$ divides $a$, then that of $P$ in $M$ divides $za$.
4. Let $f\colon U \to V$ be linear and $M', N' \subset U$ with $f(M') \subset M$ and $x \in N'$ for every $x \in M'$ with $f(x) \in N$. If the colength of $N$ in $M$ divides $z$, so does that of $N'$ in $M'$.
5. Let $f\colon V \to U$ be linear and $M', N' \subset U$ with $M' \subset f(M) + N'$ and $f(N) \subset N'$. If the colength of $N$ in $M$ divides $z$, so does that of $N'$ in $M'$.

Lean: `New.ColengthDvd.of_le` (New/Reduction/Lattices/Colength.lean).

Lean: `New.ColengthDvd.of_dvd` (New/Reduction/Lattices/Colength.lean).

Lean: `New.ColengthDvd.trans` (New/Reduction/Lattices/Colength.lean).

Lean: `New.ColengthDvd.comap` (New/Reduction/Lattices/Colength.lean).

Lean: `New.ColengthDvd.map` (New/Reduction/Lattices/Colength.lean).

*Proof.* For part 3, carry $\Phi$ into $N$ by $m$, then carry the family $m\Phi$ into $P$ by $m'$. The product $m'm$ carries $\Phi$ into $P$, and $\det(m'm) \mid za$. For part 5, write $\Phi_k = f(x_k) + y_k$ with $x_k \in M$ and $y_k \in N'$, and use the matrix for the family $x$. The other parts are direct. $\square$

The next theorem connects the definition with determinants. It is the Smith normal form, or the elementary divisor theorem, over a valuation ring (for a principal ideal domain, Lang, *Algebra*, Chapter III, §7).

**Theorem (Images of square matrices).** Let $O$ be a valuation domain, $I$ a finite set, and $A \in O^{I \times I}$ with $\det A \mid z$. If a submodule $L \subset O^I$ contains the image of $A$, then the colength of $L$ in $O^I$ divides $z$.

Lean: `New.ColengthDvd.of_det_dvd` (New/Reduction/Lattices/Colength.lean).

*Proof.* Write $A = g \operatorname{diag}(d) g'$ with $g, g'$ invertible. For a subset $s \subset I$, let $S_s$ be the set of vectors $x$ such that the $j$-th coordinate of $g^{-1}x$ is divisible by $d_j$ for every $j \in s$. Each further coordinate costs one factor $d_j$. This follows from the case of one linear form $f$ and one divisor $a$, where the vectors of $M$ with $a \mid f$ have colength dividing $a$ in $M$: in a valuation ring, one value $f(\Phi_p)$ divides all the others, so subtract multiples of $\Phi_p$ and multiply $\Phi_p$ by $a$. So the colength of $S_I$ in $O^I$ divides $\prod_j d_j$, which divides $z$. Finally, $S_I$ lies in the image of $A$, which lies in $L$. $\square$

**Corollary (Multiples of the whole module).** Over a valuation domain $O$, the colength of $a \cdot O^I$ in $O^I$ divides $a^{\# I}$.

Lean: `New.colengthDvd_top_smul_top` (New/Reduction/Lattices/Colength.lean).

**Theorem (Comparison with the length).** Let $O$ be a discrete valuation ring. Let $M$ be finitely generated, and let the colength of $N$ in $M$ divide $z$. Then the length of $M/(M \cap N)$ is at most the length of $O/(z)$.

Lean: `New.ColengthDvd.relLength_le` (New/Reduction/Lattices/Colength.lean).

*Proof.* Take a finite family $\Phi$ that generates $M$ and a matrix $m$ for it. Write $m = Q \operatorname{diag}(a) P$ in Smith normal form. The family $\Psi = P\Phi$ still generates $M$, and $a_j \Psi_j \in N$. So $M/(M \cap N)$ is an image of $\bigoplus_j O/(a_j)$, whose length is that of $O/(\prod_j a_j)$, and $\prod_j a_j \mid z$. $\square$

This theorem shows that the definition is the textbook notion over a discrete valuation ring. The source does not use the theorem in the main proof. The source also defines endomorphisms *onto up to a bounded colength*: an endomorphism $y$ of $V$ that keeps $M$, such that the colength of $y(M) + p^n M$ in $M$ divides $p^j$ for some integer $j \leq c$.

Lean: `New.IsOntoUpToColength` (New/Reduction/Lattices/Colength.lean).

The chapters on [elementary divisors](/chapter/elementary-divisors/) and [divisibility prime by prime](/chapter/divisibility/) apply it to Hecke operators.

### From colength to index

**Theorem (Index from colength).** Let $y = (y_1, \dots, y_n)$ be a family in the space $V$ of a twisted lattice. Let $e(\ell) \geq 0$ with $\sum_{\ell \in U} e(\ell) \log \ell \leq \delta$ for every finite set $U$ of primes. Suppose that for every $\iota \mid \ell$ there are an integer $j \leq e(\ell)$ and an $\mathcal{O}_\iota$-submodule $M \subset V$ that contains all $y_i$, such that the colength of the integral vectors at $\iota$ in $M$ divides $\ell^j$. Then $y$ has index at most $\delta$.

Lean: `New.TwistedLattice.indexLe_of_colengthDvd` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* At $\iota$, the definition of colength gives a matrix $u$ with $\det u \mid \ell^j$ that carries $y$ into the integral vectors. By the lemma on divisors of a power of the prime, $\|\iota \det u\| \geq \ell^{-j} \geq \ell^{-e(\ell)}$. $\square$

The proof of Theorem A uses this theorem in `New.Data.indexLe_of_mem_image_normalizedPoincare`, with $M$ the image of a module of integral source forms: see [the proof of Theorem A](/chapter/proof-of-theorem-a/).

**Remark (Formalization).** The notion `New.ColengthDvd` replaces the length of $M/N$ by a statement about all finite families. Two reasons make this the useful form. First, the rings $\mathcal{O}_\iota$ are not noetherian, and their value groups are not discrete. For $x \in \mathcal{O}_\iota$ with $\|\iota x\| < 1$, the module $\mathcal{O}_\iota/(x)$ has infinite length, so a length does not measure a loss. Second, the index of Section 4 asks for a matrix that carries a given family, and the definition gives exactly such a matrix. The textbook statement is the theorem on comparison with the length. The argument needs no more, because it uses the colength only through the index.
