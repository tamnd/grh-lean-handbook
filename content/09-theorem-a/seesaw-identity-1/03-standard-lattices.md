---
title: The standard lattices and the glued level
lean:
  - New/UpperBound/Seesaw/AdmissibleCombinations.lean
  - New/UpperBound/Seesaw/StandardLines.lean
  - New/UpperBound/Seesaw/GluedLevel.lean
  - New/UpperBound/Seesaw/LevelIdeles.lean
decls:
  - New.gradedLatticeBasis
  - New.Grading.SpansLattice
  - New.Seesaw.IsSplitSquarefree
  - New.Seesaw.gram_gradedLatticeBasis_eq_gluedGram
  - New.Seesaw.gluedGram_mul_eq_one
  - New.Seesaw.isUnimodular_gradedLatticeBasis_gram
  - New.powerIdele
  - New.Grading.SpansLattice.mem_lattice_iff
  - New.Grading.SpansLattice.isGraded
  - New.Grading.SpansLattice.mem_latticeMinus_iff
  - New.Grading.SpansLattice.mem_latticePlus_iff
  - New.Grading.SpansLattice.mem_lattice_and_stringProj_eq_zero_iff
  - New.Grading.SpansLattice.stringSum_mem_latticeMinus_iff
  - New.Grading.SpansLattice.stringSum_mem_latticePlus_iff
  - New.Grading.SpansLattice.map_stringMapFin_latticePlus
  - New.Grading.SpansLattice.odd_and_exists_place_of_notMem_latticeMinus
  - New.Grading.exists_inclXFin_sub_one_eq
  - New.Grading.inclXFin_mem_stdLevel
  - New.Grading.inclXFin_mem_levelOf
  - New.Data.v_gradingY_genericConst_eq_ideleA_mul_star
  - New.Data.spansLattice_gradingY
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The standard lattices and the glued level

Each step of the unfolding is controlled by two lattices in the string of a grading, the intersection $\Lambda^-$ and the projection $\Lambda^+$ of [lattices of finite points](/chapter/bessel-periods/). This section computes them for the standard lattice of each space $Y_k$. The answer is explicit: both lattices are sums of lines, they agree except at the middle of an odd string, and the shift between neighbouring strings carries $\Lambda^+$ of one to $a$ times $\Lambda^-$ of the next. The section also finds which finite points of the definite part preserve the standard lattice.

### The graded Gram matrix and the glued basis

Let $V$ have a basis indexed by $(X' \sqcup \{y\}) \sqcup \{0, \ldots, s-1\}$: an orthonormal part $X = X' \sqcup \{y\}$ and a string $e_0, \ldots, e_{s-1}$. The string vectors pair by $\langle e_b, e_c\rangle = 1$ if $b + c = s - 1$ and $b \neq c$, $\langle e_b, e_b\rangle = -N$ at the middle $b = (s-1)/2$ of an odd string, and $0$ otherwise. This is the graded Gram matrix of [Bessel periods](/chapter/bessel-periods/) (Lean: `New.gradedGram`). The vector $e_b$ has grade $s - 1 - 2b$. When $s$ is odd, write $z = e_{(s-1)/2}$ for the middle vector, of norm $-N$.

The lattice spanned by the basis vectors is not unimodular when $s$ is odd: $z$ has norm $-N$. The fix glues $z$ to the last vector $y$ of $X$, as in the construction of an overlattice from a gluing of discriminant groups.

**Definition (The glued basis).** Let $a, \pi$ be units and $u$ a unitary element of a star ring, and write $\bar\pi$, $\bar a$ for the conjugates. The glued basis $B = B(a, \pi, u)$ is:

1. for odd $s$: the vectors of $X'$; the vector $y' = y/\bar\pi + u z/(\pi\bar\pi)$; and $u e_b$ for each $b$;
2. for even $s$: the vectors of $X$; $u a^{-1} e_b$ for $2b < s$; and $u \bar a\, e_b$ for $2b \geq s$.

Lean: `New.gradedLatticeBasis` (New/UpperBound/Seesaw/AdmissibleCombinations.lean).

Write $\ell_b(a, u)$ for the scalar on $e_b$: $u$ for odd $s$, and $u a^{-1}$ or $u\bar a$ on the two halves for even $s$ (Lean: `New.lineIdele`).

**Definition (Split squarefree level).** A finite idele $\pi$ is *split squarefree* for $N$ and a finite set $P$ of places if $N = \pi\bar\pi$ in the finite adeles, $\pi$ is a uniformiser at the places of $P$ and a unit elsewhere, and no place of $P$ has its conjugate in $P$.

Lean: `New.Seesaw.IsSplitSquarefree`.

The glued Gram matrix with parameters $(p, q)$ is the identity on $X'$; the vector $y$ has norm $q$ and pairs to $-1$ with $z$ for odd $s$ (for even $s$ it is a unit vector orthogonal to the string); the string vectors pair antidiagonally to $1$, with $-p$ at the middle (Lean: `New.Seesaw.gluedGram`).

**Proposition (The glued basis is unimodular).** If $N = \pi\bar\pi$, then $B^\dagger J B$ is the glued Gram matrix with parameters $(N, 0)$, and it is unimodular over every subring: it is hermitian, and its inverse is the glued Gram matrix with parameters $(0, N)$.

Lean: `New.Seesaw.gram_gradedLatticeBasis_eq_gluedGram`, `New.Seesaw.gluedGram_mul_eq_one`, `New.Seesaw.isUnimodular_gradedLatticeBasis_gram`.

*Proof.* Let $s$ be odd. Since $\bar u u = 1$ and $N$ is fixed by the conjugation,

$$\langle y', y'\rangle = \frac{1}{\pi\bar\pi} + \frac{\bar u u\,\langle z, z\rangle}{N^2} = \frac1N - \frac{N}{N^2} = 0, \qquad \langle y', u z\rangle = \frac{\bar u}{N}\, u\,(-N) = -1,$$

the cross term $\langle y, z\rangle$ being $0$. The string vectors $u e_b$ keep their products, because $\bar u u = 1$. Let $s$ be even. For $2b < s$ and $c = s - 1 - b$, $\langle u a^{-1} e_b, u \bar a e_c\rangle = \bar u\, \bar a^{-1} u \bar a = 1$. This gives the first claim. For the second, multiply the two glued matrices block by block; the only nontrivial block is the $2\times 2$ block on $(y, z)$ for odd $s$, where $\begin{pmatrix} 0 & -1 \\ -1 & -N\end{pmatrix}\begin{pmatrix} N & -1\\ -1 & 0\end{pmatrix} = \begin{pmatrix}1 & 0 \\ 0 & 1\end{pmatrix}$. All entries of both matrices lie in the image of $\mathbb{Z}[N]$, so both lie in every subring. $\square$

### The lattice of a glued basis

Let $\mathsf{Y}$ grade $V$ with $X = X' \sqcup\{y\}$ and a string of length $s$, and let $\Lambda = \Lambda(1)$ be the lattice of the point $1$, spanned by the finite frame of $V$.

**Definition (Spanning the glued lattice).** The frame of $V$ *spans the glued lattice* for $(a, \pi, u)$ if it equals $B(a, \pi, u)\,k$ for some $k \in \mathrm{GL}_\iota(\hat{\mathcal{O}})$.

Lean: `New.Grading.SpansLattice`.

**Theorem (The lattice in coordinates).** Suppose that the frame spans the glued lattice. A finite adelic vector $w$ lies in $\Lambda$ if and only if:

1. $w_x \in \hat{\mathcal{O}}$ for $x \in X'$;
2. $\bar\pi\, w_y \in \hat{\mathcal{O}}$ if $s$ is odd, and $w_y \in \hat{\mathcal{O}}$ if $s$ is even;
3. $\ell_b^{-1} w_b - \delta_b\, \pi^{-1} w_y \in \hat{\mathcal{O}}$ for each $b$, where $\delta_b = 1$ if $b$ is the middle of an odd string and $\delta_b = 0$ otherwise.

In particular $\Lambda$ is graded.

Lean: `New.Grading.SpansLattice.mem_lattice_iff`, `New.Grading.SpansLattice.isGraded` (New/UpperBound/Seesaw/StandardLines.lean).

*Proof.* The vector $w$ lies in $\Lambda$ if and only if its coordinates $c = B^{-1} w$ are integral, because $k$ is invertible over $\hat{\mathcal{O}}$. Write $w = Bc$. The coordinates of $w$ are $w_x = c_x$, $w_y = \bar\pi^{-1} c_y$ (odd $s$) or $c_y$ (even $s$), and $w_b = \ell_b c_b + \delta_b u N^{-1} c_y$. Solve: $c_y = \bar\pi w_y$ and $c_b = \ell_b^{-1}(w_b - \delta_b u N^{-1}\bar\pi w_y) = \ell_b^{-1} w_b - \delta_b \pi^{-1} w_y$, since $\ell_b = u$ at the middle and $N^{-1}\bar\pi = \pi^{-1}$. For the grading: the two vectors that are combined, $y$ and $z$, both have grade $0$, so each grade component of a vector of $\Lambda$ satisfies the three conditions. $\square$

**Corollary (The two lattices are sums of lines).** Suppose that the frame spans the glued lattice. Then:

1. $\Lambda^- = \bigoplus_b \ell_b\hat{\mathcal{O}}\, e_b$;
2. if $\pi$ is split squarefree for $N$, then $\Lambda^+ = \bigoplus_b \ell_b N^{-\delta_b}\hat{\mathcal{O}}\, e_b$;
3. if $\pi$ is split squarefree and $s$ is odd, then $\Lambda \cap X = \{w \in X : w_x \in \hat{\mathcal{O}}\ (x \in X'),\ w_y \in \pi\hat{\mathcal{O}}\}$.

Lean: `New.Grading.SpansLattice.mem_latticeMinus_iff`, `New.Grading.SpansLattice.mem_latticePlus_iff`, `New.Grading.SpansLattice.mem_lattice_and_stringProj_eq_zero_iff`.

*Proof.* (1) Put $w_x = w_y = 0$ in the theorem. (2) The projection of $w \in \Lambda$ to the string has coordinates $w_b$, and $\ell_b^{-1} w_b \in \delta_b\pi^{-1} w_y + \hat{\mathcal{O}}$ with $w_y \in \bar\pi^{-1}\hat{\mathcal{O}}$. So $\ell_b^{-1}w_b \in N^{-\delta_b}\hat{\mathcal{O}}$. Conversely, given $w_b$ with $N^{\delta_b}\ell_b^{-1} w_b$ integral at the middle, put $w_y = \pi\,\ell_b^{-1} w_b$ there, which satisfies condition 2 because $\pi\bar\pi = N$. (3) A vector of $X$ with $w_b = 0$ for all $b$ satisfies condition 3 at the middle if and only if $\pi^{-1} w_y \in \hat{\mathcal{O}}$, which implies condition 2. $\square$

So $\Lambda^+/\Lambda^-$ is $0$ for even $s$, and for odd $s$ it is $N^{-1}\hat{\mathcal{O}}/\hat{\mathcal{O}}$ on the middle line, the discriminant group of the lattice $\Lambda^-$ in the string. The gluing identifies it with the discriminant group $\pi^{-1}\hat{\mathcal{O}}/\hat{\mathcal{O}} \oplus \bar\pi^{-1}\hat{\mathcal{O}}/\hat{\mathcal{O}}$ of $\Lambda \cap X$ on the line of $y$, through $y' = y/\bar\pi + uz/N$.

**Corollary (Vectors of $\Lambda^+$ outside $\Lambda^-$).** Suppose that the frame spans the glued lattice and $\pi$ is split squarefree. If $w \in \Lambda^+ \setminus \Lambda^-$, then $s$ is odd, and there is a place $w_0$ in $P$ or in its conjugate such that the middle coordinate $\ell^{-1} w_z$ has a pole at $w_0$ and, for every $w' \in \Lambda^+$, there is $c \in \hat{\mathcal{O}}$ with $\mathbf{1}_{w_0}(w' - cw) \in \Lambda^-$.

Lean: `New.Grading.SpansLattice.odd_and_exists_place_of_notMem_latticeMinus`, `New.Grading.SpansLattice.exists_pole_of_notMem_latticeMinus`, `New.Grading.SpansLattice.exists_place_generates_of_notMem_latticeMinus`.

*Proof.* By the two descriptions the lattices differ only on the middle line of an odd string, by the factor $N^{-1}$. So $s$ is odd, and $\ell^{-1}w_z \in N^{-1}\hat{\mathcal{O}}\setminus\hat{\mathcal{O}}$ has a pole at a place $w_0$ where $N$ is not a unit, that is, $w_0 \in P$ or $\bar w_0 \in P$. There $N$ is a uniformiser, so $N^{-1}\hat{\mathcal{O}}_{w_0}/\hat{\mathcal{O}}_{w_0}$ is the residue field, of dimension one, and $\ell^{-1}w_z$ generates it. Choose $c$ with $\ell^{-1} w'_z \equiv c\,\ell^{-1}w_z$ modulo $\hat{\mathcal{O}}_{w_0}$. The other lines are the same in $\Lambda^+$ and $\Lambda^-$. $\square$

### The lines in the basis $\mathfrak{e}^i$

In [Bessel periods](/chapter/bessel-periods/) the string is written as $E[\mathfrak{e}]/(\mathfrak{e}^s)$, with $\mathfrak{e}^i = p_i e_i$ and $p_i$ a power of the constant $c$ of the grading, times $-N$ in negative grade. A string vector $\sum_i t_i \mathfrak{e}^i$ is written $\mathrm{str}(t)$ (Lean: `New.Grading.stringSum`). The standard lattices use the scale $u = (a/\bar a)^{\lfloor (s+2)/2\rfloor}$, and then the lines become fractional ideals generated by explicit ideles.

**Definition.** $\mathfrak{l}_i = a^{s-i}\bar a^{-1-i}\hat{\mathcal{O}}$, the fractional ideal of the idele $a^{s-i}\bar a^{-1-i}$.

Lean: `New.powerIdele`.

**Theorem (The lines in powers).** Suppose that the frame spans the glued lattice for $(a, \pi, (a/\bar a)^{\lfloor (s+2)/2\rfloor})$, and that the constant $c$ of the grading has the valuations of $a\bar a$ at every finite place. Then:

1. $\mathrm{str}(t) \in \Lambda^-$ if and only if $t_i \in \mathfrak{l}_i$ for $2i < s$ and $t_i \in N^{-1}\mathfrak{l}_i$ for $2i \geq s$;
2. if $\pi$ is split squarefree, $\mathrm{str}(t) \in \Lambda^+$ if and only if $t_i \in \mathfrak{l}_i$ for $2i + 1 < s$ and $t_i \in N^{-1}\mathfrak{l}_i$ for $2i + 1 \geq s$.

Lean: `New.Grading.SpansLattice.stringSum_mem_latticeMinus_iff`, `New.Grading.SpansLattice.stringSum_mem_latticePlus_iff`.

*Proof.* The coordinate of $\mathrm{str}(t)$ at $e_i$ is $p_i t_i$. So the condition of the corollary is $\ell_i^{-1} p_i t_i \in N^{-\delta_i}\hat{\mathcal{O}}$. With the given scale, $\ell_i$ is $a^{s-i}\bar a^{-1-i}$ times a power of $a\bar a$ (Lean: `New.lineIdele_divStar_pow`), and $p_i$ is $c^{e_i}$ times $-N$ in negative grade, with $e_i = i - \lfloor s/2\rfloor$ or $i - \lfloor (s-1)/2\rfloor$. Since $c$ has the valuations of $a\bar a$, the powers of $a\bar a$ cancel, which is the bookkeeping of `New.Grading.lineIdele_inv_mul_stringSum_mem_iff`. What is left is $t_i \in \mathfrak{l}_i$, times $N^{-1}$ in negative grade, times $N^{-\delta_i}$ at the middle. In (1) $\delta_i$ does not occur. In (2) the middle index of an odd string, $2i + 1 = s$, moves from the first range to the second. $\square$

The point of the scale is the next theorem. Let $\mathsf{Y}'$ grade $V'$ with a string of length $s - 1$, and let $\mathrm{sh}$ be the finite shift $V \to V'$ (Lean: `New.Grading.stringMapFin`): it kills $X$ and $e_{s-1}$ and sends $\mathfrak{e}^i$ to $\mathfrak{e}'^i$ for $i < s - 1$, the map $T$ of [Bessel periods](/chapter/bessel-periods/) at the finite places.

**Theorem (The shift of the standard lattices).** Let the frames of $V$ and $V'$ span the glued lattices for $(a, \pi, (a/\bar a)^{\lfloor (s+2)/2\rfloor})$ and $(a, \pi, (a/\bar a)^{\lfloor (s+1)/2\rfloor})$, let $\pi$ be split squarefree for $N$, and let $\mathsf{Y}$ and $\mathsf{Y}'$ have the same constant $c$, with the valuations of $a\bar a$. Then

$$\mathrm{sh}(\Lambda^+) = a\, \Lambda'^-.$$

Lean: `New.Grading.SpansLattice.map_stringMapFin_latticePlus`.

*Proof.* For $s - 1$ the ideals are $\mathfrak{l}'_i = a^{s-1-i}\bar a^{-1-i}\hat{\mathcal{O}} = a^{-1}\mathfrak{l}_i$. By part (1) of the last theorem for $\mathsf{Y}'$, $a\Lambda'^-$ consists of the $\mathrm{str}'(t)$ with $t_i \in \mathfrak{l}_i$ for $2i < s - 1$ and $t_i \in N^{-1}\mathfrak{l}_i$ for $2i \geq s - 1$, for $i < s - 1$. By part (2) for $\mathsf{Y}$ these are exactly the conditions on $t_i$, $i < s - 1$, for $\mathrm{str}(t) \in \Lambda^+$, and $\mathrm{sh}$ forgets $t_{s-1}$. $\square$

### The standard lattices of the tower

The data of [the data and its sizes](/chapter/data-and-sizes/) give the ideles: $a = \alpha/\overline{\varpi_M}$, where $\alpha$ is the finite idele of the Weil data and $\varpi_M$ generates the ideal $(\bar\pi_0\bar\pi_1)$ of norm $M = p_0p_1$ and is $1$ away from the chosen places (Lean: `New.Data.ideleA`, `New.Data.chosenIdele`); $\pi = \pi_N$, the principal idele of an integer with $\pi_N\bar\pi_N = N$ (Lean: `New.Data.piNIdele`); and the scale $u_k = (a/\bar a)^{\lceil (2\varrho + 2 - k)/2\rceil}$ (Lean: `New.Data.latticeScale`).

**Theorem (The tower has standard lattices).** For $k \leq 2\varrho + 1$:

1. the constant $c = -(jM\delta_E)^{-1}$ of the grading $\mathsf{Y}_k$ has the valuations of $a\bar a$ at every finite place;
2. the frame of $Y_k$ spans the glued lattice for $(a, \pi_N, u_k)$.

Lean: `New.Data.v_gradingY_genericConst_eq_ideleA_mul_star`, `New.Data.spansLattice_gradingY` (New/UpperBound/Seesaw/LevelIdeles.lean).

*Proof.* (1) The Weil data fix the order of $j\alpha\bar\alpha$ at each finite place to be minus the order of the different of $E$, which $\delta_E$ generates; so $j\alpha\bar\alpha\delta_E$ is a unit at every finite place. The idele $\alpha\bar\alpha$ has the valuations of $a\bar a M$ (Lean: `New.Data.v_alpha_mul_star_eq_ideleA_norm_mul_M`), because $\varpi_M\overline{\varpi_M}$ has the valuations of $M$. So $jM\delta_E\, a\bar a$ is a unit at every finite place, and $c^{-1} = -jM\delta_E$ has the valuations of $(a\bar a)^{-1}$. (2) The frame of $Y_k$ is built in [the objects of the upper bound](/chapter/upper-bound-objects/), and the source compares it with the glued basis through the index equivalence of $\mathsf{Y}_k$. Since $s_k = 2\varrho + 1 - k$, the scale $u_k$ is $(a/\bar a)^{\lfloor (s_k+2)/2\rfloor}$, as the theorems above require. $\square$

So the theorems of this section apply to each pair $\mathsf{Y}_k$, $\mathsf{Y}_{k+1}$, with the same constant $c$, and $\mathrm{sh}(\Lambda_k^+) = a\Lambda_{k+1}^-$.

### The glued level

The definite part $X_k$ of $\mathsf{Y}_k$ has its own unitary group, embedded in $G_k$ by the grading (Lean: `New.Grading.inclXFin`). Which finite points $h$ of $U(X)$ preserve the glued lattice? For even $s$ every integral $h$ does. For odd $s$ the gluing imposes a congruence on the last row.

**Theorem (The glued level).** Suppose that the frame spans the glued lattice and that $\pi$ is split squarefree for $N$ and $P$.

1. There is an integral matrix $R$ such that for every finite unitary $h$ on $X$, in the coordinates of the frame, $\iota(h) - 1 = R^\dagger M_h R$, where $M_h = h - 1$ for even $s$, and for odd $s$, $M_h$ is $h - 1$ with its last row divided by $\pi$ and its last column divided by $\bar\pi$.
2. If $h$ is integral and its last row is congruent to that of $1$ modulo $\pi$, then $\iota(h)$ lies in the stabiliser $J^\circ$ of the standard lattice.
3. If in addition $h$ is congruent to $1$ at a family of places $w_i$ none of which lies in $P$ or in its conjugate, then so is $\iota(h)$.

Lean: `New.Grading.exists_inclXFin_sub_one_eq`, `New.Grading.inclXFin_mem_stdLevel`, `New.Grading.inclXFin_mem_levelOf` (New/UpperBound/Seesaw/GluedLevel.lean).

*Proof.* (1) In rational coordinates $\iota(h)$ is $h$ on $X$ and $1$ on the string, so its matrix is $1 + A^\dagger(h-1)A$, where $A$ is formed by the rows of the frame inverse indexed by $X$. Write the frame as $Bk$ with $k \in \mathrm{GL}_\iota(\hat{\mathcal{O}})$. The rows of $B^{-1}$ indexed by $X$ are those of the identity, except that for odd $s$ the row of $y$ carries the factor $\bar\pi$ (the coordinate $c_y = \bar\pi w_y$ of the theorem on the lattice in coordinates). Moving this factor into the middle gives $A = DR$ with $R$ the rows of $k$ indexed by $X$, which are integral,; the factors at $y$ give the scaling of $h - 1$ by $\pi^{-1}$ on the last row and $\bar\pi^{-1}$ on the last column.

(2) We must show that $M_h$ is integral. Its entries off the last row and column are those of $h - 1$. The last row: $(h-1)_{y,x}/\pi$ is integral because of the congruence. The last column: $h$ is unitary, so $h^{-1} = h^\dagger$, and $h^{-1}$ satisfies the same congruence, since the congruence group modulo $\pi$ on the last row is a group. So $(h-1)_{x,y} = \overline{(h^{-1}-1)_{y,x}} \in \bar\pi\hat{\mathcal{O}}$. The corner: $(h-1)_{y,y}$ lies in $\pi\hat{\mathcal{O}}$, and, by the same argument for $h^{-1}$, in $\bar\pi\hat{\mathcal{O}}$. Since no place of $P$ has its conjugate in $P$, the ideals $\pi\hat{\mathcal{O}}$ and $\bar\pi\hat{\mathcal{O}}$ are coprime, so $(h-1)_{y,y} \in \pi\bar\pi\hat{\mathcal{O}}$, as required by the two scalings. By (1), $\iota(h) - 1$ is integral, so $\iota(h)$ preserves $\hat{\mathcal{O}}^\iota$ and lies in $J^\circ$.

(3) At a place $w_i$ outside $P$ and its conjugate, $\pi$ is a unit, so $M_h \equiv 0$ at $w_i$ if $h \equiv 1$ there, and then $\iota(h) - 1 = R^\dagger M_h R \equiv 0$. An element of $J^\circ$ lies in the level at the $w_i$ if and only if every entry of $g - 1$ has valuation less than $1$ there (Lean: `New.mem_levelOf_bot`). $\square$
