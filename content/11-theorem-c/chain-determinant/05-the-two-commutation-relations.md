---
title: The two commutation relations
lean:
  - New/Determinant/Chain/ChainNorms.lean
decls:
  - New.Data.negCount_gridSigns_add
  - New.Data.negCount_gridSigns_add_lt
  - New.Data.card_gridIndex_add_card_gridIndex
  - New.Data.card_gridIndex_le_quotientPair_negWeight
  - New.Data.gridChar_mul_leftPairChar
  - New.Data.exists_squareLaw_triangleTransposedLift
  - New.Data.exists_triangleLift_triangleTransposedLift_comm
  - New.Data.exists_squareLaw_triangleReversedLift
  - New.Data.HasAbsUpToNormPower.of_norm_sq_mul_card_pow_eq_one
  - New.Data.exists_triangleLift_triangleReversedLift_comm
  - New.Data.reversalScalar
  - New.Data.exists_conj_modKernel_leftPair_eq
  - New.Data.exists_inner_triangleTransposedLift_eq
  - New.Data.exists_inner_triangleReversedLift_eq
  - New.Data.exists_triangleLift_reversalScalar_eq
  - New.Data.exists_inner_triangleLift_eq
  - New.Data.exists_triangleTransposedLift_adjoint_comm
  - New.Data.exists_isTriangle
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The two commutation relations

This section proves that the lifts and the descents of Section 4 form a triangle in the sense of Section 2, with the square moduli $\rho_{i+1,\,i+n+2}$. The work is in two relations for each square. The first relation says that the square commutes up to a scalar $\beta$. The second is the adjoint law. Both come from the one square identity of [the seesaw squares](/chapter/seesaw-squares/).

The square at $(i, n)$ has the four corners
$$F_{i,n+1} \xrightarrow{\ a\ } F_{i,n+2}, \qquad F_{i,n+1} \xrightarrow{\ d\ } F_{i+1,n}, \qquad F_{i,n+2} \xrightarrow{\ d\ } F_{i+1,n+1}, \qquad F_{i+1,n} \xrightarrow{\ a\ } F_{i+1,n+1}.$$
It exists for $i + n + 1 < m$. Both lifts $a_{i,n+1}$ and $a_{i+1,n}$ add the block $i + n + 2$, so they have the same character.

### The cited identity

We state the result of [the seesaw squares](/chapter/seesaw-squares/) that this section uses, in the form we need. Let $U_1, U_2, A, A'$ be four hermitian spaces. Send a form on $U_1$ to $U_2$ in two ways: through $A$ (a lift, then a transposed lift), with data the indicator functions of the two blocks of a matrix $x$; and through $A'$ (a transposed lift, then a lift), with the blocks of a matrix $y$. Assume that the four arrows are edges, and:

1. the number $N$ of negative signs of $U_1 \oplus U_2$ is that of $A$ and $A'$ together;
2. $\mathrm{rank}\,A = \mathrm{rank}\,A' + 2s$;
3. $2N + 2 \leq \mathrm{rank}(U_1 \oplus U_2) \leq 2\mu + 2N$ at every infinite place;
4. the characters of the two families multiply to $\mathrm{rankTwist}(\nu^{-1})$, and $\nu$ is tame for a modulus $\mathfrak{m}$ with weight $\mu$ and residue character $\chi$.

Then there are $C \in \mathbb{R}$ and $\kappa \in \mathbb{C}$, and for each twist some $c \neq 0$ with $|c|^2 = C\,L_*(\text{places of }\mathfrak{m}, \nu, s)$, such that for every form $f$ and every linear form $\ell$ the functions $x \mapsto \ell(\Theta_x f)$ and $y \mapsto \ell(\Theta'_y f)$ satisfy the square law with the constant $\kappa/c$ (`New.Exchange.one_square_identity_of_isEdgeFamily`). The square law says: both functions transform by $\chi \circ \det$, and $\sum \Psi' L' = (\kappa/c)\sum \Psi L$ for matched $\Psi, \Psi'$ (`New.Exchange.SquareLaw`).

Two consequences of the square law, from the same chapter, finish the passage to arbitrary data. Let $\mathrm{next}(\Psi)$ be the datum on the next column that has the value $\Psi(-\eta)/\#\mathrm{Mat}$ at $\binom{\eta\ s}{0\ 1}$ and $0$ elsewhere (`New.Exchange.nextDatum`). Then:

- the law gives $\#\mathrm{GL}_a \sum_y \Psi(y) L'(\dots) = (\kappa/c)\,\#\mathrm{GL}_{n+b}\sum_x \mathrm{next}(\Psi)(x) L(\dots)$ (`New.Exchange.SquareLaw.sum_eq_nextDatum`);
- for a primitive additive character $\psi$ and a primitive $\chi$, the same identity holds for the Fourier transforms of $\bar\Psi$ and $\overline{\mathrm{next}(\Psi)}$, with a constant $\gamma$ in place of the group orders, where $|\gamma|^2\,\#R^{k} = 1$ for an explicit $k$ (`New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`).

### The numerical conditions

**Lemma (Signs and ranks of a square).** For all $i, n$:

1. the diagonals of the square have the same number of negative signs: $N(V_{i,n+1}) + N(V_{i+1,n+1}) = N(V_{i,n+2}) + N(V_{i+1,n})$;
2. $N(V_{i,n+1}) + N(V_{i+1,n+1}) < \mathrm{rank}\,V_{i,n+1}$;
3. $\mathrm{rank}\,V_{i,n} + \mathrm{rank}\,V_{i,n+2} = 2\,\mathrm{rank}\,V_{i,n+1}$;
4. for $1 \leq j \leq m$, $\mathrm{rank}\,V_{i,j}$ is at most the negative weight $j\Delta$ of the quotient pair of distance $j$.

Lean: `New.Data.negCount_gridSigns_add`, `New.Data.negCount_gridSigns_add_lt`, `New.Data.card_gridIndex_add_card_gridIndex`, `New.Data.card_gridIndex_le_quotientPair_negWeight` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* 1. The added blocks have sign $+1$. A base entry has the sign $(-1)^{e}$, where $e = o + a + \min(a - o, n)$ for the offset $o$, the column $n$ and an integer $a$ fixed by the number of the entry ([parameters and grids](/chapter/upper-bound-objects/)). Compare the parities of the exponents entry by entry. 2. Only base entries can be negative, so each count is at most $r + z$. The rank is $r + z + (n+1)(t - z)$, and $r + z < t - z$ since $r + 6 \leq t$. 3. The ranks $r + z + n(t - z)$ form an arithmetic progression in $n$. 4. $r + z + j(t - z) \leq j\,(2\,\mathrm{halfGap}) = j\Delta$, by $k + t + 1 \leq \mathrm{halfGap}$ and $r + 6 \leq t$. $\square$

**Lemma (Characters of a square).** Let $1 \leq n + 1 \leq m$ and let $p, q, s$ be finite sets with $\#p + \#q = \#s$ even. The character of the lift that adds the block $n + i + 2$, on a space of rank $\#p$, times the left pair character $\lambda_i$ on a space of rank $\#q$, is
$$\big(\nu_{n+1}\,\vartheta^{n+1}\big)\,\upsilon^{\#s/2},$$
where $\nu_{n+1}$ is the character of the quotient pair of distance $n + 1$. For $z = \text{true}$, $\vartheta$ is replaced by $1$.

Lean: `New.Data.gridChar_mul_leftPairChar` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* The first character is $\mu_{n+i+2}\,\vartheta^{n+i+2}\,\upsilon^{\lfloor \#p/2 \rfloor}$. The second is $\mu_{i+1}^{-1}\vartheta^{-(i+1)}\upsilon^{-\lfloor \#q/2 \rfloor}\upsilon^{\#q}$. By the lemma that the quotient pair is a quotient (Section 3), $\mu_{n+i+2}/\mu_{i+1} = \nu_{n+1}$. The twists give $\vartheta^{n+1}$. The exponents of $\upsilon$ add to $\#s/2$, since $\#s$ is even. In additive notation this is a comparison of the exponents of each basic character. $\square$

### The first relation

**Proposition (Square law of a descent square).** Let $i + n + 1 < m$, and let $\Phi_0, \Phi_1$ be left pairs at $(i, n)$ and $(i, n+1)$. Let $(\nu_{n+1}\vartheta^{n+1})^{-1}$ be tame for $\mathfrak{m}$ with the weight of the quotient pair and the residue character $\chi_\vartheta$. Then there are $C$ and $\kappa$, and for each $\vartheta$ some $c \neq 0$ with
$$|c|^2 = C\,L_*\big(\text{places of }\mathfrak{m}, (\nu_{n+1}\vartheta^{n+1})^{-1}, t - z\big),$$
such that the two composites around the square, read through a linear form $\ell$, satisfy the square law with the constant $\kappa/c$.

Lean: `New.Data.exists_squareLaw_triangleTransposedLift` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Apply the cited identity with $U_1 = V_{i,n+1}$, $U_2 = V_{i+1,n+1}$, $A = V_{i,n+2}$ and $A' = V_{i+1,n}$. The arrows through $A$ are $a_{i,n+1}$ and the descent with $\Phi_1$. The arrows through $A'$ are the descent with $\Phi_0$ and $a_{i+1,n}$. They are edges by Section 4. The conditions are the lemma on signs and ranks: part 1 gives condition 1; $\mathrm{rank}\,V_{i,n+2} = \mathrm{rank}\,V_{i,n} + 2(t - z)$ gives condition 2 with $s = t - z$; parts 2, 3 and 4 give condition 3. The lemma on characters gives condition 4. $\square$

**Theorem (First commutation relation).** Let $i + n + 1 < m$ and let $\Phi_0, \Phi_1$ be left pairs at $(i, n)$ and $(i, n+1)$. There is a function $\beta$ of the twist such that for every $\vartheta$, every datum $\Psi$ at column $n$, every $y \in F_{i,n+1}$ and every $x \in F_{i+1,n+1}$,
$$N_n\,\big\langle x, a_{i+1,n}(d_{\Phi_0,\Psi}\,y)\big\rangle = \overline{\beta(\vartheta)}^{-1}\,N_{n+2}\,\big\langle x, d_{\Phi_1,\mathrm{next}(\Psi)}(a_{i,n+1}\,y)\big\rangle,$$
where $N_n = \#\mathrm{GL}(\mathrm{index}(0, n), O/\mathfrak{m})$. For $z = \text{false}$, $\beta$ has absolute value $\rho_{i+1,\,i+n+2}$ up to a norm power.

Lean: `New.Data.exists_triangleLift_triangleTransposedLift_comm` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Let $\nu$ be the quotient pair of distance $n + 1$. By the proposition on tame twists of a pair (Section 3), $(\nu\vartheta^{n+1})^{-1}$ is tame for $\mathfrak{m}$. Take $C$, $\kappa$ and $c(\vartheta)$ from the last proposition, and put $\beta(\vartheta) = \overline{c(\vartheta)/\kappa}$. Then $\overline{\beta}^{-1} = \kappa/c$.

Expand both descents in point data: $d_{\Phi,\Psi} = \sum_\eta \Psi(\eta)\,d_{\Phi,1_\eta}$. Apply the first consequence of the square law, with $\ell = \langle x, \cdot\rangle$ and the weights $\Psi$. It gives
$$N_n\sum_\eta \Psi(\eta)\,\langle x, a_{i+1,n}(d_{\Phi_0,1_\eta}y)\rangle = \frac{\kappa}{c}\,N_{n+2}\sum_\xi \mathrm{next}(\Psi)(\xi)\,\langle x, d_{\Phi_1,1_\xi}(a_{i,n+1}y)\rangle.$$
The inner product is linear in the second variable, so this is the claim.

For $z = \text{false}$: by Section 3, $\rho_{i+1,\,i+n+2}(\vartheta) = \Lambda(\nu, t, \vartheta^{n+1})$. Also $|\beta|^2 = |c|^2/|\kappa|^2 = (C/|\kappa|^2)\,L_*(\text{places of }\varpi Q, (\nu\vartheta^{n+1})^{-1}, t)$. The proposition that products of $L$-values have absolute value a product of ratios (Section 3) applies with $e = 1$. $\square$

**Remark (Formalization).** If $\kappa = 0$, then $\beta = 0$ and $\overline{\beta}^{-1} = 0$ in Lean. The relation then says only that the left side is $0$. The relation $M(\beta, \rho)$ still holds, with $C/|\kappa|^2 = 0$ (finding F-037). Section 2 shows that such a $\beta$ makes the chain $0$, and Section 6 excludes this by injectivity.

### Reversal and the adjoint of a descent

The second relation needs the adjoint of a descent. In the twisted triangle $z = \text{false}$ the source computes it by reversing the theta kernel.

**Definition (Reversal scalar).** For the modulus $\mathfrak{m}$ of the triangle, the reversal scalar at column $n$ is the central element `flipScalar` of the finite adelic group of a node in column $n$.

Lean: `New.Data.reversalScalar` (New/Determinant/Chain/ChainNorms.lean).

**Lemma (Reversal of a left pair).** Let $V = V_{i+1,n}$ and $W = V_{i,n+1}$ with the left pair characters. There is $\tau$ with $\tau(\vartheta) \neq 0$ and absolute value $1$ up to a norm power, such that the conjugate of the kernel of $(V, W)$ with $\Psi$ and $\Phi$ at $(g, h)$ is $\tau(\vartheta)$ times the kernel of $(W, V)$ with the Fourier transform of $\bar\Psi$ and the signed transpose of $\bar\Phi$, at $(h, g u)$, where $u$ is the reversal scalar.

Lean: `New.Data.exists_conj_modKernel_leftPair_eq`, `New.Data.HasAbsUpToNormPower.of_norm_sq_mul_card_pow_eq_one` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* The reversal law for theta kernels (`New.Exchange.exists_conj_modKernel_eq_swap`, Lib/Weil/DualPair/Flip.lean) gives such a $\tau$ with $|\tau|^2\,\#(O/\mathfrak{m})^{k} = 1$ for a fixed $k$. This gives $\tau \neq 0$. By rule 5 of Section 3 with $e = 1$ and the constant $1$, $\tau$ has absolute value $1$ up to a norm power. $\square$

**Proposition (Adjoint of a descent).** Let $\Phi$ be a left pair and $\Phi'$ a reversed pair at $(i, n)$, $z = \text{false}$. There are functions $c, c'$ of absolute value $1$ up to a norm power such that for all $\vartheta$, $\Psi$, $x \in F_{i,n+1}$ and $y \in F_{i+1,n}$,
$$\langle d_{\Phi,\Psi}\,x, y\rangle = c(\vartheta)\,\big\langle x, d'_{\Phi',\hat\Psi}(u^{-1}y)\big\rangle, \qquad \big\langle x, d'_{\Phi',\hat\Psi}(u^{-1}y)\big\rangle = c'(\vartheta)\,\langle d_{\Phi,\Psi}\,x, y\rangle.$$
Here $d'$ is the ascent, $\hat\Psi$ is the Fourier transform of $\bar\Psi$ (`New.Data.fourierDatum`), and $u$ is the reversal scalar.

Lean: `New.Data.exists_inner_triangleTransposedLift_eq`, `New.Data.exists_inner_triangleReversedLift_eq` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* We prove the first identity. Translation by $u^{-1}$ is unitary and $u$ is central, so $\langle d\,x, y\rangle = \langle u^{-1}\cdot d\,x, u^{-1} y\rangle$. The descent $d_{\Phi,\Psi}\,x$ is the integral of $x$ against the kernel of the left pair (Section 4). By the reversal lemma, its conjugate at $g$ is $\tau(\vartheta)\,L(g u)$, where $L$ is the lift of $\bar x$ along the reversed pair with $\hat\Psi$ and the transposed polynomial $Q$. So $\langle d\,x, y\rangle = \tau\,\langle \bar L, u^{-1} y\rangle_{\mathrm{Pet}}$. The edge $\Phi'$ trades $Q$ for $\Phi'$ at the cost of one constant $\kappa$ ([seesaw for periods](/chapter/theta-lifts-seesaw/)). This gives $c = \tau\,\bar\kappa$, which has absolute value $1$ up to a norm power by rules 1 and 4. The second identity has the same proof in the other direction, after writing $\Phi'$ as the signed transpose of the conjugate of a polynomial (`New.Data.exists_flipPoly_map_conj_eq`). $\square$

**Lemma (Lifts and the reversal scalar).** For $i + n < m$ there is $\eta$ with $|\eta| = 1$ such that $a_{i,n}(u_n^{-1}y) = \eta\,u_{n+1}^{-1}\,a_{i,n}(y)$ for every $y \in F_{i,n}$. Every $x \in F_{i,n+1}$ has an adjoint image $x' \in F_{i,n}$ with $\langle a_{i,n}y, x\rangle = \langle y, x'\rangle$ for all $y$.

Lean: `New.Data.exists_triangleLift_reversalScalar_eq`, `New.Data.exists_inner_triangleLift_eq` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* The pair of central scalars acts on the datum of the lift by a value $\eta$ of the character of the pair, so the law for translates of lifts applies, as in the intertwining lemma of Section 4. The spaces of forms are finite dimensional, so the adjoint exists. $\square$

### The second relation

**Proposition (Reversed square).** Let $i + n + 1 < m$, $z = \text{false}$, and let $\Phi_0, \Phi_1$ be reversed pairs at $(i, n)$ and $(i, n+1)$. There is $\gamma$ of absolute value $1$ up to a norm power such that for all $\vartheta$, $\Psi$, $y \in F_{i+1,n}$ and $x \in F_{i,n+2}$,
$$\big\langle x, a_{i,n+1}(d'_{\Phi_0,\hat\Psi}\,y)\big\rangle = \gamma(\vartheta)\,\big\langle x, d'_{\Phi_1,\widehat{\mathrm{next}(\Psi)}}(a_{i+1,n}\,y)\big\rangle.$$

Lean: `New.Data.exists_squareLaw_triangleReversedLift`, `New.Data.exists_triangleLift_triangleReversedLift_comm` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Apply the cited identity with $U_1 = V_{i+1,n}$, $U_2 = V_{i,n+2}$, $A = V_{i+1,n+1}$ and $A' = V_{i,n+1}$. The two middle spaces have the same rank, so $s = 0$. The product $L_*$ of length $0$ is empty, so $|c|^2 = C$ does not depend on $\vartheta$. The signs, ranks and characters are checked as before. This gives the square law with $\kappa/c$.

The modulus $\varpi Q$ is squarefree, and $(\nu\vartheta^{n+1})^{-1}$ is tame for it. So its residue character is primitive, by the lemma that tame characters are primitive (Section 3). The additive character of the modulus is primitive. So the second consequence of the square law applies, with a constant $\gamma_0$ with $|\gamma_0|^2\,\#(O/\mathfrak{m})^k = 1$. Expand both ascents in point data, as in the first relation. This gives the identity with $\gamma = \gamma_0\,\kappa/c$. The factor $\gamma_0$ has absolute value $1$ up to a norm power by rule 5 of Section 3, and $\kappa/c$ has $|\kappa/c|^2 = |\kappa|^2/C$, a constant. By rule 1, $\gamma$ has absolute value $1$ up to a norm power. $\square$

**Theorem (Second commutation relation).** Let $i + n + 1 < m$, $z = \text{false}$, and let $\Phi_0, \Phi_1$ be left pairs at $(i, n)$ and $(i, n+1)$. There is $\kappa$ of absolute value $1$ up to a norm power with the following property. Let $x \in F_{i,n+2}$ and let $x' \in F_{i,n+1}$ satisfy $\langle a_{i,n+1}y, x\rangle = \langle y, x'\rangle$ for every $y$. Then for every $y \in F_{i+1,n}$,
$$\langle d_{\Phi_0,\Psi}\,x', y\rangle = \kappa(\vartheta)\,\big\langle d_{\Phi_1,\mathrm{next}(\Psi)}\,x, a_{i+1,n}\,y\big\rangle.$$

Lean: `New.Data.exists_triangleTransposedLift_adjoint_comm` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Take reversed pairs $\Phi_0', \Phi_1'$ at $(i, n)$ and $(i, n+1)$ (Section 4). Write $A_0, A_1$ for the ascents with $\hat\Psi$ and $\widehat{\mathrm{next}(\Psi)}$, and $y' = u_n^{-1}y$. Then
$$\begin{aligned}
\langle d_{\Phi_0,\Psi}\,x', y\rangle &= c_0\,\langle x', A_0 y'\rangle = c_0\,\langle x, a_{i,n+1}(A_0 y')\rangle = c_0\,\gamma\,\langle x, A_1(a_{i+1,n}\,y')\rangle \\
&= c_0\,\gamma\,\eta\,\langle x, A_1(u_{n+1}^{-1} a_{i+1,n}\,y)\rangle = c_0\,\gamma\,\eta\,c_1\,\langle d_{\Phi_1,\mathrm{next}(\Psi)}\,x, a_{i+1,n}\,y\rangle.
\end{aligned}$$
The first step is the adjoint of a descent at $(i, n)$. The second is the choice of $x'$. The third is the reversed square. The fourth is the lemma on lifts and the reversal scalar. The last is the second identity of the adjoint of a descent at $(i, n+1)$. Put $\kappa = c_0\gamma\eta c_1$. Each factor has absolute value $1$ up to a norm power, and so has $\kappa$ by rule 1. $\square$

### The lifts form a triangle

**Theorem (The lifts form a triangle).** For each grid $z$ there are descents $d_{i,n} : F_{i,n+1} \to F_{i+1,n}$ such that the lifts $a$, the weights $N_n$, the descents $d$ and the embeddings $\epsilon_i$ of the base $B$ form a triangle of size $m$. For $z = \text{false}$ the triangle has the square moduli $\rho_{i+1,\,i+n+2}$ for the relation of absolute value up to a norm power.

Lean: `New.Data.exists_isTriangle` (New/Determinant/Chain/ChainNorms.lean).

*Proof.* Choose a left pair $\Phi_{i,n}$ for each $i + n < m$. For $n = 0$, the theorem on the adjoint of a lift (Section 4) with the point datum gives a datum $\Psi_{i,0}$ with $\langle x, a_{i,0}\,y\rangle = \langle d_{\Phi_{i,0},\Psi_{i,0}}\,x, \nu_* y\rangle$. Define $\Psi_{i,n+1} = \mathrm{next}(\Psi_{i,n})$ by recursion, and $d_{i,n} = d_{\Phi_{i,n}, \Psi_{i,n}}$.

*Squares commute.* The first relation with $\Psi = \Psi_{i,n}$ has the datum $\mathrm{next}(\Psi_{i,n}) = \Psi_{i,n+1}$ on the right. Testing against all $x$ gives the vector identity of Section 2, with $\overline{\beta}^{-1}w_{n+2}$ written as $w_{n+2}/\overline{\beta}$.

*Adjointness.* For $y \in B$ this is the choice of $\Psi_{i,0}$, since $\nu_*\epsilon_i = \epsilon_{i+1}$.

*Return to the base and injectivity.* Let $y \in B$, and let $v \in F_{0,0}$ have $\epsilon_{i+1}v = d_{i,0}(a_{i,0}\,\epsilon_i y)$; it exists since $\epsilon_{i+1}$ is onto. For every $x$,
$$\langle v, x\rangle = \langle \epsilon_{i+1}v, \epsilon_{i+1}x\rangle = \langle d_{i,0}(a_{i,0}\,\epsilon_i y), \nu_*\epsilon_i x\rangle = \langle a_i y, a_i x\rangle,$$
by adjointness. Part 1 of the theorem on the norm of the first lift (Section 4) gives $v \in B$, and $v = 0$ implies $y = 0$. So $d_{i,0}\,a_{i,0}$ maps the copy of $B$ in row $i$ into the copy in row $i+1$, and it is injective there.

*Square moduli for $z = \text{false}$.* The rules of Section 3 give $M(1, 1)$ and the product rule. The first relation gives $\beta$ with $M(\beta, \rho_{i+1,\,i+n+2})$. The second relation, with $x'$ from the lemma on adjoint images, gives the adjoint law with $\kappa$ and $M(\kappa, 1)$. $\square$

**Remark (Formalization).** The descents come from `choose!` over $(i, n)$ with $i + n < m$. Outside this range the chosen left pairs are junk values, and no statement uses them. The data $\Psi_{i,n}$ are defined by `Nat.rec`, so $\Psi_{i,n+1} = \mathrm{next}(\Psi_{i,n})$ holds by definition. The file declares `attribute [-simp] Bool.cond_eq_ite` at line 708 and `attribute [local implicit_reducible]` at line 76.

### Example: the square for $m = 2$

For $m = 2$ there is one square, at $(0, 0)$. It relates $a_{1,0}\,d_{0,0}$ and $d_{0,1}\,a_{0,1}$ on $F_{0,1}$. The pair of the square is the quotient pair of distance $1$, of character $\mu_2/\mu_1$. The relation $L_*$ has length $t$, and $\beta$ has absolute value $\rho_{12}(\vartheta)$ up to a norm power. The reversed square relates the ascent from $F_{1,0}$ to $F_{0,1}$ with $a_{0,1}$, and its constant has no $L$-values.
