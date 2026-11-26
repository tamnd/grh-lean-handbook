---
title: The criterion on the grid
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean
decls:
  - New.Data.norm_gridLevelGen
  - New.Data.exists_eq_zero_of_orthogonal_gridLevelForms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The criterion on the grid

This section applies the vanishing criterion of Section 5 to $V = Y_0$ and $Z = \tilde Y^0_0 = Y_0 \oplus \langle 1\rangle$. All sizes come from the data $D$. The result is the first statement of Step 3 of the sketch.

### Background for the grid

- The deep level is the principal level of $\mathfrak b = \varpi^{b}$, with $\varpi$ = `D.piM` the generator of the product of the chosen places, $\varpi\bar\varpi = M$, and $b$ = `D.natB` ([seesaw squares and grid paths](/chapter/seesaw-squares/)).
- The forms $\mathcal F_{\mathfrak b}$ = `D.gridLevelForms 0` are the forms on $\tilde Y^0_0$ of the kernel `D.gridKernel true 0 0 true`, that is of the parameter $-\tilde l$ with $\tilde l$ = `D.gridParam true 0 0 0`, and of level $J(\mathfrak b)$ ([seesaw squares and grid paths](/chapter/seesaw-squares/)).
- The principal forms `D.principalForms` on $Y_0$ are the forms of type $l$ = `D.paramW` and level $J_M$ = `D.chosenLevel` ([seesaw squares and grid paths](/chapter/seesaw-squares/)).
- Restriction theorem ([IsSteep.exists_volume_le_mul_norm_integral_dsCoeff](/decl/New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff/)): let $l$ be steep for $(X, M, B)$ with $M$ even and $B \ge 1$, and $-l'$ steep for $(X, M+1, B)$. Let both have a large gap $h$, entries at most $L$, and let $\beta \ge 10^{12}$ bound $\#(n\oplus 1) + \# n + L$ and $\#(n\oplus 1)^4(6B)^{2M+2}$, and $h \ge 10^{30}((\#(n\oplus 1) + \# n)^2\log\beta)^3$. Then some $y$ with $\|y\|^2 \le \beta$ has $\mathrm{vol}\{g : \|g - 1\| \le 1\} \le \beta^{20(\#(n\oplus1) + \# n)^2}\,\big|\int c_l(g)\,\overline{c_{l'}(y^{-1}(g\oplus 1)y)}\,dg\big|$.
- Steep parameters: Section 2 gives bijections $e$ and $e'$ for which the parameters of $Y_0$ and $\tilde Y^0_0$ are steep with $B = \kappa_0$ = `D.liftWeight 0 w` and $M = 2\varrho + 2$ ([exists_isSteep](/decl/New.Data.exists_isSteep/)).
- Logarithmic bounds: the data compare two sizes through their logarithmic bounds. Each inequality between sizes below is of this kind (`New.Data.le_of_hasLogBound`, [the data and their sizes](/chapter/data-and-sizes/)).

### The modulus of the generator

**Lemma.** For every infinite place $w$, $|\Phi_w(\mathfrak b)| = \sqrt M^{\,b}$.

Lean: `New.Data.norm_gridLevelGen` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* As $\varpi\bar\varpi = M$ and $\Phi_w$ commutes with complex conjugation on a CM field, $|\Phi_w(\varpi)|^2 = \Phi_w(M) = M$. So $|\Phi_w(\varpi)| = \sqrt M$, and $|\Phi_w(\varpi^b)| = \sqrt M^{\,b}$. $\square$

### The criterion on $Y_0$

**Theorem (Forms of level $J_M$ on $Y_0$).** There is a real point $g$ of the unitary group of $\tilde Y^0_0$ with this property. Let $y$ be a principal form on $Y_0$. If

$$\langle y,\ \varphi((\cdot \oplus 1)\,g)\rangle = 0 \quad \text{for every } \varphi \in \mathcal F_{\mathfrak b},$$

then $y = 0$.

Lean: `New.Data.exists_eq_zero_of_orthogonal_gridLevelForms` (New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean).

*Proof.* We apply the corollary of Section 5 with $V = Y_0$, the parameter $l$ of $Y_0$, the parameter $l' = -\tilde l$ of $\mathcal F_{\mathfrak b}$, and these sizes:

$$\beta = \sqrt M^{\,\lceil x\rceil}, \quad A = r^4, \quad L = \lceil 20 b\rceil, \quad N = 20(\#(Y_0\oplus 1) + \# Y_0)^2, \quad m = \beta^{20A(f+1)}.$$

Here $x$ is the length of the prime sum and $r$ the rank of $Y_0$.

*Step 1: the sizes.* The conditions $8(n+1)^2 < A$, $N < A$, $2f(n+1) + 2 \le A$, $M\kappa^2 \le \beta$, $2000(n + L + 1)^6 \le \beta$ and $f \le \beta$ are inequalities between sizes of the data. Each follows from the logarithmic bounds. For instance $n + 1 \le r + 1$ and $A = r^4$, so $8(n+1)^2 < A$ once $r$ is large. Here the rank has the bound $\log\#Y_0 \le 5\log x + 3$, and $\beta$ has the lower bound $\log\beta \ge 3\cdot 20\log b/2$. The condition $\beta^{20A(f+1)} \le m$ holds with equality.

For the last condition, Lemma 1 gives $|\Phi_w\mathfrak b| = \sqrt M^{\,b}$. Also

$$m^{3n+2} = \sqrt M^{\,\lceil x\rceil\cdot 20A(f+1)(3n+2)}.$$

As $\sqrt M \ge 1$, the power $k \mapsto \sqrt M^{\,k}$ increases. So it suffices that $\lceil x\rceil\,20A(f+1)(3n+2) \le b$, which is a size inequality of the data.

*Step 2: gaps and entries.* The parameter $l$ of $Y_0$ has a gap $D.\mathrm{gap} = 2r^8$ ([the data and their sizes](/chapter/data-and-sizes/)), and $4A = 4r^4 \le 2r^8$, so it has a large gap for $4A$. The parameter $\tilde l$ has the same gap. The negative of a parameter with a large gap has a large gap, so $-\tilde l$ has a large gap for $2A$. Every entry of the grid parameters has absolute value at most $\lceil 20 b\rceil = L$ (`New.Data.abs_gridParam_le`), and $|-a| = |a|$.

*Step 3: the pairing bound.* Fix a place $w$. The corollary asks for a point $\omega_w$ with $\|\omega_w\|^2 \le \beta$ and

$$\mathrm{vol}\{r : \|r - 1\| \le 1\} \le \beta^N\Big|\int c_{l_w}(r)\,\overline{c_{l'_w}(\omega_w^{-1}(r\oplus 1)\omega_w)}\,dr\Big|.$$

This is the restriction theorem with $n = Y_0$, $\varepsilon$ the signs of $Y_0$, the parameters $l_w$ and $l'_w$, $B = \kappa_0$, $M = 2\varrho + 2$, $h = r^7$ and $\beta$ as above. Its hypotheses hold.

- $M = 2\varrho + 2$ is even.
- $l_w$ is steep for $e$ by Section 2. The signs of $\tilde Y^0_0$ are those of $Y_0$ followed by $1$ (`New.Data.gridSigns_true_zero`). Along this identity $\tilde l_w$ is steep for $e'$, and $-l'_w = -(-\tilde l_w) = \tilde l_w$.
- $1 \le B$, and the gaps $h = r^7 \le 2r^8$ hold for both.
- The entries are at most $L$ by Step 2.
- $10^{12} \le \beta$ and $\#(Y_0 \oplus 1) + \# Y_0 + L \le \beta$ are size inequalities.
- For the bound $\#(Y_0\oplus 1)^4(6\kappa_0)^{2(2\varrho + 2) + 2} \le \beta$, both $\#(Y_0 \oplus 1)$ and $6\kappa_0$ are at most $\sqrt M$. So the left side is at most $\sqrt M^{\,4 + 2(2\varrho+2) + 2}$, and the exponent is at most $\lceil x\rceil$.
- $10^{30}((\#(Y_0\oplus1) + \#Y_0)^2\log\beta)^3 \le r^7$, with $\log\beta = \lceil x\rceil\log\sqrt M$, is a size inequality.

The exponent of the restriction theorem is $20(\#(Y_0\oplus1) + \#Y_0)^2 = N$. So the theorem gives $\omega_w$.

*Step 4.* The corollary of Section 5 now gives a point $g$ such that every form $y$ of type $l$ and level $J_M$ on $Y_0$, orthogonal to all $\varphi((\cdot\oplus 1)g)$ for $\varphi$ of type $l'$ and level $J(\mathfrak b)$, is zero. The forms of type $l'$ and level $J(\mathfrak b)$ on $\tilde Y^0_0$ are the space $\mathcal F_{\mathfrak b}$, and the principal forms are of type $l$ and level $J_M$. $\square$

**Remark (Formalization).** The source writes the embedding $x \mapsto x \oplus 1$ into the group of $\tilde Y^0_0$ through `G.reindex` along the identity of the index type and the equality `D.gridSigns_true_zero` of the signs. The point $g$ is given by an existential. It comes from `choose` in the corollary and from the restriction theorem, so it is not explicit. No size in this section is a junk value. Each size is positive, as $M \ge 1$, $r \ge 1$ and $b \ge 1$.

### Example

Take $\#Y_0 = r = 3$ and two lifts, as in the example of Section 2. Then $\varrho = 0$ and the steep block has $M = 2$ entries, $A = 81$ and $N = 20(4 + 3)^2 = 980$. The condition $N < A$ fails. So the theorem does not apply to such small data. The sizes of the data make $r$ large: they give $N \le 20(2r + 1)^2 < r^4$ once $r \ge 90$, using $\#Y_0 \le r$. The last size condition is the reason for the deep level: the exponent $20A(f+1)(3n + 2)\lceil x\rceil$ of $\sqrt M$ in $m^{3n+2}$ must be at most $b$.

### Where the criterion is used

Section 7 combines the theorem with the transposition identity of the first path. The result is a restriction map $\mathrm{res}^\flat$ from $\mathcal F_{\mathfrak b}$ onto the principal forms on $Y_0$. The point $g$ of the theorem is the real point of this map.
