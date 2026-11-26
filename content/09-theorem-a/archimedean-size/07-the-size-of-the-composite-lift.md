---
title: The size of the composite lift
lean:
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.weylNormSq_restrictedChain_le
  - New.Data.weylNormSq_compositeLift_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The size of the composite lift

This section proves the theorem of the chapter. The first theorem bounds the restricted chain of a weak chain datum. The second passes to the composite lift of a chain datum by the expansion of the glued tensor. Both bounds have the exponent
$$\beta = \mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p + fa\log^3 b .$$

### What the proof uses

The proof multiplies four bounds. All four are proved earlier in the book or in this chapter.

1. *A chain as a plain sum* ([a chain of lifts as a plain sum](/chapter/chain-valuation/#a-chain-of-lifts-as-a-plain-sum)). Let $\Psi$ be a weak chain datum, and let $\psi = \mathrm{CC}(1, \Psi, v, m)\varphi$ be the combination of the chains of $m$ lifts of $\varphi$, with the translates $v_t$ of the vacuum as data. For a tuple $g = (g_j)_{j\le m}$,
$$\psi(g_m) = \sum_{c\in\prod_{j<m}\Gamma_j\backslash G_j/K_j}\ \sum_{t\in\operatorname{supp}\Psi}\Psi(t)\,\mathrm{KP}(v_t, \varphi, \mathrm{cp}(c, g), m),$$
where $\mathrm{KP}$ is the product of the $m$ kernels applied to $\varphi$ at the points $\mathrm{cp}(c, g)$ (`New.Data.chainCombination_eq_sum`). Here $K_j$ is the level of $X_j$ (`New.Data.levelX`).
2. *Products of kernels* (same section). If each kernel multiplies a size by at most $r_j \ge 0$, and the values of $\varphi$ have size at most $B_0$, then $\mathrm{KP}$ has size at most $(\prod_{j<m}r_j)B_0$ (`New.apply_kernelProduct_le_prod_mul`).
3. *The restriction* ([the restriction to $Y_m$](/chapter/chain-valuation/)). For every $\sigma$, every form $\psi$ on $X_m$ and every $y \in G_f(Y_m)$,
$$\|\sigma\circ(\mathrm{res}\,\psi)(y)\|^2_{\mathrm W} \le \exp\Bigl(x^{70} - \Bigl(\sum_\tau n_\tau\Bigr)\log N\Bigr)\,\|\sigma\circ\psi(\mathrm{diag}(y,1))\|^2_{\mathrm W}$$
(`New.Data.weylNormSq_restrictToY_le`). The exponent of branching is $\sum_\tau n_\tau = \#\Phi_a\,a - fm\Delta/2$ ([weights and lift diagrams](/chapter/upper-bound-objects/#weights-and-lift-diagrams); `New.Data.sum_branchExponent`).
4. *The coefficients* ([columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift)). A weak chain datum for the trivial twist has admissible coefficients with size $\exp(x^{60})$. So $\sum_{t\in\operatorname{supp}\Psi}|\sigma(\Psi(t))| \le \exp(x^{60})$ for every $\sigma$ (the field `sum_norm_le` of `New.Data.IsWeakChainDatum`).

The triangle inequality for the Gram norm, $\|\sigma\circ\sum_a\xi_a\|_{\mathrm W} \le \sum_a\|\sigma\circ\xi_a\|_{\mathrm W}$, is from [Weyl modules](/chapter/weyl-modules/) (`New.sqrt_weylNormSq_sum_le`).

### The restricted chain

**Theorem (Size of the restricted chain).** Let $\Psi$ be a weak chain datum for the trivial twist, $\sigma \in \mathrm{Aut}(\mathbb C)$, $\varphi$ a source form and $B$ real. Assume $\|\sigma\circ\varphi(g)\|^2_{\mathrm W} \le e^B$ for every $g \in G_f(X_0)$. Then for every $y \in G_f(Y_m)$,
$$\|\sigma\circ(\mathrm{res}\,\mathrm{CC}(1,\Psi,v,m)\varphi)(y)\|^2_{\mathrm W} \le \exp(B + \beta).$$

Lean: `New.Data.weylNormSq_restrictedChain_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Write $\|\xi\| = \|\sigma\circ\xi\|_{\mathrm W}$ for short, and $\psi = \mathrm{CC}(1,\Psi,v,m)\varphi$. Let $g$ be the tuple with $g_m = \mathrm{diag}(y, 1)$ and $g_j = 1$ for $j < m$.

*Step 1: one term.* Put
$$R = \prod_{j<m}\exp\bigl(x^{50} + \tfrac12\mathrm{rowSize}_j\bigr)\cdot\sqrt{e^B}.$$
By the theorem on one kernel of Section 5, the kernel of stage $j$ multiplies the norm by at most $r_j = \exp(x^{50} + \tfrac12\mathrm{rowSize}_j)$, for every translate $v_t$ and every pair of points. The values of $\varphi$ have norm at most $\sqrt{e^B}$. By the bound on products of kernels, $\|\mathrm{KP}(v_t,\varphi,p,m)\| \le R$ for every $t$ and every tuple $p$.

*Step 2: the number of classes.* For $j < m$, the level $K_j$ contains the principal level $K(\pi_M\pi_N)$ (`New.Data.principalLevel_le_levelX`), and $\#X_j = n_j \le n_m$. By the corollary on classes at the data of Section 3, $\#(\Gamma_j\backslash G_j/K_j) \le \exp(x^{30})$. So the tuples $c$ number at most $\exp(x^{30})^m$.

*Step 3: the value of the chain.* By the plain sum and the triangle inequality, used twice,
$$\|\psi(\mathrm{diag}(y,1))\| \le \sum_c\sum_{t\in\operatorname{supp}\Psi}|\sigma(\Psi(t))|\,\|\mathrm{KP}(v_t,\varphi,\mathrm{cp}(c,g),m)\| \le \exp(x^{30})^m\cdot\exp(x^{60})\cdot R .$$

*Step 4: the restriction.* By the bound for the restriction and the exponent of branching,
$$\|(\mathrm{res}\,\psi)(y)\|^2 \le \exp\Bigl(x^{70} - \bigl(\#\Phi_a\,a - fm\tfrac\Delta2\bigr)\log N\Bigr)\bigl(\exp(mx^{30} + x^{60})R\bigr)^2 .$$
The logarithm of the right side is
$$x^{70} - \#\Phi_a\,a\log N + fm\tfrac\Delta2\log N + 2\bigl(mx^{30} + x^{60} + mx^{50}\bigr) + \sum_{j<m}\mathrm{rowSize}_j + B .$$

*Step 5: the exponent.* By the theorem on the rows of all lifts of Section 5, $\sum_j\mathrm{rowSize}_j \le \mathrm{chainSize} + \tfrac12 fa\log^3 b$. By the theorem on the exponent of the chain of Section 6,
$$\mathrm{chainSize} - \#\Phi_a\,a\log N \le \mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p + 32fa\log b .$$
So the logarithm is at most
$$B + \mathrm{main} - m\cdot\mathrm{rem} + 2\sum_p\mathrm{gain}_p\log p + \tfrac12 fa\log^3 b + E,$$
with
$$E = x^{70} + fm\tfrac\Delta2\log N + 2\bigl(mx^{30} + x^{60} + mx^{50}\bigr) + 32fa\log b .$$

*Step 6: the rest.* The table of sizes gives $E \le \tfrac12 fa\log^3 b$. The largest terms are $32fa\log b$ and $fm\tfrac\Delta2\log N \le f\cdot 2\sqrt x\cdot r^8\cdot 60\sqrt x\log b$, which is at most $120x\cdot r^8\cdot f\log b$, of degree $41$ in $x$ times $f\log b$. Both are far below $fa\log^3 b$, since $a \ge x^{999}x_1$. The powers $x^{70}$, $x^{60}$, $mx^{50}$ and $mx^{30}$ are below $a$. So the logarithm is at most $B + \beta$. $\square$

**Theorem (Size of the composite lift).** Let $\Psi$ be a chain datum for the trivial twist, $\sigma \in \mathrm{Aut}(\mathbb C)$, $\varphi$ a source form and $B$ real, with $\|\sigma\circ\varphi(g)\|^2_{\mathrm W} \le e^B$ for every $g \in G_f(X_0)$. Then for every $y \in G_f(Y_m)$,
$$\|\sigma\circ(B_{1,\Psi}\varphi)(y)\|^2_{\mathrm W} \le \exp(B + \beta).$$

Lean: `New.Data.weylNormSq_compositeLift_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* By [expanding the gluing](/chapter/chain-valuation/#expanding-the-gluing) (`New.Data.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq`), there is a weak chain datum $\Psi'$ for the trivial twist with $B_{1,\Psi}\varphi = \mathrm{res}\,\mathrm{CC}(1,\Psi',v,m)\varphi$ for every source form $\varphi$. Apply the theorem on the restricted chain to $\Psi'$. $\square$

This is the third input of Theorem A, stated in [the three inputs](/chapter/theorem-a-plan/#the-three-inputs). [The proof of Theorem A](/chapter/proof-of-theorem-a/) uses it with $B$ from the size of the source form.

### Remarks

**Remark (Formalization).** The theorem is only for the trivial twist $\vartheta = 1$. The reason is the coefficient bound of step 4. The field `sum_norm_le` of an admissible combination holds under a proposition $p$, and for a weak chain datum $p$ is the statement $Q = \emptyset$ about the set $Q$ of exceptional places of the twist. For the trivial twist $Q$ is empty by definition, and the proof passes `rfl`. For another twist the bound on $\sum_t|\sigma(\Psi(t))|$ is not available from the definition. The theorem has no hypothesis of integrality on $\varphi$ or on $\Psi$. It holds for every automorphism $\sigma$ of $\mathbb C$, also discontinuous ones, since every bound it uses is uniform in $\sigma$. The point $g$ of the proof is `Pi.mulSingle m (borderU y)`, where `borderU` is the embedding $y \mapsto \mathrm{diag}(y,1)$ along the relabelling `lastIndexEquiv`.

**Remark (The factor 2 on the gain).** The exponent $\beta$ contains $2\sum_p\mathrm{gain}_p\log p$, with the factor $2$. The factor comes from the squared norm: the prime sum $s_{\mathrm{fin}}$ is $\sum_p 2s_p\log p$, while the gain is defined with $s_p$. The register of findings records this as F-099 and asks in Q-20 whether it is a real loss. The source answers it in `New.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean). There the composite lift is multiplied by the rational number $c_B = \prod_p p^{-g_p}$, with $g_p = \lfloor\mathrm{gain}_p - \mathrm{err}_p\rfloor$ (`New.Data.invGainFactor`). The squared norm of $c_B\psi$ is $c_B^2\|\psi\|^2$, and $2\log c_B \le -2\sum_p\mathrm{gain}_p\log p + 2\,\mathrm{err}_0 + 2b$ (`New.Data.log_invGainFactor_le`). So the two terms $2\sum_p\mathrm{gain}_p\log p$ cancel exactly. The factor $2$ is the square of the norm, not a loss.

### The bound as a balance

The exponent $\beta$ splits into the following terms.

| term | origin | size |
|---|---|---|
| $\mathrm{main}$ | rows of length $\kappa(\tau)$, less their prime sums | main term |
| $-m\cdot\mathrm{rem}$ | first rows, less their prime sums and the expected value | small by the main inequality |
| $2\sum_p\mathrm{gain}_p\log p$ | the divisibility asked of the chain | given back on the other side |
| $fa\log^3 b$ | slacks, classes, coefficients, restriction, Stirling | error |

The restriction to $Y_m$ is the only step that makes the norm smaller. It removes $\#\Phi_a\,a\log N$, and this is the reason for the choice of $N$. Without the restriction, the first rows would cost $m\,\#\Phi_a\,a(w + G)$, far more than the error term.
