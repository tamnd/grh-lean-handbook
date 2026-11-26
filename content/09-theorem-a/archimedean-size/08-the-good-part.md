---
title: The good part
lean:
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.coe_lowerChainAtLevel_apply
  - New.Data.lowerChain_goodProjTranslate_apply
  - New.Data.goodProjTranslate_mem_integralForms
  - New.Data.normSqAt_goodProjTranslate_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The good part

The argument does not apply the lattice bound to the lift $\iota(z)$ of a form $z$ on $Y_0$. It applies the bound to the lift of the good part $|\mathsf G|\,e_0\,s\,z$. This section proves the two facts about the good part that the rest of the argument needs. Passage to the good part keeps integrality, and it changes the size of the lift by a factor of at most $\exp(x^{99})$. The first fact is cited in [two bounds in one lattice](/chapter/integral-target-forms/). The second is cited in [Theorem A](/chapter/theorems-a-b-c/) and in [the plan of Theorem A](/chapter/theorem-a-plan/).

### The objects

The section uses these objects. Each is stated in an earlier chapter.

- The group $\mathsf G = \prod_w \mathrm{GL}_r(\mathbb F_w)$, with $w$ over the chosen places above $p_0$ and $p_1$, and the good idempotent $e_0 \in \mathbb C[\mathsf G]$. The element $e_0$ is a central projection ([labels and the good idempotent](/chapter/upper-bound-objects/#labels-and-the-good-idempotent); Lean: `New.Data.chosenGL`, `New.Data.e₀`).
- The composite lift $\iota_\vartheta$ of the $m$ lifts from forms of principal level on $Y_0$ to algebraic forms on $Y_m$, for a tame character $\vartheta$ ([rows and the lower chain](/chapter/upper-bound-objects/); Lean: `New.Data.lowerChain`). The map $\iota_\vartheta^{\mathrm{lev}}$ is the same map with values in the forms of a fixed level and character ([the target forms and the chain](/chapter/integral-target-forms/); Lean: `New.Data.lowerChainAtLevel`).
- The group $\mathsf G$ acts on the principal forms on $Y_0$ (`New.Data.principalRep`). For $s \in \mathsf G$, the good part of the translate is $|\mathsf G|\,e_0\,s\,z$. It is the Lean definition `New.Data.goodProjTranslate`, which lies in a file of Volume 10.
- The lemma on translates. For $s \in \mathsf G$, the lift $\iota_\vartheta(s z)$ is the right translate of $\iota_\vartheta(z)$ by an element $\tilde s$ of the standard level on $Y_m$ ([rows and the lower chain](/chapter/upper-bound-objects/); Lean: `New.Data.lowerChain_principalRep`). In Lean, $\tilde s$ is `firstBlockLift ϑ s`.
- The $p$-adic gauge, the integral forms at a place $j : \mathbb C \to \mathbb C_l$, and the class sum $\|\varphi\|_\sigma^2$ of the squared Gram norms of the values $\sigma(\varphi(g))$ ([the $p$-adic gauge](/chapter/automorphic-forms/); Lean: `New.integralForms`, `New.LevelPlaces.LevelForm.normSqAt`).
- Two facts on central projections of a finite group $H$ ([finite characters](/chapter/congruence-subgroups/)). If $e$ is a central projection, then $|H|\,e$ is a character, so its values are algebraic integers (`New.IsCentralProj.isChar_card_mul_coeff`). Each coefficient has $|e(h)| \le 1$ (`New.IsCentralProj.norm_coeff_le_one`).

### The value of the good part

**Lemma (The lift at a level is the lift).** The form $\iota_\vartheta^{\mathrm{lev}}(z)$, seen as an algebraic form on $Y_m$, is $\iota_\vartheta(z)$.

Lean: `New.Data.coe_lowerChainAtLevel_apply` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* The map $\iota_\vartheta^{\mathrm{lev}}$ is defined as $\iota_\vartheta$ together with the proofs that the value has the given level and character. Forgetting the proofs gives back $\iota_\vartheta(z)$. $\square$

**Lemma (Value of the good part).** Let $s \in \mathsf G$, let $z$ be a form of principal level on $Y_0$ and let $g \in G_f(Y_m)$. Then
$$\iota_\vartheta\bigl(|\mathsf G|\,e_0\,s\,z\bigr)(g) = \sum_{t\in\mathsf G}|\mathsf G|\,e_0(t)\;\iota_\vartheta(z)\bigl(g\,\widetilde{ts}\bigr).$$

Lean: `New.Data.lowerChain_goodProjTranslate_apply` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Write $e_0 = \sum_{t\in\mathsf G}e_0(t)\,t$. The action of $\mathbb C[\mathsf G]$ is linear, so
$$|\mathsf G|\,e_0\,s\,z = \sum_{t\in\mathsf G}|\mathsf G|\,e_0(t)\,(ts)z .$$
The lift $\iota_\vartheta$ is linear, so $\iota_\vartheta(|\mathsf G|e_0sz) = \sum_t|\mathsf G|e_0(t)\,\iota_\vartheta((ts)z)$. By the lemma on translates, $\iota_\vartheta((ts)z)$ is the right translate of $\iota_\vartheta(z)$ by $\widetilde{ts}$. So its value at $g$ is $\iota_\vartheta(z)(g\,\widetilde{ts})$. $\square$

The value is thus a sum of $|\mathsf G|$ values of $\iota_\vartheta(z)$, at right translates of $g$ by elements of the standard level. The coefficients are the numbers $|\mathsf G|e_0(t)$. Both theorems of this section use only these two facts about the coefficients: they are algebraic integers, and they have absolute value at most $|\mathsf G|$ under every automorphism $\sigma$ of $\mathbb C$.

### Integrality

**Theorem (The good part keeps integrality).** Let $l$ be a prime, $j : \mathbb C \to \mathbb C_l$ a ring homomorphism, $c \in \mathbb C$ and $s \in \mathsf G$. Let $z$ be a form of principal level on $Y_0$. If $c\,\iota_\vartheta^{\mathrm{lev}}(z)$ is integral at $j$, then $c\,\iota_\vartheta^{\mathrm{lev}}(|\mathsf G|\,e_0\,s\,z)$ is integral at $j$.

Lean: `New.Data.goodProjTranslate_mem_integralForms` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* A form $\psi$ is integral at $j$ if the gauge of each value is at most $1$: for every $g$, the vector $j(\psi(g))$ moved by $g^{-1}$ has coordinates of $l$-adic absolute value at most $1$. Write $\gamma(g, v)$ for the gauge of a vector $v$ at the point $g$. Fix $g \in G_f(Y_m)$.

*Step 1.* By the two lemmas above, the value at $g$ is
$$c\,\iota_\vartheta(|\mathsf G|e_0sz)(g) = \sum_{t\in\mathsf G}|\mathsf G|e_0(t)\cdot c\,\iota_\vartheta(z)\bigl(g\,\widetilde{ts}\bigr).$$

*Step 2.* The gauge is ultrametric: if each term of a finite sum has gauge at most $1$, the sum has gauge at most $1$ (`New.weylGauge_sum_le`). So it suffices to bound each term.

*Step 3.* The gauge of a scalar multiple is $|j(\lambda)|_l$ times the gauge (`New.weylGauge_smul`). The number $\lambda_t = |\mathsf G|e_0(t)$ is a value of a character, so it is an algebraic integer. Its image under $j$ has $|j(\lambda_t)|_l \le 1$, since an algebraic integer is a root of a monic polynomial with integer coefficients (`norm_le_one_of_isIntegral`).

*Step 4.* The element $\widetilde{ts}$ lies in the standard level, and the standard level is contained in the local level at $l$ (`stdLevel_le_localLevel`). The gauge does not change under right translation by an element that is integral above $l$ (`New.weylGauge_mul_of_mem_integralAbove`). So the gauge of $c\,\iota_\vartheta(z)(g\widetilde{ts})$ at $g$ equals the gauge of the same vector at $g\widetilde{ts}$. This is at most $1$, by the hypothesis at the point $g\widetilde{ts}$.

*Step 5.* So each term has gauge at most $|j(\lambda_t)|_l\cdot 1 \le 1$. By Step 2, the sum has gauge at most $1$. $\square$

The constant $c$ plays no role in the proof. In the application, $c$ is the gain factor $l^{-g_l}$, and the hypothesis is the integrality of the chain datum after the gain.

### Size

**Theorem (Size of the good part).** Let $\sigma$ be an automorphism of $\mathbb C$, $s \in \mathsf G$, $B \in \mathbb R$, and $z$ a form of principal level on $Y_0$. Suppose that for every $g \in G_f(Y_m)$,
$$\bigl\|\sigma\circ\iota_1(z)(g)\bigr\|^2_{\mathrm W} \le e^B ,$$
where $\iota_1$ is the composite lift for the trivial twist. Then
$$\bigl\|\iota^{\mathrm{lev}}_1\bigl(|\mathsf G|\,e_0\,s\,z\bigr)\bigr\|^2_\sigma \le \exp\bigl(x^{99} + B\bigr).$$

Lean: `New.Data.normSqAt_goodProjTranslate_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Put $h = |\mathsf G|$.

*Step 1: the coefficients.* The image $\sigma(e_0)$ is again a central projection of $\mathbb C[\mathsf G]$, as $\sigma$ is a ring automorphism. By the second fact on central projections, $|\sigma(e_0(t))| \le 1$ for every $t$.

*Step 2: one value.* Fix $g$ and put $v_t = \iota_1(z)(g\,\widetilde{ts})$. By the hypothesis at the point $g\widetilde{ts}$, $\|\sigma\circ v_t\|_{\mathrm W} \le \sqrt{e^B}$. The Gram norm is homogeneous, so
$$\bigl\|\sigma\circ(h\,e_0(t)\,v_t)\bigr\|_{\mathrm W} = h\,|\sigma(e_0(t))|\,\|\sigma\circ v_t\|_{\mathrm W} \le h\sqrt{e^B} .$$
By the value of the good part and the triangle inequality for the Gram norm (`New.sqrt_weylNormSq_sum_le`), the sum of the $h$ terms has
$$\Bigl\|\sigma\circ\iota^{\mathrm{lev}}_1(|\mathsf G|e_0sz)(g)\Bigr\|_{\mathrm W} \le h\cdot h\sqrt{e^B} = h^2e^{B/2}.$$

*Step 3: the classes.* The level of the target forms for the trivial twist is $\mathrm{levelOf}$ of a family of places. At each place above $p_0$ or $p_1$, the ideal of the place contains $\pi_M$, so it contains $\pi_M\pi_N$. The family has no other places for the trivial twist. So the level contains the principal level $K(\pi_M\pi_N)$ (`principalLevel_le_levelOf`). As $\#Y_m \le n_m$ (`New.Data.card_Y_le`), the corollary on classes at the data of Section 3 gives at most $\exp(x^{30})$ classes.

*Step 4: the class sum.* The number $\|\varphi\|^2_\sigma$ is a sum over the classes of the squared Gram norms of the values. If the square root of each term is at most $T$, the sum is at most the number of classes times $T^2$ (`classSum_le_card_mul_sq`). With $T = h^2e^{B/2}$ this gives
$$\|\iota^{\mathrm{lev}}_1(|\mathsf G|e_0sz)\|^2_\sigma \le \exp(x^{30})\,h^4\,e^B .$$

*Step 5: the order of the group.* It remains to show $\exp(x^{30})h^4 \le \exp(x^{99})$. The group $\mathsf G$ is a product of groups $\mathrm{GL}_r(\mathbb F_w)$, and $r \le rt$. The map $g \mapsto \mathrm{diag}(g, 1)$ embeds $\mathrm{GL}_r$ in $\mathrm{GL}_{rt}$ at each place. So $h$ divides the order $O$ of $\prod_w\mathrm{GL}_{rt}(\mathbb F_w)$ ([chains and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels); Lean: `New.Data.chosenGroupOrder`, `card_GL_dvd_chosenGroupOrder`). As $O \ge 1$, this gives $h \le O = \exp(\log O)$. The order is at most $\prod_w q_w^{(rt)^2}$, and the norms $q_w$ have product $M^f$. So
$$\log O \le f(rt)^2\log M \le x^{12}\cdot r^2t^2\cdot 23\log b ,$$
which is far below $x^{98}$ by the table of sizes. Hence $x^{30} + 4\log O < x^{99}$, and $\exp(x^{30})h^4 \le \exp(x^{30} + 4\log O) \le \exp(x^{99})$. $\square$

**Remark (Formalization).** Four points of the Lean proofs are technical.

- The file sets `Fintype.ofFinite` as a local instance of low priority. The finite group $\mathsf G$ then has a `Fintype` instance, so the sums over $t \in \mathsf G$ are `Finset.sum` over `univ`. The proof of the size bound switches between `Fintype.card` and `Nat.card` with `Nat.card_eq_fintype_card`.
- The lemma on the lift at a level holds by `rfl`. It is a definitional unfolding, and it carries no content.
- The divisibility $h \mid O$ gives $h \le O$ only because $O \ne 0$. The source uses `Fin.pos'` with the instance `NeZero` that the definition of `chosenGroupOrder` derives. The hypothesis $r \le rt$ of `card_GL_dvd_chosenGroupOrder` comes from the size automation (`nat_le_of_hasLogBound`), and the final inequality $x^{30} + 4\log O < x^{99}$ comes from `le_of_hasLogBound` and `lt_of_hasLogBound`.
- The size bound is stated for the trivial twist only. The size bound of Section 7 has the same restriction, so this costs nothing.

### An example of the good part

Take $\mathsf G = \mathrm{GL}_1(\mathbb F_3) = \{\pm1\}$, so $h = 2$. Let $e_0 = \tfrac12(1 - (-1))$, the projection onto the sign part. Then $h\,e_0(1) = 1$ and $h\,e_0(-1) = -1$. For a form $z$ the good part of $sz$, with $s = 1$, is $z - (-1)z$. Its lift has the value
$$\iota(z)(g) - \iota(z)(g\,\widetilde{-1})$$
at $g$. If $\iota(z)$ is integral, each of the two values is integral, and so is the difference. If each value of $\iota(z)$ has Gram norm at most $e^{B/2}$, the difference has Gram norm at most $2e^{B/2}$. The theorem uses the weaker bound $h^2e^{B/2} = 4e^{B/2}$, since it bounds each coefficient $|h\,e_0(t)|$ by $h$ and not by $1$. The loss is a factor $h^4$ in the squared norm, which is absorbed in $\exp(x^{99})$.
