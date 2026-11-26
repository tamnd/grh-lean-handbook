---
title: The global term
lean:
  - New/Congruences/Selmer/SelmerData.lean
decls:
  - New.Selmer.length_torsionBy_pi_quot_le
  - New.Selmer.span_range_smul_single_eq_top
  - New.Selmer.length_torsionBy_characterModule_le
  - New.Selmer.smul_apply_eq_zero_of_mem_conjDualHom
  - New.Selmer.congruenceTerm_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The global term

This section proves the source's one bound for the global term: if a single element $g$ acts on $T$ and on $T^{*c}$ by scalars, then $\mathrm{glob}(T)$ is at most $n$ times the valuation of the difference of the two scalars. The file MainSummands of [Stickelberger systems and the twisting theorem](/chapter/twisting-theorem/) applies it to the main summands. All results are in the last part of [SelmerData.lean](lean:New/Congruences/Selmer/SelmerData.lean#L626).

In the Greenberg-Wiles formula the global terms are $H^0(E, W)$ and $H^0(E, W^*)$. Here the dual Selmer group is compared with $G$-maps $W \to W^{*c}$ instead, by [reciprocity at conjugate primes](/chapter/tied-selmer-groups/#reciprocity-at-conjugate-primes). The global term is small when $W$ and $W^{*c}$ have no common constituent.

### Torsion

For an $O$-module $X$ and $\varepsilon \in O$, write $X[\varepsilon]$ for the elements killed by $\varepsilon$ (`torsionBy`).

**Lemma.** Over a discrete valuation ring $O$, $\mathrm{len}\, (O/a)^n[\varepsilon] \leq n \cdot v(\varepsilon)$ for all $a, \varepsilon \in O$.

Lean: `New.Selmer.length_torsionBy_pi_quot_le` (New/Congruences/Selmer/SelmerData.lean).

*Proof.* The torsion $(O/a)^n[\varepsilon]$ is the kernel of multiplication by the scalar matrix $\varepsilon \cdot 1$ on $(O/a)^n$. The kernel bound of [lengths and determinants](/chapter/fitting-ideals/#lengths-and-determinants) (`New.length_ker_le_addVal_det`) bounds its length by $v(\det(\varepsilon \cdot 1)) = n\, v(\varepsilon)$. If $\varepsilon = 0$, the right side is $\infty$ and there is nothing to prove. $\square$

**Lemma.** Let $\rho \colon \Gamma \to M_n(O)$ be a monoid homomorphism whose values span $M_n(O)$. Then for every $a$ and every index $i$, the vectors $\rho(g) e_i$, $g \in \Gamma$, span $(O/a)^n$.

Lean: `New.Selmer.span_range_smul_single_eq_top` (New/Congruences/Selmer/SelmerData.lean).

*Proof.* Let $X$ be the span. Since $\rho(g)\rho(k) e_i = \rho(gk) e_i$, the span $X$ is stable under each $\rho(g)$. It contains $e_i = \rho(1) e_i$, whose coordinate $i$ is $1$. By the lemma on stable submodules of [Selmer data, tied Selmer groups and Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma) (`New.Selmer.eq_top_of_stable_of_isUnit`), $X = (O/a)^n$. $\square$

**Lemma.** Let $O$ be the ring of integers of a finite extension of $\mathbb{Q}_\ell$, and let $X$ be a finite $O$-module. Then $\mathrm{len}\, X^*[\varepsilon] \leq \mathrm{len}\, X[\varepsilon]$, where $X^* = \mathrm{Hom}(X, \mathbb{Q}/\mathbb{Z})$.

Lean: `New.Selmer.length_torsionBy_characterModule_le` (New/Congruences/Selmer/SelmerData.lean).

*Proof.* A character $\chi$ with $\varepsilon \chi = 0$ satisfies $\chi(\varepsilon m) = 0$ for all $m$, so it factors through $X/\varepsilon X$. So $X^*[\varepsilon]$ lies in the image of $(X/\varepsilon X)^*$. A finite abelian group and its character group have the same order, and $X/\varepsilon X$ has the order of $X[\varepsilon]$, since both are the cokernel and the kernel of the same endomorphism of a finite group. The lengths of finite $O$-modules of the same order are equal, since the length is the exponent of the order of the residue field in the order. $\square$

### The bound

**Lemma.** Let $g \in G$ act on $T$ by the scalar $\alpha$ and let $(g^c)^{-1}$ act by $\alpha'$. Then every $\eta \in \mathrm{Hom}_G(W_a, W_a^{*c})$ and every $u \in W_a$ satisfy
$$\big(\alpha - \mathrm{cyc}(g^c)\, \alpha'\big)\, \eta(u) = 0.$$

Lean: `New.Selmer.smul_apply_eq_zero_of_mem_conjDualHom` (New/Congruences/Selmer/SelmerData.lean).

*Proof.* The defining identity of $\mathrm{Hom}_G(W_a, W_a^{*c})$ at $g$ reads $\eta(\alpha u)(m) = \eta(u)(\mathrm{cyc}(g^c)\, \alpha' m)$. The left side is $\eta(u)(\alpha m)$, since $\eta$ is linear and $O$ acts on $W_a^*$ through its argument. So $\eta(u)$ kills $(\alpha - \mathrm{cyc}(g^c)\alpha') m$ for every $m$. $\square$

**Theorem (Bound for the global term).** Let the matrices $\rho(g)$ span $M_n(O)$, and let $g$ act on $T$ by $\alpha$ and $(g^c)^{-1}$ by $\alpha'$. Then
$$\mathrm{glob}(\rho) \leq n \cdot v\big(\alpha - \mathrm{cyc}(g^c)\, \alpha'\big).$$

Lean: `New.Selmer.congruenceTerm_le` (New/Congruences/Selmer/SelmerData.lean).

*Proof.* Let $a \neq 0$ and $\Delta = \alpha - \mathrm{cyc}(g^c)\alpha'$. Fix an index $i$ and the vector $e = e_i \in W_a$. Consider the evaluation $\eta \mapsto \eta(e)$ from $\mathrm{Hom}_G(W_a, W_a^{*c})$ to $W_a^*$.

1. Its image lies in $W_a^*[\Delta]$, by the lemma above.
2. It is injective. Let $\eta(e) = 0$. For $k \in G$ the defining identity gives $\eta(\rho(k) e)(m) = \eta(e)(\cdots) = 0$. So $\eta$ vanishes on the vectors $\rho(k) e$, which span $W_a$ by the second lemma. So $\eta = 0$.

Hence
$$\mathrm{len}\, \mathrm{Hom}_G(W_a, W_a^{*c}) \leq \mathrm{len}\, W_a^*[\Delta] \leq \mathrm{len}\, W_a[\Delta] \leq n\, v(\Delta),$$
by the third and the first lemma. Take the supremum over $a$. $\square$

**Remark (Formalization).** The bound is $\infty$ when $\Delta = 0$. This happens for $g = \gamma_*$: it acts by $\zeta$, its conjugate $(\gamma_*^c)^{-1}$ acts by $\zeta$ as well, and $\mathrm{cyc}(\gamma_*^c) = 1$ because $\gamma_*^c$ is inertial at a place prime to $\ell$. So the theorem needs another element. The field `congruenceTerm_ne_top` of a Selmer datum is a hypothesis, and this theorem is the tool that the next chapter uses to verify it.

### Example: rank one

Let $n = 1$, so $T = O(\psi)$ for a character $\psi \colon G \to O^\times$. Write $\Delta_g = \psi(g) - \mathrm{cyc}(g^c)\psi((g^c)^{-1})$. The theorem gives $\mathrm{glob}(\psi) \leq v(\Delta_g)$ for every $g$, since every element acts by a scalar. For rank one the bound is sharp. The character module of $O/a$ is isomorphic to $O/a$ as an $O$-module, and a linear map $\eta \colon O/a \to (O/a)^*$ is determined by $y = \eta(1)$. The condition on $\eta$ at $g$ says $\Delta_g\, y = 0$. So $\mathrm{Hom}_G(W_a, W_a^{*c}) \cong (O/a)[I]$ for the ideal $I$ generated by all $\Delta_g$, of length $\min(v(a), \min_g v(\Delta_g))$, and
$$\mathrm{glob}(\psi) = \min_{g \in G} v(\Delta_g).$$
It is $\infty$ exactly when $\psi(g)\,\psi(g^c) = \mathrm{cyc}(g)$ for all $g$, that is, when $\psi$ is conjugate self-dual up to the cyclotomic character. In that case this chapter gives no bound for the tied Selmer groups of $\psi$.
