---
title: Tame charts
lean:
  - New/Congruences/Lifting/TameCharts.lean
decls: [New.Lift.TameChart, New.Lift.TameChart.exists_z_smul_eq_sum_tameGen, New.Lift.TameChart.aeval_linearFrob_extensionLattice_eq_zero, New.Lift.TameChart.count_constantCoeff_aeval_tameMultiplier_pow_le, New.Lift.TameChart.aeval_tameMultiplier_pow_mul_mem_liftIdeal, New.Lift.TameChart.killsCokernel_of_isKilledBy, New.Lift.exists_normal_fixer_index_coprime, New.Lift.exists_tameChart]
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tame charts

On a ramified chart the different bound $d$ is positive, and the costs of [Section 7](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers) grow with it. If the ramification is tame, an element of inertia gives a cheaper killer. Its cost depends on the degree of a polynomial, not on $d$.

**Definition (Tame chart).** A *tame chart* is a Kummer chart with these data: $\Gamma'$ is normal in $\Gamma$; $p \nmid e$; an element $\varpi \in \overline{\mathbb{Q}}_p$ fixed by $\Gamma'$ with $\varpi^e = p$; an element $s \in \Gamma$ that maps into inertia and whose powers fix $\Lambda$; and $\xi \in \Lambda$ whose residue is a primitive $e$-th root of unity, with $s^kz = \xi^kz$ for all $k$.

Lean: `New.Lift.TameChart` (New/Congruences/Lifting/TameCharts.lean).

For $s$ in inertia, $\beta$ is the operator on $B_{\max} \otimes Y$ that acts as $s$ on the vectors fixed near $1$. *$q$ kills $\beta$ on $Y$* means that $Y$ is potentially crystalline and $q(\beta) = 0$ ([crystalline classes](/chapter/period-rings/)).

**Lemma.** Let $d$ be a tame chart.

1. If $q \in \mathbb{Z}_p[X]$ kills $\beta$ on $L$ and $x \in M$, then $\sum_k q_ks^kx = zy$ for some $y \in A_{\inf}[1/\tau] \otimes L$ with $\mu(\varphi^ny) \in B_{\mathrm{dR}}^+$ for all $n \geq 1$ and all forms $\mu$.
2. If $q$ kills $\beta$ on $Y$, then $q\cdot(X - 1)$ kills $\beta$ on the extension $Y \times C$.
3. If $Q$ is monic and $\nu \leq e$, at most $\deg Q$ of the $k < \nu$ make the residue of $Q(\xi^k)$ zero.
4. If $Q$ kills $\beta$ on the extension, $Q(1) = 0$ and $p^tz^{k+1} \in J_0^r(i)$, then $Q(\xi^{k+1})p^tz^k \in J_0^r(i)$.

Lean: `New.Lift.TameChart.exists_z_smul_eq_sum_tameGen`, `New.Lift.TameChart.aeval_linearFrob_extensionLattice_eq_zero`, `New.Lift.TameChart.count_constantCoeff_aeval_tameMultiplier_pow_le`, `New.Lift.TameChart.aeval_tameMultiplier_pow_mul_mem_liftIdeal` (New/Congruences/Lifting/TameCharts.lean).

*Proof.* (1) For a crystalline form $\mu$, let $\mu_k$ be its conjugate by $s^k$; it is again crystalline, as $\Gamma'$ is normal. Since $q(\beta) = 0$, $\sum_kq_k\mu_k(x) = 0$. So $\mu$ of the sum is $\sum_kq_k(s^k - 1)\mu_k(x)$. The map $s^k - 1$ gives a factor $z$ once the denominators, powers of $E$, are cleared. (2) $\beta - 1$ maps the extension into $B_{\max} \otimes Y$, as $\beta = 1$ on the trivial quotient, and there $q(\beta) = 0$. (3) If the residue of $Q(\xi^k)$ is $0$, then $\bar\xi^k$ is a root of the reduction of $Q$. The powers $\bar\xi^k$, $k < e$, are distinct. A nonzero polynomial has at most $\deg Q$ roots. (4) Lift $(p^tz^{k+1} - ru)$ times the constant of $c$ to $x$, by the lemma on lifts. Write $u = w + zv$ with $w \in \Lambda$. Apply $Q(s)$ to $x$. The element $s^j$ fixes the constant and $w$, and multiplies $z$ by $\xi^j$. So $Q(s)$ sends the multiplier $p^tz^{k+1} - ru$ to $z$ times $Q(\xi^{k+1})p^tz^k - r(\ldots)$; the terms in $w$ cancel because $Q(1) = 0$. By (1), the image of $x$ is $z$ times an element with the standard orders. Cancel the unit $z$ of $W(C^\flat)$. $\square$

**Theorem (Tame killer).** Let $d$ be a tame chart and $S$ a side. Suppose that all jumps of $S$ are at most $n$, that a monic $q$ kills $\beta$ on $Y$, and that $e \leq p^m$, $m(\deg q + 1) \leq \kappa$ and $n + \kappa + 2 < p$. Then $p^\kappa$ kills the cokernel at every letter $i$.

Lean: `New.Lift.TameChart.killsCokernel_of_isKilledBy` (New/Congruences/Lifting/TameCharts.lean).

*Proof.* By [Section 7](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers) there is $\nu$ with $z^\nu \in J_0^{p^{\kappa+1}}(i)$ for all $i$ and $(p-1)\nu \leq e(n + \kappa)$. As $n + \kappa < p - 1$, $\nu < e$. Let $Q = q\cdot(X - 1)$. By (2), $Q$ kills $\beta$ on the extension, and $Q(1) = 0$. Call $k$ *bad* if the residue of $Q(\xi^k)$ is $0$. By (3), at most $\deg q + 1$ of the $k \leq \nu$ are bad, so $m$ times their number is at most $\kappa$.

Go down from $p^0z^\nu$ to $p^tz^0$. At a step from $z^{k+1}$ to $z^k$: if $k + 1$ is not bad, $Q(\xi^{k+1})$ is a unit, and (4) gives $p^tz^k$ at no cost. If $k + 1$ is bad, lower $z$ as in Section 7 at the cost $v_p(k+1) + 1 \leq m$, since $k + 1 < e \leq p^m$. The total cost is at most $\kappa$. At $k = 0$, $p^\kappa \in J_0^{p^{\kappa+1}}(i)$, and Nakayama drops the modulus. $\square$

**Theorem (Tame charts exist).** Let $\Gamma \to G_p$ be onto, let $f \geq 1$ with $p \nmid f$, and let $e \mid p^f - 1$. Then there is a tame chart with ramification index $e$.

Lean: `New.Lift.exists_normal_fixer_index_coprime`, `New.Lift.exists_tameChart` (New/Congruences/Lifting/TameCharts.lean).

*Proof.* Take $\varpi$ with $\varpi^e = p$ and a primitive $e$-th root of unity $a \in \mathbb{F}_{p^f}$; it exists because $e \mid p^f - 1$. Let $U \subseteq G_p$ fix $\varpi$ and $\Lambda$. It is the stabilizer of $\varpi$ in the fixer of the $(p^f - 1)$-th roots of unity, so it is open and normal, and the exponent of $G_p/U$ divides $f(p^f - 1)$, which is prime to $p$. So the index of $U$ is prime to $p$. Take the chart at $\varpi$ ([charts and Kummer charts](/chapter/kisin-frames/#charts-and-kummer-charts)), with $\Gamma'$ the preimage of $U$. Inertia permutes the towers of $p$-power roots of $\varpi$. As $\Gamma \to G_p$ is onto, there are elements of $\Gamma'$ that multiply $z$ by $[\varepsilon]^l$, which give the Kummer data, and an element $s$ of inertia that fixes $\Lambda$ and multiplies $z$ by the Teichmüller lift $\xi$ of $a$. $\square$

**Remark (Formalization).** The tame chart is a class that extends the Kummer chart. The degree bound in (3) is a count over $k < \nu$ with a decidable predicate, and it needs $\nu \leq e$.
