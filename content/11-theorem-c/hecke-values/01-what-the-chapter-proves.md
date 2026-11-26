---
title: What the chapter proves
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter proves the height bounds for twisted Hecke values that the proof of Theorem C uses. Let $p = (\nu, z)$ be a critical pair, $\vartheta$ a twist with modulus $Q$, and $\varphi_\vartheta$ the theta lift of $\nu\vartheta$ from $U(1)$ to the definite group $U(2z)$ ([the lift of a character](/chapter/character-lifts/#the-lift-of-a-character)). By the norm formula of [the norm of the lift](/chapter/character-lifts/#the-norm-of-the-lift), the ratio of $L$-values
$$\mathrm{ratio}(p, \vartheta) = \frac{|L(z, (\nu\vartheta)^{-1})|}{|L(z, \nu^{-1})|}$$
is a quotient of normalized squared norms of two such lifts ([the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part)). The chapter bounds the height of the inverse ratios along a regular family of twists. The source claims that these bounds hold for the data of the proof; this book follows the Lean statements.

### The main statements

Let $\theta$ be a regular family of $m$-fold twists ([regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists)), $j \in [1, m]$, and $\vartheta_\iota = \theta(\iota)^j$.

1. (Section 7.) For a main pair $p$ for $j$, the family $\iota \mapsto \mathrm{ratio}(p, \vartheta_\iota)^{-1}$ has height at most $6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount}$. This is the theorem that [regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists) states and leaves to this chapter.
2. (Section 7.) The inverse quotient of the Hecke values of the three exchanges, $\iota \mapsto (\Gamma_j(\vartheta_\iota)/\Gamma_j(1))^{-1}$, has height at most $10\,m\,x_1 + k(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$.

The proof of these needs four tools, one in each of Sections 2 to 5, and a construction in Section 6.

- Section 2, the central action. $U(1)(\mathbb{A}_f)$ acts on forms on $U(N)$ by scalar matrices. The lift is fixed, and the action keeps integrality, Hecke polynomials and orthogonality to the false lifts. Averaging over the action gives the projection bound with the class number, which [point forms and tested forms](/chapter/character-lifts/#point-forms-and-tested-forms) uses.
- Section 3, the period at one. The class sum of a determinant kernel at a level, and how it changes when one prime is added to the modulus.
- Section 4, integrality. The scaled lift $n_\nu\varphi_\vartheta$ is integral away from $\mathrm{Nm}\,Q$. So the integral algebraic part $n_LL^{\mathrm{alg}}(\vartheta)$ is integral away from $\mathrm{Nm}\,Q$, and $\vartheta' \mapsto n_LL^{\mathrm{alg}}(\vartheta')$ is an integral measure at $Q$, the input of [twist measures of critical pairs](/chapter/twisting-theorem/#twist-measures-of-critical-pairs).
- Section 5, size. For a flat pair every conjugate of $n_LL^{\mathrm{alg}}(1)$ is at most $\exp(x^{34})$. For a main pair the constant family $\|\varphi_1\|^2$ has height at most $\mathrm{denominatorBudget} - \sum_\tau\mathrm{jetSize}(\kappa_\tau)$.
- Section 6, the test form. A seesaw on four blocks of indices gives a test form whose pairing with $\varphi_\vartheta$ has small valuation at $\ell$.

### How the argument runs

The inverse ratio at a main pair is, up to an integer power of $\mathrm{Nm}\,Q$, the quotient $\|\varphi_1\|^2/\|\varphi_\vartheta\|^2$. The numerator has a known height (Section 5). The denominator needs a lower bound at each $\ell$. Take two test forms $\Xi$, $\Xi'$ at $\ell$. Then
$$\|\varphi_\vartheta\|^2 = \frac{\langle\Xi, \varphi_\vartheta\rangle\langle\varphi_\vartheta, \Xi'\rangle}{\langle\mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi'\rangle},$$
with $\mathrm{pr}$ the projection to the line of $\varphi_\vartheta$. The regular family bounds the denominator of the projections. Section 6 bounds the pairings from below by $|\iota(c_0\rho)|\,\ell^{-F(\ell)}$, where $\rho$ is a ratio of a ramified flat pair and $F(\ell)$ is the forced divisibility of derivatives. The sum of $F(\ell)\log\ell$ over $\ell$ is the prime sum, and this produces the term $-\mathrm{directionAmount}$.

### What the chapter uses

Background, stated where it is used:

- Heights and the multiplier criterion: [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers).
- Sizes of the data: [the data and its sizes](/chapter/data-and-sizes/).
- Forms on definite groups and class sums: [algebraic forms on definite groups](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups).
- Theta kernels of data modulo an ideal and their gauges: [data from functions modulo an ideal](/chapter/theta-kernels-gauges/#data-from-functions-modulo-an-ideal).
- Tame characters and twists: [characters, twists and m-fold twists](/chapter/fields-places-twists/#characters-twists-and-m-fold-twists).
- Hecke polynomials at split places: [split places and the transfer of Hecke polynomials](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials).
- The prime sums: [the archimedean size](/chapter/archimedean-size/).

From the earlier chapters of this volume: the lift, its norm, its Galois conjugates and the tested forms of [character lifts](/chapter/character-lifts/); critical pairs, the ratio and regular families of [twists, critical pairs and regular families](/chapter/twists-critical-pairs/); and the monomial vectors of [the exchange identity, part 2](/chapter/exchange-identity-2/).

### Forward references

The file New/OneLift/HeckeValues/TwistedValueHeights.lean imports three files that the volume puts in later chapters. Each result used is stated once, with a forward link.

- [False lifts](/chapter/false-lifts/) (chapter 12): the vanishing of periods against point forms and of hyperplane sums, `New.Rows.stdClassSum_period_eq_zero` and `New.Rows.hyperplaneSum_apply_eq_zero_of_rank_one`. Stated in Section 6.
- [The divisibility is sharp](/chapter/sharpness/) (chapter 13): a derivative of each order in $[\kappa, \kappa + x^{42}]$ with valuation at most $F(\ell)$, `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff`. Stated in Section 6.
- [The comparison operator, part 2](/chapter/comparison-operator-2/) (chapter 14): the pairs of the three exchanges and the Hecke value $\Gamma_j$, `New.Data.exchangePair` and `New.Data.heckeValueProd`. Stated in Section 7.

The same file also imports New/Congruences/GaloisRepresentations/SelmerHypotheses.lean of Volume 12, for two lemmas on chosen places (Section 6).

The chapter [the height of one lift determinant](/chapter/lift-volume-height/) uses the results of Section 7.

### Positivity and nonvanishing

The ratios in this chapter are nonzero. The source proves `ratio_ne_zero` from `HasWeight.L_ne_zero`, the nonvanishing of the $L$-values, which is a field of the structure `HasWeight` (register entry F-120). It is not proved from the positivity of the algebraic part. The definition of the ratio alone does not exclude a zero denominator; `algPart_pos` and `ratio_eq_algPart_div` write it as a quotient of two positive numbers (F-033). Both lemmas are proved in [the algebraic part](/chapter/twists-critical-pairs/#the-algebraic-part), not in this chapter.
