---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of the chapter. Exercises 1 to 3 use the model of Section 1, with $d = 23$ and $q_1 = 12$.

**Exercise 1.** In the model, find the Frobenius pair of $p = 17$ and of $p = 19$. For each, give the norm of a place above $p$, the number of places above $p$, and say whether these places are self-conjugate.

*Hint.* Compute $(17/23)$ and $(19/23)$ by reciprocity. For a split prime the pair is $(v_p, 1)$, and for an inert prime it is $(v_{-p}, -1)$. The norm is $p$ to the order of the pair, and the number of places is $8$ divided by that order. A place is self-conjugate if some power of the pair is $(1, -1)$.

**Exercise 2.** In the model, check the Frobenius congruence of Section 4 for $p = 7$ and $n = 1$ on the element $y = \beta_K = (1 + \sqrt{-23})/2$. That is, show $7 \mid \beta_K^7 - \bar\beta_K$ in $\mathcal{O}_E$.

*Hint.* The automorphism $\tau = \sigma_{v_{-7}}$ fixes $K$, so $\tau(\bar\beta_K) = \bar\beta_K$. In $\mathcal{O}_K/7$, the Frobenius $y \mapsto y^7$ is the nontrivial automorphism of $\mathbb{F}_{49}$, since $7$ is inert in $K$.

**Exercise 3.** In the model, show that the places above $p = 829$ that divide $a = 1 + 6\sqrt{-23}$ are exactly the places above the prime ideal $a\mathcal{O}_K$ of $K$. Deduce again that there are $4$ of them.

*Hint.* The prime $829$ splits in $K$ as $a\mathcal{O}_K \cdot \bar a\mathcal{O}_K$. Each of the two primes of $K$ splits completely in $E/K$, which has degree $4$.

**Exercise 4.** Let $p$ be prime with $\chi_K(p) = -1$, and let $o$ be the order of $-p$ in $(\mathbb{Z}/q_1)^\times$. Show that the places above $p$ are self-conjugate if and only if $o$ is odd. Use the theorem of Section 4 to show that then $-p \equiv 1 \bmod 2^{s+1}$, and give a direct proof of this from the structure of $(\mathbb{Z}/2^{s+1})^\times$.

*Hint.* By the stabilizer theorem of Section 4, $1 \cdot w = \bar w$ if and only if $1 = v_{-p}^n$ for some odd $n$, that is, $o \mid n$ for some odd $n$. For the direct proof, an element of odd order in a group of order $2^s$ is trivial.

**Exercise 5.** Show that the phase $c$ of Section 2 is unique up to sign. That is, if $c$ and $c'$ are units of $\mathcal{O}_E$ with $c\bar c = c'\bar c' = 1$ and $c\delta$, $c'\delta$ both real, then $c' = \pm c$.

*Hint.* The quotient $u = c'/c = c'\bar c$ is the quotient of the two real numbers $c'\delta$ and $c\delta$, so $\bar u = u$. With $u\bar u = 1$ this gives $u^2 = 1$, and in the field $E$ this means $u = \pm 1$.

**Exercise 6.** Let $\alpha$ be the idele of Section 5. Show that $|\alpha| = |\bar\alpha|$ and that $\alpha\bar\alpha$ is $\delta^{-1}$ at every place that divides $\delta$. Use the product formula to give a second proof of the formula $|\alpha| = \prod_v|\delta|_v$.

*Hint.* At a place $w$ with $\delta \in w$, exactly one of $\beta_K$ and $\bar\beta_K$ lies in $w$ (Section 1 and Section 5). The product formula gives $\prod_w |\delta|_w \prod_v |\delta|_v^2 = 1$, where $w$ runs over the finite places.

**Exercise 7.** Show that for $n$ not a prime power, $\zeta_n - 1$ is a unit in $\mathbb{Z}[\zeta_n]$, and that for $n = \ell^k$ it is not. Explain why Section 5 needs $12 \mid q_1$ and not only $4 \mid q_1$.

*Hint.* The norm of $\zeta_n - 1$ to $\mathbb{Q}$ is $\pm\Phi_n(1)$. The unit $\eta = i(\zeta - 1)$ needs $i = \zeta^{q_1/4}$, which uses $4 \mid q_1$, and it needs $\zeta - 1$ to be a unit, which uses a second prime factor of $q_1$.

## Notes and references

The results of Sections 3 and 4 are the decomposition of primes in an abelian extension. The transitivity of the Galois group on the primes above $p$ is in J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 9.1, and the decomposition and inertia groups are in Chapter I, Section 9 of the same book. The different and its relation to ramification are in Chapter III, Section 2. The facts on cyclotomic fields that the chapter uses, the ring of integers $\mathbb{Z}[\zeta_n]$ and the units $1 - \zeta_n$ for $n$ not a prime power, are in L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.

The source writes the Galois group of $E/\mathbb{Q}$ as the pairs $(v, e)$ in $\Phi \times \mathbb{Z}$, with $\mathbb{Z}$ under multiplication, and not as a group. The monoid $\Phi \times \mathbb{Z}$ is larger than the group, but the Frobenius pair of a prime $p \nmid q_1 d$ lies in the subgroup $\Phi \times \{\pm1\}$, and its order there is the order of the Frobenius element. The action of $\Phi$ on finite places is the pullback; Section 3 explains why this does not change stabilizers or orbits.

The chapter does not treat the primes that divide $q_1 d$, apart from the self-conjugate case of Section 4. For $p \mid q_1$ the Frobenius pair is a junk value, and the statements of Sections 3 and 4 assume $p \nmid q_1 d$. In this chapter the places above primes of $q_1$ appear only through the different and the idele $\alpha$ of Section 5.

Two objects of this chapter are picked by a choice: the splitting character of the Weil data (finding F-043, with the open question Q-18 of the register), and the characters $T_w$, $\chi_0$ and $\chi_M$ of Section 6. The phase $c$ of Section 2 is also picked by a choice, but it is unique up to sign (Exercise 5). The bijection of Section 5 exists but is not named. The local instance `Fintype.ofFinite` of Section 6 is finding F-026.

The next chapters use the results as follows. [The objects of the upper bound](/chapter/upper-bound-objects/) builds the lift chains and the columns on the chosen places. [Marked primes and the valuation of a chain](/chapter/chain-valuation/) and [divisibility prime by prime](/chapter/divisibility/) use the inert primes of Section 4. [The integral vacuum](/chapter/integral-vacuum/) uses the number $s_0$ of Section 5. The argument of [Theorem A and its plan](/chapter/theorem-a-plan/) collects these steps.
