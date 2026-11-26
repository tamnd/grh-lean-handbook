---
title: Exercises
lean:
  - New/Reduction/PrimeSums.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Redo the example of Section 6 with $\Phi_b = \{3, 7\}$, all the other data the same. Find which pairs $(\tau, \nu)$ meet $\Phi_b$, compute $\sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(72, \tau)$, and check the identity. Which term of the table in Section 6 changes, and why only that one?

*Hint.* Now $\kappa(3) = \kappa(7) = 12$. The pairs are $(1, 5)$ and $(5, 5)$, and the sum is $72\log 3 + \tfrac{48}{5}\log 5 + \tfrac{60}{7}\log 7$. The count of Section 5 gives $\#\Phi_b = 2$ for $\nu = 5$. Only the term $(\tau, \nu) = (1, 5)$ changes, from $42/5$ to $12/5$, since it is the only pair with $[-\nu]\tau = 3$. On the right side only $\#\Phi_b$ changes.

**Exercise 2.** Prove the lemma on the sum of the logarithms of the weights without the formula for $\log\kappa(\tau)$ at each place. Group the places by their weight instead. Then show that $s_{\mathrm{main}} = a(\log(a/\bar\kappa) + c_1)$, where $\bar\kappa$ is the geometric mean of the weights, and that $x \leq a/\bar\kappa \leq x_1$.

*Hint.* There are $\#\Phi_b$ places of weight $a/x$ and $f - \#\Phi_b$ places of weight $a/x_1$. The number $\log(a/\bar\kappa)$ is a mean of $\log x$ and $\log x_1$ with weights $\#\Phi_b/f$ and $1 - \#\Phi_b/f$.

**Exercise 3.** Suppose that every place of $\Phi_b$ has class $c$ modulo $q_0$, for a fixed unit $c$, and not $-1$. Prove the analogue of the identity. Which remainder takes the place of $R_{q_0}$? Explain why this would not help Landau's criterion in the form of [Landau's criterion](/chapter/landau-criterion/).

*Hint.* The class condition becomes: $\tau \in \Phi_a$ if and only if $n \equiv -c \pmod{q_0}$. The remainder is that of the sum of $\Lambda_K(n)(1/n - 1/z)$ over $n \equiv -c$. The criterion is stated for the class $1$.

**Exercise 4.** Find every place in Section 5 where the proof uses $1 \neq -1$ modulo $q_0$. Then take $q_0 = 2$ and show that the class condition fails. What goes wrong in the count?

*Hint.* It is used only in the lemma on the class of an integer, in the case where $\nu$ is not prime to $q_1$. For $q_0 = 2$ the only unit modulo $2$ is $1 = -1$, so $\Phi_a = \Phi$. Take $n$ even. Then $[-n]$ is the identity place, so for $\tau \in \Phi_b$ the place $[-n]\tau = \tau$ lies in $\Phi_b$ and $\tau \in \Phi_a$, but $n \not\equiv 1 \pmod 2$. The count is $\#\Phi_b$, not $0$. In the lemma on one integer the count is multiplied by $\Lambda_K(n)$, so the error does no harm if $\Lambda_K$ vanishes at the powers of $2$.

**Exercise 5.** Let the weight take three values: $a/x$ on $\Phi_b$, $a/x_2$ on a second set $\Phi_c$ of places of class $-1$, disjoint from $\Phi_b$, and $a/x_1$ elsewhere, with $x \leq x_2 \leq x_1$ and $x_2 \mid a$. Define $s_{\mathrm{main}}$ by the same formula. Prove that

$$\mathrm{rem} = a\Bigl(\#\Phi_b\bigl(R_{q_0}(x) - R_{q_0}(x_1)\bigr) + \#\Phi_c\bigl(R_{q_0}(x_2) - R_{q_0}(x_1)\bigr) + \#\Phi_a R_1(x_1)\Bigr).$$

*Hint.* Write the term at a place as the term of weight $a/x_1$ plus one correction for each of the two sets. The count of Section 5 holds for $\Phi_c$, since it uses only the class $-1$.

**Exercise 6.** Section 2 proves $\sum_{n \leq N}\Lambda(n)/n \leq 2\log N$. Prove the sharper bound $\sum_{n \leq N}\Lambda(n)/n \leq \log N + \log 4$. Show that it changes the bound $s_{\mathrm{fin}}(y, \tau) \leq 4y\log x_1$ to $2y(\log x_1 + \log 4)$. Explain why the source does not need the sharper bound.

*Hint.* Use $\log N! = \sum_{n \leq N}\Lambda(n)\lfloor N/n\rfloor$, $\lfloor N/n\rfloor > N/n - 1$, Chebyshev's bound $\sum_{n \leq N}\Lambda(n) \leq N\log 4$, and $\log N! \leq N\log N$. For the second part, the bound is used only in $s_{\mathrm{fin}}(y, \tau) \leq y\log b$, and $4\log x_1 \leq 10^{-6}\cdot 4\log b$.

**Exercise 7.** Read the Lean statement of `New.Data.totalRemainder_eq` and the definitions of `New.Data.primeSum` and `New.Data.weight`. Find the hypotheses on the data that the proof uses, through the lemmas it calls. Compare with the list of four properties in Section 6.

*Hint.* The field `dvd_natB` enters through `New.Data.cast_weight`. The fields `placeClass_of_mem_bPlaces` and `exp_logX` enter directly. The inequalities $x \leq a$ and $x_1 \leq a$ enter through the automation for sizes.

## Notes and references

The identity of this chapter has no classical source. It is a finite computation, and the source file has no section on the literature. The ingredients are classical.

Mertens' estimates, of which the bound $\sum_{n \leq N}\Lambda(n)/n \leq 2\log N$ is a weak form, are in Montgomery and Vaughan, *Multiplicative Number Theory I*, Section 2.2. The prime number theorem for arithmetic progressions to a fixed modulus, which makes $R_{q_0}(x_1)$ and $R_1(x_1)$ small, is in Davenport, *Multiplicative Number Theory*, Chapter 20.

The decomposition of a prime in a cyclotomic field, which identifies the places of $E$ with $(\mathbb{Z}/q_1\mathbb{Z})^\times$ and the class of a prime $\nu$ with the action of its Frobenius element, is in Neukirch, *Algebraic Number Theory*, Chapter I, Section 10. This chapter uses only the group $\Phi$ and the map $\nu \mapsto [\nu]$, as the source defines them.

The numbers $\Lambda_K(n) = \Lambda(n)(1 - \chi_K(n))$ are the coefficients of the Dirichlet series $-(\zeta/L)'/(\zeta/L)(s)$, with $L = L(s, \chi_K)$. The source calls the constant $C_d = \gamma - \operatorname{Re}(L'/L)(1, \chi_K)$ `New.chowlaSelbergConst`. This chapter uses only its definition.

The identity answers question Q-16 of the register of findings ("Check `totalRemainder_eq` by hand for boundary terms") on paper, in the remark at the end of Section 5. It does not replace the Lean check.

Status: drafted by a model. No person has checked this chapter against the Lean source.
