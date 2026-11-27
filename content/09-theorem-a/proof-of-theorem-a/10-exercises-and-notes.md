---
title: Exercises and notes
lean:
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 1 to 7. As before, $\mathrm{err}_0 = f a\log^3 b$, $D_X$ is the dimension of the space of all source forms, and $\mathrm{src}$ is the space of ramified source forms.

**Exercise 1.** Suppose that the size theorem had the factor $1$ in front of the gains, so that $\beta = \mathrm{mainAmount} - m\cdot\mathrm{rem} + \sum_{\mathcal{S}}\mathrm{gain}_\ell\log\ell + \mathrm{err}_0$. Show that the proof of part (a) then needs $c_B' = \prod_{\ell}\ell^{-g_\ell/2}$ in place of $c_B$, and explain why $c_B'$ is not rational in general. Which step of part (b) fails for $c_B'$?

*Hint.* The squared norm multiplies by $|c|^2$. For part (b), look at the lemma on removing a power: it needs an integer exponent $\beta$.

**Exercise 2.** Check inequality (E) of Section 6 for the smallest values allowed by the argument: take $f = 1$ and $\log b = 5$, and suppose $x^{99} \leq a$ and $b \leq a$. Show that $x^{99} + 4a\log^3 b + 2b \leq a\log^4 b$. Then find the least real $L \geq 1$ such that $3 + 4L^3 \leq L^4$.

*Hint.* The left side is at most $a(3 + 4L^3)$ with $L = \log b$. The function $L^4 - 4L^3 - 3$ is increasing for $L \geq 3$, and its value at $L = 4$ is $-3$.

**Exercise 3.** In the example of Section 4, $\mathcal{S} = \{3\}$, $\mathrm{gain}_3 = 3.7$, $\mathrm{err}(3) = 0.5$ and $\mathrm{err}(N) = 2.2$. Compute the term $2\log c_B + 2\,\mathrm{gain}_3\log 3$ that the factor $c_B$ adds to the exponent of part (a) after the gains cancel. Compare it with the bound $2(\mathrm{err}_0 + b)$ of the proof, assuming $\mathrm{err}_0 \geq (\mathrm{err}(3) + 1)\log 3 + (\mathrm{err}(N) + 1)\log N$.

*Hint.* $c_B = 3^{-3}N^3$, so $2\log c_B = 6\log N - 6\log 3$. Adding $7.4\log 3$ gives $2(0.7\log 3 + 3\log N)$. Compare each term with $(\mathrm{err}(\ell) + 1)\log\ell$.

**Exercise 4.** Prove the lemma on the gain factor at a prime for a prime $\ell \notin \mathcal{S}\cup\{N\}$ directly from the four properties of the errors, without the lemma on the primes outside $\mathcal{S}$. Where does the proof need that $\ell \neq N$?

*Hint.* For $\ell \notin \mathcal{S}$ and $\ell$ prime, either $\ell \geq x_1$ or $\chi_K(\ell) = 1$. Property 2 needs $\ell \neq N$. At $N$ the gain is $0$ but the error need not be.

**Exercise 5.** Let $V$ be a space with one twist, $\Theta = \mathrm{id}$ and $\Lambda_\iota = \mathcal{O}_\iota$, as in the example of Section 3. Let $A : \mathbb{C}^2 \to V = \mathbb{C}$ be $A(u, v) = u + v/\ell_0$, and let $M = \mathcal{O}_\iota^2$ at $\iota$ above $\ell_0$. Show that $\mathrm{ColengthDvd}(M, A^{-1}(\mathcal{O}_\iota), \ell_0)$ from the definition, and deduce $\mathrm{ColengthDvd}(A(M), \mathcal{O}_\iota, \ell_0)$ by the rule for the push forward. What is the module $A(M)$?

*Hint.* $A^{-1}(\mathcal{O}_\iota) \cap M$ is the set of $(u, v) \in M$ with $\ell_0 \mid v$. For a family $\Phi_k = (u_k, v_k)$ in $M$, choose $k_0$ such that $v_{k_0}$ divides every $v_k$; this is possible, as $\mathcal{O}_\iota$ is a valuation ring. Subtract multiples of $\Phi_{k_0}$ from the other members, and multiply $\Phi_{k_0}$ by $\ell_0$. The matrix has determinant $\ell_0$. $A(M) = \ell_0^{-1}\mathcal{O}_\iota$.

**Exercise 6.** The lemma on half the source forms gives $D_X \leq 2\dim\mathrm{src}$. Use $f/(N-1) \leq b^{-8}$ to show $D_X \leq (1 - b^{-8})^{-1}\dim\mathrm{src}$. With this bound, what is the constant in part (b) in place of $2\,\mathrm{err}_0$? Explain why the constant $2$ costs nothing in the main inequality.

*Hint.* The main inequality has a slack of a factor $\log b$ between $f a\log^4 b$ and $f a\log^5 b$. A factor $2$ against $(1 - b^{-8})^{-1}$ changes the index by less than $\dim\mathrm{src}\cdot\mathrm{err}_0$.

**Exercise 7.** Show that part (a) of Theorem A stays true if $c_{ss}$ is replaced by any $c \in \mathbb{C}^\times$ for which the seesaw identity holds with constant $c$. Show that part (b) also stays true. Then explain why the statements cannot be proved for a constant $c$ for which the identity fails.

*Hint.* The proofs use $c_{ss}$ only through the lemma on the seesaw identity with constant one. If the identity fails for $c$, the composite lift does not control $\iota_\vartheta z$.

## Notes and references

The chapter follows part A of New/Reduction/ShortAndEnough.lean, from line 41 to line 379. The header of the file describes the source, the target, the maps $s\mathfrak{p}$ and the statements of Theorems A and B. It names no outside works. The file is short because it only assembles: each proof in it calls one or two results of other files and closes with a rewriting step, `linarith` or a rule of colength.

The structure of the assembly is that of the plan in [how the inputs meet](/chapter/theorem-a-plan/#how-the-inputs-meet). Section 9 lists the points where the plan and the source differ. The main ones are the dependency table, the omission of the pull back and the push forward in the proof of the index lemma, and the description of $\iota$. The short form of the proof in [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-a-short-forms-of-small-index) of Volume 1 has the same structure.

The constants are not optimal, and the source does not claim that they are. The bound $f a\log^4 b$ of part (a) leaves a margin of about $f a\log^3 b(\log b - 4)$ over the losses, and the factor $2$ of part (b) could be $1 + 2b^{-8}$. Both margins are absorbed in the main inequality, whose right side is $f a\log^5 b$. [The main inequality](/chapter/main-inequality/#the-main-inequality) shows how the two parts of Theorem A meet Theorems B and C.

The formalization has four points that the reader of the Lean text must keep in mind. First, the errors $\mathrm{err}$ and the seesaw constant $c_{ss}$ are chosen by `choose`, and Theorem A holds for every choice with the stated properties. Second, the gain factor $c_B$ is a rational number with integer exponents, so that the integrality of part (b) holds exactly; the cost of the floors is $2b$ in part (a). Third, part (a) is proved only for the trivial twist, as the size theorem is proved only for the trivial character. Fourth, the index lemma needs a pull back and a push forward of the colength, because the colength lives on all source forms and the index on target forms. [The normalized map](/chapter/proof-of-theorem-a/#the-normalized-map) and [the proof of part (b)](/chapter/proof-of-theorem-a/#the-proof-of-part-b) give the details.

This chapter does not claim that the proof of the source is correct, and it does not claim that the Riemann hypothesis is proved. It describes what the pinned source states and how its proofs combine.
