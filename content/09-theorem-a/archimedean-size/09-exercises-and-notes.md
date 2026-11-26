---
title: Exercises and notes
lean:
  - New/UpperBound/Size/ArchimedeanSize.lean
  - New/UpperBound/Size/Estimates.lean
  - New/UpperBound/Size/ClassCount.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises check the steps of the chapter on small cases. None of them is used later.

**Exercise 1 (The jet size is superadditive).** Let $s_\infty(l) = \log l! + l\log(M/\Omega)$ for $l \ge 0$. Show that $s_\infty(0) = 0$ and that $s_\infty(l) + s_\infty(l') \le s_\infty(l + l')$ for all $l, l' \ge 0$. Deduce that splitting a row of total order $L$ into pieces never increases the sum of the jet sizes above $s_\infty(L)$.

*Hint.* The terms $l\log(M/\Omega)$ add up exactly. For the factorials, the binomial coefficient $\binom{l+l'}{l} = (l+l')!/(l!\,l'!)$ is an integer at least $1$.

**Exercise 2 (Orders of linear groups).** Let $\mathbb F_q$ be a finite field and $k \ge 1$. Show that $|\mathrm{GL}_k(\mathbb F_q)| \le q^{k^2}$. Let $w$ run over a finite set of places with residue fields $\mathbb F_{q_w}$ and $\prod_w q_w = M^f$. Show that the order $O$ of $\prod_w\mathrm{GL}_k(\mathbb F_{q_w})$ has $\log O \le fk^2\log M$. Use this to check Step 5 of the size of the good part.

*Hint.* A matrix over $\mathbb F_q$ has $k^2$ entries. Take logarithms of the product over $w$.

**Exercise 3 (Central projections).** Let $H$ be a finite group and $e \in \mathbb C[H]$ a central projection, that is, $e$ is central and $e^2 = e$. Show that $1 - e$ and $\sigma(e)$ are central projections for every automorphism $\sigma$ of $\mathbb C$. Here $\sigma$ acts on the coefficients. For $H = \{\pm 1\}$, list all central projections and check $|e(h)| \le 1$ for each.

*Hint.* The map $\sum_h a_h h \mapsto \sum_h\sigma(a_h)h$ is a ring automorphism of $\mathbb C[H]$. For $H = \{\pm1\}$ write $e = \alpha + \beta(-1)$ and solve $e^2 = e$. There are four solutions.

**Exercise 4 (Why integrality does not lose a factor).** Let $l$ be a prime and let $x_1, \dots, x_h \in \mathbb C_l$ with $|x_i|_l \le 1$. Show that $|\sum_i\lambda_ix_i|_l \le 1$ for all algebraic integers $\lambda_i$ and every embedding of $\bar{\mathbb Q}$ in $\mathbb C_l$. Compare with the archimedean case, where $|\sum_i\lambda_ix_i|$ can be as large as $\sum_i|\lambda_i|$. Explain why the theorem on integrality of Section 8 has no factor $|\mathsf G|$, while the theorem on size has the factor $|\mathsf G|^4$.

*Hint.* The absolute value $|\cdot|_l$ satisfies $|u + v|_l \le \max(|u|_l, |v|_l)$. An algebraic integer satisfies a monic equation $\lambda^n + c_1\lambda^{n-1} + \dots + c_n = 0$ with $c_i \in \mathbb Z$. If $|\lambda|_l > 1$, the term $\lambda^n$ is strictly larger than all others.

**Exercise 5 (Classes of a smaller level).** Let $\Gamma$, $K$, $K'$ be subgroups of a group $G$, with $[K : K\cap K']$ finite. Show that $\#(\Gamma\backslash G/K') \le \#(\Gamma\backslash G/K)\cdot[K : K\cap K']$. Find an example with $G = \mathbb Z$, $\Gamma = 0$, $K = \mathbb Z$ and $K' = 3\mathbb Z$ where equality holds.

*Hint.* Follow the short proof of Section 3. In the example, both sides equal $3$.

**Exercise 6 (A norm one count).** Let $E = \mathbb Q(i)$ and let $p$ be a prime. Count the elements $u$ of $(\mathbb Z[i]/p)^\times$ with $u\bar u = 1$, for $p = 3$ and $p = 5$. Compare the counts with the bound $\mathrm N(p) = p^2$ of the index of the principal level $K(p)$ in $K_0$ for $\#n = 1$.

*Hint.* For $p = 3$ the ring is $\mathbb F_9$ and the conjugation is $u \mapsto u^3$, so the condition is $u^4 = 1$. For $p = 5$ the ring is $\mathbb F_5\times\mathbb F_5$ and the conjugation swaps the factors, so the condition is $u_2 = u_1^{-1}$. The example at the end of Section 3 has the answers.

## Notes and references

*The source.* The chapter follows three files of the Lean source: New/UpperBound/Size/ClassCount.lean (Section 2), New/UpperBound/Size/Estimates.lean (Sections 3 to 6) and New/UpperBound/Size/ArchimedeanSize.lean (Sections 7 and 8). The file ArchimedeanSize imports the file of the chain datum expansion of [the valuation of a chain](/chapter/chain-valuation/), chapter 10 and a file of Volume 10 that defines the good part (`New.Data.goodProjTranslate`). The file ClassCount imports a file of Volume 10 and the file of the gain of short columns of [the gain of short columns](/chapter/short-columns-gain/), which comes earlier in Volume 9. No file of this chapter imports a file of a later chapter of Volume 9.

*The order of the volume.* The plan of the handbook lists an older order of the chapters of Volume 9. This chapter follows the order of the volume file, where it is chapter 12, after [the gain of short columns](/chapter/short-columns-gain/) and [the seesaw identity, part 2](/chapter/seesaw-identity-2/).

*Class numbers.* The finiteness of $\Gamma\backslash G_f/K$ for a compact open subgroup $K$ is due to A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16 (1963). For a group whose real points are compact, as for the definite unitary groups of this book, the set of classes is the set on which algebraic modular forms live. This point of view is that of B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999). The explicit bound of Section 2 is not taken from these works. It is a direct count by short bases and bounded Gram matrices, as in the source. M. Greenberg and J. Voight, *Lattice methods for algebraic modular forms on classical groups* (2014), compute the classes of definite unitary groups as classes of hermitian lattices in a genus. Their methods give the classes, while this chapter needs only a crude upper bound for their number.

*Central idempotents.* The facts on central projections used in Section 8 are standard. The central idempotents of $\mathbb C[H]$ and the formula for their coefficients in terms of characters are in J.-P. Serre, *Linear Representations of Finite Groups*, Section 2.6. The integrality of the values of characters is in the same book, Section 6.5. The bound $|e(h)| \le 1$ follows from the bound of a character value by the degree.

*Stirling.* The bound for $\log a!$ in Section 6 is taken from Mathlib, through the monotone Stirling sequence. It is not proved again in the source.

*Background.* The data and the table of sizes are in [the data and their sizes](/chapter/data-and-sizes/). The objects of the upper bound, the lift diagrams and the good idempotent are in [the objects of the upper bound](/chapter/upper-bound-objects/). The chains of lifts as plain sums and the restriction to $Y_m$ are in [the valuation of a chain](/chapter/chain-valuation/). The $p$-adic gauge and the class sums are in [automorphic forms](/chapter/automorphic-forms/).

*Remarks on the notes.* Four points in the earlier text and the notes differ from the source. First, the plan lists the old order of Volume 9, as said above. Second, the outline of the argument refers to the archimedean bound as Volume 9, chapter 6; it is chapter 12. Third, [the normalized map](/chapter/theorems-a-b-c/) says that the gain is defined in this chapter; the source defines it in the file of the gain of short columns, chapter 9. Fourth, the register of open questions lists the factor $2$ on the gain in the exponent (F-099, Q-20) as open. In the source the factor is cancelled: the gain factor $c_B$ is the inverse gain factor $\prod_p p^{-g_p}$, and $2\log c_B \le -2\sum_p\mathrm{gain}_p\log p + 2\,\mathrm{err} + 2b$ (`New.Data.log_invGainFactor_le`). Section 7 explains this.

*Status.* Drafted by a model. No person has checked this chapter against the Lean source.
