---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Compute $c_a(n)$ for $p = 5$, $d = 0$, $a = 2$ and $n = 25$. List the costs of the steps from $o = 0$ to $o' = 3$ at level $0$.

*Hint.* $c_2(25) = 2 + 0 + 6 = 8$. At level $0$ the steps are $n = 0, 1, 2$. Each costs $0$, since $v_5(1) = v_5(2) = 0$ and $v_p(0) = 0$ in the source.

**Exercise 2.** In the unramified model case with $f = 1$ and $L = \mathbb{Z}_p$, show that the one-step gain of [Section 5](/chapter/exponent-lattices/#hodge-expansions) needs only $n = 1$ and $2$ points.

*Hint.* The multiplicity of the jump $0$ is $1$. Two vectors in $W(\mathbb{F}_p) = \mathbb{Z}_p$ have a relation with one coefficient $1$.

**Exercise 3.** Check the small-jumps theorem of [Section 7](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers) for $p = 2$. Which sides does it cover?

*Hint.* $e\omega \leq 0$ forces $\omega = 0$: all jumps are at most $0$.

**Exercise 4.** In the unramified theorem, take $p = 5$ and $s + t = 2$. What is the largest jump allowed? What goes wrong in the proof for $p = 3$?

*Hint.* The bound is $(p - 3)(s + t) = 4$. For $p = 3$ the bound is $0$. For $p = 2$ both $p - 3$ and $p - 2$ are $0$ in $\mathbb{N}$, and the step that cancels $p - 2$ fails. The source assumes $p \geq 5$ in all cases.

**Exercise 5.** Show that if $x'$ is fixed by $\Gamma'$, hypothesis (1) of the pairing lemma holds for every $e_3$.

*Hint.* Each $hx' - x'$ is $0$, and $g(0) = 0$. The pairing with $0$ is $0$, which is small.

## Notes and references

Kisin modules over $\mathfrak{S}$ and their relation to crystalline lattices are due to Kisin (M. Kisin, *Crystalline representations and F-crystals*, in Algebraic geometry and number theory, Progr. Math. 253 (2006)). The ring $A_{\inf}$ and the modules over it are in B. Bhatt, M. Morrow and P. Scholze, *Integral $p$-adic Hodge theory*, Publ. Math. IHÉS 128 (2018). This chapter does not compare the statements of the source with these texts.

The status. All five files of the chapter have full proofs in the source. The five files contain no `sorry` and no axiom. No hypothesis structure appears in the chapter; the conditions are explicit hypotheses of each statement.

Finding F-088 of the notes (`05-findings.md`) says that the unramified cokernel killer needs $p \geq 5$, and that the handling of $p = 2$ and $p = 3$ is not traced. The chapter confirms the hypothesis. The thin-cut theorem and the tame killer have no such hypothesis, but the tame killer needs $n + \kappa + 2 < p$. Whether the uses of these theorems cover $p = 2$ and $p = 3$ is decided in [Cup products](/chapter/cup-products/). The finding stays open.

The notes and the plan have small errors. Research note f-congr writes the cost of a depth step as $v_p(n) + d + 3l$; the source has $3a$, with $a$ the level. This is a naming slip only. The plan of the volume lists the topics of the chapter correctly. No file of this chapter imports a file of a later chapter of Volume 12. The chapter links to [Tied Selmer groups](/chapter/tied-selmer-groups/), which is being written, only by its slug.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
