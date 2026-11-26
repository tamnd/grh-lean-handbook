---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

1. In the model case of Section 2, show that $a_4(2) = 1$ and $a_2(11) = -6$. *Hint:* $\omega^2 = \omega - 2$, so $\omega^4 = 2 - 3\omega$. For $n = 11$, find the four $\alpha$ with $N\alpha = 11$.
2. Let $p$ be inert in $K = \mathbb{Q}(\sqrt{-7})$ and $j$ even. Show that $a_j(p) = 0$ and $a_j(p^2) = p^j$. So both bounds of the balance are equal at $p^2$.
3. Prove Legendre's formula $\log j! = \sum_{\nu} \Lambda(\nu)\lfloor j/\nu\rfloor$, the sum over prime powers $\nu$. Compare $\lfloor j/p^e\rfloor$ with the term $(y/p^e - \kappa)_+$ of the local prime sum.
4. Prove the lemma on the prime sums cancelling from the lemma on the sum of the gains and the definitions of $\mathrm{mainAmount}$ and $\mathrm{rem}$.
5. Check that the four rows of the table in Section 4 add up to $\mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4 f a\log^3 b + 2b$. Which row would change if the size theorem had $3\sum_p\mathrm{gain}_p\log p$ in place of $2\sum_p\mathrm{gain}_p\log p$, and what would the proof then need?
6. Let $c = \mathrm{normUnit}(c_0 C/d)^{-1}$ as in the remark on the seesaw identity. Show that $c = 1$ if $c_0 C = 0$. Explain why the seesaw identity alone does not give a $\varphi$ with $\iota_\vartheta(\mathcal{P}\varphi) \neq 0$, and which results of the argument supply nonvanishing.

### Notes and references

The model case of Section 2 is the theta series of a binary quadratic form with a harmonic polynomial. Section 2 proves the facts it uses. The fact that $\theta_j$ is a modular form is not used.

The shape of Theorem A, an upper bound for an integral object at every archimedean place together with a divisibility at the finite places, is the shape of the upper half of a product formula argument. [Theorems A, B and C](/chapter/theorems-a-b-c/) gives the lattice model, and its notes name the related work on interpolation determinants and slopes that the source cites.

For the seesaw identity, the source names as related work on the transfer of periods under one theta lift: B. Wang, *Global theta lifting and periods associated to nilpotent orbits* (2025); Gomez and Zhu, *Local theta lifting of generalized Whittaker models* (2014); and Gan and Ichino, *The Gross-Prasad conjecture and local theta correspondence* (2016). For the denominators of the unfolding it names Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999); Hsieh and Namikawa, *Bessel periods and non-vanishing of Yoshida lifts modulo a prime* (2015); and X. Zhang, *Non-vanishing mod p of theta lifts* (2022). For the archimedean size it names Gross (1999) and Greenberg and Voight, *Lattice methods for algebraic modular forms on classical groups* (2014), on algebraic modular forms as functions on lattice classes. This book has not compared these citations with the statements of the source.

**Remark (Formalization).** The comment of the source on the seesaw identity calls the constant non-zero. The Lean statement gives a unit $c$, but, as Section 3 explains, the identity has no content when $c_0 C/d = 0$. This chapter follows the Lean statement.
