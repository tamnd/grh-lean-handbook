---
title: Exercises and notes
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 6. The pair is the $j$-th descent pair at a tame character $\vartheta$, with $W = W_j$ of rank $r$ and $V = V_j$ of rank $n = r + t$.

**Exercise 1.** Let $q = 2$, $r = 1$ and $n = 2$, so $t = 1$. List the $2 \times 1$ matrices over $\mathbb{F}_2$ of rank $1$. Check that their number is $q^{nr}f(q)$, with $f(q) = \prod_{i=t+1}^{t+r}(1 - q^{-i})$ as in Section 4. Then compute the chosen factor $c_M$ for one chosen place of norm $2$.

*Hint.* There are three nonzero columns. The group $\mathrm{GL}_1(\mathbb{F}_2)$ has one element.

**Exercise 2.** Deduce the operator identity $\Theta_{j,\vartheta}^*\Theta_{j,\vartheta} = c_j\,c_Q\,R_{j,\vartheta}$ from the theorem on the Gram form. Show first that an endomorphism $T$ of a finite dimensional inner product space is $0$ if $\langle x, T y\rangle = 0$ for all $x$, $y$.

*Hint.* Take $x = Ty$. For the identity, use $\langle x, \Theta^*\Theta y\rangle = \langle\Theta x, \Theta y\rangle$ and the lemma on the matrix coefficients of $R_{j,\vartheta}$.

**Exercise 3.** Show that the twist factor $c_Q$ is not $0$, by the argument for $c_M$ in Section 4. Deduce from the injectivity of $\Theta_{j,\vartheta}$ and the operator identity that the Rallis operator $R_{j,\vartheta}$ is injective on the forms of level $J_M$ on $W_j$. Compare this with the injectivity of the Rallis series in Volume 6, which the proof of injectivity uses.

*Hint.* If $\Theta$ is injective, then $\langle y, \Theta^*\Theta y\rangle = \|\Theta y\|^2 > 0$ for $y \neq 0$.

**Exercise 4.** Find where the proof of injectivity uses that the set of chosen places is not empty. Which hypothesis of the theorem on the sharpness of the block datum would fail for a definite $W$ with all signs equal and no chosen places? Does the source ever need this case?

*Hint.* Read the hypothesis "all signs of $W$ agree or $\pi_M Q$ has a place" in Section 4.

**Exercise 5.** In the example of rank one in Section 6, the lift has the Hecke polynomial $\prod_{i<t}(1 - q^i\alpha X)\,(1 - \lambda q^t\alpha\beta^{-1}X)$. Find the value of $\lambda$ for which the root that depends on $y$ equals the root $x_w$ of the lift. For $t = 0$, what is the Hecke polynomial, and why does the theorem of Section 6 fail?

*Hint.* The root $x_w = (\alpha q^{t-1})^{-1}$ comes from the factor $i = t - 1$. For $t = 0$ the product is empty.

**Exercise 6.** The constant $A$ of the first form of the Gram form is $C\,d_\kappa$, with $C$ the constant of Rallis' formula. Explain why the proof takes $C$ for the pair at the trivial character and then applies it at every $\vartheta$. Which property of a tame character makes this valid?

*Hint.* The constant of Rallis' formula depends on the real data only. Compare the weights of $\mu_j^0$ and $\mu_j^0\vartheta$.

## Notes and references

**The inner product formula.** The inner product formula for theta lifts is due to Rallis. The source cites S. Rallis, *L-functions and the oscillator representation*, Lecture Notes in Math. 1245, Springer (1987), and J.-S. Li, J. reine angew. Math. 428 (1992). Volume 6 explains the version that this chapter applies. It holds in Weil's convergent range, here $r + t > 2r$, for finite data that are sharp at a level. Section 4 checks the sharpness for the block datum, and Section 5 applies the formula.

**Injectivity.** For the injectivity of theta lifts to groups of large rank the source cites S. Rallis, *Injectivity properties of liftings associated to Weil representations*, Compositio Math. 52 (1984), and J.-S. Li, *Non-vanishing theorems for the cohomology of certain arithmetic quotients*, J. reine angew. Math. 428 (1992). It also names M. Cossutta and S. Marshall, *Theta lifting and cohomology growth in p-adic towers*, arXiv 1106.2765 (2011), as related work, since there too a small support of the finite datum gives injectivity at a level. In the classical form of these results the lift of a cuspidal representation is not zero when a special value of an $L$-function is not zero. The source uses no $L$-function. The unramified part of the formula stays a convergent sum over cosets, and the injectivity of the Rallis series replaces the non-vanishing of an $L$-value.

**The Gram form.** The constant $c_j\,c_Q$ of the Gram form is explicit except for $c_j$. The factor $c_j$ contains the constant of Rallis' formula, which the source does not compute. The argument needs only that $c_j \neq 0$ and that $c_j$ does not depend on $\vartheta$. The twist factor $c_Q$ is an explicit product over the places of $\vartheta$, from the count of matrices of full rank in Section 4.

**Hecke polynomials.** The transfer of unramified Hecke eigenvalues through the theta correspondence is classical. Volume 5 proves the transfer for a vacuum datum at a split place, by a computation of the action of the Hecke operators on the Weil representation. Section 6 adds the step from eigenforms to all forms of level $J_M$, by the spectral theorem for the Hecke operators.

**What differs.** The source does not use Eisenstein series or the regularized Siegel-Weil formula. It does not identify the Gram form with an $L$-value. It states the injectivity on all forms of level $J_M$ on $W_j$, not only on the good forms of Section 1. The Gram form is a sum over the cosets of the points that are integral off $\pi_M Q$, and its terms are $c_j\,c_Q\,\mathrm{mc}(r_\gamma)\langle x, R(r_\gamma)\,y\rangle$.

**Where the results go.** The injectivity and the operator identity enter [the chain determinant and its factorization](/chapter/chain-determinant/). The injectivity also enters [the comparison operator, part 2](/chapter/comparison-operator-2/) and [the height of one lift determinant](/chapter/lift-volume-height/). The vanishing of $H_w(x_w)$ on the lifts enters [the height of one lift determinant](/chapter/lift-volume-height/).
