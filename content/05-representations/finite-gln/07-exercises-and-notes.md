---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $a \in k^\times$ and let $a_r$ be the class of the scalar map $a \cdot 1$ on $k^r$. Show that $\mu(a_r) = (-1)^r q^{r(r-1)/2}$. Check that this agrees with the value $\mu(1) = \prod_{i<r}(-q^i)$ used in Section 5.

*Hint.* Every subspace of $k^r$ is stable under $a \cdot 1$, so the defining sums of $\mu$ are sums over the lattice of all subspaces. Induct on $r$ with the $q$-binomial identity $\sum_{j=0}^{r} (-1)^j q^{j(j-1)/2} \binom{r}{j}_q = 0$ for $r \geq 1$.

**Exercise 2.** Let $s_n$ be the number of labels of degree $n$ over $k$, and $S_n$ the number of monic squarefree polynomials of degree $n$. Show that $S_n = s_n + s_{n-1}$ for $n \geq 1$. Use $S_n = q^n - q^{n-1}$ for $n \geq 2$ to show $s_2 = (q-1)^2$ and $s_3 = (q-1)(q^2 - q + 1)$. Check $s_2$ against the count in Section 1.

*Hint.* A monic squarefree $c$ with $c(0) = 0$ is $X c'$ with $c'$ squarefree and $c'(0) \neq 0$. In degree $2$ there are $(q-1)(q-2)/2$ labels $(X - a)(X - b)$ and $(q^2 - q)/2$ irreducible ones.

**Exercise 3.** Use the degree formula of Section 5 to list the degrees $\Xi_c(1)$ for the labels of degree $2$. Show that the sum of their squares is $|\mathrm{GL}_2(k)| - (q-1)(1 + q^2)$. Explain the defect by the characters $\chi \circ \det$ and $\mathrm{St} \otimes \chi \circ \det$ of Section 1, which have no squarefree label.

*Hint.* The degrees are $q + 1$ for $(X-a)(X-b)$ and $q - 1$ for an irreducible quadratic. Use $|\mathrm{GL}_2(k)| = q(q-1)^2(q+1)$ and the column orthogonality $\sum_\rho \rho(1)^2 = |G|$.

**Exercise 4.** Let $[k' : k] = 2$ with $\Gamma = \{1, \sigma\}$, and work in rank $1$, so $E = k'^\times \rtimes \Gamma$. Let $\theta$ be a character of $k^\times$. Show that $(a, \sigma)^2 = (a \, \sigma(a), 1)$, and that $\vartheta(a, \tau) = \theta(a \, \sigma(a))$ is a character of $E$. Show that it descends to $\theta$ over $k$ and to $\theta \circ N_{k'/k}$ over $k'$. Check the inner product formula of Section 6 for $\Phi = \Psi = \vartheta$.

*Hint.* For the formula, both sides are $2$: the restriction of $\vartheta$ has norm $1$ on $k'^\times$, and $\theta$ has norm $1$ on $k^\times$.

**Exercise 5.** Let $[k' : k]$ be prime and let $\Psi$ be a class function on $\mathrm{GL}_n(k') \rtimes \Gamma$ that descends to $F \in \mathcal{H}(k)$ and to $F' \in \mathcal{H}(k')$. Assume that $\langle F', F' \rangle_{|n|} = 1$. Show that $\langle \Psi, \Psi \rangle = 1$ if and only if $\langle F, F \rangle_{|n|} = 1$. Deduce that, in the Shintani lift of an irreducible label, the norm $\langle \Xi_P, \Xi_P \rangle = 1$ over $k$ follows from the norm over $k'$ and the irreducibility of $\Psi$.

*Hint.* Apply the theorem that descent keeps inner products, part 3, with $\Phi = \Psi$.

**Exercise 6.** Let $c$ be a label and $P$ an irreducible label with $P \nmid c$. Use the Leibniz rule of Section 3 and orthonormality to show that $\partial_{\tau_P}(\tau_P * \Xi_c) = \Xi_c$, where $\partial_{\tau_P}$ is the derivation of degree $\deg P$.

*Hint.* The derivation of $\tau_P$ is $\langle \tau_P, \tau_P \rangle \cdot 1 = 1$, and the derivation of $\Xi_c$ is $0$ by part 3 of orthonormality.

## Notes and references

The character table of $\mathrm{GL}_2(k)$ in Section 1 is in W. Fulton and J. Harris, *Representation Theory*, Section 5.2. The construction of all irreducible characters of $\mathrm{GL}_n(k)$ is due to J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80 (1955). The source cites Theorem 1 of that paper for the cuspidal functions, and Theorems 2, 9 and 12 to 14 for the characters $\Xi_c$. A modern account with labels given by partition valued functions on irreducible polynomials is I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter IV. Macdonald uses the Hall algebra and symmetric functions, and he treats all labels. The source treats only squarefree labels, and it does not use symmetric functions.

For the ring of class functions on all square matrices, invertible or not, the source cites Z. Chen, arXiv 2408.06191, Proposition 3.2. For the cuspidal functions it cites T. A. Springer, Séminaire Bourbaki 441 (1973/74), Sections 1.1 to 1.7, and R. Carter, *Finite Groups of Lie Type* (1985), for the product of the Steinberg character with a torus character. The source does not use Brauer induction for the virtual lift of the eigenvalue sums. It induces from tori in the semidirect product and inverts by recursion on the rank, as in Section 6. For the support of $\mu$ the source cites P. Hall's lemma, D. Krasula, arXiv 2403.05656, Lemma 23, and H. Crapo's complementation theorem. It uses only the vanishing half of Crapo's theorem.

The lifting theorem is due to T. Shintani, *Two remarks on irreducible characters of finite general linear groups*, J. Math. Soc. Japan 28 (1976), 396 to 414. The source also cites A. Silberger and E.-W. Zink, J. Algebra 319 (2008), Theorem 5.1, and, for tensor induction, D. Gluck and I. M. Isaacs, Illinois J. Math. 27 (1983). Clifford's theorem, used in the proof of the extension theorem, is Theorem 6.2 of I. M. Isaacs, *Character Theory of Finite Groups*.

The source differs from the classical treatment in four places. Irreducibility is stated as three clauses, one of which is a consequence of Schur's lemma. The exact degree of $\Xi_c$ is not stated, only a lower bound. Shintani's bijection is replaced by a lift in prime degree that records only a character in each rank. The characters of the finite field are named through one injective character of an algebraic closure, chosen by Hilbert's epsilon. The formalization remarks of Sections 2 to 6 give the details.

The planning notes for this handbook list the theorems on irreducibility and on the Shintani lift as not used by name in the main argument. This is true for the main argument, but the library itself uses both, in the files on cuspidal types for the trace formula and on the compatibility of labels at a place.

Status: drafted by a model. No person has checked this chapter against the Lean source.
