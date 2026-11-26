---
title: Exercises and notes
lean:
  - Lib/Weil/CompactLift/ThetaKernelDefs.lean
  - Lib/Weil/CompactLift/DefiniteThetaLift.lean
  - Lib/Weil/DualPair/GaloisLaw.lean
  - Lib/Weil/TameGaussSum.lean
  - Lib/Weil/Seesaw.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $n = 1$, $n' = 2$, and let $\kappa_\tau = 0$ at every real place, so that the Young diagram is empty. Write out the three conditions for $(\kappa, e)$ to go up from rank $1$ to rank $2$ along $e_b$. Show that they reduce to $e = e_b$. What are the spaces $W_1(\kappa)$ and $W_2(\kappa)$, and what is the matrix of jets of a finite datum $f$?

*Hint.* No column has any height, so the first condition is empty and $\kappa_\tau(1) = 0$. The Schur matrix of the empty diagram is the $1 \times 1$ matrix $1$, so the only jet is the value $\theta(f)(0)$.

**Exercise 2.** Let $F = \mathbb{Q}_p$ with $\mathcal{O} = \mathbb{Z}_p$ of volume $1$ and $\varpi = p$. Let $\chi$ be a character of $\mathbb{Q}_p^\times$ that is trivial on $p$ and whose restriction to $\mathbb{Z}_p^\times$ factors through a primitive character of $(\mathbb{Z}/p)^\times$. Let $\psi(x) = e^{-2\pi i \{x\}_p}$, where $\{x\}_p$ is the fractional part. Compute $\int_{\mathbb{Z}_p} \chi^{\flat}(x)\psi(x/p)\,dx$ as a classical Gauss sum divided by $p$. Check that the constant $\gamma$ of the local Gauss sum has $|\gamma|^2 = 1/p$. Then show that the integral is $0$ for $t = p^{-2}$ and for $t = 1$.

*Hint.* Split $\mathbb{Z}_p$ into the $p$ cosets $a + p\mathbb{Z}_p$, each of volume $1/p$. For $t = p^{-2}$, integrate $\psi(tx)$ over one coset. For $t = 1$, the integrand is $\chi^{\flat}$, and the sum of a nontrivial character over $(\mathbb{Z}/p)^\times$ is $0$.

**Exercise 3.** In the theorem on the definite lift, the scale of the jets satisfies $c \neq 0$. Show that for $c = 0$ the matrix of jets of every datum vanishes when the diagram $\kappa$ is not empty. Explain why the theorem would then say that the harmonic lift of every $F_\varphi$ is $0$. Why does the theorem need the hypothesis $c \neq 0$?

*Hint.* For $c = 0$, the jet series is the constant $\theta(f)(0)$, and every derivative of positive order of a constant is $0$.

**Exercise 4.** Section 4 defines the joint harmonic of two parameters by a choice, with a junk value when the parameters do not correspond. In the theorem on the definite lift, show that the parameters $l$ and $l'$ always correspond. Use the proposition on the parameters of a lift weight. Conclude that the joint harmonic in the theorem is never the junk value.

*Hint.* The hypotheses give that $l$ is a parameter of $(\kappa, e_c)$, that $l'$ is a parameter of $(\kappa, e_a)$, and that $(\kappa, e_c)$ goes up along $e_b$. These are the inputs of the proposition.

**Exercise 5.** Let $\sigma$ be complex conjugation. Use the fact that $|\Delta(g)|^2$ is a natural number to show that the multiplier ratio $\sigma(\Delta(g))/\Delta(g)$ has modulus $1$. Then show that the Galois law for $\sigma = \mathrm{id}$ and $b = 1$ says that $L$ commutes with the finite Weil representation on the finite part.

*Hint.* For complex conjugation, $\sigma(\Delta)/\Delta = \bar{\Delta}/\Delta = \bar{\Delta}^2/|\Delta|^2$. Here $|\Delta(g)|^2$ is the index of a sublattice in the standard lattice, so it is at least $1$ and $\Delta(g) \neq 0$. Without this, the convention $1/0 = 0$ would make the ratio $0$.

**Exercise 6.** In the classical seesaw of Section 5, the two sides are equal by Fubini's theorem. Find the results of Section 3 that give the absolute convergence of the double integral, for $y$ of moderate growth and $f$ of rapid decay. Which hypothesis on the forms is used, and where does the moderate growth of the kernel enter?

*Hint.* The kernel is bounded by a power of the product of the heights. A form of rapid decay beats every power of the height, and the measure of $[S]$ is finite.

**Exercise 7.** Prove the equivariance of the algebraic lift in full. Write the class integral as a finite sum over double cosets $\Gamma \backslash G_f / K$ with weights, and show that right translation by $a$ permutes the terms when $K$ is replaced by a smaller level fixed by $a$. Where is the condition that every datum has an open stabilizer used?

*Hint.* The integrand at $(g, h)$ is right invariant under the intersection of the stabilizer of $\varphi$ and the stabilizer of the datum in the first factor. This intersection is open, so the class integral at a smaller level gives the same value.

## Notes and references

The theta correspondence in adelic form goes back to Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964) 143-211, which constructs the Weil representation and proves that theta series are automorphic. The modern theory of dual pairs is due to Howe. His paper *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989) 535-552, proves the duality correspondence for real dual pairs. The $(\mathrm{GL}_{n'}, \mathrm{GL}_n)$ duality on polynomials on matrices, which Section 6 refers to, is a classical case of the same theory. The book of Mœglin, Vignéras and Waldspurger, *Correspondances de Howe sur un corps p-adique*, Lecture Notes in Math. 1291 (1987), gives the local theory at the finite places. The classical theta series of a positive definite quadratic form, the model case of Section 1, is in Serre, *A Course in Arithmetic*, Chapter VII, Section 6.

The seesaw principle is due to Kudla, *Seesaw dual reductive pairs*, in Automorphic Forms of Several Variables, Progr. Math. 46 (1984) 244-268. The form of Section 5 differs from the classical one in three ways. The two pairs need not sit in one symplectic group. Their kernels need to agree only up to weights of moderate growth, and only on a spanning set of Fock polynomials. The statement concerns finite sums of periods that are proportional to a fixed family of numbers, and it uses the convolution property of edges in place of a decomposition into irreducible representations.

The rapid decay of theta kernels for data of full rank at a split place, in Section 3, is related to the convergence results of Kudla and Rallis, *A regularized Siegel-Weil formula: the first term identity*, Ann. of Math. 140 (1994) 1-80, and to the theta dichotomy of Harris, Kudla and Sweet, *Theta dichotomy for unitary groups*, J. Amer. Math. Soc. 9 (1996) 941-1004. The treatment here uses shifts along a short isotropic vector and reduction theory, and it does not use the Siegel-Weil formula.

The lifting of discrete series types along joint harmonics, in Section 4, follows J.-S. Li, *Theta lifting for unitary representations with nonzero cohomology*, Duke Math. J. 61 (1990) 913-937. See also A. Ichino, arXiv 2002.09148, Lemma 7.8. The block rule for the correspondence of parameters is of the type studied by A. Paul, *First occurrence for the dual pairs (U(p,q), U(r,s))*, Canad. J. Math. 51 (1999) 636-657. The treatment here proves that an edge carries forms of one type to forms of the other type and back, but it does not use Howe duality, and it does not prove that the lift of a nonzero form is nonzero. The constants of Sections 4 and 6 are not shown to be nonzero.

Algebraic modular forms on definite groups are due to Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999) 61-93. The correspondence of highest weights between compact unitary groups and their partners in the Fock model is in Kashiwara and Vergne, *On the Segal-Shale-Weil representations and harmonic polynomials*, Invent. Math. 44 (1978) 1-47. The theorem of Section 6 that the harmonic lift is a multiple of a class sum of jets leaves the multiple unspecified.

The Galois action on theta functions with complex multiplication is due to Shimura, *Theta functions with complex multiplication*, Duke Math. J. 43 (1976) 673-696. The formal treatment also refers to J. Trias, *On the rationality of the Weil representation and the local theta correspondence*, arXiv 2601.16141, which is a preprint and has not been refereed. The Galois law of Section 6 is stated for any semilinear map that scales translations. The maps that the argument uses are built in later chapters, in [theta kernels and gauges](/chapter/theta-kernels-gauges/) and [Hecke values](/chapter/hecke-values/).

The findings of the register that concern this chapter are the joint harmonic as a choice with a junk value, the constant $\beta$ that can be $0$, the hypothesis of a spanning set in the seesaw and the place where it is supplied, the preprint of Trias, the unsealing of the finite part for a whole file, and the absence of any proof that the lifts are nonzero.

Status: drafted by a model. No person has checked this chapter against the Lean source.
