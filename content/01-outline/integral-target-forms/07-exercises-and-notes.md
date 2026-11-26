---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. In the model case of Section 2, let the classes be $c_1, \dots, c_r$ with stabilisers of orders $s_1, \dots, s_r$, and let $\chi$ be trivial. Write the Gram matrix of the forms $\mathbf{1}_{c_1}, \dots, \mathbf{1}_{c_r}$. Show that $A \langle \varphi, \varphi' \rangle$ is integral at $\iota$ for all forms $\varphi$ integral at $\bar\iota$ and $\varphi'$ integral at $\iota$ if and only if every $s_i$ divides $A$ in $\mathcal{O}_\iota$.
   *Hint.* Take $\varphi = \varphi' = \mathbf{1}_{c_i}$ for the converse.

2. Let $u : V \to S$ be a linear map of finite-dimensional complex inner product spaces, and let $v_1, \dots, v_d$ be a basis of $V$. Prove that $\det(\langle u v_i, u v_k\rangle) = \det(u^* u)\det(\langle v_i, v_k\rangle)$. Deduce that $Z(\xi) \neq 0$ when $\Theta_\xi$ is injective.
   *Hint.* Write $v_i = \sum_j P_{ji} e_j$ for an orthonormal basis $e$, and use $\det(P^* M P) = |\det P|^2 \det M$.

3. Let $y_1, \dots, y_n$ be vectors of a twisted lattice with $\|y_i\|_\sigma^2 \leq e^h$ for all $i$ and $\sigma$. Use Hadamard's inequality $\det(\langle y_i, y_k\rangle) \leq \prod_i \|y_i\|^2$ for each conjugate to show that $y$ has covolume at most $nh$. Compare with the definition of covolume in [twisted lattices](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume).

4. Suppose that a proof of Theorem C took $\xi_\iota = 1$ for every $\iota$. Show that the volume term is then $b_{\mathrm{volume}} = 0$, and that the lattice inequality with $n' (2x_1^2 b^2 + b) \leq d_T b$ gives only $0 \leq c + 2\delta + d_T b$. Show that the comparison with Theorem A (a) and A (b) in Section 6 then gives a bound for $m \cdot \mathrm{rem}$ that contains the term $A_{\mathrm{main}}$.
   *Hint.* Put $c = n(A_{\mathrm{main}} - m\,\mathrm{rem} + f a \log^4 b)$ in $0 \leq c + 2\delta + d_T b$ and solve for $m\,\mathrm{rem}$.

5. From $n \cdot m\,\mathrm{rem} \leq d_T(4 f a \log^4 b + 20 \log(1 + 2b^2) f a \log^3 b)$ and $d_T \leq 2n$, deduce $m\,\mathrm{rem} \leq 8 f a \log^4 b + 40 \log(1 + 2b^2) f a \log^3 b$. Show that this is at most $f a \log^5 b$ when $b \geq 3$ and $\log b \geq 128$. Then look up in [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes) whether the data of this book satisfy these conditions.
   *Hint.* For $b \geq 3$, $1 + 2b^2 \leq b^3$.

6. Let $\vartheta$ be an $m$-fold twist with modulus $Q$, and let $\ell$ divide $\mathrm{Nm}\,Q$. Show that $\vartheta$ is not allowed at $\ell$ in the target lattice. Deduce that the integral vectors at $\iota \mid \ell$ impose no condition through $\Theta_\vartheta$, and explain why Theorem C must choose $\xi_\iota$ with $\mathrm{Nm}\,Q$ prime to the prime of $\iota$.
   *Hint.* Compare the lemma on integral target forms with the hypothesis of the lattice inequality on the twists $\xi_\iota$.

## Notes and references

The target lattice is a lattice of algebraic modular forms in the sense of Gross: forms on a reductive group whose real points are compact, given by their values on the finite set of classes $\Gamma \backslash G_f / K$, with class sums weighted by $1/\#\Gamma_g$. See B. H. Gross, "Algebraic modular forms", Israel J. Math. 113 (1999), 61-93. The computational form, with forms as vectors indexed by classes, is in M. Greenberg and J. Voight, "Lattice methods for algebraic modular forms on classical groups", in *Computations with Modular Forms*, Contrib. Math. Comput. Sci. 6, Springer, 2014, 147-179. The source names both works in New/UpperBound/Size/ArchimedeanSize.lean. For the Hecke tower of levels it cites G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton University Press, 1971, chapter 3.

The norm of a theta lift is computed by the Rallis inner product formula. For the norm and injectivity of one theta lift the source names W. T. Gan, Y. Qiu and S. Takeda, "The regularized Siegel-Weil formula (second term identity) and the Rallis inner product formula", Invent. Math. 198 (2014), 739-831, Theorem 1.3. [The chain determinant](/chapter/chain-determinant/) in Volume 11 gives the proof of the factorization of Section 5 in the terms of the source.

The upper bound for the covolume is Hadamard's inequality, applied to every conjugate. The lower bound comes from the product formula, as in a Liouville bound. [Twisted lattices](/chapter/twisted-lattices/#a-lower-bound-for-a-covolume) gives the general form.

The research notes for this chapter describe a twisted lattice as "an injective linear map $\Theta_\xi$" on "a finite-dimensional complex inner product space $V$". The structure `New.TwistedLattice` asks for less. The space $V$ is only a complex vector space, and injectivity is not a field of the structure. It is a hypothesis of `New.TwistedLattice.covolume_add_index_nonneg` and of `New.TwistedLattice.volume_ne_zero`, and for the target lattice it is the lemma `New.Data.injective_lift_targetLattice`. The notes also call the Gram matrix of the coordinates "of Weyl type". In the source it is the block matrix $1 \otimes G_W$ with integer entries, as in Section 4.

Status: drafted by a model. No person has checked this chapter against the Lean source.
