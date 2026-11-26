---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\nu$ be an odd integer and $o > 0$. Use the formula $v_2(\nu^{2o} - 1) = v_2(\nu^2 - 1) + v_2(o)$ to show the following. If $\nu^o \equiv 1 \pmod{2^{s+1}}$, then $2^s$ divides $(\nu - 1)o$ or $(\nu + 1)o$. Then, with the lemma on powers of $2$ of Section 2, show that $2^{e+1} \mid o$ when $2e < s$ and $2^{e+1}$ divides neither $\nu - 1$ nor $\nu + 1$.

*Hint.* Exactly one of $\nu - 1$ and $\nu + 1$ is $2$ modulo $4$. So $v_2(\nu^2 - 1) = v_2(\nu - 1) + v_2(\nu + 1) = \max(v_2(\nu - 1), v_2(\nu + 1)) + 1$. For the second part, apply the lemma with $q$ equal to $\nu - 1$ or $\nu + 1$.

**Exercise 2.** Let $\Lambda$ be a marked set. Show directly that $\#\Lambda \le f$. Let $D$ be the set of primes $w_\tau$ with $\tau$ an a-place. Show that a full mark contains at least $\#D/2$ primes of $D$.

*Hint.* A marked set contains at most one of $w$ and $\bar w$, and the primes of $E$ above $p$ come in conjugate pairs. A full mark meets each pair $\{w_\tau, \bar w_\tau\}$, and each such pair holds at most two primes of $D$.

**Exercise 3.** Let $\Lambda$ be a finite set of primes. Show that $\sum_{\mathfrak l \in \Lambda} A_{\mathfrak l} \le a f$. Deduce that the scale $\prod_{\mathfrak l \in \Lambda} p^{A_{\mathfrak l}}$ of a product of scaled Hecke operators over a marked set is at most $p^{af}$.

*Hint.* Use the lemma $\sum_{\mathfrak l \in \Lambda} A_{\mathfrak l} = a\cdot\#(\Phi_a \cap \Phi_\Lambda)$ of Section 4 and $\#\Phi_a \le \#\Phi = f$.

**Exercise 4.** Let $\|\cdot\|$ be an ultrametric gauge on a vector space $V$ over $\mathbb C_p$, so $\|u + v\| \le \max(\|u\|, \|v\|)$ and $\|cv\| = |c|_p\|v\|$. Let $v_1, \dots, v_n \in V$ with $\|v_i\| \le C$, and let $r_1, \dots, r_n \in \mathbb C_p$ with $|r_i|_p \le p^{c}$. Show that $\|\sum_i r_iv_i\| \le p^cC$, and that no factor $n$ appears. Explain why this is the reason the chain combination of Section 6 has a gauge bound that does not grow with the size of the support of $\Psi$.

*Hint.* Induction on $n$. Compare the triangle inequality of an archimedean norm, which gives $np^cC$.

**Exercise 5.** In the notation of Section 8, compute the exact number of gluing classes as a power of $N$. Show that it equals $N^{fmn_m/2}$ if and only if $n_{2i+1} = n_m$ for all $i \le \varrho$.

*Hint.* The classes are the families $(y_i)_{i \le \varrho}$ with $y_i : X_{2i+1}\times\Pi_N \to \mathbb Z/N$. Each $y_i$ ranges over a set of $N^{f n_{2i+1}}$ elements. The dimensions $n_j$ are increasing in $j$.

**Exercise 6.** Let $z, t$ be two matrices with entries in $\mathbb A_f$, with disjoint supports in the sense of Section 8: at each place, the conjugate of $t$ and $z$ are not both nonzero. Using the composition law $\varrho_f(z)\varrho_f(t) = \chi(\bar t\cdot z)\varrho_f(z + t)$, show that $\varrho_f(z)$ and $\varrho_f(t)$ commute. Give an example in one variable, at two places $w, \bar w$ above $N$, where the supports are not disjoint and the phase $\chi(\bar t\cdot z)$ need not be $1$.

*Hint.* The phase of $\varrho_f(t)\varrho_f(z)$ is $\chi(\bar z \cdot t)$. If $\bar t\cdot z = 0$ at every place, then $\bar z \cdot t = 0$ too. For the example, take $t$ with a pole $1/N$ at $w$ and $z$ with a pole $1/N$ at $\bar w$.

**Exercise 7.** Let $\Psi$ be a chain datum, and let $\Psi'$ be the weak chain datum of Section 8 with $\varphi^\flat_{\Psi'} = \mathrm{Glue}\,\varphi^\flat_\Psi$. Show that the tuples $x + z(y)$ with $y \ne 0$ are not integral at the places above $N$. Explain why the gauge bound of Section 6 at $p = N$ does not apply to $\Psi'$, and why the projection of Section 8 avoids this.

*Hint.* The column $-y/N$ has a pole at each $w \in \Pi_N$ with $y(w) \ne 0$, by the lemma on pole columns. The projection $P_N$ kills the translates by such matrices and fixes $\varphi^\flat_\Psi$, whose tuples vanish above $N$.

## Notes and references

The chapter follows three files of the source: MarkedPrimes.lean (Sections 2 to 4), ChainValuation.lean (Sections 5 to 7) and ChainDatumExpansion.lean (Section 8), all in New/UpperBound/Divisibility. No file of the chapter imports a file of a later chapter of this volume. The order of the chapters is that of volume.yaml; the list of Volume 9 in the plan of the handbook is older and differs from it.

Decomposition groups and the splitting of primes in a Galois extension, used in Section 2, are in Neukirch, *Algebraic Number Theory*, Chapter I, Section 9. Valuations and the ultrametric inequality, used in Sections 5 and 6, are in the same book, Chapter II, Section 3. The formula for $v_2(\nu^{2o} - 1)$ of Exercise 1 is the lifting the exponent lemma at the prime $2$. The source proves the form that it uses.

The method of the divisibility side is that of the argument in this book. The marks, the scaled Hecke operators and the chain valuation are not taken from a published source, and this book does not compare them with the literature. The joint invariance turns an integral over a level into a finite sum of class volumes. This chapter does not depend on a published statement on theta lifts.

Three points of the notes of the specification differ from the source. The expansion of the gluing is in this chapter, in ChainDatumExpansion.lean, and not in the chapter on divisibility. The chain valuation uses the plain sum of kernel products with the ultrametric gauge at $p$, not a statement on sums in a set of large valuation at a prime above $N$. The characters at a level do not use full marks; the findings of the specification already note this.

Status: drafted by a model. No person has checked this chapter against the Lean source.
