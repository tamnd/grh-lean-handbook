---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

**Exercise 1.** Let $r = 5$ and two lifts, so $k = 4$ and $\varrho = 0$. Write the row parameter of Section 2 for $i = 0, 1$ and check that its entries decrease strictly.

*Hint.* The near entries are $k/2 - 1 - i = 1 - i$. The far entries are $\Delta/2 - \kappa_{i+2-k}$, and $\Delta = 2r^8$ is much larger than $N$.

**Exercise 2.** In the packing bound of Section 4, the last columns of the cosets that meet the level condition are $R\lambda$ apart. Show that halving $R$ multiplies the bound $(5/\rho)^A$ for the sum of the inverse powers by at most $2^A$.

*Hint.* The separation $\rho$ is proportional to $R$. Only the factor $\rho^{-A}$ depends on it.

**Exercise 3.** In the proof of the halving lemma away from the cusp (Section 5), the sizes give $16\beta\,|y(x)| \le 10S$. Which size condition makes this the bound $|y(x)| \le S/2$, and would $\beta \ge 1$ suffice?

*Hint.* The bound needs $10/(16\beta) \le 1/2$, so $\beta \ge 5/4$. The source uses $\beta \ge 16$ from $2000(n + L + 1)^6 \le \beta$. Check where else $16 \le \beta$ enters: the kernel bound with $16^A$.

**Exercise 4.** Explain why the vanishing criterion needs a lower bound for the local pairing at every infinite place, and not only at one.

*Hint.* The number $\eta$ of the rank one formula is a product over the places $w$ (`integral_translatedCoeff_mul_eq_prod`). A product is small if one factor is small.

**Exercise 5.** Let $V$ be a positive definite space of rank $1$ over $E$, so that $\lambda(V, x)$ is bounded below for all $x$. Which half of the proof of the vanishing criterion is then not needed for large $m$?

*Hint.* The cusp case needs $\lambda(V, x) < (m^{-2}/(M\kappa^2))^n$. For large $m$ this fails at every $x$.

**Exercise 6.** Show the step of Section 7 that the image of $\Theta^\flat$ is the whole space $\mathcal F^0_{\mathfrak b}$ in a model: $V = W = \mathbb C^n$ with the standard inner product, $T : V \to W$ linear with $T^*$ injective. Show that $T$ is onto.

*Hint.* If $z \perp T(V)$, then $\langle T^*z, v\rangle = 0$ for all $v$, so $T^*z = 0$ and $z = 0$. In Section 7 the chain $W_m$ plays the role of $T^*$ through the transposition identity.

**Exercise 7.** In the theorem on integrality and size (Section 8), the proof chooses $s = hN/\beta$ if $\beta \ne 0$. Show that with $s = 1$ in both cases, part 1 can fail, and that part 2 then holds only with $|\beta|^2$ in the bound.

*Hint.* The value is $\beta\,\Xi$, and $\beta$ has no denominator bound. The factor $hN$ clears the denominators of $\Xi$ and of the dual pairing.

### Notes and references

The source claims the results of this chapter in the files New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean, DeepLevelVanishing.lean, FirstPath.lean and SpanningForms.lean, at the pin 72fead1. Lean accepts them, if the reported checks hold. The text does not claim that the argument is correct beyond this.

The docstring of DeepLevelVanishing.lean says that nonvanishing periods through Poincaré series of deep level and restriction results of Burger and Sarnak type are known. It names three works as related. The source does not use them in the proofs. We list them as the source names them.

- D. Prasad and R. Schulze-Pillot, Generalised form of a conjecture of Jacquet, 2008.
- M. Harris, Testing rationality of coherent cohomology of Shimura varieties, 2014.
- G. Muić, Fourier coefficients of automorphic forms and integrable discrete series, 2015.

The results of this chapter are used in two places. Volume 10 uses the steep parameters (`New.Data.exists_isSteep`, Section 2) in [the Bessel functions at a real place](/chapter/bessel-real-place/) (the file FillingData.lean imports DeepLevelPoincarePeriod.lean). The spanning theorem is the input of `New.Data.exists_span_isAuxiliaryForm_eq_top` in New/Determinant/Twist/LongForms.lean, the passage to target forms ([Theorems A, B and C](/chapter/theorems-a-b-c/)).

Formalization notes, collected from the sections.

- The radius $m$ of the deep level sizes is a real number. It is not the number of lifts of the data (Section 5).
- The points $\omega$ and $g$ of the vanishing criterion come from `choose` and existentials. They are not explicit (Sections 5 and 6).
- The sums over cosets in Sections 3 and 4 are `tsum`s. The source proves their summability before it uses them, so no junk value enters the bounds.
- The constants $\alpha$ (Section 7) and $\beta$ (Section 8) may be $0$ as far as the statements go. If $\beta = 0$, the spanning theorem holds because the lifts of the restrictions vanish. The theorem is still true as stated.
- The file FirstPath.lean imports GridFirstColumns.lean, and SpanningForms.lean imports DiagonalTurns.lean, LastPath.lean and FirstFactors.lean. These lie in chapters 9 and 10 of this volume, which come before this chapter. No file of this chapter imports a file of a later chapter.

The handbook plan lists this chapter as number 9 of Volume 11, with the files DeepLevel and SpanningForms. The file volume.yaml puts it at number 11, after the comparison operator and the grids. The chapter also covers FirstPath.lean, which the plan does not name.
