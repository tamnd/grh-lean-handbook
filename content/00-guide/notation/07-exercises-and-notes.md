---
title: Exercises and notes
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Zeros/PrimeError.lean
decls:
  - New.Parameters
  - New.towerDeg
  - New.Data.k
  - New.Data.n
  - New.Data.offWeight
  - New.lambdaKResidueClass
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Show that $(q_0, d) = (18480, 9239)$ are parameters: $18480 \mid q_0$, $d$ is prime, $q_0 \mid 2(d+1)$ and $q_0 \nmid d + 1$. Find the next two primes $d$ with $(18480, d)$ parameters.

*Hint.* The conditions say that $d + 1$ is an odd multiple of $9240$. Test $d = 9240 u - 1$ for odd $u$. The answers are $46199$ and $64679$.

Lean: `New.Parameters` (New/Reduction/Data/FieldsAndPlaces.lean).

**Exercise 2.** For $s = 22$, compute $l_0$ and the degree of the tower. Check that $l_0 = 729$ and that the degree is $9172942848$.

*Hint.* Use the definitions of Section 2. The number $l_0$ is the power of $3$ with $594 < l_0 \leq 1782$.

Lean: `New.towerDeg` (New/Reduction/Data/FieldsAndPlaces.lean).

**Exercise 3.** Let $m \leq r + 1$. Show that $n_j = k + j(t + 1)$ is $r + 1 - m + j(5r + 1)$ in $\mathbb{N}$, and that Lean's subtraction in $k = r + 1 - m$ is exact. What is $k$ in Lean if $m = r + 2$?

*Hint.* In `ℕ` a difference $u - v$ with $v > u$ is $0$. So $k = 0$ for $m = r + 2$. Lean proves $m \leq r + 1$ from the conditions on the data.

Lean: `New.Data.k` (New/Reduction/Data/AdmissibleData.lean), `New.Data.n` (New/Reduction/Data/AdmissibleData.lean).

**Exercise 4.** The weight off the $b$-places is $\lfloor a/x_1 \rfloor$, a quotient in `ℕ`. Show that $a/x_1 - 1 < \lfloor a/x_1 \rfloor \leq a/x_1$, and explain why the rounding does not change any size of the table of Section 3.

*Hint.* The sizes are bounds on a logarithmic scale, and $a/x_1$ is very large.

Lean: `New.Data.offWeight` (New/Reduction/Data/AdmissibleData.lean).

**Exercise 5.** Let $d = 9239$. Compute $\Lambda_K(n)$ for $n = 2, 3, 4, 9, 9239$, with $\Lambda_K(n) = \Lambda(n)(1 - \chi_K(n))$.

*Hint.* Since $d \equiv 7 \bmod 8$, the prime $2$ splits in $K$, so $\Lambda_K(2) = \Lambda_K(4) = 0$. For $p = 3$ compute the Legendre symbol $(-9239/3)$. At $n = d$ the character is $0$, so $\Lambda_K(d) = \log d$.

Lean: `New.lambdaKResidueClass` (New/Reduction/Zeros/PrimeError.lean).

**Exercise 6.** Section 6 lists the clashes of letters. Choose one chapter of Volume 1 and make a list of its letters. For each letter, give the entry of this chapter that it names, and mark each place where the chapter uses another letter.

*Hint.* Start with the front matter of the chapter: its `decls:` list gives the Lean names, and each Lean name has one entry here.

## Notes and references

The notation of this chapter follows the readable edition of the source at the pinned commit, and the chapters of Volume 1. Where the two disagree, the Lean definitions decide, and Section 6 lists each case.

The notation for Dirichlet characters and $L$-functions is that of Mathlib, which is close to that of Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5. The use of $\Lambda$ for both the von Mangoldt function and the completed $L$-function follows the same book. The notation for CM fields and their places follows Neukirch, *Algebraic Number Theory*, Chapter I. The notation for hermitian spaces and theta lifts follows the comments of the source, which follow the notes on which it rests.

The sizes of the data are given in full in [the table of sizes](/chapter/sizes/) and in [the data and its sizes](/chapter/data-and-sizes/). The junk values of Lean are explained in [Reading the Lean](/chapter/reading-the-lean/). The findings that this chapter names are in [the register of findings](/chapter/register-of-findings/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
