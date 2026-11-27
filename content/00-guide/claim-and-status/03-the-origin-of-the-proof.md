---
title: The origin of the proof
lean:
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The origin of the proof

This section collects what the documents of the source say about the authors of the proof, about the earlier proof that it rewrites, and about the two editions in the repository. It then says what is public about the earlier proof, what its method is as the public documents describe it, and which steps the readable edition proves by other arguments. Each quotation names its document: a file of the repository at the pinned commit, or a public document with its URL and page. The section also lists what this book looked for and did not find. It makes no judgement of the persons named.

### What the documents say

The repository has two top folders, `grh/` and `grh-compact/`, and a root README. The documents speak of the authors in five places.

1. The root README says: "The proof is based on Levent Alpöge's, with Claude (https://alpo.ge/remark.pdf). This repository is a shorter version, produced in collaboration with my colleagues at Anthropic, and Claude." (root `README.md`, lines 9 to 11.) The word "my" refers to the person who wrote the README. The README does not name that person. The repository is under the account lsernau.
2. The README of the readable edition says: "The proof is Levent Alpöge's, with Claude. The Lean text and the documents in this project were written by Claude (AI)." (`grh/README.md`, lines 5 and 6.)
3. The same README says: "This project is a shorter rewriting of Levent Alpöge's Lean proof (see <https://alpo.ge/remark.pdf>). It follows that proof's method; many steps are proved by other arguments, and parts of it, mostly background material, were ported from there and then rewritten." (`grh/README.md`, line 10.)
4. The NOTICE of the readable edition says that the file of statements, and the names and types of the five theorems, are "taken from that proof unchanged", and that the lakefile "is adapted from it" (`grh/NOTICE`, lines 6 and 7).
5. The first line of the file of main theorems is the comment "The proof is Levent Alpöge's, with Claude." ([Main.lean](lean:Main.lean#L1)).

The README of each edition thanks "the colleagues at Anthropic whose direction and suggestions shaped this rewriting" (`grh/README.md`, line 41). The license is Apache 2.0, with the copyright line "Copyright 2026 Anthropic, PBC" (root `README.md`, line 38). The root README calls the repository a "Research artifact. Not maintained and not accepting contributions." (line 3).

The two READMEs use different words for the relation to Alpöge's proof. The root README says that the proof is "based on" Alpöge's. The README of the edition says that the proof "is" Alpöge's, and that the edition rewrites his Lean proof. This book does not choose between the two. It reports both.

### What is public

The documents name no paper, and the root README says that none comes with the proof: "No mathematician has read it through, and no paper comes with it." (root `README.md`, line 34.) This sentence is a statement by the source about itself. This book has no evidence against it. A reader must take it at its word: at the pinned commit, by the account of the source, no person has read the proof through.

The URL `https://alpo.ge/remark.pdf` is public. It is a note of four pages by Alpöge, without a title. The file was made on 20 November 2026. It is not a paper. It states the claim, gives the main idea in one paragraph, and lists twenty steps in the order in which they were found. The author says that he presents the proof in Lean only: "It being obviously inappropriate to attempt to post some massive unreadable travesty of "slop", I decided to only present Lean." (`remark.pdf`, page 2.) He also says that a proper account is still to come: "I intend to do my best to understand and impart understanding of this argument and its certain simplifications, to speak about it, to write it properly." (page 1.)

The original Lean proof is also public. Footnote 1 of the note points to one archive in fourteen parts, `https://alpo.ge/lean.tar.gz.part01` to `https://alpo.ge/lean.tar.gz.part14`. This book downloaded the parts on 27 November 2026 and listed the archive. It did not build it. The archive holds 175,187 Lean files and the three files of a Lean project, and nothing else: no README and no guide. It uses Lean 4.33.1 and an earlier commit of Mathlib than the source. Its file of statements is byte for byte the same as `Statements.lean` of the readable edition, as the NOTICE says. Its file of main theorems has the same five names and types, with other proofs.

Three more documents are public. All three are by third parties, and this book reports what they say without making their claims its own.

1. A joint statement of the Lean FRO and the Mathlib Initiative, dated 21 November 2026, at `https://leanprover-community.github.io/blog/posts/riemann-hypothesis/`. It concerns the original proof and the statement `RiemannHypothesis` of Mathlib. It reports the checks that the Lean community ran on that proof.
2. Two pages of checks by Andrew Sutherland (MIT): `https://math.mit.edu/~drew/grh/` for the original proof, and `https://math.mit.edu/~drew/shortgrh/` for the source of this book at the pinned commit. Section 4 describes only the checks that the source itself reports.
3. A working draft of 164 pages, *The Alpöge-Claude proof of the Riemann hypothesis explained for the Riemann zeta function*, dated 21 November 2026, at `https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf`. Its title page says that three AI models wrote it "at the behest of Michael O. Rubinstein". It reads the Lean files of the original for the case of $\zeta$. Its abstract says that the main inequality of the argument "is not proved here". This book calls it the Waterloo guide.

The author of the original has no paper on the proof on arXiv at the date of this section, and this book found no talk or blog post by him on the method.

### The method of the original

The note gives the idea of the method in its own words. "This argument is a descendant of Stepanov's, but multiplicity is hard to find over the integers, corresponding to something like differentiating whole numbers." The new step is to "examine chaining theta lifts if we were to have the same tricks recur but work in a natively automorphic manner." The length of the chain is the square root of the length of the prime sum: "for the von Mangoldt sum of length $X$, Claude's suggested length of chain of theta lifts, in view of each mimicking multiplicity, was $\sqrt{X}$." (`remark.pdf`, page 1.)

The twenty steps of the note (pages 3 and 4) name the parts of the argument. The note warns that some descriptions paraphrase a summary by a model, "which might make zero sense" (footnote 4, page 3). The steps that the Waterloo guide finds in the final proof (its Section I.9, pages 19 to 21) are these:

1. the prime sum $\sum_{n \le X} \Lambda(n)(X/n - 1) - X \log X + (1 + \gamma)X$ (step 5);
2. the divisibility of derivatives on a CM curve at primes inert in the CM field (step 2);
3. iterated theta lifts $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ between totally definite unitary groups, with $m$ about $\sqrt{X}$ (step 8);
4. the norms of the lifts, with the formula of Chowla and Selberg and the mass formula of Siegel (step 9), and a lower bound for the divisibility of the $m$-fold lift (step 10);
5. a seesaw identity: "the period of the iterated lift is a Bessel period independent of the Hecke characters" (step 12);
6. the slope inequality of Bost (step 13), and an integral structure glued across the Hecke characters (step 15);
7. a relative trace formula for the rank (step 16), and a bound for Galois cohomology, "a significant weakening of Vandiver" (step 17);
8. a tower of fields, with a set of places chosen by Behrend's construction (steps 11 and 19).

The guide also reads three steps in the Lean of the original that the note does not list. First, a criterion of Landau type on intervals: if $G(x) \le x^{\theta}$ for all $x$ in $[Y, Y^{3/2}]$, for arbitrarily large $Y$, then $\zeta(s) \neq 0$ for $\operatorname{Re} s > \theta$ (pages 4 and 5). Second, two auxiliary primes $q \equiv 3 \bmod 8$ and $d \equiv 7 \bmod 16$ with $q \mid d + 1$, chosen again for each $Y$, with $\log q$ of size $Y^{\varepsilon/5}$ (its Theorem III.1.1, pages 55 and 56). Third, two scales, the scale $x$ and a much larger scale, where a zero free region controls the primes (page 14).

### Steps that the readable edition proves by other arguments

The source says that "many steps are proved by other arguments" (`grh/README.md`, line 10), and it does not list them. This book compared the statements of the readable edition with the note and with the Waterloo guide. It did not read the proofs of the original, and it does not say that either proof is correct. The comparison is at the level of the plan.

The plan is the same. The readable edition has a criterion of Landau type, weights $\Lambda(n)(1 - \chi_K(n))$ for an imaginary quadratic field $K$, derivatives of theta functions at inert primes, a chain of $m$ theta lifts between definite hermitian spaces with $m$ in $[\sqrt{x}, 2\sqrt{x}]$, a seesaw identity, lattices with heights, a formula of Chowla and Selberg, a set of places built after Behrend, and a bound for denominators from Galois cohomology (`grh/GUIDE.md`, lines 22 to 39 and 57). [The plan of the proof](/chapter/theorem-and-plan/) gives these steps.

The analytic end differs in five ways. Each is a difference of statement, which this book has checked in the source.

1. **All large $y$, not intervals.** The original uses Landau's lemma on intervals $[Y, Y^{3/2}]$. The readable edition proves the bound $R_{q_0}(y) \le y^{-1/2+\varepsilon}$ for all large real $y$, and it uses the classical lemma of Landau for a bound that holds eventually ([OneSidedBound.lean](lean:New/Reduction/OneSidedBound.lean#L200), [Landau.lean](lean:Lib/Analytic/Landau.lean#L217)). The compact edition is closer to the original here. It has a lemma on windows, `IsPolar.exists_window_sub_mul_le` (grh-compact).
2. **Fixed auxiliary moduli.** In the original, $q$ and $d$ grow with $Y$. In the readable edition the modulus $q_0 = 18480q$ is fixed by the modulus $q$ of the character, and $d$ is one prime in the fixed class $d \equiv q_0/2 - 1 \bmod q_0$ ([OneSidedBound.lean](lean:New/Reduction/OneSidedBound.lean#L239), [FieldsAndPlaces.lean](lean:New/Reduction/Data/FieldsAndPlaces.lean#L64)).
3. **The choice of $d$.** The original bounds three twisted prime sums on $[Y, Y^{3/2}]$ by a zero density estimate near $\operatorname{Re} s = 1$ and by mean squares over the moduli (the Waterloo guide, page 15). The readable edition has no twisted prime sums to bound. It chooses $d$ so that the L-functions of the twists $\xi\chi_d$, $\xi$ modulo $q_0$, have no zero in a box to the right of $\operatorname{Re} s = \beta$, from a density bound that uses the inequality of Pólya and Vinogradov ([QuadraticTwist.lean](lean:Lib/Analytic/QuadraticTwist.lean#L796)).
4. **The large scale.** The original controls the primes at the large scale by the classical zero free region, and it chooses $q$ and $d$ so that no exceptional real zero enters (the Waterloo guide, pages 14 and 56). The readable edition uses a prime number theorem with an error term for one fixed modulus at its second cut-off $x_1$ ([PrimeNumberTheorem.lean](lean:New/Reduction/Zeros/PrimeNumberTheorem.lean#L217)). For a fixed modulus, no question of a Siegel zero arises.
5. **The prime sum.** The original uses $G$ with three twists by $\chi_q$, $\chi_d$ and $\chi_q\chi_d$, and for a character $\psi$ of order $o$ a combination of $G$ with the sums of the powers of $\psi$ (the Waterloo guide, pages 14 and 21). The readable edition uses one remainder $R_q$ for the weight $\Lambda(n)(1 - \chi_K(n))$ on the class $n \equiv 1 \bmod q$. Its transform is a mean over all characters modulo $q$ ([PrimeError.lean](lean:New/Reduction/Zeros/PrimeError.lean#L65)).

Three more points may be differences, and this book cannot decide them. The guide gives the sizes $m \approx x^{1/2}$, $k \approx x^{9/2}$ and $n \approx x^{2+8\varepsilon}$ for the original (page 15). The readable edition has $m \in [\sqrt{x}, 2\sqrt{x}]$, $r \in [x^5, 3x^5]$ and $k = r + 1 - m$. The letters may not name the same objects. The note names a relative trace formula for the rank. The readable edition proves Theorem B by a second moment of Poincaré series and cites relative trace formulas only as related work. The note asks for a weakening of Vandiver's conjecture. The readable bound for denominators says that "the orders of the even classes, where Vandiver's conjecture lives, do not enter" ([DenominatorBound.lean](lean:New/Congruences/FirstOrder/DenominatorBound.lean#L46)). This can be the same weakening in other words, or another bound.

### What this book could not find

The book did not find a list of the "other arguments", or of the parts that were "ported from there and then rewritten" (`grh/README.md`, line 10). The comparison above is the reading of this book. Points 1 to 5 rest on the Waterloo guide and on one file of the original, the lemma `landau_window` in the file `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean` of the archive. The algebraic part, Theorems A, B and C of the readable edition against the main inequality of the original, was not compared below the level of the heads of files. So when a chapter of this book says "the method of the source", it still means the method that the Lean files of the readable edition carry out, as this book reads them.

The repository at the pin has one commit, dated 25 November 2026, with the message "Lean proof of GRH". So the history of the repository says nothing about how the rewriting was made.

### Two editions, two proofs

The repository holds two Lean projects. The readable edition `grh/` has about 300,000 lines of code in 803 files under `src/`: 495 in `Lib`, 306 in `New`, and the two files `Main.lean` and `Statements.lean`. The compact edition `grh-compact/` has about 76,000 lines of code (root `README.md`, lines 15 and 16). Each README says that the other edition uses other arguments for some steps (`grh/README.md`, line 12).

The two editions share the file of statements, the five theorem types, the file `Challenge.lean`, the configuration of Comparator, the lakefile, the toolchain and the manifest. Below the file of main theorems they differ. They are two proofs of the same five statements, not two layouts of one proof. One difference is visible at the top of the argument. The readable edition reaches the second cut-off of its prime sums by a prime number theorem in arithmetic progressions with an error term. The compact edition has no such theorem and uses a different argument there. The one-sided bounds that the two editions prove for the same prime sum also have different exponents.

This book follows the readable edition only. A claim about "the source" in this book is a claim about the readable edition at the pin. [The two editions](/chapter/two-editions/) maps the names of the compact edition to those of the readable edition. The documents of the two editions also report different checks. Section 4 gives both lists.

### The documents are notes, not evidence

The documents of the source are written by the same author as the code, by its own account. That author is a model. So the documents are not an independent witness of the proof. They are a map of the code, written with it.

The book uses the documents as notes for the writers, and it checks each fact in the Lean file before it states the fact. The guide of the compact edition says the same thing about itself: "Lean checks neither comments nor this guide." (`grh-compact/GUIDE.md`, line 6.) The readable edition makes a similar point in its list of references: "Only some of the citations were compared with their sources." (`grh/REFERENCES.md`, line 3.) That file counts 228 compared citations, of which 66 have a confirmed place, and it says that the citations of 122 other files were not part of the check (`grh/REFERENCES.md`, lines 5 to 10).

These facts matter for a reader of a later chapter. A file of the source can say that a result is "known" and cite a book for it. The citation may not have been compared with the book. The result in the file may be a special case of the result in the book, or a variant with its own definitions. A chapter of this book that uses such a result states the textbook form with a source that this book checked, then the form of the source, and then the difference.

### What this means for the claim

The origin of the proof does not change what Lean checks. A proof term is checked by its type and its axioms, and not by its author. The origin changes what a reader can take from the documents and from the literature. There is no paper to compare with. The earlier proof is public only as a note of four pages and a Lean archive of 175,187 files. There is no list by the authors of the steps that differ from the earlier proof, and no person who has read the whole. The documents are the work of the same model as the code. So the only independent evidence for the claim is the evidence of the machine checks. Section 4 describes it.
