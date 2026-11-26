# Changelog

## Unreleased

## v0.2.4

New chapters since v0.2.3:

- Volume 5, chapter 5, Characters of GL_n over a finite field (#86).
- Volume 5, chapter 6, Iwahori exponents, Satake and the chain lemma (#87). Volume 5 is now complete.
- Volume 6, chapter 2, Local theta correspondence (#89).
- Volume 6, chapter 3, Theta kernels, theta lifts and the seesaw (#88).

Each chapter has the status `drafted`. No person has checked it yet. The book does not claim that the proof is correct.

## v0.2.3

New chapters since v0.2.2:

- Volume 4, chapter 3, Automorphic forms on unitary groups (#81).
- Volume 5, chapter 3, Bessel subgroups and Bruhat measures (#83).
- Volume 5, chapter 4, Integral Weyl modules and branching (#82).
- Volume 6, chapter 1, The Weil representation (#84). This opens Volume 6.

Each chapter has the status `drafted`. No person has checked it yet. The book does not claim that the proof is correct.

## v0.2.2

New chapters since v0.2.1:

- Volume 2, chapter 7, Sets with no three-term progressions (#77). Volume 2 is now complete.
- Volume 4, chapter 2, Quotients and reduction theory (#76).
- Volume 4, chapter 4, A simple trace formula (#78).
- Volume 5, chapter 2, The Laplace method (#79).

Each chapter has the status `drafted`. No person has checked it yet. The book does not claim that the proof is correct.

## v0.2.1

New chapters since v0.2.0:

- Volume 2, chapter 6, Pólya-Vinogradov and quadratic twists (#71).
- Volume 3, chapter 3, Local duality and the Greenberg-Wiles count (#72).
- Volume 3, chapter 4, Odd classes over cyclotomic fields (#74).
- Volume 5, chapter 1, Discrete series through one matrix coefficient (#73).

Each chapter has the status `drafted`. No person has checked it yet. The book does not claim that the proof is correct.

## v0.2.0

Milestone G1, The guide and the outline, is done.

- Volume 0, The guide, has all 10 chapters. The last one is chapter 8, The register of findings (#69): 126 points that a careful reader of the source must know, each checked against the pinned source.
- Volume 1, The proof in outline, has all 13 chapters. It gives the whole proof modulo Theorems A, B and C, which are stated in full.
- Volumes 9 to 12 each have their opening chapter, with the plan of the volume.

Since v0.1.8:

- Volume 2, chapter 5, Primes in windows (#68).
- Volume 3, chapter 2, Class field theory on finite ideles (#67).

Background chapters of Volumes 2, 3 and 4 have started for the next milestones.

Each chapter has the status `drafted`. No person has checked it yet. The book does not claim that the proof is correct.

## v0.1.8

New chapters:

- Volume 0, chapter 1, Preface (#61).
- Volume 0, chapter 10, Glossary and index of Lean names (#63). The index lists the Lean names that the written chapters cite, and it is rebuilt at each release (#64).
- Volume 2, chapter 4, The prime number theorem in progressions (#60).
- Volume 4, chapter 1, Adeles and hermitian spaces (#65). This is the first chapter of Volume 4 in a release.

Fix: one file count for the source in Volume 0 (#62).

Volume 0 now has 9 of its 10 chapters. Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.7

New chapters:

- Volume 0, chapter 4, How to read this book (#58). It gives reading paths through the 13 volumes.
- Volume 0, chapter 6, The table of sizes (#57).
- Volume 3, chapter 1, CM fields, towers and places (#53). This is the first chapter of Volume 3 in a release.

Fixes:

- Volume 1 now uses the notation of Volume 0, chapter 5 in all chapters (#55).
- The builder now treats `namespace A.B` and `end B` as Lean 4 does (#56).

Volume 0 now has 7 of its 10 chapters. Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.6

Four new chapters:

- Volume 2, chapter 1, Dirichlet L-functions and zero symmetry (#50). This is the first chapter of Volume 2 in a release.
- Volume 2, chapter 2, Polar functions and the explicit formula (#48).
- Volume 2, chapter 3, Landau's theorem (#52).
- Volume 12, chapter 1, Regular families: the plan (#51). Each of Volumes 9 to 12 now has its opening chapter.

Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.5

Four new chapters of Volume 0, The guide:

- Chapter 3, The statements (#47).
- Chapter 5, Notation and conventions (#45). It fixes one notation for the whole book.
- Chapter 7, Reading the Lean (#44).
- Chapter 9, The two editions (#46). It gives a name map from grh-compact to grh.

Volume 0 now has 5 of its 10 chapters. Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.4

Volume 1, The proof in outline, now has all 13 chapters.

New chapters:

- Volume 0, chapter 2, The claim and its status (#41).
- Volume 1, chapter 11, The lattice of integral target forms (#42).
- Volume 9, chapter 1, Theorem A and its plan (#38).
- Volume 10, chapter 1, Theorem B and its plan (#39).

Fix: the plan of Volume 9, chapter 5 now says that the seesaw constant is a unit, and that the identity is empty when the factor c₀C/d is 0 (#40).

Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.3

Three new chapters and one fix:

- Volume 1, chapter 1, The theorem and the plan (#33).
- Volume 1, chapter 5, Why a lattice can bound a prime sum (#35).
- Volume 11, chapter 1, Theorem C and the height argument (#34). This is the first chapter of Volume 11 in a release.
- Fix: in the outline, Theorem B gives the count of translates and the dimension that Theorem C must fill; it is not a lower bound (#36).

Volume 1 now has 11 of its 13 chapters. Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.2

Four more chapters of Volume 1, The proof in outline:

- Chapter 6, Fields, places and twists (#29).
- Chapter 8, The data exist (#25).
- Chapter 12, Theorems A, B and C (#28).
- Chapter 13, The main inequality and the end of the proof (#27).

Volume 1 now has 9 of its 13 chapters. Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.1

Four chapters of Volume 1, The proof in outline:

- Chapter 3, The weighted prime remainder (#23).
- Chapter 4, Landau's criterion (#22).
- Chapter 7, The data and its sizes (#21).
- Chapter 10, Twisted lattices (#24).

Each chapter has the status `drafted`. No person has checked it yet.

## v0.1.0

The first release of The GRH Lean Handbook. It explains the Lean proof of GRH in lsernau/grh-lean, readable edition, at commit 72fead1.

- The builder `ghb`: check, build, ledger, survey.
- The front pages, with the status of the claim.
- The plan of 13 volumes, about 545,000 words.
- Volume 1, chapter 2: From the half-plane to the line (#19). It proves zero reflection for every Dirichlet character and deduces the five theorems from the half-plane statement.

Each chapter has the status `drafted`. No person has checked it yet.
