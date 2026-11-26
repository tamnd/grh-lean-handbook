---
title: How to read this book
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## How to read this book

This chapter is a guide to the rest of the book. It proves no theorem. It says who the book is for and what it assumes. It gives the thirteen volumes, the reason for their order, and a map of the proof. It gives four reading paths, each as an exact list of chapters. It describes the form of a chapter, so that a reader knows what each part of a page does. It explains the three status labels of a chapter, and it says how to report an error. The last section has exercises and notes.

A long proof is hard to read for a simple reason. Its steps come in the order in which they depend on each other, and that is not the order in which a person understands them. The source of this book is a Lean development of about 300,000 lines in 803 files. Its background theories alone are longer than most monographs. A reader who starts at the first file and reads to the last one meets each idea long before its purpose is clear. This book does not follow the files. It follows the order in which a student learns a long proof: first the whole design, with every size, then each theorem that the design needs, then the background theory under each theorem. This chapter explains that order and how to use it.

### What the book is

The book explains the Lean proof of the generalized Riemann hypothesis for Dirichlet L-functions in the repository lsernau/grh-lean. It follows the readable edition `grh/` of the source, at the commit that the title page names. The source states five theorems. [The theorem and the plan](/chapter/theorem-and-plan/) states them in full. The main one is the half-plane theorem: for every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$. Here $\chi_0$ is the principal character modulo $q$.

The book is an explanation of mathematics. Each chapter takes one part of the source, states its results in the words of a textbook, and proves them on paper from the results below them. When the object of the source differs from the object of the literature, the chapter says how, and says why the argument does not need more. After the book, a reader can do five things:

1. state each step of the proof exactly, with its sizes;
2. prove each step on paper, from the results of the steps below it;
3. find the Lean declaration of each statement and read its type;
4. say what the source proves in full, what it proves in a weaker form than the literature, and why the weaker form is enough;
5. say what Lean checks, what is only claimed, and what no person has checked yet.

### What the book is not

The book is not a check of the proof. It does not say that the proof is correct, and it does not say that GRH is proved. It says what the source claims, what Lean accepts if the reported checks hold, and what each chapter explains. [The claim and its status](/chapter/claim-and-status/) gives the evidence for the claim and its limits. In short: the repository has no logs of its machine checks, this book did not run them again, and the source says that no mathematician has read the proof through.

The book is also not a list of declarations. The readable edition has many thousands of them. A chapter states the 10 to 40 results that carry its argument, and it puts the small lemmas, the second names and the wrappers into the `Lean:` lines and into the proofs. A reader who wants every name uses [the index of Lean names](/chapter/lean-index/).

The book is not a paraphrase of the comments of the source. The source has a comment at the head of each file and a map of its folders. These are notes by the authors of the code. Lean checks none of them. A writer of this book reads them as a guide, and checks each fact in the Lean text.

### Who the book is for

The main reader is a graduate student in number theory who wants to learn the proof and its methods. The book is written for that reader, as one mathematician explains a long proof to a strong student. Other readers can use it with a shorter path.

| Reader | Knows | Wants | Path |
|---|---|---|---|
| A graduate student in number theory | analytic and algebraic number theory, some automorphic forms | to learn the proof and the methods | all volumes, in order |
| An analytic number theorist | L-functions, zero density, sieves | to judge the reduction and the sizes | the background path of Section 3 |
| An expert in automorphic forms or arithmetic geometry | theta, Shimura varieties, Galois representations | to judge Theorems A, B and C | the outline, then one theorem (Section 3) |
| A referee | the field | to find the weakest step | the outline, the register of findings, then the volume of the step |
| A Lean user | Lean and Mathlib | to read and check the formalization | the Lean path of Section 3 |

A referee starts with [the register of findings](/chapter/register-of-findings/). It lists each point where the documents of the source and its Lean text differ, where a definition is weaker than its name, and where a question is open, with the chapter that explains it.

### What the book assumes

The book assumes a first course in each of four subjects.

1. Complex analysis, and the analytic theory of Dirichlet L-functions at the level of Davenport, *Multiplicative Number Theory*, chapters 1 to 9.
2. Algebraic number theory: Neukirch, *Algebraic Number Theory*, chapters I to III, or the same material in another book.
3. Lie groups and their representations: Knapp, *Lie Groups Beyond an Introduction*, chapters I to V, or the same.
4. Commutative algebra and schemes: Atiyah and Macdonald, *Introduction to Commutative Algebra*, and Hartshorne, *Algebraic Geometry*, chapter II, or the same.

Volume 1 needs only the first two. The background volumes need more, and each of them opens with its own list of prerequisites and the textbook chapters that give them.

The book does not assume that the reader knows Lean. The text is mathematics. The code appears in two places only: the `Lean:` line under each statement, and the remarks on the formalization. A reader who skips both reads a textbook. A reader who wants to read the Lean types needs only the little Lean of [reading the Lean](/chapter/reading-the-lean/).

### One notation

The book uses one notation in every volume. [Notation and conventions](/chapter/notation/) fixes each letter: the modulus $q_0$, the prime $d$, the fields $K$ and $E$, the sets of places $\Phi_a$ and $\Phi_b$, the scales $x$, $x_1$ and $b$, the number $m$ of lifts, and the rest. [The table of sizes](/chapter/sizes/) collects every size with the file of the source that imposes it. Where the source uses two letters for one object, or one letter for two objects, the book keeps one letter and gives the Lean name in the `Lean:` line. A reader who meets a letter with no definition nearby looks it up in the notation chapter, not in the source.

### The plan of the chapter

Section 2 gives the thirteen volumes, a map of the proof, and the reasons for the order. Section 3 gives the reading paths. Section 4 describes the form of a chapter, with an example from Volume 1. Section 5 explains the status labels, gives the status of the chapters at the time of writing, and says how to report an error. Section 6 has exercises and notes.
