---
title: Why read a machine proof
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Why read a machine proof

A proof checked by a machine seems to need no reader. If the kernel of Lean accepts a term of a type, then the type holds, under the usual assumptions on the kernel and the axioms. So why write a textbook on such a proof, and why should a student read one? This section gives three answers. The first is about what a kernel check leaves open. The second is about what a mathematician wants from a proof. The third is about what a reader gains in any case, even if the proof turns out to have gaps.

### What a kernel check leaves open

A kernel check is strong evidence of a narrow kind. It shows that a term has a type. It does not show that the type says what a reader thinks it says. For the five theorems of the source, this gap is small by design. Their types use a few definitions of Mathlib and the 16 lines of the file of statements, and a person can read them in an afternoon. [The statements](/chapter/statements/) does that reading. But the gap is real, and only a person can close it.

The kernel check also does not exist, for this book, as a record. The source reports four kinds of machine check: a full build, a list of axioms, an export that three independent checkers accept, and a run of the tool Comparator "with a stand-in for its sandbox" (`grh/README.md`, line 30). The repository holds the files that set up these checks. It holds no output of any of them. [The reported checks](/chapter/claim-and-status/#the-reported-checks) gives each check, what it would show, and how a reader can run it again.

Last, a kernel check says nothing about the meaning of the inner statements. The source has more than 20,000 declarations (`grh/README.md`, line 28). Many of them use definitions of the source that are narrower than the textbook objects with the same names. The kernel checks each proof against its type. It does not check that a definition called a cohomology group is the cohomology group of the literature. For the truth of the five theorems this does not matter, because no definition of the source enters their types. For a reader who wants to learn the method, it matters on every page.

### What a mathematician wants from a proof

A mathematician wants more from a proof than the truth of its conclusion. A mathematician wants to know why the conclusion holds: which idea carries the argument, which step is hard, which hypothesis is used where, and what else the method can prove. A Lean development does not give this. Its files come in the order of their dependencies, which is not the order in which a person understands them. Its background theories alone are longer than most monographs. A reader who starts at the first file and reads to the last meets each idea long before its purpose is clear.

A textbook gives the other order. It starts with the design, states each step exactly, gives the idea of each proof before its steps, and puts a model case before the general case. This is the form of the books that a graduate student learns from, such as Iwaniec and Kowalski, *Analytic Number Theory*, or Bump, *Automorphic Forms and Representations*. This book tries to give the source that form.

A proof of a famous conjecture by a new method is also a claim on the attention of the field. The field can judge the claim only if a person can follow the method. The source says that no mathematician has read the proof through. One reason is its length: the readable edition has about 300,000 lines of code. A textbook that puts the method into a few hundred thousand words of mathematics, with each statement tied to its Lean declaration, makes a reading by a person possible. It does not replace that reading. It makes the reading shorter, and it divides it into parts that one person can check at a time.

### What a reader gains in any case

The status of the claim is open, in the sense of [the claim and its status](/chapter/claim-and-status/). A reader can ask what the book is worth if the claim fails: if the reported checks do not hold when a person reruns them, or if a person finds that a statement of the book or of the source does not mean what it seems to mean. The book is written so that its value does not depend on the answer.

First, the methods. The argument passes through a large part of modern number theory: the analytic theory of Dirichlet L-functions, Landau's theorem on Dirichlet series with coefficients of one sign, zero density for quadratic twists, class field theory and complex multiplication, automorphic forms on definite unitary groups, discrete series and the representations of finite groups of Lie type, the theta correspondence and the Siegel-Weil formula, $p$-adic Hodge theory, and the Galois representations attached to automorphic forms. Each background volume states the classical theory with a source before it gives the form that the argument uses. A student who reads these volumes learns the theory in a form tied to one concrete use, with every size explicit.

Second, a map. If the proof has a gap, the gap is in some step, and the book names every step with its exact statement, its sizes and its Lean declaration. A person who doubts one step can find the chapter that explains it, read its statement against the Lean type, and follow its proof down to the results that it uses. [The register of findings](/chapter/register-of-findings/) collects each point where the documents of the source and its Lean text differ, where a definition is weaker than its name, or where a question is open. A gap, if there is one, is easier to find and to describe with this map than without it.

Third, the habit of reading formal statements. A mathematician will meet more formal proofs, and more proofs that a machine helped to write. The book shows, on one long example, how to read a Lean statement, what a junk value is and where it matters, what a kernel check guarantees, and what it does not. [Reading the Lean](/chapter/reading-the-lean/) collects these rules. They apply to any formal proof, and they do not depend on this one.

Fourth, the design. Volume 1 proves the five theorems from Theorems A, B and C in full. The step from the three theorems to the five is a reduction of a zero-free half-plane to a one-sided bound for a prime sum, and of that bound to an inequality between two bounds for the covolume of one lattice. A reader can study this design and judge it as mathematics, whatever the status of Theorems A, B and C. [The idea of the method](/chapter/theorem-and-plan/#the-idea-of-the-method) gives it in a few pages.
