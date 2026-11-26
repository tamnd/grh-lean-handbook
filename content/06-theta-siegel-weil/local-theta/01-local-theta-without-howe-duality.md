---
title: Local theta without Howe duality
lean:
  - Lib/DiscreteSeries/Theta/LocalCorrespondence.lean
  - Lib/DiscreteSeries/Theta/FockDualPair.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Local theta without Howe duality

This chapter treats the local theta correspondence at a real place for a dual pair of unitary groups $U(p,q) \times U(r,s)$, in the case of discrete series with a large gap. It works in the polynomial (Fock) model of the oscillator representation. It proves four facts for two matching parameters. A joint harmonic exists. It is unique up to a scalar. Its projection by the discrete series kernel of the first group is not zero and is fixed by the kernel of the second group. Every projected polynomial is a smoothing of the projected joint harmonic by a bump function on the second group. The chapter also proves that matching is the same as the block rule of Li and Paul, which is the form in which the global argument states the correspondence of parameters.

### What the global argument needs

The global theta lift of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) starts from a cusp form on one unitary group and a vector of the Weil representation. At each real place the vector is a polynomial vector of the Fock space. The lift is a form on the other unitary group. The source needs two local facts at each real place. First, a lift of a discrete series vector of a given parameter $\lambda$ is not zero. Second, the lift of every polynomial vector is a combination of right translates, smoothed by bump functions, of the lift of one vector. The second fact lets the source control all lifts of the space by one lift.

In the textbook account these facts follow from Howe duality and from a theorem of Li. Howe duality says that the oscillator representation $\omega$ of $U(p,q) \times U(r,s)$ gives a bijection between some irreducible representations of the two groups, and that the multiplicity of $\pi \otimes \pi'$ in $\omega$ is at most one (Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989)). Li proved that, in the stable range and for discrete series with nonzero cohomology, the correspondence sends a discrete series to a discrete series, and that the joint harmonics of Kashiwara and Vergne give the lowest $K$-types (J.-S. Li, *Theta lifting for unitary representations with nonzero cohomology*, Duke Math. J. 61 (1990) 913-937). Paul computed the correspondence of discrete series parameters for all real unitary dual pairs (A. Paul, *First occurrence for the dual pairs* $(U(p,q), U(r,s))$, Canad. J. Math. 51 (1999) 636-657, Theorem 2.7, as the source cites it).

The source does not prove Howe duality, and it does not prove irreducibility of any theta lift. It proves the four facts above directly, from the explicit operators of the Fock model. The docstring of the last theorem of this chapter says that it "is used in place of Howe's duality theorem for real unitary pairs" and that it "is proved by Howe's argument ... instead of through irreducibility". The source does prove one multiplicity one statement: the space of joint harmonics of a pair of matching parameters has dimension one. Its docstring calls this "the case of the multiplicity one part of Howe's (GL, GL)-duality that is used".

### The four results

Let $T$ be the data of a dual pair in the Fock model (Section 2), with rows indexed by a finite set $R$ of signs $\varepsilon$ and columns indexed by a finite set $C$ of signs $\varepsilon'$. Let $l = 2\lambda$ and $l' = 2\lambda'$ be integer vectors that match for $T$ (Section 3). Let $\pi$, $\pi'$ be an oscillator pair for $T$: two commuting representations on one Fock space, whose derivatives on polynomials are the row action and the column action. Let $e_\lambda$ be the discrete series kernel of [discrete series through one matrix coefficient](/chapter/discrete-series/) and $\pi(e_\lambda) = \int e_\lambda(g)\pi(g)\,dg$.

The first result is existence: there is a joint harmonic $\Phi$, a polynomial that is highest of the lowest $K$-type for both actions and harmonic in both directions ([Theorem](/decl/New.IsMatch.exists_isJointHarmonic/)). The second result is uniqueness: two such polynomials are proportional ([Theorem](/decl/New.IsMatch.unique/)). The third result is positivity and the fixed vector: $\operatorname{Re}\langle \Phi, \pi(e_\lambda)\Phi\rangle > 0$, and $\pi'(f)\pi(e_\lambda)\Phi = \pi(e_\lambda)\Phi$ for every $f$ of suitable decay that reproduces $e_{\lambda'}$ ([Theorem](/decl/New.OscillatorPair.re_inner_integratedRep_pos/), [Theorem](/decl/New.OscillatorPair.integratedRep_integratedRep_eq_self/)). The fourth result is the smoothing statement: for each polynomial $P$ there is a bump function $\alpha$ on the second group with $\pi(e_\lambda)P = \pi'(g \mapsto \alpha(g^{-1}))\pi(e_\lambda)\Phi$ ([Theorem](/decl/New.OscillatorPair.exists_bump_integratedRep_eq/)).

The proof of the fourth result rests on an algebraic theorem, Howe's argument ([Theorem](/decl/New.IsJointHarmonic.howe_argument/)). A space of polynomials that is stable under the column action, contains $\Phi$, and contains three kinds of images of the row operators is the space of all polynomials. The proof is an induction on the degree with the Fischer inner product. The uniqueness of the joint harmonic is the step that closes the induction.

### Plan of the chapter

Section 2 defines the dual pair data in the Fock model: the raising and lowering operators, the row action and the column action, the swap, the vacuum weight and the standard data. Section 3 defines matched pairs, matching parameters and joint harmonics, and proves that matching is the block rule. Section 4 builds the joint harmonic as a product of minors along layers. Section 5 proves its uniqueness by polarisation and by evaluation at the 0-1 matrix of the matching. Section 6 compares the Casimir operators of the two groups. Section 7 proves Howe's argument. Section 8 passes to the representations: it defines oscillator pairs and proves positivity, the fixed vector and the smoothing statement. Section 9 has exercises and notes.

The first seven sections are pure algebra on polynomial rings. They use no analysis. Only Section 8 uses the representations, the kernel $e_\lambda$ and integrals over the groups.

### What the chapter uses

From [the Weil representation from a vacuum](/chapter/weil-representation/) the chapter uses the Fock space, the map $P \mapsto v_P$ from polynomials to Fock vectors, and the construction of the oscillator pair from the real Weil representation. From [discrete series through one matrix coefficient](/chapter/discrete-series/) it uses the parameters $l = 2\lambda$, the gap condition, the lowest $K$-type $\Lambda = \lambda + \rho - 2\rho_c$, the kernel $e_\lambda$, and two theorems: the positivity of $\operatorname{Re}\langle x, \pi(e_\lambda)x\rangle$ for a highest vector $x$ of weight $\Lambda$, and the fixed vector theorem for $\pi(f)$. The place of this chapter in the proof of the main theorem is in [the theorem and the plan of the proof](/chapter/theorem-and-plan/).

### Conventions

All parameters are doubled, so that they are integers. A parameter is an integer vector $l = 2\lambda$ indexed by a finite set with signs; in Lean it is `New.HCParam ε`, which is the type of functions `n → ℤ` for the signs `ε : n → ℤˣ`. The group $U(\varepsilon)$ is the unitary group of the hermitian form $\operatorname{diag}(\varepsilon)$, so $U(\varepsilon) = U(p,q)$ when $\varepsilon$ has $p$ entries $1$ and $q$ entries $-1$. The matrix unit $E_{ab}$ of $\mathfrak{gl}_n$ acts on a module $\rho$ by the operator $\rho(E_{ab})$, which Lean writes `ρ.E a b`.

The source writes "highest" for the order of $l$. A vector $x$ is *compact primitive* for $l$ if $E_{ab}x = 0$ whenever $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$. It is *$K$-highest of weight $\nu$* if also $E_{aa}x = \nu_a x$ for every $a$. The vector $0$ is $K$-highest of every weight. This is `New.HCParam.IsKHighest` in [RepresentationsAndCasimirs.lean](lean:Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean#L112). The chapter keeps the source's names: "row action" for the first group and "column action" for the second group.

The source claims these results. Lean accepts them, if the reported checks hold. This chapter does not claim that the proof of the main theorem is correct.
