---
title: The chapter and its place
lean:
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
  - New/UpperBound/ElementaryDivisors/TwistingData.lean
decls:
  - New.FrobeniusCycle.elementary_divisors
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter proves the theorem on elementary divisors. A Hecke operator $A$ acts on functions on a finite set of lattices, with values in a space of polynomial forms. Its matrix has entries in a valuation ring $O$ that contains a prime $p$. The theorem bounds how far $A$ is from onto modulo $p^m$. In the language of elementary divisors: outside a proportion $\theta$ of them, the elementary divisors of $A$ have mean $p$-adic exponent at most $3c_{\mathrm{div}}$, where $c_{\mathrm{div}}$ is an explicit number. The bound comes from forms that are integral at every edge into a lattice, and the hard part is to show that there are few of them, counted with their depth.

### Where the chapter sits

The plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/), and the plan of the book is in [the theorem and the plan](/chapter/theorem-and-plan/). Theorem A needs a lower bound for the divisibility of a composite lift by each prime of a finite set. At a split prime the composite lift is an eigenvector of a Hecke operator up to an error, and the divisibility follows if the Hecke operator, restricted to a lattice of integral forms, is nearly onto. The next chapter, [divisibility prime by prime](/chapter/divisibility/), applies the present theorem to the Hecke edges and the mark operator at each such prime. This chapter is pure local algebra: it uses no automorphic forms, and its only sizes are its own parameters $N$, $k$, $n$, $r$, $\theta$ and $q$. The sizes of the book enter only in the next chapter, through [the data and their sizes](/chapter/data-and-sizes/).

### What the chapter uses

The measure of "nearly onto" is a colength. For submodules $M$, $N$ of a module $V$ over a commutative ring and an element $z$, the colength of $N$ in $M$ divides $z$ if every finite family $\Phi_1, \dots, \Phi_n$ in $M$ has a square matrix $m$ with $\det m \mid z$ and all $\sum_k m_{ik}\Phi_k$ in $N$. An endomorphism $y$ is onto on $M$ modulo $p^n$ up to colength $c$ if $y(M) \subseteq M$ and the colength of $y(M) + p^n M$ in $M$ divides $p^l$ for some natural number $l \le c$. Both notions, and the rules for them (monotone, transitive, image under a map, bound by a determinant, comparison with lengths over a discrete valuation ring), are in [twisted lattices](/chapter/twisted-lattices/#colength). From earlier volumes the chapter uses:

- the symmetric powers of the standard representation of $\mathrm{GL}_k$ and their divided power lattices, from [Weyl modules](/chapter/weyl-modules/);
- the parahoric and Levi subgroups of $\mathrm{GL}_k(W)$ for a two block partition, and the count of cosets of a parahoric subgroup over a finite field, from [finite general linear groups](/chapter/finite-gln/);
- the Hermite form over a valuation ring, from [twisted lattices](/chapter/twisted-lattices/).

### The notation

Let $W$ be a local ring whose residue field $k_W$ has $q$ elements, and let $O$ be a valuation domain of characteristic zero. A Frobenius cycle (Section 2) is a prime $p$, a power $P = p^f$ with $P \ge 5$ and $q = P^N$, ring maps $\iota_s : W \to O$ for $s \in \mathbb Z/N$ (the letters), alternately even and odd, with $\iota_{s+1}(x) \equiv \iota_s(x)^P \pmod p$, and an element $w \in O$ with $w^2 = p$. The rank is $k$. A form of degree $n$ in each letter is a polynomial in the variables $x_{bs}$, $b < k$, $s \in \mathbb Z/N$, that is homogeneous of degree $n$ in the $k$ variables of each letter. Its exponents form the finite set $\mathrm{Exp} = \mathrm{Exp}(N,k,n)$ of families $\beta = (\beta_s)_s$ of exponent vectors of degree $n$. The group $\mathrm{GL}_k(W)$ acts on forms through $\iota_s(g)$ in even letters and $\iota_s((g^{-1})^{\mathsf T})$ in odd letters; $\rho(g)$ is its matrix on coefficient vectors. Fix $r$ with $0 < 2r \le k$. An edge is a pair of lattices $L' \subseteq L$ with $pL \subseteq L'$ and $\dim L/L' = r$; $L'$ is its origin. The two numbers that govern the theorem are

$$c_0 = k^2 f N, \qquad c_{\mathrm{div}} = Nn\Big(\frac{1}{P^{2r}} + \frac{r^2}{kP}\Big).$$

Here $c_0 = k^2\log_p q$ bounds the $p$-adic valuation of a multinomial coefficient of degree less than $q$ with at most $k^2$ parts, and $c_{\mathrm{div}}$ bounds the mean depth of the forms that are integral for all edges.

### The theorem

**Theorem (Elementary divisors).** Let $O$ be a valuation domain of characteristic zero and $T$ a Frobenius cycle with $N$ letters over $W$ and $O$, with $p$ not a unit of $O$. Let $X$ be a finite set (the lattices), let $H$ and $I$ be finite sets with a bijection $J : I \to \mathrm{Exp} \times H$, and let $\mathcal E$ be edge coordinates for $X$ (Section 7), with edge Hecke operator $A$ on $X \to O^I$. Let $f : (X \to O^I) \to M$ be $O$-linear and $Y$ an endomorphism of $M$ with $Y \circ f = f \circ A$. Assume $0 < r$, $2r \le k$, $0 < \theta \le 1$, $n^4 \le q$ and $(Nk\log q/\theta)^5 P^{3r} \le n$. Then for every $m \in \mathbb N$ the map $Y$ is onto on $L = f(X \to O^I)$ modulo $p^m$ up to colength

$$(3c_{\mathrm{div}} + \theta m)\,|X|\,|I|.$$

Lean: `New.FrobeniusCycle.elementary_divisors` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

The proof is in [Section 8](/chapter/elementary-divisors/#the-proof-of-the-theorem). Over a discrete valuation ring the conclusion reads: $Y(L) \subseteq L$, and the length of $L/(Y(L) + p^m L)$ is at most $l$ times the length of $O/p$ for some $l \le (3c_{\mathrm{div}} + \theta m)|X||I|$. Read with $m$ large, the bound says the following. Diagonalize $A$ on $L$ by elementary divisors $p^{e_1}, \dots, p^{e_D}$ with $D = |X||I|$. Then $\sum_j \min(e_j, m) \le (3c_{\mathrm{div}} + \theta m)D$. So at most $\theta D$ (plus the share of the term $3c_{\mathrm{div}}D/m$) of the $e_j$ reach $m$, and the others have mean at most $3c_{\mathrm{div}}$.

### A model case

Take $k = 2$, $r = 1$, $N = 2$, with letter $0$ even and letter $1$ odd, so $q = P^2$. A lattice $L$ has $q + 1$ edges from it, one for each line of $L/pL$. A form is a pair of binary forms of degree $n$, $h(x_{00}, x_{10})\,h'(x_{01}, x_{11})$ and sums of such. The deep variables for $r = 1$ are $x_{10}$ (in the even letter, index at least $r$) and $x_{01}$ (in the odd letter, index below $r$). The depth of a monomial is its degree in the deep variables. The halfway lattice of the edge $L' \subseteq L$ is spanned by $w^{-\mathrm{depth}(\beta)} z^\beta$ in an adapted basis $z$ of $L'$. A form that lies in the halfway lattices of all $q+1$ edges must, modulo $w$, have only monomials of large depth in every adapted basis. Read on the residue field, this says that a form vanishes to high order at the $q+1$ points of the projective line over $k_W$. A nonzero form of low degree cannot vanish to high order at so many points (Section 4), and $n^4 \le q$ makes the allowed order small. This is the source of the term $Nn/P^{2r}$ in $c_{\mathrm{div}}$. The term $Nnr^2/(kP)$ comes from the forms that are deep in a weaker sense, along one root at a time; those are counted by the defect and a cone of Pieri type.

### A sketch of the proofs

*Factor the operator.* On vectors multiplied by a pairing $b$, the operator $A$ is the composite $M \subseteq M_{\mathrm{all}} \subseteq M_{\mathrm{edge}} \to \mathcal N \subseteq M^\circ$ of four maps. Here $M$ is the integral functions on lattices, $M_{\mathrm{all}}$ the functions on edges that depend only on the origin, $M_{\mathrm{edge}}$ all functions on edges, and $\mathcal N$ the functions whose value at $L$ is dual to the forms in the halfway lattices of all edges from the dual of $L$. The map $\mathrm{Add}$ adds the values at the edges into $L$.

*Ends of small colength.* The two inclusions at the ends have colength dividing $p^{|X| c_{\mathrm{div}}|\mathrm{Exp}|}$ each. This is a Smith form argument with the count of deep forms (Sections 3 and 4).

*A near inverse.* The image of $\mathrm{Add}$ contains $p^{Nc_0}\mathcal N$, by a near inverse built from an average over a Schur algebra (Section 6). At each edge there are conditions modulo $w^c$, $c = 5Nc_0$, that the functions in $M_{\mathrm{all}}$ satisfy, and the near inverse has values that satisfy them.

*Few extra generators.* The conditions cut out a space of dimension at most $(1+\theta)|\mathrm{Exp}|$ per edge class, by the root lemma and the Pieri volume (Section 5). By Nakayama's lemma, $\mathrm{Add}(M_{\mathrm{all}})$ and at most $\theta|X||\mathrm{Exp}|$ more generators span a module that contains $p^{2Nc_0}\mathcal N$.

*Add up.* Colengths multiply along chains. The ends give $2c_{\mathrm{div}}$, the middle gives $2Nc_0 \le 2c_{\mathrm{div}}$ minus what the generators save, and each extra generator costs at most $m$. The total is $(3c_{\mathrm{div}} + \theta m)|X||I|$ (Section 8).

### The sections

Section 2 defines Frobenius cycles, the twisted action, depth, defect and the size conditions. Section 3 treats edges, halfway lattices, the pairing and the functions on origins. Section 4 counts deep forms. Section 5 proves the defect bounds: the root lemma and the Pieri volume. Section 6 builds the averaging map and the edge conditions. Section 7 defines the edge Hecke operator and its factorization. Section 8 proves the theorem. Section 9 has exercises and notes.
