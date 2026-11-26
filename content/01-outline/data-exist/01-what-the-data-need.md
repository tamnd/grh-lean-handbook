---
title: What the data need
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the data need

This chapter proves that the data of the argument exist. The main inequality of the source holds for every term $D$ of the type of data, and it bounds the prime remainder $R_{q_0}(x)$ at the length $x$ of $D$ (see [the plan](/chapter/theorem-and-plan/) and [the main inequality](/chapter/main-inequality/)). To get a bound at every large integer $x$, one needs, for each such $x$, data whose length is $x$ and whose other scales have an explicit size. The existence theorem gives exactly this. It is the last input to the one-sided bound $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$.

### The demands

The fields of $D$ are listed in [the data and its sizes](/chapter/data-and-sizes/), and that chapter is the reference for each of them. Here is what a construction must supply. Fix parameters $P$: a multiple $q_0$ of $18480$ and a prime $d$ with $d \equiv q_0/2 - 1 \pmod{q_0}$ (see [fields, places and twists](/chapter/fields-places-twists/)). Put $K = \mathbb{Q}(\sqrt{-d})$. For an exponent $s \geq 1$ put $l_0 = 3^{\lfloor \log_3 s \rfloor + 4}$, the least power of $3$ above $27s$, and
$$\operatorname{towerDeg}(s) = 3 l_0 2^s, \qquad q_1 = q_0 \operatorname{towerDeg}(s), \qquad q_2 = (q_0 d)^{s + 6}.$$
Let $E = K(\zeta_{q_1})$. Its infinite places $\Phi$ form a group isomorphic to $(\mathbb{Z}/q_1\mathbb{Z})^\times$. Data for $P$ consist of the following objects.

1. **Scales.** Integers $x$, $x_1$, $b$ with the five scale inequalities
$$10^{12} c_P \leq \log\log b, \quad (\log b)^{100} \leq x, \quad x^{10^6} \leq x_1, \quad x_1^{10^6} \leq b, \quad (\log x_1)^6 \leq \log b,$$
where $c_P$ is a constant that depends on $q_0$ and $d$ only, and with $q_1 x_1 \mid b$.
2. **Ranks.** A power of two $m = 2^{e+1}$ in $[\sqrt{x}, 2\sqrt{x}]$, the exponent $s = 22(e+1)$, so that $2^s = m^{22}$, with $s \leq 32 \log x$, and a power of three $r$ in $[x^5, 3x^5]$.
3. **Places.** A set $\Phi_b \subseteq \Phi$ of places whose classes are $\equiv -1 \pmod{q_0}$, with $\operatorname{towerDeg}(s) \leq \#\Phi_b \cdot \log b$, and which is sparse for the primes $\ell \leq kt$, where $k = r + 1 - m$ and $t = 5r$. The weight is $b$ on $\Phi_b$ and $\lfloor xb/x_1 \rfloor$ elsewhere.
4. **Primes.** Two distinct primes $p_0, p_1 \equiv 1 \pmod{q_2^2}$ in $[b^{10}, b^{11}]$, with an integer $\alpha$ of $K$ such that $\alpha\bar\alpha = p_0 p_1$. A prime $N \equiv 1 \pmod{q_2^2}$ with $\log N$ in an interval $[\log N_-, \log N_- + \sqrt{\log b}]$, where $\log N_-$ is an explicit number between $m \log b$ and $24 m \log b$, and an integer $\beta$ of $E$ with $\beta\bar\beta = N$.

The word *sparse* means this: for no prime $\ell \leq kt$ and no exponents $0 < i < j < l_0$ are there places $\sigma, \tau, \rho \in \Phi_b$ with $\tau/\sigma \equiv \pm \ell^i$ and $\rho/\sigma \equiv \pm \ell^j$ modulo the part of $q_1$ prime to $\ell$. Section 3 gives the exact form.

The demands are of three kinds. The scales and the ranks are sizes. They only need a careful choice of exponents. The set $\Phi_b$ is a combinatorial demand: it must be large, of density at least $1/\log b$ in a group of order $\operatorname{towerDeg}(s)$, and it must avoid a family of configurations of three points. Behrend's construction of sets without three-term progressions meets this demand. The primes are an arithmetic demand. Their modulus $q_2^2 = (q_0 d)^{2(s+6)}$ grows with $x$, since $s$ is about $11 \log_2 x$. So Dirichlet's theorem for a fixed modulus is not enough. One needs primes in progressions whose modulus is a power of $x$, with $\log p$ in a prescribed window. The source proves a theorem of this kind from a zero-free region.

### The recipe

Fix $\varepsilon$ with $0 < \varepsilon < 1/100$. Let $x$ be a large integer, and put $W = x^{\varepsilon/6}$. The recipe is:

- $x_1 = \lfloor e^{W} \rfloor$, so that $W - 1 \leq \log x_1 \leq W$;
- $b$ is the least multiple of $q_1 x_1$ with $b > e^{W^6}$, so that $x^{\varepsilon} = W^6 \leq \log b \leq W^6 + 1$;
- $m$ is the least power of $2$ with $m \geq \sqrt{x}$, and $r$ is the least power of $3$ with $r \geq x^5$;
- the places of $\Phi_b$ are $-g^{e}$, with $g = 1 + 3 l_0 q_0$ and $e$ in a set of Behrend type;
- $p_0$, $p_1$ and $N$ come from windows for primes in progressions; $\alpha$ comes from a pigeonhole argument in the class group of $K$, and $\beta$ from Fermat's theorem on sums of two squares.

The scales then satisfy
$$\log\log b \approx \varepsilon \log x \ll \log x \ll \log x_1 \approx x^{\varepsilon/6} \ll \log b \approx x^{\varepsilon}.$$

The exponents are forced by the scale inequalities. Here is the reason for each.

| demand | what it asks of $W$ | where it holds |
|---|---|---|
| $(\log b)^{100} \leq x$ | $100(6\log W + 1) \leq \log x$ | $\varepsilon < 1/100$ and $x$ large |
| $x^{10^6} \leq x_1$ | $10^6 \log x \leq W - 1$ | $W$ is a power of $x$ |
| $x_1^{10^6} \leq b$ | $10^6 W \leq W^6$ | $W \geq 10^2$ |
| $(\log x_1)^6 \leq \log b$ | $W^6 \leq \log b$ | the choice of $b$ |
| $10^{12} c_P \leq \log\log b$ | $10^{12} c_P \leq \log W$ | $x$ large |

The first row is the only place where the bound $\varepsilon < 1/100$ enters: $\log b$ is about $x^{\varepsilon}$, and its hundredth power must stay below $x$. The fourth row is the reason for the exponent $6$ in $W^6$. The upper bound $\log x_1 \leq W$ and the lower bound $\log b \geq W^6$ give $(\log x_1)^6 \leq \log b$ with no room to spare.

The end of the proof uses only four facts about the data at $x$: the length is $x$, $\log b \leq 2x^{\varepsilon}$, $m \geq \sqrt{x}$, and $\log x_1 \geq x^{\varepsilon/12}$. The second and third facts give the main term. The main inequality bounds $R_{q_0}(x)$ by $\varphi(q_0) (\log b)^6 / m$ and two terms at $x_1$, and $(2x^{\varepsilon})^6/\sqrt{x} = 64 x^{-1/2 + 6\varepsilon}$. The fourth fact makes the terms at $x_1$ small. The prime number theorem with an error $(\log x_1)^{-B}$ and $B \geq 24/\varepsilon$ gives $|R(x_1)| \leq x^{-2}$. These steps are in [the main inequality and the end of the proof](/chapter/main-inequality/).

### The plan

Section 2 proves Behrend's construction in the form that the source uses, with all details. It is the model for the rest of the chapter: a short and complete proof of an explicit construction. Section 3 turns the construction into the set $\Phi_b$ of places and proves that it is sparse and large. Section 4 states the theorem on primes in windows, compares it with the Siegel-Walfisz theorem, and gives the main steps of its proof. Section 5 assembles the recipe and proves the existence theorem. Section 6 has the exercises and the notes.

Lean accepts the existence theorem if the checks that the source reports hold. This book did not rerun the checks.
