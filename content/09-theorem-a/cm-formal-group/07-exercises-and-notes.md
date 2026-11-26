---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of the chapter. Exercises 1, 2 and 6 use only Section 5. Exercises 4 and 5 use the model $d = 23$, $q_1 = 12$ of Section 6.

**Exercise 1.** Let $p$ be nonsplit, and let $|\varpi| = p^{-\rho}$ for a real number $\rho$. Show that $v(c_\varpi\pi_p) \ge 1/(p-1)$ if and only if $\rho \ge \rho_p$. Deduce that $\rho_p$ is the smallest exponent for which the proposition on the exponent modulo $\pi$ of Section 5 applies with $\pi = \pi_p$. Do the same computation for a split prime with $\pi = p$, and compare the result with $\rho_p = 1/(p-1)$ of Volume 3.

*Hint.* $v(c_\varpi\pi_p) = (p+1)\rho - 1 + v(\pi_p)$. This is increasing in $\rho$. Insert $v(\pi_p) = 1$ or $1/2$ and solve for $\rho$. For a split prime, the bound is $\rho \ge 1/(p^2 - 1)$. It is smaller than $\rho_p = 1/(p-1)$, so at a split prime the scale of Volume 3 satisfies the condition with room to spare.

**Exercise 2.** Let $p = 3$ and $S$ the set of odd numbers. List all pairs $(e, j)$ with $e \in S$ and $(3^e + 1)3^j \le 120$, together with the degree of $\Gamma_e^{3^j}$. Do the same for $p = 7$ and $S = \mathbb{N}$, with the bound $120$. In each case, give the set of $e$ for which the theorem on integrality from the normal form needs $\pi \mid \Gamma_e(Z)$ when $B = 120$.

*Hint.* For $p = 3$ the degrees are $4, 12, 36, 108$ for $e = 1$ and $28, 84$ for $e = 3$. The next exponent $e = 5$ gives $244$. For $p = 7$ the degrees are $2, 14, 98$ for $e = 0$ and $8, 56$ for $e = 1$, and $e = 2$ gives $50$. The theorem uses $e \le \lfloor\log_p 120\rfloor$, which is $4$ for $p = 3$ and $2$ for $p = 7$. Note that the theorem asks for $e = 2$ at $p = 7$, since $\Gamma_2$ has degree $50 \le 120$.

**Exercise 3.** Let $p$ be inert, $e$ even and $\tau \in \Phi$. Show that the partner congruence of Section 6 fails for $\alpha = \sqrt{-d}$. That is, show $|\iota_p(\tau(\sqrt{-d}))^{p^e} - \iota_p(\overline{\tau'_e(\sqrt{-d})})| = 1$.

*Hint.* Every embedding of the CM type sends $\sqrt{-d}$ to the same square root $\delta$ of $-d$ in $\mathbb{C}$. Modulo $p$, $\delta^{p^e} \equiv \chi_K(p)^e\delta = \delta$, and the second term is $\bar\delta = -\delta$. So the difference is $\equiv 2\delta$, and $2d$ is prime to $p$.

**Exercise 4.** In the model, let $p = 23$. Find the partner rule for every $e$. Show that $\Gamma_e = \sum_x z_x^{23^e + 1}$ for every odd $e$, and that $\Gamma_e = \sum_{(\tau, c)}z_{(\tau, c)}^{23^e}z_{(-\tau, c)}$ for every even $e$, where $-\tau$ is the place $u(-1)\tau$.

*Hint.* $23 \equiv -1$ modulo $12$, so $-23^e \equiv -(-1)^e$. The places are the classes $1, 5, 7, 11$ modulo $12$.

**Exercise 5.** Let $(u_j, m_j)$ be a resolution of the identity in $E^n$. Let $\gamma \in E$ with $|\tau(\gamma)| = 1$ for every place $\tau$, for example a root of unity. Show that $(\gamma u_j, m_j)$ is a resolution of the identity. If the $u_j$ are integral above $p$ and $\gamma$ is a unit of $\mathcal{O}_E$, show that the $\gamma u_j$ are integral above $p$. Show that the dagger forms change by the factors $\overline{\tau(\gamma)}$ in the coordinate $z_{(\tau, c)}$, and check directly that the coupling congruence of Section 6 still holds.

*Hint.* For $x = (\tau, c)$ and $x_1 = (\tau_1, c_1)$ the new sum is $\tau(\gamma)\overline{\tau_1(\gamma)}$ times the old sum. The old sum is $0$ for $x \ne x_1$, and for $x = x_1$ the factor is $|\tau(\gamma)|^2 = 1$. For the coupling, use part 2 of the partner congruence for $\beta = \gamma$.

**Exercise 6.** Let $\pi \mid p$ in $\mathfrak{o}$, let $L_j$ be integral series and $m_j \in \mathbb{N}$. Prove
$$\sum_j m_j\,L_j^{\,p} \equiv \Bigl(\sum_j m_jL_j\Bigr)^p \pmod{\pi}$$
in two ways: first by Fermat's little theorem for the $m_j$, and second by writing the sum with multiplicities as a sum over the pairs $(j, k)$ with $k < m_j$, as the source does in the lemma on exponents adds.

*Hint.* For any integral $a$ and $b$, $(a + b)^p - a^p - b^p$ is divisible by $p$, since the binomial coefficients $\binom{p}{i}$ with $0 < i < p$ are. For the first way, use $m_j^p \equiv m_j$ modulo $p$.

**Exercise 7.** In the proof of the supersingular coefficient (Section 3), the recursion is used for $n + 2 \le m$ with $p = 2m + 1$. For $p = 11$ write the recursion relations at $n = 0, 1, 2, 3$ modulo $\mathfrak{m}$ and show directly that $h_1 \equiv 0$ forces $h_5 \equiv 0$. Explain why this contradicts $h_5 = 1$.

*Hint.* The factors $4n + 6$ are $6, 10, 14, 18$, and none is divisible by $11$. Each relation gives $h_{n+2}$ in terms of $h_{n+1}$ and $h_n$. With $h_0 = 0$ and $h_1 \equiv 0$, induction gives $h_n \equiv 0$ for $n \le 5$.

## Notes and references

The integrality of the scaled theta function in Section 4 rests on the formal group of the CM curve at a nonsplit prime. Formal groups with complex multiplication by the integers of a local field are due to Lubin and Tate [J. Lubin and J. Tate, "Formal complex multiplication in local fields", Ann. of Math. 81 (1965) 380 to 387]. The source does not use the theory of Lubin and Tate. It works directly with the series $x$, $y$ and $\theta$ and with the integrality of the ring $\mathfrak{o}[[y]]$ of Volume 3.

For formal groups of elliptic curves and the formal logarithm see [J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer GTM 106, 2009, Chapter IV]. For the reduction of curves with complex multiplication, the criterion of Deuring says that a CM curve with good reduction at a prime above $p$ has supersingular reduction there if and only if $p$ does not split in the field of complex multiplication. Section 3 proves the one fact that the argument needs, the unit coefficient of $z^{p-1}$ in $x$ at inert $p$, without reduction of the curve. For the $p$-adic exponential and the bound $v(j!) \le j/(p-1)$ see [N. Koblitz, p-adic Numbers, p-adic Analysis, and Zeta-Functions, 2nd ed., Springer GTM 58, 1984, Chapter IV].

The source names earlier bounds for one curve at inert primes and says that they are not used: Bannai and Kobayashi, "Algebraic theta functions and the p-adic interpolation of Eisenstein-Kronecker numbers" (first arXiv version, Theorem 4.1); Bannai and Kobayashi, "Integral structures on p-adic Fourier theory"; Bannai, Kobayashi and Yasuda, "The radius of convergence of the p-adic sigma function"; and Fujiwara, "On divisibilities of special values of real analytic Eisenstein series". The handbook has not compared their statements with the theorem of Section 4.

The module docstring of the file on resolutions says that a resolution of the identity is a Parseval frame. In the language of frame theory, the vectors $\sqrt{m_j}\,u_j$ form a tight frame with frame bound $1$ for the complex space with the coordinates $(\tau, c)$. Tight frames of this kind appear in [the integral vacuum and tight frames](/chapter/integral-vacuum/).

The normal form of Section 5 and its use in Section 6 are specific to the source. The handbook found no statement of the same form in the literature. The partner rule $\tau \mapsto u(-p^e)\tau$ is the place form of the Frobenius at $p$ in $E$, composed with complex conjugation; see [the field E at the primes](/chapter/field-at-primes/). The local prime sum $s_p(y, \sigma)$ of [the three inputs](/chapter/theorem-a-plan/) compares a place with this partner, and the [next chapter](/chapter/normal-forms/) is where the couplings $\Gamma_e$ turn into the divisibility of jets.

This chapter does not prove that the argument of the source is correct. It states what the Lean files state, and it explains the proofs as the files give them.
