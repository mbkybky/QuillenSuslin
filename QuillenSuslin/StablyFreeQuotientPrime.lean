import QuillenSuslin.StablyFree

universe u v w

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal

theorem hasFiniteFreeResolution_quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) := by
  sorry

/-- Reduce the prime-quotient case to the corresponding prime ideal as an `R[X]`-module. -/
theorem hasFiniteFreeResolution_primeIdeal [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Ideal (R[X])) (hP : P.IsPrime) : HasFiniteFreeResolution (R[X]) P := by
  classical
  let p : PrimeSpectrum (R[X]) := ⟨P, hP⟩
  have hquot : HasFiniteFreeResolution (R[X]) (R[X] ⧸ P) :=
    hasFiniteFreeResolution_quotient_prime (R := R) hR p
  have hA : HasFiniteFreeResolution (R[X]) (R[X]) :=
    hasFiniteFreeResolution_of_finite_of_free (R := (R[X])) (R[X])
  -- Use `0 → P → R[X] → R[X]/P → 0`.
  refine hasFiniteFreeResolution_of_shortExact_of_middle_of_right (R := (R[X])) P (R[X]) (R[X] ⧸ P)
    (f := P.subtype) (g := P.mkQ) (hf := Subtype.coe_injective)
    (hg := Submodule.mkQ_surjective P)
    (h := by simpa using (LinearMap.exact_subtype_mkQ P))
    hA hquot

/-
\begin{definition}
	A finitely generated module $P$ over a commutative ring $R$ is said to be stably free if there exists a finitely generated free module $F$ such that the direct sum $P \oplus F$ is a free module.
\end{definition}

\begin{lemma}\label{exact_seq}
	Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third.
\end{lemma}

\begin{proposition}
	Let $R$ be a commutative Noetherian ring. Let $x$ be a variable. If every finite $R$-module has a finite free resolution, then every finite $R[x]$-module has a finite free resolution.
\end{proposition}

\begin{proof}
	Let $M$ be a finite $R[x]$-module. $M$ has a finite filtration
	$$M = M_0 \supset M_1 \supset \dots \supset M_n = 0$$
	such that each factor $M_i/M_{i+1}$ is isomorphic to $R[x]/P_i$ for some prime $P_i$. In light of Lemma \ref{exact_seq}, it suffices to prove the theorem in case $M = R[x]/P$ where $P$ is prime, which we now assume. In light of the exact sequence
	$$0 \to P \to R[x] \to R[x]/P \to 0$$
	and Lemma \ref{exact_seq}, we note that $M$ has a finite free resolution if and only if $P$ does.

	Let $\mathfrak{p} = P \cap R$. Then $\mathfrak{p}$ is prime in $R$. Suppose there is some $M = R[x]/P$ which does not admit a finite free resolution. Among all such $M$ we select one for which the intersection $\mathfrak{p}$ is maximal in the family of prime ideals obtained as above. This is possible in light of one of the basic properties characterizing Noetherian rings.

	Let $R_0 = R/\mathfrak{p}$ so $R_0$ is entire. Let $P_0 = P/\mathfrak{p}R[x]$. Then we may view $M$ as an $R_0[x]$-module, equal to $R_0/P_0$. Let $f_1, \dots, f_n$ be a finite set of generators for $P_0$, and let $f$ be a polynomial of minimal degree in $P_0$. Let $K_0$ be the quotient field of $R_0$. By the euclidean algorithm, we can write
	$$f_i = q_i f + r_i \quad \text{for } i = 1, \dots, n$$
	with $q_i, r_i \in K_0[x]$ and $\deg r_i < \deg f$. Let $d_0$ be a common denominator for the coefficients of all $q_i, r_i$. Then $d_0 \neq 0$ and
	$$d_0 f_i = q'_i f + r'_i$$
	where $q'_i = d_0 q_i$ and $r'_i = d_0 r_i$ lie in $R_0[x]$. Since $\deg f$ is minimal in $P_0$ it follows that $r'_i = 0$ for all $i$, so
	$$d_0 P_0 \subset R_0[x]f = (f).$$

	Let $N_0 = P_0/(f)$, so $N_0$ is a module over $R_0[x]$, and we can also view $N_0$ as a module over $R[x]$. When so viewed, we denote $N_0$ by $N$. Let $d \in R$ be any element reducing to $d_0 \pmod{\mathfrak{p}}$. Then $d \notin \mathfrak{p}$ since $d_0 \neq 0$. The module $N_0$ has a finite filtration such that each factor module of the filtration is isomorphic to some $R_0[x]/\bar{Q}_0$ where $\bar{Q}_0$ is an associated prime of $N_0$. Let $Q$ be the inverse image of $\bar{Q}_0$ in $R[x]$. These prime ideals $Q$ are precisely the associated primes of $N$ in $R[x]$. Since $d_0$ kills $N_0$ it follows that $d$ kills $N$ and therefore $d$ lies in every associated prime of $N$. By the maximality property in the selection of $P$, it follows that every one of the factor modules in the filtration of $N$ has a finite free resolution, and by Lemma \ref{exact_seq} it follows that $N$ itself has a finite free resolution.

	Now we view $R_0[x]$ as an $R[x]$-module, via the canonical homomorphism
	$$R[x] \to R_0[x] = R[x]/\mathfrak{p}R[x].$$
	By assumption, $\mathfrak{p}$ has a finite free resolution as $R$-module, say
	$$0 \to E_n \to \dots \to E_0 \to \mathfrak{p} \to 0.$$
	Then we may simply form the modules $E_i[x]$ in the obvious sense to obtain a finite free resolution of $\mathfrak{p}[x] = \mathfrak{p}R[x]$. From the exact sequence
	$$0 \to \mathfrak{p}R[x] \to R[x] \to R_0[x] \to 0$$
	we conclude that $R_0[x]$ has a finite free resolution as $R[x]$-module.

	Since $R_0$ is entire, it follows that the principal ideal $(f)$ in $R_0[x]$ is $R[x]$-isomorphic to $R_0[x]$, and therefore has a finite free resolution as $R[x]$-module. Lemma \ref{exact_seq} applied to the exact sequence of $R[x]$-modules
	$$0 \to (f) \to P_0 \to N \to 0$$
	shows that $P_0$ has a finite free resolution, and further applied to the exact sequence
	$$0 \to \mathfrak{p}R[x] \to P \to P_0 \to 0$$
	shows that $P$ has a finite free resolution, thereby concluding the proof.
\end{proof}

-/
