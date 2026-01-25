import Mathlib

universe u v

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

variable {R : Type u} [CommRing R]

/-- Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third. -/
theorem isStablyFree_two_of_three_of_shortExact (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂] [Module.Projective R P₂]
    [AddCommGroup P₃] [Module R P₃] [Module.Finite R P₃] [Module.Projective R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
      (IsStablyFree R P₁ → IsStablyFree R P₂ → IsStablyFree R P₃) ∧
        (IsStablyFree R P₁ → IsStablyFree R P₃ → IsStablyFree R P₂) ∧
          (IsStablyFree R P₂ → IsStablyFree R P₃ → IsStablyFree R P₁) := by
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.2 hg)
  set eSigma := h.splitSurjectiveEquiv hf ⟨l, hl⟩ with heSigma
  set e : P₂ ≃ₗ[R] P₁ × P₃ := eSigma.1 with he
  refine ⟨?_, ?_⟩
  · intro hP₁ hP₂
    rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
    rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
    refine ⟨(P₁ × N₁) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    -- Rewrite `P₃ × ((P₁ × N₁) × N₂)` as `((P₂ × N₂) × N₁)` using the splitting `P₂ ≃ P₁ × P₃`.
    let eP₃ : (P₃ × ((P₁ × N₁) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₁) :=
      (LinearEquiv.prodAssoc R P₃ (P₁ × N₁) N₂).symm ≪≫ₗ
        (LinearEquiv.prodAssoc R P₃ P₁ N₁).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
          ((LinearEquiv.prodComm R P₃ P₁).prodCongr (LinearEquiv.refl R N₁)).prodCongr
              (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₁ N₂ ≪≫ₗ
              (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₁ N₂) ≪≫ₗ
                (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₁).symm ≪≫ₗ
                  (((e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₁)))
    exact Module.Free.of_equiv eP₃.symm
  · refine ⟨?_, ?_⟩
    · intro hP₁ hP₃
      rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨N₁ × N₃, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₂ : (P₂ × (N₁ × N₃)) ≃ₗ[R] ((P₁ × N₁) × (P₃ × N₃)) :=
        e.prodCongr (LinearEquiv.refl R (N₁ × N₃)) ≪≫ₗ LinearEquiv.prodProdProdComm R P₁ P₃ N₁ N₃
      exact Module.Free.of_equiv eP₂.symm
    · intro hP₂ hP₃
      rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨(P₃ × N₃) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₁ : (P₁ × ((P₃ × N₃) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₃) :=
        (LinearEquiv.prodAssoc R P₁ (P₃ × N₃) N₂).symm ≪≫ₗ
          (LinearEquiv.prodAssoc R P₁ P₃ N₃).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
            ((LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.refl R N₃)).prodCongr
                (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₃ N₂ ≪≫ₗ
                (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₃ N₂) ≪≫ₗ
                  (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₃).symm ≪≫ₗ
                    (e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₃)
      exact Module.Free.of_equiv eP₁.symm

open Polynomial Module

/-- `HasFiniteFreeResolutionLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionLength (R : Type u) [CommRing R] :
    ∀ (P : Type v), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P] :
      HasFiniteFreeResolutionLength R P 0
  | succ (P : Type v) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      (f : F →ₗ[R] P) (hf : Function.Surjective f)
      (hker : HasFiniteFreeResolutionLength R (LinearMap.ker f) n) :
      HasFiniteFreeResolutionLength R P (n + 1)

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) (P : Type v)
    [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ n : ℕ, HasFiniteFreeResolutionLength R P n

/-- A finitely generated free module has a finite free resolution (of length `0`). -/
theorem hasFiniteFreeResolution_of_finite_of_free (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P] : HasFiniteFreeResolution R P :=
  ⟨0, HasFiniteFreeResolutionLength.zero P⟩

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    HasFiniteFreeResolution R P₁ → HasFiniteFreeResolution R P₃ → HasFiniteFreeResolution R P₂ :=
  sorry

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    HasFiniteFreeResolution R P₁ → HasFiniteFreeResolution R P₂ → HasFiniteFreeResolution R P₃ :=
  sorry

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    HasFiniteFreeResolution R P₂ → HasFiniteFreeResolution R P₃ → HasFiniteFreeResolution R P₁ :=
  sorry

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type v), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] :
    HasFiniteFreeResolution (Polynomial R) P :=
  sorry

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
	shows that $P_0$ has a finite free resolution; and further applied to the exact sequence
	$$0 \to \mathfrak{p}R[x] \to P \to P_0 \to 0$$
	shows that $P$ has a finite free resolution, thereby concluding the proof.
\end{proof}

-/
