import QuillenSuslin.FiniteFreeResolution

universe u v w

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

variable {R : Type u} [CommRing R]

open Polynomial Module

theorem stably_free_iff (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : IsStablyFree R M ↔ HasFiniteFreeResolution R M := by
  classical
  have moduleFinite_of_hasFiniteFreeResolutionLength :
      ∀ {P : Type u} [AddCommGroup P] [Module R P] {n : ℕ},
        HasFiniteFreeResolutionLength R P n → Module.Finite R P := by
    intro P _ _ n hn
    induction hn with
    | zero P => infer_instance
    | succ P n F f hf hker ih => exact Module.Finite.of_surjective f hf
  have isStablyFree_of_projective_of_hasFiniteFreeResolutionLength :
      ∀ {P : Type u} [AddCommGroup P] [Module R P] {n : ℕ},
        HasFiniteFreeResolutionLength R P n → (Module.Projective R P → IsStablyFree R P) := by
    intro P _ _ n hn
    induction hn with
    | zero P =>
        intro _
        refine ⟨(Fin 0 → R), inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
        infer_instance
    | succ P n F f hf hker ih =>
        intro hPproj
        have hf' : f.range = ⊤ := LinearMap.range_eq_top.2 hf
        obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective f hf'
        have hexact : Function.Exact (LinearMap.ker f).subtype f :=
          LinearMap.exact_subtype_ker_map f
        set eSigma := hexact.splitSurjectiveEquiv Subtype.coe_injective ⟨l, hl⟩ with heSigma
        set e : F ≃ₗ[R] LinearMap.ker f × P := eSigma.1 with he
        haveI : Module.Projective R (LinearMap.ker f × P) := Module.Projective.of_equiv e
        haveI : Module.Projective R (LinearMap.ker f) :=
          Module.Projective.of_split (i := LinearMap.inl R (LinearMap.ker f) P)
            (s := LinearMap.fst R (LinearMap.ker f) P) (by ext x <;> simp)
        have hK : IsStablyFree R (LinearMap.ker f) := ih inferInstance
        rcases hK with ⟨N, _, _, hNfin, hNfree, hKNfree⟩
        haveI : Module.Finite R (LinearMap.ker f) :=
          moduleFinite_of_hasFiniteFreeResolutionLength hker
        haveI : Module.Finite R (LinearMap.ker f × N) := inferInstance
        haveI : Module.Free R (LinearMap.ker f × N) := hKNfree
        refine ⟨(LinearMap.ker f × N), inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
        haveI : Module.Free R F := inferInstance
        haveI : Module.Free R (LinearMap.ker f × P) := Module.Free.of_equiv e
        haveI : Module.Free R N := hNfree
        have : Module.Free R (((LinearMap.ker f × P) × N)) := by infer_instance
        -- Rearrange `(ker f × P) × N` as `P × (ker f × N)`.
        let e' : ((LinearMap.ker f × P) × N) ≃ₗ[R] (P × (LinearMap.ker f × N)) :=
          (LinearEquiv.prodComm R (LinearMap.ker f) P).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
            LinearEquiv.prodAssoc R P (LinearMap.ker f) N
        exact Module.Free.of_equiv e'
  constructor
  · intro h
    rcases h with ⟨N, _, _, hNfin, hNfree, hMNfree⟩
    haveI : Module.Finite R N := hNfin
    haveI : Module.Free R N := hNfree
    haveI : Module.Free R (M × N) := hMNfree
    haveI : Module.Finite R (M × N) := inferInstance
    have h₁ : HasFiniteFreeResolution R N := hasFiniteFreeResolution_of_finite_of_free (R := R) N
    have h₂ : HasFiniteFreeResolution R (M × N) :=
      hasFiniteFreeResolution_of_finite_of_free (R := R) (M × N)
    have hf : Function.Injective (LinearMap.inr R M N) := by
      intro x y hxy
      simpa using congrArg Prod.snd hxy
    have hg : Function.Surjective (LinearMap.fst R M N) := by
      intro x
      exact ⟨(x, 0), rfl⟩
    have hexact : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) :=
      (LinearMap.exact_iff).2 (by simpa using (LinearMap.ker_fst (R := R) (M := M) (M₂ := N)))
    exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle N (M × N) M hf hg hexact h₁ h₂
  · intro h
    rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
    have hf' : f.range = ⊤ := LinearMap.range_eq_top.2 hf
    obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective f hf'
    have hexact : Function.Exact (LinearMap.ker f).subtype f :=
      LinearMap.exact_subtype_ker_map f
    set eSigma := hexact.splitSurjectiveEquiv Subtype.coe_injective ⟨l, hl⟩ with heSigma
    set e : F ≃ₗ[R] LinearMap.ker f × M := eSigma.1 with he
    haveI : Module.Projective R (LinearMap.ker f × M) := Module.Projective.of_equiv e
    haveI : Module.Projective R (LinearMap.ker f) :=
      Module.Projective.of_split (i := LinearMap.inl R (LinearMap.ker f) M)
        (s := LinearMap.fst R (LinearMap.ker f) M) (by ext x <;> simp)
    have hK : IsStablyFree R (LinearMap.ker f) :=
      isStablyFree_of_projective_of_hasFiniteFreeResolutionLength hn inferInstance
    rcases hK with ⟨N, _, _, hNfin, hNfree, hKNfree⟩
    haveI : Module.Finite R (LinearMap.ker f) := moduleFinite_of_hasFiniteFreeResolutionLength hn
    haveI : Module.Finite R N := hNfin
    haveI : Module.Free R N := hNfree
    haveI : Module.Free R (LinearMap.ker f × N) := hKNfree
    haveI : Module.Finite R (LinearMap.ker f × N) := inferInstance
    refine ⟨(LinearMap.ker f × N), inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    haveI : Module.Free R F := inferInstance
    haveI : Module.Free R (LinearMap.ker f × M) := Module.Free.of_equiv e
    have : Module.Free R ((LinearMap.ker f × M) × N) := by infer_instance
    let e' : ((LinearMap.ker f × M) × N) ≃ₗ[R] (M × (LinearMap.ker f × N)) :=
      (LinearEquiv.prodComm R (LinearMap.ker f) M).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
        LinearEquiv.prodAssoc R M (LinearMap.ker f) N
    exact Module.Free.of_equiv e'

-- 转化为有限自由分解存在性的问题
theorem polynomial_isStablyFree [IsNoetherianRing R]
    (hR : ∀ (P : Type u) [AddCommGroup P] [Module R P],
        Module.Finite R P → Module.Projective R P → IsStablyFree R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P]
    [Module.Projective R[X] P] : IsStablyFree R[X] P := by
  sorry

theorem isStablyFree_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] :
    IsStablyFree R P := by
  -- 先证引理 1 : R 上的投射模都是自由的，引理 2 : 自由模 stably free
  sorry

-- use `polynomial_isStablyFree` to induction
theorem cor3_aux [IsDomain R] [IsPrincipalIdealRing R] (s : Type) [Finite s]
    (P : Type u) [AddCommGroup P] [Module (MvPolynomial s R) P] [Module.Finite (MvPolynomial s R) P]
    [Module.Projective (MvPolynomial s R) P] : IsStablyFree (MvPolynomial s R) P := by
  sorry

-- use `cor3_aux` and the fact that these propoties are invariant under isomorphism
theorem cor3 [IsDomain R] [IsPrincipalIdealRing R] (s : Type*) [Finite s]
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial s R) P] [Module.Finite (MvPolynomial s R) P]
    [Module.Projective (MvPolynomial s R) P] : IsStablyFree (MvPolynomial s R) P := by
  sorry

/-
\begin{definition}
	A finitely generated module $P$ over a commutative ring $R$ is said to be stably free if there
	exists a finitely generated free module $F$ such that the direct sum $P \oplus F$ is a free
	module.
\end{definition}

\begin{proposition}\label{stably_free_iff}
	Let $M$ be a projective module. Then $M$ is stably free if and only if $M$ admits a finite free resolution.
\end{proposition}

\begin{proof}
	If $M$ is stably free then it is trivial that $M$ has a finite free resolution. Conversely assume the existence of the resolution with the above notation. We prove that $M$ is stably free by induction on $n$. The assertion is obvious if $n = 0$. Assume $n \geqq 1$. Insert the kernels and cokernels at each step, in the manner of dimension shifting. Say
$$
M_1 = \text{Ker}(E_0 \to P),
$$
giving rise to the exact sequence
$$
0 \to M_1 \to E_0 \to M \to 0.
$$
Since $M$ is projective, this sequence splits, and $E_0 \cong M \oplus M_1$. But $M_1$ has a finite free resolution of length smaller than the resolution of $M$, so there exists a finite free module $F$ such that $M_1 \oplus F$ is free. Since $E_0 \oplus F$ is also free, this concludes the proof of the theorem.
\end{proof}

\begin{proposition}
	Let $R$ be a commutative Noetherian ring. Let $x$ be a variable. If every finite $R$-module has a finite free resolution, then every finite $R[x]$-module has a finite free resolution.
\end{proposition}

\begin{theorem}\label{poly}
	Let $R$ be a noetherian ring such that every finitely generated projective module over $R$ is stably free. Then the same property holds true for $R[x]$.
\end{theorem}

By induction, we see:

\begin{corollary}\label{cor:3}
	Every finitely generated projective module over $k[x_1, \dots, x_n]$, for any field $k$, is necessarily stably free.
\end{corollary}

-/
