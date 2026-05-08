/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import QuillenSuslin.StablyFree.Basic

/-!
This file proves that a finite stably free module `M` is free if it is locally free of rank `1`.
-/

public section

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- The map linear in the first argument and alternating in the remaining arguments that
underlies the cofactor expansion along the `M`-summand of `M × N`. -/
private noncomputable def cofactorLinear (bN : Module.Basis (Fin n) R N) :
    M × N →ₗ[R] (M × N) [⋀^Fin n]→ₗ[R] M where
  toFun x := (bN.det.compLinearMap (LinearMap.snd R M N)).smulRight x.1
  map_add' x y := AlternatingMap.ext fun _ ↦ by simp
  map_smul' c x := AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm]

/-- The linear map from the top exterior power of `M × N` to `M` induced by the cofactor
expansion along the `M`-summand. -/
private noncomputable def cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))

noncomputable def exteriorPower.alternatizeUncurryFin (f : M →ₗ[R] ⋀[R]^n M →ₗ[R] N) :
    ⋀[R]^(n + 1) M →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv <| AlternatingMap.alternatizeUncurryFin <|
    exteriorPower.alternatingMapLinearEquiv.symm.comp f

private lemma cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i))) = m := by
  simp [cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Module.Basis.det_self]

/-- Let `R` be a commutative ring, `M` be a finite stably free `R`-module.
  If `Mₘ ≃ Rₘ` for any maximal ideal `m` of `R`, then `M` is free. -/
theorem Module.free_of_isStablyFree_of_localized_eq_ring [Nontrivial R] [Module.Finite R M]
    [IsStablyFree R M] (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Free R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  have h1 : Module.rankAtStalk M ⟨𝔪, h𝔪.isPrime⟩ = 1 := by simpa using (hlo 𝔪).finrank_eq
  let n := Module.finrank R N
  have hp : Module.finrank R (M × N) = n + 1 := by
    simpa [← h1, n, Nat.add_comm] using congrArg (fun f ↦ f ⟨𝔪, h𝔪.isPrime⟩) <|
      Module.rankAtStalk_eq_finrank_of_free.symm.trans (Module.rankAtStalk_prod M N)
  let bN : Module.Basis (Fin n) R N := Module.finBasis R N
  let b : Module.Basis (Fin (n + 1)) R (M × N) := Module.finBasisOfFinrankEq R (M × N) hp
  let e : R ≃ₗ[R] (⋀[R]^(n + 1) (M × N)) := Classical.choice <|
    Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]
  let f : R →ₗ[R] M := cofactorToLeft bN ∘ₗ e
  have hfs : Function.Surjective f := fun x ↦
    ⟨e.symm (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))),
      by simp [f, cofactorToLeft_ιMulti_cons]⟩
  exact Module.Free.of_equiv <| LinearEquiv.ofBijective f <| bijective_of_localized_maximal f <| by
    intro m _
    have : Module.Invertible _ (LocalizedModule.AtPrime m M) := Module.Invertible.congr (hlo m).symm
    exact Invertible.bijective_of_surjective (LocalizedModule.map_surjective m.primeCompl f hfs)

theorem Module.Invertible.of_locally_free_of_rank_one [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M := by
  -- To show M is invertible, we need to show contractLeft R M is bijective
  refine Module.Invertible.mk ?_
  -- Since R is invertible, it suffices to show contractLeft R M is surjective
  have h_surj : Function.Surjective (contractLeft R M) := by
    -- Let I be the image of contractLeft (an ideal of R)
    let I : Ideal R := LinearMap.range (contractLeft R M)
    -- Suppose I ≠ R
    by_cases hI_top : I = ⊤
    · -- Then contractLeft is surjective
      intro r
      have : r ∈ I := by rw [hI_top]; trivial
      exact LinearMap.mem_range.mp this
    · -- I is proper, so contained in a maximal ideal
      obtain ⟨m, hm_max, hmI⟩ := Ideal.exists_le_maximal I hI_top
      let S := m.primeCompl
      let Rₘ := Localization S
      let Mₘ := LocalizedModule S M
      -- The isomorphism Mₘ ≃ Rₘ from the hypothesis
      let e : Mₘ ≃ₗ[Rₘ] Rₘ := hlo m
      -- e.symm 1 is an element of Mₘ
      let y : Mₘ := e.symm 1
      -- Represent y as a fraction x/s
      obtain ⟨⟨x, s⟩, hy⟩ := IsLocalizedModule.mk'_surjective S
        (LocalizedModule.mkLinearMap S M) y
      -- hy : mk' (LocalizedModule.mkLinearMap S M) x s = y
      -- i.e., LocalizedModule.mk x s = y
      have hy' : LocalizedModule.mk x s = y := by
        simpa [IsLocalizedModule.mk_eq_mk'] using hy
      -- Construct the dual isomorphism (with named components for later use)
      let e1 := Module.FinitePresentation.linearEquivMapExtendScalars S (M := M) (N := R)
      let e1ₘ : LocalizedModule S (M →ₗ[R] R) ≃ₗ[Rₘ] (Mₘ →ₗ[Rₘ] LocalizedModule S R) :=
        e1.extendScalarsOfIsLocalization S Rₘ
      let iso_R : LocalizedModule S R ≃ₗ[Rₘ] Rₘ :=
        (IsLocalizedModule.iso S (LocalizedModule.mkLinearMap S R)).extendScalarsOfIsLocalization S Rₘ
      let φ_dual : LocalizedModule S (Module.Dual R M) ≃ₗ[Rₘ] Module.Dual Rₘ Mₘ :=
        e1ₘ ≪≫ₗ LinearEquiv.arrowCongr (.refl Rₘ Mₘ) iso_R
      -- e is an Rₘ-linear map Mₘ → Rₘ, i.e., an element of Dual_{Rₘ} Mₘ
      let f_local : Module.Dual Rₘ Mₘ := e
      -- Via φ_dual.symm, we get an element of LocalizedModule S (Dual R M)
      let g : LocalizedModule S (Module.Dual R M) := φ_dual.symm f_local
      -- Write g as a fraction f/t
      obtain ⟨⟨f, t⟩, hg⟩ := IsLocalizedModule.mk'_surjective S
        (LocalizedModule.mkLinearMap S (Module.Dual R M)) g
      -- hg : mk' ... f t = g, i.e., LocalizedModule.mk f t = g
      -- Now we have: φ_dual (LocalizedModule.mk f t) = e
      have h_dual_apply : φ_dual (LocalizedModule.mk f t) = e := by
        rw [hg, LinearEquiv.apply_symm_apply]
      -- Evaluate both sides at y = LocalizedModule.mk x s
      have h_eval : (e : Mₘ →ₗ[Rₘ] Rₘ) y = (1 : Rₘ) := by
        dsimp [y]
        simp
      -- Also compute via the dual element
      have h_eval' : (φ_dual (LocalizedModule.mk f t)) (LocalizedModule.mk x s) = (1 : Rₘ) := by
        rw [h_dual_apply, hy]
        exact h_eval
      -- Key formula: (φ_dual (mk f t)) (mk x s) = mk (f x) (t * s)
      have h_formula : (φ_dual (LocalizedModule.mk f t)) (LocalizedModule.mk x s) =
          LocalizedModule.mk (contractLeft R M (f ⊗ₜ[R] x)) (t * s) := by
        have h_contract : contractLeft R M (f ⊗ₜ[R] x) = f x := contractLeft_apply _ _
        rw [h_contract]
        -- It suffices to prove the formula for denominators 1, then use Rₘ-linearity
        -- First, prove the base case
        have h_base : (φ_dual (LocalizedModule.mk f 1)) (LocalizedModule.mk x 1) =
            LocalizedModule.mk (f x) 1 := by
          dsimp [φ_dual, e1ₘ]
          -- e1ₘ = e1.extendScalarsOfIsLocalization S Rₘ
          -- So goal: (e1 (mk f 1)).extendScalarsOfIsLocalization ... (mk x 1) followed by iso_R = mk (f x) 1
          -- But extendScalarsOfIsLocalization doesn't change the function
          -- And iso_R is essentially the identity
          -- We need to compute e1 (mk f 1)
          have h_e1 := Module.FinitePresentation.linearEquivMapExtendScalars_apply S f
          -- h_e1 : e1 (mk f 1) = IsLocalizedModule.mapExtendScalars S
          --   (mkLinearMap S M) (mkLinearMap S R) (Localization S) f
          -- Now mapExtendScalars is (extend... ∘ map ...)
          -- The key property: (mapExtendScalars ... f) (mk x 1) = mk (f x) 1
          -- This follows from map_apply:
          --   (map S f_M f_R f) (f_M x) = f_R (f x)
          -- i.e., (map ... f) (mk x 1) = mk (f x) 1
          -- and extendScalarsOfIsLocalizationEquiv preserves this
          have h_map : (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
              (LocalizedModule.mkLinearMap S R) f) (LocalizedModule.mk x 1) =
              LocalizedModule.mk (f x) 1 := by
            simpa using IsLocalizedModule.map_apply (S := S)
              (f := LocalizedModule.mkLinearMap S M)
              (g := LocalizedModule.mkLinearMap S R) (h := f) (x := x)
          -- Now relate mapExtendScalars to map
          simpa [iso_R, h_e1] using congrArg
            (fun α => (α.extendScalarsOfIsLocalization S Rₘ) (LocalizedModule.mk x 1)) h_e1
        -- Now reduce the general case to the base case using Rₘ-linearity
        -- Note: LocalizedModule.mk f t = (mk (1 : R) t : Rₘ) • LocalizedModule.mk f 1
        have h_smul_f : LocalizedModule.mk f t =
            (LocalizedModule.mk (1 : R) t : Rₘ) • LocalizedModule.mk f 1 := by
          simp
        have h_smul_x : LocalizedModule.mk x s =
            (LocalizedModule.mk (1 : R) s : Rₘ) • LocalizedModule.mk x 1 := by
          simp
        rw [h_smul_f, h_smul_x]
        -- φ_dual is Rₘ-linear
        have h_φ_linear : φ_dual ((LocalizedModule.mk (1 : R) t : Rₘ) • LocalizedModule.mk f 1) =
            (LocalizedModule.mk (1 : R) t : Rₘ) • φ_dual (LocalizedModule.mk f 1) := by
          simp
        -- This is already taken care of by `simp` above
        -- Now the LHS becomes:
        -- ((mk 1 t : Rₘ) • φ_dual (mk f 1)) ((mk 1 s : Rₘ) • mk x 1)
        -- = (mk 1 t) * (mk 1 s) * (φ_dual (mk f 1) (mk x 1))
        -- = (mk 1 (t*s)) * mk (f x) 1
        -- = mk (f x) (t*s)
        simp [h_base, mul_comm, smul_smul, LocalizedModule.smul_mk, LocalizedModule.mk_smul_mk]
      rw [h_formula] at h_eval'
      -- Now h_eval' : LocalizedModule.mk (f x) (t * s) = 1 in Rₘ
      -- This means there exists u ∈ S such that u * f x = u * (t * s) in R
      have h_mk_eq := (LocalizedModule.mk_eq_mk_iff S _ _ _ _).mp h_eval'
      rcases h_mk_eq with ⟨u, hu⟩
      -- Now contractLeft R M (f ⊗ x) = f x ∈ I (by definition of I)
      have h_mem_I : contractLeft R M (f ⊗ₜ[R] x) ∈ I := by
        apply LinearMap.mem_range.mpr
        exact ⟨f ⊗ₜ[R] x, rfl⟩
      -- hu says u * (1) * (f x) = u * (t * s) * 1
      -- Simplify: u * f x = u * t * s
      have hu_simp : (u : R) * contractLeft R M (f ⊗ₜ[R] x) = (u : R) * (t : R) * (s : R) := by
        simpa [contractLeft_apply, mul_comm, mul_left_comm, mul_assoc] using hu
      -- Then u * f x ∈ I
      have h_mem_u : (u : R) * contractLeft R M (f ⊗ₜ[R] x) ∈ I :=
        Ideal.mul_mem_right _ h_mem_I
      rw [hu_simp] at h_mem_u
      -- Now u * t * s ∈ S (product of elements of S)
      have h_prod_S : (u : R) * (t : R) * (s : R) ∈ S :=
        Submonoid.mul_mem S (Submonoid.mul_mem S u.2 t.2) s.2
      -- Since I ⊆ m (by hmI)
      have h_in_m : (u : R) * (t : R) * (s : R) ∈ m := hmI h_mem_u
      -- But h_prod_S says it's in S = m.primeCompl, i.e., NOT in m, contradiction
      exact h_prod_S h_in_m
  -- Now we have that contractLeft R M is surjective
  -- Since R is invertible, surjective implies bijective
  exact Invertible.bijective_of_surjective h_surj
