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

open TensorProduct LocalizedModule IsLocalizedModule IsLocalization

theorem Module.Invertible.of_locally_free_of_rank_one' [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M where
  bijective := by
    apply bijective_of_localized_maximal
    intro m _
    let φ (p : Ideal R) [p.IsPrime] : LocalizedModule.AtPrime p (Module.Dual R M) ≃ₗ[Localization.AtPrime p] Module.Dual (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
      (Module.FinitePresentation.linearEquivMapExtendScalars p.primeCompl).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    sorry

theorem Module.Invertible.of_locally_free_of_rank_one'' [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M where
  bijective := by
    have f (m : Ideal R) [m.IsMaximal] : Module.Dual R M ⊗[R] M →ₗ[R] Localization.AtPrime m := sorry
    have (m : Ideal R) [m.IsMaximal] : IsLocalizedModule.AtPrime m (f m) := sorry
    refine bijective_of_isLocalized_maximal (fun m ↦ Localization.AtPrime m) f
      (fun m ↦ Localization.AtPrime m) (fun _ _ ↦ mkLinearMap _ _) (contractLeft R M) (fun m _ ↦ ?_)
    sorry

section


variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]

-- For every maximal ideal `p` of `R`, let `Mₚ` (resp. `Nₚ`, resp. `Lₚ`) the localizations
-- of `M` (resp. `N`, resp. `L`) at `p`.
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [_hf : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [_hg : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P)]
  (F : M →ₗ[R] N)

theorem bijective_of_isLocalized_maximal'
    (H : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (IsLocalizedModule.map P.primeCompl (f P) (g P) F)) :
    Function.Bijective F :=
  bijective_of_isLocalized_maximal Mₚ f Nₚ g F H

end

theorem Module.Invertible.of_locally_free_of_rank_one''' [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M where
  bijective := by
    --let f1 (m : Ideal R) [m.IsMaximal] : Module.Dual R M →ₗ[R] LocalizedModule.AtPrime m (Module.Dual R M) := mkLinearMap _ _
    --let f2 (m : Ideal R) [m.IsMaximal] : Module.Dual R M →ₗ[R] LocalizedModule.AtPrime m (Module.Dual R M) := mkLinearMap _ _
    /- have f (m : Ideal R) [m.IsMaximal] : Module.Dual R M ⊗[R] M →ₗ[R] Module.Dual (Localization.AtPrime m) (LocalizedModule.AtPrime m M) ⊗[Localization.AtPrime m] (LocalizedModule.AtPrime m M) := sorry -/
    let φ (p : Ideal R) [p.IsPrime] : LocalizedModule.AtPrime p (Module.Dual R M) ≃ₗ[Localization.AtPrime p] Module.Dual (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
      (Module.FinitePresentation.linearEquivMapExtendScalars p.primeCompl).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    let f (m : Ideal R) [m.IsMaximal] : Module.Dual R M →ₗ[R] Module.Dual (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := (φ m).toLinearMap ∘ₗ (mkLinearMap m.primeCompl (Module.Dual R M))
    have (m : Ideal R) [m.IsMaximal] : IsLocalizedModule m.primeCompl (f m) := by
      apply IsLocalizedModule.of_linearEquiv
    let ϕ (m : Ideal R) [m.IsMaximal] := ((IsLocalization.moduleTensorEquiv m.primeCompl (Localization.AtPrime m) (Dual (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) (LocalizedModule.AtPrime m M)).restrictScalars R).symm.toLinearMap ∘ₗ TensorProduct.map (f m) (mkLinearMap m.primeCompl M)
    have hϕ : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (ϕ P) := by
      intro P hP
      apply IsLocalizedModule.of_linearEquiv
    refine bijective_of_isLocalized_maximal' _ ϕ (_hf := hϕ)
      (fun m ↦ Localization.AtPrime m) (fun _ _ ↦ mkLinearMap _ _) (contractLeft R M) (fun m _ ↦ ?_)
    have h : (mapExtendScalars m.primeCompl (ϕ m) (mkLinearMap m.primeCompl R))
        (Localization.AtPrime m) (contractLeft R M) =
        contractLeft (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := by
      apply TensorProduct.ext
      ext ψ x
      simp --[ϕ, f, φ]
      sorry
    change Function.Bijective <| (mapExtendScalars _ (ϕ m) _) (Localization.AtPrime m) _
    rw [h]
    sorry

/-
    refine bijective_of_isLocalized_maximal' _ ϕ (_hf := fun _ _ ↦ inferInstance)
      (fun m ↦ Localization.AtPrime m) (fun _ _ ↦ mkLinearMap _ _) _ (fun m _ ↦ ⟨?_, ?_⟩)
    · sorry
    · intro x
      simp
      sorry
-/

theorem Module.Invertible.of_locally_free_of_rank_one''''' [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M where
  bijective := by
    let ϕ (m : Ideal R) [m.IsMaximal] :=
      TensorProduct.map (mkLinearMap m.primeCompl (Module.Dual R M)) (mkLinearMap m.primeCompl M)
    refine bijective_of_isLocalized_maximal _ ϕ
      (fun m ↦ Localization.AtPrime m) (fun _ _ ↦ mkLinearMap _ _) (contractLeft R M) (fun m _ ↦ ?_)
    let Rₘ := Localization.AtPrime m
    let Mₘ := LocalizedModule.AtPrime m M
    let Dₘ := Module.Dual Rₘ (LocalizedModule.AtPrime m M)
    simp
    let ψ : LocalizedModule m.primeCompl (Dual R M) ⊗[R] Mₘ ≃ₗ[Rₘ] Dₘ ⊗[Rₘ] Mₘ :=
      (moduleTensorEquiv m.primeCompl Rₘ (LocalizedModule m.primeCompl (Dual R M)) Mₘ).symm ≪≫ₗ
        (Module.FinitePresentation.linearEquivMapExtendScalars  m.primeCompl
          |>.extendScalarsOfIsLocalization m.primeCompl Rₘ).rTensor Mₘ
    have h : (mapExtendScalars m.primeCompl (ϕ m) (mkLinearMap m.primeCompl R)) Rₘ (contractLeft R M)
        = contractLeft Rₘ Mₘ ∘ₗ ψ.toLinearMap := by
      sorry
    sorry

theorem Module.Invertible.of_locally_free_of_rank_one [Module.FinitePresentation R M]
    (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Invertible R M where
  bijective := by
    let ϕ (m : Ideal R) [m.IsMaximal] :=
      TensorProduct.map (mkLinearMap m.primeCompl (Module.Dual R M)) (mkLinearMap m.primeCompl M)
    refine bijective_of_isLocalized_maximal _ ϕ
      (fun m ↦ Localization.AtPrime m) (fun _ _ ↦ mkLinearMap _ _) (contractLeft R M) (fun m _ ↦ ?_)
    let Rₘ := Localization.AtPrime m
    let Mₘ := LocalizedModule.AtPrime m M
    let Dₘ := Module.Dual Rₘ (LocalizedModule.AtPrime m M)
    simp
    let ψ : LocalizedModule m.primeCompl (Dual R M) ⊗[R] Mₘ ≃ₗ[R] Dₘ ⊗[Rₘ] Mₘ :=
      (Module.FinitePresentation.linearEquivMapExtendScalars m.primeCompl).rTensor Mₘ ≪≫ₗ
        (moduleTensorEquiv m.primeCompl Rₘ Dₘ Mₘ).symm.restrictScalars R
    have h : (map m.primeCompl (ϕ m) (mkLinearMap m.primeCompl R)) (contractLeft R M)
        = (contractLeft Rₘ Mₘ).restrictScalars R ∘ₗ ψ.toLinearMap := by
      apply TensorProduct.ext
      ext f x
      simp
      rw [show ψ (f ⊗ₜ[R] x) =
        (Module.FinitePresentation.linearEquivMapExtendScalars m.primeCompl f) ⊗ₜ[Rₘ] x from rfl]
      induction x using induction_on with | _ x s
      induction f using induction_on with | _ f t
      simp [ϕ]
      sorry
    sorry
