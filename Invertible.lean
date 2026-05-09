/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib

public section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

open TensorProduct LocalizedModule IsLocalizedModule IsLocalization

theorem Module.Invertible.of_isLocalized_maximal [Module.FinitePresentation R M]
    (Rₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], CommRing (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Algebra R (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalization.AtPrime (Rₚ m) m]
    (Mₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], AddCommGroup (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module R (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module (Rₚ m) (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsScalarTower R (Rₚ m) (Mₚ m)]
    (f : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₚ m)
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalizedModule.AtPrime m (f m)]
    (h : ∀ (m : Ideal R) [m.IsMaximal], Module.Invertible (Rₚ m) (Mₚ m)) :
    Module.Invertible R M where
  bijective := by
    sorry

theorem Module.Invertible.of_localized_maximal [Module.FinitePresentation R M]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) :
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
