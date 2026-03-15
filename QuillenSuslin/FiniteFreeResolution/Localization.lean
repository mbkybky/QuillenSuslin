/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.LocalProperties.Projective
import QuillenSuslin.FiniteFreeResolution.Basic

universe u

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

open CategoryTheory in
theorem hasFiniteFreeResolution_of_hasProjectiveDimensionLE
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasFiniteFreeResolution R M := by
  induction n generalizing M with
  | zero =>
      have hproj : Projective (ModuleCat.of R M) :=
        (projective_iff_hasProjectiveDimensionLT_one _).2 inferInstance
      have : Module.Projective R M := (IsProjective.iff_projective M).2 hproj
      have : Module.Free R M := Module.free_of_flat_of_isLocalRing
      exact hasFiniteFreeResolution_of_finite_of_free M
  | succ n ih =>
      obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
      let S := LinearMap.shortComplexKer f
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hker : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
        simpa [S, HasProjectiveDimensionLE] using
          (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
      have : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.of_injective (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype
      have hfreeP : HasFiniteFreeResolution R P := hasFiniteFreeResolution_of_finite_of_free P
      have hker' : HasFiniteFreeResolution R (LinearMap.ker f) := ih _
      exact @hasFiniteFreeResolution_of_shortExact_of_left_of_middle
        R _ (LinearMap.ker f) P M _ _ _ _ _ _ (LinearMap.ker f).subtype f
          (LinearMap.ker f).injective_subtype hf (LinearMap.exact_subtype_ker_map f) hker' hfreeP

variable {R M}

theorem hasFiniteFreeResolutionLength_localized
    (S : Submonoid R) {n : ℕ} (h : HasFiniteFreeResolutionLength R M n) :
    HasFiniteFreeResolutionLength (Localization S) (LocalizedModule S M) n := by
  induction h with
  | zero P =>
      let b := Module.Free.chooseBasis R P
      let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S P)
      have : Module.Free (Localization S) (LocalizedModule S P) :=
        Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S P)
      have : Module.Finite (Localization S) (LocalizedModule S P) := Module.Finite.of_basis bS
      exact HasFiniteFreeResolutionLength.zero (LocalizedModule S P)
  | succ P n F f hf hker ih =>
      let b := Module.Free.chooseBasis R F
      let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S F)
      have : Module.Free (Localization S) (LocalizedModule S F) :=
        Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S F)
      have : Module.Finite (Localization S) (LocalizedModule S F) := Module.Finite.of_basis bS
      have hker' :
          HasFiniteFreeResolutionLength (Localization S)
            (LinearMap.ker (LocalizedModule.map S f)) n := by
        let eKer : LocalizedModule S (LinearMap.ker f) ≃ₗ[Localization S]
            LinearMap.ker (LocalizedModule.map S f) :=
          (Submodule.localizedEquiv S (LinearMap.ker f)).symm ≪≫ₗ
            LinearEquiv.ofEq _ _ (LinearMap.localized'_ker_eq_ker_localizedMap (Localization S) S
              (LocalizedModule.mkLinearMap S F) (LocalizedModule.mkLinearMap S P) f)
        exact hasFiniteFreeResolutionLength_of_linearEquiv eKer ih
      exact HasFiniteFreeResolutionLength.succ (LocalizedModule S P) n
        (LocalizedModule S F) (LocalizedModule.map S f)
          (LocalizedModule.map_surjective S f hf) hker'

theorem hasFiniteFreeResolution_localized
    (S : Submonoid R) (h : HasFiniteFreeResolution R M) :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) := by
  rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
  let b := Module.Free.chooseBasis R F
  let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S F)
  have : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S F)
  have : Module.Finite (Localization S) (LocalizedModule S F) := Module.Finite.of_basis bS
  let eKer : LocalizedModule S (LinearMap.ker f) ≃ₗ[Localization S]
      LinearMap.ker (LocalizedModule.map S f) :=
    (Submodule.localizedEquiv S (LinearMap.ker f)).symm ≪≫ₗ
      LinearEquiv.ofEq _ _ (LinearMap.localized'_ker_eq_ker_localizedMap
        (Localization S) S (LocalizedModule.mkLinearMap S F) (LocalizedModule.mkLinearMap S M) f)
  exact ⟨LocalizedModule S F, inferInstance, inferInstance, inferInstance, inferInstance,
    LocalizedModule.map S f, LocalizedModule.map_surjective S f hf, n,
      hasFiniteFreeResolutionLength_of_linearEquiv eKer <|
        hasFiniteFreeResolutionLength_localized S hn⟩
