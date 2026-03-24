/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.LocalRing.Module
import QuillenSuslin.FiniteFreeResolution.Basic

universe u v

open CategoryTheory

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Small.{v} R]

theorem hasFiniteFreeResolution_of_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasFiniteFreeResolution R M := by
  induction n generalizing M with
  | zero =>
      have : Module.Projective R M := (IsProjective.iff_projective M).2 <|
        projective_iff_hasProjectiveDimensionLT_one.2 inferInstance
      have : Module.Free R M := Module.free_of_flat_of_isLocalRing
      exact hasFiniteFreeResolution_of_finite_of_free M
  | succ n ih =>
      rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
      have hker : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
        (LinearMap.shortExact_shortComplexKer surjf).hasProjectiveDimensionLT_X₁ (n + 1)
          inferInstance inferInstance
      rcases ih (LinearMap.ker f) with ⟨k, hk⟩
      exact hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution
        (LinearMap.ker f).subtype f (Submodule.subtype_injective _) surjf
        (LinearMap.exact_subtype_ker_map f) ⟨k, hk⟩
