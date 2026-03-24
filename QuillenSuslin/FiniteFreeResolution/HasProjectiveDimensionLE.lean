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

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem hasFiniteFreeResolutionOfLength_of_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] : HasFiniteFreeResolutionOfLength R M n := by
  induction n generalizing M with
  | zero =>
      have : Module.Projective R M := (IsProjective.iff_projective M).2 <|
        projective_iff_hasProjectiveDimensionLT_one.2 inferInstance
      have : Module.Free R M := Module.free_of_flat_of_isLocalRing
      exact HasFiniteFreeResolutionOfLength.zero M
  | succ n ih =>
      rcases Module.exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
      have : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
        (LinearMap.shortExact_shortComplexKer surjf).hasProjectiveDimensionLT_X₁ (n + 1)
          inferInstance inferInstance
      exact hasFiniteFreeResolutionOfLength_of_ker_hasFiniteFreeResolutionOfLength
        (LinearMap.ker f).subtype f (Submodule.subtype_injective _) surjf
          (LinearMap.exact_subtype_ker_map f) (ih (LinearMap.ker f))

theorem hasFiniteFreeResolution_of_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] : HasFiniteFreeResolution R M :=
  ⟨n, hasFiniteFreeResolutionOfLength_of_hasProjectiveDimensionLE R M n⟩
