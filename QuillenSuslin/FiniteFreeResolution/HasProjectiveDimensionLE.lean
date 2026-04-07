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

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem hasFiniteFreeResolutionOfLength_of_hasProjectiveDimensionLE (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] : HasFiniteFreeResolutionOfLength R M n := by
  induction n generalizing M with
  | zero =>
      have : Projective R M := (IsProjective.iff_projective M).2 <|
        projective_iff_hasProjectiveDimensionLT_one.2 inferInstance
      have : Free R M := free_of_flat_of_isLocalRing
      exact HasFiniteFreeResolutionOfLength.zero M
  | succ n ih =>
      rcases exists_finite_presentation R M with ⟨P, _, _, _, _, f, surjf⟩
      have : HasProjectiveDimensionLE (ModuleCat.of R f.ker) n :=
        (LinearMap.shortExact_shortComplexKer surjf).hasProjectiveDimensionLT_X₁ (n + 1)
          inferInstance inferInstance
      exact HasFiniteFreeResolutionOfLength.succ _ _ _ _  (LinearMap.ker f).subtype f
        f.ker.subtype_injective surjf (LinearMap.exact_subtype_ker_map f) (ih (LinearMap.ker f))

variable {R M} in
theorem hasFiniteFreeResolution_of_projectiveDimension_ne_top
    (h : projectiveDimension (ModuleCat.of R M) ≠ ⊤) : HasFiniteFreeResolution R M :=
  let ⟨n, _⟩ := (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R M)).1 h
  ⟨n, hasFiniteFreeResolutionOfLength_of_hasProjectiveDimensionLE R M n⟩

end Module
