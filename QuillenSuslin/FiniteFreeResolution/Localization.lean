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

universe u v

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Small.{v} R]

open CategoryTheory in
theorem hasFiniteFreeResolution_of_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasFiniteFreeResolution R M := by
  sorry

variable {R M}

theorem hasFiniteFreeResolutionLength_localized (S : Submonoid R) {n : ℕ}
    (h : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength (Localization S) (LocalizedModule S M) n := by
  sorry

theorem hasFiniteFreeResolution_localized (S : Submonoid R) (h : HasFiniteFreeResolution R M) :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) := by
  sorry
