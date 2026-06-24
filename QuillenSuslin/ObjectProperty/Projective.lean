/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import QuillenSuslin.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Finite projective resolutions and projective dimension

This file relates finite resolutions by projective objects, defined via
`ObjectProperty.HasFiniteResolutionOfLength`, with Mathlib's Ext-vanishing
definition of `HasProjectiveDimensionLE`.
-/

public section

universe v u

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A] {X : A} {n : ℕ}

namespace HasFiniteResolutionOfLength

/-- A finite projective resolution of length `n` gives projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE (hX : (isProjective A).HasFiniteResolutionOfLength X n) :
    HasProjectiveDimensionLE X n := by
  induction hX with
  | zero X hX => infer_instance
  | succ S n hS h₂ _ ih =>
      refine hS.hasProjectiveDimensionLT_X₃ (n + 1) ih <|
        hasProjectiveDimensionLT_of_ge S.X₂ 1 ((n + 1) + 1) (by simp)

/-- If the category has enough projectives, projective dimension at most `n` gives a finite
projective resolution of length `n`. -/
theorem of_hasProjectiveDimensionLE [EnoughProjectives A] (hX : HasProjectiveDimensionLE X n) :
    (isProjective A).HasFiniteResolutionOfLength X n := by
  induction n generalizing X with
  | zero =>
      exact HasFiniteResolutionOfLength.zero X
        ((projective_iff_hasProjectiveDimensionLE_zero X).mpr hX)
  | succ n ih =>
      let f : Projective.over X ⟶ X := Projective.π X
      let S : ShortComplex A := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_kernel f)
      have hker : HasProjectiveDimensionLE (kernel f) n :=
        hS.hasProjectiveDimensionLT_X₁ (n + 1)
          (hasProjectiveDimensionLT_of_ge S.X₂ 1 (n + 1) (by simp)) (by simp [S, hX])
      exact HasFiniteResolutionOfLength.succ S n hS inferInstance (ih hker)

end HasFiniteResolutionOfLength

end ObjectProperty

end CategoryTheory
