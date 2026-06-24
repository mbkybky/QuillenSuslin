/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import QuillenSuslin.FiniteFreeResolution.Basic
public import QuillenSuslin.ObjectProperty.Exact

/-!
# The short exact sequences of modules admitting finite free resolutions

This file proves that in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if any two of these modules
have a finite free resolution, then so does the third .
-/

public section

universe u v

open CategoryTheory Category Limits

namespace ModuleCat

variable (R : Type u) [Ring R]

private noncomputable def pairCone (F : Discrete WalkingPair ⥤ ModuleCat.{v} R) :
    Cone F where
  pt := ModuleCat.of R (F.obj ⟨WalkingPair.left⟩ × F.obj ⟨WalkingPair.right⟩)
  π :=
    { app := fun j => by
        rcases j with ⟨j⟩
        cases j with
        | left =>
            exact ModuleCat.ofHom
              (LinearMap.fst R (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩))
        | right =>
            exact ModuleCat.ofHom
              (LinearMap.snd R (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩))
      naturality := by
        rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
        cases h
        cases j
        · simp
        · simp }

private noncomputable def pairConeIsLimit (F : Discrete WalkingPair ⥤ ModuleCat.{v} R) :
    IsLimit (pairCone R F) := by
  refine IsLimit.mk ?lift ?fac ?uniq
  · intro s
    exact ModuleCat.ofHom <| LinearMap.prod
      ((s.π.app ⟨WalkingPair.left⟩).hom) ((s.π.app ⟨WalkingPair.right⟩).hom)
  · intro s j
    rcases j with ⟨j⟩
    cases j
    · ext x
      rfl
    · ext x
      rfl
  · intro s m hm
    ext x
    apply Prod.ext
    · change (m.hom x).1 = (s.π.app ⟨WalkingPair.left⟩).hom x
      exact ConcreteCategory.congr_hom (hm ⟨WalkingPair.left⟩) x
    · change (m.hom x).2 = (s.π.app ⟨WalkingPair.right⟩).hom x
      exact ConcreteCategory.congr_hom (hm ⟨WalkingPair.right⟩) x

instance finiteFree_isClosedUnderBinaryProducts :
    (finiteFree R : ObjectProperty (ModuleCat.{v} R)).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let F := p.diag
    let e : (pairCone R F).pt ≅ X :=
      IsLimit.conePointUniqueUpToIso (pairConeIsLimit R F) p.isLimit
    apply (finiteFree R).prop_of_iso e
    have hleft := p.prop_diag_obj ⟨WalkingPair.left⟩
    have hleft' : Module.Finite R (F.obj ⟨WalkingPair.left⟩) ∧
        Module.Free R (F.obj ⟨WalkingPair.left⟩) :=
      (ModuleCat.finiteFree_iff R (F.obj ⟨WalkingPair.left⟩)).1 hleft
    have hright := p.prop_diag_obj ⟨WalkingPair.right⟩
    have hright' : Module.Finite R (F.obj ⟨WalkingPair.right⟩) ∧
        Module.Free R (F.obj ⟨WalkingPair.right⟩) :=
      (ModuleCat.finiteFree_iff R (F.obj ⟨WalkingPair.right⟩)).1 hright
    letI : Module.Finite R (F.obj ⟨WalkingPair.left⟩) :=
      hleft'.1
    letI : Module.Free R (F.obj ⟨WalkingPair.left⟩) :=
      hleft'.2
    letI : Module.Finite R (F.obj ⟨WalkingPair.right⟩) :=
      hright'.1
    letI : Module.Free R (F.obj ⟨WalkingPair.right⟩) :=
      hright'.2
    exact finiteFree_of R (F.obj ⟨WalkingPair.left⟩ × F.obj ⟨WalkingPair.right⟩)

theorem finiteFree_le_projective :
    (finiteFree R : ObjectProperty (ModuleCat.{v} R)) ≤
      CategoryTheory.isProjective (ModuleCat.{v} R) := by
  intro X hX
  have hX' : Module.Finite R X ∧ Module.Free R X :=
    (ModuleCat.finiteFree_iff R X).1 hX
  letI : Module.Free R X := hX'.2
  haveI : Module.Projective R X := Module.Projective.of_free
  exact ModuleCat.projective_of_categoryTheory_projective X

end ModuleCat

namespace Module.HasFiniteFreeResolution

variable {R : Type u} [CommRing R]
  {M₁ : Type v} {M₂ : Type v} {M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₁` and `M₃` have
finite free resolutions, then so does `M₂`. -/
theorem of_shortExact_of_left_of_right (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₁] [HasFiniteFreeResolution R M₃] :
    HasFiniteFreeResolution R M₂ := by
  let S : ShortComplex (ModuleCat.{v} R) := ModuleCat.shortComplexOfCompEqZero f g (by
    ext x
    exact h.apply_apply_eq_zero x)
  exact CategoryTheory.ObjectProperty.HasFiniteResolution.of_shortExact_of_left_of_right
    (ModuleCat.finiteFree_le_projective R) (ModuleCat.shortComplex_shortExact S h hf hg)

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₁` and `M₂` have
finite free resolutions, then so does `M₃`. -/
theorem of_shortExact_of_left_of_middle (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₁] [HasFiniteFreeResolution R M₂] :
    HasFiniteFreeResolution R M₃ := by
  let S : ShortComplex (ModuleCat.{v} R) := ModuleCat.shortComplexOfCompEqZero f g (by
    ext x
    exact h.apply_apply_eq_zero x)
  exact CategoryTheory.ObjectProperty.HasFiniteResolution.of_shortExact_of_left_of_middle
    (ModuleCat.finiteFree_le_projective R) (ModuleCat.shortComplex_shortExact S h hf hg)

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₂` and `M₃` have
finite free resolutions, then so does `M₁`. -/
theorem of_shortExact_of_middle_of_right (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₂] [HasFiniteFreeResolution R M₃] :
    HasFiniteFreeResolution R M₁ := by
  let S : ShortComplex (ModuleCat.{v} R) := ModuleCat.shortComplexOfCompEqZero f g (by
    ext x
    exact h.apply_apply_eq_zero x)
  exact CategoryTheory.ObjectProperty.HasFiniteResolution.of_shortExact_of_middle_of_right
    (ModuleCat.finiteFree_le_projective R) (ModuleCat.shortComplex_shortExact S h hf hg)

end Module.HasFiniteFreeResolution
