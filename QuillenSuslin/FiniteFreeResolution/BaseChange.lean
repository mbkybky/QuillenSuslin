/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import QuillenSuslin.FiniteFreeResolution.Basic

/-!
# Flat base change of modules admitting finite free resolutions

This file proves that finite free resolutions are preserved by flat base change and localization.
-/

public section

universe v v' u u'

open TensorProduct CategoryTheory Limits

namespace Module

variable {R : Type u} [CommRing R] {A : Type u'} [CommRing A] [Algebra R A] [Flat R A]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type v'} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] {f : M →ₗ[R] N}

theorem HasFiniteFreeResolutionOfLength.of_flat_baseChange {n : ℕ}
    (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A (A ⊗[R] M) n := by
  let F : ModuleCat.{v} R ⥤ ModuleCat.{max u' v} A :=
    { obj X := ModuleCat.of A (A ⊗[R] X)
      map f := ModuleCat.ofHom (AlgebraTensorModule.lTensor A A f.hom)
      map_id _ := by simp
      map_comp _ _ := by
        ext
        simp }
  have : F.Additive := ⟨fun {_} _ _ ↦ by simp [F]⟩
  obtain ⟨_, _⟩ : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
    ((Functor.exact_tfae F).out 1 3).1 fun S hS ↦ by
      rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
      exact Flat.lTensor_exact A hS
  exact hM.map_exactFunctor F (fun X ⟨_, _⟩ ↦ ModuleCat.finiteFree_of A (F.obj X))

instance HasFiniteFreeResolution.of_flat_baseChange [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution A (A ⊗[R] M) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, hn.of_flat_baseChange⟩

theorem HasFiniteFreeResolutionOfLength.of_isBaseChange_of_flat [Small.{v', u'} A]
    (hf : IsBaseChange A f) {n : ℕ} (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A N n :=
  hM.of_flat_baseChange.of_linearEquiv hf.equiv

theorem HasFiniteFreeResolution.of_isBaseChange_of_flat [Small.{v', u'} A]
    (hf : IsBaseChange A f) [HasFiniteFreeResolution R M] : HasFiniteFreeResolution A N :=
  HasFiniteFreeResolution.of_linearEquiv hf.equiv

variable (S : Submonoid R)

theorem HasFiniteFreeResolutionOfLength.localizedModule
    {n : ℕ} (h : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength (Localization S) (LocalizedModule S M) n :=
  h.of_isBaseChange_of_flat
    (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M))

instance HasFiniteFreeResolution.localizedModule [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) :=
  HasFiniteFreeResolution.of_isBaseChange_of_flat
    (IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M))

end Module
