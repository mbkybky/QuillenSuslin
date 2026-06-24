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

universe u v w

open TensorProduct CategoryTheory Limits

namespace Module

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Flat R A]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] {f : M →ₗ[R] N}

theorem HasFiniteFreeResolutionOfLength.of_flat_baseChange {n : ℕ}
    (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A (A ⊗[R] M) n := by
  have hM' : HasFiniteFreeResolutionOfLength R (ULift.{u} M) n :=
    hM.of_linearEquiv (show M ≃ₗ[R] ULift.{u} M from ULift.moduleEquiv.symm)
  have hULift : HasFiniteFreeResolutionOfLength A (A ⊗[R] ULift.{u} M) n := by
    let F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} A :=
      { obj := fun X => ModuleCat.of A (A ⊗[R] X)
        map := fun {X Y} f => ModuleCat.ofHom (AlgebraTensorModule.lTensor A A f.hom)
        map_id := fun X => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a m => simp
          | add x y hx hy => rw [map_add, map_add, hx, hy]
        map_comp := fun {X Y Z} f g => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a m => simp
          | add x y hx hy => rw [map_add, map_add, hx, hy] }
    haveI : F.Additive :=
      { map_add := fun {X Y} f g => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          induction x using TensorProduct.induction_on with
          | zero => simp [F]
          | tmul a m => simp [F]
          | add x y hx hy => rw [map_add, map_add, hx, hy] }
    have hExactFunctor : PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
      exact ((Functor.exact_tfae F).out 0 3).1 (fun S hS => by
        refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
        · change Function.Exact (LinearMap.lTensor A S.f.hom) (LinearMap.lTensor A S.g.hom)
          exact Flat.lTensor_exact A
            ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
        · change Function.Injective (LinearMap.lTensor A S.f.hom)
          exact Flat.lTensor_preserves_injective_linearMap S.f.hom hS.moduleCat_injective_f
        · change Function.Surjective (LinearMap.lTensor A S.g.hom)
          exact LinearMap.lTensor_surjective A hS.moduleCat_surjective_g)
    haveI : PreservesFiniteLimits F := hExactFunctor.1
    haveI : PreservesFiniteColimits F := hExactFunctor.2
    change (ModuleCat.finiteFree A).HasFiniteResolutionOfLength
      (F.obj (ModuleCat.of R (ULift.{u} M))) n
    exact hM'.map_exactFunctor F (fun X hX => by
      have hX' : Module.Finite R X ∧ Module.Free R X :=
        (ModuleCat.finiteFree_iff R X).1 hX
      letI : Module.Finite R X := hX'.1
      letI : Module.Free R X := hX'.2
      exact ModuleCat.finiteFree_of A (F.obj X))
  exact hULift.of_linearEquiv (LinearEquiv.baseChange R A (ULift.{u} M) M ULift.moduleEquiv)

instance HasFiniteFreeResolution.of_flat_baseChange [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution A (A ⊗[R] M) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, hn.of_flat_baseChange⟩

variable [Small.{w, u} A] (S : Submonoid R)

theorem HasFiniteFreeResolutionOfLength.of_isBaseChange_of_flat
    (hf : IsBaseChange A f) {n : ℕ} (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A N n :=
  hM.of_flat_baseChange.of_linearEquiv hf.equiv

theorem HasFiniteFreeResolution.of_isBaseChange_of_flat
    (hf : IsBaseChange A f) [HasFiniteFreeResolution R M] : HasFiniteFreeResolution A N :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, hn.of_isBaseChange_of_flat hf⟩

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
