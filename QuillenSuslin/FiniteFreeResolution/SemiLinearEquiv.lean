/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import QuillenSuslin.FiniteFreeResolution.Basic

public section

universe v v' u u'

namespace Module.HasFiniteFreeResolutionOfLength

open CategoryTheory Category Limits

variable {R : Type u} [Ring R]

theorem of_semilinearEquiv {S : Type u'} [Ring S] [Small.{v'} S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R M n)
    {N : Type v'} [AddCommGroup N] [Module S N] (e : M ≃ₛₗ[σ] N) :
    HasFiniteFreeResolutionOfLength S N n := by
  haveI : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} σ') := by
    constructor
    intro J _ _
    constructor
    intro K
    exact ModuleCat.preservesLimit_restrictScalars σ' K
  haveI : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} σ') := by
    constructor
    intro J _ _
    constructor
    intro K
    exact ModuleCat.preservesColimit_restrictScalars σ' K
  letI : Module S M := Module.compHom M σ'
  have hM : HasFiniteFreeResolutionOfLength S M n := by
    refine ObjectProperty.HasFiniteResolutionOfLength.map_exactFunctor
      (ModuleCat.restrictScalars.{v} σ') (fun X hX => ?_) hn
    rw [ModuleCat.finiteFree_iff] at hX ⊢
    rcases hX with ⟨hfinite, hfree⟩
    letI : Module.Finite R X := hfinite
    letI : Module.Free R X := hfree
    let fX : X →ₛₗ[σ] (ModuleCat.restrictScalars.{v} σ').obj X :=
      { toFun := fun x => x
        map_add' _ _ := rfl
        map_smul' := by
          intro r x
          change r • x = σ' (σ r) • x
          rw [← RingHom.comp_apply σ' σ r, RingHomInvPair.comp_eq]
          rfl }
    let eX : X ≃ₛₗ[σ] (ModuleCat.restrictScalars.{v} σ').obj X :=
      LinearEquiv.mk fX id (by intro x; rfl) (by intro x; rfl)
    exact ⟨Module.Finite.of_surjective
      (eX : X →ₛₗ[σ] (ModuleCat.restrictScalars.{v} σ').obj X) eX.surjective,
      Module.Free.of_equiv eX⟩
  let eS : M ≃ₗ[S] N :=
    e.toAddEquiv.toLinearEquiv (by
      intro s x
      change e (σ' s • x) = s • e x
      rw [e.map_smulₛₗ, ← RingHom.comp_apply σ σ' s, RingHomInvPair.comp_eq]
      rfl)
  exact hM.of_linearEquiv eS

end Module.HasFiniteFreeResolutionOfLength
