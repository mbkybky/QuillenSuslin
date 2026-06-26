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

open CategoryTheory Category Limits

section compHom

/-- Let `M` be a `R`-module. Viewing `M` as an `S`-module via `σ' : S →+* R`, then the identity map
gives a semilinear equivalence over `σ: R →+* S`. -/
def Module.compHom.selfEquiv {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (σ' : S →+* R)
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [AddCommMonoid M] [Module R M] :
  letI : Module S M := compHom M σ'; M ≃ₛₗ[σ] M :=
  letI : Module S M := compHom M σ'
{ __ := AddEquiv.refl M
  map_smul' a x : a • x = (σ' (σ a)) • x := by simp }

end compHom

namespace ModuleCat

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S)

instance : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteLimits _ _ _ := ⟨fun {K} ↦ preservesLimit_restrictScalars f K⟩

instance : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) where
  preservesFiniteColimits _ _ _ := ⟨fun {K} ↦ preservesColimit_restrictScalars f K⟩

end ModuleCat

namespace Module

variable {R : Type u} [Ring R] {S : Type u'} [Ring S] [Small.{v'} S]
  {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  {M : Type v} [AddCommGroup M] [Module R M] {N : Type v'} [AddCommGroup N] [Module S N]

theorem HasFiniteFreeResolutionOfLength.of_semilinearEquiv
    {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R M n) (e : M ≃ₛₗ[σ] N) :
    HasFiniteFreeResolutionOfLength S N n := by
  let : Module S M := Module.compHom M σ'
  refine HasFiniteFreeResolutionOfLength.of_linearEquiv
    ((Module.compHom.selfEquiv σ σ' M).symm.trans e)
      (hn.map_exactFunctor (ModuleCat.restrictScalars.{v} σ') fun X ⟨_, _⟩ ↦ ?_)
  let : Module S X := Module.compHom X σ'
  let eX : X ≃ₛₗ[σ] (ModuleCat.restrictScalars.{v} σ').obj X := Module.compHom.selfEquiv σ σ' X
  exact ⟨Module.Finite.of_surjective eX.toLinearMap eX.surjective, Module.Free.of_equiv eX⟩

theorem HasFiniteFreeResolution.of_semilinearEquiv [HasFiniteFreeResolution R M] (e : M ≃ₛₗ[σ] N) :
    HasFiniteFreeResolution S N := by
  obtain ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  exact ⟨n, hn.of_semilinearEquiv e⟩

end Module
