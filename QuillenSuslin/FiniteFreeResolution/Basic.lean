/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Finiteness.Small
public import QuillenSuslin.ObjectProperty.Basic

/-!
# Modules admitting finite free resolutions

## Main definitions
* `Module.HasFiniteFreeResolutionOfLength` : We say that an `R`-module `M` has a finite free
  resolution of length `n` if there exists an exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ M ⟶ 0` such
  that `Eᵢ` are finite free `R`-modules.
* `Module.HasFiniteFreeResolution` : We say that an `R`-module `M` has a finite free resolution
  if it has a finite free resolution of some finite length.
-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits ZeroObject

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- The object property of finite free modules. -/
def finiteFree : ObjectProperty (ModuleCat.{v} R) :=
  fun M => Module.Finite R M ∧ Module.Free R M

theorem finiteFree_of (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] : finiteFree R (ModuleCat.of R M) := by
  exact ⟨inferInstance, inferInstance⟩

theorem finiteFree_iff (M : ModuleCat.{v} R) :
    finiteFree R M ↔ Module.Finite R M ∧ Module.Free R M :=
  Iff.rfl

instance finiteFree_isClosedUnderIsomorphisms : (finiteFree R).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e ⟨_, _⟩
  constructor
  · exact Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.toLinearEquiv.surjective
  · exact Module.Free.of_equiv e.toLinearEquiv

end ModuleCat

namespace Module

variable (R : Type u) [Ring R]

/-- We say that an `R`-module `M` has a finite free resolution of length `n` if
`ModuleCat.of R M` has a finite resolution of length `n` by finite free modules. -/
def HasFiniteFreeResolutionOfLength (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : Prop :=
  (ModuleCat.finiteFree R).HasFiniteResolutionOfLength (ModuleCat.of R M) n

namespace HasFiniteFreeResolutionOfLength

variable {R} {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

variable (R M) in
protected theorem zero [Module.Finite R M] [Module.Free R M] :
    HasFiniteFreeResolutionOfLength R M 0 :=
  ObjectProperty.HasFiniteResolutionOfLength.zero (ModuleCat.of R M) (ModuleCat.finiteFree_of R M)

protected theorem succ {K F M : Type v} [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    [Module.Finite R F] [Module.Free R F] {n : ℕ}
    (f : K →ₗ[R] F) (g : F →ₗ[R] M) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hK : HasFiniteFreeResolutionOfLength R K n) :
    HasFiniteFreeResolutionOfLength R M (n + 1) := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ModuleCat.shortComplexOfCompEqZero f g h.linearMap_comp_eq_zero
  exact ObjectProperty.HasFiniteResolutionOfLength.succ S n
    (ModuleCat.shortComplex_shortExact S h hf hg) (ModuleCat.finiteFree_of R F) hK

theorem induction_on
    {motive : ∀ {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ},
      HasFiniteFreeResolutionOfLength R M n → Prop}
    (hM : HasFiniteFreeResolutionOfLength R M n)
    (zero : ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M],
      motive (Module.HasFiniteFreeResolutionOfLength.zero R M))
    (succ : ∀ (K F M : Type v) [AddCommGroup K] [Module R K]
      [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      [AddCommGroup M] [Module R M]
      (n : ℕ) (f : K →ₗ[R] F) (g : F →ₗ[R] M) (h : Function.Exact f g)
      (hf : Function.Injective f) (hg : Function.Surjective g)
      (hK : HasFiniteFreeResolutionOfLength R K n), motive hK →
      motive (Module.HasFiniteFreeResolutionOfLength.succ f g h hf hg hK)) :
    motive hM := by
  suffices ∀ {X : ModuleCat.{v} R} {n : ℕ}
    (hX : (ModuleCat.finiteFree R).HasFiniteResolutionOfLength X n), motive hX from this hM
  intro X n hX
  induction hX with
  | zero X hX =>
      letI : Module.Finite R X := hX.1
      letI : Module.Free R X := hX.2
      exact zero X
  | succ S n hS h₂ h₁ ih =>
      letI : Module.Finite R S.X₂ := h₂.1
      letI : Module.Free R S.X₂ := h₂.2
      exact succ S.X₁ S.X₂ S.X₃ n S.f.hom S.g.hom
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
          hS.moduleCat_injective_f hS.moduleCat_surjective_g h₁ ih

theorem module_finite (hM : HasFiniteFreeResolutionOfLength R M n) : Module.Finite R M := by
  induction hM using induction_on with
  | zero X => infer_instance
  | succ _ F _ _ _ g _ _ hg _ _ => exact Module.Finite.of_surjective g hg

variable [Small.{w} R]

theorem of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R M n) : HasFiniteFreeResolutionOfLength R N n := by
  revert N
  induction hn using induction_on with
  | zero M =>
      intro N _ _ e
      have : Module.Finite R N := Module.Finite.of_surjective e.toLinearMap e.surjective
      have : Module.Free R N := Module.Free.of_equiv e
      exact Module.HasFiniteFreeResolutionOfLength.zero R N
  | succ K F _ n f g h hf hg hK ih =>
      intro N _ _ e
      haveI : Module.Finite R K := module_finite hK
      have : Small.{w} K := Module.Finite.small R K
      have : Small.{w} F := Module.Finite.small R F
      let e₁ : Shrink.{w} K ≃ₗ[R] K := Shrink.linearEquiv R K
      let e₂ : Shrink.{w} F ≃ₗ[R] F := Shrink.linearEquiv R F
      haveI : Module.Finite R (Shrink.{w} F) :=
        Module.Finite.of_surjective e₂.symm.toLinearMap e₂.symm.surjective
      haveI : Module.Free R (Shrink.{w} F) := Module.Free.of_equiv e₂.symm
      let S' : ShortComplex (ModuleCat.{w} R) :=
        ModuleCat.shortComplexOfConj e₁ e₂ e.symm f g h.linearMap_comp_eq_zero
      have hS' : S'.ShortExact :=
        ModuleCat.shortComplexOfConj_shortExact e₁ e₂ e.symm f g h hf hg
      exact ObjectProperty.HasFiniteResolutionOfLength.succ S' n hS'
        (ModuleCat.finiteFree_of R (Shrink.{w} F)) (ih e₁.symm)

end HasFiniteFreeResolutionOfLength

/-- An `R`-module `M` has a finite free resolution if it has a finite free resolution of some
finite length. -/
abbrev HasFiniteFreeResolution (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M] :
    Prop :=
  (ModuleCat.finiteFree R).HasFiniteResolution (ModuleCat.of R M)

namespace HasFiniteFreeResolution

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem out [HasFiniteFreeResolution R M] : ∃ (n : ℕ), HasFiniteFreeResolutionOfLength R M n :=
  ObjectProperty.HasFiniteResolution.out (ModuleCat.finiteFree R) (ModuleCat.of R M)

instance of_finite_of_free [Module.Finite R M] [Module.Free R M] : HasFiniteFreeResolution R M :=
  ObjectProperty.HasFiniteResolution.of_property (ModuleCat.finiteFree_of R M)

scoped instance module_finite [HasFiniteFreeResolution R M] : Module.Finite R M :=
  (HasFiniteFreeResolution.out R M).choose_spec.module_finite

variable {R M}

theorem of_linearEquiv [Small.{w} R] {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [HasFiniteFreeResolution R M] : HasFiniteFreeResolution R N := by
  obtain ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  exact ⟨n, hn.of_linearEquiv e⟩

variable (R M)

instance [Small.{max w v} R] [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution R (ULift.{w} M) :=
  of_linearEquiv ULift.moduleEquiv.symm

theorem of_ulift [Small.{v} R] [Small.{max w v} R] [HasFiniteFreeResolution R (ULift.{w} M)] :
    HasFiniteFreeResolution R M :=
  of_linearEquiv ULift.moduleEquiv

instance [Small.{w} R] [Small.{w} M] [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution R (Shrink.{w} M) :=
  of_linearEquiv (Shrink.linearEquiv R M).symm

theorem of_shrink [Small.{v} R] [Small.{w, v} M] [HasFiniteFreeResolution R (Shrink.{w} M)] :
    HasFiniteFreeResolution R M :=
  of_linearEquiv (Shrink.linearEquiv R M)

end HasFiniteFreeResolution

end Module
