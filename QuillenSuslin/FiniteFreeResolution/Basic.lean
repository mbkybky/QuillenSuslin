/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.PicardGroup

universe u v α β γ

/-- `HasFiniteFreeResolutionOfLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionOfLength (R : Type u) [CommRing R] [Small.{v} R] :
    ∀ (P : Type v), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P] :
      HasFiniteFreeResolutionOfLength R P 0
  | succ (P : Type v) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      (K : Type v) [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Free R K]
      {f : K →ₗ[R] F} (hf : Function.Injective f) {g : F →ₗ[R] P} (hg : Function.Surjective g)
      (he : Function.Exact f g) (hk : HasFiniteFreeResolutionOfLength R K n) :
      HasFiniteFreeResolutionOfLength R P (n + 1)

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) [CommRing R] [Small.{v} R]
    (P : Type v) [AddCommGroup P] [Module R P] : Prop :=
  ∃ (n : ℕ),  HasFiniteFreeResolutionOfLength R P n

variable {R : Type u} [CommRing R] [Small.{α} R] [Small.{β} R] [Small.{γ} R]

omit [Small.{γ, u} R] in
theorem hasFiniteFreeResolutionOfLength_of_linearEquiv {P : Type α} {Q : Type β}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R P n) : HasFiniteFreeResolutionOfLength R Q n := by
  let motive :
      ∀ (P : Type α), [AddCommGroup P] → [Module R P] → (n : ℕ) →
        HasFiniteFreeResolutionOfLength R P n → Prop :=
      fun P _ _ n _ =>
        ∀ {Q : Type β}, [AddCommGroup Q] → [Module R Q] → (P ≃ₗ[R] Q) →
          HasFiniteFreeResolutionOfLength R Q n
  exact HasFiniteFreeResolutionOfLength.rec (motive := motive)
    (zero := by
      intro P _ _ _ _ Q _ _ e
      letI : Module.Finite R Q := Module.Finite.of_surjective (e : P →ₗ[R] Q) e.surjective
      letI : Module.Free R Q := Module.Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero Q)
    (succ := by
      intro P _ _ n F _ _ _ _ K _ _ _ _ f hf g hg he hk ih Q _ _ e
      letI : Small.{β} F := @Module.Finite.small.{β, u, α} R F _ _ _ _ _
      letI : Small.{β} K := @Module.Finite.small.{β, u, α} R K _ _ _ _ _
      let eF : F ≃ₗ[R] Shrink.{β} F :=
        (equivShrink.{β} F).toLinearEquiv
          { map_add := fun x y => equivShrink_add x y
            map_smul := fun r x => equivShrink_smul r x }
      let eK : K ≃ₗ[R] Shrink.{β} K :=
        (equivShrink.{β} K).toLinearEquiv
          { map_add := fun x y => equivShrink_add x y
            map_smul := fun r x => equivShrink_smul r x }
      letI : Module.Finite R (Shrink.{β} F) :=
        Module.Finite.of_surjective (eF : F →ₗ[R] Shrink.{β} F) eF.surjective
      letI : Module.Free R (Shrink.{β} F) := Module.Free.of_equiv eF
      letI : Module.Finite R (Shrink.{β} K) :=
        Module.Finite.of_surjective (eK : K →ₗ[R] Shrink.{β} K) eK.surjective
      letI : Module.Free R (Shrink.{β} K) := Module.Free.of_equiv eK
      let f' : Shrink.{β} K →ₗ[R] Shrink.{β} F := (eF.toLinearMap.comp f).comp eK.symm.toLinearMap
      let g' : Shrink.{β} F →ₗ[R] Q := e.toLinearMap.comp (g.comp eF.symm.toLinearMap)
      have hf' : Function.Injective f' := by
        dsimp [f']
        exact eF.injective.comp (hf.comp eK.symm.injective)
      have hg' : Function.Surjective g' := by
        dsimp [g']
        exact e.surjective.comp (hg.comp eF.symm.surjective)
      have he' : Function.Exact f' g' := by
        dsimp [f', g']
        have h1 : Function.Exact (eF.toLinearMap.comp f) (g.comp eF.symm.toLinearMap) := by
          exact (LinearEquiv.conj_exact_iff_exact f g eF).2 he
        have h2 :
            Function.Exact ((eF.toLinearMap.comp f).comp eK.symm.toLinearMap)
              (g.comp eF.symm.toLinearMap) := by
          exact (Function.Surjective.comp_exact_iff_exact
            (p := eK.symm.toLinearMap) eK.symm.surjective).2 h1
        exact (Function.Injective.comp_exact_iff_exact (i := e.toLinearMap) e.injective).2 h2
      have hk' : HasFiniteFreeResolutionOfLength R (Shrink.{β} K) n := ih eK
      exact @HasFiniteFreeResolutionOfLength.succ _ _ _ Q _ _ n
        (Shrink.{β} F) _ _ _ _ (Shrink.{β} K) _ _ _ _ f' hf' g' hg' he' hk')
    hn e

omit [Small.{γ} R] in
theorem hasFiniteFreeResolution_of_linearEquiv {P : Type α} {Q : Type β}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (hn : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases hn with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv e hn⟩

section exact_seq

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right (P₁ : Type α) (P₂ : Type β)
    (P₃ : Type γ) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃]
    [Module R P₃] {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₂ := sorry

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle (P₁ : Type α) (P₂ : Type β)
    (P₃ : Type γ) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃]
    [Module R P₃] {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₃ := sorry

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right (P₁ : Type α) (P₂ : Type β)
    (P₃ : Type γ) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃]
    [Module R P₃] {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₂ : HasFiniteFreeResolution R P₂)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₁ := sorry

end exact_seq
