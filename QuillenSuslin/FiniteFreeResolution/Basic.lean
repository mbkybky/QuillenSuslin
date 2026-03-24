/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Finiteness.Small

universe u v w

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
      (K : Type v) [AddCommGroup K] [Module R K] [Module.Finite R K]
      (f : K →ₗ[R] F) (g : F →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
      (he : Function.Exact f g) (hk : HasFiniteFreeResolutionOfLength R K n) :
      HasFiniteFreeResolutionOfLength R P (n + 1)

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) [CommRing R] [Small.{v} R]
    (P : Type v) [AddCommGroup P] [Module R P] : Prop :=
  ∃ (n : ℕ),  HasFiniteFreeResolutionOfLength R P n

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- A subsingleton finitely generated module has a finite free resolution. -/
theorem hasFiniteFreeResolution_of_subsingleton (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    HasFiniteFreeResolution R M :=
  ⟨0, HasFiniteFreeResolutionOfLength.zero M⟩

/-- A finitely generated free module has a finite free resolution of length `0`. -/
theorem hasFiniteFreeResolution_of_finite_of_free (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] :
    HasFiniteFreeResolution R M :=
  ⟨0, HasFiniteFreeResolutionOfLength.zero M⟩

variable [Small.{w} R]

theorem hasFiniteFreeResolutionOfLength_of_linearEquiv {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R P n) : HasFiniteFreeResolutionOfLength R Q n := by
  induction hn generalizing Q with
  | zero =>
      have : Module.Finite R Q := Module.Finite.equiv e
      have : Module.Free R Q := Module.Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero Q
  | succ P n F K f g hf hg he hk ih =>
      have : Small.{w} F := Module.Finite.small R F
      have : Small.{w} K := Module.Finite.small R K
      have eF : Shrink.{w} F ≃ₗ[R] F := Shrink.linearEquiv R F
      have eK : Shrink.{w} K ≃ₗ[R] K := Shrink.linearEquiv R K
      refine HasFiniteFreeResolutionOfLength.succ Q n (Shrink.{w} F) (Shrink.{w} K)
        (eF.symm ∘ₗ (f.comp eK.toLinearMap)) (e ∘ₗ (g.comp eF.toLinearMap)) ?_ ?_ ?_ (ih eK.symm)
      · exact eF.symm.injective.comp (hf.comp eK.injective)
      · exact e.surjective.comp (hg.comp eF.surjective)
      · exact (Function.Injective.comp_exact_iff_exact e.injective).2 <|
          (LinearEquiv.conj_exact_iff_exact (f.comp eK.toLinearMap) g eF.symm).2 <|
            (Function.Surjective.comp_exact_iff_exact eK.surjective).2 he

theorem hasFiniteFreeResolution_of_linearEquiv {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (hn : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases hn with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv e hn⟩

omit [Small.{w} R] in
theorem moduleFinite_of_hasFiniteFreeResolution {P : Type v} [AddCommGroup P] [Module R P]
    (hP : HasFiniteFreeResolution R P) : Module.Finite R P := by
  rcases hP with ⟨n, hn⟩
  induction hn with
  | zero => infer_instance
  | succ P n F K f g hf hg he hk ih => exact Module.Finite.of_surjective g hg

theorem hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution {P : Type v} {F : Type*} {K : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Module.Free R F] [AddCommGroup K] [Module R K] [Module.Finite R K]
    (i : K →ₗ[R] F) (s : F →ₗ[R] P) (hi : Function.Injective i)
    (hs : Function.Surjective s) (he : Function.Exact i s)
    (hk : HasFiniteFreeResolution R K) : HasFiniteFreeResolution R P := by
  have : Small.{v} F := Module.Finite.small.{v} R F
  have : Small.{v} K := Module.Finite.small.{v} R K
  have eF : Shrink.{v} F ≃ₗ[R] F := Shrink.linearEquiv R F
  have eK : Shrink.{v} K ≃ₗ[R] K := Shrink.linearEquiv R K
  rcases hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv R K).symm hk with ⟨n, hk⟩
  let i' : Shrink.{v} K →ₗ[R] Shrink.{v} F := eF.symm ∘ₗ (i.comp eK.toLinearMap)
  let s' : Shrink.{v} F →ₗ[R] P := s.comp eF.toLinearMap
  refine ⟨n + 1,  HasFiniteFreeResolutionOfLength.succ P n (Shrink.{v} F) (Shrink.{v} K) i' s'
    (eF.symm.injective.comp (hi.comp eK.injective)) (hs.comp eF.surjective) ?_ hk⟩
  exact (LinearEquiv.conj_exact_iff_exact (i.comp eK.toLinearMap) s eF.symm).2 <|
    (Function.Surjective.comp_exact_iff_exact eK.surjective).2 he
