/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Finiteness.Small

universe u u' v v' w

namespace Module

variable (R : Type u) [CommRing R] [Small.{v} R]

/-- `HasFiniteFreeResolutionOfLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionOfLength (R : Type u) [CommRing R] [Small.{v} R] :
    ∀ (P : Type v), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Free R P] :
      HasFiniteFreeResolutionOfLength R P 0
  | succ (P : Type v) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Free R F]
      (K : Type v) [AddCommGroup K] [Module R K] [Module.Finite R K]
      (f : K →ₗ[R] F) (g : F →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
      (he : Function.Exact f g) (hk : HasFiniteFreeResolutionOfLength R K n) :
      HasFiniteFreeResolutionOfLength R P (n + 1)

namespace HasFiniteFreeResolutionOfLength

variable {R} {P : Type v} [AddCommGroup P] [Module R P] {n : ℕ}

theorem module_finite (hP : HasFiniteFreeResolutionOfLength R P n) : Module.Finite R P := by
  cases hP with
  | zero => infer_instance
  | succ _ _ _ _ _ g _ hg _ _ => exact Module.Finite.of_surjective g hg

theorem succ_of_hasFiniteFreeResolutionOfLength (hP : HasFiniteFreeResolutionOfLength R P n) :
    HasFiniteFreeResolutionOfLength R P (n + 1) := by
  induction hP with
  | zero P =>
      exact (HasFiniteFreeResolutionOfLength.zero PUnit).succ P 0 P PUnit 0 LinearMap.id
        (Function.injective_of_subsingleton _) (fun x ↦ ⟨x, rfl⟩)
          (Function.Exact.of_comp_of_mem_range rfl (fun _ hy ↦ ⟨0, hy.symm⟩))
  | succ P n F K f g hf hg he _ ih => exact ih.succ P (n + 1) F K f g hf hg he

theorem of_ge {m : ℕ} (hP : HasFiniteFreeResolutionOfLength R P n) (h : n ≤ m) :
    HasFiniteFreeResolutionOfLength R P m :=
  Nat.le.rec hP (fun _ ↦ succ_of_hasFiniteFreeResolutionOfLength) h

section compHom

variable {R S M N : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (σ' : S →+* R)
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/- Let `M` be a `R`-module. Viewing `M` as an `S`-module via `σ' : S →+* R`, then the identity map
gives a semilinear equivalence over `σ: R →+* S`. -/
variable (M) in
def _root_.Module.compHom.self_equiv : let : Module S M := compHom M σ'
    M ≃ₛₗ[σ] M :=
  let : Module S M := compHom M σ'
{ __ := AddEquiv.refl M
  map_smul' a x : a • x = (σ' (σ a)) • x := by simp }

end compHom

/-- A semilinear equivalence over mutually inverse ring homomorphisms preserves finite free
resolutions. -/
theorem of_semilinearEquiv {S : Type u'} [CommRing S] [Small.{v'} S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {P : Type v} [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n)
    {Q : Type v'} [AddCommGroup Q] [Module S Q] (e : P ≃ₛₗ[σ] Q) :
    HasFiniteFreeResolutionOfLength S Q n := by
  induction hn generalizing Q with
  | zero _ =>
      have : Module.Finite S Q := Module.Finite.of_surjective e.toLinearMap e.surjective
      have : Free S Q := Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero Q
  | succ _ n F K f g hf hg he hk ih =>
      let : Module S F := compHom F σ'
      let : Module S K := compHom K σ'
      let eF : F ≃ₛₗ[σ] F := compHom.self_equiv F σ σ'
      let eK : K ≃ₛₗ[σ] K := compHom.self_equiv K σ σ'
      let fS : K →ₗ[S] F := (eF.toLinearMap ∘ₛₗ f) ∘ₛₗ eK.symm.toLinearMap
      let gS : F →ₗ[S] Q := (e.toLinearMap ∘ₛₗ g) ∘ₛₗ eF.symm.toLinearMap
      have : Free S F := Free.of_equiv eF
      have : Module.Finite S F := Module.Finite.of_surjective eF.toLinearMap eF.surjective
      have : Module.Finite S K := Module.Finite.of_surjective eK.toLinearMap eK.surjective
      have : Small.{v'} F := Module.Finite.small S F
      have : Small.{v'} K := Module.Finite.small S K
      have eFv : Shrink.{v'} F ≃ₗ[S] F := Shrink.linearEquiv S F
      have eKv : Shrink.{v'} K ≃ₗ[S] K := Shrink.linearEquiv S K
      refine (ih (eK.trans eKv.symm)).succ Q n (Shrink.{v'} F) (Shrink.{v'} K)
        (eFv.symm ∘ₗ fS ∘ₗ eKv) (gS ∘ₗ eFv) ?_ ((e.surjective.comp hg).comp eFv.surjective) ?_
      · exact eFv.symm.injective.comp (hf.comp eKv.injective)
      · exact (LinearEquiv.conj_exact_iff_exact (fS ∘ₗ eKv.toLinearMap) gS eFv.symm).2 <|
          fun x ↦ by simpa [gS, fS] using he (eF.symm x)

variable [Small.{w} R]

theorem of_linearEquiv {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (e : P ≃ₗ[R] Q) {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n) :
    HasFiniteFreeResolutionOfLength R Q n :=
  hn.of_semilinearEquiv e

theorem succ' {P : Type v} {F : Type*} {K : Type w} [AddCommGroup P] [Module R P] [AddCommGroup F]
    [Module R F] [Module.Finite R F] [Free R F] [AddCommGroup K] [Module R K]
    (f : K →ₗ[R] F) (g : F →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g) {n : ℕ}
    (hk : HasFiniteFreeResolutionOfLength R K n) : HasFiniteFreeResolutionOfLength R P (n + 1) := by
  have : Module.Finite R K := hk.module_finite
  have : Small.{v} F := Module.Finite.small.{v} R F
  have : Small.{v} K := Module.Finite.small.{v} R K
  have eF : Shrink.{v} F ≃ₗ[R] F := Shrink.linearEquiv R F
  have eK : Shrink.{v} K ≃ₗ[R] K := Shrink.linearEquiv R K
  let fv : Shrink.{v} K →ₗ[R] Shrink.{v} F := eF.symm ∘ₗ (f ∘ₗ eK.toLinearMap)
  exact (hk.of_linearEquiv eK.symm).succ P n (Shrink.{v} F) (Shrink.{v} K) fv (g ∘ₗ eF.toLinearMap)
    (eF.symm.injective.comp (hf.comp eK.injective)) (hg.comp eF.surjective) <|
      (LinearEquiv.conj_symm_exact_iff_exact (f ∘ₗ eK.toLinearMap) g eF).2 <|
        (Function.Surjective.comp_exact_iff_exact eK.surjective).2 he

end HasFiniteFreeResolutionOfLength

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
class HasFiniteFreeResolution (R : Type u) [CommRing R] [Small.{v} R]
    (P : Type v) [AddCommGroup P] [Module R P] : Prop where
  out (R P) : ∃ (n : ℕ),  HasFiniteFreeResolutionOfLength R P n

namespace HasFiniteFreeResolution

/-- A finitely generated free module has a finite free resolution of length `0`. -/
instance of_finite_of_free (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Free R M] : HasFiniteFreeResolution R M :=
  ⟨0, HasFiniteFreeResolutionOfLength.zero M⟩

instance (priority := low) module_finite (P : Type v) [AddCommGroup P] [Module R P]
    [HasFiniteFreeResolution R P] : Module.Finite R P :=
  (HasFiniteFreeResolution.out R P).choose_spec.module_finite

/-- A semilinear equivalence over mutually inverse ring homomorphisms preserves finite free
resolutions. -/
theorem of_semilinearEquiv (S : Type u') [CommRing S] [Small.{v'} S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (P : Type v) [AddCommGroup P] [Module R P] [HasFiniteFreeResolution R P]
    (Q : Type v') [AddCommGroup Q] [Module S Q] (e : P ≃ₛₗ[σ] Q) :
    HasFiniteFreeResolution S Q :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R P
  ⟨n, hn.of_semilinearEquiv e⟩

variable {R} [Small.{w} R]

theorem of_linearEquiv {P : Type v} {Q : Type w} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (e : P ≃ₗ[R] Q) [HasFiniteFreeResolution R P] : HasFiniteFreeResolution R Q :=
  of_semilinearEquiv R R P Q e

theorem of_ker_hasFiniteFreeResolution {P : Type v} {F : Type*} {K : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Free R F] [AddCommGroup K] [Module R K] (f : K →ₗ[R] F) (g : F →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    [HasFiniteFreeResolution R K] : HasFiniteFreeResolution R P :=
  let ⟨n, hk⟩ := HasFiniteFreeResolution.out R K
  ⟨n + 1, hk.succ' f g hf hg he⟩

end HasFiniteFreeResolution

end Module
