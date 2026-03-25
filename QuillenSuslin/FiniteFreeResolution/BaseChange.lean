/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import QuillenSuslin.FiniteFreeResolution.Basic

universe u v w z

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Module.Flat R A]
  {P : Type u} [AddCommGroup P] [Module R P]

open TensorProduct

/-- Extending scalars along a flat `R`-algebra preserves finite free resolutions. -/
theorem hasFiniteFreeResolutionOfLength_tensorProduct_of_flat {n : ℕ}
    (hP : HasFiniteFreeResolutionOfLength R P n) :
    HasFiniteFreeResolutionOfLength A (A ⊗[R] P) n := by
  induction hP with
  | zero P =>
      exact HasFiniteFreeResolutionOfLength.zero (A ⊗[R] P)
  | succ P n F K f g hf hg he hk ih =>
      refine HasFiniteFreeResolutionOfLength.succ (A ⊗[R] P) n
        (A ⊗[R] F) (A ⊗[R] K)
        (AlgebraTensorModule.lTensor A A f)
        (AlgebraTensorModule.lTensor A A g) ?_ ?_ ?_ ih
      · exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) f hf
      · exact (LinearMap.lTensor_surjective (Q := A) (g := g) hg)
      · exact Module.Flat.lTensor_exact (M := A) he

/-- Extending scalars along a flat `R`-algebra preserves finite free resolutions. -/
theorem hasFiniteFreeResolution_tensorProduct_of_flat (hP : HasFiniteFreeResolution R P) :
    HasFiniteFreeResolution A (A ⊗[R] P) := by
  rcases hP with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_tensorProduct_of_flat hn⟩

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (e : A ≃+* B)

noncomputable def compatLinearEquiv {M : Type z} [AddCommMonoid M] [Module A M] [Module B M]
    (hcompat : ∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) := by
  let : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
  show M ≃ₛₗ[(e : A →+* B)] M
  exact {
    toFun := id
    invFun := id
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' := by
      intro a x
      exact (hcompat a x).symm
  }

variable [Small.{z} A] [Small.{z} B]

theorem hasFiniteFreeResolutionOfLength_of_ringEquiv :
    ∀ {M : Type z} [AddCommGroup M] [Module A M] {n : ℕ},
      HasFiniteFreeResolutionOfLength A M n →
      ∀ [Module B M], (∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) →
        HasFiniteFreeResolutionOfLength B M n := by
  intro M _ _ n hn
  induction hn with
  | zero M =>
      intro _ hcompat
      let : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
      let : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
      let eM := compatLinearEquiv e hcompat
      have : Module.Finite B M := (LinearMap.finite_iff_of_bijective
        (eM : M →ₛₗ[(e : A →+* B)] M) eM.bijective).1 inferInstance
      have : Module.Free B M := Module.Free.of_equiv eM
      exact HasFiniteFreeResolutionOfLength.zero M
  | succ M n F K f g hf hg he hk ih =>
      intro _ hcompatM
      let : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
      let : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
      let : Module B F := Module.compHom F (e.symm : B →+* A)
      let : Module B K := Module.compHom K (e.symm : B →+* A)
      have hcompatF : ∀ (a : A) (x : F), (e a : B) • x = (a : A) • x := by
        intro a x
        change ((e.symm (e a) : A) • x) = a • x
        simp
      have hcompatK : ∀ (a : A) (x : K), (e a : B) • x = (a : A) • x := by
        intro a x
        change ((e.symm (e a) : A) • x) = a • x
        simp
      let eF := compatLinearEquiv e hcompatF
      let eK := compatLinearEquiv e hcompatK
      have : Module.Finite B F := (LinearMap.finite_iff_of_bijective
        (eF : F →ₛₗ[(e : A →+* B)] F) eF.bijective).1 inferInstance
      have : Module.Free B F := Module.Free.of_equiv eF
      have : Module.Finite B K := (LinearMap.finite_iff_of_bijective
        (eK : K →ₛₗ[(e : A →+* B)] K) eK.bijective).1 inferInstance
      let fB : K →ₗ[B] F :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := by
            intro b x
            exact f.map_smul (e.symm b) x }
      let gB : F →ₗ[B] M :=
        { toFun := g
          map_add' := g.map_add
          map_smul' := by
            intro b x
            change g ((e.symm b : A) • x) = b • g x
            rw [g.map_smul]
            simpa using (hcompatM (e.symm b) (g x)).symm }
      exact HasFiniteFreeResolutionOfLength.succ M n F K fB gB hf hg he (ih hcompatK)

theorem hasFiniteFreeResolution_of_ringEquiv :
    ∀ {M : Type z} [AddCommGroup M] [Module A M],
      HasFiniteFreeResolution A M →
      ∀ [Module B M], (∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) →
        HasFiniteFreeResolution B M := by
  intro M _ _ hM _ hcompat
  rcases hM with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_ringEquiv e hn hcompat⟩
