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
  | zero P => exact HasFiniteFreeResolutionOfLength.zero (A ⊗[R] P)
  | succ P n F K f g hf hg he hk ih =>
      refine HasFiniteFreeResolutionOfLength.succ (A ⊗[R] P) n
        (A ⊗[R] F) (A ⊗[R] K)
        (AlgebraTensorModule.lTensor A A f)
        (AlgebraTensorModule.lTensor A A g) ?_ ?_ ?_ ih
      · exact Module.Flat.lTensor_preserves_injective_linearMap (M := A) f hf
      · exact (LinearMap.lTensor_surjective (Q := A) (g := g) hg)
      · exact Module.Flat.lTensor_exact (M := A) he

/-- Extending scalars along a flat `R`-algebra preserves finite free resolutions. -/
instance hasFiniteFreeResolution_tensorProduct_of_flat [HasFiniteFreeResolution R P] :
    HasFiniteFreeResolution A (A ⊗[R] P) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R P
  ⟨n, hasFiniteFreeResolutionOfLength_tensorProduct_of_flat hn⟩
