/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.RingTheory.Flat.Basic
public import QuillenSuslin.FiniteFreeResolution.Basic

public section

universe u v w z

namespace Module

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] [Flat R A]
  {M : Type u} [AddCommGroup M] [Module R M]

open TensorProduct

/-- Extending scalars along a flat `R`-algebra preserves finite free resolutions. -/
theorem HasFiniteFreeResolutionOfLength.tensorProduct_of_flat {n : ℕ}
    (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength A (A ⊗[R] M) n := by
  induction hM with
  | zero M => exact HasFiniteFreeResolutionOfLength.zero (A ⊗[R] M)
  | succ _ _ _ _ f g hf hg he _ ih =>
      exact ih.succ' (AlgebraTensorModule.lTensor A A f) (AlgebraTensorModule.lTensor A A g)
        (Flat.lTensor_preserves_injective_linearMap f hf) (LinearMap.lTensor_surjective A hg)
          (Flat.lTensor_exact A he)

/-- Extending scalars along a flat `R`-algebra preserves finite free resolutions. -/
instance HasFiniteFreeResolution.of_flat_baseChange [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution A (A ⊗[R] M) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, hn.tensorProduct_of_flat⟩

end Module
