/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import QuillenSuslin.FiniteFreeResolution.Polynomial
import QuillenSuslin.StablyFree.HasFiniteFreeResolution

universe u v

/-- Every finitely generated projective module over $k[x_1, \dots, x_n]$, for any field $k$,
  is necessarily stably free. -/
theorem mvPolynomial_isStablyFree_of_isPrincipalIdealRing (R : Type u) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (σ : Type v) [Finite σ] (P : Type*) [AddCommGroup P]
    [Module (MvPolynomial σ R) P] [Module.Finite (MvPolynomial σ R) P]
    [Module.Projective (MvPolynomial σ R) P] : IsStablyFree (MvPolynomial σ R) P := by
  have e : (ULift.{max u v} P) ≃ₗ[MvPolynomial σ R] P := ULift.moduleEquiv
  have : Module.Projective (MvPolynomial σ R) (ULift P) := Module.Projective.of_equiv' e.symm
  refine IsStablyFree.equiv e <|
    (isStablyFree_iff_hasFiniteFreeResolution (MvPolynomial σ R) (ULift P)).2 <|
      mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing σ (fun Q _ _ hQ ↦ ?_) (ULift P)
  rcases Module.Finite.exists_fin' R Q with ⟨n, f, hf⟩
  obtain ⟨m, bK⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (LinearMap.ker f)
  have : Module.Free R (LinearMap.ker f) := Module.Free.of_basis bK
  have : Module.Finite R (LinearMap.ker f) := Module.Finite.of_basis bK
  exact hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution (LinearMap.ker f).subtype f
    Subtype.val_injective hf (LinearMap.exact_subtype_ker_map f)
      (hasFiniteFreeResolution_of_finite_of_free (LinearMap.ker f))
