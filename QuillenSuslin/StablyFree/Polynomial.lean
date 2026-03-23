/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import QuillenSuslin.StablyFree.HasFiniteFreeResolution

variable (R : Type u) [CommRing R]

/-- Every finitely generated projective module over $k[x_1, \dots, x_n]$, for any field $k$,
  is necessarily stably free. -/
theorem mvPolynomial_isStablyFree_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    (s : Type w) [Finite s] (P : Type v) [AddCommGroup P] [Module (MvPolynomial s R) P]
    [Module.Finite (MvPolynomial s R) P] [Module.Projective (MvPolynomial s R) P] :
    IsStablyFree (MvPolynomial s R) P := by
  refine (stably_free_iff (MvPolynomial s R) P).2 <|
    mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing s ?_ P
  intro Q _ _ hQ
  rcases Module.Finite.exists_fin' R Q with ⟨n, f, hf⟩
  obtain ⟨m, bK⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (LinearMap.ker f)
  have : Module.Free R (LinearMap.ker f) := Module.Free.of_basis bK
  have : Module.Finite R (LinearMap.ker f) := Module.Finite.of_basis bK
  refine ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance, f, hf, 0, ?_⟩
  simpa using (HasFiniteFreeResolutionLength.zero (LinearMap.ker f))
