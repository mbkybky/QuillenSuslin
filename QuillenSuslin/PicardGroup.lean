/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import QuillenSuslin.MainTheorem

open Module Polynomial Finset BigOperators Bivariate

variable (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (σ : Type*) [Fintype σ]

theorem subsingleton_pic_of_pid : Subsingleton (CommRing.Pic (MvPolynomial σ R)) := by
  sorry
