/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import QuillenSuslin.MainTheorem

public section

theorem subsingleton_pic_of_pid (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (σ : Type*) [Finite σ] : Subsingleton (CommRing.Pic (MvPolynomial σ R)) :=
  CommRing.Pic.subsingleton_iff.2 <| by
    intro M _ _ _
    exact Module.quillenSuslin R σ M
