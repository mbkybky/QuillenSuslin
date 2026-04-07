/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.Finiteness
import QuillenSuslin.FiniteFreeResolution.Basic

universe u v

namespace Module

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
  (S : Submonoid R)

theorem localizedModule_hasFiniteFreeResolutionLength
    {n : ℕ} (h : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength (Localization S) (LocalizedModule S M) n := by
  induction h with
  | zero P =>
      have : Free (Localization S) (LocalizedModule S P) :=
        free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S P)
      exact HasFiniteFreeResolutionOfLength.zero (LocalizedModule S P)
  | succ P n F K f g hf hg he hk ih =>
      have : Free (Localization S) (LocalizedModule S F) :=
        free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S F)
      exact HasFiniteFreeResolutionOfLength.succ (LocalizedModule S P) n _ _ _ _
        (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
          (LocalizedModule.map_exact S f g he) ih

instance localizedModule_hasFiniteFreeResolution [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) :=
  let ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  ⟨n, localizedModule_hasFiniteFreeResolutionLength S hn⟩

end Module
