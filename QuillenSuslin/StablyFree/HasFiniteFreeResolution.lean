/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import QuillenSuslin.StablyFree.Basic
import QuillenSuslin.FiniteFreeResolution.Exact

universe u v

namespace Module

variable {R : Type u} [CommRing R] [Small.{v, u} R]

theorem isStablyFree_of_projective_of_hasFiniteFreeResolutionLength  {P : Type v} [AddCommGroup P]
    [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n) :
    Module.Projective R P → Module.IsStablyFree R P := by
  induction hn with
  | zero P =>
      intro _
      exact ⟨Fin 0 → R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  | succ P n F K f g hf hg he hk ih =>
      intro _
      obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
      let e : F ≃ₗ[R] K × P := ((Function.Exact.splitSurjectiveEquiv he hf) ⟨l, hl⟩).1
      have : Module.Projective R (K × P) := Module.Projective.of_equiv e
      have hprojK : Module.Projective R K := Module.Projective.of_split
        (LinearMap.inl R K P) (LinearMap.fst R K P) (LinearMap.ext fun _ ↦ by simp)
      rcases ih hprojK with ⟨N, _, _, _, _, _⟩
      have : Module.Free R (K × P) := Module.Free.of_equiv e
      have : Module.Free R (P × (K × N)) := Module.Free.of_equiv <|
        (LinearEquiv.prodComm R K P).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
          LinearEquiv.prodAssoc R P K N
      have : Module.Finite R K := module_finite_of_hasFiniteFreeResolutionOfLength hk
      exact Module.IsStablyFree.of_free_prod R P (K × N)

variable (R)

/-- Let `M` be a finite projective module. Then `M` is stably free if `M` admits a
  finite free resolution. -/
instance isStablyFree_of_hasFiniteFreeResolution (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [HasFiniteFreeResolution R M] :
    Module.IsStablyFree R M := by
  obtain ⟨_, hn⟩ := HasFiniteFreeResolution.out R M
  exact isStablyFree_of_projective_of_hasFiniteFreeResolutionLength hn inferInstance

theorem isStablyFree_iff_hasFiniteFreeResolution
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.IsStablyFree R M ↔ HasFiniteFreeResolution R M := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ isStablyFree_of_hasFiniteFreeResolution R M⟩
  obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.out R M
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle (LinearMap.inr R M N)
    (LinearMap.fst R M N) LinearMap.inr_injective LinearMap.fst_surjective Function.Exact.inr_fst

end Module
