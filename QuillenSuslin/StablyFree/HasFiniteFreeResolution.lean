/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import QuillenSuslin.StablyFree.Basic
import QuillenSuslin.FiniteFreeResolution.Exact

universe u v w

variable {R : Type u} [CommRing R] [Small.{v, u} R]

open Polynomial Module

theorem isStablyFree_of_projective_of_hasFiniteFreeResolutionLength
    {P : Type u} [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n) :
    Module.Projective R P → IsStablyFree R P := by
  induction hn with
  | zero P =>
      intro _
      exact ⟨(Fin 0 → R), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  | succ P n F f hf hk ih =>
      intro hPproj
      have hf' : f.range = ⊤ := LinearMap.range_eq_top.2 hf
      obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective f hf'
      have hexact : Function.Exact (LinearMap.ker f).subtype f :=
        LinearMap.exact_subtype_ker_map f
      set eSigma := hexact.splitSurjectiveEquiv Subtype.coe_injective ⟨l, hl⟩ with heSigma
      set e : F ≃ₗ[R] LinearMap.ker f × P := eSigma.1 with he
      have : Module.Projective R (LinearMap.ker f × P) := Module.Projective.of_equiv e
      have : Module.Projective R (LinearMap.ker f) :=
        Module.Projective.of_split (LinearMap.inl R (LinearMap.ker f) P)
          (LinearMap.fst R (LinearMap.ker f) P) (LinearMap.ext fun _ ↦ by simp)
      have hK : IsStablyFree R (LinearMap.ker f) := ih inferInstance
      rcases hK with ⟨N, _, _, _, _, _⟩
      have : Module.Finite R (LinearMap.ker f) := module_finite_of_hasFiniteFreeResolutionLength hk
      refine ⟨LinearMap.ker f × N, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      have : Module.Free R (LinearMap.ker f × P) := Module.Free.of_equiv e
      -- Rearrange `(ker f × P) × N` as `P × (ker f × N)`.
      let e' : ((LinearMap.ker f × P) × N) ≃ₗ[R] (P × (LinearMap.ker f × N)) :=
        (LinearEquiv.prodComm R (LinearMap.ker f) P).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
          LinearEquiv.prodAssoc R P (LinearMap.ker f) N
      exact Module.Free.of_equiv e'

variable (R)

/-- Let $M$ be a projective module. Then $M$ is stably free if and only if $M$ admits a
  finite free resolution. -/
theorem stably_free_iff (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : IsStablyFree R M ↔ HasFiniteFreeResolution R M := by
  constructor
  · intro h
    rcases h with ⟨N, _, _, _, _, hMNfree⟩
    have h₁ : HasFiniteFreeResolution R N := hasFiniteFreeResolution_of_finite_of_free N
    have h₂ : HasFiniteFreeResolution R (M × N) :=
      hasFiniteFreeResolution_of_finite_of_free (M × N)
    have hf : Function.Injective (LinearMap.inr R M N) := by
      intro x y hxy
      simpa using congrArg Prod.snd hxy
    have hg : Function.Surjective (LinearMap.fst R M N) := by
      intro x
      exact ⟨(x, 0), rfl⟩
    have hexact : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) :=
      (LinearMap.exact_iff).2 (by simpa using LinearMap.ker_fst R M N)
    exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle N (M × N) M hf hg hexact h₁ h₂
  · intro h
    rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
    have hf' : f.range = ⊤ := LinearMap.range_eq_top.2 hf
    obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective f hf'
    have hexact : Function.Exact (LinearMap.ker f).subtype f :=
      LinearMap.exact_subtype_ker_map f
    set eSigma := hexact.splitSurjectiveEquiv Subtype.coe_injective ⟨l, hl⟩ with heSigma
    set e : F ≃ₗ[R] LinearMap.ker f × M := eSigma.1 with he
    have : Module.Projective R (LinearMap.ker f × M) := Module.Projective.of_equiv e
    have : Module.Projective R (LinearMap.ker f) :=
      Module.Projective.of_split (LinearMap.inl R (LinearMap.ker f) M)
        (LinearMap.fst R (LinearMap.ker f) M) (LinearMap.ext fun _ ↦ by simp)
    have hK : IsStablyFree R (LinearMap.ker f) :=
      isStablyFree_of_projective_of_hasFiniteFreeResolutionLength hn inferInstance
    rcases hK with ⟨N, _, _, _, _, _⟩
    have : Module.Finite R (LinearMap.ker f) := module_finite_of_hasFiniteFreeResolutionLength hn
    refine ⟨(LinearMap.ker f × N), inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    have : Module.Free R (LinearMap.ker f × M) := Module.Free.of_equiv e
    let e' : ((LinearMap.ker f × M) × N) ≃ₗ[R] (M × (LinearMap.ker f × N)) :=
      (LinearEquiv.prodComm R (LinearMap.ker f) M).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
        LinearEquiv.prodAssoc R M (LinearMap.ker f) N
    exact Module.Free.of_equiv e'
