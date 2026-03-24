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
    {P : Type v} [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n) :
    Module.Projective R P → IsStablyFree R P := by
  induction hn with
  | zero P =>
      intro _
      exact ⟨(Fin 0 → R), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  | succ P n F K f g hf hg hExact hk ih =>
      intro hPproj
      have hg' : g.range = ⊤ := LinearMap.range_eq_top.mpr hg
      obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective g hg'
      have hexact : Function.Exact (LinearMap.ker g).subtype g :=
        LinearMap.exact_subtype_ker_map g
      set eSigma := hexact.splitSurjectiveEquiv Subtype.coe_injective ⟨l, hl⟩ with heSigma
      set e : F ≃ₗ[R] LinearMap.ker g × P := eSigma.1 with hE
      have hkerProjProd : Module.Projective R (LinearMap.ker g × P) := Module.Projective.of_equiv e
      letI : Module.Projective R (LinearMap.ker g × P) := hkerProjProd
      have hkerProj : Module.Projective R (LinearMap.ker g) :=
        Module.Projective.of_split (LinearMap.inl R (LinearMap.ker g) P)
          (LinearMap.fst R (LinearMap.ker g) P) (LinearMap.ext fun _ ↦ by simp)
      letI : Module.Projective R (LinearMap.ker g) := hkerProj
      let eK : K ≃ₗ[R] LinearMap.ker g :=
        LinearEquiv.ofInjective f hf ≪≫ₗ (LinearEquiv.ofEq g.ker f.range hExact.linearMap_ker_eq).symm
      have hKproj : Module.Projective R K := Module.Projective.of_equiv eK.symm
      have hK : IsStablyFree R K := ih hKproj
      rcases hK with ⟨N, hNAdd, hNMod, hNFin, hNFree, hKNFree⟩
      letI : AddCommGroup N := hNAdd
      letI : Module R N := hNMod
      letI : Module.Finite R N := hNFin
      letI : Module.Free R N := hNFree
      have hKfin : Module.Finite R K := moduleFinite_of_hasFiniteFreeResolution ⟨n, hk⟩
      letI : Module.Finite R (LinearMap.ker g) := Module.Finite.equiv eK
      have hkerNFree : Module.Free R (LinearMap.ker g × N) := by
        let eKN : (K × N) ≃ₗ[R] (LinearMap.ker g × N) := eK.prodCongr (LinearEquiv.refl R N)
        exact Module.Free.of_equiv eKN
      refine ⟨LinearMap.ker g × N, inferInstance, inferInstance, inferInstance, hkerNFree, ?_⟩
      have : Module.Free R (LinearMap.ker g × P) := Module.Free.of_equiv e
      -- Rearrange `(ker f × P) × N` as `P × (ker f × N)`.
      let e' : ((LinearMap.ker g × P) × N) ≃ₗ[R] (P × (LinearMap.ker g × N)) :=
        (LinearEquiv.prodComm R (LinearMap.ker g) P).prodCongr (LinearEquiv.refl R N) ≪≫ₗ
          LinearEquiv.prodAssoc R P (LinearMap.ker g) N
      exact Module.Free.of_equiv e'

variable (R)

/-- Let $M$ be a projective module. Then $M$ is stably free if and only if $M$ admits a
  finite free resolution. -/
theorem stably_free_iff (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] : IsStablyFree R M ↔ HasFiniteFreeResolution R M := by
  constructor
  · intro h
    rcases h with ⟨N, _, _, _, _, _⟩
    have h₁ : HasFiniteFreeResolution R N := hasFiniteFreeResolution_of_finite_free N
    have h₂ : HasFiniteFreeResolution R (M × N) := hasFiniteFreeResolution_of_finite_free (M × N)
    exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle
      (LinearMap.inr R M N) (LinearMap.fst R M N)
        LinearMap.inr_injective LinearMap.fst_surjective Function.Exact.inr_fst h₁ h₂
  · intro h
    have hSmall : Small.{u} M := Module.Finite.small.{u} R M
    let eM : Shrink.{u} M ≃ₗ[R] M := Shrink.linearEquiv R M
    rcases hasFiniteFreeResolution_of_linearEquiv eM.symm h with ⟨n, hn⟩
    obtain ⟨N, hNAdd, hNMod, hNFin, hNFree, _⟩ :=
      isStablyFree_of_projective_of_hasFiniteFreeResolutionLength hn <|
        Module.Projective.of_equiv eM.symm
    refine ⟨N, hNAdd, hNMod, hNFin, hNFree, ?_⟩
    exact Module.Free.of_equiv (eM.prodCongr (LinearEquiv.refl R N))
