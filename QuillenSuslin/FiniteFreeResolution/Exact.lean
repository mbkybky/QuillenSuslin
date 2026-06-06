/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import QuillenSuslin.FiniteFreeResolution.Basic

/-!
# The short exact sequences of modules admitting finite free resolutions

This file proves that in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if any two of these modules
have a finite free resolution, then so does the third .
-/

public section

universe u α β γ

variable {R : Type u} [CommRing R] [Small.{α} R] [Small.{β} R] [Small.{γ} R]
  {M₁ : Type α} {M₂ : Type β} {M₃ : Type γ} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  {F : Type γ} [AddCommGroup F] [Module R F] {K : Type γ} [AddCommGroup K] [Module R K]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)

section Function.Exact

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R]

variable {A : Type*} {B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
   (u : A →ₗ[R] M₁) (v : B →ₗ[R] M₃) (l : B →ₗ[R] M₂)

private theorem surjective_coprod_of_exact_lift (h : Function.Exact f g)
    (hu : Function.Surjective u) (hv : Function.Surjective v) (hl : g.comp l = v) :
    Function.Surjective ((f.comp u).coprod l) := by
  intro z
  rcases hv (g z) with ⟨y, hy⟩
  obtain ⟨x₁, hx₁⟩ := (h (z - l y)).1 <| by
    rw [LinearMap.map_sub]
    change g z - (g.comp l) y = 0
    simp [hl, hy]
  rcases hu x₁ with ⟨x, hx⟩
  exact ⟨(x, y), by simp [hx, hx₁]⟩

private theorem snd_mem_ker_of_mem_ker_coprod (h : Function.Exact f g)
    (hl : g.comp l = v) (y : A × B) (hy : ((f.comp u).coprod l) y = 0) : v y.2 = 0 := by
  simpa [← hl, h.apply_apply_eq_zero (u y.1)] using congrArg g hy

end Function.Exact

namespace Module.HasFiniteFreeResolution

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₁` and `M₃` have finite free
resolutions, then so does `M₂`. -/
theorem of_shortExact_of_left_of_right (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₁] [HasFiniteFreeResolution R M₃] :
    HasFiniteFreeResolution R M₂ := by
  have : Small.{max α γ, u} R := small_lift R
  obtain ⟨n₁, h₁⟩ := HasFiniteFreeResolution.out R M₁
  induction h₁ generalizing M₂ M₃ with
  | zero M₁ =>
      obtain ⟨n₃, h₃⟩ := HasFiniteFreeResolution.out R M₃
      cases h₃ with
      | zero M₃ =>
          obtain ⟨s, hs⟩ := projective_lifting_property g LinearMap.id hg
          let e : M₂ ≃ₗ[R] M₁ × M₃ := ((h.splitSurjectiveEquiv hf) ⟨s, hs⟩).1
          exact of_linearEquiv e.symm
      | succ M₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          obtain ⟨l, hl⟩ := projective_lifting_property g g₃ hg
          let t : K₃ →ₗ[R] M₁ := LinearMap.codRestrictOfInjective (l.comp f₃) f hf <| fun k ↦
            (h _).1 <| show (g.comp l) _ = 0 from hl.symm ▸ he₃.apply_apply_eq_zero k
          let i : K₃ →ₗ[R] M₁ × F₃ := LinearMap.prod (- t) f₃
          let s : M₁ × F₃ →ₗ[R] M₂ := f.coprod l
          have : HasFiniteFreeResolution R K₃ := ⟨n, hk₃⟩
          refine of_ker_hasFiniteFreeResolution i s ?_ ?_ ?_
          · exact fun _ _ hxy ↦ hf₃ (congrArg Prod.snd hxy)
          · exact surjective_coprod_of_exact_lift f g .id g₃ l h Function.surjective_id hg₃ hl
          · refine LinearMap.exact_of_comp_of_mem_range ?_ ?_
            · exact LinearMap.ext fun k ↦ by simp [i, s, t]
            · intro y hy
              rcases (he₃ y.2).1
                  (snd_mem_ker_of_mem_ker_coprod f g LinearMap.id g₃ l h hl y hy) with ⟨k, hk⟩
              have hxy0 : y.1 + t k = 0 := hf <| by
                simpa [LinearMap.map_add, t, hk, s, add_comm] using hy
              exact ⟨k, Prod.ext (by simp [i, eq_neg_iff_add_eq_zero.mpr hxy0]) hk⟩
  | succ M₁ n F₁ K₁ f₁ g₁ hf₁ hg₁ he₁ hk₁ ih =>
      obtain ⟨n₃, h₃⟩ := HasFiniteFreeResolution.out R M₃
      cases h₃ with
      | zero M₃ =>
          obtain ⟨l, hl⟩ := projective_lifting_property g LinearMap.id hg
          let i : K₁ →ₗ[R] F₁ × M₃ := (LinearMap.inl R F₁ M₃).comp f₁
          let s : F₁ × M₃ →ₗ[R] M₂ := (f.comp g₁).coprod l
          have : HasFiniteFreeResolution R K₁ := ⟨n, hk₁⟩
          refine of_ker_hasFiniteFreeResolution i s ?_ ?_ ?_
          · exact fun x y hxy ↦ hf₁ (congrArg Prod.fst hxy)
          · exact surjective_coprod_of_exact_lift f g g₁ .id l h hg₁ Function.surjective_id hl
          · refine LinearMap.exact_of_comp_of_mem_range ?_ ?_
            · exact LinearMap.ext fun x ↦ by simp [i, s, he₁.apply_apply_eq_zero x]
            · intro y hy
              have hy0 : y.2 = 0 := snd_mem_ker_of_mem_ker_coprod f g g₁ LinearMap.id l h hl y hy
              rcases (he₁ y.1).1 (hf <| by simpa [s, hy0] using hy) with ⟨x, hx⟩
              exact ⟨x, Prod.ext hx (by simp [hy0, i])⟩
      | succ M₃ n₃ F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          have : Small.{β} (F₁ × F₃) := Module.Finite.small.{β} R (F₁ × F₃)
          obtain ⟨l, hl⟩ := projective_lifting_property g g₃ hg
          let s : F₁ × F₃ →ₗ[R] M₂ := (f.comp g₁).coprod l
          let K : Submodule R (F₁ × F₃) := s.ker
          let i₁ : K₁ →ₗ[R] F₁ × F₃ := (LinearMap.inl R F₁ F₃).comp f₁
          let ϕ : K₁ →ₗ[R] K := LinearMap.codRestrict K i₁ <| fun k ↦ by
            simp [K, s, i₁, he₁.apply_apply_eq_zero k]
          let p : F₁ × F₃ →ₗ[R] F₃ := LinearMap.snd R F₁ F₃
          let ψ : K →ₗ[R] g₃.ker := LinearMap.codRestrict g₃.ker (p.comp K.subtype) <|
            fun x ↦ snd_mem_ker_of_mem_ker_coprod f g g₁ g₃ l h hl x.1 x.2
          have hϕ : Function.Injective ϕ := fun _ _ hxy ↦ hf₁ <|
            congrArg Prod.fst (congrArg Subtype.val hxy)
          have hψ : Function.Surjective ψ := by
            intro y
            obtain ⟨x₁, hx₁⟩ := (h (l (y : F₃))).1 (hl.symm ▸ y.2)
            rcases hg₁ (- x₁) with ⟨x, hx⟩
            exact ⟨⟨(x, (y : F₃)), by simp [K, s, hx, hx₁]⟩, Subtype.ext (by simp [ψ, p])⟩
          have hKer : Function.Exact ϕ ψ := by
            refine LinearMap.exact_of_comp_of_mem_range ?_ ?_
            · exact LinearMap.ext fun k ↦ Subtype.ext <| by simp [ψ, p, ϕ, i₁]
            · intro x hx
              have hx2 : x.1.2 = 0 := congrArg Subtype.val hx
              have hlx : l x.1.2 = 0 := by simp [hx2]
              have hxg1 : g₁ x.1.1 = 0 := hf <| by
                simpa [hlx] using (eq_neg_of_add_eq_zero_left x.2 : f (g₁ x.1.1) = -l x.1.2)
              rcases (he₁ x.1.1).1 hxg1 with ⟨k, hk⟩
              exact ⟨k, by ext <;> simp [ϕ, i₁, hx2, hk]⟩
          have : HasFiniteFreeResolution R K₃ := ⟨n₃, hk₃⟩
          have hK₃ : HasFiniteFreeResolution R g₃.ker :=
            of_linearEquiv (LinearEquiv.ofInjective f₃ hf₃ ≪≫ₗ
              (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm)
          let +nondep eK : Shrink.{β} K ≃ₗ[R] K := Shrink.linearEquiv R K
          have : HasFiniteFreeResolution R (Shrink.{β} K) :=
            ih _ _ (eK.symm.injective.comp hϕ) (hψ.comp eK.surjective)
              ((LinearEquiv.conj_exact_iff_exact ϕ ψ eK.symm).2 hKer)
          have : HasFiniteFreeResolution R K := of_shrink.{β} R K
          exact of_ker_hasFiniteFreeResolution K.subtype s (Submodule.subtype_injective K)
            (surjective_coprod_of_exact_lift f g g₁ g₃ l h hg₁ hg₃ hl)
              (LinearMap.exact_subtype_ker_map s)

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₁` and `M₂` have finite free
resolutions, then so does `M₃`. -/
theorem of_shortExact_of_left_of_middle (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₁] [HasFiniteFreeResolution R M₂] :
    HasFiniteFreeResolution R M₃ := by
  obtain ⟨n₂, h₂⟩ := HasFiniteFreeResolution.out R M₂
  cases h₂ with
  | zero M₂ => exact of_ker_hasFiniteFreeResolution f g hf hg h
  | succ M₂ n F₂ K₂ f₂ g₂ hf₂ hg₂ he₂ hk₂ =>
      let s : F₂ →ₗ[R] M₃ := g.comp g₂
      let L : Submodule R F₂ := s.ker
      let ϕ : K₂ →ₗ[R] L := LinearMap.codRestrict L f₂ <| fun x ↦ by
        simp [L, s, he₂.apply_apply_eq_zero x]
      let e : M₁ ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
      have hRange (x : L) : g₂ x.1 ∈ f.range := (h (g₂ x.1)).1 x.2
      let ψ : L →ₗ[R] M₁ := e.symm ∘ₗ LinearMap.codRestrict f.range (g₂.comp L.subtype) hRange
      have hϕ : Function.Injective ϕ := fun _ _ hxy ↦ hf₂ (congrArg Subtype.val hxy)
      have hψ : Function.Surjective ψ := by
        intro y
        rcases hg₂ (f y) with ⟨x, hx⟩
        exact ⟨⟨x, by simpa [L, s, hx] using h.apply_apply_eq_zero y⟩,
          hf <| by simp [ψ, e, hx]⟩
      have hExact : Function.Exact ϕ ψ := by
        refine LinearMap.exact_of_comp_of_mem_range ?_ ?_
        · exact LinearMap.ext fun k ↦ hf <| by simpa [ψ, e, ϕ] using he₂.apply_apply_eq_zero k
        · intro x hx
          rcases (he₂ x.1).1 (by simpa [ψ, e] using congrArg f hx) with ⟨k, hk⟩
          exact ⟨k, Subtype.ext hk⟩
      have : HasFiniteFreeResolution R K₂ := ⟨n, hk₂⟩
      have : HasFiniteFreeResolution R L := of_shortExact_of_left_of_right ϕ ψ hϕ hψ hExact
      exact of_ker_hasFiniteFreeResolution L.subtype s
        (Submodule.subtype_injective _) (hg.comp hg₂) (LinearMap.exact_subtype_ker_map s)

private theorem of_split [Module.Finite R M₃] [Free R M₃]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    [HasFiniteFreeResolution R M₂] : HasFiniteFreeResolution R M₁ := by
  obtain ⟨s, hs⟩ := projective_lifting_property g LinearMap.id hg
  let e : M₂ ≃ₗ[R] M₁ × M₃ := ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1
  have : Small.{max α γ, u} R := small_lift R
  have : HasFiniteFreeResolution R (M₁ × M₃) := of_linearEquiv e
  exact of_shortExact_of_left_of_middle (LinearMap.inr R M₁ M₃) (LinearMap.fst R M₁ M₃)
    LinearMap.inr_injective LinearMap.fst_surjective Function.Exact.inr_fst

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, if `M₂` and `M₃` have finite free
resolutions, then so does `M₁`. -/
theorem of_shortExact_of_middle_of_right (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) [HasFiniteFreeResolution R M₂] [HasFiniteFreeResolution R M₃] :
    HasFiniteFreeResolution R M₁ := by
  obtain ⟨n₃, h₃⟩ := HasFiniteFreeResolution.out R M₃
  cases h₃ with
  | zero M₃ =>
      obtain ⟨s, hs⟩ := projective_lifting_property g LinearMap.id hg
      let e : M₂ ≃ₗ[R] M₁ × M₃ := ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1
      have : Small.{max α γ, u} R := small_lift R
      have : HasFiniteFreeResolution R (M₁ × M₃) := of_linearEquiv e
      exact of_shortExact_of_left_of_middle (LinearMap.inr R M₁ M₃) (LinearMap.fst R M₁ M₃)
        LinearMap.inr_injective LinearMap.fst_surjective Function.Exact.inr_fst
  | succ M₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
      let s : M₂ × F₃ →ₗ[R] M₃ := g.coprod (- g₃)
      let N : Submodule R (M₂ × F₃) := s.ker
      let i₁ : K₃ →ₗ[R] M₂ × F₃ := (LinearMap.inr R M₂ F₃).comp f₃
      let ϕ₁ : K₃ →ₗ[R] N := LinearMap.codRestrict N i₁ <| fun x ↦ by
        simp [N, s, i₁, he₃.apply_apply_eq_zero x]
      let ψ₁ : N →ₗ[R] M₂ := (LinearMap.fst R M₂ F₃).comp N.subtype
      have hϕ₁ : Function.Injective ϕ₁ := fun _ _ hxy ↦
        hf₃ (congrArg Prod.snd (congrArg Subtype.val hxy))
      have hψ₁ : Function.Surjective ψ₁ := by
        intro y
        rcases hg₃ (g y) with ⟨z, hz⟩
        exact ⟨⟨(y, z), by simp [N, s, hz]⟩, by simp [ψ₁]⟩
      have hExact₁ : Function.Exact ϕ₁ ψ₁ := by
        refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
        · exact LinearMap.ext fun _ ↦ by simp [ϕ₁, ψ₁, i₁]
        · intro y hy
          have hy₁ : y.1.1 = 0 := hy
          have hy₂ : g₃ y.1.2 = 0 := by simpa [hy₁] using show g y.1.1 + (-g₃) y.1.2 = 0 from y.2
          rcases (he₃ y.1.2).1 hy₂ with ⟨x, hx⟩
          exact ⟨x, by ext <;> simp [ϕ₁, i₁, hy₁, hx]⟩
      have : Small.{max β γ, u} R := small_lift R
      let i₂ : M₁ →ₗ[R] M₂ × F₃ := (LinearMap.inl R M₂ F₃).comp f
      let ϕ₂ : M₁ →ₗ[R] N := LinearMap.codRestrict N i₂ <| fun x ↦ by
        simp [N, s, i₂, h.apply_apply_eq_zero x]
      let ψ₂ : N →ₗ[R] F₃ := (LinearMap.snd R M₂ F₃).comp N.subtype
      have hϕ₂ : Function.Injective ϕ₂ := fun _ _ hxy ↦
        hf (congrArg Prod.fst (congrArg Subtype.val hxy))
      have hψ₂ : Function.Surjective ψ₂ := by
        intro z
        rcases hg (g₃ z) with ⟨y, hy⟩
        refine ⟨⟨(y, z), by simp [N, s, hy]⟩, by simp [ψ₂]⟩
      have : HasFiniteFreeResolution R K₃ := ⟨n, hk₃⟩
      have : HasFiniteFreeResolution R N := of_shortExact_of_left_of_right ϕ₁ ψ₁ hϕ₁ hψ₁ hExact₁
      exact of_split ϕ₂ ψ₂ hϕ₂ hψ₂ <| by
        refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
        · exact LinearMap.ext fun _ ↦ by simp [ϕ₂, ψ₂, i₂]
        · intro y hy
          have hy₂ : y.1.2 = 0 := hy
          have hy₁ : g y.1.1 = 0 := by
            simpa [hy₂] using show g y.1.1 + (-g₃) y.1.2 = 0 from y.2
          rcases (h y.1.1).1 hy₁ with ⟨x, hx⟩
          exact ⟨x, by ext <;> simp [ϕ₂, i₂, hy₂, hx]⟩

end Module.HasFiniteFreeResolution
