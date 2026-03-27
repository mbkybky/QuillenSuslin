/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.Finiteness.Prod
import QuillenSuslin.FiniteFreeResolution.Basic

universe u α β γ

variable {R : Type u} [CommRing R] [Small.{α} R] [Small.{β} R] [Small.{γ} R]
  {P₁ : Type α} {P₂ : Type β} {P₃ : Type γ} [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
  {F : Type γ} [AddCommGroup F] [Module R F] {K : Type γ} [AddCommGroup K] [Module R K]
  (f : P₁ →ₗ[R] P₂) (g : P₂ →ₗ[R] P₃) (f₃ : K →ₗ[R] F) (g₃ : F →ₗ[R] P₃)

private noncomputable def leftLiftOfRightLift (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) : K →ₗ[R] P₁ :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ (LinearMap.codRestrict f.range (l.comp f₃) <|
    fun k => (h (l (f₃ k))).1 <| by simpa [← hl] using Function.Exact.apply_apply_eq_zero he₃ k)

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R] in
private theorem leftLiftOfRightLift_apply (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) (k : K) :
    f (leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl k) = l (f₃ k) := by
  simp [leftLiftOfRightLift]

section

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R]

variable {A : Type*} {B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
   (u : A →ₗ[R] P₁) (v : B →ₗ[R] P₃) (l : B →ₗ[R] P₂)

private theorem surjective_coprod_of_exact_of_lift (h : Function.Exact f g)
    (hu : Function.Surjective u) (hv : Function.Surjective v) (hl : g.comp l = v) :
    Function.Surjective ((f.comp u).coprod l) := by
  intro z
  rcases hv (g z) with ⟨y, hy⟩
  obtain ⟨x₁, hx₁⟩ := (h (z - l y)).1 (by
    rw [LinearMap.map_sub]
    change g z - (g.comp l) y = 0
    rw [hl, hy]
    simp)
  rcases hu x₁ with ⟨x, hx⟩
  exact ⟨(x, y), by simp [hx, hx₁]⟩

private theorem coprod_snd_eq_zero_of_eq_zero (h : Function.Exact f g)
    (hl : g.comp l = v) (y : A × B) (hy : ((f.comp u).coprod l) y = 0) : v y.2 = 0 := by
  simpa [← hl, Function.Exact.apply_apply_eq_zero h (u y.1)] using congrArg g hy

end

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₁ : HasFiniteFreeResolution R P₁) (h₃ : HasFiniteFreeResolution R P₃) :
    HasFiniteFreeResolution R P₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  induction h₁ generalizing P₂ P₃ with
  | zero P₁ =>
      rcases h₃ with ⟨n₃, h₃⟩
      cases h₃ with
      | zero P₃ =>
          obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
          have : Small.{β} (P₁ × P₃) := Module.Finite.small.{β} R (P₁ × P₃)
          exact hasFiniteFreeResolution_of_linearEquiv
            ((Shrink.linearEquiv R (P₁ × P₃)).trans ((h.splitSurjectiveEquiv hf) ⟨s, hs⟩).1.symm)
              ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} (P₁ × P₃))⟩
      | succ P₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
          let t : K₃ →ₗ[R] P₁ := leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl
          let i : K₃ →ₗ[R] P₁ × F₃ := LinearMap.prod (- t) f₃
          let s : P₁ × F₃ →ₗ[R] P₂ := f.coprod l
          refine hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution i s ?_ ?_ ?_ ⟨n, hk₃⟩
          · intro x y hxy
            exact hf₃ (congrArg Prod.snd hxy)
          · exact surjective_coprod_of_exact_of_lift f g .id g₃ l h Function.surjective_id hg₃ hl
          · intro y
            constructor
            · intro hy
              have hy0 : g₃ y.2 = 0 := coprod_snd_eq_zero_of_eq_zero f g LinearMap.id g₃ l h hl y hy
              rcases (he₃ y.2).1 hy0 with ⟨k, hk⟩
              have hxy0 : y.1 + t k = 0 := hf <| by
                rw [LinearMap.map_add, leftLiftOfRightLift_apply]
                simpa [hk, s, add_comm] using hy
              exact ⟨k, Prod.ext (by simp [i, eq_neg_iff_add_eq_zero.mpr hxy0]) hk⟩
            · rintro ⟨k, rfl⟩
              simpa [i, s] using congrArg (fun z => - z + l (f₃ k))
                (leftLiftOfRightLift_apply f g f₃ g₃ hf h he₃ l hl k)
  | succ P₁ n F₁ K₁ f₁ g₁ hf₁ hg₁ he₁ hk₁ ih =>
      rcases h₃ with ⟨n₃, h₃⟩
      cases h₃ with
      | zero P₃ =>
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
          let i : K₁ →ₗ[R] F₁ × P₃ := (LinearMap.inl R F₁ P₃).comp f₁
          let s : F₁ × P₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          refine hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution i s ?_ ?_ ?_ ⟨n, hk₁⟩
          · intro x y hxy
            exact hf₁ (congrArg Prod.fst hxy)
          · exact surjective_coprod_of_exact_of_lift f g g₁ .id l h hg₁ Function.surjective_id hl
          · intro y
            constructor
            · intro hy
              have hy0 : y.2 = 0 := coprod_snd_eq_zero_of_eq_zero f g g₁ LinearMap.id l h hl y hy
              rcases (he₁ y.1).1 (hf <| by simpa [s, hy0] using hy) with ⟨x, hx⟩
              exact ⟨x, Prod.ext hx (by simp [hy0, i])⟩
            · rintro ⟨x, rfl⟩
              simpa [i, s] using congrArg f (Function.Exact.apply_apply_eq_zero he₁ x)
      | succ P₃ n₃ F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          have : Small.{β} (F₁ × F₃) := Module.Finite.small.{β} R (F₁ × F₃)
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
          let s : F₁ × F₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          let K : Submodule R (F₁ × F₃) := s.ker
          let i₁ : K₁ →ₗ[R] F₁ × F₃ := (LinearMap.inl R F₁ F₃).comp f₁
          let α : K₁ →ₗ[R] K := LinearMap.codRestrict K i₁ <| fun k ↦ by
            simp [K, s, i₁, Function.Exact.apply_apply_eq_zero he₁ k]
          let p : F₁ × F₃ →ₗ[R] F₃ := LinearMap.snd R F₁ F₃
          let β : K →ₗ[R] g₃.ker := LinearMap.codRestrict g₃.ker (p.comp K.subtype) <|
            fun x ↦ coprod_snd_eq_zero_of_eq_zero f g g₁ g₃ l h hl x.1 x.2
          have hα : Function.Injective α := fun _ _ hxy =>
            hf₁ <| congrArg Prod.fst (congrArg Subtype.val hxy)
          have hβ : Function.Surjective β := by
            intro y
            have hy0 : g₃ (y : F₃) = 0 := y.2
            obtain ⟨x₁, hx₁⟩ := (h (l (y : F₃))).1 (by
              change (g.comp l) (y : F₃) = 0
              rwa [hl])
            rcases hg₁ (- x₁) with ⟨x, hx⟩
            exact ⟨⟨(x, (y : F₃)), by simp [K, s, hx, hx₁]⟩, Subtype.ext (by simp [β, p])⟩
          have hKer : Function.Exact α β := by
            refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
            · ext k
              simp [β, p, α, i₁]
            · intro x hx
              have hx2 : x.1.2 = 0 := congrArg Subtype.val hx
              have hx1mem : (x.1.1 : F₁) ∈ f₁.range := by
                have hlx : l x.1.2 = 0 := by simp [hx2]
                have hxg1 : g₁ x.1.1 = 0 := hf <| by
                  simpa [hlx] using (eq_neg_of_add_eq_zero_left x.2 : f (g₁ x.1.1) = -l x.1.2)
                simpa [Function.Exact.linearMap_ker_eq he₁] using
                  (show (x.1.1 : F₁) ∈ g₁.ker from hxg1)
              rcases hx1mem with ⟨k, hk⟩
              exact ⟨k, by ext <;> simp [α, i₁, hx2, hk]⟩
          have hK₃ : HasFiniteFreeResolution R g₃.ker :=
            hasFiniteFreeResolution_of_linearEquiv (LinearEquiv.ofInjective f₃ hf₃ ≪≫ₗ
              (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm) ⟨n₃, hk₃⟩
          have eK : Shrink.{β} K ≃ₗ[R] K := Shrink.linearEquiv R K
          have : Small.{max α γ, u} R := small_lift R
          refine hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution K.subtype s
            (Submodule.subtype_injective K)
              (surjective_coprod_of_exact_of_lift f g g₁ g₃ l h hg₁ hg₃ hl)
                (LinearMap.exact_subtype_ker_map s) <|
                  hasFiniteFreeResolution_of_linearEquiv eK <|
                    ih _ _ (eK.symm.injective.comp hα) (hβ.comp eK.surjective)
                      ((LinearEquiv.conj_exact_iff_exact α β eK.symm).2 hKer) hK₃

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₁ : HasFiniteFreeResolution R P₁) (h₂ : HasFiniteFreeResolution R P₂) :
    HasFiniteFreeResolution R P₃ := by
  rcases h₂ with ⟨n₂, h₂⟩
  cases h₂ with
  | zero P₂ => exact hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution f g hf hg h h₁
  | succ P₂ n F₂ K₂ f₂ g₂ hf₂ hg₂ he₂ hk₂ =>
      let s : F₂ →ₗ[R] P₃ := g.comp g₂
      let L : Submodule R F₂ := s.ker
      let α : K₂ →ₗ[R] L := LinearMap.codRestrict L f₂ <| fun x ↦ by
        simp [L, s, Function.Exact.apply_apply_eq_zero he₂ x]
      let e : P₁ ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
      have hRange (x : L) : g₂ x.1 ∈ f.range := (h (g₂ x.1)).1 x.2
      let β : L →ₗ[R] P₁ := e.symm ∘ₗ LinearMap.codRestrict f.range (g₂.comp L.subtype) hRange
      have hα : Function.Injective α := fun _ _ hxy => hf₂ (congrArg Subtype.val hxy)
      have hβ : Function.Surjective β := by
        intro y
        rcases hg₂ (f y) with ⟨x, hx⟩
        have hxL : x ∈ L := by simpa [L, s, hx] using Function.Exact.apply_apply_eq_zero h y
        exact ⟨⟨x, hxL⟩, hf <| by simp [β, e, hx]⟩
      have hExact : Function.Exact α β := by
        refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
        · ext k
          exact hf <| by simpa [β, e, α] using Function.Exact.apply_apply_eq_zero he₂ k
        · intro x hx
          rcases (he₂ x.1).1 (by simpa [β, e] using congrArg f hx) with ⟨k, hk⟩
          exact ⟨k, Subtype.ext hk⟩
      refine hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution
        L.subtype s (Submodule.subtype_injective _) ?_ (LinearMap.exact_subtype_ker_map s) ?_
      · simpa [s] using hg.comp hg₂
      · exact hasFiniteFreeResolution_of_shortExact_of_left_of_right α β hα hβ hExact ⟨n, hk₂⟩ h₁

private theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right
    [Module.Finite R P₃] [Module.Free R P₃]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₁ := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : P₂ ≃ₗ[R] P₁ × P₃ := ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1
  have : Module.Finite R P₂ := module_finite_of_hasFiniteFreeResolution h₂
  have : Module.Finite R (P₁ × P₃) := Module.Finite.equiv e
  have : Small.{β} (P₁ × P₃) := Module.Finite.small.{β} R (P₁ × P₃)
  let e' : Shrink.{β} (P₁ × P₃) ≃ₗ[R] (P₁ × P₃) := Shrink.linearEquiv R (P₁ × P₃)
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle
    (e'.symm.toLinearMap ∘ₗ LinearMap.inr R P₁ P₃) (LinearMap.fst R P₁ P₃ ∘ₗ e'.toLinearMap)
      (e'.symm.injective.comp LinearMap.inr_injective)
        ((LinearMap.fst_surjective (R := R)).comp e'.surjective)
          ((LinearEquiv.conj_exact_iff_exact _ _ e'.symm).2 Function.Exact.inr_fst)
            ⟨0, HasFiniteFreeResolutionOfLength.zero P₃⟩
              (hasFiniteFreeResolution_of_linearEquiv (e.trans e'.symm) h₂)

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₂ : HasFiniteFreeResolution R P₂) (h₃ : HasFiniteFreeResolution R P₃) :
    HasFiniteFreeResolution R P₁ := by
  have : Module.Finite R P₂ := module_finite_of_hasFiniteFreeResolution h₂
  rcases h₃ with ⟨n₃, h₃⟩
  cases h₃ with
  | zero P₃ => exact hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right f g hf hg h h₂
  | succ P₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
      let s : P₂ × F₃ →ₗ[R] P₃ := g.coprod (- g₃)
      let Q : Submodule R (P₂ × F₃) := s.ker
      let i₁ : K₃ →ₗ[R] P₂ × F₃ := (LinearMap.inr R P₂ F₃).comp f₃
      let α₁ : K₃ →ₗ[R] Q := LinearMap.codRestrict Q i₁ <| fun x ↦ by
        simp [Q, s, i₁, Function.Exact.apply_apply_eq_zero he₃ x]
      let β₁ : Q →ₗ[R] P₂ := (LinearMap.fst R P₂ F₃).comp Q.subtype
      have hα₁ : Function.Injective α₁ := fun _ _ hxy =>
        hf₃ (congrArg Prod.snd (congrArg Subtype.val hxy))
      have hβ₁ : Function.Surjective β₁ := by
        intro y
        rcases hg₃ (g y) with ⟨z, hz⟩
        refine ⟨⟨(y, z), by simp [Q, s, hz]⟩, by simp [β₁]⟩
      have hExact₁ : Function.Exact α₁ β₁ := by
        refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
        · ext x
          simp [α₁, β₁, i₁]
        · intro y hy
          have hy₁ : y.1.1 = 0 := by simpa [β₁] using hy
          have hy0 : g y.1.1 + (-g₃) y.1.2 = 0 := y.2
          have hy₂ : g₃ y.1.2 = 0 := by simpa [hy₁] using hy0
          rcases (he₃ y.1.2).1 hy₂ with ⟨x, hx⟩
          exact ⟨x, by ext <;> simp [α₁, i₁, hy₁, hx]⟩
      have : Module.Finite R K₃ := module_finite_of_hasFiniteFreeResolutionOfLength hk₃
      have : Module.Finite R Q := Module.Finite.of_exact hExact₁ hβ₁
      have : Small.{γ} Q := Module.Finite.small.{γ} R Q
      let eQ : Shrink.{γ} Q ≃ₗ[R] Q := Shrink.linearEquiv R Q
      let i₂ : P₁ →ₗ[R] P₂ × F₃ := (LinearMap.inl R P₂ F₃).comp f
      let α₂ : P₁ →ₗ[R] Q := LinearMap.codRestrict Q i₂ <| fun x ↦ by
        simp [Q, s, i₂, Function.Exact.apply_apply_eq_zero h x]
      let β₂ : Q →ₗ[R] F₃ := (LinearMap.snd R P₂ F₃).comp Q.subtype
      have hα₂ : Function.Injective α₂ := fun _ _ hxy =>
        hf (congrArg Prod.fst (congrArg Subtype.val hxy))
      have hβ₂ : Function.Surjective β₂ := by
        intro z
        rcases hg (g₃ z) with ⟨y, hy⟩
        refine ⟨⟨(y, z), by simp [Q, s, hy]⟩, by simp [β₂]⟩
      have hExact₂ : Function.Exact α₂ β₂ := by
        refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
        · ext x
          simp [α₂, β₂, i₂]
        · intro y hy
          have hy₂ : y.1.2 = 0 := by simpa [β₂] using hy
          have hy₁ : g y.1.1 = 0 := by
            have hy0 : g y.1.1 + (-g₃) y.1.2 = 0 := y.2
            rwa [hy₂, LinearMap.map_zero, add_zero] at hy0
          rcases (h y.1.1).1 hy₁ with ⟨x, hx⟩
          exact ⟨x, by ext <;> simp [α₂, i₂, hy₂, hx]⟩
      exact hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right
        (eQ.symm.toLinearMap ∘ₗ α₂) _ (eQ.symm.injective.comp hα₂) (hβ₂.comp eQ.surjective)
          ((LinearEquiv.conj_exact_iff_exact α₂ β₂ eQ.symm).2 hExact₂) <|
            hasFiniteFreeResolution_of_shortExact_of_left_of_right
              (eQ.symm.toLinearMap ∘ₗ α₁) _ (eQ.symm.injective.comp hα₁) (hβ₁.comp eQ.surjective)
                ((LinearEquiv.conj_exact_iff_exact α₁ β₁ eQ.symm).2 hExact₁) ⟨n, hk₃⟩ h₂
