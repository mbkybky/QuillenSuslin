/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.PicardGroup

universe u v α β γ

/-- `HasFiniteFreeResolutionOfLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionOfLength (R : Type u) [CommRing R] [Small.{v} R] :
    ∀ (P : Type v), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P] :
      HasFiniteFreeResolutionOfLength R P 0
  | succ (P : Type v) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      (K : Type v) [AddCommGroup K] [Module R K] [Module.Finite R K]
      (f : K →ₗ[R] F) (g : F →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
      (he : Function.Exact f g) (hk : HasFiniteFreeResolutionOfLength R K n) :
      HasFiniteFreeResolutionOfLength R P (n + 1)

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) [CommRing R] [Small.{v} R]
    (P : Type v) [AddCommGroup P] [Module R P] : Prop :=
  ∃ (n : ℕ),  HasFiniteFreeResolutionOfLength R P n

variable {R : Type u} [CommRing R] [Small.{α} R] [Small.{β} R] [Small.{γ} R]

omit [Small.{γ} R] in
theorem hasFiniteFreeResolutionOfLength_of_linearEquiv {P : Type α} {Q : Type β}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R P n) : HasFiniteFreeResolutionOfLength R Q n := by
  induction hn generalizing Q with
  | zero =>
      have : Module.Finite R Q := Module.Finite.equiv e
      have : Module.Free R Q := Module.Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero Q
  | succ P n F K f g hf hg he hk ih =>
      have : Small.{β} F := Module.Finite.small R F
      have : Small.{β} K := Module.Finite.small R K
      have eF : F ≃ₗ[R] Shrink.{β} F := (Shrink.linearEquiv R F).symm
      have eK : K ≃ₗ[R] Shrink.{β} K := (Shrink.linearEquiv R K).symm
      refine HasFiniteFreeResolutionOfLength.succ Q n (Shrink.{β} F) (Shrink.{β} K)
        (eF ∘ₗ (f.comp eK.symm.toLinearMap))
        (e ∘ₗ (g.comp eF.symm.toLinearMap)) ?_ ?_ ?_ ?_
      · intro x y hxy
        exact eK.symm.injective <| hf <| eF.injective <| by simpa [LinearMap.comp_apply] using hxy
      · intro q
        rcases hg (e.symm q) with ⟨x, hx⟩
        exact ⟨eF x, by simp [LinearMap.comp_apply, hx]⟩
      · intro y
        constructor
        · intro hy
          have h0 : g (eF.symm y) = 0 := e.injective <| by simpa [LinearMap.comp_apply] using hy
          rcases (he (eF.symm y)).1 h0 with ⟨x, hx⟩
          exact ⟨eK x, by simp [LinearMap.comp_apply, hx]⟩
        · rintro ⟨x, rfl⟩
          simp [LinearMap.comp_apply, (he (f (eK.symm x))).2 ⟨eK.symm x, rfl⟩]
      · exact ih eK

omit [Small.{γ} R] in
theorem hasFiniteFreeResolution_of_linearEquiv {P : Type α} {Q : Type β}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (hn : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases hn with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv e hn⟩

section exact_seq

variable {P₁ : Type α} {P₂ : Type β} {P₃ : Type γ} [AddCommGroup P₁] [Module R P₁]
  [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
  {F : Type γ} [AddCommGroup F] [Module R F] {K : Type γ} [AddCommGroup K] [Module R K]
  (f : P₁ →ₗ[R] P₂) (g : P₂ →ₗ[R] P₃) (f₃ : K →ₗ[R] F) (g₃ : F →ₗ[R] P₃)

omit [Small.{α} R] [Small.{γ} R] in
private theorem hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution
    {P : Type β} {F : Type*} {K : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Module.Free R F] [Small.{β} F] [AddCommGroup K] [Module R K] [Module.Finite R K]
    [Small.{β} K] (i : K →ₗ[R] F) (s : F →ₗ[R] P) (hi : Function.Injective i)
    (hs : Function.Surjective s) (he : Function.Exact i s)
    (hk : HasFiniteFreeResolution R (Shrink.{β} K)) : HasFiniteFreeResolution R P := by
  let eF : F ≃ₗ[R] Shrink.{β} F := (Shrink.linearEquiv R F).symm
  let eK : K ≃ₗ[R] Shrink.{β} K := (Shrink.linearEquiv R K).symm
  rcases hk with ⟨n, hk⟩
  let i' : Shrink.{β} K →ₗ[R] Shrink.{β} F := eF ∘ₗ (i.comp eK.symm.toLinearMap)
  let s' : Shrink.{β} F →ₗ[R] P := s.comp eF.symm.toLinearMap
  refine ⟨n + 1,
      HasFiniteFreeResolutionOfLength.succ P n (Shrink.{β} F) (Shrink.{β} K) i' s' ?_ ?_ ?_ hk⟩
  · intro x y hxy
    exact eK.symm.injective <| hi <| eF.injective <| by simpa [i', LinearMap.comp_apply] using hxy
  · intro p
    rcases hs p with ⟨x, rfl⟩
    exact ⟨eF x, by simp [s', LinearMap.comp_apply]⟩
  · intro y
    constructor
    · intro hy
      rcases (he (eF.symm y)).1 <| by simpa [s', LinearMap.comp_apply] using hy with ⟨x, hx⟩
      exact ⟨eK x, by simp [i', LinearMap.comp_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      simpa [i', s', LinearMap.comp_apply] using (he (i (eK.symm x))).2 ⟨eK.symm x, rfl⟩

private noncomputable def leftLiftOfRightLift (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) : K →ₗ[R] P₁ :=
  (LinearEquiv.ofInjective f hf).symm ∘ₗ (LinearMap.codRestrict f.range (l.comp f₃) <|
    fun k => (h (l (f₃ k))).1 <| by simpa [← hl] using Function.Exact.apply_apply_eq_zero he₃ k)

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R] in
private theorem leftLiftOfRightLift_apply (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) (k : K) :
    f (leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl k) = l (f₃ k) := by
  simp [leftLiftOfRightLift, LinearMap.comp_apply]

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right
    (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₂ := by
  rcases h₁ with ⟨n₁, h₁⟩
  rcases h₃ with ⟨n₃, h₃⟩
  cases h₁ with
  | zero P₁ =>
      cases h₃ with
      | zero P₃ =>
          obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
          have : Small.{β} (P₁ × P₃) := Module.Finite.small.{β} R (P₁ × P₃)
          have hprod : HasFiniteFreeResolution R (Shrink.{β} (P₁ × P₃)) :=
            ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} (P₁ × P₃))⟩
          exact hasFiniteFreeResolution_of_linearEquiv ((Shrink.linearEquiv R (P₁ × P₃)).trans
            ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1.symm) hprod
      | succ P₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          have : Small.{β} K₃ := Module.Finite.small.{β} R K₃
          have : Small.{β} (P₁ × F₃) := Module.Finite.small.{β} R (P₁ × F₃)
          have hk₃' : HasFiniteFreeResolution R (Shrink.{β} K₃) :=
            ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} K₃)⟩
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
          let t : K₃ →ₗ[R] P₁ := leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl
          let i : K₃ →ₗ[R] P₁ × F₃ := LinearMap.prod (- t) f₃
          let s : P₁ × F₃ →ₗ[R] P₂ := f.coprod l
          refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution i s ?_ ?_ ?_ hk₃'
          · intro x y hxy
            exact hf₃ <| by simpa [i, LinearMap.prod_apply] using congrArg Prod.snd hxy
          · intro z
            rcases hg₃ (g z) with ⟨y, hy⟩
            have hz0 : g (z - l y) = 0 := by
              rw [LinearMap.map_sub]
              change g z - (g.comp l) y = 0
              rw [hl, hy]
              simp
            rcases (h (z - l y)).1 hz0 with ⟨x, hx⟩
            exact ⟨(x, y), by simp [s, LinearMap.coprod_apply, hx]⟩
          · intro y
            constructor
            · intro hy
              have hfg0 : g (f y.1) = 0 := (h (f y.1)).2 ⟨y.1, rfl⟩
              have hy0' : g (l y.2) = 0 := by
                simpa [s, LinearMap.coprod_apply, hfg0] using congrArg g hy
              have hy0 : g₃ y.2 = 0 := by
                change (g.comp l) y.2 = 0 at hy0'
                rw [hl] at hy0'
                exact hy0'
              rcases (he₃ y.2).1 hy0 with ⟨k, hk⟩
              have hsum : f (t k + y.1) = 0 := by
                rw [LinearMap.map_add, leftLiftOfRightLift_apply]
                simpa [hk, s, LinearMap.coprod_apply, add_comm, add_left_comm, add_assoc] using hy
              have hsum' : f (y.1 + t k) = 0 := by
                simpa [add_comm] using hsum
              have hxy0 : y.1 + t k = 0 := hf <| by simpa using hsum'
              have hx : y.1 = - t k := by simpa using (eq_neg_iff_add_eq_zero.mpr hxy0)
              refine ⟨k, ?_⟩
              apply Prod.ext
              · simp [i, LinearMap.prod_apply, hx]
              · simpa [i, LinearMap.prod_apply] using hk
            · rintro ⟨k, rfl⟩
              have ht : f (t k) = l (f₃ k) := leftLiftOfRightLift_apply f g f₃ g₃ hf h he₃ l hl k
              have : f (- t k) + l (f₃ k) = 0 := by simp [ht]
              simpa [i, s, LinearMap.prod_apply, LinearMap.coprod_apply] using this
  | succ P₁ n F₁ K₁ f₁ g₁ hf₁ hg₁ he₁ hk₁ =>
      cases h₃ with
      | zero P₃ =>
          have : Small.{β} K₁ := Module.Finite.small.{β} R K₁
          have : Small.{β} (F₁ × P₃) := Module.Finite.small.{β} R (F₁ × P₃)
          have hk₁' : HasFiniteFreeResolution R (Shrink.{β} K₁) :=
            ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} K₁)⟩
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
          let i : K₁ →ₗ[R] F₁ × P₃ := (LinearMap.inl R F₁ P₃).comp f₁
          let s : F₁ × P₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution i s ?_ ?_ ?_ hk₁'
          · intro x y hxy
            exact hf₁ <| by simpa [i, LinearMap.comp_apply] using congrArg Prod.fst hxy
          · intro z
            have hz0 : g (z - l (g z)) = 0 := by
              rw [LinearMap.map_sub]
              change g z - (g.comp l) (g z) = 0
              rw [hl]
              simp
            rcases (h (z - l (g z))).1 hz0 with ⟨x₁, hx₁⟩
            rcases hg₁ x₁ with ⟨x, hx⟩
            exact ⟨(x, g z), by simp [s, hx, hx₁]⟩
          · intro y
            constructor
            · intro hy
              have hfg0 : g (f (g₁ y.1)) = 0 := (h (f (g₁ y.1))).2 ⟨g₁ y.1, rfl⟩
              have hy0' : g (l y.2) = 0 := by
                simpa [s, LinearMap.coprod_apply, hfg0] using congrArg g hy
              have hy0 : y.2 = 0 := by
                change (g.comp l) y.2 = 0 at hy0'
                rw [hl] at hy0'
                simpa using hy0'
              have hx0 : g₁ y.1 = 0 := by
                apply hf
                simpa [s, LinearMap.coprod_apply, hy0] using hy
              rcases (he₁ y.1).1 hx0 with ⟨x, hx⟩
              exact ⟨x, Prod.ext (by simpa [i, LinearMap.comp_apply] using hx)
                (by simp [hy0, i, LinearMap.comp_apply])⟩
            · rintro ⟨x, rfl⟩
              have hx0 : g₁ (f₁ x) = 0 := (he₁ (f₁ x)).2 ⟨x, rfl⟩
              have : f (g₁ (f₁ x)) + l 0 = 0 := by simp [hx0]
              simpa [i, s, hl, LinearMap.comp_apply, LinearMap.coprod_apply] using this
      | succ P₃ n₃ F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          have : Small.{β} K₁ := Module.Finite.small.{β} R K₁
          have : Small.{β} K₃ := Module.Finite.small.{β} R K₃
          have : Small.{β} (F₁ × F₃) := Module.Finite.small.{β} R (F₁ × F₃)
          have hk' : HasFiniteFreeResolution R (Shrink.{β} (K₁ × K₃)) :=
            ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} (K₁ × K₃))⟩
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
          let t : K₃ →ₗ[R] P₁ := leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl
          obtain ⟨τ, hτ⟩ := Module.projective_lifting_property g₁ (- t) hg₁
          let i : K₁ × K₃ →ₗ[R] F₁ × F₃ :=
            { toFun := fun x => (f₁ x.1 + τ x.2, f₃ x.2)
              map_add' := by
                intro x y
                ext <;> simp [add_assoc, add_left_comm, add_comm]
              map_smul' := by
                intro a x
                ext <;> simp }
          let s : F₁ × F₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution i s ?_ ?_ ?_ hk'
          · intro x y hxy
            have hk : x.2 = y.2 := hf₃ (by simpa [i] using congrArg Prod.snd hxy)
            have h1 : f₁ x.1 + τ x.2 = f₁ y.1 + τ y.2 := by simpa [i] using congrArg Prod.fst hxy
            have hx : x.1 = y.1 := hf₁ (by simpa [hk] using h1)
            exact Prod.ext hx hk
          · intro z
            rcases hg₃ (g z) with ⟨y, hy⟩
            have hz0 : g (z - l y) = 0 := by
              rw [LinearMap.map_sub]
              change g z - (g.comp l) y = 0
              rw [hl, hy]
              simp
            rcases (h (z - l y)).1 hz0 with ⟨x₁, hx₁⟩
            rcases hg₁ x₁ with ⟨x, hx⟩
            exact ⟨(x, y), by simp [s, hx, hx₁]⟩
          · intro y
            constructor
            · intro hy
              have hfg0 : g (f (g₁ y.1)) = 0 := (h (f (g₁ y.1))).2 ⟨g₁ y.1, rfl⟩
              have hy0' : g (l y.2) = 0 := by
                simpa [s, LinearMap.coprod_apply, hfg0] using congrArg g hy
              have hy0 : g₃ y.2 = 0 := by
                change (g.comp l) y.2 = 0 at hy0'
                rw [hl] at hy0'
                exact hy0'
              rcases (he₃ y.2).1 hy0 with ⟨k, hk⟩
              have hsum : f (g₁ y.1 + t k) = 0 := by
                rw [LinearMap.map_add, leftLiftOfRightLift_apply]
                simpa [s, LinearMap.coprod_apply, hk] using hy
              have hx0 : g₁ y.1 = - t k := by
                apply hf
                rw [LinearMap.map_neg]
                exact eq_neg_iff_add_eq_zero.mpr <| by simpa [LinearMap.map_add] using hsum
              have hτk : g₁ (τ k) = - t k := by
                simpa [LinearMap.comp_apply] using congrArg (fun u => u k) hτ
              have hxker : g₁ (y.1 - τ k) = 0 := by
                rw [LinearMap.map_sub, hx0, hτk]
                simp
              rcases (he₁ (y.1 - τ k)).1 hxker with ⟨x, hx⟩
              refine ⟨(x, k), ?_⟩
              apply Prod.ext
              · have hx' : f₁ x + τ k = y.1 := by
                  rw [hx]
                  abel
                simp [i, hx', hk]
              · simpa [i] using hk
            · rintro ⟨⟨x, k⟩, rfl⟩
              have hτk : g₁ (τ k) = - t k := by
                simpa [LinearMap.comp_apply] using congrArg (fun u => u k) hτ
              have hτf : f (g₁ (τ k)) + l (f₃ k) = 0 := by
                rw [hτk, LinearMap.map_neg, leftLiftOfRightLift_apply]
                simp
              have hf1 : f (g₁ (f₁ x)) = 0 := by
                have : g₁ (f₁ x) = 0 := (he₁ (f₁ x)).2 ⟨x, rfl⟩
                simp [this]
              have : f (g₁ (f₁ x + τ k)) + l (f₃ k) = 0 := by
                rw [LinearMap.map_add, LinearMap.map_add, hf1]
                simpa [add_assoc] using hτf
              simpa [i, s, LinearMap.coprod_apply, LinearMap.comp_apply] using this

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle (P₁ : Type α) (P₂ : Type β)
    (P₃ : Type γ) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃]
    [Module R P₃] {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₃ := sorry

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right (P₁ : Type α) (P₂ : Type β)
    (P₃ : Type γ) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃]
    [Module R P₃] {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) (h₂ : HasFiniteFreeResolution R P₂)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₁ := sorry

end exact_seq
