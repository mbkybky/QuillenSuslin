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

omit [Small.{β} R] [Small.{γ} R] in
theorem moduleFinite_of_hasFiniteFreeResolution {P : Type α} [AddCommGroup P] [Module R P]
    (hP : HasFiniteFreeResolution R P) : Module.Finite R P := by
  rcases hP with ⟨n, hn⟩
  induction hn with
  | zero => infer_instance
  | succ P n F K f g hf hg he hk ih => exact Module.Finite.of_surjective g hg

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
          have hprod : HasFiniteFreeResolution R (Shrink.{β} (P₁ × P₃)) :=
            ⟨0, HasFiniteFreeResolutionOfLength.zero (Shrink.{β} (P₁ × P₃))⟩
          exact hasFiniteFreeResolution_of_linearEquiv ((Shrink.linearEquiv R (P₁ × P₃)).trans
            ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1.symm) hprod
      | succ P₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
            have : Small.{β} K₃ := Module.Finite.small.{β} R K₃
            have : Small.{β} (P₁ × F₃) := Module.Finite.small.{β} R (P₁ × F₃)
            obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
            let t : K₃ →ₗ[R] P₁ := leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl
            let i : K₃ →ₗ[R] P₁ × F₃ := LinearMap.prod (- t) f₃
            let s : P₁ × F₃ →ₗ[R] P₂ := f.coprod l
            refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution i s ?_ ?_ ?_
              ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv (Shrink.linearEquiv R K₃).symm hk₃⟩
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
                have ht : f (t k) = l (f₃ k) :=
                  leftLiftOfRightLift_apply f g f₃ g₃ hf h he₃ l hl k
                have : f (- t k) + l (f₃ k) = 0 := by simp [ht]
                simpa [i, s, LinearMap.prod_apply, LinearMap.coprod_apply] using this
  | succ P₁ n F₁ K₁ f₁ g₁ hf₁ hg₁ he₁ hk₁ ih =>
      rcases h₃ with ⟨n₃, h₃⟩
      cases h₃ with
      | zero P₃ =>
          have : Small.{β} K₁ := Module.Finite.small.{β} R K₁
          have : Small.{β} (F₁ × P₃) := Module.Finite.small.{β} R (F₁ × P₃)
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
          let i : K₁ →ₗ[R] F₁ × P₃ := (LinearMap.inl R F₁ P₃).comp f₁
          let s : F₁ × P₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution i s ?_ ?_ ?_
            ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv (Shrink.linearEquiv R K₁).symm hk₁⟩
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
            have : Small.{β} (F₁ × F₃) := Module.Finite.small.{β} R (F₁ × F₃)
            obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
            let s : F₁ × F₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
            have hs : Function.Surjective s := by
              intro z
              rcases hg₃ (g z) with ⟨y, hy⟩
              have hz0 : g (z - l y) = 0 := by
                rw [LinearMap.map_sub]
                change g z - (g.comp l) y = 0
                rw [hl, hy]
                simp
              rcases (h (z - l y)).1 hz0 with ⟨x₁, hx₁⟩
              rcases hg₁ x₁ with ⟨x, hx⟩
              exact ⟨(x, y), by simp [s, hx, hx₁]⟩
            let K : Submodule R (F₁ × F₃) := s.ker
            let i₁ : K₁ →ₗ[R] F₁ × F₃ := (LinearMap.inl R F₁ F₃).comp f₁
            have hi₁ : ∀ k, i₁ k ∈ K := by
              intro k
              change s (i₁ k) = 0
              have : g₁ (f₁ k) = 0 := (he₁ (f₁ k)).2 ⟨k, rfl⟩
              simp [s, i₁, LinearMap.coprod_apply, LinearMap.comp_apply, this]
            let α : K₁ →ₗ[R] K := LinearMap.codRestrict K i₁ hi₁
            let p : F₁ × F₃ →ₗ[R] F₃ := LinearMap.snd R F₁ F₃
            have hp : ∀ x : K, p x.1 ∈ g₃.ker := by
              intro x
              change g₃ (p x.1) = 0
              have hx0 : f (g₁ x.1.1) + l x.1.2 = 0 := x.2
              have hx0'' : g (f (g₁ x.1.1) + l x.1.2) = 0 := by simpa using congrArg g hx0
              have hx0''' : g (f (g₁ x.1.1)) + g (l x.1.2) = 0 := by
                simpa [LinearMap.map_add] using hx0''
              have hfx : g (f (g₁ x.1.1)) = 0 := (h (f (g₁ x.1.1))).2 ⟨g₁ x.1.1, rfl⟩
              have hgl : g (l x.1.2) = 0 := by
                have : 0 + g (l x.1.2) = 0 := by simpa [hfx] using hx0'''
                simpa using this
              have : g₃ x.1.2 = 0 := by
                have : (g.comp l) x.1.2 = 0 := by simpa [LinearMap.comp_apply] using hgl
                simpa [LinearMap.comp_apply, hl] using this
              simpa [p] using this
            let β : K →ₗ[R] g₃.ker := LinearMap.codRestrict g₃.ker (p.comp K.subtype) hp
            have hα : Function.Injective α := by
              intro x y hxy
              have hxy' : (i₁ x : F₁ × F₃) = i₁ y := by
                simpa [α, LinearMap.codRestrict_apply] using congrArg Subtype.val hxy
              refine hf₁ ?_
              simpa [i₁, LinearMap.comp_apply] using congrArg Prod.fst hxy'
            have hβ : Function.Surjective β := by
              intro y
              have hy0 : g₃ (y : F₃) = 0 := y.2
              have hly0 : g (l (y : F₃)) = 0 := by
                change (g.comp l) (y : F₃) = 0
                rw [hl]
                exact hy0
              rcases (h (l (y : F₃))).1 hly0 with ⟨x₁, hx₁⟩
              rcases hg₁ (-x₁) with ⟨x, hx⟩
              have hxmem : (x, (y : F₃)) ∈ K := by
                change s (x, (y : F₃)) = 0
                simp [s, hx, hx₁, LinearMap.coprod_apply, LinearMap.comp_apply]
              refine ⟨⟨(x, (y : F₃)), hxmem⟩, ?_⟩
              ext
              simp [β, p, LinearMap.codRestrict_apply, LinearMap.comp_apply]
            have hKer : Function.Exact α β := by
              intro x
              constructor
              · intro hx
                have hx2 : x.1.2 = 0 := by
                  have : (β x : F₃) = 0 := by simpa using congrArg Subtype.val hx
                  simpa [β, p, LinearMap.codRestrict_apply, LinearMap.comp_apply] using this
                have hx1mem : (x.1.1 : F₁) ∈ f₁.range := by
                  have hlx : l x.1.2 = 0 := by
                    rw [hx2, LinearMap.map_zero]
                  have hfx0 : f (g₁ x.1.1) = 0 := by
                    have : f (g₁ x.1.1) = -l x.1.2 := eq_neg_of_add_eq_zero_left x.2
                    rw [hlx] at this
                    simpa using this
                  have hxg1 : g₁ x.1.1 = 0 := by
                    apply hf
                    simpa using hfx0
                  have hxker : (x.1.1 : F₁) ∈ g₁.ker := by simpa using hxg1
                  have hxrange : (x.1.1 : F₁) ∈ f₁.range := by
                    have hker_eq : g₁.ker = f₁.range := LinearMap.exact_iff.mp he₁
                    simpa [hker_eq] using hxker
                  simpa using hxrange
                rcases hx1mem with ⟨k, hk⟩
                refine ⟨k, ?_⟩
                ext <;> simp [α, i₁, hx2, hk, LinearMap.codRestrict_apply, LinearMap.comp_apply]
              · rintro ⟨k, rfl⟩
                ext
                simp [β, p, α, i₁, LinearMap.codRestrict_apply, LinearMap.comp_apply]
            have hK₃ : HasFiniteFreeResolution R g₃.ker :=
              hasFiniteFreeResolution_of_linearEquiv (LinearEquiv.ofInjective f₃ hf₃ ≪≫ₗ
                (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm) ⟨n₃, hk₃⟩
            let eK : K ≃ₗ[R] Shrink.{β} K :=
              (Shrink.linearEquiv R K).symm
            let α' : K₁ →ₗ[R] Shrink.{β} K := eK ∘ₗ α
            let β' : Shrink.{β} K →ₗ[R] g₃.ker :=
              β.comp eK.symm.toLinearMap
            have hα' : Function.Injective α' := by
              intro x y hxy
              refine hα ?_
              exact eK.injective <| by simpa [α', LinearMap.comp_apply] using hxy
            have hβ' : Function.Surjective β' := by
              intro y
              rcases hβ y with ⟨x, hx⟩
              refine ⟨eK x, ?_⟩
              simpa [β', LinearMap.comp_apply] using hx
            have hKer' : Function.Exact α' β' := by
              intro y
              constructor
              · intro hy
                have hy' : β (eK.symm y) = 0 := by
                  simpa [β', LinearMap.comp_apply] using hy
                rcases (hKer (eK.symm y)).1 hy' with ⟨x, hx⟩
                refine ⟨x, ?_⟩
                simpa [α', LinearMap.comp_apply] using congrArg eK hx
              · rintro ⟨x, rfl⟩
                have : β (α x) = 0 := (hKer (α x)).2 ⟨x, rfl⟩
                simpa [α', β', LinearMap.comp_apply] using this
            have : Module.Finite R g₃.ker :=
              Module.Finite.equiv (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm
            have : Module.Finite R K := Module.Finite.of_exact hKer hβ
            exact hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution
              K.subtype s (Submodule.subtype_injective _) hs (LinearMap.exact_subtype_ker_map s) <|
                ih α' β' hα' hβ' hKer' hK₃

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₁ : HasFiniteFreeResolution R P₁) (h₂ : HasFiniteFreeResolution R P₂) :
    HasFiniteFreeResolution R P₃ := by
  have : Module.Finite R P₁ := moduleFinite_of_hasFiniteFreeResolution h₁
  rcases h₂ with ⟨n₂, h₂⟩
  cases h₂ with
  | zero P₂ =>
      have : Small.{γ} P₁ := Module.Finite.small.{γ} R P₁
      have : Small.{γ} P₂ := Module.Finite.small.{γ} R P₂
      refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution f g hf hg h ?_
      exact hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv R P₁).symm h₁
  | succ P₂ n F₂ K₂ f₂ g₂ hf₂ hg₂ he₂ hk₂ =>
      have : Small.{γ} F₂ := Module.Finite.small.{γ} R F₂
      let s : F₂ →ₗ[R] P₃ := g.comp g₂
      let L : Submodule R F₂ := s.ker
      have hLmem : ∀ x : K₂, f₂ x ∈ L := by
        intro x
        change s (f₂ x) = 0
        have hx : g₂ (f₂ x) = 0 := (he₂ (f₂ x)).2 ⟨x, rfl⟩
        simp [s, LinearMap.comp_apply, hx]
      let α : K₂ →ₗ[R] L := LinearMap.codRestrict L f₂ hLmem
      let e : P₁ ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
      have hRange (x : L) : g₂ x.1 ∈ f.range := (h (g₂ x.1)).1 x.2
      let β : L →ₗ[R] P₁ := e.symm ∘ₗ LinearMap.codRestrict f.range (g₂.comp L.subtype) hRange
      have hα : Function.Injective α := by
        intro x y hxy
        refine hf₂ ?_
        simpa [α, LinearMap.codRestrict_apply] using congrArg Subtype.val hxy
      have hβ_apply (x : L) : f (β x) = g₂ x.1 := by simp [β, e, LinearMap.comp_apply]
      have hβ : Function.Surjective β := by
        intro y
        rcases hg₂ (f y) with ⟨x, hx⟩
        have hxL : x ∈ L := by
          change s x = 0
          simpa [s, hx, LinearMap.comp_apply] using (h (f y)).2 ⟨y, rfl⟩
        refine ⟨⟨x, hxL⟩, ?_⟩
        refine hf ?_
        simp [hβ_apply, hx]
      have hExact : Function.Exact α β := by
        intro x
        constructor
        · intro hx
          have hx0 : g₂ x.1 = 0 := by
            have : f (β x) = 0 := by simpa using congrArg f hx
            simpa [hβ_apply x] using this
          rcases (he₂ x.1).1 hx0 with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          ext
          simpa [α, LinearMap.codRestrict_apply] using hk
        · rintro ⟨k, rfl⟩
          refine hf ?_
          simpa [hβ_apply, α, LinearMap.codRestrict_apply] using (he₂ (f₂ k)).2 ⟨k, rfl⟩
      have : Module.Finite R L := Module.Finite.of_exact hExact hβ
      have : Small.{γ} L := Module.Finite.small.{γ} R L
      refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution
        L.subtype s (Submodule.subtype_injective _) ?_ (LinearMap.exact_subtype_ker_map s) ?_
      · intro z
        rcases hg z with ⟨y, rfl⟩
        rcases hg₂ y with ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · exact hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv R L).symm <|
          hasFiniteFreeResolution_of_shortExact_of_left_of_right α β hα hβ hExact ⟨n, hk₂⟩ h₁

private theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right
    [Module.Finite R P₃] [Module.Free R P₃]
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₁ := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  let e : P₂ ≃ₗ[R] P₁ × P₃ := ((Function.Exact.splitSurjectiveEquiv h hf) ⟨s, hs⟩).1
  let j : P₃ →ₗ[R] P₂ := e.symm.toLinearMap.comp (LinearMap.inr R P₁ P₃)
  let q : P₂ →ₗ[R] P₁ := (LinearMap.fst R P₁ P₃).comp e.toLinearMap
  have hj : Function.Injective j := by
    intro x y hxy
    have hxy' : e (j x) = e (j y) := by simpa using congrArg e hxy
    simpa [j, LinearMap.comp_apply] using congrArg Prod.snd hxy'
  have hq : Function.Surjective q := by
    intro x
    refine ⟨e.symm (x, 0), ?_⟩
    simp [q, LinearMap.comp_apply]
  have hExact : Function.Exact j q := by
    intro y
    constructor
    · intro hy
      refine ⟨Prod.snd (e y), e.injective ?_⟩
      apply Prod.ext
      · have hy' : Prod.fst (e y) = 0 := by simpa [q, LinearMap.comp_apply] using hy
        simp [j, LinearMap.comp_apply, hy']
      · simp [j, LinearMap.comp_apply]
    · rintro ⟨x, rfl⟩
      simp [j, q, LinearMap.comp_apply]
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle j q hj hq hExact
    ⟨0, HasFiniteFreeResolutionOfLength.zero P₃⟩ h₂

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right
    (hf : Function.Injective f) (hg : Function.Surjective g) (h : Function.Exact f g)
    (h₂ : HasFiniteFreeResolution R P₂) (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₁ := by
  have : Module.Finite R P₂ := moduleFinite_of_hasFiniteFreeResolution h₂
  rcases h₃ with ⟨n₃, h₃⟩
  cases h₃ with
  | zero P₃ => exact hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right f g hf hg h h₂
  | succ P₃ n F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
      let s : P₂ × F₃ →ₗ[R] P₃ := g.coprod (-g₃)
      let Q : Submodule R (P₂ × F₃) := s.ker
      let i₁ : K₃ →ₗ[R] P₂ × F₃ := (LinearMap.inr R P₂ F₃).comp f₃
      have hi₁ : ∀ x : K₃, i₁ x ∈ Q := by
        intro x
        change s (i₁ x) = 0
        have hx : g₃ (f₃ x) = 0 := (he₃ (f₃ x)).2 ⟨x, rfl⟩
        simp [s, i₁, LinearMap.comp_apply, hx]
      let α₁ : K₃ →ₗ[R] Q := LinearMap.codRestrict Q i₁ hi₁
      let β₁ : Q →ₗ[R] P₂ := (LinearMap.fst R P₂ F₃).comp Q.subtype
      have hα₁ : Function.Injective α₁ := by
        intro x y hxy
        refine hf₃ ?_
        simpa [α₁, i₁, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
          congrArg Prod.snd (congrArg Subtype.val hxy)
      have hβ₁ : Function.Surjective β₁ := by
        intro y
        rcases hg₃ (g y) with ⟨z, hz⟩
        have hyQ : (y, z) ∈ Q := by
          change s (y, z) = 0
          simp [s, hz]
        refine ⟨⟨(y, z), hyQ⟩, ?_⟩
        simp [β₁, LinearMap.comp_apply]
      have hExact₁ : Function.Exact α₁ β₁ := by
        intro y
        constructor
        · intro hy
          have hy₁ : y.1.1 = 0 := by simpa [β₁, LinearMap.comp_apply] using hy
          have hy₂ : g₃ y.1.2 = 0 := by
            have : s y.1 = 0 := y.2
            change g y.1.1 + (-g₃) y.1.2 = 0 at this
            rw [hy₁, LinearMap.map_zero, zero_add] at this
            change -g₃ y.1.2 = 0 at this
            exact neg_eq_zero.mp this
          rcases (he₃ y.1.2).1 hy₂ with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          ext <;> simp [α₁, i₁, hy₁, hx, LinearMap.codRestrict_apply, LinearMap.comp_apply]
        · rintro ⟨x, rfl⟩
          simp [α₁, β₁, i₁, LinearMap.codRestrict_apply, LinearMap.comp_apply]
      have : Module.Finite R Q := Module.Finite.of_exact hExact₁ hβ₁
      have : Small.{γ} Q := Module.Finite.small.{γ} R Q
      let eQ : Q ≃ₗ[R] Shrink.{γ} Q := (Shrink.linearEquiv R Q).symm
      let α₁' : K₃ →ₗ[R] Shrink.{γ} Q := eQ ∘ₗ α₁
      let β₁' : Shrink.{γ} Q →ₗ[R] P₂ := β₁.comp eQ.symm.toLinearMap
      have hα₁' : Function.Injective α₁' := by
        intro x y hxy
        exact hα₁ <| eQ.injective <| by simpa [α₁', LinearMap.comp_apply] using hxy
      have hβ₁' : Function.Surjective β₁' := by
        intro y
        rcases hβ₁ y with ⟨x, hx⟩
        refine ⟨eQ x, ?_⟩
        simpa [β₁', LinearMap.comp_apply] using hx
      have hExact₁ : Function.Exact α₁' β₁' := by
        intro y
        constructor
        · intro hy
          have hy' : β₁ (eQ.symm y) = 0 := by simpa [β₁', LinearMap.comp_apply] using hy
          rcases (hExact₁ (eQ.symm y)).1 hy' with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          simpa [α₁', LinearMap.comp_apply] using congrArg eQ hx
        · rintro ⟨x, rfl⟩
          have : β₁ (α₁ x) = 0 := (hExact₁ (α₁ x)).2 ⟨x, rfl⟩
          simpa [α₁', β₁', LinearMap.comp_apply] using this
      let i₂ : P₁ →ₗ[R] P₂ × F₃ := (LinearMap.inl R P₂ F₃).comp f
      have hi₂ : ∀ x : P₁, i₂ x ∈ Q := by
        intro x
        change s (i₂ x) = 0
        have hx : g (f x) = 0 := (h (f x)).2 ⟨x, rfl⟩
        simp [s, i₂, LinearMap.comp_apply, hx]
      let α₂ : P₁ →ₗ[R] Q := LinearMap.codRestrict Q i₂ hi₂
      let β₂ : Q →ₗ[R] F₃ := (LinearMap.snd R P₂ F₃).comp Q.subtype
      have hα₂ : Function.Injective α₂ := by
        intro x y hxy
        refine hf ?_
        simpa [α₂, i₂, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
          congrArg Prod.fst (congrArg Subtype.val hxy)
      have hβ₂ : Function.Surjective β₂ := by
        intro z
        rcases hg (g₃ z) with ⟨y, hy⟩
        have hzQ : (y, z) ∈ Q := by
          change s (y, z) = 0
          simp [s, hy]
        refine ⟨⟨(y, z), hzQ⟩, ?_⟩
        simp [β₂, LinearMap.comp_apply]
      have hExact₂ : Function.Exact α₂ β₂ := by
        intro y
        constructor
        · intro hy
          have hy₂ : y.1.2 = 0 := by
            simpa [β₂, LinearMap.comp_apply] using hy
          have hy₁ : g y.1.1 = 0 := by
            have : s y.1 = 0 := y.2
            change g y.1.1 + (-g₃) y.1.2 = 0 at this
            rw [hy₂, LinearMap.map_zero, add_zero] at this
            exact this
          rcases (h y.1.1).1 hy₁ with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          ext <;> simp [α₂, i₂, hy₂, hx, LinearMap.codRestrict_apply, LinearMap.comp_apply]
        · rintro ⟨x, rfl⟩
          simp [α₂, β₂, i₂, LinearMap.codRestrict_apply, LinearMap.comp_apply]
      let α₂' : P₁ →ₗ[R] Shrink.{γ} Q := eQ ∘ₗ α₂
      let β₂' : Shrink.{γ} Q →ₗ[R] F₃ := β₂.comp eQ.symm.toLinearMap
      have hα₂' : Function.Injective α₂' := by
        intro x y hxy
        refine hα₂ ?_
        exact eQ.injective <| by simpa [α₂', LinearMap.comp_apply] using hxy
      have hβ₂' : Function.Surjective β₂' := by
        intro z
        rcases hβ₂ z with ⟨x, hx⟩
        refine ⟨eQ x, ?_⟩
        simpa [β₂', LinearMap.comp_apply] using hx
      have hExact₂ : Function.Exact α₂' β₂' := by
        intro y
        constructor
        · intro hy
          have hy' : β₂ (eQ.symm y) = 0 := by
            simpa [β₂', LinearMap.comp_apply] using hy
          rcases (hExact₂ (eQ.symm y)).1 hy' with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          simpa [α₂', LinearMap.comp_apply] using congrArg eQ hx
        · rintro ⟨x, rfl⟩
          have : β₂ (α₂ x) = 0 := (hExact₂ (α₂ x)).2 ⟨x, rfl⟩
          simpa [α₂', β₂', LinearMap.comp_apply] using this
      exact hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right _ _ hα₂' hβ₂' hExact₂ <|
        hasFiniteFreeResolution_of_shortExact_of_left_of_right α₁' β₁' hα₁' hβ₁' hExact₁ ⟨n, hk₃⟩ h₂

end exact_seq
