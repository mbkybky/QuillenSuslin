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
            have hk₃' : HasFiniteFreeResolution R (Shrink.{β} K₃) := by
              refine ⟨n, ?_⟩
              simpa using hasFiniteFreeResolutionOfLength_of_linearEquiv
                (R := R) (e := (Shrink.linearEquiv R K₃).symm) hk₃
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
          have hk₁' : HasFiniteFreeResolution R (Shrink.{β} K₁) := by
            refine ⟨n, ?_⟩
            simpa using hasFiniteFreeResolutionOfLength_of_linearEquiv
              (R := R) (e := (Shrink.linearEquiv R K₁).symm) hk₁
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
              have hx0 : s x.1 = 0 := x.2
              -- Expand `s (x₁, x₃) = f (g₁ x₁) + l x₃`, then apply `g`.
              have hx0' : f (g₁ x.1.1) + l x.1.2 = 0 := by
                change s x.1 = 0
                exact hx0
              have hx0'' : g (f (g₁ x.1.1) + l x.1.2) = 0 := by
                simpa using congrArg g hx0'
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
              -- Lift `y` along `s` by solving `f (g₁ x₁) = - l y`.
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
                -- `β x = 0` forces the second component of `x` to be `0`.
                have hx2 : x.1.2 = 0 := by
                  have : (β x : F₃) = 0 := by simpa using congrArg Subtype.val hx
                  simpa [β, p, LinearMap.codRestrict_apply, LinearMap.comp_apply] using this
                have hx1mem : (x.1.1 : F₁) ∈ f₁.range := by
                  have hx0 : s x.1 = 0 := x.2
                  have hx0' : f (g₁ x.1.1) + l x.1.2 = 0 := by
                    change s x.1 = 0
                    exact hx0
                  have hlx : l x.1.2 = 0 := by
                    rw [hx2, LinearMap.map_zero]
                  have hfx0 : f (g₁ x.1.1) = 0 := by
                    have : f (g₁ x.1.1) = -l x.1.2 := eq_neg_of_add_eq_zero_left hx0'
                    rw [hlx] at this
                    simpa using this
                  have hxg1 : g₁ x.1.1 = 0 := by
                    apply hf
                    simpa using hfx0
                  -- exactness for `f₁,g₁` gives membership in `f₁.range`
                  have hxker : (x.1.1 : F₁) ∈ g₁.ker := by
                    -- `x.1.1 ∈ g₁.ker` is definitionally `g₁ x.1.1 = 0`
                    simpa using hxg1
                  -- Now use `g₁.ker = f₁.range`.
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
            have hK₃ : HasFiniteFreeResolution R (g₃.ker : Type γ) := by
              -- Identify `g₃.ker` with `K₃` via `f₃`.
              have hker : g₃.ker = f₃.range := Function.Exact.linearMap_ker_eq he₃
              have e₁ : K₃ ≃ₗ[R] (f₃.range : Type γ) := LinearEquiv.ofInjective f₃ hf₃
              have e₂ : (f₃.range : Type γ) ≃ₗ[R] (g₃.ker : Type γ) :=
                (LinearEquiv.ofEq g₃.ker f₃.range hker).symm
              refine hasFiniteFreeResolution_of_linearEquiv (e₁.trans e₂) ?_
              exact ⟨n₃, hk₃⟩
            let eK : (K : Type (max α γ)) ≃ₗ[R] Shrink.{β} (K : Type (max α γ)) :=
              (Shrink.linearEquiv R (K : Type (max α γ))).symm
            let α' : K₁ →ₗ[R] Shrink.{β} (K : Type (max α γ)) := eK ∘ₗ α
            let β' : Shrink.{β} (K : Type (max α γ)) →ₗ[R] g₃.ker :=
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
            have hK' : HasFiniteFreeResolution R (Shrink.{β} (K : Type (max α γ))) := by
              exact ih α' β' hα' hβ' hKer' hK₃
            have : Module.Finite R (g₃.ker : Type γ) := by
              have hker : g₃.ker = f₃.range := Function.Exact.linearMap_ker_eq he₃
              have : Module.Finite R (f₃.range : Type γ) := by infer_instance
              have e : (f₃.range : Type γ) ≃ₗ[R] (g₃.ker : Type γ) :=
                (LinearEquiv.ofEq g₃.ker f₃.range hker).symm
              exact Module.Finite.equiv e
            have : Module.Finite R (K : Type (max α γ)) := by
              -- finiteness follows from exactness and surjectivity
              exact Module.Finite.of_exact hKer hβ
            letI : Module.Finite R (K : Type (max α γ)) := this
            have : Small.{β} (K : Type (max α γ)) :=
              Module.Finite.small.{β} R (K : Type (max α γ))
            refine hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution
              (R := R) (P := P₂) (F := F₁ × F₃) (K := K) K.subtype s
              (Submodule.subtype_injective _) hs (LinearMap.exact_subtype_ker_map s) hK'

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
