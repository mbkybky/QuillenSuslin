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
        (eF ∘ₗ (f.comp eK.symm.toLinearMap)) (e ∘ₗ (g.comp eF.symm.toLinearMap)) ?_ ?_ ?_ (ih eK)
      · exact eF.injective.comp (hf.comp eK.symm.injective)
      · exact e.surjective.comp (hg.comp eF.symm.surjective)
      · exact (Function.Injective.comp_exact_iff_exact e.injective).2 <|
          (LinearEquiv.conj_exact_iff_exact (f.comp eK.symm.toLinearMap) g eF).2 <|
            (Function.Surjective.comp_exact_iff_exact eK.symm.surjective).2 he

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
  refine ⟨n + 1,  HasFiniteFreeResolutionOfLength.succ P n (Shrink.{β} F) (Shrink.{β} K) i' s'
    (eF.injective.comp (hi.comp eK.symm.injective)) (hs.comp eF.symm.surjective) ?_ hk⟩
  exact (LinearEquiv.conj_exact_iff_exact (i.comp eK.symm.toLinearMap) s eF).2 <|
    (Function.Surjective.comp_exact_iff_exact eK.symm.surjective).2 he

private noncomputable def leftLiftOfRightLift (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) : K →ₗ[R] P₁ :=
  (LinearEquiv.ofInjective f hf).symm ∘ₗ (LinearMap.codRestrict f.range (l.comp f₃) <|
    fun k => (h (l (f₃ k))).1 <| by simpa [← hl] using Function.Exact.apply_apply_eq_zero he₃ k)

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R] in
private theorem leftLiftOfRightLift_apply (hf : Function.Injective f) (h : Function.Exact f g)
    (he₃ : Function.Exact f₃ g₃) (l : F →ₗ[R] P₂) (hl : g.comp l = g₃) (k : K) :
    f (leftLiftOfRightLift f g f₃ g₃ hf h he₃ l hl k) = l (f₃ k) := by
  simp [leftLiftOfRightLift]

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R] in
private theorem surjective_coprod_of_exact_of_lift
    {A : Type*} {B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (h : Function.Exact f g) (u : A →ₗ[R] P₁) (v : B →ₗ[R] P₃) (l : B →ₗ[R] P₂)
    (hu : Function.Surjective u) (hv : Function.Surjective v) (hl : g.comp l = v) :
    Function.Surjective ((f.comp u).coprod l) := by
  intro z
  rcases hv (g z) with ⟨y, hy⟩
  have hz0 : g (z - l y) = 0 := by
    rw [LinearMap.map_sub]
    change g z - (g.comp l) y = 0
    rw [hl, hy]
    simp
  rcases (h (z - l y)).1 hz0 with ⟨x₁, hx₁⟩
  rcases hu x₁ with ⟨x, hx⟩
  exact ⟨(x, y), by simp [hx, hx₁]⟩

omit [Small.{α} R] [Small.{β} R] [Small.{γ} R] in
private theorem coprod_snd_eq_zero_of_eq_zero
    {A : Type*} {B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (h : Function.Exact f g) (u : A →ₗ[R] P₁) (v : B →ₗ[R] P₃) (l : B →ₗ[R] P₂)
    (hl : g.comp l = v) (y : A × B) (hy : ((f.comp u).coprod l) y = 0) : v y.2 = 0 := by
  simpa [← hl, Function.Exact.apply_apply_eq_zero h (u y.1)] using congrArg g hy

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
            exact hf₃ (congrArg Prod.snd hxy)
          · exact surjective_coprod_of_exact_of_lift f g h .id g₃ l Function.surjective_id hg₃ hl
          · intro y
            constructor
            · intro hy
              have hy0 : g₃ y.2 = 0 := coprod_snd_eq_zero_of_eq_zero
                f g h LinearMap.id  g₃ l hl y <| by simpa [s] using hy
              rcases (he₃ y.2).1 hy0 with ⟨k, hk⟩
              have hsum : f (t k + y.1) = 0 := by
                rw [LinearMap.map_add, leftLiftOfRightLift_apply]
                simpa [hk, s, add_comm] using hy
              have hxy0 : y.1 + t k = 0 := hf <| by simpa [add_comm] using hsum
              exact ⟨k, Prod.ext (by simp [i, eq_neg_iff_add_eq_zero.mpr hxy0]) hk⟩
            · rintro ⟨k, rfl⟩
              have ht : f (t k) = l (f₃ k) := leftLiftOfRightLift_apply f g f₃ g₃ hf h he₃ l hl k
              change f (- t k) + l (f₃ k) = 0
              simp [ht]
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
            exact hf₁ (congrArg Prod.fst hxy)
          · exact surjective_coprod_of_exact_of_lift f g h g₁ .id l hg₁ Function.surjective_id hl
          · intro y
            constructor
            · intro hy
              have hy0 : y.2 = 0 := coprod_snd_eq_zero_of_eq_zero f g h g₁ LinearMap.id l hl y <|
                by simpa [s] using hy
              have hx0 : g₁ y.1 = 0 := by
                apply hf
                simpa [s, hy0] using hy
              rcases (he₁ y.1).1 hx0 with ⟨x, hx⟩
              exact ⟨x, Prod.ext hx (by simp [hy0, i])⟩
            · rintro ⟨x, rfl⟩
              have hx0 : g₁ (f₁ x) = 0 := Function.Exact.apply_apply_eq_zero he₁ x
              change f (g₁ (f₁ x)) + l 0 = 0
              simp [hx0]
      | succ P₃ n₃ F₃ K₃ f₃ g₃ hf₃ hg₃ he₃ hk₃ =>
          have : Small.{β} (F₁ × F₃) := Module.Finite.small.{β} R (F₁ × F₃)
          obtain ⟨l, hl⟩ := Module.projective_lifting_property g g₃ hg
          let s : F₁ × F₃ →ₗ[R] P₂ := (f.comp g₁).coprod l
          let K : Submodule R (F₁ × F₃) := s.ker
          let i₁ : K₁ →ₗ[R] F₁ × F₃ := (LinearMap.inl R F₁ F₃).comp f₁
          have hi₁ : ∀ k, i₁ k ∈ K := by
            intro k
            change s (i₁ k) = 0
            have : g₁ (f₁ k) = 0 := Function.Exact.apply_apply_eq_zero he₁ k
            simp [s, i₁, this]
          let α : K₁ →ₗ[R] K := LinearMap.codRestrict K i₁ hi₁
          let p : F₁ × F₃ →ₗ[R] F₃ := LinearMap.snd R F₁ F₃
          have hp : ∀ x : K, p x.1 ∈ g₃.ker := by
            intro x
            change g₃ (p x.1) = 0
            simpa [p] using coprod_snd_eq_zero_of_eq_zero f g h g₁ g₃ l hl x.1 x.2
          let β : K →ₗ[R] g₃.ker := LinearMap.codRestrict g₃.ker (p.comp K.subtype) hp
          have hα : Function.Injective α := by
            intro x y hxy
            exact hf₁ <| congrArg Prod.fst (congrArg Subtype.val hxy)
          have hβ : Function.Surjective β := by
            intro y
            have hy0 : g₃ (y : F₃) = 0 := y.2
            have hly0 : g (l (y : F₃)) = 0 := by
              change (g.comp l) (y : F₃) = 0
              rw [hl, hy0]
            rcases (h (l (y : F₃))).1 hly0 with ⟨x₁, hx₁⟩
            rcases hg₁ (-x₁) with ⟨x, hx⟩
            have hxmem : (x, (y : F₃)) ∈ K := by
              change s (x, (y : F₃)) = 0
              simp [s, hx, hx₁]
            refine ⟨⟨(x, (y : F₃)), hxmem⟩, ?_⟩
            ext
            simp [β, p]
          have hKer : Function.Exact α β := by
            intro x
            constructor
            · intro hx
              have hx2 : x.1.2 = 0 := congrArg Subtype.val hx
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
                simpa [LinearMap.exact_iff.mp he₁] using show (x.1.1 : F₁) ∈ g₁.ker from hxg1
              rcases hx1mem with ⟨k, hk⟩
              exact ⟨k, by ext <;> simp [α, i₁, hx2, hk]⟩
            · rintro ⟨k, rfl⟩
              ext
              simp [β, p, α, i₁]
          have hK₃ : HasFiniteFreeResolution R g₃.ker :=
            hasFiniteFreeResolution_of_linearEquiv (LinearEquiv.ofInjective f₃ hf₃ ≪≫ₗ
              (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm) ⟨n₃, hk₃⟩
          let eK : K ≃ₗ[R] Shrink.{β} K := (Shrink.linearEquiv R K).symm
          have : Module.Finite R g₃.ker :=
            Module.Finite.equiv (LinearEquiv.ofEq g₃.ker f₃.range he₃.linearMap_ker_eq).symm
          have : Module.Finite R K := Module.Finite.of_exact hKer hβ
          exact hasFiniteFreeResolution_of_shrink_ker_hasFiniteFreeResolution K.subtype s
            (Submodule.subtype_injective K)
              (surjective_coprod_of_exact_of_lift f g h g₁ g₃ l hg₁ hg₃ hl)
                (LinearMap.exact_subtype_ker_map s) <|
                  ih _ _ (eK.injective.comp hα) (hβ.comp eK.symm.surjective)
                    ((LinearEquiv.conj_exact_iff_exact α β eK).2 hKer) hK₃

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
        have hx : g₂ (f₂ x) = 0 := Function.Exact.apply_apply_eq_zero he₂ x
        simp [s, hx]
      let α : K₂ →ₗ[R] L := LinearMap.codRestrict L f₂ hLmem
      let e : P₁ ≃ₗ[R] f.range := LinearEquiv.ofInjective f hf
      have hRange (x : L) : g₂ x.1 ∈ f.range := (h (g₂ x.1)).1 x.2
      let β : L →ₗ[R] P₁ := e.symm ∘ₗ LinearMap.codRestrict f.range (g₂.comp L.subtype) hRange
      have hα : Function.Injective α := by
        intro x y hxy
        exact hf₂ (congrArg Subtype.val hxy)
      have hβ_apply (x : L) : f (β x) = g₂ x.1 := by simp [β, e]
      have hβ : Function.Surjective β := by
        intro y
        rcases hg₂ (f y) with ⟨x, hx⟩
        have hxL : x ∈ L := by
          change s x = 0
          simpa [s, hx] using Function.Exact.apply_apply_eq_zero h y
        refine ⟨⟨x, hxL⟩, ?_⟩
        refine hf ?_
        simp [hβ_apply, hx]
      have hExact : Function.Exact α β := by
        intro x
        constructor
        · intro hx
          have hx0 : g₂ x.1 = 0 := by simpa [hβ_apply x] using congrArg f hx
          rcases (he₂ x.1).1 hx0 with ⟨k, hk⟩
          exact ⟨k, (Subtype.ext hk)⟩
        · rintro ⟨k, rfl⟩
          refine hf ?_
          simpa [hβ_apply, α] using Function.Exact.apply_apply_eq_zero he₂ k
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
  have : Module.Finite R P₂ := moduleFinite_of_hasFiniteFreeResolution h₂
  have : Module.Finite R (P₁ × P₃) := Module.Finite.equiv e
  have : Small.{β} (P₁ × P₃) := Module.Finite.small.{β} R (P₁ × P₃)
  let e' : (P₁ × P₃) ≃ₗ[R] Shrink.{β} (P₁ × P₃) := (Shrink.linearEquiv R (P₁ × P₃)).symm
  let i : P₃ →ₗ[R] Shrink.{β} (P₁ × P₃) := e' ∘ₗ LinearMap.inr R P₁ P₃
  let q : Shrink.{β} (P₁ × P₃) →ₗ[R] P₁ := (LinearMap.fst R P₁ P₃).comp e'.symm.toLinearMap
  have hi : Function.Injective i := e'.injective.comp LinearMap.inr_injective
  have hq : Function.Surjective q := (LinearMap.fst_surjective (R := R)).comp e'.symm.surjective
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle i q hi hq
    ((LinearEquiv.conj_exact_iff_exact _ _ e').2 Function.Exact.inr_fst)
      ⟨0, HasFiniteFreeResolutionOfLength.zero P₃⟩
        (hasFiniteFreeResolution_of_linearEquiv (e.trans e') h₂)

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
      let s : P₂ × F₃ →ₗ[R] P₃ := g.coprod (- g₃)
      let Q : Submodule R (P₂ × F₃) := s.ker
      let i₁ : K₃ →ₗ[R] P₂ × F₃ := (LinearMap.inr R P₂ F₃).comp f₃
      have hi₁ : ∀ x : K₃, i₁ x ∈ Q := by
        intro x
        change s (i₁ x) = 0
        have hx : g₃ (f₃ x) = 0 := Function.Exact.apply_apply_eq_zero he₃ x
        simp [s, i₁, hx]
      let α₁ : K₃ →ₗ[R] Q := LinearMap.codRestrict Q i₁ hi₁
      let β₁ : Q →ₗ[R] P₂ := (LinearMap.fst R P₂ F₃).comp Q.subtype
      have hα₁ : Function.Injective α₁ := by
        intro x y hxy
        exact hf₃ (congrArg Prod.snd (congrArg Subtype.val hxy))
      have hβ₁ : Function.Surjective β₁ := by
        intro y
        rcases hg₃ (g y) with ⟨z, hz⟩
        have hyQ : (y, z) ∈ Q := by
          change s (y, z) = 0
          simp [s, hz]
        refine ⟨⟨(y, z), hyQ⟩, ?_⟩
        simp [β₁]
      have hExact₁₀ : Function.Exact α₁ β₁ := by
        intro y
        constructor
        · intro hy
          have hy₁ : y.1.1 = 0 := hy
          have hy0 : g y.1.1 + (- g₃) y.1.2 = 0 := y.2
          have hy₂ : g₃ y.1.2 = 0 := by
            rw [hy₁, LinearMap.map_zero, zero_add] at hy0
            exact neg_eq_zero.mp hy0
          rcases (he₃ y.1.2).1 hy₂ with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          ext <;> simp [α₁, i₁, hy₁, hx]
        · rintro ⟨x, rfl⟩
          simp [α₁, β₁, i₁]
      have : Module.Finite R Q := Module.Finite.of_exact hExact₁₀ hβ₁
      have : Small.{γ} Q := Module.Finite.small.{γ} R Q
      let eQ : Q ≃ₗ[R] Shrink.{γ} Q := (Shrink.linearEquiv R Q).symm
      let i₂ : P₁ →ₗ[R] P₂ × F₃ := (LinearMap.inl R P₂ F₃).comp f
      have hi₂ : ∀ x : P₁, i₂ x ∈ Q := by
        intro x
        change s (i₂ x) = 0
        have hx : g (f x) = 0 := Function.Exact.apply_apply_eq_zero h x
        simp [s, i₂, hx]
      let α₂ : P₁ →ₗ[R] Q := LinearMap.codRestrict Q i₂ hi₂
      let β₂ : Q →ₗ[R] F₃ := (LinearMap.snd R P₂ F₃).comp Q.subtype
      have hα₂ : Function.Injective α₂ := by
        intro x y hxy
        exact hf (congrArg Prod.fst (congrArg Subtype.val hxy))
      have hβ₂ : Function.Surjective β₂ := by
        intro z
        rcases hg (g₃ z) with ⟨y, hy⟩
        have hzQ : (y, z) ∈ Q := by
          change s (y, z) = 0
          simp [s, hy]
        refine ⟨⟨(y, z), hzQ⟩, ?_⟩
        simp [β₂]
      have hExact₂₀ : Function.Exact α₂ β₂ := by
        intro y
        constructor
        · intro hy
          have hy₂ : y.1.2 = 0 := hy
          have hy₁ : g y.1.1 = 0 := by
            have h : g y.1.1 + (-g₃) y.1.2 = 0 := y.2
            rwa [hy₂, LinearMap.map_zero, add_zero] at h
          rcases (h y.1.1).1 hy₁ with ⟨x, hx⟩
          refine ⟨x, ?_⟩
          ext <;> simp [α₂, i₂, hy₂, hx]
        · rintro ⟨x, rfl⟩
          simp [α₂, β₂, i₂]
      exact hasFiniteFreeResolution_of_shortExact_of_middle_of_free_right
        (eQ.toLinearMap ∘ₗ α₂) _ (eQ.injective.comp hα₂) (hβ₂.comp eQ.symm.surjective)
          ((LinearEquiv.conj_exact_iff_exact α₂ β₂ eQ).2 hExact₂₀) <|
            hasFiniteFreeResolution_of_shortExact_of_left_of_right
              (eQ.toLinearMap ∘ₗ α₁) _ (eQ.injective.comp hα₁) (hβ₁.comp eQ.symm.surjective)
                ((LinearEquiv.conj_exact_iff_exact α₁ β₁ eQ).2 hExact₁₀) ⟨n, hk₃⟩ h₂

end exact_seq
