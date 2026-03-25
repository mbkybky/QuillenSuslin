/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.Finiteness.Small

universe u u' v v' w

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

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- A finitely generated free module has a finite free resolution of length `0`. -/
theorem hasFiniteFreeResolution_of_finite_of_free (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Free R M] : HasFiniteFreeResolution R M :=
  ⟨0, HasFiniteFreeResolutionOfLength.zero M⟩

/-- A subsingleton module has a finite free resolution. -/
theorem hasFiniteFreeResolution_of_subsingleton (M : Type v)
    [AddCommGroup M] [Module R M] [Subsingleton M] : HasFiniteFreeResolution R M :=
  hasFiniteFreeResolution_of_finite_of_free M

theorem moduleFinite_of_hasFiniteFreeResolutionOfLength {P : Type v} [AddCommGroup P] [Module R P]
    {n : ℕ} (hP : HasFiniteFreeResolutionOfLength R P n) : Module.Finite R P := by
  induction hP with
  | zero => infer_instance
  | succ P n F K f g hf hg he hk ih => exact Module.Finite.of_surjective g hg

theorem moduleFinite_of_hasFiniteFreeResolution {P : Type v} [AddCommGroup P] [Module R P]
    (hP : HasFiniteFreeResolution R P) : Module.Finite R P := by
  rcases hP with ⟨n, hn⟩
  exact moduleFinite_of_hasFiniteFreeResolutionOfLength hn

/-- A semilinear equivalence over mutually inverse ring homomorphisms preserves finite free
resolutions. -/
theorem hasFiniteFreeResolutionOfLength_of_semilinearEquiv {S : Type u'} [CommRing S] [Small.{v'} S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {P : Type v} [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R P n)
    {Q : Type v'} [AddCommGroup Q] [Module S Q] (e : P ≃ₛₗ[σ] Q) :
    HasFiniteFreeResolutionOfLength S Q n := by
  induction hn generalizing Q with
  | zero P =>
      have : Module.Finite S Q :=
        (LinearMap.finite_iff_of_bijective e.toLinearMap e.bijective).1 inferInstance
      have : Module.Free S Q := Module.Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero Q
  | succ P n F K f g hf hg he hk ih =>
      let : Module S F := Module.compHom F σ'
      let : Module S K := Module.compHom K σ'
      let eF : F ≃ₛₗ[σ] F :=
        { toFun := id
          invFun := id
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' := by
            intro a x
            change a • x = (σ' (σ a) : R) • x
            simp }
      let eK : K ≃ₛₗ[σ] K :=
        { toFun := id
          invFun := id
          left_inv _ := rfl
          right_inv _ := rfl
          map_add' _ _ := rfl
          map_smul' := by
            intro a x
            change a • x = (σ' (σ a) : R) • x
            simp }
      let fS : K →ₗ[S] F :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := by
            intro b x
            exact f.map_smul (σ' b) x }
      let gS : F →ₗ[S] Q :=
        { toFun := fun x => e (g x)
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro b x
            change e (g (σ' b • x)) = b • e (g x)
            rw [g.map_smul]
            simp [LinearEquiv.map_smulₛₗ] }
      have hFSfinite : Module.Finite S F :=
        (LinearMap.finite_iff_of_bijective eF.toLinearMap eF.bijective).1 inferInstance
      have hFSfree : Module.Free S F := Module.Free.of_equiv eF
      have hKSfinite : Module.Finite S K :=
        (LinearMap.finite_iff_of_bijective eK.toLinearMap eK.bijective).1 inferInstance
      have : Small.{v'} F := Module.Finite.small S F
      have : Small.{v'} K := Module.Finite.small S K
      let eF' : Shrink.{v'} F ≃ₗ[S] F := Shrink.linearEquiv S F
      let eK' : Shrink.{v'} K ≃ₗ[S] K := Shrink.linearEquiv S K
      have heS : Function.Exact f gS := by
        intro y
        change e (g y) = 0 ↔ y ∈ Set.range f
        rw [show e (g y) = 0 ↔ g y = 0 by
          constructor
          · intro h
            apply e.injective
            simpa using h
          · intro h
            simp [h]]
        exact he y
      refine HasFiniteFreeResolutionOfLength.succ Q n (Shrink.{v'} F) (Shrink.{v'} K)
        (eF'.symm ∘ₗ (fS.comp eK'.toLinearMap)) (gS.comp eF'.toLinearMap) ?_ ?_ ?_
          (ih (eK.trans eK'.symm))
      · exact eF'.symm.injective.comp (hf.comp eK'.injective)
      · exact (e.surjective.comp hg).comp eF'.surjective
      · exact (LinearEquiv.conj_exact_iff_exact (fS.comp eK'.toLinearMap) gS eF'.symm).2 <|
          (Function.Surjective.comp_exact_iff_exact eK'.surjective).2 heS

/-- A semilinear equivalence over mutually inverse ring homomorphisms preserves finite free
resolutions. -/
theorem hasFiniteFreeResolution_of_semilinearEquiv
    {S : Type u'} [CommRing S] [Small.{v'} S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {P : Type v} [AddCommGroup P] [Module R P] (hP : HasFiniteFreeResolution R P)
    {Q : Type v'} [AddCommGroup Q] [Module S Q] (e : P ≃ₛₗ[σ] Q) :
    HasFiniteFreeResolution S Q := by
  rcases hP with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_semilinearEquiv hn e⟩

variable [Small.{w} R]

theorem hasFiniteFreeResolutionOfLength_of_linearEquiv {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q) {n : ℕ}
    (hn : HasFiniteFreeResolutionOfLength R P n) : HasFiniteFreeResolutionOfLength R Q n :=
  hasFiniteFreeResolutionOfLength_of_semilinearEquiv hn e

theorem hasFiniteFreeResolution_of_linearEquiv {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (hn : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases hn with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_linearEquiv e hn⟩

theorem hasFiniteFreeResolutionOfLength_of_ker_hasFiniteFreeResolutionOfLength
    {P : Type v} {F : Type*} {K : Type w} [AddCommGroup P] [Module R P] [AddCommGroup F]
    [Module R F] [Module.Finite R F] [Module.Free R F] [AddCommGroup K] [Module R K]
    (i : K →ₗ[R] F) (s : F →ₗ[R] P) (hi : Function.Injective i)
    (hs : Function.Surjective s) (he : Function.Exact i s) {n : ℕ}
    (hk : HasFiniteFreeResolutionOfLength R K n) : HasFiniteFreeResolutionOfLength R P (n + 1) := by
  have : Module.Finite R K := moduleFinite_of_hasFiniteFreeResolutionOfLength hk
  have : Small.{v} F := Module.Finite.small.{v} R F
  have : Small.{v} K := Module.Finite.small.{v} R K
  have eF : Shrink.{v} F ≃ₗ[R] F := Shrink.linearEquiv R F
  have eK : Shrink.{v} K ≃ₗ[R] K := Shrink.linearEquiv R K
  let i' : Shrink.{v} K →ₗ[R] Shrink.{v} F := eF.symm ∘ₗ (i.comp eK.toLinearMap)
  let s' : Shrink.{v} F →ₗ[R] P := s.comp eF.toLinearMap
  refine HasFiniteFreeResolutionOfLength.succ P n (Shrink.{v} F) (Shrink.{v} K) i' s'
    (eF.symm.injective.comp (hi.comp eK.injective)) (hs.comp eF.surjective) ?_
      (hasFiniteFreeResolutionOfLength_of_linearEquiv eK.symm hk)
  exact (LinearEquiv.conj_exact_iff_exact (i.comp eK.toLinearMap) s eF.symm).2 <|
    (Function.Surjective.comp_exact_iff_exact eK.surjective).2 he

theorem hasFiniteFreeResolution_of_ker_hasFiniteFreeResolution {P : Type v} {F : Type*} {K : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Module.Free R F] [AddCommGroup K] [Module R K] (i : K →ₗ[R] F) (s : F →ₗ[R] P)
    (hi : Function.Injective i) (hs : Function.Surjective s) (he : Function.Exact i s)
    (hk : HasFiniteFreeResolution R K) : HasFiniteFreeResolution R P := by
  rcases hk with ⟨n, hk⟩
  exact ⟨n + 1,
    hasFiniteFreeResolutionOfLength_of_ker_hasFiniteFreeResolutionOfLength i s hi hs he hk⟩
