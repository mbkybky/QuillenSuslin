/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

public section

namespace Module

open scoped TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

section Free

lemma rankAtStalk_eq_of_le_of_finite_of_flat [Module.Finite R M] [Module.Flat R M]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    rankAtStalk M ⟨p, inferInstance⟩ = rankAtStalk M ⟨q, inferInstance⟩ := by
  let S := Localization.AtPrime q
  have hdisj : Disjoint (q.primeCompl : Set R) p := by
    rw [Set.disjoint_left]
    intro x hxq hxp
    exact hxq (hpq hxp)
  have hp_range : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.primeCompl]
    exact hdisj
  obtain ⟨P, hP⟩ := hp_range
  have : Module.Free S (LocalizedModule q.primeCompl M) := Module.free_of_flat_of_isLocalRing
  let e : LocalizedModule q.primeCompl M ≃ₗ[S] S ⊗[R] M :=
    LocalizedModule.equivTensorProduct q.primeCompl M
  calc
    rankAtStalk M (⟨p, inferInstance⟩ : PrimeSpectrum R)
        = rankAtStalk (S ⊗[R] M) P := by
          rw [rankAtStalk_baseChange]
          exact congr_arg (rankAtStalk M) hP.symm
    _ = rankAtStalk (LocalizedModule q.primeCompl M) P := by
          exact congr_fun (rankAtStalk_eq_of_equiv e.symm) P
    _ = Module.finrank S (LocalizedModule q.primeCompl M) := by
          simp
    _ = rankAtStalk M (⟨q, inferInstance⟩ : PrimeSpectrum R) := rfl

variable (M) in
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant [Module.Finite R M] [Module.Flat R M]
    (m : Ideal R) [m.IsPrime] (h : ∀ (p : Ideal R) [p.IsMaximal],
      rankAtStalk M ⟨p, inferInstance⟩ = rankAtStalk M ⟨m, inferInstance⟩) :
    ∃ (f : R) (_ : f ∉ m), Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  let n := rankAtStalk M ⟨m, inferInstance⟩
  obtain ⟨v, hφm⟩ : ∃ (v : Fin n → M), Function.Bijective <| IsLocalizedModule.map m.primeCompl
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime m)))
        (LocalizedModule.mkLinearMap m.primeCompl M) (Finsupp.linearCombination R v) := by
    have : Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    let b : Basis (Fin n) (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
      Module.finBasisOfFinrankEq (Localization.AtPrime m) (LocalizedModule m.primeCompl M) rfl
    choose y hy using fun i ↦
      IsLocalizedModule.surj m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl M) (b i)
    let v : Fin n → M := fun i ↦ (y i).1
    refine ⟨v, ?_⟩
    let b' := b.isUnitSMul (fun i ↦ IsLocalization.map_units (Localization.AtPrime m) (y i).2)
    have hb' (i : Fin n) : b' i = (LocalizedModule.mkLinearMap m.primeCompl M) (v i) := by
      rw [Module.Basis.isUnitSMul_apply]
      simpa [Algebra.smul_def] using hy i
    rw [IsLocalizedModule.map_linearCombination]
    rw [show ((LocalizedModule.mkLinearMap m.primeCompl M) ∘ v) = b' by
      funext i
      exact (hb' i).symm]
    rw [← b'.coe_repr_symm]
    exact b'.repr.symm.bijective
  let φ : (Fin n →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  obtain ⟨g, hgm, hφs⟩ :
      ∃ g ∉ m, Function.Surjective (LocalizedModule.map (Submonoid.powers g) φ) := by
    let Q := M ⧸ LinearMap.range φ
    have hQm : Subsingleton (LocalizedModule m.primeCompl Q) := by
      let e : (LocalizedModule m.primeCompl M ⧸ (LinearMap.range φ).localized m.primeCompl)
          ≃ₗ[Localization.AtPrime m] LocalizedModule m.primeCompl Q :=
        localizedQuotientEquiv m.primeCompl (LinearMap.range φ)
      have hquot : Subsingleton
          (LocalizedModule m.primeCompl M ⧸ (LinearMap.range φ).localized m.primeCompl) := by
        rw [Submodule.Quotient.subsingleton_iff]
        apply Submodule.restrictScalars_injective R
        rw [Submodule.restrictScalars_localized']
        rw [← LinearMap.range_localizedMap_eq_localized₀_range (m.primeCompl)
          (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime m)))]
        exact LinearMap.range_eq_top.mpr hφm.2
      exact e.symm.subsingleton
    obtain ⟨g, hgm, hQg⟩ := LocalizedModule.exists_subsingleton_away (M := Q) m
    refine ⟨g, hgm, ?_⟩
    rw [← LinearMap.range_eq_top]
    apply Submodule.restrictScalars_injective R
    change Submodule.restrictScalars R ((LocalizedModule.map (Submonoid.powers g)) φ).range =
      (⊤ : Submodule R (LocalizedModule (Submonoid.powers g) M))
    rw [eq_top_iff]
    intro y hy
    have hyker :
        y ∈ LinearMap.ker (LocalizedModule.map (Submonoid.powers g) (LinearMap.range φ).mkQ) := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ 0
    change y ∈ LinearMap.ker
        (IsLocalizedModule.map (Submonoid.powers g)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers g) Q)
          (LinearMap.range φ).mkQ) at hyker
    rw [LinearMap.ker_localizedMap_eq_localized₀_ker, Submodule.ker_mkQ,
      ← LinearMap.range_localizedMap_eq_localized₀_range (Submonoid.powers g)
        (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.Away g)))] at hyker
    rcases hyker with ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := IsLocalizedModule.surj (Submonoid.powers g)
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.Away g))) x
    change (z.2 : R) • x =
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.Away g))) z.1 at hz
    refine ⟨IsLocalizedModule.mk'
      (LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin n →₀ R)) z.1 z.2, ?_⟩
    apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap (Submonoid.powers g) M) z.2
    calc
      z.2 • (((LocalizedModule.map (Submonoid.powers g)) φ)
          (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers g)
            (Fin n →₀ R)) z.1 z.2))
          = (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (φ z.1) := by
            simp [LocalizedModule.map]
      _ = z.2 • (((IsLocalizedModule.map (Submonoid.powers g)
              (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.Away g)))
              (LocalizedModule.mkLinearMap (Submonoid.powers g) M)) φ) x) := by
            change (LocalizedModule.mkLinearMap (Submonoid.powers g) M) (φ z.1) =
              (z.2 : R) • (((IsLocalizedModule.map (Submonoid.powers g)
                (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.Away g)))
                (LocalizedModule.mkLinearMap (Submonoid.powers g) M)) φ) x)
            rw [← LinearMap.map_smul]
            rw [hz]
            rw [IsLocalizedModule.map_apply]
  refine ⟨g, hgm, ?_⟩
  let A := Localization.Away g
  let Mg := LocalizedModule.Away g M
  let Fg := LocalizedModule.Away g (Fin n →₀ R)
  let φg : Fg →ₗ[A] Mg := LocalizedModule.map (Submonoid.powers g) φ
  have hφs' : Function.Surjective φg := hφs
  have hφg_bij : Function.Bijective φg := by
    refine bijective_of_localized_maximal φg ?_
    intro 𝔪 h𝔪
    have h01A : (0 : A) ≠ 1 := by
      intro h01
      apply h𝔪.ne_top
      simp [Ideal.eq_top_iff_one, ← h01]
    have : Nontrivial A := ⟨⟨0, 1, h01A⟩⟩
    let B := Localization.AtPrime 𝔪
    let F𝔪 := LocalizedModule 𝔪.primeCompl Fg
    let M𝔪 := LocalizedModule 𝔪.primeCompl Mg
    let φ𝔪 : F𝔪 →ₗ[B] M𝔪 := LocalizedModule.map 𝔪.primeCompl φg
    have hφ𝔪_surj : Function.Surjective φ𝔪 :=
      LocalizedModule.map_surjective 𝔪.primeCompl φg hφs'
    have : Module.Free B M𝔪 := Module.free_of_flat_of_isLocalRing
    have : Module.Free A Fg := Module.free_of_isLocalizedModule (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin n →₀ R))
    have : Module.Free B F𝔪 := Module.free_of_isLocalizedModule 𝔪.primeCompl
      (LocalizedModule.mkLinearMap 𝔪.primeCompl Fg)
    have hfinFg : Module.finrank A Fg = n := by
      calc
        Module.finrank A Fg = Module.finrank R (Fin n →₀ R) := by
          exact Module.finrank_of_isLocalizedModule_of_free A (Submonoid.powers g)
            (LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin n →₀ R))
        _ = n := by
          rw [Module.finrank_finsupp_self, Fintype.card_fin]
    have hfinF𝔪 : Module.finrank B F𝔪 = n := by
      calc
        Module.finrank B F𝔪 = Module.finrank A Fg := by
          exact Module.finrank_of_isLocalizedModule_of_free B 𝔪.primeCompl
            (LocalizedModule.mkLinearMap 𝔪.primeCompl Fg)
        _ = n := hfinFg
    have hrankMg : rankAtStalk Mg ⟨𝔪, inferInstance⟩ = n := by
      let P : PrimeSpectrum A := ⟨𝔪, inferInstance⟩
      let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A) P
      obtain ⟨m', hm', hqm'⟩ := Ideal.exists_le_maximal q.asIdeal q.2.1
      let e : Mg ≃ₗ[A] A ⊗[R] M := LocalizedModule.equivTensorProduct (Submonoid.powers g) M
      calc
        rankAtStalk Mg P = rankAtStalk (A ⊗[R] M) P := congr_fun (rankAtStalk_eq_of_equiv e) P
        _ = rankAtStalk M q := by rw [rankAtStalk_baseChange]
        _ = rankAtStalk M ⟨m', hm'.isPrime⟩ := rankAtStalk_eq_of_le_of_finite_of_flat hqm'
        _ = n := h m'
    let bF : Basis (Fin n) B F𝔪 := Module.finBasisOfFinrankEq B F𝔪 hfinF𝔪
    let bM : Basis (Fin n) B M𝔪 := Module.finBasisOfFinrankEq B M𝔪 hrankMg
    let e : F𝔪 ≃ₗ[B] M𝔪 := bF.repr ≪≫ₗ bM.repr.symm
    let ψ : Module.End B F𝔪 := e.symm.toLinearMap ∘ₗ φ𝔪
    have hψ_surj : Function.Surjective ψ := e.symm.surjective.comp hφ𝔪_surj
    have hψ_inj : Function.Injective ψ := Module.End.injective_of_surjective B F𝔪 hψ_surj
    exact ⟨fun x y hxy ↦ hψ_inj (congr_arg e.symm hxy), hφ𝔪_surj⟩
  have : Module.Free A Fg := Module.free_of_isLocalizedModule (Submonoid.powers g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (Fin n →₀ R))
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φg hφg_bij)

end Free

section FinitePresentation

-- porved in [#39109](https://github.com/leanprover-community/mathlib4/pull/39109)
theorem FinitePresentation.of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    Module.FinitePresentation R M :=
  sorry

theorem FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant
    [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsMaximal], rankAtStalk M ⟨p, inferInstance⟩ = n) :
    Module.FinitePresentation R M := by
  let s : Set R := {g | Module.Free (Localization.Away g) (LocalizedModule.Away g M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra! hs
    obtain ⟨m, _, hsm⟩ := Ideal.exists_le_maximal _ hs
    obtain ⟨g, hgm, hfree⟩ :=
      Free.away_of_finite_of_flat_of_rankAtStalk_constant M m (fun p _ ↦ by simp [h p, h m])
    exact hgm (hsm (Submodule.mem_span_of_mem hfree))
  refine FinitePresentation.of_localizationSpan s hs (fun ⟨g, hg⟩ ↦ ?_)
  simp only [Set.mem_setOf_eq, s] at hg
  exact finitePresentation_of_projective (Localization.Away g) (LocalizedModule.Away g M)

end FinitePresentation

section Invertible

open IsLocalizedModule IsLocalization

open scoped TensorProduct

theorem Invertible.of_isLocalized_maximal [Module.Finite R M]
    (Rₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], CommRing (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Algebra R (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalization.AtPrime (Rₚ m) m]
    (Mₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], AddCommGroup (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module R (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module (Rₚ m) (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsScalarTower R (Rₚ m) (Mₚ m)]
    (f : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₚ m)
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalizedModule.AtPrime m (f m)]
    (h : ∀ (m : Ideal R) [m.IsMaximal], Module.Invertible (Rₚ m) (Mₚ m)) :
    Module.Invertible R M where
  bijective := by
    have : Flat R M := by
      refine flat_of_isLocalized_maximal R M Mₚ f (fun m _ ↦ ?_)
      have : Flat R (Rₚ m) := IsLocalization.flat (Rₚ m) m.primeCompl
      exact Flat.trans R (Rₚ m) (Mₚ m)
    have : Module.FinitePresentation R M := by
      refine Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant 1 (fun m _ ↦ ?_)
      have : IsLocalRing (Rₚ m) := IsLocalization.AtPrime.isLocalRing (Rₚ m) m
      have hfree : Module.Free (Rₚ m) (Mₚ m) := Module.free_of_flat_of_isLocalRing
      let e : LocalizedModule m.primeCompl M ≃ₗ[R] Localization.AtPrime m :=
        IsLocalizedModule.linearEquiv m.primeCompl (LocalizedModule.mkLinearMap _ M) (f m) ≪≫ₗ
          (Invertible.free_iff_linearEquiv.mp hfree).some.restrictScalars R ≪≫ₗ
            (algEquiv m.primeCompl (Localization.AtPrime m) (Rₚ m)).symm.toLinearEquiv
      exact (e.extendScalarsOfIsLocalization m.primeCompl (Localization.AtPrime m)).finrank_eq.trans
        (CommSemiring.finrank_self (Localization.AtPrime m))
    let ϕ (m : Ideal R) [m.IsMaximal] := TensorProduct.map
      (mapExtendScalars m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) (Rₚ m)) (f m)
    refine bijective_of_isLocalized_maximal _ ϕ Rₚ
      (fun m _ ↦ Algebra.linearMap R (Rₚ m)) (contractLeft R M) (fun m _ ↦ ?_)
    let ψ : Module.Dual (Rₚ m) (Mₚ m) ⊗[Rₚ m] Mₚ m ≃ₗ[R] Module.Dual (Rₚ m) (Mₚ m) ⊗[R] Mₚ m :=
      (moduleTensorEquiv m.primeCompl (Rₚ m) (Module.Dual (Rₚ m) (Mₚ m)) (Mₚ m)).restrictScalars R
    have hψ : (map m.primeCompl (ϕ m) (Algebra.linearMap R (Rₚ m))) (contractLeft R M) =
        (contractLeft (Rₚ m) (Mₚ m)).restrictScalars R ∘ₗ ψ.symm.toLinearMap := by
      apply IsLocalizedModule.ext m.primeCompl (ϕ m) (map_units (Algebra.linearMap R (Rₚ m)))
      ext α x
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply]
      change _ = mapExtendScalars m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) (Rₚ m) α (f m x)
      simp
    simp [hψ, (h m).bijective.comp ψ.symm.bijective]

theorem Invertible.of_localized_maximal [Module.Finite R M]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) :
    Module.Invertible R M :=
  of_isLocalized_maximal (fun m _ ↦ Localization.AtPrime m) (fun m _ ↦ LocalizedModule.AtPrime m M)
    (fun m _ ↦ LocalizedModule.mkLinearMap m.primeCompl M) h

end Invertible

end Module
