/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

public section

namespace Module

open scoped TensorProduct

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

section Free

open LocalizedModule

-- [Mathlib.RingTheory.Localization.BaseChange]
lemma _root_.LocalizedModule.isBaseChange (S : Submonoid R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsBaseChange (Localization S) (LocalizedModule.mkLinearMap S M) :=
  IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

-- [Mathlib.RingTheory.Spectrum.Prime.FreeLocus]
lemma rankAtStalk_isBaseChange [Module.Finite R M] [Module.Flat R M] {S Mₛ : Type*} [CommRing S]
    [Algebra R S] [AddCommGroup Mₛ] [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ]
    {f : M →ₗ[R] Mₛ} (hf : IsBaseChange S f) (p : PrimeSpectrum S) :
    rankAtStalk Mₛ p = rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat [Module.Finite R M] [Module.Flat R M]
    {p q : PrimeSpectrum R} (hpq : p ≤ q) : rankAtStalk M p = rankAtStalk M q := by
  let S := Localization.AtPrime q.asIdeal
  have hpr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  have : Module.Free S (LocalizedModule q.asIdeal.primeCompl M) := free_of_flat_of_isLocalRing
  rw [← hpr.choose_spec, ← rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange q.asIdeal.primeCompl M), rankAtStalk_eq_finrank_of_free]
  simp [rankAtStalk]

variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat' [Module.Finite R M] [Module.Flat R M]
    {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime] (hpq : p ≤ q) :
    rankAtStalk M ⟨p, hp⟩ = rankAtStalk M ⟨q, hq⟩ :=
  rankAtStalk_eq_of_le_of_finite_of_flat M hpq

-- [Mathlib.Algebra.Module.FinitePresentation]
/-- Let `M` be a finitely presented `R`-module, `N` be a `R`-module, `S` be a submonoid of `R`,
`Mₚ` be the localization of `M` at `S`, `Nₚ` be the localization of `N` at `S`. Then any surjective
linear map `ϕ : Mₚ →ₗ[R] Nₚ` lifts to a linear map `φ : M →ₗ[R] N` that is surjective after
localization at `S`. -/
lemma exists_localizedMap_surjective_of_surjective [Module.FinitePresentation R M]
    (S : Submonoid R) {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule S f] {Nₚ : Type*} [AddCommGroup Nₚ] [Module R Nₚ]
    (g : N →ₗ[R] Nₚ) [IsLocalizedModule S g] {ϕ : Mₚ →ₗ[R] Nₚ} (hϕ : Function.Surjective ϕ) :
    ∃ φ : M →ₗ[R] N, Function.Surjective (IsLocalizedModule.map S f g φ) := by
  obtain ⟨φ, s, hφ⟩ := FinitePresentation.exists_lift_of_isLocalizedModule S g (ϕ ∘ₗ f)
  refine ⟨φ, ?_⟩
  have hmap : IsLocalizedModule.map S f g φ = s • ϕ := by
    apply IsLocalizedModule.linearMap_ext S f g
    simp [IsLocalizedModule.map_comp, hφ, LinearMap.smul_comp]
  simpa only [hmap] using! ((End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).2.comp hϕ

-- [Mathlib.Algebra.Module.LocalizedModule.Submodule]
lemma _root_.LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker (S : Submonoid R)
    (φ : M →ₗ[R] N) :
    Function.Surjective (map S φ) ↔ Subsingleton (LocalizedModule S (N ⧸ φ.range)) := by
  rw [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr]
  rw [Submodule.Quotient.subsingleton_iff, Submodule.localized]
  rw [LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N), LinearMap.range_eq_top]
  rfl

-- [Mathlib.RingTheory.Support]
lemma exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective [Module.Finite R N]
    (p : Ideal R) [p.IsPrime]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

-- [Mathlib.LinearAlgebra.FiniteDimensional.Basic]
lemma bijective_of_surjective_of_finite_of_free_of_finrank_eq [StrongRankCondition R]
    [Module.Finite R M] [Module.Free R M] [Module.Free R N]
    (h : finrank R M = finrank R N) {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Bijective f := by
  have : Module.Finite R N := Module.Finite.of_surjective f hf
  let +nondep e : M ≃ₗ[R] N := LinearEquiv.ofFinrankEq M N h
  have hinj : Function.Injective (e.symm.toLinearMap ∘ₗ f) :=
    Module.End.injective_of_surjective R M (e.symm.surjective.comp hf)
  exact ⟨fun x y hxy ↦ hinj (by simp [hxy]), hf⟩

attribute [local instance] Module.free_of_flat_of_isLocalRing

lemma localizedMap_bijective_of_surjective_of_rankAtStalk_eq [Module.Finite R M] [Module.Flat R M]
    [Module.Finite R N] [Module.Flat R N] (a : R) {φ : M →ₗ[R] N}
    (hφs : Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ))
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Mₐ := LocalizedModule.Away a M
  let Nₐ := LocalizedModule.Away a N
  refine bijective_of_localized_maximal (map (Submonoid.powers a) φ) <| fun m _ ↦
    bijective_of_surjective_of_finite_of_free_of_finrank_eq ?_
      (LocalizedModule.map_surjective m.primeCompl (map (Submonoid.powers a) φ) hφs)
  change rankAtStalk Mₐ ⟨m, inferInstance⟩ = rankAtStalk Nₐ ⟨m, inferInstance⟩
  rw [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) M)]
  rw [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) N)]
  obtain ⟨𝔪, _, hm𝔪⟩ : ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
      (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ ≤ 𝔪 :=
    Ideal.exists_le_maximal (m.comap (algebraMap R (Localization.Away a))) Ideal.IsPrime.ne_top'
  simp [rankAtStalk_eq_of_le_of_finite_of_flat' _ hm𝔪, h 𝔪]

variable (M) in
/-- Let `M` be a finite flat `R`-module, `p` be a prime ideal of `R`. If `rankAtStalk M` is
constant, then there exists `a ∉ p` such that the `M` is free after localization away from `a`. -/
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant [Module.Finite R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    ∃ (a : R) (_ : a ∉ p), Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  · let Rₚ := Localization.AtPrime p
    let n := rankAtStalk M ⟨p, inferInstance⟩
    let f : (Fin n →₀ R) →ₗ[R] Fin n →₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
    let g : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
    obtain ⟨φ, hφps⟩ := exists_localizedMap_surjective_of_surjective p.primeCompl f g
      ((finBasis Rₚ (LocalizedModule.AtPrime p M)).repr.restrictScalars R).symm.surjective
    obtain ⟨a, hap, hφas⟩ := by
      refine exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p φ ?_
      simpa [LocalizedModule.coe_map_eq f g]
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n →₀ R)) :=
      free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n →₀ R))
    let φₐ : LocalizedModule.Away a (Fin n →₀ R) →ₗ[Localization.Away a] LocalizedModule.Away a M :=
      LocalizedModule.map (Submonoid.powers a) φ
    exact ⟨a, hap, Module.Free.of_equiv <| LinearEquiv.ofBijective φₐ <|
      localizedMap_bijective_of_surjective_of_rankAtStalk_eq a hφas <| fun m _ ↦ by simp [n, h m]⟩

end Free

section FinitePresentation

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
      let e : LocalizedModule.AtPrime m M ≃ₗ[R] Localization.AtPrime m :=
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
      apply IsLocalizedModule.linearMap_ext m.primeCompl (ϕ m) (Algebra.linearMap R (Rₚ m))
      ext α x
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
        TensorProduct.curry_apply, LinearMap.coe_comp, Function.comp_apply, map_apply]
      exact (IsLocalizedModule.map_apply m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) α x).symm
    simp [hψ, (h m).bijective.comp ψ.symm.bijective]

/-- Let `M` be a finite `R`-module, then `M` is invertible if `Mₘ` is invertible for any every
maximal ideal `m` of `R`. -/
theorem Invertible.of_localized_maximal [Module.Finite R M]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) :
    Module.Invertible R M :=
  of_isLocalized_maximal (fun m _ ↦ Localization.AtPrime m) (fun m _ ↦ LocalizedModule.AtPrime m M)
    (fun m _ ↦ LocalizedModule.mkLinearMap m.primeCompl M) h

end Invertible

end Module
