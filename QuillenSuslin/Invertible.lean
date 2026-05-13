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

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

section Free

open LocalizedModule

lemma rankAtStalk_isBaseChange [Module.Finite R M] [Module.Flat R M] {S Mₛ : Type*} [CommRing S]
    [Algebra R S] [AddCommGroup Mₛ] [Module R Mₛ] [Module S Mₛ] [IsScalarTower R S Mₛ]
    {f : M →ₗ[R] Mₛ} (hf : IsBaseChange S f) (p : PrimeSpectrum S) :
    rankAtStalk Mₛ p = rankAtStalk M (p.comap (algebraMap R S)) := by
  simp [rankAtStalk_eq_of_equiv hf.equiv.symm, rankAtStalk_baseChange]

lemma _root_.LocalizedModule.isBaseChange (S : Submonoid R)
    (M : Type*) [AddCommGroup M] [Module R M] :
    IsBaseChange (Localization S) (LocalizedModule.mkLinearMap S M) :=
  IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat [Module.Finite R M] [Module.Flat R M]
    {p q : PrimeSpectrum R} (hpq : p ≤ q) : rankAtStalk M p = rankAtStalk M q := by
  let S := Localization.AtPrime q.asIdeal
  have hpr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_comap_range S q.asIdeal.primeCompl]
    exact disjoint_compl_left_iff.mpr hpq
  have : Module.Free S (LocalizedModule q.asIdeal.primeCompl M) := free_of_flat_of_isLocalRing
  have := IsLocalizedModule.isBaseChange q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) (mkLinearMap q.asIdeal.primeCompl M)
  rw [← hpr.choose_spec, ← rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange q.asIdeal.primeCompl M), rankAtStalk_eq_finrank_of_free]
  simp [rankAtStalk]

variable (M) in
lemma rankAtStalk_eq_of_le_of_finite_of_flat' [Module.Finite R M] [Module.Flat R M]
    {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime] (hpq : p ≤ q) : rankAtStalk M ⟨p, hp⟩ = rankAtStalk M ⟨q, hq⟩ :=
  rankAtStalk_eq_of_le_of_finite_of_flat M hpq

/-
lemma wedqe (S : Submonoid R) (Rₐ : Type*) [CommRing Rₐ] [Algebra R Rₐ] [IsLocalization S Rₐ]
    (Mₐ : Type*) [AddCommGroup Mₐ] [Module R Mₐ] [Module Rₐ Mₐ] [IsScalarTower R Rₐ Mₐ]
    (p : PrimeSpectrum Rₐ) :
    rankAtStalk Mₐ p = rankAtStalk M (p.comap (algebraMap R Rₐ)) := by
  sorry
 -/

lemma exists_isLocalizedModule_map_surjective_of_surjective [Module.FinitePresentation R M]
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module (Rₚ) Mₚ] [IsScalarTower R (Rₚ) Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    {Nₚ : Type*} [AddCommGroup Nₚ] [Module R Nₚ] [Module (Rₚ) Nₚ] [IsScalarTower R (Rₚ) Nₚ]
    (g : N →ₗ[R] Nₚ) [IsLocalizedModule.AtPrime p g] {ϕ : Mₚ →ₗ[Rₚ] Nₚ} (hϕ : Function.Surjective ϕ) :
    ∃ φ : M →ₗ[R] N, Function.Surjective (IsLocalizedModule.map p.primeCompl f g φ) := by
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl g (ϕ.restrictScalars R ∘ₗ f)
  refine ⟨φ, ?_⟩
  have hmap : IsLocalizedModule.map p.primeCompl f g φ = s • ϕ.restrictScalars R := by
    apply IsLocalizedModule.ext p.primeCompl f (IsLocalizedModule.map_units g)
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply] using
      LinearMap.congr_fun hφ x
  rw [hmap]
  intro y
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (S := p.primeCompl) (f := g) s)).2 y
  obtain ⟨x, rfl⟩ := hϕ z
  exact ⟨x, hz⟩

lemma _root_.LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker (S : Submonoid R)
    (φ : M →ₗ[R] N) :
    Function.Surjective (map S φ) ↔ Subsingleton (LocalizedModule S (N ⧸ φ.range)) := by
  rw [(localizedQuotientEquiv S φ.range).symm.subsingleton_congr]
  rw [Submodule.Quotient.subsingleton_iff, Submodule.localized]
  rw [LinearMap.localized'_range_eq_range_localizedMap (Localization S) S
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N), LinearMap.range_eq_top]
  rfl

lemma exists_localizedModule_map_away_surjective_of_map_atPrime_surjective [Module.Finite R N]
    (p : Ideal R) [p.IsPrime]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_subsingleton_away p

theorem _root_.Function.bijective_of_subsingleton' {α β : Type*} [Nonempty α] [Subsingleton α]
    [Subsingleton β] (f : α → β) : Function.Bijective f :=
  ⟨f.injective_of_subsingleton, f.surjective_to_subsingleton⟩

lemma bijective_of_surjective_of_finite_of_free_of_finrank_eq
    [Module.Finite R M] [Module.Free R M] [Module.Free R N]
    (h : finrank R M = finrank R N) {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Bijective f := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    have : Subsingleton N := Module.subsingleton R N
    exact Function.bijective_of_subsingleton' f
  · have : Module.Finite R N := Module.Finite.of_surjective f hf
    let +nondep e : M ≃ₗ[R] N := LinearEquiv.ofFinrankEq M N h
    have hinj : Function.Injective (e.symm.toLinearMap ∘ₗ f) :=
      Module.End.injective_of_surjective R M (e.symm.surjective.comp hf)
    exact ⟨fun x y hxy ↦ hinj (by simp [hxy]), hf⟩

lemma localized_map_bijective_of_surjective_of_rankAtStalk_eq [Module.Finite R M] [Module.Flat R M]
    [Module.Finite R N] [Module.Flat R N] (a : R) {φ : M →ₗ[R] N}
    (hφs : Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ))
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Mₐ := LocalizedModule.Away a M
  let Nₐ := LocalizedModule.Away a N
  refine bijective_of_localized_maximal (map (Submonoid.powers a) φ) (fun m _ ↦ ?_)
  have : Free (Localization.AtPrime m) (LocalizedModule.AtPrime m Mₐ) := free_of_flat_of_isLocalRing
  have : Free (Localization.AtPrime m) (LocalizedModule.AtPrime m Nₐ) := free_of_flat_of_isLocalRing
  refine bijective_of_surjective_of_finite_of_free_of_finrank_eq ?_
    (LocalizedModule.map_surjective m.primeCompl (map (Submonoid.powers a) φ) hφs)
  change rankAtStalk Mₐ ⟨m, inferInstance⟩ = rankAtStalk Nₐ ⟨m, inferInstance⟩
  rw [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) M)]
  rw [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) N)]
  obtain ⟨𝔪, _, hm𝔪⟩ : ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
      (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ ≤ 𝔪 :=
    Ideal.exists_le_maximal (m.comap (algebraMap R (Localization.Away a))) Ideal.IsPrime.ne_top'
  simp [rankAtStalk_eq_of_le_of_finite_of_flat' _ hm𝔪, h 𝔪]

variable (M) in
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant [Module.Finite R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    ∃ (f : R) (_ : f ∉ p), Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  let Rₚ := Localization.AtPrime p
  let n := rankAtStalk M ⟨p, inferInstance⟩
  have : Module.Free Rₚ (LocalizedModule.AtPrime p M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨φ, hφps⟩ := exists_isLocalizedModule_map_surjective_of_surjective p Rₚ
    (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)) (mkLinearMap p.primeCompl M)
      (finBasisOfFinrankEq Rₚ (LocalizedModule.AtPrime p M) rfl).repr.symm.surjective
  obtain ⟨a, hap, hφas⟩ := by
    refine exists_localizedModule_map_away_surjective_of_map_atPrime_surjective p φ ?_
    simpa [LocalizedModule.coe_map_eq (Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ))
      (LocalizedModule.mkLinearMap p.primeCompl M)]
  have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n →₀ R)) :=
    free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n →₀ R))
  let φₐ : LocalizedModule.Away a (Fin n →₀ R) →ₗ[Localization.Away a] LocalizedModule.Away a M :=
    LocalizedModule.map (Submonoid.powers a) φ
  exact ⟨a, hap, Module.Free.of_equiv <| LinearEquiv.ofBijective φₐ <|
    localized_map_bijective_of_surjective_of_rankAtStalk_eq a hφas <| fun m _ ↦ by
      simp [Module.rankAtStalk_eq_finrank_of_free, n, h m]⟩

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
