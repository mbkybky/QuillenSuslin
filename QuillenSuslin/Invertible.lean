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

lemma exists_isLocalizedModule_map_surjective_of_surjective [Module.FinitePresentation R M]
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module (Rₚ) Mₚ] [IsScalarTower R (Rₚ) Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    {Nₚ : Type*} [AddCommGroup Nₚ] [Module R Nₚ] [Module (Rₚ) Nₚ] [IsScalarTower R (Rₚ) Nₚ]
    (g : N →ₗ[R] Nₚ) [IsLocalizedModule.AtPrime p g] {ϕ : Mₚ →ₗ[Rₚ] Nₚ} (hϕ : Function.Surjective ϕ) :
    ∃ φ : M →ₗ[R] N, Function.Surjective (IsLocalizedModule.map p.primeCompl f g φ) := by
  sorry

lemma exists_localizedModule_map_away_surjective_of_map_atPrime_surjective [Module.Finite R N]
    (p : Ideal R) [p.IsPrime]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  sorry

lemma bijective_of_surjective_of_finite_of_free_of_finrank_eq
    [Module.Finite R M] [Module.Free R M] [Module.Free R N]
    (h : finrank R M = finrank R N) {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Bijective f := by
  sorry

lemma localized_map_bijective_of_surjective_of_rankAtStalk_eq [Module.Finite R M] [Module.Flat R M]
    [Module.Finite R N] [Module.Flat R N] (a : R) {φ : M →ₗ[R] N}
    (hφs : Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ))
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Rₐ := Localization.Away a
  let Mₐ := LocalizedModule.Away a M
  let Nₐ := LocalizedModule.Away a N
  let φₐ : Mₐ →ₗ[Rₐ] Nₐ := LocalizedModule.map (Submonoid.powers a) φ
  refine bijective_of_localized_maximal (φₐ.restrictScalars R) (fun m _ ↦ ?_)
  have : Function.Surjective (φₐ.restrictScalars R) := hφs
  have hφₐ : Function.Surjective (LocalizedModule.map m.primeCompl (φₐ.restrictScalars R)) :=
    LocalizedModule.map_surjective _ _ hφs
  let aₘ : Localization.AtPrime m := algebraMap R (Localization.AtPrime m) a
  have f : LocalizedModule.AtPrime m M →ₗ[Localization.AtPrime m] LocalizedModule.AtPrime m Mₐ :=
    LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  have : IsLocalizedModule.Away aₘ f := sorry
  have g : LocalizedModule.AtPrime m N →ₗ[Localization.AtPrime m] LocalizedModule.AtPrime m Nₐ :=
    LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
  have : IsLocalizedModule.Away aₘ g := sorry
  sorry

variable (M) in
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant [Module.Finite R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    ∃ (f : R) (_ : f ∉ p), Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  let n := rankAtStalk M ⟨p, inferInstance⟩
  have : Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
    Module.free_of_flat_of_isLocalRing
  let b : Basis (Fin n) (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
    finBasisOfFinrankEq (Localization.AtPrime p) (LocalizedModule.AtPrime p M) rfl
  obtain ⟨φ, hφs⟩ := exists_isLocalizedModule_map_surjective_of_surjective p (Localization.AtPrime p)
    (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime p)))
      (LocalizedModule.mkLinearMap p.primeCompl M) <| LinearEquiv.surjective <|
        (finBasisOfFinrankEq (Localization.AtPrime p) (LocalizedModule.AtPrime p M) rfl).repr.symm
  obtain ⟨a, hap, hφs⟩ := by
    refine exists_localizedModule_map_away_surjective_of_map_atPrime_surjective p φ ?_
    sorry
  refine ⟨a, hap, ?_⟩
  let Rₐ := Localization.Away a
  let Mₐ := LocalizedModule.Away a M
  let Fₐ := LocalizedModule.Away a (Fin n →₀ R)
  have : Module.Free Rₐ Fₐ := Module.free_of_isLocalizedModule (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) (Fin n →₀ R))
  let φₐ : Fₐ →ₗ[Rₐ] Mₐ := LocalizedModule.map (Submonoid.powers a) φ
  have hφbij : Function.Bijective φₐ := by
    refine localized_map_bijective_of_surjective_of_rankAtStalk_eq a hφs (fun m _ ↦ ?_)
    sorry
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φₐ hφbij)

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
