import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import QuillenSuslin.FiniteFreeResolution.Basic

universe u

open CategoryTheory

variable (R : Type u) [CommRing R]

theorem hasFiniteFreeResolution_of_hasProjectiveDimensionLE
    [IsRegularLocalRing R]
    [Small R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] {n : ℕ}
    [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasFiniteFreeResolution R M := by
  induction n generalizing M with
  | zero =>
      have hproj : Projective (ModuleCat.of R M) :=
        (projective_iff_hasProjectiveDimensionLT_one _).2 inferInstance
      have hmodproj : Module.Projective R M := (IsProjective.iff_projective (R := R) M).2 hproj
      letI : Module.Projective R M := hmodproj
      letI : Module.Free R M := Module.free_of_flat_of_isLocalRing
      exact hasFiniteFreeResolution_of_finite_of_free M
  | succ n ih =>
      obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
      let S := LinearMap.shortComplexKer f
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hproj : Projective S.X₂ := by
        change Projective (ModuleCat.of R P)
        infer_instance
      have hker : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
        simpa [S, HasProjectiveDimensionLE] using
          (hS.hasProjectiveDimensionLT_X₃_iff n hproj).mp inferInstance
      letI := hker
      letI : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.of_injective (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype
      have hfreeP : HasFiniteFreeResolution R P := hasFiniteFreeResolution_of_finite_of_free P
      have hker' : HasFiniteFreeResolution R (LinearMap.ker f) := ih
      exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle
        (P₁ := LinearMap.ker f) (P₂ := P) (P₃ := M)
        (f := (LinearMap.ker f).subtype) (g := f)
        (LinearMap.ker f).injective_subtype
        hf
        (LinearMap.exact_subtype_ker_map f)
        hker'
        hfreeP

theorem hasFiniteFreeResolutionLength_localized
    [Nontrivial R] {M : Type u} [AddCommGroup M] [Module R M] (S : Submonoid R) {n : ℕ}
    (h : HasFiniteFreeResolutionLength R M n) :
    HasFiniteFreeResolutionLength (Localization S) (LocalizedModule S M) n := by
  induction h with
  | zero P =>
      let b := Module.Free.chooseBasis R P
      haveI : Finite (Module.Free.ChooseBasisIndex R P) := Module.Finite.finite_basis b
      let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S P)
      letI : Module.Free (Localization S) (LocalizedModule S P) :=
        Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S P)
      letI : Module.Finite (Localization S) (LocalizedModule S P) := Module.Finite.of_basis bS
      exact HasFiniteFreeResolutionLength.zero (LocalizedModule S P)
  | succ P n F f hf hker ih =>
      let b := Module.Free.chooseBasis R F
      haveI : Finite (Module.Free.ChooseBasisIndex R F) := Module.Finite.finite_basis b
      let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S F)
      letI : Module.Free (Localization S) (LocalizedModule S F) :=
        Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S F)
      letI : Module.Finite (Localization S) (LocalizedModule S F) := Module.Finite.of_basis bS
      have hker' :
          HasFiniteFreeResolutionLength (Localization S)
            (LinearMap.ker (LocalizedModule.map S f)) n := by
        let eKer :
            LocalizedModule S (LinearMap.ker f) ≃ₗ[Localization S]
              LinearMap.ker (LocalizedModule.map S f) :=
          (Submodule.localizedEquiv (p := S) (M' := LinearMap.ker f)).symm ≪≫ₗ
            LinearEquiv.ofEq _ _
              (LinearMap.localized'_ker_eq_ker_localizedMap
                (Localization S) S (LocalizedModule.mkLinearMap S F)
                (LocalizedModule.mkLinearMap S P) f)
        exact hasFiniteFreeResolutionLength_of_linearEquiv eKer ih
      exact HasFiniteFreeResolutionLength.succ (LocalizedModule S P) n
        (LocalizedModule S F) (LocalizedModule.map S f)
        (LocalizedModule.map_surjective S f hf) hker'

theorem hasFiniteFreeResolution_localized
    [Nontrivial R] {M : Type u} [AddCommGroup M] [Module R M] (S : Submonoid R)
    (h : HasFiniteFreeResolution R M) :
    HasFiniteFreeResolution (Localization S) (LocalizedModule S M) := by
  rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
  let b := Module.Free.chooseBasis R F
  haveI : Finite (Module.Free.ChooseBasisIndex R F) := Module.Finite.finite_basis b
  let bS := b.ofIsLocalizedModule (Localization S) S (LocalizedModule.mkLinearMap S F)
  letI : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S F)
  letI : Module.Finite (Localization S) (LocalizedModule S F) := Module.Finite.of_basis bS
  have hk0 :
      HasFiniteFreeResolutionLength (Localization S) (LocalizedModule S (LinearMap.ker f)) n :=
    hasFiniteFreeResolutionLength_localized (R := R) S hn
  let eKer :
      LocalizedModule S (LinearMap.ker f) ≃ₗ[Localization S]
        LinearMap.ker (LocalizedModule.map S f) :=
    (Submodule.localizedEquiv (p := S) (M' := LinearMap.ker f)).symm ≪≫ₗ
      LinearEquiv.ofEq _ _
        (LinearMap.localized'_ker_eq_ker_localizedMap
          (Localization S) S (LocalizedModule.mkLinearMap S F)
          (LocalizedModule.mkLinearMap S M) f)
  have hk :
      HasFiniteFreeResolutionLength (Localization S)
        (LinearMap.ker (LocalizedModule.map S f)) n :=
    hasFiniteFreeResolutionLength_of_linearEquiv eKer hk0
  exact ⟨LocalizedModule S F, inferInstance, inferInstance, inferInstance, inferInstance,
    LocalizedModule.map S f, LocalizedModule.map_surjective S f hf, n, hk⟩
