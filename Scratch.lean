import Mathlib.RingTheory.RegularLocalRing.Localization
import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.PicardGroup
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import QuillenSuslin.FiniteFreeResolution.StablyFree
import QuillenSuslin.UFD.Lemmas

#check Module.projective_of_localization_maximal
#check Module.freeLocus_eq_univ_iff
#check Module.freeLocus_eq_univ
#check Module.free_of_flat_of_isLocalRing
#check Module.Invertible.exists_linearEquiv_ideal
#check CommRing.Pic.instSubsingletonOfIsLocalRing
#check CommRing.Pic.instFreeOfSubsingleton
#check CommRing.Pic.mk_eq_one_iff_free
#check Module.Invertible.free_iff_linearEquiv
#check Module.Invertible.rank_eq_one
#check Module.Invertible.of_isLocalization
#check Module.Invertible.instLocalizationLocalizedModule
#check Submodule.rank_le_one_iff_isPrincipal
#check quotient_span_singleton
#check ufd_of_ufd_away_of_prime
#check Ideal.isPrincipal_of_isPrincipal_map_away_of_prime
#check Localization.AtPrime.map_eq_maximalIdeal
#check Localization.AtPrime.comap_maximalIdeal
#check IsLocalization.localizationLocalizationAtPrimeIsoLocalization
#check projectiveDimension_ne_top_of_isRegularLocalRing
#check isDomain_of_isRegularLocalRing
#check Module.mem_freeLocus_of_isLocalization
#check Module.freeLocus_eq_univ_iff
#check Module.freeLocus_eq_univ
#check Module.flat_of_localized_maximal
#check IsLocalization.coeSubmodule_isPrincipal
#check Submodule.range_unitsToPic
#check Submodule.mulExact_unitsToPic_mapAlgebra
#check Module.Flat.submoduleAlgebra
#check Module.Flat.submoduleAlgebraEquiv
#check rank_submodule_eq_one_iff
#check rank_submodule_le_one_iff
#check rank_submodule_le_one_iff'
#check bijective_of_isLocalized_maximal
#check injective_of_isLocalized_maximal
#check Module.Basis.equivFun
#check Finsupp.linearEquivFunOnFinite
#check LinearEquiv.ofFinrankEq
#check AlternatingMap.domLCongr
#check LinearMap.det
#check LinearMap.det_toMatrix
#check IsLocalizedModule.mapEquiv
#check IsLocalizedModule.linearEquiv
#check LinearEquiv.isUnit_det
#check Matrix.det_updateCol_add
#check Matrix.det_updateCol_smul

section Test

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def stableMatrix {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (m : M) :
  Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j =>
    if h : j = 0 then e.toFun (m, 0) i
    else e.toFun (0, Pi.basisFun R (Fin n) (Fin.pred j (by simpa using h))) i

noncomputable def stableBaseMatrix {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  stableMatrix e 0

noncomputable def stableMap {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) : M →ₗ[R] R where
  toFun m := (stableMatrix e m).det
  map_add' m₁ m₂ := by
    have hm :
        stableMatrix e (m₁ + m₂) =
          (stableBaseMatrix e).updateCol 0
            (e.toFun (m₁, 0) + e.toFun (m₂, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simpa [stableMatrix, stableBaseMatrix] using
          congrFun (map_add e (m₁, 0) (m₂, 0)) i
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm₁ :
        stableMatrix e m₁ =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m₁, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simpa [stableMatrix, stableBaseMatrix] using
          congrFun (map_smulₛₗ e r (m, 0)) i
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm₂ :
        stableMatrix e m₂ =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m₂, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simp [stableMatrix, stableBaseMatrix]
      · simp [stableMatrix, stableBaseMatrix, h]
    rw [hm, Matrix.det_updateCol_add, hm₁, hm₂]
  map_smul' r m := by
    have hm :
        stableMatrix e (r • m) =
          (stableBaseMatrix e).updateCol 0 (r • e.toFun (m, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simpa [stableMatrix, stableBaseMatrix, smul_eq_mul] using
          congrFun (map_smulₛₗ e r (m, 0)) i
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm' :
        stableMatrix e m =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simp [stableMatrix, stableBaseMatrix]
      · simp [stableMatrix, stableBaseMatrix, h]
    rw [hm, Matrix.det_updateCol_smul, hm']
    simp

theorem isUnit_stableMap_of_linearEquiv {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (u : M ≃ₗ[R] R) :
    IsUnit (stableMap e (u.symm 1)) := by
  let e' : (R × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R) :=
    (u.symm.prodCongr (LinearEquiv.refl R (Fin n → R))) ≪≫ₗ e
  have hmatrix :
      stableMatrix e (u.symm 1) =
        LinearMap.toMatrix
          (Pi.basisFun R (Fin (n + 1)))
          (Pi.basisFun R (Fin (n + 1)))
          (((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm ≪≫ₗ e').toLinearMap) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    by_cases h : j = 0
    · subst h
      have htail :
          Fin.tail (show Fin (n + 1) → R from Pi.single (0 : Fin (n + 1)) (1 : R)) = 0 := by
        funext k
        simp [Fin.tail_def]
      simpa [stableMatrix, e', htail]
    · simp [stableMatrix, e', h]
      have htail :
          Fin.tail (show Fin (n + 1) → R from Pi.single j (1 : R)) =
            Pi.basisFun R (Fin n) (j.pred (by simpa using h)) := by
        funext k
        rw [Fin.tail_def, Pi.basisFun_apply]
        change (show Fin (n + 1) → R from Pi.single j (1 : R)) k.succ =
          (show Fin n → R from Pi.single (j.pred (by simpa using h)) (1 : R)) k
        by_cases hk : k = j.pred (by simpa using h)
        · subst hk
          simp [Pi.single, Fin.succ_pred j (by simpa using h)]
        · have hne : k.succ ≠ j := by
            intro hEq
            apply hk
            exact Fin.succ_injective _ <| by
              simpa [Fin.succ_pred j (by simpa using h)] using hEq
          simp [Pi.single, hne, hk]
      simpa [stableMatrix, e', h, htail]
  change IsUnit ((stableMatrix e (u.symm 1)).det)
  rw [hmatrix]
  exact LinearEquiv.isUnit_det
    (((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm ≪≫ₗ e')
      : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (Pi.basisFun R (Fin (n + 1)))
    (Pi.basisFun R (Fin (n + 1)))

theorem stableMap_bijective_of_linearEquiv {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (u : M ≃ₗ[R] R) :
    Function.Bijective (stableMap e) := by
  let a : R := stableMap e (u.symm 1)
  have ha : IsUnit a := by
    simpa [a] using isUnit_stableMap_of_linearEquiv e u
  have hrepr : ∀ m, m = (u m) • u.symm 1 := by
    intro m
    apply u.injective
    simp
  have hm : ∀ m, stableMap e m = u m * a := by
    intro m
    rw [hrepr m, LinearMap.map_smul]
    simp [a, smul_eq_mul, mul_comm]
  constructor
  · intro m₁ m₂ h
    apply u.injective
    rcases ha with ⟨a', ha'⟩
    have h' : u m₁ * ↑a' = u m₂ * ↑a' := by
      simpa [hm m₁, hm m₂, ha'] using h
    have h'' := congrArg (fun x : R => x * ↑a'⁻¹) h'
    simpa [mul_assoc] using h''
  · intro b
    rcases ha with ⟨a', ha'⟩
    refine ⟨(b * ↑a'⁻¹) • u.symm 1, ?_⟩
    rw [hm]
    rw [← ha']
    simp [mul_assoc]

end Test
