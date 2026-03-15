import Mathlib.RingTheory.RegularLocalRing.Localization
import Mathlib.RingTheory.RegularLocalRing.GlobalDimension
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PicardGroup
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import QuillenSuslin.FiniteFreeResolution.Localization
import QuillenSuslin.FiniteFreeResolution.FreeOfLocalizedEq
import QuillenSuslin.UFD.Lemmas

universe u

#check isRegularLocalRing_localization

open CategoryTheory

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

private theorem Ideal.isPrincipal_of_free [IsDomain R] {I : Ideal R} [Module.Free R I] :
    I.IsPrincipal := by
  refine (Submodule.rank_le_one_iff_isPrincipal I).1 ?_
  calc
    Module.rank R I ≤ Module.rank R R := Submodule.rank_le I
    _ = 1 := Module.rank_self R

theorem regularLocalRing_isUFD : UniqueFactorizationMonoid R := by
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp hheight
  let K := Localization.AtPrime p
  have hregK : IsRegularLocalRing K := isRegularLocalRing_localization R p
  have hheight' : (p.height : WithBot ℕ∞) = 1 := by
    simpa [Ideal.height_eq_primeHeight] using
      congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hheight
  have hdimK : ringKrullDim K = 1 := by
    simpa [K] using
      (IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)).trans hheight'
  have hDVR : IsDiscreteValuationRing K :=
    IsDiscreteValuationRing.of_isRegularLocalRing_of_ringKrullDim_eq_one (R := K) hdimK
  have hPID : IsPrincipalIdealRing K := by infer_instance
  sorry

instance : UniqueFactorizationMonoid R := regularLocalRing_isUFD R

/-!
Proof notes from Serre duality.pdf, §8, pages 46-47.

- 8.12: a projective module with a finite free resolution is stably free.
- 8.13: a stably free module of rank one is free.
- 8.14 (Nagata): if `x` is prime and `A_x` is UFD, then `A` is UFD.
- 8.15: for a regular local ring `(A,m)`, choose `x ∈ m \ m^2`.
  Then `A/(x)` is regular and `x` is prime, so by 8.14 it suffices to prove `A_x` is UFD.
  For a height-one prime `q` of `A_x`, each maximal localization `(A_x)_P` is a regular local ring
  of strictly smaller dimension, hence is UFD by induction, so `q_P` is principal for every maximal `P`.
  Thus `q` is a rank-one locally free module. One shows `A_x / q` has finite free resolution by
  localizing a finite free resolution of `A / p`, where `p = comap q`, then the short exact sequence
  `0 → q → A_x → A_x / q → 0` gives a finite free resolution of `q`. Since `q` is also projective,
  8.12 makes it stably free, and 8.13 upgrades rank-one stably free to free, so `q` is principal.
  Therefore every height-one prime of `A_x` is principal, hence `A_x` is UFD, and then 8.14 gives
  that `A` is UFD.
-/
