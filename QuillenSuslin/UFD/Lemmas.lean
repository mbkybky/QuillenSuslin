/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `UniqueFactorizationMonoid.iff_height_one_primes_principal` : Let `R` be a Noetherian domain. Then
  `R` is a UFD if and only if every height `1` prime ideal is principal.

* `UniqueFactorizationMonoid.iff_localization_away_of_prime` : Let `R` be a Noetherian domain,
  `x ∈ R` be a prime element. Then `R` is a UFD if and only if `Rₓ` is a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

lemma Ideal.height_eq_zero_iff_eq_bot {I : Ideal R} : I.height = 0 ↔ I = ⊥ := by
  sorry

/-- If `x ≠ 0`, then the localization of a domain away from `x` is again a domain. -/
theorem Localization.Away.isDomain {x : R} (hx : x ≠ 0) :
    IsDomain (Localization.Away x) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)

theorem UniqueFactorizationMonoid.height_one_primes_principal [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  sorry

theorem UniqueFactorizationMonoid.of_height_one_primes_principal [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime] (_ : p.height = 1), p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  sorry

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem UniqueFactorizationMonoid.iff_height_one_primes_principal [IsNoetherianRing R] :
    UniqueFactorizationMonoid R ↔ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal :=
  ⟨fun _ _ _ ↦ height_one_primes_principal, of_height_one_primes_principal⟩

theorem Ideal.isPrincipal_of_isPrincipal_isLocalization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  sorry

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalization_away_of_prime hx hxp (Localization.Away x) hp

theorem UniqueFactorizationMonoid.iff_isLocalization_away_of_prime [IsNoetherianRing R] {x : R}
    (hx : Prime x) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S] :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  sorry

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if and only if
  `Rₓ` is a UFD. -/
theorem UniqueFactorizationMonoid.iff_localization_away_of_prime
    [IsNoetherianRing R] {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  UniqueFactorizationMonoid.iff_isLocalization_away_of_prime hx (Localization.Away x)
