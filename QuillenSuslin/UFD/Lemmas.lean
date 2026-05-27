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

theorem UniqueFactorizationMonoid.isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p ≠ ⊥ := p.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one hph)
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  sorry

theorem UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
  have hpn : p ≠ ⊥ := fun hpb ↦ hx0 <|
    Ideal.span_singleton_eq_bot.mp <| bot_unique (hpmin.le.trans_eq hpb)
  have hpp : p.IsPrincipal := h p <| le_antisymm
    ((Ideal.span {x}).height_le_one_of_isPrincipal_of_mem_minimalPrimes p hpmin)
      (ENat.one_le_iff_ne_zero.mpr (p.height_eq_zero_iff_eq_bot.not.mpr hpn))
  exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one [IsNoetherianRing R] :
    UniqueFactorizationMonoid R ↔ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal :=
  ⟨fun _ _ _ ↦ isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩

theorem Ideal.isPrincipal_of_isPrincipal_isLocalization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  have hd : Disjoint (Submonoid.powers x : Set R) p := by
    rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p ≠ ⊥ := by simp [Ideal.map_eq_bot_iff_of_injective hi, hpbot]
    obtain ⟨g, hg⟩ := hp
    have hg0 : g ≠ 0 := fun hg0 ↦ hpb <| by simp [hg0, hg]
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x S hg0 hx.irreducible
    have hu : IsUnit (selfZPow x S n) :=
      IsUnit.of_mul_eq_one (selfZPow x S (- n)) (selfZPow_mul_neg x S n)
    sorry

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalization_away_of_prime hx hxp (Localization.Away x) hp

theorem UniqueFactorizationMonoid.iff_isLocalization_away_of_prime
    [IsNoetherianRing R] {x : R} (hx : Prime x) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away x S] : UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  sorry

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if and only if
  `Rₓ` is a UFD. -/
theorem UniqueFactorizationMonoid.iff_localization_away_of_prime
    [IsNoetherianRing R] {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  UniqueFactorizationMonoid.iff_isLocalization_away_of_prime hx (Localization.Away x)
