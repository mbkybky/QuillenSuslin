/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.RegularLocalRing.Localization
import QuillenSuslin.FiniteFreeResolution.HasProjectiveDimensionLE
import QuillenSuslin.FiniteFreeResolution.Localization
import QuillenSuslin.StablyFree.FreeOfLocalizedEq
import QuillenSuslin.StablyFree.HasFiniteFreeResolution
import QuillenSuslin.UFD.Lemmas

universe u

variable {R : Type u} [CommRing R]

theorem Ideal.isPrincipal_of_free [IsDomain R] {I : Ideal R} [Module.Free R I] : I.IsPrincipal :=
  (Submodule.rank_le_one_iff_isPrincipal I).1 ((Submodule.rank_le I).trans_eq (Module.rank_self R))

lemma IsLocalRing.exists_mem_maximalIdeal_not_mem_sq [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}
    (hn : ringKrullDim R = n.succ) : ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
  have : Nontrivial (IsLocalRing.CotangentSpace R) := by
    simpa only [← not_subsingleton_iff_nontrivial, subsingleton_cotangentSpace_iff] using fun hf ↦
      ((ringKrullDim_eq_zero_of_isField hf).symm.trans hn).not_lt (WithBot.coe_lt_coe.2 (by simp))
  obtain ⟨u, hu⟩ := exists_ne (0 : CotangentSpace R)
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (maximalIdeal R) u
  exact ⟨x, x.2, by simpa [Ideal.toCotangent_eq_zero] using hu⟩

lemma ringKrullDim_localizationAtPrime_lt_of_lt_maximalIdeal [IsLocalRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] (hP_lt_max : P < IsLocalRing.maximalIdeal R) :
    ringKrullDim (Localization.AtPrime P) < ringKrullDim R := by
  apply (IsLocalization.AtPrime.ringKrullDim_eq_height P _).trans_lt
  apply lt_of_lt_of_eq ?_ IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim
  rw [Ideal.height_eq_primeHeight]
  exact_mod_cast Ideal.primeHeight_strict_mono hP_lt_max

private lemma ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd
    [IsRegularLocalRing R] {x : R} (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hxp : Prime x)
    (hP : ∀ (P : Ideal R) [P.IsPrime] (_ : P < IsLocalRing.maximalIdeal R),
      UniqueFactorizationMonoid (Localization.AtPrime P)) :
    UniqueFactorizationMonoid (Localization.Away x) := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hxp.ne_zero
  apply Ideal.ufd_iff_height_one_primes_principal.2
  intro Q hQ hQheight
  have hloc (P : Ideal (Localization.Away x)) [P.IsMaximal] :
      LocalizedModule P.primeCompl Q ≃ₗ[Localization.AtPrime P] Localization.AtPrime P := by
    let eIdeal : LocalizedModule P.primeCompl Q ≃ₗ[Localization.AtPrime P]
        Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q :=
      LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P) <|
        IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl Q)
          (Algebra.idealMap (Localization.AtPrime P) Q)
    by_cases hQP : Q ≤ P
    · let p : Ideal R := Ideal.comap (algebraMap R (Localization.Away x)) P
      have hx_not_mem_p : x ∉ p := Set.disjoint_left.mp
        ((IsLocalization.isPrime_iff_isPrime_disjoint M (Localization.Away x) P).1 inferInstance).2
          (Submonoid.mem_powers x)
      have hp_lt_max : p < IsLocalRing.maximalIdeal R := by
        refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) ?_
        intro hEq
        exact hx_not_mem_p (hEq ▸ hxmem)
      have : UniqueFactorizationMonoid (Localization.AtPrime P) :=
        IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P
          |>.toMulEquiv.uniqueFactorizationMonoid (hP p hp_lt_max)
      have : (Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q).IsPrime :=
        Ideal.isPrime_map_of_isLocalizationAtPrime P hQP
      have hmap_disj : Disjoint (P.primeCompl : Set (Localization.Away x))
          (Q : Set (Localization.Away x)) := by
        simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hQP]
      have hmap_height : (Ideal.map (algebraMap
          (Localization.Away x) (Localization.AtPrime P)) Q).primeHeight = 1 := by
        simpa [IsLocalization.comap_map_of_isPrime_disjoint
            P.primeCompl (Localization.AtPrime P) inferInstance hmap_disj, hQheight]
          using (IsLocalization.primeHeight_comap P.primeCompl
            (Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q)).symm
      have := (Ideal.ufd_iff_height_one_primes_principal).1 inferInstance
        (Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q) hmap_height
      exact eIdeal.trans <| LinearEquiv.symm <| Ideal.isoBaseOfIsPrincipal <|
        Ideal.primeHeight_eq_zero_iff_eq_bot.not.mp (by simp [hmap_height])
    · exact eIdeal.trans <| LinearEquiv.ofTop _ <|
        IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hQP
  have : Module.Projective (Localization.Away x) Q := by
    have := Module.finitePresentation_of_finite (Localization.Away x) Q
    apply Module.projective_of_localization_maximal
    intro P _
    have : Module.Free (Localization.AtPrime P) (Localization.AtPrime P) := Module.Free.self _
    have : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) :=
      Module.Free.of_equiv (hloc P).symm
    exact Module.Projective.of_free
  let q : Ideal R := Ideal.comap (algebraMap R (Localization.Away x)) Q
  obtain ⟨n, _⟩ := (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R (R ⧸ q))).1 <|
    projectiveDimension_ne_top_of_isRegularLocalRing (ModuleCat.of R (R ⧸ q))
  let eQuotMap : LocalizedModule M (R ⧸ q) ≃ₗ[Localization.Away x]
      Localization.Away x ⧸ Ideal.map (algebraMap R (Localization.Away x)) q :=
    (localizedQuotientEquiv M q).symm.trans
      (Submodule.quotEquivOfEq _ _ (Ideal.localized'_eq_map (Localization.Away x) M q))
  have hffr_quot : HasFiniteFreeResolution (Localization.Away x) (Localization.Away x ⧸ Q) :=
    hasFiniteFreeResolution_of_linearEquiv
      (Ideal.quotientEquivAlgOfEq (Localization.Away x) (IsLocalization.map_comap M _ Q)) <|
        hasFiniteFreeResolution_of_linearEquiv eQuotMap <| hasFiniteFreeResolution_localizedModule M
          (hasFiniteFreeResolution_of_hasProjectiveDimensionLE R (R ⧸ q) n)
  have hffr_Q : HasFiniteFreeResolution (Localization.Away x) Q :=
    have : Module.Free (Localization.Away x) (Localization.Away x) := Module.Free.self _
    hasFiniteFreeResolution_of_shortExact_of_middle_of_right _ _
      (Submodule.subtype_injective Q) (Submodule.mkQ_surjective Q) (LinearMap.exact_subtype_mkQ Q)
        (hasFiniteFreeResolution_of_finite_of_free (Localization.Away x)) hffr_quot
  have : Module.Free (Localization.Away x) Q := Module.free_of_isStablyFree_of_localized_eq_ring
    ((isStablyFree_iff_hasFiniteFreeResolution (Localization.Away x) Q).2 hffr_Q) hloc
  exact Q.isPrincipal_of_free

variable (R) in
theorem ufd_of_isRegularLocalRing [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  have hmain (n : ℕ) : ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S],
      ringKrullDim S = n → UniqueFactorizationMonoid S := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S _ _ hdim
      cases n with
      | zero =>
          have := (isField_of_isRegularLocalRing_of_dimension_zero hdim).isPrincipalIdealRing
          infer_instance
      | succ n =>
          obtain ⟨x, hxm, hxnm⟩ := IsLocalRing.exists_mem_maximalIdeal_not_mem_sq hdim
          have hx_ne_zero : x ≠ 0 := fun hx0 ↦ hxnm (by simp [hx0])
          have : IsRegularLocalRing (S ⧸ Ideal.span {x}) := (quotient_span_singleton S hxm hxnm).1
          have hxp : Prime x := (Ideal.span_singleton_prime hx_ne_zero).1 <|
            (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
          have hP (P : Ideal S) [P.IsPrime] (hP_lt_max : P < IsLocalRing.maximalIdeal S) :
              UniqueFactorizationMonoid (Localization.AtPrime P) := by
            have hdim_loc_lt : ringKrullDim (Localization.AtPrime P) < ringKrullDim S :=
              ringKrullDim_localizationAtPrime_lt_of_lt_maximalIdeal hP_lt_max
            have : IsRegularLocalRing _ := isRegularLocalRing_localization S P
            obtain ⟨k, hk⟩ := exist_nat_eq (Localization.AtPrime P)
            exact ih k (ENat.coe_lt_coe.mp <| WithBot.coe_lt_coe.mp <|
              hk.symm.trans_lt <| hdim_loc_lt.trans_eq hdim) hk
          have := ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd hxm hxp hP
          exact ufd_of_ufd_localization_away_of_prime hxp
  obtain ⟨n, hn⟩ := exist_nat_eq R
  exact hmain n hn
