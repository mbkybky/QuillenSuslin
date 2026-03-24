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

private lemma ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd
    [IsRegularLocalRing R] {x : R} (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hxp : Prime x)
    (hP : ∀ (P : Ideal R) [P.IsPrime] (_ : P < IsLocalRing.maximalIdeal R),
      UniqueFactorizationMonoid (Localization.AtPrime P)) :
    UniqueFactorizationMonoid (Localization.Away x) := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hxp.ne_zero
  apply Ideal.ufd_iff_height_one_primes_principal.2
  intro Q hQ hQheight
  have hloc : ∀ (P : Ideal (Localization.Away x)) [P.IsMaximal],
      LocalizedModule P.primeCompl Q ≃ₗ[Localization.AtPrime P] Localization.AtPrime P := by
    intro P _
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
      have hmap_principal :
          (Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q).IsPrincipal :=
        (Ideal.ufd_iff_height_one_primes_principal).1 inferInstance
          (Ideal.map (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q) hmap_height
      have hmap_ne_bot : Ideal.map
          (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q ≠ ⊥ := by
        intro hbot
        have h0 : (Ideal.map
            (algebraMap (Localization.Away x) (Localization.AtPrime P)) Q).primeHeight = 0 := by
          simp [hbot, Ideal.primeHeight_eq_zero_iff_eq_bot]
        simp [hmap_height] at h0
      exact eIdeal.trans (Ideal.isoBaseOfIsPrincipal hmap_ne_bot).symm
    · exact eIdeal.trans (LinearEquiv.ofTop _ <|
        IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hQP)
  have hQ_projective : Module.Projective (Localization.Away x) Q := by
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
  have hffr_Q : HasFiniteFreeResolution (Localization.Away x) Q :=
    have : Module.Free (Localization.Away x) (Localization.Away x) := Module.Free.self _
    hasFiniteFreeResolution_of_shortExact_of_middle_of_right _ _
      (Submodule.subtype_injective Q) (Submodule.mkQ_surjective Q)
        (LinearMap.exact_subtype_mkQ Q)
          (hasFiniteFreeResolution_of_finite_of_free (Localization.Away x)) <|
            hasFiniteFreeResolution_of_linearEquiv
              (Ideal.quotientEquivAlgOfEq (Localization.Away x) (IsLocalization.map_comap M _ Q)) <|
                hasFiniteFreeResolution_of_linearEquiv eQuotMap <|
                  hasFiniteFreeResolution_localizedModule M <|
                    hasFiniteFreeResolution_of_hasProjectiveDimensionLE R (R ⧸ q) n
  have hfree : Module.Free (Localization.Away x) Q :=
    Module.free_of_isStablyFree_of_localized_eq_ring
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
        have : IsPrincipalIdealRing S := IsField.isPrincipalIdealRing <|
          isField_of_isRegularLocalRing_of_dimension_zero hdim
        infer_instance
      | succ n =>
        have hmax_ne_bot : IsLocalRing.maximalIdeal S ≠ ⊥ := by
          intro hbot
          have hfield : IsField S := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot
          have hdim0 : ringKrullDim S = 0 := ringKrullDim_eq_zero_of_isField hfield
          exact (not_eq_of_beq_eq_false rfl) (by simpa [hdim, Nat.cast_add] using hdim0)
        have hpd_ne_top : CategoryTheory.projectiveDimension
            (ModuleCat.of S (Shrink.{u, u} (IsLocalRing.maximalIdeal S))) ≠ ⊤ :=
          projectiveDimension_ne_top_of_isRegularLocalRing
            (ModuleCat.of S (Shrink.{u, u} (IsLocalRing.maximalIdeal S)))
        obtain ⟨m, hm⟩ := CategoryTheory.projectiveDimension_ne_top_iff
            (ModuleCat.of S (Shrink.{u, u} (IsLocalRing.maximalIdeal S))) |>.1 hpd_ne_top
        obtain ⟨x, hxmem, hxnmem, hxreg⟩ :=
          exist_isSMulRegular_of_exist_hasProjectiveDimensionLE hmax_ne_bot ⟨m, hm⟩
        have : IsRegularLocalRing (S ⧸ Ideal.span {x}) := (quotient_span_singleton S hxmem hxnmem).1
        have hxp : Prime x := (Ideal.span_singleton_prime (IsLeftRegular.ne_zero hxreg)).1 <|
          (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance
        have hP (P : Ideal S) [P.IsPrime] (hP_lt_max : P < IsLocalRing.maximalIdeal S) :
            UniqueFactorizationMonoid (Localization.AtPrime P) := by
          have hdim_loc_succ : ringKrullDim (Localization.AtPrime P) + 1 ≤ ringKrullDim S := by
            have hprime_succ :
                (((P.primeHeight + 1 : ℕ∞) : WithBot ℕ∞)) ≤ ringKrullDim S := by
              calc
                _ ≤ (((IsLocalRing.maximalIdeal S).primeHeight : ℕ∞) : WithBot ℕ∞) := by
                  exact_mod_cast Ideal.primeHeight_add_one_le_of_lt hP_lt_max
                _ = ringKrullDim S := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim
            calc
              _ = (P.height : WithBot ℕ∞) + 1 := by
                simpa using congrArg (fun t : WithBot ℕ∞ => t + 1)
                  (IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P))
              _ = (P.primeHeight : WithBot ℕ∞) + 1 := by simp [Ideal.height_eq_primeHeight]
              _ = (((P.primeHeight + 1 : ℕ∞) : WithBot ℕ∞)) := by simp
              _ ≤ ringKrullDim S := hprime_succ
          have : IsRegularLocalRing (Localization.AtPrime P) := isRegularLocalRing_localization S P
          let k : ℕ := Classical.choose (exist_nat_eq (Localization.AtPrime P))
          have hk : ringKrullDim (Localization.AtPrime P) = k :=
            Classical.choose_spec (exist_nat_eq (Localization.AtPrime P))
          have hk_lt : k < n.succ := by
            have hdim_loc_succ' : ((k + 1 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S := by
              simpa [hk, Nat.cast_add] using hdim_loc_succ
            have hdim_loc_succ'' : (k + 1 : ℕ∞) ≤ (n + 1 : ℕ∞) :=
              WithBot.coe_le_coe.mp (by simpa [hdim] using hdim_loc_succ')
            have : k + 1 ≤ n + 1 := ENat.coe_le_coe.mp hdim_loc_succ''
            exact Nat.lt_succ_of_le (Nat.succ_le_succ_iff.mp this)
          exact ih k hk_lt hk
        have : UniqueFactorizationMonoid (Localization.Away x) :=
          ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd hxmem hxp hP
        exact ufd_of_ufd_localization_away_of_prime hxp
  obtain ⟨n, hn⟩ := exist_nat_eq R
  exact hmain n hn
