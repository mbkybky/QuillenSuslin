import Mathlib.RingTheory.RegularLocalRing.Localization
import QuillenSuslin.FiniteFreeResolution.FreeOfLocalizedEq
import QuillenSuslin.FiniteFreeResolution.Localization
import QuillenSuslin.UFD.Lemmas

universe u

variable (R : Type u) [CommRing R]

theorem Ideal.isPrincipal_of_free [IsDomain R] {I : Ideal R} [Module.Free R I] : I.IsPrincipal :=
  (Submodule.rank_le_one_iff_isPrincipal I).1 <| Submodule.rank_le I |>.trans_eq <|
    Module.rank_self R

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
              have : ¬ (((n : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) = 0 := by
                intro hzero
                have hneq : (((n : ℕ∞) + 1 : ℕ∞)) ≠ 0 := by simp
                exact hneq (WithBot.coe_eq_coe.mp hzero)
              exact this (by simpa [hdim, Nat.cast_add] using hdim0)
            have hpd_ne_top :
                CategoryTheory.projectiveDimension
                    (ModuleCat.of S (Shrink.{u, u} ↥(IsLocalRing.maximalIdeal S))) ≠ ⊤ :=
              projectiveDimension_ne_top_of_isRegularLocalRing
                (ModuleCat.of S (Shrink.{u, u} ↥(IsLocalRing.maximalIdeal S)))
            obtain ⟨m, hm⟩ :
                ∃ m, CategoryTheory.HasProjectiveDimensionLE
                  (ModuleCat.of S (Shrink.{u, u} ↥(IsLocalRing.maximalIdeal S))) m :=
              (CategoryTheory.projectiveDimension_ne_top_iff
                (ModuleCat.of S (Shrink.{u, u} ↥(IsLocalRing.maximalIdeal S)))).1 hpd_ne_top
            obtain ⟨x, hxmem, hxnmem, hxreg⟩ :=
              exist_isSMulRegular_of_exist_hasProjectiveDimensionLE (R := S) hmax_ne_bot ⟨m, hm⟩
            have hx_ne_zero : x ≠ 0 := by
              intro hx0
              have : (1 : S) = 0 := by
                apply hxreg.right_eq_zero_of_smul
                simp [hx0]
              exact one_ne_zero this
            obtain ⟨hquot_reg, hquot_dim⟩ := quotient_span_singleton (R := S) hxmem hxnmem
            have hquot_dom : IsDomain (S ⧸ Ideal.span {x}) :=
              isDomain_of_isRegularLocalRing (R := S ⧸ Ideal.span {x})
            have hxprime_ideal : (Ideal.span ({x} : Set S)).IsPrime :=
              (Ideal.Quotient.isDomain_iff_prime _).1 hquot_dom
            have hxprime : Prime x := (Ideal.span_singleton_prime hx_ne_zero).1 hxprime_ideal
            let M : Submonoid S := Submonoid.powers x
            have hM : M ≤ nonZeroDivisors S := by
              refine Submonoid.powers_le.2 ?_
              rw [mem_nonZeroDivisors_iff]
              constructor <;> intro a ha
              · exact mul_eq_zero.mp ha |>.resolve_left hxprime.ne_zero
              · exact mul_eq_zero.mp ha |>.resolve_right hxprime.ne_zero
            have hA_dom : IsDomain (Localization M) :=
              IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hM
            have hA_ufd : UniqueFactorizationMonoid (Localization M) := by
              apply (Ideal.ufd_iff_height_one_primes_principal (R := Localization M)).2
              intro q hq hqheight
              have hq_ne_bot : q ≠ ⊥ := by
                intro hqbot
                have hbot_height : (⊥ : Ideal (Localization M)).primeHeight = 0 := by
                  rw [Ideal.primeHeight_eq_zero_iff]
                  simp [IsDomain.minimalPrimes_eq_singleton_bot (Localization M)]
                have : q.primeHeight = 0 := by simpa [hqbot] using hbot_height
                rw [hqheight] at this
                norm_num at this
              have hloc :
                  ∀ (P : Ideal (Localization M)) [P.IsMaximal],
                    Nonempty (LocalizedModule P.primeCompl q ≃ₗ[Localization.AtPrime P]
                      Localization.AtPrime P) := by
                intro P _
                let eIdeal :
                    LocalizedModule P.primeCompl q ≃ₗ[Localization.AtPrime P]
                      Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q :=
                  LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P)
                    (IsLocalizedModule.linearEquiv P.primeCompl
                      (LocalizedModule.mkLinearMap P.primeCompl q)
                      (Algebra.idealMap (Localization.AtPrime P) q))
                by_cases hqP : q ≤ P
                · let p : Ideal S := Ideal.comap (algebraMap S (Localization M)) P
                  have hpprime_disj :
                      (Ideal.comap (algebraMap S (Localization M)) P).IsPrime ∧
                        Disjoint (M : Set S) (p : Set S) := by
                    simpa [p] using
                      (IsLocalization.isPrime_iff_isPrime_disjoint M (Localization M) P).1
                        inferInstance
                  have hp_disj : Disjoint (M : Set S) (p : Set S) := hpprime_disj.2
                  have hx_not_mem_p : x ∉ p := by
                    intro hxp
                    have hxpow : x ∈ M := by
                      exact ⟨1, by simp⟩
                    exact Set.disjoint_left.mp hp_disj hxpow hxp
                  have hp_le_max : p ≤ IsLocalRing.maximalIdeal S :=
                    IsLocalRing.le_maximalIdeal_of_isPrime p
                  have hp_lt_max : p < IsLocalRing.maximalIdeal S := by
                    refine lt_of_le_of_ne hp_le_max ?_
                    intro hEq
                    exact hx_not_mem_p (hEq ▸ hxmem)
                  have hdim_loc_succ :
                      ringKrullDim (Localization.AtPrime p) + 1 ≤ ringKrullDim S := by
                    have hprime_succ :
                        (((p.primeHeight + 1 : ℕ∞) : WithBot ℕ∞)) ≤ ringKrullDim S := by
                      calc
                        (((p.primeHeight + 1 : ℕ∞) : WithBot ℕ∞))
                            ≤ (((IsLocalRing.maximalIdeal S).primeHeight : ℕ∞) : WithBot ℕ∞) := by
                              exact_mod_cast Ideal.primeHeight_add_one_le_of_lt hp_lt_max
                        _ = ringKrullDim S := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim
                    calc
                      ringKrullDim (Localization.AtPrime p) + 1 = (p.height : WithBot ℕ∞) + 1 := by
                        simpa using
                          congrArg (fun t : WithBot ℕ∞ => t + 1)
                            (IsLocalization.AtPrime.ringKrullDim_eq_height p
                              (Localization.AtPrime p))
                      _ = (p.primeHeight : WithBot ℕ∞) + 1 := by
                        simp [Ideal.height_eq_primeHeight]
                      _ = (((p.primeHeight + 1 : ℕ∞) : WithBot ℕ∞)) := by simp
                      _ ≤ ringKrullDim S := hprime_succ
                  have hreg_loc : IsRegularLocalRing (Localization.AtPrime p) :=
                    isRegularLocalRing_localization S p
                  obtain ⟨k, hk⟩ := exist_nat_eq (Localization.AtPrime p)
                  have hk_lt : k < n.succ := by
                    have hdim_loc_succ' : ((k + 1 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S := by
                      simpa [hk, Nat.cast_add] using hdim_loc_succ
                    have hdim_loc_succ'' : (k + 1 : ℕ∞) ≤ (n + 1 : ℕ∞) := by
                      exact WithBot.coe_le_coe.mp (by simpa [hdim] using hdim_loc_succ')
                    have : k + 1 ≤ n + 1 := ENat.coe_le_coe.mp hdim_loc_succ''
                    exact Nat.lt_succ_of_le (Nat.succ_le_succ_iff.mp this)
                  have hufd_loc : UniqueFactorizationMonoid (Localization.AtPrime p) :=
                    ih k hk_lt hk
                  let : UniqueFactorizationMonoid (Localization.AtPrime P) :=
                    MulEquiv.uniqueFactorizationMonoid
                      ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P).toMulEquiv)
                      hufd_loc
                  have hmap_prime :
                      (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q).IsPrime :=
                    Ideal.isPrime_map_of_isLocalizationAtPrime P hqP
                  have hmap_disj :
                      Disjoint (P.primeCompl : Set (Localization M)) (q : Set (Localization M)) := by
                    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hqP]
                  have hmap_height :
                      (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q).primeHeight = 1 := by
                    simpa [IsLocalization.comap_map_of_isPrime_disjoint
                        P.primeCompl (Localization.AtPrime P) inferInstance hmap_disj, hqheight] using
                      (IsLocalization.primeHeight_comap P.primeCompl
                        (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q)).symm
                  have hmap_principal :
                      (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q).IsPrincipal :=
                    (Ideal.ufd_iff_height_one_primes_principal).1 inferInstance
                      (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q) hmap_height
                  have hmap_ne_bot :
                      Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q ≠ ⊥ := by
                    intro hbot
                    have hcomap :
                        Ideal.comap (algebraMap (Localization M) (Localization.AtPrime P))
                          (Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q) = q :=
                      IsLocalization.comap_map_of_isPrime_disjoint
                        P.primeCompl (Localization.AtPrime P) inferInstance hmap_disj
                    have : q = ⊥ := by simpa only [hbot, Ideal.under_bot] using hcomap.symm
                    exact hq_ne_bot this
                  exact ⟨eIdeal.trans (Ideal.isoBaseOfIsPrincipal hmap_ne_bot).symm⟩
                · have hmap_top :
                    Ideal.map (algebraMap (Localization M) (Localization.AtPrime P)) q = ⊤ :=
                      IsLocalization.AtPrime.map_eq_top_of_not_le (S := Localization.AtPrime P)
                        (I := q) (p := P) hqP
                  exact ⟨eIdeal.trans (LinearEquiv.ofTop _ hmap_top)⟩
              have hq_projective : Module.Projective (Localization M) q := by
                have : Module.FinitePresentation (Localization M) q :=
                  Module.finitePresentation_of_finite (Localization M) q
                apply Module.projective_of_localization_maximal
                intro P _
                rcases hloc P with ⟨uP⟩
                have : Module.Free (Localization.AtPrime P) (Localization.AtPrime P) :=
                  Module.Free.self _
                have: Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl q) :=
                  Module.Free.of_equiv uP.symm
                exact Module.Projective.of_free
              let p0 : Ideal S := Ideal.comap (algebraMap S (Localization M)) q
              have hp0prime_disj :
                  p0.IsPrime ∧ Disjoint (M : Set S) (p0 : Set S) := by
                simpa [p0] using
                  (IsLocalization.isPrime_iff_isPrime_disjoint M (Localization M) q).1 inferInstance
              have hp0_disj : Disjoint (M : Set S) (p0 : Set S) := hp0prime_disj.2
              have hqeq :
                  Ideal.map (algebraMap S (Localization M)) p0 = q := by
                have htmp :
                    (RelIso.symm (IsLocalization.orderIsoOfPrime M (Localization M)))
                      ⟨p0, inferInstance, hp0_disj⟩ = ⟨q, inferInstance⟩ := by
                  apply (IsLocalization.orderIsoOfPrime M (Localization M)).injective
                  ext I
                  simp [p0, IsLocalization.orderIsoOfPrime_apply_coe]
                simpa [IsLocalization.orderIsoOfPrime_symm_apply_coe] using
                  congrArg Subtype.val htmp
              have hquot_pd_ne_top :
                  CategoryTheory.projectiveDimension (ModuleCat.of S (S ⧸ p0)) ≠ ⊤ :=
                projectiveDimension_ne_top_of_isRegularLocalRing (ModuleCat.of S (S ⧸ p0))
              obtain ⟨m0, hm0⟩ :
                  ∃ m0, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of S (S ⧸ p0)) m0 :=
                (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of S (S ⧸ p0))).1
                  hquot_pd_ne_top
              have hffr_p0 : HasFiniteFreeResolution S (S ⧸ p0) :=
                hasFiniteFreeResolution_of_hasProjectiveDimensionLE (R := S) (M := S ⧸ p0) m0
              have hffr_loc :
                  HasFiniteFreeResolution (Localization M) (LocalizedModule M (S ⧸ p0)) :=
                hasFiniteFreeResolution_localized (R := S) (M := S ⧸ p0) M hffr_p0
              let eQuotMap :
                  LocalizedModule M (S ⧸ p0) ≃ₗ[Localization M]
                    Localization M ⧸ Ideal.map (algebraMap S (Localization M)) p0 :=
                (localizedQuotientEquiv (p := M) (M' := p0)).symm.trans
                  (Submodule.quotEquivOfEq _ _
                    (Ideal.localized'_eq_map (Localization M) M p0))
              have hffr_map :
                  HasFiniteFreeResolution (Localization M)
                    (Localization M ⧸ Ideal.map (algebraMap S (Localization M)) p0) :=
                hasFiniteFreeResolution_of_linearEquiv eQuotMap hffr_loc
              have hffr_quot : HasFiniteFreeResolution (Localization M) (Localization M ⧸ q) := by
                exact hasFiniteFreeResolution_of_linearEquiv
                  ((Ideal.quotientEquivAlgOfEq (Localization M) hqeq).toLinearEquiv :
                    (Localization M ⧸ Ideal.map (algebraMap S (Localization M)) p0) ≃ₗ[Localization M]
                      Localization M ⧸ q)
                  hffr_map
              have hffr_q : HasFiniteFreeResolution (Localization M) q := by
                have : Module.Free (Localization M) (Localization M) := Module.Free.self _
                refine hasFiniteFreeResolution_of_shortExact_of_middle_of_right q (Localization M)
                  (Localization M ⧸ q)
                  (by
                    intro a b hab
                    exact Subtype.ext hab)
                  Ideal.Quotient.mk_surjective (LinearMap.exact_subtype_mkQ q)
                  (hasFiniteFreeResolution_of_finite_of_free (R := Localization M) (Localization M))
                  hffr_quot
              have hstable : IsStablyFree (Localization M) q :=
                (stably_free_iff (Localization M) q).2 hffr_q
              have hq_ne_top : q ≠ ⊤ := Ideal.IsPrime.ne_top'
              obtain ⟨P0, hP0max, hqP0⟩ := Ideal.exists_le_maximal q hq_ne_top
              have hfree : Module.Free (Localization M) q :=
                free_of_isStablyFree_of_localized_eq_ring
                  hstable P0 (Classical.choice (hloc P0)) hloc
              exact Ideal.isPrincipal_of_free (R := Localization M) (I := q)
            exact ufd_of_ufd_away_of_prime x hxprime
  obtain ⟨n, hn⟩ := exist_nat_eq R
  exact hmain n hn
