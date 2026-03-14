import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

@[stacks 0AFT]
theorem Ideal.ufd_iff_height_one_primes_principal [IsDomain R]:
    UniqueFactorizationMonoid R ↔
    ∀ (p : Ideal R) [p.IsPrime], p.primeHeight = 1 → p.IsPrincipal := by
  constructor
  · intro h p hp h1
    have hpb : p ≠ ⊥ := by
      intro hp
      simp_rw [hp] at h1
      have h: Order.height (⊥ : PrimeSpectrum R) = 1 := h1
      simp at h
    rcases (Submodule.ne_bot_iff p).mp hpb with ⟨x, hxp, hx⟩
    rcases UniqueFactorizationMonoid.exists_prime_factors x hx with ⟨s, hps, hxs⟩
    have hsprod_mem : s.prod ∈ p := by
      rcases Associated.dvd hxs.symm with ⟨b, hb⟩
      rw [hb]
      exact Ideal.mul_mem_right b p hxp
    obtain ⟨a, ha, hap⟩ : ∃ a ∈ s, a ∈ p :=
      (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hp s).1 hsprod_mem
    let I : Ideal R := Ideal.span ({a} : Set R)
    have hsap : (span {a}).IsPrime :=
      (span_singleton_prime (Prime.ne_zero (hps a ha))).mpr (hps a ha)
    by_cases hpa : p = span {a}
    · rw [hpa]
      exact instIsPrincipalSpanSingletonSet
    let l1 : LTSeries (PrimeSpectrum R) := by
      refine (RelSeries.singleton _ (⊥ : PrimeSpectrum R)).append
        (RelSeries.singleton _ ⟨span {a}, hsap⟩) ?_
      simp only [RelSeries.last_singleton, RelSeries.head_singleton, Set.mem_setOf_eq]
      refine (PrimeSpectrum.asIdeal_lt_asIdeal ⊥ ⟨span {a}, hsap⟩).mp ?_
      simpa [bot_lt_iff_ne_bot] using Prime.ne_zero (hps a ha)
    let l : LTSeries (PrimeSpectrum R) := by
      refine l1.append (RelSeries.singleton _ ⟨p, hp⟩) ?_
      simpa using (PrimeSpectrum.asIdeal_lt_asIdeal ⟨span {a}, hsap⟩ ⟨p, hp⟩).mp <|
        Std.lt_of_le_of_ne ((span_singleton_le_iff_mem p).mpr hap) fun eq => hpa eq.symm
    have h2 : 2 ≤ p.primeHeight := by
      simp [primeHeight, Order.height]
      apply le_sSup
      use l
      simp [l, l1]
    rw [h1] at h2
    exfalso
    have h2' : (2 : WithTop ℕ) ≤ 1 := h2
    norm_num at h2'
  · intro hPrincipal
    refine UniqueFactorizationMonoid.mk ?_
    intro q
    constructor
    · intro hqirr
      have hq0 : q ≠ 0 := Irreducible.ne_zero hqirr
      have hspan_ne_top : (Ideal.span ({q} : Set R)) ≠ ⊤ := by
        intro htop
        exact hqirr.not_isUnit ((Ideal.span_singleton_eq_top).1 htop)
      rcases Ideal.exists_le_maximal (Ideal.span ({q} : Set R)) hspan_ne_top with
        ⟨M, hMmax, hspan_le_M⟩
      rcases Ideal.exists_minimalPrimes_le hspan_le_M with ⟨p, hpmin, -⟩
      have hpprime : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
      have hq_mem_p : q ∈ p := hpmin.1.2 (Ideal.subset_span (by simp))
      have hp_ne_bot : p ≠ ⊥ := by
        intro hpbot
        exact hq0 (by simpa [hpbot] using hq_mem_p)
      have hp_not_min : p ∉ minimalPrimes R := by
        intro hpminR
        rw [IsDomain.minimalPrimes_eq_singleton_bot R] at hpminR
        exact hp_ne_bot (by simpa using hpminR)
      have hp_height_ne_zero : p.primeHeight ≠ 0 := by
        intro hp0
        exact hp_not_min (p.primeHeight_eq_zero_iff.1 hp0)
      have hp_height_le_one : p.primeHeight ≤ 1 := by
        have hheight : p.height ≤ 1 :=
          Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span ({q} : Set R)) p
            hpmin
        simpa [p.height_eq_primeHeight] using hheight
      have hp_height_eq_one : p.primeHeight = 1 := by
        have hp_top : p.primeHeight ≠ ⊤ := Ideal.primeHeight_ne_top p
        rcases ENat.ne_top_iff_exists.mp hp_top with ⟨n, hn⟩
        rw [← hn] at hp_height_le_one hp_height_ne_zero ⊢
        have hn_le : n ≤ 1 := by
          simpa using (show (n : WithTop ℕ) ≤ 1 from hp_height_le_one)
        interval_cases n <;> simp at *
      have hp_principal : p.IsPrincipal := hPrincipal p hp_height_eq_one
      let g : R := Submodule.IsPrincipal.generator p
      have hp_span : Ideal.span ({g} : Set R) = p := by simp [g]
      have hq_mem_span_g : q ∈ Ideal.span ({g} : Set R) := by
        simpa [hp_span] using hq_mem_p
      rcases (Ideal.mem_span_singleton.mp hq_mem_span_g) with ⟨a, hqa⟩
      have hg_dvd_q : g ∣ q := ⟨a, hqa⟩
      have hg_ne_zero : g ≠ 0 := by
        intro hg0
        apply hp_ne_bot
        rw [← hp_span, Ideal.span_singleton_eq_bot]
        exact hg0
      have hg_prime : Prime g :=
        (Ideal.span_singleton_prime hg_ne_zero).1 (by simpa [hp_span] using hpprime)
      have hg_irr : Irreducible g := Prime.irreducible hg_prime
      have hassoc : Associated g q := Irreducible.associated_of_dvd hg_irr hqirr hg_dvd_q
      have hspan_q_eq_p : Ideal.span ({q} : Set R) = p :=
        (Ideal.span_singleton_eq_span_singleton).2 hassoc |>.symm.trans hp_span
      have hspanq_prime : (Ideal.span ({q} : Set R)).IsPrime := by
        simpa [hspan_q_eq_p] using hpprime
      exact (Ideal.span_singleton_prime hq0).1 hspanq_prime
    · intro hqprime
      exact Prime.irreducible hqprime

@[stacks 0ALV]
theorem Ring.krullDimLE_one_of_finite_primeSpectrum [Finite (PrimeSpectrum R)] :
    Ring.KrullDimLE 1 R := by
  classical
  rw [Ring.krullDimLE_iff, ringKrullDim_le_iff_height_le]
  intro p hp
  let P : PrimeSpectrum R := ⟨p, hp⟩
  let s : Finset (PrimeSpectrum R) := Finset.univ.filter fun q => q < P
  have hnot : ¬ (p : Set R) ⊆ ⋃ q ∈ s, q.asIdeal := by
    intro hsub
    rcases (Ideal.subset_union_prime P P (fun q hq _ _ => by simpa using q.isPrime)).1 hsub
      with ⟨q, hq, hpq⟩
    have hq_lt : q < P := by
      have : q ∈ Finset.univ.filter (fun q => q < P) := by simpa [s] using hq
      exact (Finset.mem_filter.1 this).2
    exact (not_le_of_gt hq_lt) hpq
  rcases Set.not_subset.1 hnot with ⟨x, _, hxnot⟩
  have hIle : Ideal.span {x} ≤ p := by
    refine Ideal.span_le.2 ?_
    intro y hy
    rwa [Set.mem_singleton_iff.mp hy]
  rcases Ideal.exists_minimalPrimes_le hIle with ⟨q, hqmin, hqle⟩
  have hqeq : q = p := by
    by_contra hne
    have qPrime : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
    let Q : PrimeSpectrum R := ⟨q, qPrime⟩
    have hQne : Q ≠ P := by
      intro h
      exact hne (by simpa using congrArg PrimeSpectrum.asIdeal h)
    have hQlt : Q < P := lt_of_le_of_ne hqle hQne
    have hQmem : Q ∈ s := by
      have : Q ∈ Finset.univ.filter (fun r => r < P) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hQlt⟩
      simpa [s] using this
    have hxI : x ∈ Ideal.span {x} := by
      refine Ideal.subset_span ?_
      simp
    exact hxnot <| Set.mem_iUnion₂.2 ⟨Q, Finset.mem_coe.2 hQmem, hqmin.1.2 hxI⟩
  have hpmin : p ∈ (Ideal.span {x}).minimalPrimes := by simpa [hqeq] using hqmin
  simpa using Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hpmin

section

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A) (hx : Prime x)

theorem Ideal.isPrincipal_of_isPrincipal_map_away_of_prime
    (hx : Prime x) (p : Ideal A) [p.IsPrime] (hpx : x ∉ p)
    (hprincipal : (Ideal.map (algebraMap A (Localization.Away x)) p).IsPrincipal) :
    p.IsPrincipal := by
  let M : Submonoid A := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors A := by
    refine Submonoid.powers_le.2 ?_
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro a ha
    · exact mul_eq_zero.mp ha |>.resolve_left hx.ne_zero
    · exact mul_eq_zero.mp ha |>.resolve_right hx.ne_zero
  have : IsDomain (Localization.Away x) := by
    simpa [M] using IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x) hM
  by_cases hpbot : p = ⊥
  · simpa [hpbot] using (inferInstance : (⊥ : Ideal A).IsPrincipal)
  let S : Set (Ideal A) :=
    {I | I ≤ p ∧ I.IsPrincipal ∧ Ideal.map
      (algebraMap A (Localization.Away x)) I = Ideal.map (algebraMap A (Localization.Away x)) p}
  have hSnonempty : S.Nonempty := by
    have hex : ∃ y : A, y ∈ p ∧
        Ideal.map (algebraMap A (Localization.Away x)) p =
          Ideal.span {algebraMap A (Localization.Away x) y} := by
      let J : Ideal (Localization.Away x) := Ideal.map (algebraMap A (Localization.Away x)) p
      let g : Localization.Away x := Submodule.IsPrincipal.generator J
      have hgJ : g ∈ J := Submodule.IsPrincipal.generator_mem J
      obtain ⟨a, s, hgs⟩ := IsLocalization.exists_mk'_eq M g
      rw [← hgs] at hgJ
      rw [IsLocalization.mk'_mem_map_algebraMap_iff M] at hgJ
      rcases hgJ with ⟨t, ht, hat⟩
      refine ⟨t * a, hat, ?_⟩
      show J = Ideal.span {algebraMap A (Localization.Away x) (t * a)}
      rw [← Ideal.span_singleton_generator J]
      apply Ideal.span_singleton_eq_span_singleton.2
      have hsunit : IsUnit (algebraMap A (Localization.Away x) s) :=
        IsLocalization.map_units (Localization.Away x) s
      have htunit : IsUnit (algebraMap A (Localization.Away x) t) :=
        IsLocalization.map_units (Localization.Away x) ⟨t, ht⟩
      have hy_eq : algebraMap A (Localization.Away x) (t * a) =
          Submodule.IsPrincipal.generator J *
            ((algebraMap A (Localization.Away x) t) * (algebraMap A (Localization.Away x) s)) := by
        calc
          _ = (algebraMap A (Localization.Away x) t) * (algebraMap A (Localization.Away x) a) := by
            rw [map_mul]
          _ = (algebraMap A (Localization.Away x) t) * (g *
                (algebraMap A (Localization.Away x) s)) := by
            rw [← hgs, IsLocalization.mk'_spec]
          _ = Submodule.IsPrincipal.generator J * ((algebraMap A (Localization.Away x) t) *
              (algebraMap A (Localization.Away x) s)) := by
            dsimp [g]
            ring
      apply associated_of_dvd_dvd
      · exact ⟨(algebraMap A (Localization.Away x) t) *
          (algebraMap A (Localization.Away x) s), hy_eq⟩
      · rcases htunit.mul hsunit with ⟨u, hu⟩
        refine ⟨u⁻¹.1, ?_⟩
        have htmp : algebraMap A (Localization.Away x) (t * a) * u⁻¹.1 =
            Submodule.IsPrincipal.generator J := by
          calc
            algebraMap A (Localization.Away x) (t * a) * u⁻¹.1 =
                (Submodule.IsPrincipal.generator J * ((algebraMap A (Localization.Away x) t) *
                  (algebraMap A (Localization.Away x) s))) * u⁻¹.1 := by rw [hy_eq]
            _ = Submodule.IsPrincipal.generator J * (u * u⁻¹.1) := by
                simp [hu, mul_assoc]
            _ = Submodule.IsPrincipal.generator J := by simp
        exact htmp.symm
    rcases hex with ⟨y, hyp, hy⟩
    refine ⟨Ideal.span ({y} : Set A), ?_⟩
    refine ⟨(Ideal.span_singleton_le_iff_mem p).2 hyp, inferInstance, ?_⟩
    calc
      _ = Ideal.span ({algebraMap A (Localization.Away x) y} : Set (Localization.Away x)) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.map (algebraMap A (Localization.Away x)) p := hy.symm
  obtain ⟨I, hIS, hImax⟩ : ∃ I ∈ S, ∀ J ∈ S, ¬ I < J :=
    (inferInstance : WellFoundedGT (Ideal A)).wf.has_min S hSnonempty
  have hIp : I ≤ p := hIS.1
  have hIprincipal : I.IsPrincipal := hIS.2.1
  have hImap : Ideal.map (algebraMap A (Localization.Away x)) I =
      Ideal.map (algebraMap A (Localization.Away x)) p := hIS.2.2
  let y : A := Submodule.IsPrincipal.generator I
  have hy_mem_I : y ∈ I := Submodule.IsPrincipal.generator_mem I
  have hy_mem_p : y ∈ p := hIp hy_mem_I
  have hIspan : Ideal.span ({y} : Set A) = I := Ideal.span_singleton_generator I
  have hd : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    intro s hs hs'
    rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
    exact hpx (Ideal.IsPrime.mem_of_pow_mem inferInstance n hs')
  have hcomap : Ideal.comap (algebraMap A (Localization.Away x))
      (Ideal.map (algebraMap A (Localization.Away x)) p) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) inferInstance hd
  have hJ_ne_bot : Ideal.map (algebraMap A (Localization.Away x)) p ≠ ⊥ := by
    intro hbot
    have hcbot : Ideal.comap (algebraMap A (Localization.Away x))
        (⊥ : Ideal (Localization.Away x)) = ⊥ := by
      ext a
      show ((algebraMap A (Localization.Away x)) a = 0) ↔ a = 0
      constructor
      · exact (injective_iff_map_eq_zero (algebraMap A (Localization.Away x))).1
          (IsLocalization.injective (Localization.Away x) hM) a
      · intro ha
        simp [ha]
    exact hpbot (by simpa [hbot, hcbot] using hcomap.symm)
  have hI_ne_bot : I ≠ ⊥ := by
    intro hbot
    apply hJ_ne_bot
    rw [← hImap, hbot, Ideal.map_bot]
  have hy_ne_zero : y ≠ 0 := by
    intro hy0
    exact hI_ne_bot <| (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).2 hy0
  have hy_not_dvd : ¬ x ∣ y := by
    intro hxy
    rcases hxy with ⟨b, hb⟩
    have hxb_mem_p : x * b ∈ p := by simpa [hb] using hy_mem_p
    have hb_mem_p : b ∈ p := (Ideal.IsPrime.mem_or_mem inferInstance hxb_mem_p).resolve_left hpx
    have hmap_b :
        Ideal.map (algebraMap A (Localization.Away x)) (Ideal.span ({b} : Set A)) =
          Ideal.map (algebraMap A (Localization.Away x)) p := by
      have hxunit : IsUnit (algebraMap A (Localization.Away x) x) :=
        IsLocalization.map_units (Localization.Away x)
          ⟨x, by exact (Submonoid.mem_powers_iff x x).2 ⟨1, by simp⟩⟩
      have hassoc : Associated (algebraMap A (Localization.Away x) (x * b))
          (algebraMap A (Localization.Away x) b) := by
        apply associated_of_dvd_dvd
        · rcases hxunit with ⟨u, hu⟩
          refine ⟨u⁻¹.1, ?_⟩
          have htmp : algebraMap A (Localization.Away x) (x * b) * u⁻¹.1 =
              algebraMap A (Localization.Away x) b := by
            calc
              _ = ((algebraMap A (Localization.Away x) x) *
                  (algebraMap A (Localization.Away x) b)) * u⁻¹.1 := by
                rw [map_mul]
              _ = algebraMap A (Localization.Away x) b * (u * u⁻¹.1) := by
                  simp [hu, mul_left_comm, mul_comm]
              _ = algebraMap A (Localization.Away x) b := by simp
          exact htmp.symm
        · exact ⟨algebraMap A (Localization.Away x) x, by rw [map_mul, mul_comm]⟩
      calc
        Ideal.map (algebraMap A (Localization.Away x)) (Ideal.span ({b} : Set A)) =
            Ideal.span ({algebraMap A (Localization.Away x) b} : Set (Localization.Away x)) := by
          rw [Ideal.map_span, Set.image_singleton]
        _ = Ideal.span ({algebraMap A (Localization.Away x) (x * b)} :
            Set (Localization.Away x)) := by
          exact (Ideal.span_singleton_eq_span_singleton.2 hassoc).symm
        _ = Ideal.map (algebraMap A (Localization.Away x)) I := by
          rw [← hIspan, hb, Ideal.map_span, Set.image_singleton]
        _ = Ideal.map (algebraMap A (Localization.Away x)) p := hImap
    have hspanb_mem : Ideal.span ({b} : Set A) ∈ S := by
      refine ⟨(Ideal.span_singleton_le_iff_mem p).2 hb_mem_p, inferInstance, hmap_b⟩
    have hI_le_spanb : I ≤ Ideal.span ({b} : Set A) := by
      rw [← hIspan, hb]
      exact (Ideal.span_singleton_le_span_singleton).2 ⟨x, by rw [mul_comm]⟩
    have hb_ne_zero : b ≠ 0 := by
      intro hb0
      apply hy_ne_zero
      rw [hb, hb0]
      simp
    have hI_ne_spanb : I ≠ Ideal.span ({b} : Set A) := by
      intro hEq
      have hb_mem_I : b ∈ I := by
        rw [hEq]
        exact Ideal.subset_span (by simp)
      rw [← hIspan, Ideal.mem_span_singleton] at hb_mem_I
      rcases hb_mem_I with ⟨c, hc⟩
      have hmul : (x * c) * b = 1 * b := by
        calc _ = x * (b * c) := by ring
          _ = x * b * c := by ring
          _ = y * c := by rw [hb]
          _ = b := hc.symm
          _ = 1 * b := by simp
      exact hx.not_unit <| IsUnit.of_mul_eq_one c (mul_right_cancel₀ hb_ne_zero hmul)
    exact hImax (Ideal.span ({b} : Set A)) hspanb_mem (lt_of_le_of_ne hI_le_spanb hI_ne_spanb)
  refine ⟨y, ?_⟩
  show p = Ideal.span ({y} : Set A)
  rw [hIspan]
  apply le_antisymm
  · intro z hz
    have hzmap :
        algebraMap A (Localization.Away x) z ∈
          Ideal.map (algebraMap A (Localization.Away x)) I := by
      rw [hImap]
      exact Ideal.mem_map_of_mem _ hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hzmap
    rcases hzmap with ⟨s, hs, hsz⟩
    rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
    clear hs
    induction n with
    | zero =>
        simpa using hsz
    | succ n ih =>
        have hxz_mem : x * (x ^ n * z) ∈ I := by
          simpa [pow_succ', mul_assoc] using hsz
        rw [← hIspan, Ideal.mem_span_singleton] at hxz_mem
        rcases hxz_mem with ⟨a, ha⟩
        have hxy_or : x ∣ y ∨ x ∣ a := hx.2.2 y a ⟨x ^ n * z, ha.symm⟩
        have hxa : x ∣ a := hxy_or.resolve_left hy_not_dvd
        rcases hxa with ⟨b, hb⟩
        have hcancel : x * (x ^ n * z) = x * (y * b) := by
          simpa [hb, mul_assoc, mul_left_comm, mul_comm] using ha
        have hrest : x ^ n * z = y * b := mul_left_cancel₀ hx.ne_zero hcancel
        apply ih
        rw [← hIspan, Ideal.mem_span_singleton]
        exact ⟨b, hrest⟩
  · exact hIp

theorem ufd_of_ufd_away_of_prime
    (hx : Prime x) [UniqueFactorizationMonoid (Localization.Away x)] :
    UniqueFactorizationMonoid A := by
  let M : Submonoid A := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors A := by
    refine Submonoid.powers_le.2 ?_
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro a ha
    · exact mul_eq_zero.mp ha |>.resolve_left hx.ne_zero
    · exact mul_eq_zero.mp ha |>.resolve_right hx.ne_zero
  have : IsDomain (Localization.Away x) := by
    simpa [M] using IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x) hM
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp hheight
  by_cases hxp : x ∈ p
  · let q : Ideal A := Ideal.span ({x} : Set A)
    have hqprime : q.IsPrime := (Ideal.span_singleton_prime hx.ne_zero).2 hx
    have hqle : q ≤ p := (Ideal.span_singleton_le_iff_mem p).2 hxp
    by_cases hqp : q = p
    · rw [← hqp]
      infer_instance
    · have hq_lt : q < p := lt_of_le_of_ne hqle hqp
      have hbot_lt_q : (⊥ : Ideal A) < q := by
        have hq_ne_bot : q ≠ ⊥ := by
          simpa [q, Ideal.span_singleton_eq_bot] using hx.ne_zero
        exact bot_lt_iff_ne_bot.mpr hq_ne_bot
      have hq_ge_one : (1 : ℕ∞) ≤ q.primeHeight := by
        have htmp : (⊥ : Ideal A).primeHeight + 1 ≤ q.primeHeight :=
          Ideal.primeHeight_add_one_le_of_lt hbot_lt_q
        rw [← Ideal.height_eq_primeHeight, Ideal.height_bot] at htmp
        simpa using htmp
      have hq_add_one : q.primeHeight + 1 ≤ p.primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt hq_lt
      have htwo : (2 : ℕ∞) ≤ p.primeHeight := by
        calc _ = (1 : ℕ∞) + 1 := by norm_num
          _ ≤ q.primeHeight + 1 := by simpa [add_comm] using add_le_add_right hq_ge_one 1
          _ ≤ p.primeHeight := hq_add_one
      rw [hheight] at htwo
      exfalso
      have htwo' : (2 : WithTop ℕ) ≤ 1 := htwo
      norm_num at htwo'
  · have hd : Disjoint (M : Set A) (p : Set A) := by
      rw [Set.disjoint_left]
      intro s hs hs'
      rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
      exact hxp (Ideal.IsPrime.mem_of_pow_mem inferInstance n hs')
    have hmapprime :
        (Ideal.map (algebraMap A (Localization.Away x)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (Localization.Away x) p inferInstance hd
    have hmapheight :
        (Ideal.map (algebraMap A (Localization.Away x)) p).primeHeight = 1 := by
      have htmp := IsLocalization.primeHeight_comap M
        (Ideal.map (algebraMap A (Localization.Away x)) p)
      simpa [IsLocalization.comap_map_of_isPrime_disjoint
        M (Localization.Away x) inferInstance hd, hheight] using htmp.symm
    have hloc_principal :
        (Ideal.map (algebraMap A (Localization.Away x)) p).IsPrincipal :=
      (Ideal.ufd_iff_height_one_primes_principal).1 inferInstance
        (Ideal.map (algebraMap A (Localization.Away x)) p) hmapheight
    exact Ideal.isPrincipal_of_isPrincipal_map_away_of_prime
      x hx p hxp hloc_principal

end
