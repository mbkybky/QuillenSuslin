import Mathlib

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
    simp at h2
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
        have hn_le : n ≤ 1 := by simpa using hp_height_le_one
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
