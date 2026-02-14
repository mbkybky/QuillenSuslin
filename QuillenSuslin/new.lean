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
    obtain ⟨a, ha, hap⟩ : ∃ a ∈ s, a ∈ p := sorry
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
  · sorry

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
