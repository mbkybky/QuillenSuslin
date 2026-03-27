/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

open Polynomial Bivariate

open scoped BigOperators

namespace Ideal

variable {A : Type*} [CommRing A]

section Ideal.leadingCoeff

lemma leadingCoeff_mono {I J : Ideal A[X]} (hIJ : I ≤ J) : I.leadingCoeff ≤ J.leadingCoeff := by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff _).2 ⟨p, hIJ hpI, rfl⟩

lemma leadingCoeff_map_C (p : Ideal A) : (Ideal.map C p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases ((Ideal.map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    simpa using p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((Ideal.map C p).mem_leadingCoeff x).2 ⟨C x, Ideal.mem_map_of_mem C hx, by simp⟩

lemma leadingCoeff_top : (⊤ : Ideal A[X]).leadingCoeff = ⊤ := by
  simpa only [← Ideal.map_top C] using leadingCoeff_map_C ⊤

lemma leadingCoeff_mul_le [NoZeroDivisors A] (I J : Ideal A[X]) :
    I.leadingCoeff * J.leadingCoeff ≤ (I * J).leadingCoeff := by
  refine (Ideal.mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  -- The product `p*q` lies in `I*J` and has leading coefficient `a*b`.
  refine ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, Ideal.mul_mem_mul hpI hqJ, ?_⟩
  simp [Polynomial.leadingCoeff_mul, hp, hq]

lemma leadingCoeff_finset_prod_le [NoZeroDivisors A] {ι : Type*} (s : Finset ι)
    (f : ι → Ideal A[X]) : (s.prod fun i => (f i).leadingCoeff) ≤ (s.prod f).leadingCoeff := by
  classical refine Finset.induction_on s ?_ ?_
  · simp [leadingCoeff_top]
  · intro i s hi hs
    have hmul : (f i).leadingCoeff * (s.prod f).leadingCoeff ≤ (f i * s.prod f).leadingCoeff := by
      simpa [mul_assoc] using leadingCoeff_mul_le (f i) (s.prod f)
    simpa [Finset.prod_insert, hi, mul_assoc, mul_left_comm, mul_comm] using
      le_trans (Ideal.mul_mono_right hs) hmul

lemma leadingCoeff_pow_le [NoZeroDivisors A] (I : Ideal A[X]) (n : ℕ) :
    I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff := by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ => I

lemma map_C_comp_of_leadingCoeff_eq_comap (I : Ideal A[X]) (hI : I.leadingCoeff = Ideal.comap C I) :
    Ideal.map C (Ideal.comap C I) = I := by
  let J : Ideal A := Ideal.comap C I
  refine le_antisymm Ideal.map_comap_le (fun f hfI ↦ ?_)
  have hcoeff (m : ℕ) : ∀ g : A[X], g ∈ I → g.support.card = m → ∀ n, g.coeff n ∈ J := by
    refine Nat.strongRecOn' m (fun m ih g hgI hgm n ↦ ?_)
    by_cases hg0 : g = 0
    · simp [J, hg0]
    · have hLCI : g.leadingCoeff ∈ I.leadingCoeff :=
        (I.mem_leadingCoeff g.leadingCoeff).2 ⟨g, hgI, rfl⟩
      have hLCJ : g.leadingCoeff ∈ J := by simpa [J, hI] using hLCI
      by_cases hn : n = g.natDegree
      · simpa [J, hI, hn] using hLCI
      · have hmainJ : C g.leadingCoeff * X ^ g.natDegree ∈ Ideal.map C J :=
          (Ideal.map C J).mul_mem_right (X ^ g.natDegree) (Ideal.mem_map_of_mem C hLCJ)
        have heraseI : g.eraseLead ∈ I := by
          simpa using I.sub_mem hgI (Ideal.map_comap_le hmainJ)
        have hcard : g.eraseLead.support.card < m := by
          simpa [hgm] using Polynomial.eraseLead_support_card_lt hg0
        have heraseCoeff : g.eraseLead.coeff n ∈ J := ih _ hcard _ heraseI rfl n
        simpa [g.eraseLead_coeff_of_ne n hn] using heraseCoeff
  exact Ideal.mem_map_C_iff.2 (hcoeff f.support.card f hfI rfl)

end Ideal.leadingCoeff

lemma height_le_one_of_isPrime_comap_C_eq_bot [IsDomain A] (Q : Ideal A[X]) [Q.IsPrime]
    (hQ : Ideal.comap C Q = ⊥) : Q.height ≤ 1 := by
  let K := FractionRing A
  let M : Submonoid A[X] := Submonoid.map C (nonZeroDivisors A)
  have hdisj : Disjoint (M : Set A[X]) (Q : Set A[X]) := by
    refine Set.disjoint_left.2 ?_
    intro x hxM hxQmem
    rcases (Submonoid.mem_map).1 hxM with ⟨a, ha, rfl⟩
    have : a ∈ (Ideal.comap C Q) := by
      simpa [Ideal.mem_comap] using hxQmem
    have : a = 0 := by simpa [hQ] using this
    have ha0 : (a : A) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).1 ha
    exact ha0 this
  let : Algebra A[X] K[X] := Polynomial.algebra A K
  let : IsLocalization M K[X] := Polynomial.isLocalization (nonZeroDivisors A) K
  have hheight : (Ideal.map (algebraMap A[X] K[X]) Q).height = Q.height := by
    simpa [M] using IsLocalization.height_map_of_disjoint M Q hdisj
  have hne_top : Ideal.map (algebraMap A[X] K[X]) Q ≠ (⊤ : Ideal K[X]) := by
    exact Ideal.IsPrime.ne_top <|
      IsLocalization.isPrime_of_isPrime_disjoint M K[X] Q inferInstance hdisj
  have hdim : ringKrullDim K[X] = (1 : WithBot ℕ∞) := by
    simp [Polynomial.ringKrullDim_of_isNoetherianRing]
  rw [← hheight]
  exact (WithBot.coe_le_coe).1 <| by simpa only [WithBot.coe_one, WithBot.coe_le_one, hdim] using
    (Ideal.map (algebraMap A[X] K[X]) Q).height_le_ringKrullDim_of_ne_top hne_top

variable [IsNoetherianRing A]

lemma height_le_leadingCoeff_of_isPrime (P : Ideal A[X]) [P.IsPrime] :
    P.height ≤ P.leadingCoeff.height := by
  let p : Ideal A := Ideal.comap C P
  have : p.IsPrime := Ideal.comap_isPrime C P
  have hp_le : p ≤ P.leadingCoeff :=
    fun a ha ↦ (P.mem_leadingCoeff a).2 ⟨C a, ha, by simp⟩
  have : P.LiesOver p := ⟨ext fun _ ↦ Iff.rfl⟩
  have hheight : P.height =
      p.height + (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P).height := by
    simpa [Ideal.under_def] using Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  by_cases hPeq : P = Ideal.map C p
  · have hQ : Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P = ⊥ := by
      simpa [hPeq] using Ideal.map_quotient_self (Ideal.map (algebraMap A A[X]) p)
    have hI0_ne_top : Ideal.map (algebraMap A A[X]) p ≠ (⊤ : Ideal A[X]) := by
      simpa [hPeq] using Ideal.IsPrime.ne_top inferInstance
    letI : Nontrivial (A[X] ⧸ Ideal.map (algebraMap A A[X]) p) :=
      (Ideal.Quotient.nontrivial_iff).2 hI0_ne_top
    have hp' : P.height = p.height := by
      rw [hheight, hQ, Ideal.height_bot]
      simp
    simpa [hp'] using Ideal.height_mono hp_le
  · let I0 : Ideal A[X] := Ideal.map C p
    let q : A[X] →+* (A[X] ⧸ I0) := Ideal.Quotient.mk I0
    let Q : Ideal (A[X] ⧸ I0) := Ideal.map q P
    have hI0_le : I0 ≤ P := by simpa [I0] using Ideal.map_comap_le
    have hker : RingHom.ker q ≤ P := by
      simpa [q, Ideal.mk_ker] using hI0_le
    have : Q.IsPrime := by
      have hQprime : (Ideal.map q P).IsPrime :=
        P.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
      simpa [Q] using hQprime
    have hQle : Q.height ≤ 1 := by
      let e : (A ⧸ p)[X] ≃+* (A[X] ⧸ I0) :=
        p.polynomialQuotientEquivQuotientPolynomial
      have hcomap_q : Ideal.comap q Q = P := by
        simpa [Q] using (Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective P).trans <|
          by rw [sup_eq_left.mpr hker]
      have hcomap : Ideal.comap (C : (A ⧸ p) →+* (A ⧸ p)[X]) (Ideal.comap e.toRingHom Q) =
          (⊥ : Ideal (A ⧸ p)) := by
        ext a
        refine Quotient.inductionOn a ?_
        intro a0
        have hCe : e (C (Ideal.Quotient.mk p a0)) = q (C a0) := by
          simpa [I0, q] using p.polynomialQuotientEquivQuotientPolynomial_map_mk (C a0)
        have hmem : q (C a0) ∈ Q ↔ C a0 ∈ P := by
          change C a0 ∈ Ideal.comap q Q ↔ C a0 ∈ P
          simp [hcomap_q]
        have hp0 : C a0 ∈ P ↔ a0 ∈ p := by
          simp [p, Ideal.mem_comap]
        have hq0 : (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) ↔ a0 ∈ p := by
          simpa using Ideal.Quotient.eq_zero_iff_mem
        change e (C (Ideal.Quotient.mk p a0)) ∈ Q ↔ Ideal.Quotient.mk p a0 = (0 : A ⧸ p)
        simpa [hCe] using (hmem.trans hp0).trans hq0.symm
      have hcomap_height : (Ideal.comap e.toRingHom Q).height = Q.height := e.height_comap Q
      calc _ = (Ideal.comap e.toRingHom Q).height := by simpa using hcomap_height.symm
        _ ≤ 1 := height_le_one_of_isPrime_comap_C_eq_bot (Ideal.comap e.toRingHom Q) hcomap
    have hP_le : P.height ≤ p.height + 1 := by simpa [hheight] using add_le_add_right hQle p.height
    have hp_lt : p < P.leadingCoeff := by
      refine lt_of_le_of_ne hp_le ?_
      intro hp_eq
      exact hPeq (map_C_comp_of_leadingCoeff_eq_comap P hp_eq.symm).symm
    exact hP_le.trans (Order.add_one_le_of_lt <| Ideal.height_strict_mono_of_is_prime hp_lt)

theorem height_le_height_leadingCoeff [NoZeroDivisors A] (I : Ideal A[X]) :
    I.height ≤ I.leadingCoeff.height := by
  by_cases hI : I = ⊤
  · subst hI
    simp [leadingCoeff_top]
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A[X] I
  let Pset : Finset (Ideal A[X]) := hfin.toFinset
  let J : Ideal A[X] := Pset.prod id
  have hJ_le_rad : J ≤ I.radical := by
    have hprod : J ≤ Pset.inf id := Ideal.prod_le_inf
    have hinf : (Pset.inf id : Ideal A[X]) = sInf I.minimalPrimes := by
      have : Pset = I.minimalPrimes := by simp [Pset]
      simp [Finset.inf_id_eq_sInf, this]
    simpa [J, hinf, Ideal.sInf_minimalPrimes] using hprod
  rcases Ideal.exists_pow_le_of_le_radical_of_fg hJ_le_rad J.fg_of_isNoetherianRing with ⟨N, hJN⟩
  refine le_iInf fun q => le_iInf fun hq => ?_
  have : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  have hLC : (Pset.prod fun P => P.leadingCoeff) ^ N ≤ I.leadingCoeff := by
    have h₁ : (Pset.prod fun P => P.leadingCoeff) ≤ J.leadingCoeff := by
      simpa [J] using leadingCoeff_finset_prod_le Pset id
    exact le_trans (le_trans (pow_right_mono h₁ N) (leadingCoeff_pow_le J N))
      (leadingCoeff_mono hJN)
  have hLCq' : (Pset.prod fun P => P.leadingCoeff) ≤ q :=
    Ideal.IsPrime.le_of_pow_le (le_trans hLC hq.1.2)
  rcases (Ideal.IsPrime.prod_le inferInstance).1 (by simpa using hLCq') with ⟨P, hP, hPq⟩
  have hPmin : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 hP
  have : P.IsPrime := Ideal.minimalPrimes_isPrime hPmin
  exact le_trans (by simpa [Ideal.height] using (iInf₂_le P hPmin))
    (by simpa [P.height_eq_primeHeight, q.height_eq_primeHeight] using
      le_trans (height_le_leadingCoeff_of_isPrime P) (Ideal.height_mono hPq))

end Ideal

theorem exists_K_monic_swap_algEquivAevalXAddC {S : Type*} [CommRing S] [Nontrivial S] (p : S[X][Y])
    (hp : p.leadingCoeff.Monic) : ∃ K : ℕ, (swap ((algEquivAevalXAddC (X ^ K)) p)).Monic := by
  let N : ℕ := p.natDegree
  let M : ℕ := (Finset.range N).sup fun i => (p.coeff i).natDegree
  let K : ℕ := M + 1
  refine ⟨K, ?_⟩
  let t : S[X] := X ^ K
  let τ : S[X][Y] ≃ₐ[S[X]] S[X][Y] := Polynomial.algEquivAevalXAddC t
  let swapS : S[X][Y] ≃ₐ[S] _ := Polynomial.Bivariate.swap
  let base : S[X][Y] := (C X) + Y ^ K
  let term : ℕ → S[X][Y] := fun i => swapS (C (p.coeff i)) * base ^ i
  have hswapC (q : S[X]) : swapS (C q) = Polynomial.map C q := by
    simpa [swapS] using Polynomial.Bivariate.swap_C q
  have hnat_swapC (q : S[X]) : (swapS (C q)).natDegree = q.natDegree := by
    simpa [hswapC q] using Polynomial.natDegree_map_eq_of_injective C_injective q
  have hτ : τ p =  ∑ i ∈ Finset.range (N + 1), (C (p.coeff i)) * (Y + C t) ^ i := by
    simpa [τ, N, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      Polynomial.aeval_eq_sum_range (Y + C t)
  have hswap_YCt : swapS (Y + C t) = base := by
    have hswapY : swapS Y = C X := by
      simpa [swapS] using
        (Polynomial.Bivariate.swap_Y : Polynomial.Bivariate.swap (Y : S[X][Y]) = C X)
    simp [base, t, K, map_add, hswapY, hswapC]
  have hswap : swapS (τ p) = ∑ i ∈ Finset.range (N + 1), term i := by
    simpa [term, map_sum, map_mul, map_pow, map_add, hswap_YCt] using congrArg swapS hτ
  let rest : S[X][Y] := ∑ i ∈ Finset.range N, term i
  let main : S[X][Y] := term N
  have hswap' : swapS (τ p) = rest + main := by
    simp [hswap, rest, main, Finset.sum_range_succ]
  have hbase_monic : base.Monic := by
    simpa [K, base, add_comm] using Polynomial.monic_X_pow_add_C X (Nat.succ_ne_zero M)
  have hbase_natDegree : base.natDegree = K := by
    simp only [add_comm, natDegree_add_C, natDegree_X_pow, base]
  have hcoeffN : p.coeff N = p.leadingCoeff := by simp [N]
  have hswapLC_monic : (swapS (C p.leadingCoeff)).Monic := by
    simpa [hswapC] using (hp.map (C : S →+* S[X]))
  have hmain_monic : (term N).Monic := by
    simpa [term, hcoeffN] using hswapLC_monic.mul (hbase_monic.pow N)
  let bound : ℕ := M + (N - 1) * K
  have hnat_term : ∀ i, i < N → (term i).natDegree ≤ bound := by
    intro i hi
    have hMi : (p.coeff i).natDegree ≤ M := by
      unfold M
      let f : ℕ → ℕ := fun j => (p.coeff j).natDegree
      change f i ≤ (Finset.range N).sup f
      exact Finset.le_sup (Finset.mem_range.2 hi)
    have hnat_swapCi : (swapS (C (p.coeff i))).natDegree ≤ M := by
      simpa [hnat_swapC (p.coeff i)] using hMi
    have hi_le : i ≤ N - 1 := Nat.le_pred_of_lt hi
    have hnat_base_i : (base ^ i).natDegree = i * K := by
      simpa [hbase_natDegree] using (hbase_monic.natDegree_pow i)
    have hnat_base_i_le : (base ^ i).natDegree ≤ (N - 1) * K := by
      rw [hnat_base_i]
      exact Nat.mul_le_mul_right K hi_le
    calc
      (term i).natDegree ≤ (swapS (C (p.coeff i))).natDegree + (base ^ i).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ M + ((N - 1) * K) := add_le_add hnat_swapCi hnat_base_i_le
      _ = bound := by simp [bound]
  have hnat_rest : rest.natDegree ≤ bound := by
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range N) term ?_
    intro i hi
    exact hnat_term i (Finset.mem_range.1 hi)
  have hdeg_lt : rest.degree < main.degree := by
    by_cases hN0 : N = 0
    · have hmain0 : main ≠ 0 := hmain_monic.ne_zero
      have hdeg0 : (⊥ : WithBot ℕ) < main.degree :=
        (bot_lt_iff_ne_bot).2 (by simpa [Polynomial.degree_eq_bot] using hmain0)
      simpa [hN0, rest, main] using hdeg0
    have hnat_baseN : (base ^ N).natDegree = N * K := by
      simpa [hbase_natDegree] using (hbase_monic.natDegree_pow N)
    have hnat_main : main.natDegree = p.leadingCoeff.natDegree + N * K := by
      simpa [main, term, hcoeffN, hnat_swapC p.leadingCoeff, hnat_baseN, add_comm] using
        hswapLC_monic.natDegree_mul (hbase_monic.pow N)
    have hNK : N * K = (N - 1) * K + K := by
      have hpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hsucc : N = Nat.succ (N - 1) := (Nat.succ_pred_eq_of_pos hpos).symm
      simpa [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using congrArg (fun m => m * K) hsucc
    have hM_lt_TK : M < p.leadingCoeff.natDegree + K :=
      lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_add_left _ _)
    have hbound_lt : bound < p.leadingCoeff.natDegree + N * K := by
      simpa [bound, hNK, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_right hM_lt_TK ((N - 1) * K)
    have hnat_lt : rest.natDegree < main.natDegree := by
      rw [hnat_main]
      exact lt_of_le_of_lt hnat_rest hbound_lt
    exact Polynomial.degree_lt_degree hnat_lt
  have : (swapS (τ p)).Monic := by
    simpa [hswap', rest, main, add_comm, add_left_comm, add_assoc] using
      Polynomial.Monic.add_of_right hmain_monic hdeg_lt
  simpa [swapS, τ, t, K] using this

theorem suslin_monic_polynomial_thm {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (n : ℕ) (I : Ideal (MvPolynomial (Fin (n + 1)) R)) (hI : ringKrullDim R < I.height) :
    ∃ e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R,
      ∃ f : MvPolynomial (Fin (n + 1)) R, f ∈ I ∧
        (MvPolynomial.finSuccEquiv R n (e f)).Monic := by
  induction n with
  | zero =>
    let eEmpty : MvPolynomial (Fin 0) R ≃ₐ[R] R := MvPolynomial.isEmptyAlgEquiv R (Fin 0)
    let e0 : MvPolynomial (Fin (0 + 1)) R ≃ₐ[R] Polynomial R :=
      (MvPolynomial.finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv eEmpty)
    let J : Ideal (Polynomial R) := Ideal.map e0.toRingHom I
    have hheight : J.height = I.height := e0.toRingEquiv.height_map I
    have hJ : ringKrullDim R < J.height := by simpa [hheight] using hI
    have hJ_le : (J.height : WithBot ℕ∞) ≤ (J.leadingCoeff.height : WithBot ℕ∞) :=
      (WithBot.coe_le_coe).2 J.height_le_height_leadingCoeff
    have hLC : ringKrullDim R < (J.leadingCoeff.height : WithBot ℕ∞) := lt_of_lt_of_le hJ hJ_le
    have hLC_top : (J.leadingCoeff : Ideal R) = ⊤ := by
      by_contra hne
      have hbound : (J.leadingCoeff.height : WithBot ℕ∞) ≤ ringKrullDim R :=
        J.leadingCoeff.height_le_ringKrullDim_of_ne_top hne
      exact (not_lt_of_ge hbound) hLC
    rcases (J.mem_leadingCoeff 1).1 (by simp [hLC_top]) with ⟨g, hgJ, hgLC⟩
    have hgMonic : g.Monic := by simp [Polynomial.Monic, hgLC]
    rcases (Ideal.mem_map_iff_of_surjective e0.toRingHom e0.toRingEquiv.surjective).1 hgJ with
      ⟨f, hfI, rfl⟩
    exact ⟨AlgEquiv.refl, f, hfI, by simpa [e0, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom] using
        Polynomial.monic_of_injective eEmpty.toRingEquiv.injective hgMonic⟩
  | succ n ih =>
    let A := MvPolynomial (Fin (n + 2)) R
    let B := MvPolynomial (Fin (n + 1)) R
    let S := MvPolynomial (Fin n) R
    let eFirst : A ≃ₐ[R] Polynomial B :=
      MvPolynomial.finSuccEquiv R (n + 1)
    let J : Ideal (Polynomial B) := Ideal.map eFirst.toRingHom I
    have hJheight : J.height = I.height := eFirst.toRingEquiv.height_map I
    have hJ : ringKrullDim R < J.height := by simpa [hJheight] using hI
    have hJ_le : (J.height : WithBot ℕ∞) ≤ (J.leadingCoeff.height : WithBot ℕ∞) :=
      (WithBot.coe_le_coe).2 (Ideal.height_le_height_leadingCoeff J)
    have hLC : ringKrullDim R < (J.leadingCoeff.height : WithBot ℕ∞) := lt_of_lt_of_le hJ hJ_le
    rcases ih J.leadingCoeff hLC with ⟨eB, g, hgLC, hgMonic⟩
    rcases (J.mem_leadingCoeff g).1 hgLC with ⟨q, hqJ, hqLC⟩
    obtain ⟨f0, hf0I, hq⟩ :=
      (Ideal.mem_map_iff_of_surjective eFirst.toRingHom eFirst.toRingEquiv.surjective).1 hqJ
    have hq : eFirst f0 = q := hq
    let eExt : A ≃ₐ[R] A := (eFirst.trans (Polynomial.mapAlgEquiv eB)).trans eFirst.symm
    let eX : B ≃ₐ[R] Polynomial S := MvPolynomial.finSuccEquiv R n
    let H : A ≃ₐ[R] Polynomial (Polynomial S) := eFirst.trans (Polynomial.mapAlgEquiv eX)
    let p : Polynomial (Polynomial S) := H (eExt f0)
    have hp_lc : p.leadingCoeff = eX (eB g) := by
      have hLC_q1 : (eFirst (eExt f0)).leadingCoeff = eB g := by
        simpa [eExt, hq, hqLC] using
          Polynomial.leadingCoeff_map_of_injective eB.toRingEquiv.injective (eFirst f0)
      simpa [p, H, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom, hLC_q1] using
        Polynomial.leadingCoeff_map_of_injective eX.toRingEquiv.injective (eFirst (eExt f0))
    have hp_lc_monic : p.leadingCoeff.Monic := by simpa [hp_lc, eX] using hgMonic
    rcases exists_K_monic_swap_algEquivAevalXAddC p hp_lc_monic with ⟨K, hmonic_swap⟩
    let τ : (Polynomial (Polynomial S)) ≃ₐ[Polynomial S] (Polynomial (Polynomial S)) :=
      Polynomial.algEquivAevalXAddC ((Polynomial.X : Polynomial S) ^ K)
    let swapR : Polynomial (Polynomial S) ≃ₐ[R] Polynomial (Polynomial S) :=
      (Polynomial.Bivariate.swap).restrictScalars R
    let eTau : A ≃ₐ[R] A :=
      (H.trans ((τ.restrictScalars R).trans swapR)).trans H.symm
    let eTotal : A ≃ₐ[R] A := eExt.trans eTau
    have hHp : H (eTotal f0) = Polynomial.Bivariate.swap (τ p) := by
      simp [eTotal, eTau, p, H, swapR]
    have hmo : (H (eTotal f0)).Monic := by simpa [hHp, τ] using hmonic_swap
    set q0 := MvPolynomial.finSuccEquiv R (n + 1) (eTotal f0) with hq0
    have hq0_monic : q0.Monic := by
      simpa [hq0, H, eFirst, eX, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom] using
        Polynomial.monic_of_injective eX.toRingEquiv.injective hmo
    exact ⟨eTotal, f0, hf0I, by simpa [hq0] using hq0_monic⟩
