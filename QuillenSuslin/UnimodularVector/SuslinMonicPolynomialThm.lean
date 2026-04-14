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

variable {R : Type*} [CommRing R]

section leadingCoeff

@[gcongr]
lemma leadingCoeff_mono {I J : Ideal R[X]} (hIJ : I ≤ J) : I.leadingCoeff ≤ J.leadingCoeff := by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff p.leadingCoeff).2 ⟨p, hIJ hpI, rfl⟩

@[simp]
lemma map_C_leadingCoeff (p : Ideal R) : (map C p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

@[simp]
lemma leadingCoeff_top : (⊤ : Ideal R[X]).leadingCoeff = ⊤ := by simp [← map_top C]

lemma leadingCoeff_mul_le [NoZeroDivisors R] (I J : Ideal R[X]) :
    I.leadingCoeff * J.leadingCoeff ≤ (I * J).leadingCoeff := by
  refine (mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  exact ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, mul_mem_mul hpI hqJ, by simp [hp, hq]⟩

lemma leadingCoeff_finset_prod_le [NoZeroDivisors R] {ι : Type*} (s : Finset ι)
    (f : ι → Ideal R[X]) : (s.prod fun i ↦ (f i).leadingCoeff) ≤ (s.prod f).leadingCoeff := by
  classical refine Finset.induction_on s (by simp) ?_
  intro i s hi hs
  simpa [hi] using (mul_mono_right hs).trans (leadingCoeff_mul_le (f i) (s.prod f))

lemma leadingCoeff_pow_le [NoZeroDivisors R] (I : Ideal R[X]) (n : ℕ) :
    I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff := by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ ↦ I

lemma map_C_comap_of_comap_eq_leadingCoeff (I : Ideal R[X]) (hI : comap C I = I.leadingCoeff) :
    map C (comap C I) = I := by
  refine le_antisymm map_comap_le (fun f hfI ↦ ?_)
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f with | _ _ ih
  have h : C f.leadingCoeff * X ^ f.natDegree ∈ map C (comap C I) :=
    (map C (comap C I)).mul_mem_right (X ^ f.natDegree) <| mem_map_of_mem C <| by
      simpa [hI] using (I.mem_leadingCoeff f.leadingCoeff).2 ⟨f, hfI, rfl⟩
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hzero
  · have he : f.eraseLead ∈ I := by simpa using I.sub_mem hfI (map_comap_le h)
    simpa using (map C (comap C I)).add_mem (ih _ (by simpa [hn] using hlt) _ he rfl) h
  · rwa [← f.eraseLead_add_C_mul_X_pow, hzero, zero_add]

end leadingCoeff

lemma height_le_one_of_isPrime_comap_C_eq_bot [IsDomain R] (Q : Ideal R[X]) [Q.IsPrime]
    (hQ : comap C Q = ⊥) : Q.height ≤ 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := Submonoid.map C (nonZeroDivisors R)
  have hdisj : Disjoint (M : Set R[X]) (Q : Set R[X]) := by
    refine Set.disjoint_left.2 ?_
    intro x hxM hxQmem
    rcases (Submonoid.mem_map).1 hxM with ⟨a, ha, rfl⟩
    have ha0 : (a : R) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).1 ha
    exact ha0 (by simpa [hQ, mem_comap] using (show a ∈ comap C Q from hxQmem))
  let : Algebra R[X] K[X] := Polynomial.algebra R K
  let : IsLocalization M K[X] := Polynomial.isLocalization (nonZeroDivisors R) K
  have hheight : (map (algebraMap R[X] K[X]) Q).height = Q.height :=
    IsLocalization.height_map_of_disjoint M Q hdisj
  have hne_top : map (algebraMap R[X] K[X]) Q ≠ (⊤ : Ideal K[X]) :=
    IsPrime.ne_top <| IsLocalization.isPrime_of_isPrime_disjoint M K[X] Q inferInstance hdisj
  exact (WithBot.coe_le_coe).1 <| by
    simpa [← hheight, Polynomial.ringKrullDim_of_isNoetherianRing] using
      (map (algebraMap R[X] K[X]) Q).height_le_ringKrullDim_of_ne_top hne_top

variable [IsNoetherianRing R]

lemma height_le_leadingCoeff_of_isPrime (P : Ideal R[X]) [P.IsPrime] :
    P.height ≤ P.leadingCoeff.height := by
  let p : Ideal R := comap C P
  have : p.IsPrime := comap_isPrime C P
  have hp_le : p ≤ P.leadingCoeff :=
    fun a ha ↦ (P.mem_leadingCoeff a).2 ⟨C a, ha, by simp⟩
  have : P.LiesOver p := ⟨ext fun _ ↦ Iff.rfl⟩
  have hheight : P.height =
      p.height + (map (Quotient.mk (map (algebraMap R R[X]) p)) P).height := by
    simpa [under_def] using height_eq_height_add_of_liesOver_of_hasGoingDown p P
  by_cases hPeq : P = map C p
  · have hQ : map (Quotient.mk (map (algebraMap R R[X]) p)) P = ⊥ := by
      simpa [hPeq] using map_quotient_self (map (algebraMap R R[X]) p)
    have hQ' : map (Quotient.mk (map C p)) P = ⊥ := by simpa using hQ
    have hP_le : P.height ≤ p.height := by
      calc _ ≤ p.height + (map (Quotient.mk (map C p)) P).height := by simpa [hheight] using by rfl
        _ = p.height := by simp [hQ', height_bot]
    exact hP_le.trans (height_mono hp_le)
  · let I0 : Ideal R[X] := map C p
    let q : R[X] →+* (R[X] ⧸ I0) := Quotient.mk I0
    let Q : Ideal (R[X] ⧸ I0) := map q P
    have hker : RingHom.ker q ≤ P := by simpa [I0, q, mk_ker] using map_comap_le
    have : Q.IsPrime := P.map_isPrime_of_surjective Quotient.mk_surjective hker
    have hQle : Q.height ≤ 1 := by
      let e := p.polynomialQuotientEquivQuotientPolynomial
      have hcomap_q : comap q Q = P := by
        simpa [Q] using (comap_map_of_surjective' q Quotient.mk_surjective P).trans <|
          by rw [sup_eq_left.mpr hker]
      have hcomap : comap (C : (R ⧸ p) →+* (R ⧸ p)[X]) (comap e.toRingHom Q) =
          (⊥ : Ideal (R ⧸ p)) := by
        ext a
        refine Quotient.inductionOn a ?_
        intro a0
        have hCe : e (C (Quotient.mk p a0)) = q (C a0) := by
          simpa [I0, q] using p.polynomialQuotientEquivQuotientPolynomial_map_mk (C a0)
        have hmem : q (C a0) ∈ Q ↔ C a0 ∈ P := by
          change C a0 ∈ comap q Q ↔ C a0 ∈ P
          simp [hcomap_q]
        have hp0 : C a0 ∈ P ↔ a0 ∈ p := by simp [p, mem_comap]
        have hq0 : (Quotient.mk p a0 = (0 : R ⧸ p)) ↔ a0 ∈ p := by
          simpa using Quotient.eq_zero_iff_mem
        change e (C (Quotient.mk p a0)) ∈ Q ↔ Quotient.mk p a0 = (0 : R ⧸ p)
        simpa [hCe] using (hmem.trans hp0).trans hq0.symm
      exact (e.height_comap Q).symm.le.trans <|
        height_le_one_of_isPrime_comap_C_eq_bot (comap e.toRingHom Q) hcomap
    have hP_le : P.height ≤ p.height + 1 := by simpa [hheight] using add_le_add_right hQle p.height
    have hp_lt : p < P.leadingCoeff := lt_of_le_of_ne hp_le fun hp_eq ↦
      hPeq (map_C_comap_of_comap_eq_leadingCoeff P hp_eq).symm
    exact hP_le.trans (Order.add_one_le_of_lt <| height_strict_mono_of_is_prime hp_lt)

theorem height_le_height_leadingCoeff [NoZeroDivisors R] (I : Ideal R[X]) :
    I.height ≤ I.leadingCoeff.height := by
  by_cases hI : I = ⊤
  · subst hI
    simp
  have hfin : I.minimalPrimes.Finite := finite_minimalPrimes_of_isNoetherianRing R[X] I
  let Pset : Finset (Ideal R[X]) := hfin.toFinset
  let J : Ideal R[X] := Pset.prod id
  have hJ_le_rad : J ≤ I.radical := by
    simpa [J, Pset, Finset.inf_id_eq_sInf, sInf_minimalPrimes] using
      (prod_le_inf : J ≤ Pset.inf id)
  rcases exists_pow_le_of_le_radical_of_fg hJ_le_rad J.fg_of_isNoetherianRing with ⟨N, hJN⟩
  refine le_iInf fun q ↦ le_iInf fun hq ↦ ?_
  have : q.IsPrime := minimalPrimes_isPrime hq
  rcases (IsPrime.prod_le inferInstance).1 <|
      IsPrime.le_of_pow_le <|
        (pow_right_mono (by simpa [J] using leadingCoeff_finset_prod_le Pset id) N).trans <|
          (leadingCoeff_pow_le J N).trans <| (leadingCoeff_mono hJN).trans hq.1.2
    with ⟨P, hP, hPq⟩
  have hPmin : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 hP
  have : P.IsPrime := minimalPrimes_isPrime hPmin
  exact le_trans (by simpa [height] using (iInf₂_le P hPmin))
    (by simpa [P.height_eq_primeHeight, q.height_eq_primeHeight] using
      le_trans (height_le_leadingCoeff_of_isPrime P) (height_mono hPq))

end Ideal

noncomputable def shearSwap (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (K : ℕ) : Polynomial (Polynomial S) ≃ₐ[R] Polynomial (Polynomial S) :=
  ((algEquivAevalXAddC (X ^ K)).restrictScalars R).trans (Bivariate.swap.restrictScalars R)

theorem exists_K_monic_shearSwap {R : Type*} [CommRing R] [Nontrivial R] (p : R[X][Y])
    (hp : p.leadingCoeff.Monic) : ∃ K : ℕ, (shearSwap R R K p).Monic := by
  let N : ℕ := p.natDegree
  let M : ℕ := (Finset.range N).sup fun i ↦ (p.coeff i).natDegree
  let K : ℕ := M + 1
  refine ⟨K, ?_⟩
  let τ : R[X][Y] ≃ₐ[R[X]] R[X][Y] := Polynomial.algEquivAevalXAddC (X ^ K)
  let swapR : R[X][Y] ≃ₐ[R] R[X][Y] := Polynomial.Bivariate.swap
  let base : R[X][Y] := (C X) + Y ^ K
  let term : ℕ → R[X][Y] := fun i ↦ swapR (C (p.coeff i)) * base ^ i
  have hswapC (q : R[X]) : swapR (C q) = Polynomial.map C q := by
    simpa [swapR] using Polynomial.Bivariate.swap_C q
  have hnat_swapC (q : R[X]) : (swapR (C q)).natDegree = q.natDegree := by
    simpa [hswapC q] using Polynomial.natDegree_map_eq_of_injective C_injective q
  have hτ : τ p = ∑ i ∈ Finset.range (N + 1), (C (p.coeff i)) * (Y + C X ^ K) ^ i := by
    simpa [τ, N, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      Polynomial.aeval_eq_sum_range (Y + C X ^ K)
  have hswap_YCt : swapR (Y + C X ^ K) = base := by
    have hswapY : swapR Y = C X := Polynomial.Bivariate.swap_Y
    simp [base, K, map_add, hswapY, hswapC]
  have hswap : swapR (τ p) = ∑ i ∈ Finset.range (N + 1), term i := by
    simpa [term, map_sum, map_mul, map_pow, map_add, hswap_YCt] using congrArg swapR hτ
  let rest : R[X][Y] := ∑ i ∈ Finset.range N, term i
  have hswap' : swapR (τ p) = rest + term N := by simp [hswap, rest, Finset.sum_range_succ]
  have hbase_monic : base.Monic := by
    simpa [K, base, add_comm] using Polynomial.monic_X_pow_add_C X (Nat.succ_ne_zero M)
  have hbase_natDegree : base.natDegree = K := by simp [base]
  have hswapLC_monic : (swapR (C p.leadingCoeff)).Monic := by
    simpa [hswapC] using (hp.map (C : R →+* R[X]))
  have hmain_monic : (term N).Monic := by
    simpa [term, N] using hswapLC_monic.mul (hbase_monic.pow N)
  let bound : ℕ := M + (N - 1) * K
  have hnat_term : ∀ i, i < N → (term i).natDegree ≤ bound := by
    intro i hi
    have hMi : (p.coeff i).natDegree ≤ M :=
      Finset.le_sup (f := fun j ↦ (p.coeff j).natDegree) (Finset.mem_range.2 hi)
    have hnat_base_i_le : (base ^ i).natDegree ≤ (N - 1) * K := by
      rw [show (base ^ i).natDegree = i * K by
        simpa [hbase_natDegree] using hbase_monic.natDegree_pow i]
      exact Nat.mul_le_mul_right K (Nat.le_pred_of_lt hi)
    calc _ ≤ (swapR (C (p.coeff i))).natDegree + (base ^ i).natDegree := natDegree_mul_le
      _ ≤ M + ((N - 1) * K) := by simpa [hnat_swapC (p.coeff i)] using add_le_add hMi hnat_base_i_le
      _ = bound := by simp [bound]
  have hnat_rest : rest.natDegree ≤ bound :=
    natDegree_sum_le_of_forall_le (Finset.range N) term fun i hi ↦
      hnat_term i (Finset.mem_range.1 hi)
  have hdeg_lt : rest.degree < (term N).degree := by
    by_cases hN0 : N = 0
    · have hmain0 : term N ≠ 0 := hmain_monic.ne_zero
      have hdeg0 : (⊥ : WithBot ℕ) < (term N).degree :=
        (bot_lt_iff_ne_bot).2 (by simpa [Polynomial.degree_eq_bot] using hmain0)
      simpa [hN0, rest] using hdeg0
    have hnat_baseN : (base ^ N).natDegree = N * K := by
      simpa [hbase_natDegree] using (hbase_monic.natDegree_pow N)
    have hnat_main : (term N).natDegree = p.leadingCoeff.natDegree + N * K := by
      simpa [term, N, hnat_swapC p.leadingCoeff, hnat_baseN, add_comm] using
        hswapLC_monic.natDegree_mul (hbase_monic.pow N)
    have hNK : N * K = (N - 1) * K + K := by
      simpa [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using
        congrArg (fun m ↦ m * K) (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hN0)).symm
    have hM_lt_TK : M < p.leadingCoeff.natDegree + K :=
      lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_add_left _ _)
    have hbound_lt : bound < p.leadingCoeff.natDegree + N * K := by
      simpa [bound, hNK, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_right hM_lt_TK ((N - 1) * K)
    have hnat_lt : rest.natDegree < (term N).natDegree := by
      rw [hnat_main]
      exact lt_of_le_of_lt hnat_rest hbound_lt
    exact Polynomial.degree_lt_degree hnat_lt
  change (swapR (τ p)).Monic
  simpa [hswap'] using hmain_monic.add_of_right hdeg_lt

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
    let J : Ideal (Polynomial R) := I.map e0.toRingHom
    have hheight : J.height = I.height := e0.toRingEquiv.height_map I
    have hLC := lt_of_lt_of_le (by simpa [hheight] using hI)
      ((WithBot.coe_le_coe).2 J.height_le_height_leadingCoeff)
    have hLC_top : (J.leadingCoeff : Ideal R) = ⊤ := by
      by_contra hne
      exact (not_lt_of_ge (J.leadingCoeff.height_le_ringKrullDim_of_ne_top hne)) hLC
    rcases (J.mem_leadingCoeff 1).1 (by simp [hLC_top]) with ⟨g, hgJ, hgLC⟩
    have hgMonic : g.Monic := by simp [Polynomial.Monic, hgLC]
    obtain ⟨f, hfI, rfl⟩ := (Ideal.mem_map_iff_of_surjective e0.toRingHom e0.surjective).1 hgJ
    exact ⟨AlgEquiv.refl, f, hfI, by simpa [e0, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom] using
        Polynomial.monic_of_injective eEmpty.toRingEquiv.injective hgMonic⟩
  | succ n ih =>
    let A := MvPolynomial (Fin (n + 2)) R
    let B := MvPolynomial (Fin (n + 1)) R
    let S := MvPolynomial (Fin n) R
    let eFirst : A ≃ₐ[R] Polynomial B := MvPolynomial.finSuccEquiv R (n + 1)
    let J := I.map eFirst.toRingHom
    have hJheight : J.height = I.height := eFirst.toRingEquiv.height_map I
    have hLC := lt_of_lt_of_le (by simpa [hJheight] using hI)
      ((WithBot.coe_le_coe).2 (Ideal.height_le_height_leadingCoeff J))
    rcases ih J.leadingCoeff hLC with ⟨eB, g, hgLC, hgMonic⟩
    rcases (J.mem_leadingCoeff g).1 hgLC with ⟨q, hqJ, hqLC⟩
    obtain ⟨f0, hf0I, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective eFirst.toRingHom eFirst.surjective).1 hqJ
    let eExt : A ≃ₐ[R] A := (eFirst.trans (Polynomial.mapAlgEquiv eB)).trans eFirst.symm
    let eX : B ≃ₐ[R] Polynomial S := MvPolynomial.finSuccEquiv R n
    let H : A ≃ₐ[R] Polynomial (Polynomial S) := eFirst.trans (Polynomial.mapAlgEquiv eX)
    have hp_lc : (H (eExt f0)).leadingCoeff = eX (eB g) := by
      have hLC_q1 : (eFirst (eExt f0)).leadingCoeff = eB g := by
        simpa [eExt] using Polynomial.leadingCoeff_map_of_injective
          eB.toRingEquiv.injective (eFirst f0) |>.trans (congrArg eB hqLC)
      simpa [H, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom, hLC_q1] using
        Polynomial.leadingCoeff_map_of_injective eX.toRingEquiv.injective (eFirst (eExt f0))
    have hp_lc_monic : (H (eExt f0)).leadingCoeff.Monic := by simpa [hp_lc, eX] using hgMonic
    rcases exists_K_monic_shearSwap (H (eExt f0)) hp_lc_monic with ⟨K, hmonic_swap⟩
    let eTau : A ≃ₐ[R] A := (H.trans (shearSwap R S K)).trans H.symm
    let eTotal : A ≃ₐ[R] A := eExt.trans eTau
    have hmo : (H (eTotal f0)).Monic := by simpa [eTotal, eTau, H, shearSwap] using hmonic_swap
    set q0 := MvPolynomial.finSuccEquiv R (n + 1) (eTotal f0) with hq0
    have hq0_monic : q0.Monic := by
      simpa [hq0, H, eFirst, eX, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom] using
        Polynomial.monic_of_injective eX.toRingEquiv.injective hmo
    exact ⟨eTotal, f0, hf0I, by simpa [hq0] using hq0_monic⟩
