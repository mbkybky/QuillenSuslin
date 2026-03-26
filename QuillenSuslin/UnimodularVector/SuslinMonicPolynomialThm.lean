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
    exact ((Ideal.map C p).mem_leadingCoeff x).2 ⟨C x,
      p.mem_map_C_iff.2 (by
        intro n
        cases n <;> simp [hx]),
      by simp⟩

variable [IsDomain A]

lemma leadingCoeff_mul_le (I J : Ideal A[X]) :
    I.leadingCoeff * J.leadingCoeff ≤ (I * J).leadingCoeff := by
  refine (Ideal.mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  -- The product `p*q` lies in `I*J` and has leading coefficient `a*b`.
  refine ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, Ideal.mul_mem_mul hpI hqJ, ?_⟩
  simp [Polynomial.leadingCoeff_mul, hp, hq]

lemma leadingCoeff_pow_le (I : Ideal A[X]) : ∀ n : ℕ, I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff
   | 0 => by
        have htop : ((⊤ : Ideal A[X]).leadingCoeff : Ideal A) = ⊤ := by
          rw [← Ideal.map_top (C : A →+* A[X])]
          exact leadingCoeff_map_C (A := A) (p := (⊤ : Ideal A))
        simp [pow_zero, Ideal.one_eq_top, htop]
   | n + 1 => by
        simpa [pow_succ] using
          (le_trans (Ideal.mul_mono_left (leadingCoeff_pow_le I n)) <|
            by simpa [mul_assoc] using leadingCoeff_mul_le (I ^ n) I)

lemma leadingCoeff_finset_prod_le (s : Finset (Ideal A[X])) :
    (s.prod fun P => P.leadingCoeff) ≤ (s.prod id).leadingCoeff := by
  classical refine Finset.induction_on s ?_ ?_
  · have htop : ((⊤ : Ideal A[X]).leadingCoeff : Ideal A) = ⊤ := by
      rw [← Ideal.map_top (C : A →+* A[X])]
      exact leadingCoeff_map_C (A := A) (p := (⊤ : Ideal A))
    simp [htop]
  · intro P s hP hs
    have h : P.leadingCoeff * (s.prod id).leadingCoeff ≤ (P * s.prod id).leadingCoeff := by
      simpa [mul_assoc] using leadingCoeff_mul_le P (s.prod id)
    simpa [Finset.prod_insert, hP, Finset.prod_insert, hP, mul_assoc, mul_left_comm, mul_comm] using
      le_trans (Ideal.mul_mono_right hs) h

lemma height_le_one_of_isPrime_comap_C_eq_bot (Q : Ideal A[X]) [Q.IsPrime]
    (hQ : Ideal.comap C Q = ⊥) : Q.height ≤ 1 := by
  let K := FractionRing A
  let M : Submonoid A[X] := Submonoid.map C (nonZeroDivisors A)
  have hdisj : Disjoint (M : Set A[X]) (Q : Set A[X]) := by
    refine Set.disjoint_left.2 ?_
    intro x hxM hxQmem
    rcases (Submonoid.mem_map).1 hxM with ⟨a, ha, rfl⟩
    have : a ∈ (Ideal.comap C Q) := by
      simpa [Ideal.mem_comap] using hxQmem
    have : a = 0 := by
      simpa [hQ] using this
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
  -- Let `p = P ∩ A`.
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
      have hcomap : Ideal.comap (C : (A ⧸ p) →+* (A ⧸ p)[X]) (Ideal.comap e.toRingHom Q) =
          (⊥ : Ideal (A ⧸ p)) := by
        ext a
        have hEq : e (C a) ∈ Q ↔ a = 0 := by
          refine Quotient.inductionOn a ?_
          intro a0
          have hCe : e (C (Ideal.Quotient.mk p a0)) = q (C a0) := by
            simpa [I0, q] using p.polynomialQuotientEquivQuotientPolynomial_map_mk (C a0)
          have hmem : q (C a0) ∈ Q ↔ C a0 ∈ P := by
            constructor
            · intro hx
              rcases (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).1 hx
                with ⟨y, hyP, hyEq⟩
              have hySub : y - C a0 ∈ I0 := Ideal.Quotient.eq.1 hyEq
              have hySubP : y - C a0 ∈ P := hI0_le hySub
              have : y - (y - C a0) ∈ P := Ideal.sub_mem P hyP hySubP
              simpa [sub_sub] using this
            · intro hx
              exact Ideal.mem_map_of_mem q hx
          have hp0 : C a0 ∈ P ↔ a0 ∈ p := by simp [p, Ideal.mem_comap]
          have hq0 : (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) ↔ a0 ∈ p := by
            simpa using Ideal.Quotient.eq_zero_iff_mem
          change e (C (Ideal.Quotient.mk p a0)) ∈ Q ↔ Ideal.Quotient.mk p a0 = (0 : A ⧸ p)
          simpa [hCe] using (hmem.trans hp0).trans hq0.symm
        simpa using hEq
      have hcomap_height : (Ideal.comap e.toRingHom Q).height = Q.height := e.height_comap Q
      calc _ = (Ideal.comap e.toRingHom Q).height := by simpa using hcomap_height.symm
        _ ≤ 1 := height_le_one_of_isPrime_comap_C_eq_bot (Ideal.comap e.toRingHom Q) hcomap
    -- `P.height = p.height + Q.height ≤ p.height + 1`.
    have hP_le : P.height ≤ p.height + 1 := by
      have hheight' : P.height = p.height + Q.height := by simpa [Q, q, I0] using hheight
      simpa [hheight'] using add_le_add_right hQle p.height
    have hp_lt : p < P.leadingCoeff := by
      refine lt_of_le_of_ne hp_le ?_
      -- Choose a polynomial of minimal `natDegree` in `P \ I0`.
      have hex : ∃ f : A[X], f ∈ P ∧ f ∉ I0 := by
        by_contra h
        have hle : P ≤ I0 := by
          intro f hfP
          by_contra hfI0
          exact h ⟨f, hfP, hfI0⟩
        exact hPeq (by simpa [I0] using le_antisymm hle hI0_le)
      let Pred : ℕ → Prop := fun n => ∃ f : A[X], f ∈ P ∧ f ∉ I0 ∧ f.natDegree = n
      have hNat : ∃ n, Pred n := by
        rcases hex with ⟨f, hfP, hfI0⟩
        exact ⟨f.natDegree, f, hfP, hfI0, rfl⟩
      classical
      let n0 : ℕ := Nat.find hNat
      have hn0 : Pred n0 := Nat.find_spec hNat
      rcases hn0 with ⟨f0, hf0P, hf0I0, hf0deg⟩
      have hf0_ne0 : f0 ≠ 0 := by
        intro hf0z
        apply hf0I0
        simp [hf0z]
      have hmin : ∀ m : ℕ, m < n0 → ¬ Pred m := ((n0.find_eq_iff hNat).1 rfl).2
      have hLCnot : f0.leadingCoeff ∉ p := by
        intro hLC
        let d : ℕ := f0.natDegree
        let t : A[X] := C f0.leadingCoeff * Polynomial.X ^ d
        let g : A[X] := f0 - t
        have htP : t ∈ P :=
          P.mul_mem_right (Polynomial.X ^ d) <| by simpa [p, Ideal.mem_comap] using hLC
        have hgP : g ∈ P := by simpa [g] using P.sub_mem hf0P htP
        have htI0 : t ∈ I0 :=
          I0.mul_mem_right (Polynomial.X ^ d) (Ideal.mem_map_of_mem C hLC)
        have hgI0 : g ∉ I0 := by
          intro hg
          exact hf0I0 <| by simpa [g, sub_add_cancel] using I0.add_mem hg htI0
        have hdeg_lt : g.degree < f0.degree := by
          have hdeg_f0 : f0.degree = (d : WithBot ℕ) := by
            simpa [hf0deg, d] using (Polynomial.degree_eq_natDegree hf0_ne0)
          have hdeg_t : t.degree = (d : WithBot ℕ) := by
            have hLC0 : f0.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hf0_ne0
            simpa [t] using (Polynomial.degree_C_mul_X_pow d hLC0)
          have hLCeq : f0.leadingCoeff = t.leadingCoeff := by simp [t]
          simpa [g] using Polynomial.degree_sub_lt (by simp [hdeg_f0, hdeg_t]) hf0_ne0 hLCeq
        have hnat_lt : g.natDegree < n0 := by
          by_cases hg0 : g = 0
          · have hn0' : n0 ≠ 0 := by
              intro hn0z
              have hd0 : d = 0 := by simp [d, hf0deg, hn0z]
              have hf0_eq_t : f0 = t := sub_eq_zero.mp <| by simpa [g] using hg0
              exact hf0I0 <| by simpa [hf0_eq_t] using htI0
            simpa [hg0] using Nat.pos_of_ne_zero hn0'
          · simpa [hf0deg, d] using Polynomial.natDegree_lt_natDegree hg0 hdeg_lt
        exact (hmin g.natDegree hnat_lt) ⟨g, hgP, hgI0, rfl⟩
      have hLCmem : f0.leadingCoeff ∈ P.leadingCoeff :=
        (P.mem_leadingCoeff f0.leadingCoeff).2 ⟨f0, hf0P, rfl⟩
      intro hEq
      exact hLCnot <| by simpa [hEq] using hLCmem
    exact hP_le.trans (Order.add_one_le_of_lt <| Ideal.height_strict_mono_of_is_prime hp_lt)

theorem height_le_height_leadingCoeff (I : Ideal A[X]) : I.height ≤ I.leadingCoeff.height := by
  by_cases hI : I = ⊤
  · subst hI
    have htop : ((⊤ : Ideal A[X]).leadingCoeff : Ideal A) = ⊤ := by
      rw [← Ideal.map_top (C : A →+* A[X])]
      exact leadingCoeff_map_C (A := A) (p := (⊤ : Ideal A))
    simp [htop]
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
      simpa [J] using leadingCoeff_finset_prod_le Pset
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
    simpa [swapS] using (Polynomial.Bivariate.swap_C (R := S) q)
  have hnat_swapC (q : S[X]) : (swapS (C q)).natDegree = q.natDegree := by
    simpa [hswapC q] using Polynomial.natDegree_map_eq_of_injective C_injective q
  have hτ : τ p =  ∑ i ∈ Finset.range (N + 1), (C (p.coeff i)) * (Y + C t) ^ i := by
    simpa [τ, N, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      Polynomial.aeval_eq_sum_range (Y + C t)
  have hswap_YCt : swapS (Y + C t) = base := by
    have hswapY : swapS Y = C X := by
      simpa [swapS] using (Polynomial.Bivariate.swap_Y (R := S))
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
  let bound : WithBot ℕ := (M : WithBot ℕ) + (((N - 1) * K : ℕ) : WithBot ℕ)
  have hdeg_term : ∀ i, i < N → (term i).degree ≤ bound := by
    intro i hi
    have hMi : (p.coeff i).natDegree ≤ M :=
      Finset.le_sup (f := fun j => (p.coeff j).natDegree) (Finset.mem_range.2 hi)
    have hdeg_swapCi : (swapS (C (p.coeff i))).degree ≤ (M : WithBot ℕ) := by
      exact le_trans Polynomial.degree_le_natDegree <| by
        simpa [hnat_swapC (p.coeff i)] using (WithBot.coe_le_coe.2 hMi)
    have hi_le : i ≤ N - 1 := Nat.le_pred_of_lt hi
    have hdeg_base_i : (base ^ i).degree ≤ (((N - 1) * K : ℕ) : WithBot ℕ) := by
      have hbase_i_monic : (base ^ i).Monic := (hbase_monic.pow i)
      have hnat_base_i : (base ^ i).natDegree = i * K := by
        simpa [hbase_natDegree] using (hbase_monic.natDegree_pow i)
      have hdeg_eq : (base ^ i).degree = ((i * K : ℕ) : WithBot ℕ) := by
        have hne : base ^ i ≠ 0 := hbase_i_monic.ne_zero
        simpa [hnat_base_i] using (Polynomial.degree_eq_natDegree hne)
      have hmul_le : ((i * K : ℕ) : WithBot ℕ) ≤ (((N - 1) * K : ℕ) : WithBot ℕ) :=
        WithBot.coe_le_coe.2 (Nat.mul_le_mul_right K hi_le)
      simpa [hdeg_eq] using hmul_le
    simpa [bound] using (Polynomial.degree_mul_le (swapS (C (p.coeff i))) (base ^ i)).trans
        (add_le_add hdeg_swapCi hdeg_base_i)
  have hdeg_rest : rest.degree ≤ bound := by
    have hsup : (Finset.range N).sup (fun i => (term i).degree) ≤ bound := by
      refine Finset.sup_le ?_
      intro i hi
      exact (hdeg_term i (Finset.mem_range.1 hi)).trans le_rfl
    exact le_trans (by
      simpa [rest] using Polynomial.degree_sum_le (Finset.range N) (fun i => term i)) hsup
  have hdeg_lt : rest.degree < main.degree := by
    by_cases hN0 : N = 0
    · have hmain0 : main ≠ 0 := by
        simpa [main, hN0] using hmain_monic.ne_zero
      have hdeg0 : (⊥ : WithBot ℕ) < main.degree :=
        (bot_lt_iff_ne_bot).2 (by simpa [Polynomial.degree_eq_bot] using hmain0)
      simpa [hN0, rest, main] using hdeg0
    have hnat_baseN : (base ^ N).natDegree = N * K := by
      simpa [hbase_natDegree] using (hbase_monic.natDegree_pow N)
    have hnat_main : main.natDegree = p.leadingCoeff.natDegree + N * K := by
      simpa [main, term, hcoeffN, hnat_swapC p.leadingCoeff, hnat_baseN, add_comm] using
        hswapLC_monic.natDegree_mul (hbase_monic.pow N)
    have hmain_deg : main.degree = ((p.leadingCoeff.natDegree + N * K : ℕ) : WithBot ℕ) := by
      have hne : main ≠ 0 := hmain_monic.ne_zero
      simpa [hnat_main] using (Polynomial.degree_eq_natDegree hne)
    have hNK : N * K = (N - 1) * K + K := by
      have hpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hsucc : N = Nat.succ (N - 1) := (Nat.succ_pred_eq_of_pos hpos).symm
      simpa [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using congrArg (fun m => m * K) hsucc
    have hM_lt_TK : M < p.leadingCoeff.natDegree + K :=
      lt_of_lt_of_le (Nat.lt_succ_self M) (Nat.le_add_left _ _)
    have hbound_lt : (M : WithBot ℕ) + (((N - 1) * K : ℕ) : WithBot ℕ) <
        ((p.leadingCoeff.natDegree + N * K : ℕ) : WithBot ℕ) := by
      simpa [hNK, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, bound] using
        WithBot.coe_lt_coe.2 <| Nat.add_lt_add_right hM_lt_TK ((N - 1) * K)
    exact lt_of_le_of_lt hdeg_rest (by simpa [hmain_deg] using hbound_lt)
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
      have hbound : (J.leadingCoeff.height : WithBot ℕ∞) ≤ ringKrullDim R := by
        simpa using J.leadingCoeff.height_le_ringKrullDim_of_ne_top hne
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
    rcases
      (Ideal.mem_map_iff_of_surjective eFirst.toRingHom eFirst.toRingEquiv.surjective).1 hqJ
      with ⟨f0, hf0I, hq⟩
    have hq : eFirst f0 = q := hq
    let eExt : A ≃ₐ[R] A :=
      (eFirst.trans (Polynomial.mapAlgEquiv eB)).trans eFirst.symm
    let eX : B ≃ₐ[R] Polynomial S := MvPolynomial.finSuccEquiv R n
    let H : A ≃ₐ[R] Polynomial (Polynomial S) :=
      eFirst.trans (Polynomial.mapAlgEquiv eX)
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
