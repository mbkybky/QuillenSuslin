import Mathlib

open Polynomial Bivariate

open scoped BigOperators

namespace MvPolynomial

variable (R : Type*) [CommSemiring R]

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
multivariable polynomials in `Fin n`, singling out the **last** variable. -/
noncomputable def finSuccEquivLast (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R _root_.finSuccEquivLast).trans (optionEquivLeft R (Fin n))

@[simp]
lemma finSuccEquivLast_X_castSucc (n : ℕ) (i : Fin n) :
    finSuccEquivLast R n (X (Fin.castSucc i)) = Polynomial.C (X i) := by
  simp [finSuccEquivLast, _root_.finSuccEquivLast_castSucc]

@[simp]
lemma finSuccEquivLast_X_last (n : ℕ) :
    finSuccEquivLast R n (X (Fin.last n)) = Polynomial.X := by
  simp [finSuccEquivLast, _root_.finSuccEquivLast_last]

@[simp]
lemma finSuccEquivLast_symm_X (n : ℕ) :
    (finSuccEquivLast R n).symm Polynomial.X = X (Fin.last n) := by
  simpa [finSuccEquivLast_X_last R n] using (finSuccEquivLast R n).symm_apply_apply (X (Fin.last n))

@[simp]
lemma finSuccEquivLast_symm_C_X (n : ℕ) (i : Fin n) :
    (finSuccEquivLast R n).symm (Polynomial.C (X i)) = X (Fin.castSucc i) := by
  simpa [finSuccEquivLast_X_castSucc R n i] using
    (finSuccEquivLast R n).symm_apply_apply (X (Fin.castSucc i))

end MvPolynomial

namespace Ideal

variable {A : Type*} [CommRing A]

lemma leadingCoeff_mono {I J : Ideal A[X]} (hIJ : I ≤ J) : I.leadingCoeff ≤ J.leadingCoeff := by
  intro x hx
  rcases (Ideal.mem_leadingCoeff (I := I) x).1 hx with ⟨p, hpI, rfl⟩
  exact (Ideal.mem_leadingCoeff (I := J) _).2 ⟨p, hIJ hpI, rfl⟩
lemma leadingCoeff_map_C (p : Ideal A) :
    (Ideal.map (C : A →+* A[X]) p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases (Ideal.mem_leadingCoeff (I := Ideal.map (C : A →+* A[X]) p) x).1 hx with ⟨f, hf, rfl⟩
    have hx' : f.leadingCoeff ∈ p := by
      -- In `p.map C`, all coefficients lie in `p`, hence so does the leading coefficient.
      have hf' : ∀ n : ℕ, f.coeff n ∈ p := (Ideal.mem_map_C_iff (I := p)).1 hf
      -- Avoid `simp [Polynomial.leadingCoeff]` loops.
      change f.coeff f.natDegree ∈ p
      exact hf' f.natDegree
    simpa using hx'
  · intro hx
    exact (Ideal.mem_leadingCoeff (I := Ideal.map (C : A →+* A[X]) p) x).2 ⟨Polynomial.C x,
      (Ideal.mem_map_C_iff (I := p)).2 (by
        intro n
        cases n <;> simp [hx]),
      by simp⟩

@[simp]
lemma leadingCoeff_top : ((⊤ : Ideal A[X]).leadingCoeff : Ideal A) = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    exact (Ideal.mem_leadingCoeff (I := (⊤ : Ideal A[X])) x).2 ⟨Polynomial.C x, trivial, by simp⟩

variable [IsDomain A]

lemma leadingCoeff_mul_le (I J : Ideal A[X]) :
    I.leadingCoeff * J.leadingCoeff ≤ (I * J).leadingCoeff := by
  classical
  -- Use the `Ideal.mul_le` characterization for the product on the coefficient ring.
  refine (Ideal.mul_le).2 ?_
  intro a ha b hb
  rcases (Ideal.mem_leadingCoeff (I := I) a).1 ha with ⟨p, hpI, hp⟩
  rcases (Ideal.mem_leadingCoeff (I := J) b).1 hb with ⟨q, hqJ, hq⟩
  -- The product `p*q` lies in `I*J` and has leading coefficient `a*b`.
  refine (Ideal.mem_leadingCoeff (I := I * J) (a * b)).2 ?_
  refine ⟨p * q, Ideal.mul_mem_mul hpI hqJ, ?_⟩
  -- `A` is a domain, so leading coefficients multiply.
  simp [Polynomial.leadingCoeff_mul, hp, hq]

lemma leadingCoeff_pow_le (I : Ideal A[X]) : ∀ n : ℕ, I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff
   | 0 => by
       simp [pow_zero, Ideal.one_eq_top, leadingCoeff_top (A := A)]
   | n + 1 => by
       -- `I.leadingCoeff^(n+1) = I.leadingCoeff^n * I.leadingCoeff`.
       have h₁ : I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff := leadingCoeff_pow_le I n
       -- Multiply the inequality by `I.leadingCoeff` and use the multiplicativity lemma.
       have hmul : (I.leadingCoeff ^ n) * I.leadingCoeff ≤ ((I ^ n) * I).leadingCoeff := by
         refine le_trans (Ideal.mul_mono_left h₁) ?_
         simpa [mul_assoc] using leadingCoeff_mul_le (I := I ^ n) (J := I)
       simpa [pow_succ] using hmul

lemma leadingCoeff_finset_prod_le (s : Finset (Ideal A[X])) :
    (s.prod fun P => P.leadingCoeff) ≤ (s.prod id).leadingCoeff := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro P s hP hs
    have h₁ : P.leadingCoeff * (s.prod fun Q => Q.leadingCoeff) ≤
        P.leadingCoeff * (s.prod id).leadingCoeff := by
      exact Ideal.mul_mono_right hs
    have h₂ : P.leadingCoeff * (s.prod id).leadingCoeff ≤ (P * s.prod id).leadingCoeff := by
      simpa [mul_assoc] using leadingCoeff_mul_le P (s.prod id)
    simpa [Finset.prod_insert, hP, Finset.prod_insert, hP, mul_assoc, mul_left_comm, mul_comm] using
      le_trans h₁ h₂

lemma height_le_one_of_isPrime_comap_C_eq_bot (Q : Ideal A[X]) [Q.IsPrime]
    (hQ : Ideal.comap (C : A →+* A[X]) Q = ⊥) :
    Q.height ≤ 1 := by
  classical
  let K := FractionRing A
  let M : Submonoid A[X] := Submonoid.map (C : A →+* A[X]) (nonZeroDivisors A)
  have hdisj : Disjoint (M : Set A[X]) (Q : Set A[X]) := by
    refine Set.disjoint_left.2 ?_
    intro x hxM hxQmem
    rcases (Submonoid.mem_map).1 hxM with ⟨a, ha, rfl⟩
    have : a ∈ (Ideal.comap (C : A →+* A[X]) Q) := by
      simpa [Ideal.mem_comap] using hxQmem
    have : a = 0 := by
      simpa [hQ] using this
    -- But `a ∈ A⁰` implies `a ≠ 0` in a domain.
    have ha0 : (a : A) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).1 ha
    exact ha0 this
  -- Height is preserved under localization at a disjoint submonoid.
  classical
  -- Turn on the polynomial localization instances locally.
  let _ : Algebra A[X] K[X] := Polynomial.algebra A K
  let _ : IsLocalization M K[X] := Polynomial.isLocalization (nonZeroDivisors A) K
  have hheight : (Ideal.map (algebraMap A[X] K[X]) Q).height = Q.height := by
    -- `K[X]` is a localization of `A[X]` at `M`.
    -- We rely on `Polynomial.isLocalization` to provide the instance.
    -- See `Mathlib/RingTheory/KrullDimension/Polynomial.lean` for the same pattern.
    classical
    simpa [M] using IsLocalization.height_map_of_disjoint (M := M) (p := Q) hdisj
  -- Now bound the height in `K[X]` by `dim K[X] = 1`.
  have hne_top : Ideal.map (algebraMap A[X] K[X]) Q ≠ (⊤ : Ideal K[X]) := by
    -- It is a proper ideal since it is prime.
    have hprime : (Ideal.map (algebraMap A[X] K[X]) Q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M K[X] Q inferInstance hdisj
    exact Ideal.IsPrime.ne_top hprime
  have hdim : ringKrullDim K[X] = (1 : WithBot ℕ∞) := by
    -- `K` is a field, so `dim K[X] = 1`.
    -- Use the noetherian polynomial dimension formula.
    simp [Polynomial.ringKrullDim_of_isNoetherianRing]
  have hbound : (Ideal.map (algebraMap A[X] K[X]) Q).height ≤ (1 : ℕ∞) := by
    -- Height is bounded by Krull dimension.
    have h' :=
      Ideal.height_le_ringKrullDim_of_ne_top (I := Ideal.map (algebraMap A[X] K[X]) Q) hne_top
    -- Convert the inequality from `WithBot ℕ∞`.
    have : (↑(Ideal.map (algebraMap A[X] K[X]) Q).height : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
      simpa [hdim] using h'
    exact (WithBot.coe_le_coe).1 this
  -- Transport the bound back to `Q`.
  calc
    Q.height = (Ideal.map (algebraMap A[X] K[X]) Q).height := by simpa using hheight.symm
    _ ≤ 1 := hbound

variable [IsNoetherianRing A]

lemma height_le_leadingCoeff_of_isPrime (P : Ideal A[X]) [P.IsPrime] :
    P.height ≤ P.leadingCoeff.height := by
  classical
  -- Let `p = P ∩ A`.
  let p : Ideal A := Ideal.comap (C : A →+* A[X]) P
  haveI : p.IsPrime := Ideal.comap_isPrime (f := (C : A →+* A[X])) P
  have hp_le : p ≤ P.leadingCoeff := by
    intro a ha
    have : Polynomial.C a ∈ P := ha
    exact (Ideal.mem_leadingCoeff (I := P) a).2 ⟨Polynomial.C a, this, by simp⟩
  -- Use the height formula for primes lying over `p`.
  haveI : P.LiesOver p := ⟨by
    -- `p = under A P` by definition.
    ext a
    rfl⟩
  have hheight : P.height = p.height +
      (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P).height := by
    simpa [Ideal.under_def] using Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  -- Split into the extended-prime case and the strict case.
  by_cases hPeq : P = Ideal.map (C : A →+* A[X]) p
  · -- Then the quotient image is `⊥`, so `P.height = p.height`.
    have hQ : Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P = ⊥ := by
      -- Avoid `subst` since `p` depends on `P`.
      simp [hPeq]
    -- Conclude using `p ≤ P.leadingCoeff`.
    have hp' : P.height = p.height := by
      -- `⊥.height = 0`
      rw [hheight, hQ]
      simp
    -- `p.height ≤ P.leadingCoeff.height` by monotonicity.
    have : p.height ≤ P.leadingCoeff.height := Ideal.height_mono hp_le
    simpa [hp'] using this
  · -- The quotient image has height ≤ 1.
    let I0 : Ideal A[X] := Ideal.map (C : A →+* A[X]) p
    let q : A[X] →+* (A[X] ⧸ I0) := Ideal.Quotient.mk I0
    let Q : Ideal (A[X] ⧸ I0) := Ideal.map q P
    have hI0_le : I0 ≤ P := by
      simpa [I0] using (Ideal.map_comap_le (f := (C : A →+* A[X])) (K := P))
    have hker : RingHom.ker q ≤ P := by
      simpa [q, Ideal.mk_ker] using hI0_le
    haveI : Q.IsPrime := by
      -- `Q` is prime since `P` is prime and contains the kernel of the quotient map.
      have hQprime : (Ideal.map q P).IsPrime :=
        Ideal.map_isPrime_of_surjective (f := q) Ideal.Quotient.mk_surjective (I := P) hker
      simpa [Q] using hQprime
    have hQle : Q.height ≤ 1 := by
      -- Transport to `(A ⧸ p)[X]` and use the localization-to-fraction-field bound.
      let e : (A ⧸ p)[X] ≃+* (A[X] ⧸ I0) :=
        p.polynomialQuotientEquivQuotientPolynomial
      -- Pull back along `e` and apply the bound for primes lying over `⊥`.
      have hcomap : Ideal.comap (C : (A ⧸ p) →+* (A ⧸ p)[X]) (Ideal.comap e.toRingHom Q) =
          (⊥ : Ideal (A ⧸ p)) := by
        -- The contracted ideal is `⊥` since `P` lies over `p`.
        ext a
        -- Reduce to showing `e (C a) ∈ Q ↔ a = 0`.
        have hEq : e (C a) ∈ Q ↔ a = 0 := by
          -- Unfold the quotient element `a`.
          refine Quotient.inductionOn a ?_
          intro a0
          -- Rewrite `e (C (mk a0))` as the image of `C a0` in `A[X] ⧸ I0`.
          have hCe : e (C (Ideal.Quotient.mk p a0)) = q (Polynomial.C a0) := by
            -- `C (mk a0) = map (mk p) (C a0)`.
            simpa [I0, q] using p.polynomialQuotientEquivQuotientPolynomial_map_mk (Polynomial.C a0)
          -- Membership in the image ideal is equivalent to membership in `P` since `ker q ≤ P`.
          have hmem : q (Polynomial.C a0) ∈ Q ↔ Polynomial.C a0 ∈ P := by
            constructor
            · intro hx
              rcases (Ideal.mem_map_iff_of_surjective (f := q) Ideal.Quotient.mk_surjective).1 hx
                with ⟨y, hyP, hyEq⟩
              have hySub : y - Polynomial.C a0 ∈ I0 := (Ideal.Quotient.eq (I := I0)).1 hyEq
              have hySubP : y - Polynomial.C a0 ∈ P := hI0_le hySub
              have : y - (y - Polynomial.C a0) ∈ P := Ideal.sub_mem P hyP hySubP
              simpa [sub_sub] using this
            · intro hx
              exact Ideal.mem_map_of_mem q hx
          -- Finish by chasing through the definitions of `p` and the quotient.
          -- `C a0 ∈ P ↔ a0 ∈ p ↔ mk a0 = 0`.
          have hp0 : Polynomial.C a0 ∈ P ↔ a0 ∈ p := by
            simp [p, Ideal.mem_comap]
          have hq0 : (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) ↔ a0 ∈ p := by
            simpa using (Ideal.Quotient.eq_zero_iff_mem (I := p) (a := a0))
          -- Now conclude.
          calc
            e (C (Ideal.Quotient.mk p a0)) ∈ Q ↔ q (Polynomial.C a0) ∈ Q := by simp [hCe]
            _ ↔ Polynomial.C a0 ∈ P := hmem
            _ ↔ a0 ∈ p := hp0
            _ ↔ (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) := by
                  exact hq0.symm
        -- Now `simp` finishes the ideal equality.
        simp [Ideal.mem_comap, hEq]
      have hbound' : (Ideal.comap e.toRingHom Q).height ≤ 1 :=
        height_le_one_of_isPrime_comap_C_eq_bot (Ideal.comap e.toRingHom Q) hcomap
      -- Transport back along `e`.
      have hcomap_height : (Ideal.comap e.toRingHom Q).height = Q.height :=
        e.height_comap Q
      calc
        Q.height = (Ideal.comap e.toRingHom Q).height := by simpa using hcomap_height.symm
        _ ≤ 1 := hbound'
    -- Use `P.height = p.height + Q.height ≤ p.height + 1`.
    have hP_le : P.height ≤ p.height + 1 := by
      have hheight' : P.height = p.height + Q.height := by
        -- Rewrite the height formula using `I0`/`q`/`Q`.
        simpa [Q, q, I0] using hheight
      rw [hheight']
      exact add_le_add_right hQle p.height
    -- And `p.height + 1 ≤ P.leadingCoeff.height` since `p < P.leadingCoeff`.
    have hp_lt : p < P.leadingCoeff := by
      -- `p ≤ P.leadingCoeff` is already `hp_le`, it suffices to show strictness.
      refine lt_of_le_of_ne hp_le ?_
      -- Choose a polynomial of minimal `natDegree` in `P \ I0`.
      have hex : ∃ f : A[X], f ∈ P ∧ f ∉ I0 := by
        by_contra h
        have hle : P ≤ I0 := by
          intro f hfP
          by_contra hfI0
          exact h ⟨f, hfP, hfI0⟩
        have : P = I0 := le_antisymm hle hI0_le
        exact hPeq (by simpa [I0] using this)
      classical
      let Pred : ℕ → Prop := fun n =>
        ∃ f : A[X], f ∈ P ∧ f ∉ I0 ∧ f.natDegree = n
      have hNat : ∃ n, Pred n := by
        rcases hex with ⟨f, hfP, hfI0⟩
        exact ⟨f.natDegree, f, hfP, hfI0, rfl⟩
      let n0 : ℕ := Nat.find hNat
      have hn0 : Pred n0 := Nat.find_spec hNat
      rcases hn0 with ⟨f0, hf0P, hf0I0, hf0deg⟩
      have hf0_ne0 : f0 ≠ 0 := by
        intro hf0z
        apply hf0I0
        simp [hf0z]
      -- Minimality of `n0`.
      have hmin : ∀ m : ℕ, m < n0 → ¬ Pred m := by
        have hEq := (Nat.find_eq_iff (m := n0) (h := hNat)).1 rfl
        exact hEq.2
      -- If the leading coefficient lay in `p`, we could cancel the leading term
      -- and contradict minimality.
      have hLCnot : f0.leadingCoeff ∉ p := by
        intro hLC
        let d : ℕ := f0.natDegree
        let t : A[X] := Polynomial.C f0.leadingCoeff * Polynomial.X ^ d
        let g : A[X] := f0 - t
        have htP : t ∈ P := by
          have hC : Polynomial.C f0.leadingCoeff ∈ P := by
            simpa [p, Ideal.mem_comap] using hLC
          exact P.mul_mem_right (Polynomial.X ^ d) hC
        have hgP : g ∈ P := by
          simpa [g] using P.sub_mem hf0P htP
        have htI0 : t ∈ I0 := by
          have hC : Polynomial.C f0.leadingCoeff ∈ I0 :=
            Ideal.mem_map_of_mem (C : A →+* A[X]) hLC
          exact I0.mul_mem_right (Polynomial.X ^ d) hC
        have hgI0 : g ∉ I0 := by
          intro hg
          have : g + t ∈ I0 := I0.add_mem hg htI0
          have : f0 ∈ I0 := by simpa [g, sub_add_cancel] using this
          exact hf0I0 this
        -- Show `g.natDegree < n0`.
        have hdeg_lt : g.degree < f0.degree := by
          have hdeg_f0 : f0.degree = (d : WithBot ℕ) := by
            simpa [hf0deg, d] using (Polynomial.degree_eq_natDegree hf0_ne0)
          have hdeg_t : t.degree = (d : WithBot ℕ) := by
            have hLC0 : f0.leadingCoeff ≠ 0 := (Polynomial.leadingCoeff_ne_zero).2 hf0_ne0
            simpa [t] using (Polynomial.degree_C_mul_X_pow (R := A) d hLC0)
          have hLCeq : f0.leadingCoeff = t.leadingCoeff := by
            simp [t]
          have : g.degree < f0.degree := by
            -- apply `degree_sub_lt` to `f0` and `t`
            have := Polynomial.degree_sub_lt (p := f0) (q := t) (by simp [hdeg_f0, hdeg_t])
              hf0_ne0 hLCeq
            simpa [g] using this
          exact this
        have hnat_lt : g.natDegree < n0 := by
          by_cases hg0 : g = 0
          · -- Then `g.natDegree = 0`, and we just need `0 < n0`.
            have hn0' : n0 ≠ 0 := by
              intro hn0z
              have hd0 : d = 0 := by simp [d, hf0deg, hn0z]
              have hf0_eq_t : f0 = t := by
                have : f0 - t = 0 := by simpa [g] using hg0
                exact sub_eq_zero.mp this
              have : f0 ∈ I0 := by
                -- If `n0 = 0`, then `f0 = t ∈ I0`, contradiction.
                simpa [hf0_eq_t] using htI0
              exact hf0I0 this
            have : (0 : ℕ) < n0 := Nat.pos_of_ne_zero hn0'
            simpa [hg0] using this
          · have : g.natDegree < f0.natDegree := Polynomial.natDegree_lt_natDegree hg0 hdeg_lt
            simpa [hf0deg, d] using this
        -- `g` witnesses `Pred g.natDegree` with a smaller degree, contradiction.
        have : Pred g.natDegree := ⟨g, hgP, hgI0, rfl⟩
        exact (hmin g.natDegree hnat_lt) this
      -- The leading coefficient gives strictness.
      have hLCmem : f0.leadingCoeff ∈ P.leadingCoeff :=
        (Ideal.mem_leadingCoeff (I := P) f0.leadingCoeff).2 ⟨f0, hf0P, rfl⟩
      intro hEq
      have : f0.leadingCoeff ∈ p := by simpa [hEq] using hLCmem
      exact hLCnot this
    have hp_height_le : p.height + 1 ≤ P.leadingCoeff.height := by
      -- Show the bound holds for each minimal prime over `P.leadingCoeff`.
      refine le_iInf₂ ?_
      intro q hq
      haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
      have hpq : p < q := lt_of_lt_of_le hp_lt (hq.1.2)  -- `P.leadingCoeff ≤ q`
      have : p.primeHeight + 1 ≤ q.primeHeight := Ideal.primeHeight_add_one_le_of_lt hpq
      simpa [Ideal.height_eq_primeHeight (I := p), Ideal.height_eq_primeHeight (I := q)] using this
    exact le_trans hP_le hp_height_le

theorem height_le_height_leadingCoeff (I : Ideal A[X]) : I.height ≤ I.leadingCoeff.height := by
  classical
  by_cases hI : I = ⊤
  · subst hI
    simp
  -- Let `P₁, …, P_r` be the minimal primes over `I`.
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing (R := A[X]) I
  let Pset : Finset (Ideal A[X]) := hfin.toFinset
  have hPmem : ∀ P : Ideal A[X], P ∈ Pset ↔ P ∈ I.minimalPrimes := fun P =>
    (Set.Finite.mem_toFinset hfin)
  let J : Ideal A[X] := Pset.prod id
  have hJ_le_rad : J ≤ I.radical := by
    -- `∏ Pᵢ ≤ ⋂ Pᵢ = rad I`.
    have hprod : J ≤ Pset.inf id := Ideal.prod_le_inf (s := Pset) (f := id)
    have hinf : (Pset.inf id : Ideal A[X]) = sInf I.minimalPrimes := by
      -- Convert the finset infimum to `sInf`.
      have : (↑Pset : Set (Ideal A[X])) = I.minimalPrimes := by
        simp [Pset]
      simp [Finset.inf_id_eq_sInf, this]
    simpa [J, hinf, Ideal.sInf_minimalPrimes] using hprod
  -- Some power of the product is contained in `I`.
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing J
  rcases Ideal.exists_pow_le_of_le_radical_of_fg hJ_le_rad hJfg with ⟨N, hJN⟩
  -- Now show `I.height ≤ q.primeHeight` for every `q` minimal over `I.leadingCoeff`.
  refine le_iInf fun q => le_iInf fun hq => ?_
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  -- Get some minimal prime `P ∈ I.minimalPrimes` whose leading-coefficient ideal
  -- is contained in `q`.
  have hLC : (Pset.prod fun P => P.leadingCoeff) ^ N ≤ I.leadingCoeff := by
    have h₁ : (Pset.prod fun P => P.leadingCoeff) ≤ J.leadingCoeff := by
      simpa [J] using leadingCoeff_finset_prod_le Pset
    have h₂ : (Pset.prod fun P => P.leadingCoeff) ^ N ≤ J.leadingCoeff ^ N := pow_right_mono h₁ N
    have h₃ : J.leadingCoeff ^ N ≤ (J ^ N).leadingCoeff := leadingCoeff_pow_le J N
    have h₄ : (J ^ N).leadingCoeff ≤ I.leadingCoeff :=
      leadingCoeff_mono (A := A) hJN
    exact le_trans (le_trans h₂ h₃) h₄
  have hLCq : (Pset.prod fun P => P.leadingCoeff) ^ N ≤ q := le_trans hLC hq.1.2
  have hLCq' : (Pset.prod fun P => P.leadingCoeff) ≤ q :=
    (Ideal.IsPrime.le_of_pow_le (I := Pset.prod fun P => P.leadingCoeff) (P := q) hLCq)
  rcases (Ideal.IsPrime.prod_le (hp := (show q.IsPrime from inferInstance)) (s := Pset)
      (f := fun P => P.leadingCoeff)).1 (by simpa using hLCq') with ⟨P, hP, hPq⟩
  have hPmin : P ∈ I.minimalPrimes := (hPmem P).1 hP
  haveI : P.IsPrime := Ideal.minimalPrimes_isPrime hPmin
  have hI_le_P : I.height ≤ P.primeHeight := by
    -- `I.height` is the infimum over minimal primes, so it is bounded by each such prime height.
    simpa [Ideal.height] using (iInf₂_le P hPmin)
  have hP_le : P.primeHeight ≤ q.primeHeight := by
    -- `P.height ≤ P.leadingCoeff.height ≤ q.height`.
    have hP' : P.height ≤ P.leadingCoeff.height := height_le_leadingCoeff_of_isPrime (A := A) P
    have hP'' : P.primeHeight ≤ P.leadingCoeff.height := by
      simpa [Ideal.height_eq_primeHeight (I := P)] using hP'
    have hmono : P.leadingCoeff.height ≤ q.height := Ideal.height_mono hPq
    -- Replace `q.height` with `q.primeHeight`.
    have : P.primeHeight ≤ q.primeHeight := by
      simpa [Ideal.height_eq_primeHeight (I := q)] using le_trans hP'' hmono
    exact this
  exact le_trans hI_le_P hP_le

end Ideal

lemma bivariate_swap_C {A : Type*} [CommSemiring A] (p : A[X]) :
    Polynomial.Bivariate.swap (R := A) (C p : A[X][Y]) = Polynomial.map (C : A →+* A[X]) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hp' : (aeval (Y : A[X][Y])) p = Polynomial.map (C : A →+* A[X]) p := by
      simpa [Polynomial.Bivariate.swap_apply] using hp
    have hq' : (aeval (Y : A[X][Y])) q = Polynomial.map (C : A →+* A[X]) q := by
      simpa [Polynomial.Bivariate.swap_apply] using hq
    -- Unfold `swap` on `C (p + q)` and use additivity of `aeval`/`map`.
    simp [Polynomial.Bivariate.swap_apply, hp', hq', Polynomial.map_add]
  | monomial n a =>
    -- `C (monomial n a) = monomial 0 (monomial n a)` and swap exchanges the two exponents.
    simp [C_mul_X_pow_eq_monomial, Polynomial.map_monomial]

lemma finSuccEquiv_map_finSuccEquivLast_apply {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPolynomial (Fin (n + 2)) R) :
    (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast (R := R) n)
        (MvPolynomial.finSuccEquiv R (n + 1) f)) =
      Polynomial.Bivariate.swap (R := MvPolynomial (Fin n) R)
        (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R n)
          (MvPolynomial.finSuccEquivLast (R := R) (n + 1) f)) := by
  let F : MvPolynomial (Fin (n + 2)) R →ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin n) R)) :=
    ((MvPolynomial.finSuccEquiv R (n + 1)).trans
        (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast R n))).toAlgHom
  let swapR : Polynomial (Polynomial (MvPolynomial (Fin n) R)) ≃ₐ[R] _ :=
    (Polynomial.Bivariate.swap).restrictScalars R
  let G : MvPolynomial (Fin (n + 2)) R →ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin n) R)) :=
    (((MvPolynomial.finSuccEquivLast R (n + 1)).trans
            (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R n))).trans
          swapR).toAlgHom
  have hFG : F = G := by
    refine MvPolynomial.algHom_ext ?_
    intro i
    -- Split `i : Fin (n+2)` as either `castSucc j` or the last index.
    cases i using Fin.lastCases with
    | last =>
      -- The last variable becomes the *inner* variable.
      have hlast : MvPolynomial.finSuccEquiv R (n + 1) (MvPolynomial.X (Fin.last (n + 1))) =
          Polynomial.C (MvPolynomial.X (Fin.last n)) := by
        -- `Fin.last (n+1) = (Fin.last n).succ`.
        simpa [Fin.succ_last] using
          (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := n + 1) (j := Fin.last n))
      have hF : F (MvPolynomial.X (Fin.last (n + 1))) =
          (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) :
            (MvPolynomial (Fin n) R)[X][Y]) := by
        -- Map the coefficient `X (Fin.last n)` to the inner variable via `finSuccEquivLast`.
        simp [F, hlast, MvPolynomial.finSuccEquivLast_X_last R n]
      have hG' : G (MvPolynomial.X (Fin.last (n + 1))) =
          swapR (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
        simp [G]
      have hG : G (MvPolynomial.X (Fin.last (n + 1))) =
          (Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) :
            (MvPolynomial (Fin n) R)[X][Y]) := by
        -- `swap` sends the outer variable `Y` to the inner variable `C X`.
        simp [hG', swapR]
      simp [hF, hG]
    | cast i =>
      -- Now split `i : Fin (n+1)` into `0` or `succ j`.
      cases i using Fin.cases with
      | zero =>
        -- The distinguished variable for `finSuccEquiv` is `0`.
        have hF : F (MvPolynomial.X (0 : Fin (n + 2))) = (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
          simp [F, MvPolynomial.finSuccEquiv_X_zero]
        have hG' : G (MvPolynomial.X (0 : Fin (n + 2))) =
            swapR (C (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) :
              (MvPolynomial (Fin n) R)[X][Y]) := by
          -- `X 0` becomes the inner variable, then `swap` sends `C X` to `Y`.
          have h0 : MvPolynomial.finSuccEquivLast R (n + 1) (MvPolynomial.X (0 : Fin (n + 2))) =
              Polynomial.C (MvPolynomial.X (0 : Fin (n + 1))) := by
            simpa using MvPolynomial.finSuccEquivLast_X_castSucc R (n + 1) (0 : Fin (n + 1))
          -- Unfold the definitions and use the behavior on `X 0`.
          simp [G, h0, MvPolynomial.finSuccEquiv_X_zero]
        have hG : G (MvPolynomial.X (0 : Fin (n + 2))) = (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- `swap (C X) = Y`.
          have : swapR (C (Polynomial.X : Polynomial (MvPolynomial (Fin n) R)) :
              (MvPolynomial (Fin n) R)[X][Y]) = Y := by
            simp [swapR]
          simp [hG', this]
        simp [hF, hG]
      | succ j =>
        -- Variables other than `0` are sent to constants in the bivariate polynomial ring.
        -- `castSucc (succ j) = succ (castSucc j)` aligns the two normal forms.
        have hF : F (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- Under `finSuccEquiv`, this variable is a constant coefficient `X (castSucc j)`.
          -- Under `finSuccEquivLast`, `X (castSucc j)` stays a constant coefficient.
          simp [F, MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquivLast_X_castSucc]
        have hG' : G (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
            swapR (Polynomial.C (Polynomial.C (MvPolynomial.X j)) :
              (MvPolynomial (Fin n) R)[X][Y]) := by
          have hcast : MvPolynomial.finSuccEquivLast R (n + 1)
              (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
              Polynomial.C (MvPolynomial.X (Fin.succ j)) := by
            -- `Fin.castSucc (Fin.succ j)` is a non-last variable.
            -- Rewrite `j.castSucc.succ` as `Fin.castSucc (Fin.succ j)`.
            simpa [Fin.castSucc_succ] using
              (MvPolynomial.finSuccEquivLast_X_castSucc R (n + 1) (Fin.succ j))
          -- Now use `finSuccEquiv` on the coefficient `X (succ j)`.
          simp [G, hcast, MvPolynomial.finSuccEquiv_X_succ]
        have hswap : swapR
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) =
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- This element is constant in both variables, so `swap` fixes it.
          -- Use `swap (C p) = map C p` and simplify.
          -- Here `p = C (X j)` is a constant polynomial, so mapping coefficients does nothing.
          simp only [swapR, AlgEquiv.restrictScalars_apply, bivariate_swap_C,
            Polynomial.map_C]
        have hG : G (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
            (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          simp [hG', hswap]
        simp [hF, hG]
  -- Finish by rewriting both sides in terms of `F` and `G`.
  simpa [F, G] using congrArg (fun h => h f) hFG

theorem exists_K_monic_swap_algEquivAevalXAddC {S : Type*} [CommRing S] [Nontrivial S] (p : S[X][Y])
    (hp : p.leadingCoeff.Monic) : ∃ K : ℕ,
      (Polynomial.Bivariate.swap ((Polynomial.algEquivAevalXAddC ((X : S[X]) ^ K)) p)).Monic := by
  classical
  -- `p ≠ 0` since its leading coefficient is monic.
  have hp0 : p ≠ 0 := by
    intro h
    have : p.leadingCoeff = 0 := by simp [h]
    exact hp.ne_zero this
  -- Degree in `Y`.
  let N : ℕ := p.natDegree
  -- A bound on degrees-in-`X` of the lower `Y`-coefficients.
  let M : ℕ := (Finset.range N).sup fun i => (p.coeff i).natDegree
  -- Choose `K > M`.
  let K : ℕ := M + 1
  refine ⟨K, ?_⟩
  -- Abbreviations.
  let t : S[X] := (X : S[X]) ^ K
  let τ : S[X][Y] ≃ₐ[S[X]] S[X][Y] := Polynomial.algEquivAevalXAddC t
  let swapS : S[X][Y] ≃ₐ[S] _ := Polynomial.Bivariate.swap
  let base : S[X][Y] := (C (X : S[X]) : S[X][Y]) + (Y : S[X][Y]) ^ K
  let term : ℕ → S[X][Y] := fun i =>
    swapS (C (p.coeff i) : S[X][Y]) * base ^ i
  -- Expand `τ p` as a sum over coefficients.
  have hτ : τ p =
      ∑ i ∈ Finset.range (N + 1), (C (p.coeff i) : S[X][Y]) * (Y + C t) ^ i := by
    -- `τ` is `p(Y) ↦ p(Y + t)`, i.e. `aeval (Y + C t)`.
    -- Then use the standard `aeval` expansion.
    -- (The `simp` below uses the `@[simps]` lemma for `algEquivAevalXAddC`.)
    simpa [τ, N, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
      (Polynomial.aeval_eq_sum_range (R := S[X]) (S := S[X][Y]) (p := p) (x := (Y + C t)))
  -- Simplify `swap (Y + C t)`.
  have hswap_YCt : swapS (Y + C t : S[X][Y]) = base := by
    -- `swap Y = C X` and `swap (C (X^K)) = Y^K`.
    simp [swapS, base, t, K]
  -- Push `swap` through the above sum.
  have hswap : swapS (τ p) = ∑ i ∈ Finset.range (N + 1), term i := by
    have := congrArg swapS hτ
    -- `swap` is a ring hom, simplify each summand.
    simpa [term, map_sum, map_mul, map_pow, map_add, hswap_YCt] using this
  -- Split off the top `Y`-degree term.
  let rest : S[X][Y] := ∑ i ∈ Finset.range N, term i
  let main : S[X][Y] := term N
  have hswap' : swapS (τ p) = rest + main := by
    -- `range (N+1)` splits as `range N` and `N`.
    have hsum : (∑ i ∈ Finset.range (N + 1), term i) = rest + main := by
      simp [rest, main, Finset.sum_range_succ]
    -- Combine with `hswap`.
    simpa [hswap] using (hswap.trans hsum)
  -- Monicity of the `base` polynomial (as a polynomial in `Y` over `S[X]`).
  have hK0 : K ≠ 0 := Nat.succ_ne_zero M
  have hbase_monic : base.Monic := by
    -- `Y^K + C X` is monic.
    simpa [base, add_comm, add_left_comm, add_assoc] using
      (Polynomial.monic_X_pow_add_C (R := S[X]) (a := (X : S[X])) (n := K) hK0)
  have hbase_natDegree : base.natDegree = K := by
    -- `natDegree (Y^K + C X) = K`.
    simp [base, add_comm]
  -- The leading coefficient term is monic.
  have hcoeffN : p.coeff N = p.leadingCoeff := by
    simp [N]
  have hswapLC_monic : (swapS (C p.leadingCoeff : S[X][Y])).Monic := by
    -- `swap (C g) = map C g`, and mapping coefficients preserves monicity.
    have hswapC : swapS (C p.leadingCoeff : S[X][Y]) =
        Polynomial.map (C : S →+* S[X]) p.leadingCoeff := by
      simpa [swapS] using (bivariate_swap_C (A := S) (p := p.leadingCoeff))
    simpa [hswapC] using (hp.map (C : S →+* S[X]))
  have hmain_monic : (term N).Monic := by
    -- `term N = swap (C leadingCoeff) * base^N`.
    have h1 : (swapS (C (p.coeff N) : S[X][Y])).Monic := by
      simpa [hcoeffN] using hswapLC_monic
    simpa [term] using h1.mul (hbase_monic.pow N)
  -- Degree bounds for the lower-degree part.
  let bound : WithBot ℕ := (M : WithBot ℕ) + (((N - 1) * K : ℕ) : WithBot ℕ)
  have hdeg_term : ∀ i, i < N → (term i).degree ≤ bound := by
    intro i hi
    -- Bound the `swap (C (coeff i))` factor by `M`.
    have hi_mem : i ∈ Finset.range N := Finset.mem_range.2 hi
    have hMi : (p.coeff i).natDegree ≤ M :=
      Finset.le_sup (s := Finset.range N) (f := fun j => (p.coeff j).natDegree) hi_mem
    have hdeg_swapCi : (swapS (C (p.coeff i) : S[X][Y])).degree ≤ (M : WithBot ℕ) := by
      -- Convert via natDegree.
      have hnat : (swapS (C (p.coeff i) : S[X][Y])).natDegree = (p.coeff i).natDegree := by
        have hswapC : swapS (C (p.coeff i) : S[X][Y]) =
            Polynomial.map (C : S →+* S[X]) (p.coeff i) := by
          simpa [swapS] using (bivariate_swap_C (A := S) (p := p.coeff i))
        simpa [hswapC] using
          (Polynomial.natDegree_map_eq_of_injective
            (hf := (Polynomial.C_injective : Function.Injective (C : S →+* S[X])))
            (p := (p.coeff i)))
      have hdeg_le_nat : (swapS (C (p.coeff i) : S[X][Y])).degree ≤
          (swapS (C (p.coeff i) : S[X][Y])).natDegree := Polynomial.degree_le_natDegree
      exact le_trans hdeg_le_nat (by
        simpa [hnat] using (WithBot.coe_le_coe.2 hMi))
    -- Bound `base^i` by `(N-1)*K` in degree.
    have hi_le : i ≤ N - 1 := Nat.le_pred_of_lt hi
    have hdeg_base_i : (base ^ i).degree ≤ (((N - 1) * K : ℕ) : WithBot ℕ) := by
      -- Since `base` is monic of natDegree `K`, `base^i` is monic of natDegree `i*K`.
      have hbase_i_monic : (base ^ i).Monic := (hbase_monic.pow i)
      have hnat_base_i : (base ^ i).natDegree = i * K := by
        -- `natDegree (base^i) = i * natDegree base = i*K`.
        simpa [hbase_natDegree] using (hbase_monic.natDegree_pow i)
      have hdeg_eq : (base ^ i).degree = ((i * K : ℕ) : WithBot ℕ) := by
        have hne : base ^ i ≠ 0 := hbase_i_monic.ne_zero
        simpa [hnat_base_i] using (Polynomial.degree_eq_natDegree hne)
      -- Now use `i*K ≤ (N-1)*K`.
      have hmul_le : ((i * K : ℕ) : WithBot ℕ) ≤ (((N - 1) * K : ℕ) : WithBot ℕ) :=
        WithBot.coe_le_coe.2 (Nat.mul_le_mul_right K hi_le)
      simpa [hdeg_eq] using hmul_le
    -- Combine degrees using `degree_mul_le`.
    have hdeg_mul : (term i).degree ≤ (M : WithBot ℕ) + (((N - 1) * K : ℕ) : WithBot ℕ) := by
      have := Polynomial.degree_mul_le
        (p := swapS (C (p.coeff i) : S[X][Y]))
        (q := base ^ i)
      exact le_trans this (add_le_add hdeg_swapCi hdeg_base_i)
    simpa [bound] using hdeg_mul
  have hdeg_rest : rest.degree ≤ bound := by
    -- Use `degree_sum_le` and the uniform bound for summands.
    have hsup : (Finset.range N).sup (fun i => (term i).degree) ≤ bound := by
      refine Finset.sup_le ?_
      intro i hi
      have hi' : i < N := Finset.mem_range.1 hi
      exact (hdeg_term i hi').trans (le_rfl)
    have := Polynomial.degree_sum_le (s := Finset.range N) (f := fun i => term i)
    have : rest.degree ≤ (Finset.range N).sup (fun i => (term i).degree) := by
      simpa [rest] using this
    exact le_trans this hsup
  have hdeg_lt : rest.degree < main.degree := by
    -- If `N = 0`, then `rest = 0` and the inequality is trivial.
    by_cases hN0 : N = 0
    · -- `rest = 0` and `main = term 0` is nonzero (indeed monic).
      have hmain0 : main ≠ 0 := by
        have : (term 0).Monic := by simpa [main, hN0] using hmain_monic
        simpa [main, hN0] using this.ne_zero
      have hdeg0 : (⊥ : WithBot ℕ) < main.degree :=
        (bot_lt_iff_ne_bot).2 (by
          -- `degree = ⊥` iff the polynomial is `0`.
          simpa [Polynomial.degree_eq_bot] using hmain0)
      simpa [hN0, rest, main] using hdeg0
    -- Otherwise compare explicit numeric bounds.
    -- Compute `main.degree`.
    have hnat_swapLC : (swapS (C p.leadingCoeff : S[X][Y])).natDegree =
        p.leadingCoeff.natDegree := by
      -- `swap (C g) = map C g`, and `natDegree` is preserved under the injective map `C`.
      have hswapC : swapS (C p.leadingCoeff : S[X][Y]) =
          Polynomial.map (C : S →+* S[X]) p.leadingCoeff := by
        simpa [swapS] using (bivariate_swap_C (A := S) (p := p.leadingCoeff))
      -- Now apply `natDegree_map_eq_of_injective` to the RHS.
      simpa [hswapC] using
        (Polynomial.natDegree_map_eq_of_injective
          (hf := (Polynomial.C_injective : Function.Injective (C : S →+* S[X])))
          (p := p.leadingCoeff))
    have hnat_baseN : (base ^ N).natDegree = N * K := by
      simpa [hbase_natDegree] using (hbase_monic.natDegree_pow N)
    have hnat_main : main.natDegree = p.leadingCoeff.natDegree + N * K := by
      have hswapLC' : (swapS (C p.leadingCoeff : S[X][Y])).Monic := hswapLC_monic
      have hbaseN' : (base ^ N).Monic := (hbase_monic.pow N)
      have := (hswapLC'.natDegree_mul hbaseN')
      simpa [main, term, hcoeffN, hnat_swapLC, hnat_baseN, add_comm, add_left_comm,
        add_assoc] using this
    have hmain_deg : main.degree = ((p.leadingCoeff.natDegree + N * K : ℕ) : WithBot ℕ) := by
      have hne : main ≠ 0 := hmain_monic.ne_zero
      simpa [hnat_main] using (Polynomial.degree_eq_natDegree hne)
    -- Compare the numeric bounds.
    have hNK : N * K = (N - 1) * K + K := by
      have hpos : 0 < N := Nat.pos_of_ne_zero hN0
      have h1 : 1 ≤ N := (Nat.succ_le_iff).2 hpos
      have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
      calc
        N * K = (N - 1 + 1) * K := by simp [hsub]
        _ = (N - 1) * K + 1 * K := by simp [Nat.add_mul]
        _ = (N - 1) * K + K := by simp
    have hM_lt_TK : M < p.leadingCoeff.natDegree + K := by
      have hMK : M < K := Nat.lt_succ_self M
      have hKle : K ≤ p.leadingCoeff.natDegree + K := Nat.le_add_left _ _
      exact lt_of_lt_of_le hMK hKle
    have hbound_lt : (M : WithBot ℕ) + (((N - 1) * K : ℕ) : WithBot ℕ) <
        ((p.leadingCoeff.natDegree + N * K : ℕ) : WithBot ℕ) := by
      -- Add `(N-1)*K` to `M < natDegree(leadingCoeff)+K`, and rewrite `N*K`.
      have h' : (M + (N - 1) * K) < (p.leadingCoeff.natDegree + K) + (N - 1) * K :=
        Nat.add_lt_add_right hM_lt_TK ((N - 1) * K)
      -- Cast to `WithBot ℕ` and rewrite.
      have h'' : ((M + (N - 1) * K : ℕ) : WithBot ℕ) <
          (((p.leadingCoeff.natDegree + K) + (N - 1) * K : ℕ) : WithBot ℕ) :=
        WithBot.coe_lt_coe.2 h'
      -- `((natDegree + K) + (N-1)*K) = natDegree + (N*K)` by `hNK`.
      simpa [hNK, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, bound] using h''
    -- Final comparison: `rest.degree ≤ bound < main.degree`.
    have hrest_le : rest.degree ≤ bound := hdeg_rest
    have hmain_eq : ((p.leadingCoeff.natDegree + N * K : ℕ) : WithBot ℕ) = main.degree := by
      simp [hmain_deg]
    exact lt_of_le_of_lt hrest_le (by simpa [hmain_eq] using hbound_lt)
  -- Finish: `swap (τ p) = rest + main` with `main` monic and `degree rest < degree main`.
  have : (swapS (τ p)).Monic := by
    -- Use `Monic.add_of_right`.
    have := Polynomial.Monic.add_of_right (p := rest) (q := main) hmain_monic hdeg_lt
    simpa [hswap', rest, main, add_comm, add_left_comm, add_assoc] using this
  -- Unfold abbreviations back to the statement.
  simpa [swapS, τ, t, K] using this

theorem suslin_monic_polynomial_theorem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] (hr : ringKrullDim R < ⊤) (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) R)) (hI : ringKrullDim R < I.height) :
    ∃ e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R,
      ∃ f : MvPolynomial (Fin (n + 1)) R,
        f ∈ I ∧ (MvPolynomial.finSuccEquiv R n (e f)).Monic := by
  classical
  have _hdim : ringKrullDim R ≠ ⊤ := ne_of_lt hr
  induction n with
  | zero =>
    -- `MvPolynomial (Fin 1) R` is (noncanonically) `R[X]`, use `finSuccEquiv` to work in `R[X]`.
    let eEmpty : MvPolynomial (Fin 0) R ≃ₐ[R] R :=
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0))
    let e0 : MvPolynomial (Fin (0 + 1)) R ≃ₐ[R] Polynomial R :=
      (MvPolynomial.finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv eEmpty)
    let J : Ideal (Polynomial R) := Ideal.map e0.toRingHom I
    have hheight : J.height = I.height := by
      -- Avoid `simp` rewriting `x = x` to `True`.
      change (Ideal.map e0.toRingEquiv I).height = I.height
      exact e0.toRingEquiv.height_map I
    have hJ : ringKrullDim R < J.height := by simpa [hheight] using hI
    have hJ_le : (J.height : WithBot ℕ∞) ≤ (J.leadingCoeff.height : WithBot ℕ∞) :=
      (WithBot.coe_le_coe).2 (Ideal.height_le_height_leadingCoeff (A := R) J)
    have hLC : ringKrullDim R < (J.leadingCoeff.height : WithBot ℕ∞) := lt_of_lt_of_le hJ hJ_le
    have hLC_top : (J.leadingCoeff : Ideal R) = ⊤ := by
      by_contra hne
      have hne' : (J.leadingCoeff : Ideal R) ≠ ⊤ := hne
      have hbound : (J.leadingCoeff.height : WithBot ℕ∞) ≤ ringKrullDim R := by
        simpa using Ideal.height_le_ringKrullDim_of_ne_top (I := (J.leadingCoeff : Ideal R)) hne'
      exact (not_lt_of_ge hbound) hLC
    have h1 : (1 : R) ∈ (J.leadingCoeff : Ideal R) := by simp [hLC_top]
    rcases (Ideal.mem_leadingCoeff (I := J) (1 : R)).1 h1 with ⟨g, hgJ, hgLC⟩
    have hgMonic : g.Monic := by simp [Polynomial.Monic, hgLC]
    rcases (Ideal.mem_map_iff_of_surjective e0.toRingHom e0.toRingEquiv.surjective).1 hgJ with
      ⟨f, hfI, rfl⟩
    refine ⟨(AlgEquiv.refl (R := R) (A₁ := MvPolynomial (Fin 1) R)), f, hfI, ?_⟩
    -- `e0 = mapAlgEquiv eEmpty ∘ finSuccEquiv`, and `eEmpty` is injective.
    -- So monicity of `e0 f` implies monicity of `finSuccEquiv f`.
    have hf_map : e0 f = Polynomial.map (eEmpty : MvPolynomial (Fin 0) R →+* R)
        ((MvPolynomial.finSuccEquiv R 0) f) := by
      simp [e0, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom]
    have hLC_map : (Polynomial.map (eEmpty : MvPolynomial (Fin 0) R →+* R)
          ((MvPolynomial.finSuccEquiv R 0) f)).leadingCoeff =
        (eEmpty : MvPolynomial (Fin 0) R →+* R)
          (((MvPolynomial.finSuccEquiv R 0) f).leadingCoeff) := by
      simpa using
        (Polynomial.leadingCoeff_map_of_injective
          (f := (eEmpty : MvPolynomial (Fin 0) R →+* R))
          (hf := eEmpty.toRingEquiv.injective) (p := (MvPolynomial.finSuccEquiv R 0) f))
    have hLC_image : (eEmpty : MvPolynomial (Fin 0) R →+* R)
        (((MvPolynomial.finSuccEquiv R 0) f).leadingCoeff) = 1 := by
      have : (Polynomial.map (eEmpty : MvPolynomial (Fin 0) R →+* R)
            ((MvPolynomial.finSuccEquiv R 0) f)).leadingCoeff = 1 := by
        simpa [hf_map] using (show (e0 f).leadingCoeff = 1 from hgMonic)
      simpa [hLC_map] using this
    have hLC : ((MvPolynomial.finSuccEquiv R 0) f).leadingCoeff = 1 := by
      -- Rewrite `1` as the image of `1` and use injectivity.
      have : (eEmpty : MvPolynomial (Fin 0) R →+* R)
          (((MvPolynomial.finSuccEquiv R 0) f).leadingCoeff) =
          (eEmpty : MvPolynomial (Fin 0) R →+* R) 1 := by
        simpa using hLC_image
      exact eEmpty.toRingEquiv.injective this
    simpa [Polynomial.Monic] using hLC
  | succ n ih =>
    -- Inductive step: `A = R[x₀,…,xₙ,x_{n+1}]`, view as `B[t]` with `B = R[x₀,…,xₙ]`.
    -- The proof follows Suslin's argument via the leading-coefficient ideal and a translation.
    classical
    let A := MvPolynomial (Fin (n + 2)) R
    let B := MvPolynomial (Fin (n + 1)) R
    let S := MvPolynomial (Fin n) R
    -- Split off the last variable: `A ≃ B[Y]`.
    let eLast : A ≃ₐ[R] Polynomial B := MvPolynomial.finSuccEquivLast R (n + 1)
    let J : Ideal (Polynomial B) := Ideal.map eLast.toRingHom I
    have hJheight : J.height = I.height := by
      change (Ideal.map eLast.toRingEquiv I).height = I.height
      exact eLast.toRingEquiv.height_map I
    have hJ : ringKrullDim R < J.height := by simpa [hJheight] using hI
    have hJ_le : (J.height : WithBot ℕ∞) ≤ (J.leadingCoeff.height : WithBot ℕ∞) :=
      (WithBot.coe_le_coe).2 (Ideal.height_le_height_leadingCoeff (A := B) J)
    have hLC : ringKrullDim R < (J.leadingCoeff.height : WithBot ℕ∞) := lt_of_lt_of_le hJ hJ_le
    -- Apply the inductive hypothesis to the leading-coefficient ideal in `B`.
    rcases ih (I := (J.leadingCoeff : Ideal B)) hLC with ⟨eB, g, hgLC, hgMonic⟩
    -- Choose a polynomial in `J` whose leading coefficient is `g`.
    rcases (Ideal.mem_leadingCoeff (I := J) g).1 hgLC with ⟨q, hqJ, hqLC⟩
    -- Pull it back to an element of `I`.
    rcases (Ideal.mem_map_iff_of_surjective eLast.toRingHom eLast.toRingEquiv.surjective).1 hqJ with
      ⟨f0, hf0I, hf0eq⟩
    have hq : eLast f0 = q := hf0eq
    -- Extend the automorphism `eB` of `B` to `A = B[Y]` by acting on coefficients.
    let eExt : A ≃ₐ[R] A := (eLast.trans (Polynomial.mapAlgEquiv eB)).trans eLast.symm
    -- Identify `B` as a polynomial ring in `x₀` over `S`,
    -- then view `A` as a bivariate polynomial ring.
    let eX : B ≃ₐ[R] Polynomial S := MvPolynomial.finSuccEquiv R n
    let H : A ≃ₐ[R] Polynomial (Polynomial S) := eLast.trans (Polynomial.mapAlgEquiv eX)
    -- Set `p` to be the image of `f0` in the bivariate polynomial ring
    -- after the coefficient change.
    let p : Polynomial (Polynomial S) := H (eExt f0)
    have hp_lc : p.leadingCoeff = eX (eB g) := by
      -- Work with `Polynomial.map` rather than `mapAlgEquiv`.
      have h₁ : eLast (eExt f0) = Polynomial.map (eB : B →+* B) (eLast f0) := by
        have hf : eExt f0 = eLast.symm (Polynomial.map (eB : B →+* B) (eLast f0)) := by
          simp [eExt, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom]
          rfl
        calc
          eLast (eExt f0) =
              eLast (eLast.symm (Polynomial.map (eB : B →+* B) (eLast f0))) := by
                simp [hf]
          _ = Polynomial.map (eB : B →+* B) (eLast f0) := by
                simp
      have hLC_q1 : (eLast (eExt f0)).leadingCoeff = eB g := by
        have hLC_mapB : (Polynomial.map (eB : B →+* B) (eLast f0)).leadingCoeff =
            eB (eLast f0).leadingCoeff := by
          simpa using
            (Polynomial.leadingCoeff_map_of_injective
              (f := (eB : B →+* B))
              (hf := eB.toRingEquiv.injective) (p := (eLast f0)))
        -- Rewrite `eLast f0 = q` and `q.leadingCoeff = g`.
        simpa [h₁, hq, hqLC] using hLC_mapB
      have hp_def : p = Polynomial.map (eX : B →+* Polynomial S) (eLast (eExt f0)) := by
        simp [p, H, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom]
      have hLC_mapX : (Polynomial.map (eX : B →+* Polynomial S) (eLast (eExt f0))).leadingCoeff =
          eX (eLast (eExt f0)).leadingCoeff := by
        simpa using
          (Polynomial.leadingCoeff_map_of_injective
            (f := (eX : B →+* Polynomial S))
            (hf := eX.toRingEquiv.injective) (p := (eLast (eExt f0))))
      simp [hp_def, hLC_mapX, hLC_q1]
    have hp_lc_monic : p.leadingCoeff.Monic := by
      -- This is exactly the monicity statement from the inductive hypothesis.
      simpa [hp_lc, eX] using hgMonic
    -- Apply the translation lemma in the bivariate polynomial ring.
    rcases exists_K_monic_swap_algEquivAevalXAddC (S := S) p hp_lc_monic with ⟨K, hmonic_swap⟩
    let τ : (Polynomial (Polynomial S)) ≃ₐ[Polynomial S] (Polynomial (Polynomial S)) :=
      Polynomial.algEquivAevalXAddC ((Polynomial.X : Polynomial S) ^ K)
    -- Conjugate the translation back to `A` and compose with the coefficient change.
    let eTau : A ≃ₐ[R] A := (H.trans (τ.restrictScalars R)).trans H.symm
    let eTotal : A ≃ₐ[R] A := eExt.trans eTau
    -- Compute the image of `f0` under the bivariate identification.
    have hHp : H (eTotal f0) = τ p := by
      simp [eTotal, eTau, p, H]
    have hEq : (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast R n)
          (MvPolynomial.finSuccEquiv R (n + 1) (eTotal f0))) =
        Polynomial.Bivariate.swap (H (eTotal f0)) := by
      -- `finSuccEquiv_map_finSuccEquivLast_apply` rewrites the LHS as a swapped bivariate form.
      simpa [H, eLast, eX] using
        (finSuccEquiv_map_finSuccEquivLast_apply (R := R) n (eTotal f0))
    have hLHS_monic : (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast R n)
          (MvPolynomial.finSuccEquiv R (n + 1) (eTotal f0))).Monic := by
      -- Rewrite to the swapped translated polynomial and use `hmonic_swap`.
      simpa [hEq, hHp, τ] using hmonic_swap
    -- Remove the coefficient map `finSuccEquivLast` to get monicity in `finSuccEquiv`.
    set q0 := MvPolynomial.finSuccEquiv R (n + 1) (eTotal f0) with hq0
    have hLC_q0 : q0.leadingCoeff = 1 := by
      -- Compare leading coefficients after applying the injective coefficient map.
      let eCoeff : B →+* Polynomial S := (MvPolynomial.finSuccEquivLast R n : B →+* Polynomial S)
      have hLC_map : (Polynomial.map eCoeff q0).leadingCoeff = eCoeff q0.leadingCoeff := by
        simpa [eCoeff] using
          (Polynomial.leadingCoeff_map_of_injective
            (f := eCoeff)
            (hf := (MvPolynomial.finSuccEquivLast R n).toRingEquiv.injective)
            (p := q0))
      have hmap_monic : (Polynomial.map eCoeff q0).Monic := by
        simpa [eCoeff, Polynomial.mapAlgEquiv, Polynomial.mapAlgHom] using hLHS_monic
      have hLC_image : eCoeff q0.leadingCoeff = 1 := by
        -- `hmap_monic` gives `leadingCoeff = 1`.
        have : (Polynomial.map eCoeff q0).leadingCoeff = 1 := hmap_monic
        simpa [hLC_map] using this
      -- Use injectivity of `finSuccEquivLast`.
      have :
          eCoeff q0.leadingCoeff = eCoeff (1 : B) := by
        simpa using hLC_image
      exact (MvPolynomial.finSuccEquivLast R n).toRingEquiv.injective this
    have hq0Monic : q0.Monic := by simpa [Polynomial.Monic] using hLC_q0
    refine ⟨eTotal, f0, hf0I, ?_⟩
    simpa [hq0] using hq0Monic
