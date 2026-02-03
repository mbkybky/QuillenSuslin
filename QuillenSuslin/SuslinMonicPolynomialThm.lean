import Mathlib

variable {R : Type*} [CommRing R] [IsDomain R]

namespace MvPolynomial

open scoped BigOperators

variable (R : Type*) [CommSemiring R]

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
multivariable polynomials in `Fin n`, singling out the **last** variable. -/
noncomputable def finSuccEquivLast (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquivLast (n := n))).trans (optionEquivLeft R (Fin n))

@[simp]
lemma finSuccEquivLast_X_castSucc (n : ℕ) (i : Fin n) :
    finSuccEquivLast (R := R) n (X (Fin.castSucc i)) = Polynomial.C (X i) := by
  simp [finSuccEquivLast, _root_.finSuccEquivLast_castSucc]

@[simp]
lemma finSuccEquivLast_X_last (n : ℕ) :
    finSuccEquivLast (R := R) n (X (Fin.last n)) = Polynomial.X := by
  simp [finSuccEquivLast, _root_.finSuccEquivLast_last]

@[simp]
lemma finSuccEquivLast_symm_X (n : ℕ) :
    (finSuccEquivLast (R := R) n).symm Polynomial.X = X (Fin.last n) := by
  simpa [finSuccEquivLast_X_last (R := R) n] using
    (finSuccEquivLast (R := R) n).symm_apply_apply (X (Fin.last n))

@[simp]
lemma finSuccEquivLast_symm_C_X (n : ℕ) (i : Fin n) :
    (finSuccEquivLast (R := R) n).symm (Polynomial.C (X i)) = X (Fin.castSucc i) := by
  simpa [finSuccEquivLast_X_castSucc (R := R) n i] using
    (finSuccEquivLast (R := R) n).symm_apply_apply (X (Fin.castSucc i))

end MvPolynomial

namespace Ideal

open scoped BigOperators
open Polynomial

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
      (Ideal.mem_map_C_iff (I := p)).2 (by intro n; cases n <;> simp [hx]), by simp⟩

variable [IsDomain A]

@[simp] lemma leadingCoeff_top : ((⊤ : Ideal A[X]).leadingCoeff : Ideal A) = ⊤ := by
  ext x
  constructor
  · intro _; trivial
  · intro _; exact (Ideal.mem_leadingCoeff (I := (⊤ : Ideal A[X])) x).2 ⟨Polynomial.C x, trivial, by simp⟩

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
  simpa [hp, hq] using (Polynomial.leadingCoeff_mul p q)

 lemma leadingCoeff_pow_le (I : Ideal A[X]) : ∀ n : ℕ, I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff
   | 0 => by
       simpa [pow_zero, Ideal.one_eq_top, leadingCoeff_top (A := A)] using (le_rfl : (⊤ : Ideal A) ≤ ⊤)
   | n + 1 => by
       -- `I.leadingCoeff^(n+1) = I.leadingCoeff^n * I.leadingCoeff`.
       have h₁ : I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff := leadingCoeff_pow_le I n
       -- Multiply the inequality by `I.leadingCoeff` and use the multiplicativity lemma.
       have hmul :
           (I.leadingCoeff ^ n) * I.leadingCoeff ≤ ((I ^ n) * I).leadingCoeff := by
         refine le_trans (Ideal.mul_mono_left h₁) ?_
         simpa [mul_assoc] using leadingCoeff_mul_le (I := I ^ n) (J := I)
       simpa [pow_succ] using hmul

open scoped nonZeroDivisors

variable [IsNoetherianRing A]

private lemma ideal_pow_mono {I J : Ideal A} (hIJ : I ≤ J) : ∀ n : ℕ, I ^ n ≤ J ^ n
  | 0 => by simp
  | n + 1 => by
      simpa [pow_succ] using Ideal.mul_mono (ideal_pow_mono hIJ n) hIJ

private lemma leadingCoeff_finset_prod_le (s : Finset (Ideal A[X])) :
    (s.prod fun P => P.leadingCoeff) ≤ (s.prod id).leadingCoeff := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro P s hP hs
    have h₁ :
        P.leadingCoeff * (s.prod fun Q => Q.leadingCoeff) ≤
          P.leadingCoeff * (s.prod id).leadingCoeff :=
      Ideal.mul_mono_right hs
    have h₂ :
        P.leadingCoeff * (s.prod id).leadingCoeff ≤ (P * (s.prod id)).leadingCoeff := by
      simpa [mul_assoc] using leadingCoeff_mul_le (I := P) (J := (s.prod id))
    simpa [Finset.prod_insert, hP, Finset.prod_insert, hP, mul_assoc, mul_left_comm, mul_comm] using
      le_trans h₁ h₂

private lemma height_le_one_of_isPrime_comap_C_eq_bot (Q : Ideal A[X]) [Q.IsPrime]
    (hQ : Ideal.comap (C : A →+* A[X]) Q = ⊥) :
    Q.height ≤ 1 := by
  classical
  let K := FractionRing A
  -- Work in the localization `K[X]`.
  -- Make the localization instance available for polynomial rings.
  -- (`Polynomial.isLocalization` is not an instance globally.)
  let M : Submonoid A[X] := Submonoid.map (C : A →+* A[X]) (A⁰)
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
  let _ : IsLocalization M K[X] := Polynomial.isLocalization (S := (A⁰)) (A := K)
  have hheight :
      (Ideal.map (algebraMap A[X] K[X]) Q).height = Q.height := by
    -- `K[X]` is a localization of `A[X]` at `M`.
    -- We rely on `Polynomial.isLocalization` to provide the instance.
    -- See `Mathlib/RingTheory/KrullDimension/Polynomial.lean` for the same pattern.
    classical
    simpa [M] using
      (IsLocalization.height_map_of_disjoint (R := A[X]) (S := K[X]) (M := M) (p := Q) hdisj)
  -- Now bound the height in `K[X]` by `dim K[X] = 1`.
  have hne_top : Ideal.map (algebraMap A[X] K[X]) Q ≠ (⊤ : Ideal K[X]) := by
    -- It is a proper ideal since it is prime.
    have hprime : (Ideal.map (algebraMap A[X] K[X]) Q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M K[X] Q inferInstance hdisj
    exact Ideal.IsPrime.ne_top hprime
  have hdim : ringKrullDim K[X] = (1 : WithBot ℕ∞) := by
    -- `K` is a field, so `dim K[X] = 1`.
    have : ringKrullDim K = 0 := by simpa using ringKrullDim_eq_zero_of_field K
    -- Use the noetherian polynomial dimension formula.
    simpa [this] using (Polynomial.ringKrullDim_of_isNoetherianRing (R := K))
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

private lemma height_le_leadingCoeff_of_isPrime (P : Ideal A[X]) [P.IsPrime] :
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
  have hheight :
      P.height =
        p.height +
          (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P).height := by
    simpa [Ideal.under_def] using
      (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := A[X]) p P)
  -- Split into the extended-prime case and the strict case.
  by_cases hPeq : P = Ideal.map (C : A →+* A[X]) p
  · -- Then the quotient image is `⊥`, so `P.height = p.height`.
    have hQ : Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A[X]) p)) P = ⊥ := by
      -- Avoid `subst` since `p` depends on `P`.
      simpa [hPeq] using (Ideal.map_quotient_self (Ideal.map (algebraMap A A[X]) p))
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
      have hQprime :
          (Ideal.map q P).IsPrime :=
        Ideal.map_isPrime_of_surjective (f := q) Ideal.Quotient.mk_surjective (I := P) hker
      simpa [Q] using hQprime
    have hQle : Q.height ≤ 1 := by
      -- Transport to `(A ⧸ p)[X]` and use the localization-to-fraction-field bound.
      let e : (A ⧸ p)[X] ≃+* (A[X] ⧸ I0) :=
        p.polynomialQuotientEquivQuotientPolynomial
      -- Pull back along `e` and apply the bound for primes lying over `⊥`.
      have hcomap :
          Ideal.comap (C : (A ⧸ p) →+* (A ⧸ p)[X]) (Ideal.comap e.toRingHom Q) = ⊥ := by
        -- The contracted ideal is `⊥` since `P` lies over `p`.
        ext a
        -- Reduce to showing `e (C a) ∈ Q ↔ a = 0`.
        have hEq : e (C a) ∈ Q ↔ a = 0 := by
          -- Unfold the quotient element `a`.
          refine Quotient.inductionOn a ?_
          intro a0
          -- Rewrite `e (C (mk a0))` as the image of `C a0` in `A[X] ⧸ I0`.
          have hCe :
              e (C (Ideal.Quotient.mk p a0)) =
                q (Polynomial.C a0) := by
            -- `C (mk a0) = map (mk p) (C a0)`.
            simpa [I0, q] using (p.polynomialQuotientEquivQuotientPolynomial_map_mk (f := Polynomial.C a0))
          -- Membership in the image ideal is equivalent to membership in `P` since `ker q ≤ P`.
          have hmem :
              q (Polynomial.C a0) ∈ Q ↔ Polynomial.C a0 ∈ P := by
            constructor
            · intro hx
              rcases
                  (Ideal.mem_map_iff_of_surjective (f := q) Ideal.Quotient.mk_surjective).1 hx with
                ⟨y, hyP, hyEq⟩
              have hySub : y - Polynomial.C a0 ∈ I0 := (Ideal.Quotient.eq (I := I0)).1 hyEq
              have hySubP : y - Polynomial.C a0 ∈ P := hI0_le hySub
              have : y - (y - Polynomial.C a0) ∈ P := Ideal.sub_mem P hyP hySubP
              simpa [sub_sub] using this
            · intro hx
              exact Ideal.mem_map_of_mem q hx
          -- Finish by chasing through the definitions of `p` and the quotient.
          -- `C a0 ∈ P ↔ a0 ∈ p ↔ mk a0 = 0`.
          have hp0 : Polynomial.C a0 ∈ P ↔ a0 ∈ p := by
            simpa [p, Ideal.mem_comap]
          have hq0 : (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) ↔ a0 ∈ p := by
            simpa using (Ideal.Quotient.eq_zero_iff_mem (I := p) (a := a0))
          -- Now conclude.
          calc
            e (C (Ideal.Quotient.mk p a0)) ∈ Q ↔ q (Polynomial.C a0) ∈ Q := by simpa [hCe]
            _ ↔ Polynomial.C a0 ∈ P := hmem
            _ ↔ a0 ∈ p := hp0
            _ ↔ (Ideal.Quotient.mk p a0 = (0 : A ⧸ p)) := by
                  simpa [eq_comm] using hq0.symm
        -- Now `simp` finishes the ideal equality.
        simpa [Ideal.mem_comap, hEq]
      have hbound' :
          (Ideal.comap e.toRingHom Q).height ≤ 1 :=
        height_le_one_of_isPrime_comap_C_eq_bot (A := A ⧸ p) (Q := Ideal.comap e.toRingHom Q) hcomap
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
      -- `p ≤ P.leadingCoeff` is already `hp_le`; it suffices to show strictness.
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
        simpa [hf0z]
      -- Minimality of `n0`.
      have hmin : ∀ m : ℕ, m < n0 → ¬ Pred m := by
        have hEq := (Nat.find_eq_iff (m := n0) (h := hNat)).1 rfl
        exact hEq.2
      -- If the leading coefficient lay in `p`, we could cancel the leading term and contradict minimality.
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
            simpa [t] using (Polynomial.leadingCoeff_C_mul_X_pow (a := f0.leadingCoeff) (n := d)).symm
          have : g.degree < f0.degree := by
            -- apply `degree_sub_lt` to `f0` and `t`
            have := Polynomial.degree_sub_lt (p := f0) (q := t) (by simpa [hdeg_f0, hdeg_t])
              hf0_ne0 hLCeq
            simpa [g] using this
          exact this
        have hnat_lt : g.natDegree < n0 := by
          by_cases hg0 : g = 0
          · -- Then `g.natDegree = 0`, and we just need `0 < n0`.
            have hn0' : n0 ≠ 0 := by
              intro hn0z
              have hd0 : d = 0 := by simpa [d, hf0deg, hn0z]
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
        simpa [Pset] using (Set.Finite.coe_toFinset hfin)
      simpa [Finset.inf_id_eq_sInf, this] using (rfl : (Pset.inf id : Ideal A[X]) = Pset.inf id)
    simpa [J, hinf, Ideal.sInf_minimalPrimes] using hprod
  -- Some power of the product is contained in `I`.
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing (R := A[X]) J
  rcases Ideal.exists_pow_le_of_le_radical_of_fg hJ_le_rad hJfg with ⟨N, hJN⟩
  -- Now show `I.height ≤ q.primeHeight` for every `q` minimal over `I.leadingCoeff`.
  refine le_iInf fun q => le_iInf fun hq => ?_
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  -- Get some minimal prime `P ∈ I.minimalPrimes` whose leading-coefficient ideal is contained in `q`.
  have hLC :
      (Pset.prod fun P => P.leadingCoeff) ^ N ≤ I.leadingCoeff := by
    have h₁ : (Pset.prod fun P => P.leadingCoeff) ≤ J.leadingCoeff := by
      simpa [J] using leadingCoeff_finset_prod_le (A := A) Pset
    have h₂ : (Pset.prod fun P => P.leadingCoeff) ^ N ≤ J.leadingCoeff ^ N :=
      ideal_pow_mono (A := A) h₁ N
    have h₃ : J.leadingCoeff ^ N ≤ (J ^ N).leadingCoeff := leadingCoeff_pow_le (A := A) J N
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

/- Auxiliary lemmas for relating `finSuccEquiv`/`finSuccEquivLast` to bivariate polynomials. -/
namespace SuslinMonicAux

open scoped Polynomial.Bivariate
open Polynomial
open Polynomial.Bivariate

section

variable {A : Type*} [CommSemiring A]

@[simp]
lemma bivariate_swap_C (p : A[X]) :
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
    simpa [C_mul_X_pow_eq_monomial, Polynomial.map_monomial] using
      (Polynomial.Bivariate.swap_monomial_monomial (R := A) (n := 0) (m := n) (r := a))

end

section

variable {R : Type*} [CommRing R]

open MvPolynomial

-- The two-step identifications of `R[x₀,…,xₙ,x_{n+1}]` with a bivariate polynomial ring agree, up to
-- swapping the two polynomial variables.
lemma finSuccEquiv_map_finSuccEquivLast_apply (n : ℕ) (f : MvPolynomial (Fin (n + 2)) R) :
    (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast (R := R) n)
        (MvPolynomial.finSuccEquiv R (n + 1) f)) =
      Polynomial.Bivariate.swap (R := MvPolynomial (Fin n) R)
        (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R n)
          (MvPolynomial.finSuccEquivLast (R := R) (n + 1) f)) := by
  -- Prove equality of `R`-algebra homomorphisms by checking on variables.
  classical
  let F : MvPolynomial (Fin (n + 2)) R →ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin n) R)) :=
    ((MvPolynomial.finSuccEquiv R (n + 1)).trans
        (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquivLast (R := R) n))).toAlgHom
  let swapR : Polynomial (Polynomial (MvPolynomial (Fin n) R)) ≃ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin n) R)) :=
    (Polynomial.Bivariate.swap (R := MvPolynomial (Fin n) R)).restrictScalars R
  let G : MvPolynomial (Fin (n + 2)) R →ₐ[R] Polynomial (Polynomial (MvPolynomial (Fin n) R)) :=
    (((MvPolynomial.finSuccEquivLast (R := R) (n + 1)).trans
            (Polynomial.mapAlgEquiv (MvPolynomial.finSuccEquiv R n))).trans
          swapR).toAlgHom
  have hFG : F = G := by
    refine MvPolynomial.algHom_ext ?_
    intro i
    -- Split `i : Fin (n+2)` as either `castSucc j` or the last index.
    cases i using Fin.lastCases with
    | last =>
      -- The last variable becomes the *inner* variable.
      have hlast :
          MvPolynomial.finSuccEquiv R (n + 1) (MvPolynomial.X (Fin.last (n + 1))) =
            Polynomial.C (MvPolynomial.X (Fin.last n)) := by
        -- `Fin.last (n+1) = (Fin.last n).succ`.
        simpa [Fin.succ_last] using
          (MvPolynomial.finSuccEquiv_X_succ (R := R) (n := n + 1) (j := Fin.last n))
      have hF :
          F (MvPolynomial.X (Fin.last (n + 1))) =
            (Polynomial.C (Polynomial.X (R := MvPolynomial (Fin n) R)) : (MvPolynomial (Fin n) R)[X][Y]) := by
        -- Map the coefficient `X (Fin.last n)` to the inner variable via `finSuccEquivLast`.
        simp [F, hlast, MvPolynomial.finSuccEquivLast_X_last]
      have hG' :
          G (MvPolynomial.X (Fin.last (n + 1))) =
            swapR (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
        simp [G, MvPolynomial.finSuccEquivLast_X_last]
      have hG :
          G (MvPolynomial.X (Fin.last (n + 1))) =
            (Polynomial.C (Polynomial.X (R := MvPolynomial (Fin n) R)) : (MvPolynomial (Fin n) R)[X][Y]) := by
        -- `swap` sends the outer variable `Y` to the inner variable `C X`.
        simpa [hG', swapR] using (Polynomial.Bivariate.swap_Y (R := MvPolynomial (Fin n) R))
      simpa [hF, hG]
    | cast i =>
      -- Now split `i : Fin (n+1)` into `0` or `succ j`.
      cases i using Fin.cases with
      | zero =>
        -- The distinguished variable for `finSuccEquiv` is `0`.
        have hF : F (MvPolynomial.X (0 : Fin (n + 2))) = (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
          simp [F, MvPolynomial.finSuccEquiv_X_zero]
        have hG' :
            G (MvPolynomial.X (0 : Fin (n + 2))) =
              swapR (C (Polynomial.X (R := MvPolynomial (Fin n) R)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- `X 0` becomes the inner variable, then `swap` sends `C X` to `Y`.
          have h0 :
              MvPolynomial.finSuccEquivLast (R := R) (n + 1) (MvPolynomial.X (0 : Fin (n + 2))) =
                Polynomial.C (MvPolynomial.X (0 : Fin (n + 1))) := by
            simpa using (MvPolynomial.finSuccEquivLast_X_castSucc (R := R) (n := n + 1) (i := (0 : Fin (n + 1))))
          -- Unfold the definitions and use the behavior on `X 0`.
          simp [G, h0, MvPolynomial.finSuccEquiv_X_zero]
        have hG :
            G (MvPolynomial.X (0 : Fin (n + 2))) = (Y : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- `swap (C X) = Y`.
          have : swapR (C (Polynomial.X (R := MvPolynomial (Fin n) R)) : (MvPolynomial (Fin n) R)[X][Y]) = Y := by
            simpa [swapR] using (Polynomial.Bivariate.swap_X (R := MvPolynomial (Fin n) R))
          simpa [hG', this]
        simpa [hF, hG]
      | succ j =>
        -- Variables other than `0` are sent to constants in the bivariate polynomial ring.
        -- `castSucc (succ j) = succ (castSucc j)` aligns the two normal forms.
        have hF :
            F (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
              (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- Under `finSuccEquiv`, this variable is a constant coefficient `X (castSucc j)`.
          -- Under `finSuccEquivLast`, `X (castSucc j)` stays a constant coefficient.
          simp [F, MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquivLast_X_castSucc]
        have hG' :
            G (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
              swapR (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          have hcast :
              MvPolynomial.finSuccEquivLast (R := R) (n + 1) (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
                Polynomial.C (MvPolynomial.X (Fin.succ j)) := by
            -- `Fin.castSucc (Fin.succ j)` is a non-last variable.
            -- Rewrite `j.castSucc.succ` as `Fin.castSucc (Fin.succ j)`.
            simpa [Fin.castSucc_succ] using
              (MvPolynomial.finSuccEquivLast_X_castSucc (R := R) (n := n + 1) (i := Fin.succ j))
          -- Now use `finSuccEquiv` on the coefficient `X (succ j)`.
          simp [G, hcast, MvPolynomial.finSuccEquiv_X_succ]
        have hswap :
            swapR (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) =
              (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          -- This element is constant in both variables, so `swap` fixes it.
          -- Use `swap (C p) = map C p` and simplify.
          -- Here `p = C (X j)` is a constant polynomial, so mapping coefficients does nothing.
          simp only [swapR, AlgEquiv.restrictScalars_apply, SuslinMonicAux.bivariate_swap_C, Polynomial.map_C]
        have hG :
            G (MvPolynomial.X (j.castSucc.succ : Fin (n + 2))) =
              (Polynomial.C (Polynomial.C (MvPolynomial.X j)) : (MvPolynomial (Fin n) R)[X][Y]) := by
          simpa [hG', hswap]
        simpa [hF, hG]
  -- Finish by rewriting both sides in terms of `F` and `G`.
  simpa [F, G] using congrArg (fun h => h f) hFG

end

end SuslinMonicAux

/-- **Suslin's monic polynomial theorem**

Let `A = R[x₀,…,xₙ]`. If an ideal `I ⊆ A` has height `> dim R`, then after a show of variables
one can find an element of `I` that is monic in `x₀`.

This is a convenient `Fin (n+1)`-indexed formulation; it is equivalent to the usual “there exist
new variables `s₀,…,sₙ` with `A = R[s₀,…,sₙ]` such that `I` contains a polynomial monic in `s₀`.” -/
theorem suslin_monic_polynomial_theorem [IsNoetherianRing R] (hr : ringKrullDim R < ⊤) (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) R)) (hI : ringKrullDim R < I.height) :
    ∃ e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R,
      ∃ f : MvPolynomial (Fin (n + 1)) R,
        f ∈ I ∧ (MvPolynomial.finSuccEquiv R n (e f)).Monic := by
  sorry

/-
Let $R$ be a commutative ring. For any ideal $\mathfrak{A}$ in $R[t]$, let $\ell(\mathfrak{A})$ be the set in $R$ consisting of zero and all the leading coefficients of polynomials in $\mathfrak{A}$. This is clearly an ideal in $R$ (containing $\mathfrak{A} \cap R$). We shall need the following lemma which relates the height of $\ell(\mathfrak{A})$ to the height of $\mathfrak{A}$. (By definition, $\mathrm{ht} I = \min \{ \mathrm{ht} \mathfrak{p} \}$ where $\mathfrak{p}$ ranges over all prime ideals $\supseteq I$. The height of the unit ideal is taken to be $\infty$.)

\begin{lemma}
	Let $R$ be a commutative noetherian ring, and $\mathfrak{A}$ be an ideal in $R[t]$. Then $\mathrm{ht} \ell(\mathfrak{A}) \geqslant \mathrm{ht} \mathfrak{A}$.
\end{lemma}

\begin{proof}
	First assume $\mathfrak{A}$ is a prime ideal, $\mathfrak{P}$; let $\mathfrak{p} = \mathfrak{P} \cap R$. If $\mathfrak{P} = \mathfrak{p}[t]$, clearly $\ell(\mathfrak{P}) = \mathfrak{p}$, so $\mathrm{ht} \ell(\mathfrak{P}) = \mathrm{ht} \mathfrak{p} = \mathrm{ht} \mathfrak{p}[t] = \mathrm{ht} \mathfrak{P}$ by (II.7.7). If $\mathfrak{P} \supsetneq \mathfrak{p}[t]$, clearly $\ell(\mathfrak{P}) \supseteq \mathfrak{p}$, so, again by (II.7.7), $\mathrm{ht} \ell(\mathfrak{P}) > \mathrm{ht} \mathfrak{p} = \mathrm{ht} \mathfrak{P} - 1$, i.e., $\mathrm{ht} \ell(\mathfrak{P}) \geqslant \mathrm{ht} \mathfrak{P}$. For the general case, let $\mathfrak{P}_1, \dots, \mathfrak{P}_r$ be the prime ideals of $R[t]$ that are minimal over $\mathfrak{A}$. (We know that $r < \infty$ by (II.7.6), since $R[t]$ is noetherian by Hilbert's Basis Theorem. Also, we may assume $r \geqslant 1$, for if $\mathfrak{A}$ is the unit ideal, we have $\mathrm{ht}\, \ell(\mathfrak{A}) = \infty = \mathrm{ht}\, \mathfrak{A}$.) From
	\[
	\prod \mathfrak{P}_i \subseteq \bigcap \mathfrak{P}_i = \mathrm{rad} \mathfrak{A},
	\]
	we see that $(\prod \mathfrak{P}_i)^N \subseteq \mathfrak{A}$ for some $N$. Applying ``$\ell$'' to this, and using the fact that $\ell(I) \cdot \ell(J) \subseteq \ell(I \cdot J)$, we get $\prod \ell(\mathfrak{P}_i)^N \subseteq \ell(\mathfrak{A})$. Let $\mathfrak{p}$ be a prime over $\ell(\mathfrak{A})$ with $\mathrm{ht}\, \ell(\mathfrak{A}) = \mathrm{ht}\, \mathfrak{p}$. Then $\ell(\mathfrak{P}_i) \subseteq \mathfrak{p}$ for some $i$, from which we get
	\[
	\mathrm{ht}\, \mathfrak{A} \leqslant \mathrm{ht}\, \mathfrak{P}_i \leqslant \mathrm{ht}\, \ell(\mathfrak{P}_i) \leqslant \mathrm{ht}\, \mathfrak{p} = \mathrm{ht}\, \ell(\mathfrak{A}). \qedhere
	\]
\end{proof}

\begin{theorem}\label{Suslin’s Monic Polynomial Theorem}
	Let $R$ be a commutative noetherian ring of Krull dimension $d < \infty$. Let $\mathfrak{A}$ be an ideal in $A = R[t_1, \dots, t_m]$, with $\operatorname{ht} \mathfrak{A} > d$. Then there exist new ``variables'' $s_1, \dots, s_m \in A$ with $A = R[s_1, \dots, s_m]$ such that $\mathfrak{A}$ contains a polynomial that is monic as a polynomial in $s_1$.
\end{theorem}

\begin{proof}
	We induct on $m$. If $m=0$, $\operatorname{ht} \mathfrak{A} > d$ means $\mathfrak{A} = R$ so the result is trivial. For $m \geqslant 1$, write $B = R[t_1, \dots, t_{m-1}]$; we view $\mathfrak{A}$ as an ideal in $B[t_m] = A$, and get $\ell(\mathfrak{A}) \subseteq B$. By (3.2), $\operatorname{ht} \ell(\mathfrak{A}) \geqslant \operatorname{ht} \mathfrak{A} > d$, so, by the inductive hypothesis, we can write $B = R[s_1, \dots, s_{m-1}]$ such that there exists $g \in \ell(\mathfrak{A})$ that is monic in $s_1$, say,
	\[
	g = s_1^T + g_{T-1}s_1^{T-1} + \dots + g_0 \quad (g_i \in R[s_2, \dots, s_{m-1}]).
	\]
	By definition of $\ell(\mathfrak{A})$, $\mathfrak{A}$ contains a polynomial
	\[
	f = g \cdot t_m^N + b_{N-1}t_m^{N-1} + \dots + b_0, \quad b_i \in B.
	\]
	Let $M$ be the highest power of $s_1$ occurring in $b_0, \dots, b_{N-1}$. Set $t_m = s_m + s_1^K$, so $A = B[t_m] = R[s_1, \dots, s_m]$. In $b_{N-1}t_m^{N-1} + \dots + b_0$, $s_1$ occurs with exponent $\leqslant M + K(N-1)$. On the other hand,
	\[
	g \cdot t_m^N = (s_1^T + g_{T-1}s_1^{T-1} + \dots + g_0)(s_m + s_1^K)^N
	\]
	is monic of degree $T + KN$ in $s_1$. For $K$ sufficiently large, we have $T + K \cdot N > M + K(N-1)$, so $f$ is monic as a polynomial in $s_1$.
\end{proof}
-/
