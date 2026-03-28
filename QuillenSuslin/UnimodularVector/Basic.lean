/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.Bivariate

open Module Polynomial Finset BigOperators

variable {R : Type*} [CommRing R] {s : Type*} [Fintype s] [DecidableEq s]

/-- A vector `v : s → R` is unimodular if its components generate the unit ideal. -/
def IsUnimodular (v : s → R) : Prop := Ideal.span (Set.range v) = ⊤

/-- Two vectors `v w : s → R` are equivalent if they differ by left multiplication by an element
of `GL s R`. -/
def UnimodularVectorEquiv (v w : s → R) : Prop :=
  ∃ M : Matrix.GeneralLinearGroup s R, M.1.mulVec v = w

/-- `UnimodularVectorEquiv` is an equivalence relation. -/
theorem unimodularVectorEquiv_equivalence :
    Equivalence (UnimodularVectorEquiv (R := R) (s := s)) := by
  refine ⟨fun v ↦ ⟨1, by simp⟩, ?_, ?_⟩
  · intro v w h
    rcases h with ⟨M, hM⟩
    refine ⟨M⁻¹, ?_⟩
    calc _ = (M⁻¹).1.mulVec (M.1.mulVec v) := by simp [hM]
      _ = v := by simp
  · intro a b c ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨N * M, ?_⟩
    calc _ = N.1.mulVec (M.1.mulVec a) := by simp
      _ = c := by simp [hM, hN]

section isUnimodular_map

variable {A B : Type*} [CommRing A] [CommRing B] {s : Type*}

/-- Unimodularity is preserved under a ring homomorphism. -/
theorem isUnimodular_map_ringHom (f : A →+* B) (v : s → A) (hv : IsUnimodular v) :
    IsUnimodular fun i => f (v i) := by
  unfold IsUnimodular at hv ⊢
  have hmap : Ideal.map f (Ideal.span (Set.range v)) = ⊤ := by
    simpa [hv] using (Ideal.map_top f : Ideal.map f (⊤ : Ideal A) = (⊤ : Ideal B))
  have hrange : (f : A → B) '' Set.range v = Set.range fun i => f (v i) := by
    ext b
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  have hspan : Ideal.span ((f : A → B) '' Set.range v) = ⊤ := by simpa [Ideal.map_span] using hmap
  simpa [hrange] using hspan

/-- Unimodularity is preserved under an algebra equivalence. -/
theorem isUnimodular_map_ringEquiv (e : A ≃+* B) (v : s → A) (hv : IsUnimodular v) :
    IsUnimodular fun i => e (v i) := by
  unfold IsUnimodular at hv ⊢
  have hmap : Ideal.map (e : A →+* B) (Ideal.span (Set.range v)) = ⊤ := by
    simpa using (congrArg (Ideal.map e) hv).trans (by simpa using (Ideal.map_top (e : A →+* B)))
  have hspan : Ideal.span ((e : A →+* B) '' Set.range v) = ⊤ := by
    simpa [Ideal.map_span] using hmap
  have hrange : (e : A → B) '' Set.range v = Set.range fun i => e (v i) := by
    ext b
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  simpa [hrange] using hspan

variable [Fintype s] [DecidableEq s]

theorem generalLinearGroup_map_mulVec_eq (f : A →+* B) (M : GL s A) {v w : s → A}
    (hM : M.1.mulVec v = w) : (M.map f).1.mulVec (fun i => f (v i)) = fun i => f (w i) :=
  funext fun i ↦ (RingHom.map_mulVec f M.1 v i).symm.trans (congrArg f (congrFun hM i))

/-- Push a unimodular-vector equivalence along a ring homomorphism. -/
theorem unimodularVectorEquiv_map (f : A →+* B) {v w : s → A} (hvw : UnimodularVectorEquiv v w) :
    UnimodularVectorEquiv (fun i => f (v i)) (fun i => f (w i)) := by
  rcases hvw with ⟨M, hM⟩
  refine ⟨Matrix.GeneralLinearGroup.map f M, ?_⟩
  ext i
  have hi : f ((M.1.mulVec v) i) = f (w i) := congrArg f (congrArg (fun u : s → A => u i) hM)
  have hmap : (M.1.map f).mulVec (fun j => f (v j)) i = f ((M.1.mulVec v) i) := by
    simpa [Function.comp] using (RingHom.map_mulVec f M.1 v i).symm
  simpa [Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply] using hmap.trans hi

/-- Unimodular-vector equivalence is preserved under an algebra equivalence. -/
theorem unimodularVectorEquiv_map_ringEquiv (e : A ≃+* B) (v w : s → A)
    (hvw : UnimodularVectorEquiv v w) :
    UnimodularVectorEquiv (fun i => e (v i)) (fun i => e (w i)) := by
  simpa using unimodularVectorEquiv_map e.toRingHom hvw

end isUnimodular_map

section degree

/-- If `0 < p.natDegree`, then `p ≠ 1`. -/
lemma ne_one_of_natDegree_pos {p : R[X]} (hp : 0 < p.natDegree) : p ≠ 1 := by
  rintro rfl
  simp at hp

/-- If we have two polynomials $a(x), b(x) \in R[x]$, with $\deg a = d$ and $a$ monic,
  and $b$ of degree $\leq d-1$ containing at least one coefficient which is a unit, there is a
  polynomial $a(x) e(x) + b(x) f(x) \in (a(x), b(x))$ of degree $\leq d-1$ whose leading coefficient
  is one. -/
theorem degree_lowering (a b : R[X]) (ha : a.Monic) (hb : b.natDegree < a.natDegree)
    (h : ∃ i : ℕ, IsUnit (b.coeff i)) :
    ∃ e f : R[X], (a * e + b * f).Monic ∧ (a * e + b * f).natDegree = a.natDegree - 1 := by
  have : Nontrivial R := by
    by_contra! htriv
    have ha0 : a = 0 := Subsingleton.elim _ _
    have hb0 : b = 0 := Subsingleton.elim _ _
    have : ¬ b.natDegree < a.natDegree := by simp [ha0, hb0]
    exact this hb
  let d := a.natDegree
  have hd_pos : 0 < d := Nat.zero_lt_of_lt (by simpa [d] using hb)
  let Φ : R[X] →ₗ[R] R :=
    (Polynomial.lcoeff R (d - 1)).comp <| (Polynomial.modByMonicHom a).comp <| LinearMap.mulLeft R b
  by_contra hno
  have hrange_ne_top : (Φ.range : Ideal R) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ (Φ.range : Ideal R) := by simp [htop]
    rcases h1 with ⟨f, hf1⟩
    let e : R[X] := -(b * f /ₘ a)
    have hrepr : a * e + b * f = (b * f) %ₘ a := by
      dsimp [e]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using (Polynomial.modByMonic_eq_sub_mul_div (b * f) a).symm
    have hne1 : a ≠ 1 := ne_one_of_natDegree_pos (by simpa [d] using hd_pos)
    have hdeg_lt : ((b * f) %ₘ a).natDegree < d := by
      simpa [d] using Polynomial.natDegree_modByMonic_lt (b * f) ha hne1
    have hdeg_le : ((b * f) %ₘ a).natDegree ≤ d - 1 := by omega
    have hcoeff1 : (((b * f) %ₘ a).coeff (d - 1)) = 1 := by
      simpa [Φ, d] using hf1
    have hmonic : ((b * f) %ₘ a).Monic := by
      apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (d - 1) hdeg_le
      exact hcoeff1
    have hnatDegree : ((b * f) %ₘ a).natDegree = d - 1 := by
      apply le_antisymm hdeg_le
      apply Polynomial.le_natDegree_of_ne_zero
      simp [hcoeff1]
    exact hno ⟨e, f, by simpa [hrepr] using hmonic, by simpa [hrepr, d] using hnatDegree⟩
  obtain ⟨M, hMmax, hrange_le⟩ := Ideal.exists_le_maximal (Φ.range : Ideal R) hrange_ne_top
  let : Field (R ⧸ M) := Ideal.Quotient.field (R := R) M
  let π : R →+* R ⧸ M := Ideal.Quotient.mk M
  have hphi_mem (f : R[X]) : Φ f ∈ M := hrange_le (show Φ f ∈ (Φ.range : Ideal R) from ⟨f, rfl⟩)
  let bbar : (R ⧸ M)[X] := Polynomial.map π b
  have hbbar_ne_zero : bbar ≠ 0 := by
    rcases h with ⟨i, hi⟩
    intro hbbar0
    have himg_ne_zero : π (b.coeff i) ≠ 0 := (IsUnit.map π hi).ne_zero
    have hmap0 : Polynomial.map π b = 0 := by
      simpa [bbar] using hbbar0
    have hcoeff0 : (Polynomial.map π b).coeff i = 0 := by
      rw [hmap0]
      rfl
    have himg_zero : π (b.coeff i) = 0 := by simpa [Polynomial.coeff_map] using hcoeff0
    exact himg_ne_zero himg_zero
  have hmap_monic : (Polynomial.map π a).Monic := ha.map π
  have hdmap : (Polynomial.map π a).natDegree = d := by
    simpa [d] using Polynomial.Monic.natDegree_map ha π
  let n := bbar.natDegree
  have hn_lt : n < d := by
    exact lt_of_le_of_lt (Polynomial.natDegree_map_le (f := π) (p := b)) (by simpa [d] using hb)
  let qbar : (R ⧸ M)[X] := Polynomial.C bbar.leadingCoeff⁻¹ * Polynomial.X ^ (d - 1 - n)
  have hlead_ne_zero : bbar.leadingCoeff ≠ 0 := by
    intro hzero
    exact hbbar_ne_zero (Polynomial.leadingCoeff_eq_zero.mp hzero)
  have hqbar_ne_zero : qbar ≠ 0 := by
    have hC_ne_zero : Polynomial.C bbar.leadingCoeff⁻¹ ≠ 0 := by
      exact Polynomial.C_ne_zero.mpr (inv_ne_zero hlead_ne_zero)
    have hX_ne_zero : (Polynomial.X ^ (d - 1 - n) : (R ⧸ M)[X]) ≠ 0 := by
      exact pow_ne_zero _ Polynomial.X_ne_zero
    exact mul_ne_zero hC_ne_zero hX_ne_zero
  have hqbar_natDegree : qbar.natDegree = d - 1 - n := by
    apply Polynomial.natDegree_C_mul_X_pow
    simpa [hlead_ne_zero]
  have hprod_natDegree : (bbar * qbar).natDegree = d - 1 := by
    rw [Polynomial.natDegree_mul hbbar_ne_zero hqbar_ne_zero, hqbar_natDegree]
    omega
  have hcoeff_top : (bbar * qbar).coeff (d - 1) = 1 := by
    rw [← hprod_natDegree, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul]
    simp [qbar, mul_inv_cancel₀ hlead_ne_zero]
  have hmod_self : (bbar * qbar) %ₘ Polynomial.map π a = bbar * qbar := by
    rw [Polynomial.modByMonic_eq_self_iff hmap_monic]
    have hprod_ne_zero : bbar * qbar ≠ 0 := mul_ne_zero hbbar_ne_zero hqbar_ne_zero
    rw [Polynomial.degree_eq_natDegree hprod_ne_zero, Polynomial.degree_eq_natDegree hmap_monic.ne_zero]
    exact_mod_cast hprod_natDegree.trans_lt (by simpa [hdmap])
  have hcoeff_one : (((bbar * qbar) %ₘ Polynomial.map π a).coeff (d - 1)) = 1 := by
    simpa [hmod_self] using hcoeff_top
  obtain ⟨f, hf⟩ := Polynomial.map_surjective π Ideal.Quotient.mk_surjective qbar
  have hpi : π (Φ f) = 1 := by
    dsimp [Φ]
    rw [← Polynomial.coeff_map, Polynomial.map_modByMonic π ha, Polynomial.map_mul, hf]
    simpa [bbar, qbar] using hcoeff_one
  have hzero : π (Φ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hphi_mem f)
  have hπ1 : π (1 : R) = 0 := hpi.symm.trans hzero
  have h1_mem : (1 : R) ∈ M := Ideal.Quotient.eq_zero_iff_mem.mp hπ1
  exact hMmax.ne_top (Ideal.eq_top_of_isUnit_mem M h1_mem (isUnit_one : IsUnit (1 : R)))

end degree

section horrocks

private def basisVec {A : Type*} [CommRing A] (o : s) : s → A := fun i => if i = o then 1 else 0

private noncomputable def transvectionGL {A : Type*} [CommRing A] (i j : s) (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup s A :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j c) <| by
    simp [Matrix.det_transvection_of_ne i j hij c]

private lemma transvectionGL_mulVec_same {A : Type*} [CommRing A] (i j : s) (hij : i ≠ j)
    (c : A) (v : s → A) :
    (transvectionGL (s := s) i j hij c).1.mulVec v i = v i + c * v j := by
  change (Matrix.transvection i j c).mulVec v i = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp

private lemma transvectionGL_mulVec_of_ne {A : Type*} [CommRing A] (i j a : s) (hij : i ≠ j)
    (ha : a ≠ i) (c : A) (v : s → A) :
    (transvectionGL (s := s) i j hij c).1.mulVec v a = v a := by
  change (Matrix.transvection i j c).mulVec v a = _
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  simp [ha]

private noncomputable def permGL {A : Type*} [CommRing A] (σ : Equiv.Perm s) : Matrix.GeneralLinearGroup s A :=
  Matrix.GeneralLinearGroup.mk'' (Equiv.Perm.permMatrix A σ) <| by
    simpa [Matrix.det_permutation] using
      (show IsUnit ((↑↑(Equiv.Perm.sign σ)) : A) from
        (Units.map (Int.castRingHom A).toMonoidHom (Equiv.Perm.sign σ)).isUnit)

private lemma permGL_mulVec {A : Type*} [CommRing A] (σ : Equiv.Perm s) (v : s → A) :
    (permGL (s := s) (A := A) σ).1.mulVec v = v ∘ σ := by
  change (Equiv.Perm.permMatrix A σ).mulVec v = _
  rw [Matrix.permMatrix_mulVec]

private theorem ideal_span_range_mulVec_local {A : Type*} [CommRing A]
    (M : Matrix.GeneralLinearGroup s A) (v : s → A) :
    Ideal.span (Set.range (M.1.mulVec v)) = Ideal.span (Set.range v) := by
  have span_mulVec_le (N : Matrix.GeneralLinearGroup s A) (w : s → A) :
      Ideal.span (Set.range (N.1.mulVec w)) ≤ Ideal.span (Set.range w) := by
    let I : Ideal A := Ideal.span (Set.range w)
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hwj (j : s) : w j ∈ I := Ideal.subset_span ⟨j, rfl⟩
    have hterm (j : s) : N.1 i j * w j ∈ I := by
      simpa [mul_comm] using I.mul_mem_left (N.1 i j) (hwj j)
    simpa [Matrix.mulVec, dotProduct, I] using I.sum_mem (fun j _ => hterm j)
  refine le_antisymm (span_mulVec_le M v) ?_
  simpa only [Matrix.coe_units_inv, Matrix.mulVec_mulVec, Matrix.isUnits_det_units,
    Matrix.nonsing_inv_mul, Matrix.one_mulVec] using span_mulVec_le (M⁻¹) (M.1.mulVec v)

private theorem isUnimodular_iff_of_unimodularVectorEquiv_local {A : Type*} [CommRing A]
    {v w : s → A} (hvw : UnimodularVectorEquiv v w) :
    IsUnimodular v ↔ IsUnimodular w := by
  rcases hvw with ⟨M, rfl⟩
  unfold IsUnimodular
  simp [ideal_span_range_mulVec_local (s := s) M v]

private def twoByTwoMatrix {A : Type*} [CommRing A] (o i : s) (a b α β : A) : Matrix s s A :=
  fun r c =>
    if r = o then
      if c = o then α else if c = i then β else 0
    else if r = i then
      if c = o then -b else if c = i then a else 0
    else 0

private def twoByTwoInv {A : Type*} [CommRing A] (o i : s) (a b α β : A) : Matrix s s A :=
  fun r c =>
    if r = o then
      if c = o then a else if c = i then -β else 0
    else if r = i then
      if c = o then b else if c = i then α else 0
    else 0

private theorem equiv_basis_of_eq_one {A : Type*} [CommRing A] (o j : s) (v : s → A)
    (hj : v j = 1) : UnimodularVectorEquiv v (basisVec (s := s) (A := A) o) := by
  have hclear :
      ∀ t : Finset s, t ⊆ Finset.univ.erase j →
        UnimodularVectorEquiv v (fun a => if a = j then 1 else if a ∈ t then 0 else v a) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      refine ⟨1, ?_⟩
      ext a
      by_cases ha : a = j
      · simp [ha, hj]
      · simp [ha]
    · intro a t ha hrec ht
      have hsub : t ⊆ Finset.univ.erase j := by
        intro x hx
        exact ht (by simp [hx])
      have hneq : a ≠ j := by
        have : a ∈ Finset.univ.erase j := ht (by simp [ha])
        simpa [Finset.mem_erase, Finset.mem_univ] using this
      let w : s → A := fun b => if b = j then 1 else if b ∈ t then 0 else v b
      have hw : UnimodularVectorEquiv v w := hrec hsub
      let w' : s → A := fun b => if b = j then 1 else if b ∈ insert a t then 0 else v b
      have hstep : UnimodularVectorEquiv w w' := by
        refine ⟨transvectionGL (s := s) a j hneq (-(w a)), ?_⟩
        ext b
        by_cases hbj : b = j
        · have hba' : b ≠ a := by simpa [hbj] using hneq.symm
          rw [transvectionGL_mulVec_of_ne (s := s) a j b hneq hba']
          simp [w, w', hbj]
        · by_cases hba : b = a
          · have hsame :=
                transvectionGL_mulVec_same (s := s) a j hneq (-(w a)) w
            have hwa : w a = v a := by
              simp [w, hneq, ha]
            simpa [hba, w, w', hneq, ha, hwa, hj] using hsame
          · rw [transvectionGL_mulVec_of_ne (s := s) a j b hneq hba]
            by_cases hbt : b ∈ t
            · simp [w, w', hbj, hba, hbt]
            · simp [w, w', hbj, hba, hbt]
      exact (unimodularVectorEquiv_equivalence.trans hw hstep)
  have hjbasis :
      UnimodularVectorEquiv v (basisVec (s := s) (A := A) j) := by
    have htmp := hclear (Finset.univ.erase j) (by intro x hx; exact hx)
    change UnimodularVectorEquiv v (fun a => if a = j then 1 else 0)
    convert htmp using 2
    rename_i a
    by_cases ha : a = j
    · simp [ha]
    · simp [ha, Finset.mem_erase, Finset.mem_univ]
  by_cases hjo : j = o
  · simpa [hjo] using hjbasis
  · have hswap :
        UnimodularVectorEquiv (basisVec (s := s) (A := A) j) (basisVec (s := s) (A := A) o) := by
      refine ⟨permGL (s := s) (A := A) (Equiv.swap j o), ?_⟩
      ext a
      rw [permGL_mulVec]
      by_cases hao : a = o
      · subst hao
        simp [basisVec]
      · by_cases haj : a = j
        · have hleft : (basisVec (s := s) (A := A) j) ((Equiv.swap j o) a) = 0 := by
            have hoj : o ≠ j := fun h => hjo h.symm
            simp [basisVec, haj, hoj]
          have hright : basisVec (s := s) (A := A) o a = 0 := by
            simp [basisVec, hao]
          exact hleft.trans hright.symm
        · simp [basisVec, hao, haj, Equiv.swap_apply_of_ne_of_ne]
    exact (unimodularVectorEquiv_equivalence.trans hjbasis hswap)

private theorem equiv_basis_of_two {A : Type*} [CommRing A] (o i : s) (hoi : o ≠ i)
    (v : s → A) (hcover : ∀ x : s, x = o ∨ x = i)
    (hbez : ∃ α β : A, α * v o + β * v i = 1) :
    UnimodularVectorEquiv v (basisVec (s := s) (A := A) o) := by
  rcases hbez with ⟨α, β, hbez⟩
  let M : Matrix s s A := twoByTwoMatrix o i (v o) (v i) α β
  let N : Matrix s s A := twoByTwoInv o i (v o) (v i) α β
  have huniv : (Finset.univ : Finset s) = {o, i} := by
    ext x
    simp [hcover x]
  have hleft : N * M = 1 := by
    ext r c
    rcases hcover r with hr | hr <;> rcases hcover c with hc | hc
    · rw [Matrix.mul_apply, huniv]
      have hio : i ≠ o := fun h => hoi h.symm
      simp [M, N, twoByTwoMatrix, twoByTwoInv, hr, hc, hoi, hio]
      simpa [Matrix.one_apply, hr, hc, hoi, mul_comm] using hbez
    · rw [Matrix.mul_apply, huniv]
      have hio : i ≠ o := fun h => hoi h.symm
      simp [M, N, twoByTwoMatrix, twoByTwoInv, hr, hc, hoi, hio]
      ring
    · rw [Matrix.mul_apply, huniv]
      have hio : i ≠ o := fun h => hoi h.symm
      simp [M, N, twoByTwoMatrix, twoByTwoInv, hr, hc, hoi, hio]
      ring
    · rw [Matrix.mul_apply, huniv]
      have hio : i ≠ o := fun h => hoi h.symm
      simp [M, N, twoByTwoMatrix, twoByTwoInv, hr, hc, hoi, hio]
      simpa [Matrix.one_apply, hr, hc, hoi, mul_comm, add_comm] using hbez
  refine ⟨Matrix.GeneralLinearGroup.mk'' M (Matrix.isUnit_det_of_left_inverse hleft), ?_⟩
  ext a
  rcases hcover a with ha | ha
  · rw [Matrix.mulVec, dotProduct, huniv]
    have hio : i ≠ o := fun h => hoi h.symm
    simp [M, twoByTwoMatrix, basisVec, ha, hoi, hio]
    simpa [mul_comm] using hbez
  · rw [Matrix.mulVec, dotProduct, huniv]
    have hio : i ≠ o := fun h => hoi h.symm
    simp [M, twoByTwoMatrix, basisVec, ha, hoi, hio]
    ring

/-- Let `A = R[X]` for a local ring `R`. Then any unimodular vector in `A^s` with a monic
component is equivalent to `e₁`. -/
theorem horrocks [IsLocalRing R] (o : s) (v : s → R[X]) (huv : IsUnimodular v)
    (h : ∃ i : s, (v i).Monic) : UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  let eo : s → R[X] := basisVec o
  have haux :
      ∀ d : ℕ, ∀ w : s → R[X], IsUnimodular w →
        (∃ j : s, (w j).Monic ∧ (w j).natDegree = d) →
        UnimodularVectorEquiv (R := R[X]) w eo := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih w huw hmon
    rcases hmon with ⟨j, hjmonic, hjdeg⟩
    by_cases hd0 : d = 0
    · have hwj_C : w j = C ((w j).coeff 0) := by
        simpa [hd0] using Polynomial.eq_C_of_natDegree_eq_zero (hjdeg.trans hd0)
      have hwj_coeff : (w j).coeff 0 = 1 := by
        simpa [hjdeg, hd0] using hjmonic.coeff_natDegree
      have hwj_one : w j = 1 := by
        calc _ = C ((w j).coeff 0) := hwj_C
          _ = C 1 := by rw [hwj_coeff]
          _ = 1 := by simp
      simpa [eo, basisVec] using equiv_basis_of_eq_one o j w hwj_one
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
      have hwj_ne_one : w j ≠ 1 := by
        apply ne_one_of_natDegree_pos
        simpa [hjdeg] using hd_pos
      have hreduce :
          ∀ t : Finset s, t ⊆ Finset.univ.erase j →
            UnimodularVectorEquiv (R := R[X]) w
              (fun a => if a = j then w j else if a ∈ t then w a %ₘ w j else w a) := by
        intro t
        refine Finset.induction_on t ?_ ?_
        · intro _
          refine ⟨1, ?_⟩
          ext a
          by_cases ha : a = j
          · simp [ha]
          · simp [ha]
        · intro a t ha hrec ht
          have hsub : t ⊆ Finset.univ.erase j := by
            intro x hx
            exact ht (by simp [hx])
          have hneq : a ≠ j := by
            have : a ∈ Finset.univ.erase j := ht (by simp [ha])
            simpa [Finset.mem_erase, Finset.mem_univ] using this
          let u : s → R[X] := fun b => if b = j then w j else if b ∈ t then w b %ₘ w j else w b
          have hu : UnimodularVectorEquiv (R := R[X]) w u := hrec hsub
          let u' : s → R[X] :=
            fun b => if b = j then w j else if b ∈ insert a t then w b %ₘ w j else w b
          have hstep : UnimodularVectorEquiv (R := R[X]) u u' := by
            refine ⟨transvectionGL (s := s) a j hneq (-(w a /ₘ w j)), ?_⟩
            funext b
            by_cases hbj : b = j
            · have hba' : b ≠ a := by simpa [hbj] using hneq.symm
              rw [transvectionGL_mulVec_of_ne (s := s) a j b hneq hba']
              simp [u, u', hbj]
            · by_cases hba : b = a
              · have hsame :=
                    transvectionGL_mulVec_same (s := s) a j hneq (-(w a /ₘ w j)) u
                have hua : u a = w a := by simp [u, hneq, ha]
                have huj : u j = w j := by simp [u]
                have hrem : w a + -(w a /ₘ w j) * w j = w a %ₘ w j := by
                  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
                    mul_assoc] using (Polynomial.modByMonic_eq_sub_mul_div (w a) (w j)).symm
                calc
                  (transvectionGL (s := s) a j hneq (-(w a /ₘ w j))).1.mulVec u b
                      = u a + -(w a /ₘ w j) * u j := by simpa [hba] using hsame
                  _ = w a + -(w a /ₘ w j) * w j := by rw [hua, huj]
                  _ = w a %ₘ w j := hrem
                  _ = u' b := by simp [u', hba, hneq, ha]
              · rw [transvectionGL_mulVec_of_ne (s := s) a j b hneq hba]
                by_cases hbt : b ∈ t
                · simp [u, u', hbj, hba, hbt]
                · simp [u, u', hbj, hba, hbt]
          exact (unimodularVectorEquiv_equivalence.trans hu hstep)
      let wred : s → R[X] := fun a => if a = j then w j else w a %ₘ w j
      have hwred_eqv : UnimodularVectorEquiv (R := R[X]) w wred := by
        have htmp := hreduce (Finset.univ.erase j) (by intro x hx; exact hx)
        convert htmp using 2
        rename_i a
        by_cases ha : a = j
        · simp [wred, ha]
        · simp [wred, ha, Finset.mem_erase, Finset.mem_univ]
      have hwred_unimod : IsUnimodular wred := by
        exact (isUnimodular_iff_of_unimodularVectorEquiv_local hwred_eqv).1 huw
      have hdeg_lt (a : s) (ha : a ≠ j) : (wred a).natDegree < d := by
        have hdeg : (w a %ₘ w j).natDegree < (w j).natDegree := by
          exact Polynomial.natDegree_modByMonic_lt (w a) hjmonic hwj_ne_one
        simpa [wred, ha, hjdeg] using hdeg
      have hunit_coeff :
          ∃ i : s, i ≠ j ∧ ∃ n : ℕ, IsUnit ((wred i).coeff n) := by
        by_contra hnone
        push_neg at hnone
        let π : R →+* IsLocalRing.ResidueField R := IsLocalRing.residue R
        let wbar : s → (IsLocalRing.ResidueField R)[X] := fun a => Polynomial.map π (wred a)
        have hwbar_unimod : IsUnimodular wbar := by
          simpa [wbar] using isUnimodular_map_ringHom (Polynomial.mapRingHom π) wred hwred_unimod
        have hzero (a : s) (ha : a ≠ j) : wbar a = 0 := by
          ext n
          have hcoeff_zero : π ((wred a).coeff n) = 0 := by
            by_contra hne
            exact hnone a ha n ((IsLocalRing.residue_ne_zero_iff_isUnit ((wred a).coeff n)).1 hne)
          simpa [wbar, Polynomial.coeff_map] using hcoeff_zero
        have hunit_bar : IsUnit (wbar j) := by
          have h1mem : (1 : (IsLocalRing.ResidueField R)[X]) ∈ Ideal.span (Set.range wbar) := by
            rw [hwbar_unimod]
            exact Submodule.mem_top
          rcases (Ideal.mem_span_range_iff_exists_fun).1 h1mem with ⟨c, hc⟩
          have hsum : ∑ a : s, c a * wbar a = c j * wbar j := by
            apply Finset.sum_eq_single j
            · intro a _ hne
              simp [hzero a hne]
            · simp
          have hmul : c j * wbar j = 1 := by simpa [hsum] using hc
          exact IsUnit.of_mul_eq_one_right _ hmul
        have hbar_monic : (wbar j).Monic := by
          simpa [wbar, wred] using hjmonic.map π
        have hbar_not_unit : ¬ IsUnit (wbar j) := by
          intro hu
          rcases Polynomial.isUnit_iff.1 hu with ⟨r, _, hr⟩
          have hr1 : r = 1 := by
            have : (Polynomial.C r : (IsLocalRing.ResidueField R)[X]).Monic := by
              simpa [hr] using hbar_monic
            simpa using this.coeff_natDegree
          have hdeg_bar : (wbar j).natDegree = d := by
            simpa [wbar, wred, hjdeg] using Polynomial.Monic.natDegree_map hjmonic π
          rw [← hr, hr1] at hdeg_bar
          simp at hdeg_bar
          exact (Nat.ne_of_gt hd_pos) hdeg_bar.symm
        exact hbar_not_unit hunit_bar
      rcases hunit_coeff with ⟨i, hi_ne, n, hin⟩
      by_cases hthird : ∃ k : s, k ≠ j ∧ k ≠ i
      · rcases hthird with ⟨k, hk_ne_j, hk_ne_i⟩
        have hwred_i_deg : (wred i).natDegree < (wred j).natDegree := by
          simpa [wred, hi_ne, hjdeg] using hdeg_lt i hi_ne
        obtain ⟨e, f, hue_monic, hue_deg⟩ :=
          degree_lowering (wred j) (wred i) (by simpa [wred] using hjmonic) hwred_i_deg ⟨n, hin⟩
        let γr : R := 1 - (wred k).coeff (d - 1)
        let γ : R[X] := C γr
        let w1 : s → R[X] := fun a => if a = k then wred a + (γ * e) * wred j else wred a
        have hw1 : UnimodularVectorEquiv (R := R[X]) wred w1 := by
          refine ⟨transvectionGL (s := s) k j hk_ne_j (γ * e), ?_⟩
          funext a
          by_cases hak : a = k
          · simpa [w1, hak] using transvectionGL_mulVec_same (s := s) k j hk_ne_j (γ * e) wred
          · rw [transvectionGL_mulVec_of_ne (s := s) k j a hk_ne_j hak]
            simp [w1, hak]
        let wnew : s → R[X] :=
          fun a => if a = k then w1 a + (γ * f) * w1 i else w1 a
        have hwnew1 : UnimodularVectorEquiv (R := R[X]) w1 wnew := by
          refine ⟨transvectionGL (s := s) k i hk_ne_i (γ * f), ?_⟩
          funext a
          by_cases hak : a = k
          · simpa [wnew, hak] using transvectionGL_mulVec_same (s := s) k i hk_ne_i (γ * f) w1
          · rw [transvectionGL_mulVec_of_ne (s := s) k i a hk_ne_i hak]
            simp [wnew, hak]
        have hwnew_eqv : UnimodularVectorEquiv (R := R[X]) w wnew :=
          (unimodularVectorEquiv_equivalence.trans hwred_eqv)
            (unimodularVectorEquiv_equivalence.trans hw1 hwnew1)
        have hwnew_unimod : IsUnimodular wnew := by
          exact (isUnimodular_iff_of_unimodularVectorEquiv_local hwnew_eqv).1 huw
        let u : R[X] := wred j * e + wred i * f
        have hu_monic : u.Monic := by
          simpa [u] using hue_monic
        have hu_deg : u.natDegree = d - 1 := by
          simpa [u, wred, hjdeg] using hue_deg
        have hγu_le : (γ * u).natDegree ≤ d - 1 := by
          exact le_trans (Polynomial.natDegree_C_mul_le γr u) (by simp [hu_deg])
        have hwred_k_le : (wred k).natDegree ≤ d - 1 := by
          have hklt : (wred k).natDegree < d := hdeg_lt k hk_ne_j
          omega
        have hwk_coeff : (wred k + γ * u).coeff (d - 1) = 1 := by
          have hu_coeff : u.coeff (d - 1) = 1 := by
            simpa [hu_deg] using hu_monic.coeff_natDegree
          rw [Polynomial.coeff_add]
          change (wred k).coeff (d - 1) + (C γr * u).coeff (d - 1) = 1
          rw [Polynomial.coeff_C_mul]
          simp [γr, hu_coeff]
        have hwk_le : (wred k + γ * u).natDegree ≤ d - 1 := by
          exact le_trans (Polynomial.natDegree_add_le _ _)
            (max_le_iff.mpr ⟨hwred_k_le, hγu_le⟩)
        have hwk_monic : (wred k + γ * u).Monic := by
          exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one (d - 1) hwk_le hwk_coeff
        have hw1_i : w1 i = wred i := by
          simp [w1, hk_ne_i.symm]
        have hw1_k : w1 k = wred k + γ * e * wred j := by
          simp [w1]
        have hwnew_k : wnew k = wred k + γ * u := by
          calc
            wnew k = w1 k + γ * f * w1 i := by simp [wnew]
            _ = (wred k + γ * e * wred j) + γ * f * wred i := by
                  rw [hw1_k, hw1_i]
            _ = wred k + γ * (wred j * e + wred i * f) := by ring
            _ = wred k + γ * u := by simp [u]
        have hnew_monic : ∃ a : s, (wnew a).Monic ∧ (wnew a).natDegree = d - 1 := by
          refine ⟨k, ?_, ?_⟩
          · simpa [hwnew_k] using hwk_monic
          · have : (wred k + γ * u).natDegree = d - 1 := by
              apply le_antisymm hwk_le
              exact Polynomial.le_natDegree_of_ne_zero (by simp [hwk_coeff])
            simpa [hwnew_k] using this
        exact (unimodularVectorEquiv_equivalence.trans hwnew_eqv)
          (ih (d - 1) (by omega) wnew hwnew_unimod hnew_monic)
      · have hcover2 (x : s) : x = j ∨ x = i := by
          by_cases hxj : x = j
          · exact Or.inl hxj
          · by_cases hxi : x = i
            · exact Or.inr hxi
            · exact False.elim (hthird ⟨x, hxj, hxi⟩)
        have h1mem : (1 : R[X]) ∈ Ideal.span (Set.range wred) := by
          rw [hwred_unimod]
          exact Submodule.mem_top
        rcases (Ideal.mem_span_range_iff_exists_fun).1 h1mem with ⟨c, hc⟩
        have huniv2 : (Finset.univ : Finset s) = {j, i} := by
          ext x
          simp [hcover2 x]
        have hbez2 : c j * wred j + c i * wred i = 1 := by
          rw [← hc, huniv2]
          symm
          simp [hi_ne.symm]
        by_cases hoj : o = j
        · let hcoverji : ∀ x : s, x = j ∨ x = i := hcover2
          have hpair : UnimodularVectorEquiv (R := R[X]) wred (basisVec j) := by
            exact equiv_basis_of_two j i hi_ne.symm wred hcoverji
              ⟨c j, c i, hbez2⟩
          simpa [eo, basisVec, hoj] using
            (unimodularVectorEquiv_equivalence.trans hwred_eqv hpair)
        · have hoi' : o = i := by
            rcases hcover2 o with rfl | rfl
            · exact False.elim (hoj rfl)
            · rfl
          have hcoverij : ∀ x : s, x = i ∨ x = j := by
            intro x
            rcases hcover2 x with hxi | hxj
            · exact Or.inr hxi
            · exact Or.inl hxj
          have hbez2' : c i * wred i + c j * wred j = 1 := by
            simpa [add_comm] using hbez2
          have hpair : UnimodularVectorEquiv (R := R[X]) wred (basisVec i) := by
            exact equiv_basis_of_two i j hi_ne wred hcoverij
              ⟨c i, c j, hbez2'⟩
          simpa [eo, basisVec, hoi'] using
            (unimodularVectorEquiv_equivalence.trans hwred_eqv hpair)
  rcases h with ⟨j, hj⟩
  exact haux (v j).natDegree v huv ⟨j, hj, rfl⟩

end horrocks

/-- If $R$ is local and $v(x) \in R[x]^s$ is a unimodular vector one of whose elements is monic,
  then $v(x) \sim v(0)$. -/
theorem cor9 [IsLocalRing R] (v : s → R[X]) (hv : IsUnimodular v)
    (h : ∃ i : s, (v i).Monic) : UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  rcases h with ⟨j, hj⟩
  let ej : s → R[X] := fun i => if i = j then 1 else 0
  have hv_ej : UnimodularVectorEquiv v ej := by simpa [ej] using (horrocks j v hv ⟨j, hj⟩)
  let ev0 : R[X] →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
  have h0 : UnimodularVectorEquiv (fun i => (v i).coeff 0) (fun i : s => if i = j then 1 else 0) :=
    by simpa [ev0, ej] using unimodularVectorEquiv_map ev0 hv_ej
  have hC : UnimodularVectorEquiv (fun i => C ((v i).coeff 0)) ej := by
    simpa [ej] using unimodularVectorEquiv_map (C : R →+* R[X]) h0
  simpa [Polynomial.coeff_zero_eq_eval_zero] using
    unimodularVectorEquiv_equivalence.trans hv_ej (unimodularVectorEquiv_equivalence.symm hC)

open Bivariate

variable {R : Type*} [CommRing R] [IsDomain R] {s : Type*} [Fintype s] [DecidableEq s]

section lem10

lemma clearDenominators_poly_map {T A B : Type*} [CommRing T] [CommRing A] [CommRing B]
    {S : Submonoid T} (g : A →+* B) (num : S →* A)
    (hclear : ∀ b : B, ∃ c : S, ∃ a : A, g a = b * g (num c)) (p : B[X]) :
    ∃ c : S, ∃ q : A[X], Polynomial.map g q = p * C (g (num c)) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rcases hp with ⟨cp, qp, hqp⟩
    rcases hq with ⟨cq, qq, hqq⟩
    refine ⟨cp * cq, qp * C (num cq) + qq * C (num cp), ?_⟩
    simp [hqp, hqq, add_mul, mul_left_comm, mul_comm]
  · intro n b
    rcases hclear b with ⟨c, a, ha⟩
    exact ⟨c, Polynomial.monomial n a, by simp [ha]⟩

lemma generalLinearGroup_det_eq_one_of_eval_zero_eq_one (G : GL s (Polynomial R))
    (hG0 : (Polynomial.eval₂RingHom (RingHom.id R) 0).mapMatrix G.1 = 1) : G.1.det = 1 := by
  rcases Polynomial.isUnit_iff.1 (Matrix.isUnits_det_units G) with ⟨r, _, hdet⟩
  have hdet0 : (Polynomial.eval₂RingHom (RingHom.id R) 0) G.1.det = 1 := by
    simpa [RingHom.map_det] using congrArg Matrix.det hG0
  have hr1 : r = 1 := by
    calc r = (Polynomial.eval₂RingHom (RingHom.id R) 0) (C r) := by simp
      _ = _ := by rw [hdet, hdet0]
  rw [← hdet, hr1, map_one]

/-- Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such
  that $v(x) \sim v(x + cy)$ over $R[x, y]$. -/
theorem lem10 {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
    (h : UnimodularVectorEquiv (fun i => (v i).map (algebraMap R (Localization S)))
      (fun i => C (algebraMap R (Localization S) ((v i).eval 0)))) :
    ∃ c : S, UnimodularVectorEquiv (fun i => C (v i))
      (fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y)) := by
  let L := Localization S
  let f : R →+* L := algebraMap R L
  let fX : R[X] →+* L[X] := Polynomial.mapRingHom f
  let fXY : R[X][Y] →+* L[X][Y] := Polynomial.mapRingHom fX
  let ccR : S → R[X][Y] := fun c => C (C (c : R))
  let ccL : S → L[X][Y] := fun c => C (C (f c))
  let ιR : R →+* R[X][Y] := (C : R[X] →+* R[X][Y]).comp C
  let ιL : L →+* L[X][Y] := (C : L[X] →+* L[X][Y]).comp C
  let vL : s → L[X] := fun i => (v i).map f
  let vx : s → R[X][Y] := fun i => C (v i)
  let vxL : s → L[X][Y] := fun i => C (vL i)
  let vxy1L : s → L[X][Y] := fun i => (vL i).eval₂ ιL (C X + Y)
  let constL : s → L[X] := fun i => C (f ((v i).eval 0))
  let const2L : s → L[X][Y] := fun i => C (constL i)
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hs
  have hfX_inj : Function.Injective fX := Polynomial.map_injective f (IsLocalization.injective L hs)
  have hfXY_inj : Function.Injective fXY := Polynomial.map_injective fX hfX_inj
  let numR : S →* R := {
    toFun := fun c : S => (c : R)
    map_one' := rfl
    map_mul' := fun _ _ => rfl
  }
  have clearCoeff (a : L) : ∃ c : S, ∃ r : R, f r = a * f c := by
    rcases IsLocalization.surj S a with ⟨⟨r, c⟩, hc⟩
    exact ⟨c, r, hc.symm⟩
  have clearX : ∀ p : L[X], ∃ c : S, ∃ q : R[X], Polynomial.map f q = p * C (f c) :=
    clearDenominators_poly_map f numR clearCoeff
  let numRX : S →* R[X] := {
    toFun := fun c : S => C (c : R)
    map_one' := by simp
    map_mul' := fun _ _ => by simp
  }
  have clearCoeffX (a : L[X]) : ∃ c : S, ∃ q : R[X], fX q = a * fX (numRX c) := by
    simpa [fX, numRX] using clearX a
  have clearXY : ∀ p : L[X][Y], ∃ c : S, ∃ q : R[X][Y], Polynomial.map fX q = p * ccL c := by
    intro p
    simpa [fX, numRX, ccL] using clearDenominators_poly_map fX numRX clearCoeffX p
  rcases h with ⟨M, hM⟩
  let lift : L[X] →+* L[X][Y] := C
  let shift1 : L[X] →+* L[X][Y] := Polynomial.eval₂RingHom ιL (C X + Y)
  let MC : Matrix.GeneralLinearGroup s L[X][Y] := Matrix.GeneralLinearGroup.map lift M
  let Mshift : Matrix.GeneralLinearGroup s L[X][Y] := Matrix.GeneralLinearGroup.map shift1 M
  let P : Matrix.GeneralLinearGroup s L[X][Y] := Mshift⁻¹ * MC
  have hMC : MC.1.mulVec vxL = const2L := generalLinearGroup_map_mulVec_eq lift M hM
  have hMshift : Mshift.1.mulVec vxy1L = const2L := by
    calc
      Mshift.1.mulVec vxy1L = fun i => ιL (f ((v i).eval 0)) := by
        simpa [Mshift, shift1, vxy1L, constL] using generalLinearGroup_map_mulVec_eq shift1 M hM
      _ = const2L := by
            funext i
            simp [const2L, constL, ιL]
  have hPvxL : P.1.mulVec vxL = vxy1L := by
    change
      ((Mshift⁻¹ * MC : Matrix.GeneralLinearGroup s (Localization S)[X][Y]).1).mulVec vxL = vxy1L
    calc
      ((Mshift⁻¹ * MC : Matrix.GeneralLinearGroup s (Localization S)[X][Y]).1).mulVec vxL
          = (Mshift⁻¹).1.mulVec (MC.1.mulVec vxL) := by simp [L]
      _ = (Mshift⁻¹).1.mulVec (Mshift.1.mulVec vxy1L) := by rw [hMC, hMshift]
      _ = (((Mshift⁻¹).1 * Mshift.1).mulVec vxy1L) := by
            exact Matrix.mulVec_mulVec vxy1L (Mshift⁻¹).1 Mshift.1
      _ = vxy1L := by simp
  let ev0Y : L[X][Y] →+* L[X] := Polynomial.eval₂RingHom (RingHom.id L[X]) 0
  have h_ev0_shift1 (p : L[X]) : ev0Y (shift1 p) = p := by
    have hcomp : ev0Y.comp ιL = (C : L →+* L[X]) := by
      ext a
      simp [ιL, ev0Y]
    have hX : ev0Y (C X + Y) = X := by simp [ev0Y]
    calc
      ev0Y (shift1 p) = Polynomial.eval₂ (ev0Y.comp ιL) (ev0Y (C X + Y)) p :=
        Polynomial.hom_eval₂ p ιL ev0Y (C X + Y)
      _ = p := by rw [hcomp, hX, Polynomial.eval₂_C_X]
  have hMC0 : Matrix.GeneralLinearGroup.map ev0Y MC = M := by
    ext i j
    simp [MC, lift, ev0Y]
  have hMshift0 : Matrix.GeneralLinearGroup.map ev0Y Mshift = M := by
    ext i j n
    exact congrArg (fun p : (Localization S)[X] => p.coeff n) (h_ev0_shift1 (M.1 i j))
  have hP0_gl : Matrix.GeneralLinearGroup.map ev0Y P = 1 := by
    change Matrix.GeneralLinearGroup.map ev0Y
      (Mshift⁻¹ * MC : Matrix.GeneralLinearGroup s (Localization S)[X][Y]) = 1
    simp [MonoidHom.map_mul, MonoidHom.map_inv, hMshift0, hMC0, L]
  have hP0 : ev0Y.mapMatrix P.1 = 1 :=
    congrArg (fun g : Matrix.GeneralLinearGroup s L[X] => (g : Matrix s s L[X])) hP0_gl
  have hdiv (i j : s) :
      ∃ w : L[X][Y], P.1 i j - (if i = j then (1 : L[X][Y]) else 0) = Y * w := by
    have hentry : ev0Y (P.1 i j) = if i = j then (1 : L[X]) else 0 := congrFun (congrFun hP0 i) j
    have hcoeff0 : (P.1 i j - (if i = j then (1 : L[X][Y]) else 0)).coeff 0 = 0 := by
      by_cases hij : i = j
      · subst hij
        simpa [Polynomial.coeff_zero_eq_eval_zero, ev0Y, sub_eq_zero] using hentry
      · simpa [Polynomial.coeff_zero_eq_eval_zero, ev0Y, hij] using hentry
    rcases (Polynomial.X_dvd_iff).2 hcoeff0 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa using hw
  let W : Matrix s s L[X][Y] := fun i j => Classical.choose (hdiv i j)
  have hW : ∀ i j, P.1 i j = (if i = j then 1 else 0) + Y * W i j := by
    intro i j
    have hw := Classical.choose_spec (hdiv i j)
    simpa [W, add_comm] using (sub_eq_iff_eq_add).1 hw
  have hclearW :
      ∃ c : S, ∃ W0 : Matrix s s R[X][Y], ∀ i j, Polynomial.map fX (W0 i j) = W i j * ccL c := by
    let Pidx (t : Finset (s × s)) : Prop :=
      ∃ c : S, ∃ W0 : Matrix s s R[X][Y], ∀ ij ∈ t, Polynomial.map fX (W0 ij.1 ij.2) = W ij.1 ij.2 * ccL c
    have hPidx : ∀ t : Finset (s × s), Pidx t := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · refine ⟨1, fun _ _ => 0, ?_⟩
        intro ij hij
        simp at hij
      · intro a t ha ht
        rcases ht with ⟨c0, W0, hW0⟩
        rcases clearXY (W a.1 a.2) with ⟨c1, qa, hqa⟩
        have hmapc0 : fX (C (c0 : R)) = C (f c0) := by simp [fX]
        have hmapc1 : fX (C (c1 : R)) = C (f c1) := by simp [fX]
        refine ⟨c0 * c1, fun i j => if (i, j) = a then qa * ccR c0 else W0 i j * ccR c1, ?_⟩
        intro ij hij
        by_cases hEq : ij = a
        · subst hEq
          simp only [Prod.mk.eta, ↓reduceIte, Polynomial.map_mul, hqa, mul_comm, map_C, hmapc0,
            Submonoid.coe_mul, map_mul, mul_assoc, ccR, ccL]
        · have hijt : ij ∈ t := by simpa [Finset.mem_insert, hEq] using hij
          simp only [Prod.mk.eta, hEq, ↓reduceIte, Polynomial.map_mul, hW0 ij hijt, mul_comm, map_C,
            hmapc1, mul_left_comm, Submonoid.coe_mul, map_mul, mul_assoc, ccR, ccL]
    rcases hPidx Finset.univ with ⟨c, W0, hW0⟩
    refine ⟨c, W0, ?_⟩
    intro i j
    exact hW0 (i, j) (Finset.mem_univ _)
  rcases hclearW with ⟨c, W0, hW0fun⟩
  let substR : R[X][Y] →+* R[X][Y] := Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) (ccR c * Y)
  let substL : L[X][Y] →+* L[X][Y] := Polynomial.eval₂RingHom (C : L[X] →+* L[X][Y]) (ccL c * Y)
  let B : Matrix s s R[X][Y] := fun i j => (if i = j then 1 else 0) + Y * substR (W0 i j)
  let vxy : s → R[X][Y] := fun i => (v i).eval₂ ιR (C X + ccR c * Y)
  let vxyL : s → L[X][Y] := fun i => (vL i).eval₂ ιL (C X + ccL c * Y)
  have hcompC : fXY.comp (C : R[X] →+* R[X][Y]) = (C : L[X] →+* L[X][Y]).comp fX := by
    apply Polynomial.ringHom_ext
    · intro p
      simp [fXY, fX]
    · simp [fXY, fX]
  have hmap_cc : fXY (ccR c * Y) = ccL c * Y := by
    simp [fXY, fX, ccR, ccL]
  have hsubst_W0 (i j : s) : fXY (substR (W0 i j)) = substL (W i j * ccL c) := by
    calc
      fXY (substR (W0 i j))
          = Polynomial.eval₂ (fXY.comp (C : R[X] →+* R[X][Y])) (fXY (ccR c * Y)) (W0 i j) :=
            Polynomial.hom_eval₂ (W0 i j) (C : R[X] →+* R[X][Y]) fXY (ccR c * Y)
      _ = Polynomial.eval₂ ((C : L[X] →+* L[X][Y]).comp fX) (ccL c * Y) (W0 i j) := by
            rw [hcompC, hmap_cc]
      _ = (Polynomial.map fX (W0 i j)).eval₂ (C : L[X] →+* L[X][Y]) (ccL c * Y) :=
        (Polynomial.eval₂_map fX (C : L[X] →+* L[X][Y]) (ccL c * Y)).symm
      _ = substL (W i j * ccL c) := by
            rw [hW0fun i j]
            rfl
  have hfXY_Y : fXY Y = Y := by simp [fXY, fX]
  have hfXY_diag (i j : s) : fXY (if i = j then (1 : R[X][Y]) else 0) = if i = j then 1 else 0 := by
    by_cases hij : i = j <;> simp [hij, fXY, fX]
  have hYW (i j : s) : Y * substL (W i j * ccL c) = substL Y * substL (W i j) := by
    calc
      Y * substL (W i j * ccL c) = Y * (substL (W i j) * ccL c) := by simp [substL, ccL, map_mul]
      _ = (ccL c * Y) * substL (W i j) := by simp [mul_assoc, mul_comm]
      _ = substL Y * substL (W i j) := by simp [substL, ccL]
  have hBij (i j : s) : fXY (B i j) = substL (P.1 i j) := by
    calc
      fXY (B i j) = (if i = j then 1 else 0) + Y * substL (W i j * ccL c) := by
        calc
          fXY (B i j) = fXY ((if i = j then 1 else 0) + Y * substR (W0 i j)) := by rfl
          _ = (if i = j then 1 else 0) + fXY (Y * substR (W0 i j)) := by
                rw [map_add, hfXY_diag i j]
          _ = (if i = j then 1 else 0) + fXY Y * fXY (substR (W0 i j)) := by
                rw [map_mul]
          _ = (if i = j then 1 else 0) + Y * substL (W i j * ccL c) := by
                rw [hsubst_W0 i j, hfXY_Y]
      _ = (if i = j then 1 else 0) + substL Y * substL (W i j) := by
        rw [hYW i j]
      _ = substL (P.1 i j) := by
        have hconst : substL (if i = j then (1 : L[X][Y]) else 0) = (if i = j then 1 else 0) := by
          by_cases hij : i = j <;> simp [hij]
        calc
          (if i = j then 1 else 0) + substL Y * substL (W i j)
          _ = substL ((if i = j then (1 : L[X][Y]) else 0) + Y * W i j) := by
                rw [map_add, map_mul, hconst]
          _ = substL (P.1 i j) := by
                rw [hW i j]
  have hBmap : fXY.mapMatrix B = substL.mapMatrix P.1 := by
    funext i
    funext j
    exact hBij i j
  have hev0_subst : ev0Y.comp substL = ev0Y := by
    apply Polynomial.ringHom_ext
    · intro p
      simp [ev0Y, substL]
    · simp [ev0Y, substL, ccL]
  have hPsub0 : ev0Y.mapMatrix (substL.mapMatrix P.1) = 1 := by
    calc
      ev0Y.mapMatrix (substL.mapMatrix P.1) = (ev0Y.comp substL).mapMatrix P.1 := by
        ext i j
        rfl
      _ = ev0Y.mapMatrix P.1 := by rw [hev0_subst]
      _ = 1 := hP0
  let PsubGL : Matrix.GeneralLinearGroup s L[X][Y] := Matrix.GeneralLinearGroup.map substL P
  have hdetB_map : fXY B.det = 1 := by
    calc
      fXY B.det = (fXY.mapMatrix B).det := by simpa using (RingHom.map_det fXY B)
      _ = (substL.mapMatrix P.1).det := by rw [hBmap]
      _ = 1 := generalLinearGroup_det_eq_one_of_eval_zero_eq_one PsubGL hPsub0
  have hdetB : B.det = 1 := by
    apply hfXY_inj
    simpa using hdetB_map
  have hvxy1_subst : substL ∘ vxy1L = vxyL := by
    funext i
    have hcomp : substL.comp ιL = ιL := by
      ext a
      simp [substL, ιL, ccL]
    have hX : substL (C X + Y) = C X + ccL c * Y := by
      simp [substL, ccL]
    calc
      substL (vxy1L i) = Polynomial.eval₂ (substL.comp ιL) (substL (C X + Y)) (vL i) := by
        exact Polynomial.hom_eval₂ (vL i) ιL substL (C X + Y)
      _ = vxyL i := by
        rw [hcomp, hX]
  have hvxL_fixed : (fun i => substL (vxL i)) = vxL := by
    funext i
    simp [vxL, substL]
  have hPsubvxL_map :
      (substL.mapMatrix P.1).mulVec (fun i => substL (vxL i)) = fun i => substL (vxy1L i) := by
    funext i
    exact (RingHom.map_mulVec substL P.1 vxL i).symm.trans (congrArg substL (congrFun hPvxL i))
  have hPsubvxL : (substL.mapMatrix P.1).mulVec vxL = vxyL := by
    calc _ = (substL.mapMatrix P.1).mulVec (fun i => substL (vxL i)) := by rw [hvxL_fixed]
      _ = fun i => substL (vxy1L i) := hPsubvxL_map
      _ = vxyL := by
            funext i
            exact congrFun hvxy1_subst i
  have hvx_map (i : s) : fXY (vx i) = vxL i := by
    simp [vx, vxL, vL, fXY, fX]
  have hvxy_map (i : s) : fXY (vxy i) = vxyL i := by
    have hcomp : fXY.comp ιR = ιL.comp f := by
      ext r
      simp [fXY, fX, ιR, ιL]
    have hX : fXY (C X + ccR c * Y) = C X + ccL c * Y := by
      simp [fXY, fX, ccR, ccL]
    calc
      fXY (vxy i)
          = Polynomial.eval₂ (fXY.comp ιR) (fXY (C X + ccR c * Y)) (v i) := by
              exact Polynomial.hom_eval₂ (v i) ιR fXY (C X + ccR c * Y)
      _ = Polynomial.eval₂ (ιL.comp f) (C X + ccL c * Y) (v i) := by rw [hcomp, hX]
      _ = vxyL i := (Polynomial.eval₂_map f ιL (C X + ccL c * Y)).symm
  have hBvx_map : (fun i => fXY (B.mulVec vx i)) = fun i => fXY (vxy i) := by
    funext i
    calc
      fXY (B.mulVec vx i) = (fXY.mapMatrix B).mulVec (fun j => fXY (vx j)) i :=
        RingHom.map_mulVec fXY B vx i
      _ = (substL.mapMatrix P.1).mulVec vxL i := by
            simp [hBmap, hvx_map]
      _ = vxyL i := congrFun hPsubvxL i
      _ = fXY (vxy i) := (hvxy_map i).symm
  have hBvx : B.mulVec vx = vxy := by
    funext i
    apply hfXY_inj
    exact congrFun hBvx_map i
  refine ⟨c, ⟨Matrix.GeneralLinearGroup.mk'' B ?_, ?_⟩⟩
  · simp [hdetB]
  · funext i
    simpa [vx, vxy, ιR, ccR, Algebra.smul_def] using congrFun hBvx i

end lem10

section cor11

/-- Suppose $R$ is any ring, and $v(x) \in R[x]^s$ is a unimodular vector one of whose
  leading coefficients is one. Then $v(x) \sim v(0)$. -/
theorem cor11 (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  let base : s → R[X][Y] := fun i => C (v i)
  let shift : R → s → R[X][Y] := fun q i =>
    (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + q • Y)
  let I : Ideal R :=
    { carrier := {q | UnimodularVectorEquiv base (shift q)}
      zero_mem' := by
        let ψ : R[X] →+* R[X][Y] :=
          Polynomial.eval₂RingHom ((C : R[X] →+* R[X][Y]).comp C) (C X)
        have hψ : ψ = (C : R[X] →+* R[X][Y]) := by
          apply Polynomial.ringHom_ext
          · intro a
            simp [ψ]
          · simp [ψ]
        change UnimodularVectorEquiv base (shift 0)
        refine ⟨1, ?_⟩
        funext i
        simpa [base, shift, ψ] using (congrArg (fun f : R[X] →+* R[X][Y] => f (v i)) hψ).symm
      add_mem' := by
        intro a b ha hb
        let σ : R[X][Y] →+* R[X][Y] :=
          Polynomial.eval₂RingHom
            (Polynomial.eval₂RingHom ((C : R[X] →+* R[X][Y]).comp C) (C X + b • Y)) Y
        have hσ : UnimodularVectorEquiv
            (fun i => σ (base i))
            (fun i => σ (shift a i)) :=
          unimodularVectorEquiv_map σ ha
        have hσ_left : (fun i => σ (base i)) = shift b := by
          funext i
          simp [σ, base, shift]
        have hcomp : σ.comp ((C : R[X] →+* R[X][Y]).comp C) =
            ((C : R[X] →+* R[X][Y]).comp C) := by
          ext r
          simp [σ]
        have hX : σ (C X + a • Y) = C X + (a + b) • Y := by
          simp [σ, Algebra.smul_def, add_mul, add_comm, add_left_comm]
        have hσ_right : (fun i => σ (shift a i)) = shift (a + b) := by
          funext i
          calc
            σ (shift a i)
                = Polynomial.eval₂ (σ.comp ((C : R[X] →+* R[X][Y]).comp C))
                    (σ (C X + a • Y)) (v i) := by
                      exact Polynomial.hom_eval₂ (v i) ((C : R[X] →+* R[X][Y]).comp C) σ
                        (C X + a • Y)
            _ = shift (a + b) i := by rw [hcomp, hX]
        have hσ' : UnimodularVectorEquiv (shift b) (shift (a + b)) := by
          simpa [hσ_left, hσ_right] using hσ
        exact (unimodularVectorEquiv_equivalence.trans hb hσ')
      smul_mem' := by
        intro r q hq
        let τ : R[X][Y] →+* R[X][Y] :=
          Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) (C (C r) * Y)
        have hτ : UnimodularVectorEquiv
            (fun i => τ (base i))
            (fun i => τ (shift q i)) :=
          unimodularVectorEquiv_map τ hq
        have hτ_left : (fun i => τ (base i)) = base := by
          funext i
          simp [τ, base]
        have hcomp : τ.comp ((C : R[X] →+* R[X][Y]).comp C) =
            ((C : R[X] →+* R[X][Y]).comp C) := by
          ext a
          simp [τ]
        have hX : τ (C X + q • Y) = C X + (r * q) • Y := by
          change Polynomial.eval₂ (C : R[X] →+* R[X][Y]) (C (C r) * Y) (C X + q • Y) = _
          rw [Polynomial.eval₂_add, Polynomial.eval₂_C]
          rw [show Polynomial.eval₂ (C : R[X] →+* R[X][Y]) (C (C r) * Y) (q • Y)
                = Polynomial.eval₂ (C : R[X] →+* R[X][Y]) (C (C r) * Y) (C (C q) * Y) by
                  simp [Algebra.smul_def]]
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
          rw [show C (C q) * (C (C r) * Y) = (C (C q) * C (C r)) * Y by ring]
          rw [show C (C q) * C (C r) = C (C (q * r)) by simp]
          simp [Algebra.smul_def, mul_comm]
        have hτ_right : (fun i => τ (shift q i)) = shift (r * q) := by
          funext i
          calc
            τ (shift q i)
                = Polynomial.eval₂ (τ.comp ((C : R[X] →+* R[X][Y]).comp C))
                    (τ (C X + q • Y)) (v i) := by
                      exact Polynomial.hom_eval₂ (v i) ((C : R[X] →+* R[X][Y]).comp C) τ
                        (C X + q • Y)
            _ = shift (r * q) i := by rw [hcomp, hX]
        simpa [hτ_left, hτ_right] using hτ }
  have hI_top : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hmmax, hIm⟩ := Ideal.exists_le_maximal I hI
    let f : R →+* Localization m.primeCompl := algebraMap R (Localization m.primeCompl)
    let fX : R[X] →+* (Localization m.primeCompl)[X] := Polynomial.mapRingHom f
    haveI : IsLocalRing (Localization m.primeCompl) := by infer_instance
    have hv' : IsUnimodular (fun i => (v i).map f) :=
      isUnimodular_map_ringHom fX v hv
    have h' : ∃ i : s, ((v i).map f).Monic := by
      rcases h with ⟨i, hi⟩
      exact ⟨i, hi.map f⟩
    have hloc : UnimodularVectorEquiv
        (fun i => (v i).map (algebraMap R (Localization m.primeCompl)))
        (fun i => C (algebraMap R (Localization m.primeCompl) ((v i).eval 0))) := by
      have hloc0 : UnimodularVectorEquiv (fun i => (v i).map f)
          (fun i => C (((v i).map f).eval 0)) :=
        cor9 (R := Localization m.primeCompl) (s := s) (v := fun i => (v i).map f) hv' h'
      simpa [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_map, Polynomial.eval₂_at_apply, f]
        using hloc0
    have hs : m.primeCompl ≤ nonZeroDivisors R := by
      simpa using (Ideal.primeCompl_le_nonZeroDivisors (R := R) (P := m))
    obtain ⟨c, hc⟩ := lem10 (R := R) (s := s) (S := m.primeCompl) hs v hloc
    have hcI : (c : R) ∈ I := by
      simpa [I, base, shift] using hc
    exact c.2 (hIm hcI)
  have h1 : (1 : R) ∈ I := by
    rw [hI_top]
    simp
  let φ : R[X][Y] →+* R[X] := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (C : R →+* R[X]) 0) X
  have hφ : UnimodularVectorEquiv (fun i => φ (base i)) (fun i => φ (shift 1 i)) :=
    unimodularVectorEquiv_map φ h1
  have hφ_left : (fun i => φ (base i)) = fun i => C ((v i).eval 0) := by
    funext i
    simp [φ, base, Polynomial.coeff_zero_eq_eval_zero]
  have hcomp : φ.comp ((C : R[X] →+* R[X][Y]).comp C) = (C : R →+* R[X]) := by
    ext r
    simp [φ]
  have hX : φ (C X + (1 : R) • Y) = X := by
    simp [φ, Algebra.smul_def]
  have hφ_right : (fun i => φ (shift 1 i)) = v := by
    funext i
    calc
      φ (shift 1 i)
          = Polynomial.eval₂ (φ.comp ((C : R[X] →+* R[X][Y]).comp C))
              (φ (C X + (1 : R) • Y)) (v i) := by
                exact Polynomial.hom_eval₂ (v i) ((C : R[X] →+* R[X][Y]).comp C) φ
                  (C X + (1 : R) • Y)
      _ = v i := by rw [hcomp, hX, Polynomial.eval₂_C_X]
  exact (unimodularVectorEquiv_equivalence.symm (by simpa [hφ_left, hφ_right] using hφ))

end cor11
