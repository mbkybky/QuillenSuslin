import QuillenSuslin.Horrocks

open Module Polynomial Finset BigOperators

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]

open Bivariate in
set_option maxHeartbeats 20000000 in
/-- Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such
  that $v(x) \sim v(x + cy)$ over $R[x, y]$. -/
theorem lem10 [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
    (h : UnimodularVectorEquiv (fun i => (v i).map (algebraMap R (Localization S)))
      (fun i => C (algebraMap R (Localization S) ((v i).eval 0)))) :
    ∃ c : S, UnimodularVectorEquiv (R := R[X][Y]) (fun i => C (v i))
      (fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y)) := by
  classical
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let ι : R →+* Localization S := algebraMap R (Localization S)
  let vA : s → (Localization S)[X] := fun i => (v i).map ι
  let v0A : s → (Localization S)[X] := fun i => C (ι ((v i).eval 0))
  rcases h with ⟨M, hM⟩
  let CAY : (Localization S)[X] →+* (Localization S)[X][Y] :=
    (C : (Localization S)[X] →+* (Localization S)[X][Y])
  let φ : (Localization S)[X] →+* (Localization S)[X][Y] :=
    Polynomial.eval₂RingHom ((CAY.comp (C : Localization S →+* (Localization S)[X])))
      ((CAY (X : (Localization S)[X])) + (Y : (Localization S)[X][Y]))
  let Mx : Matrix.GeneralLinearGroup s (Localization S)[X][Y] :=
    (Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X]) (S := (Localization S)[X][Y]) CAY) M
  let Mxy : Matrix.GeneralLinearGroup s (Localization S)[X][Y] :=
    (Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X]) (S := (Localization S)[X][Y]) φ) M
  let N : Matrix.GeneralLinearGroup s (Localization S)[X][Y] := Mx⁻¹ * Mxy
  have hMx :
      (Mx : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i)) =
        fun i => CAY (v0A i) := by
    funext i
    have hMi : (M.1.mulVec vA) i = v0A i := congrArg (fun w => w i) hM
    have hMi' : CAY ((M.1.mulVec vA) i) = CAY (v0A i) := congrArg CAY hMi
    refine (RingHom.map_mulVec CAY M.1 vA i).symm.trans ?_
    simpa using hMi'
  have hMxy :
      (Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) =
        fun i => CAY (v0A i) := by
    funext i
    have hMi : (M.1.mulVec vA) i = v0A i := congrArg (fun w => w i) hM
    have hMi' : φ ((M.1.mulVec vA) i) = φ (v0A i) := congrArg φ hMi
    refine (RingHom.map_mulVec φ M.1 vA i).symm.trans ?_
    simpa [v0A, φ] using hMi'
  have hN :
      (N : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) =
        fun i => CAY (vA i) := by
    have hEq : (Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) =
        (Mx : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i)) := by
      calc
        (Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) =
            fun i => CAY (v0A i) := hMxy
        _ = (Mx : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i)) := hMx.symm
    have hEq' := congrArg (fun w => (Mx.2 : Matrix s s (Localization S)[X][Y]).mulVec w) hEq
    have hInvVal : (Mx.2 : Matrix s s (Localization S)[X][Y]) * (Mx.1 : Matrix s s _) = 1 := by
      simp
    have hRight :
        (Mx.2 : Matrix s s (Localization S)[X][Y]).mulVec
            ((Mx : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i))) =
          fun i => CAY (vA i) := by
      simp only [Units.inv_eq_val_inv, Matrix.coe_units_inv, Matrix.mulVec_mulVec,
        Matrix.isUnits_det_units, Matrix.nonsing_inv_mul, Matrix.one_mulVec]
    have hLeft :
        (Mx.2 : Matrix s s (Localization S)[X][Y]).mulVec
            ((Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i))) =
          (N : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) := by
      simp only [Units.inv_eq_val_inv, Matrix.coe_units_inv, Matrix.mulVec_mulVec, Units.val_mul, N]
    have hLeft' :
        (N : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) = fun i => CAY (vA i) := by
      have h' :
          (Mx.2 : Matrix s s (Localization S)[X][Y]).mulVec
              ((Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i))) =
            fun i => CAY (vA i) := hEq'.trans hRight
      calc
        (N : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i)) =
            (Mx.2 : Matrix s s (Localization S)[X][Y]).mulVec
              ((Mxy : Matrix s s (Localization S)[X][Y]).mulVec (fun i => φ (vA i))) := by
            simpa using hLeft.symm
        _ = fun i => CAY (vA i) := h'
    exact hLeft'
  have hNinv :
      (N.2 : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i)) =
        fun i => φ (vA i) := by
    have h' := congrArg (fun w => (N.2 : Matrix s s (Localization S)[X][Y]).mulVec w) hN
    dsimp at h'
    have hInvVal :
        (↑N⁻¹ : Matrix s s (Localization S)[X][Y]) * (↑N : Matrix s s (Localization S)[X][Y]) = 1 := by
      simp only [Matrix.coe_units_inv, Matrix.isUnits_det_units, Matrix.nonsing_inv_mul]
    rw [Matrix.mulVec_mulVec] at h'
    rw [hInvVal] at h'
    have h'' :
        (fun i => φ (vA i)) =
          (N.2 : Matrix s s (Localization S)[X][Y]).mulVec (fun i => CAY (vA i)) := by
      simpa [Matrix.one_mulVec] using h'
    exact h''.symm
  let Sx : Submonoid R[X] := S.map (C : R →+* R[X])
  let Sxy : Submonoid R[X][Y] := Sx.map (C : R[X] →+* R[X][Y])
  let fX : R[X] →+* (Localization S)[X] := Polynomial.mapRingHom ι
  letI : Algebra R[X] (Localization S)[X] := fX.toAlgebra
  haveI : IsLocalization Sx (Localization S)[X] := by
    simpa [Sx] using (Polynomial.isLocalization (R := R) S (Localization S))
  let fXY : R[X][Y] →+* (Localization S)[X][Y] :=
    Polynomial.mapRingHom (R := R[X]) (S := (Localization S)[X]) fX
  letI : Algebra R[X][Y] (Localization S)[X][Y] :=
    RingHom.toAlgebra (R := R[X][Y]) (S := (Localization S)[X][Y]) fXY
  haveI : IsLocalization Sxy (Localization S)[X][Y] := by
    simpa [Sxy] using (Polynomial.isLocalization (R := R[X]) Sx (Localization S)[X])
  have hsx : Sx ≤ nonZeroDivisors R[X] := by
    intro p hp
    rcases (Submonoid.mem_map).1 hp with ⟨c, hc, rfl⟩
    have hc0 : (c : R) ∈ nonZeroDivisors R := hs hc
    have hC0 : (C (c : R) : R[X]).coeff 0 ∈ nonZeroDivisors R := by simpa using hc0
    exact Polynomial.mem_nonzeroDivisors_of_coeff_mem (R := R) (p := C (c : R)) 0 hC0
  have hsxy : Sxy ≤ nonZeroDivisors R[X][Y] := by
    intro p hp
    rcases (Submonoid.mem_map).1 hp with ⟨q, hq, rfl⟩
    rcases (Submonoid.mem_map).1 hq with ⟨c, hc, rfl⟩
    have hC0 : (C (C (c : R)) : R[X][Y]).coeff 0 ∈ nonZeroDivisors R[X] := by
      have : (C (c : R) : R[X]) ∈ nonZeroDivisors R[X] := hsx <| by
        exact (Submonoid.mem_map).2 ⟨c, hc, rfl⟩
      simpa using this
    exact
      Polynomial.mem_nonzeroDivisors_of_coeff_mem (R := R[X]) (p := (C (C (c : R)) : R[X][Y])) 0
        hC0
  have hinj : Function.Injective (algebraMap R[X][Y] (Localization S)[X][Y]) :=
    IsLocalization.injective (R := R[X][Y]) (S := (Localization S)[X][Y]) (M := Sxy) hsxy
  let W : Matrix s s (Localization S)[X][Y] :=
    fun i j => ((N : Matrix s s (Localization S)[X][Y]) i j).divX
  let Winv : Matrix s s (Localization S)[X][Y] :=
    fun i j => ((N⁻¹ : Matrix s s (Localization S)[X][Y]) i j).divX
  let idx : Finset (s × s) := Finset.univ.product Finset.univ
  let F : Finset (Localization S)[X][Y] :=
    (idx.image fun ij => W ij.1 ij.2) ∪ idx.image fun ij => Winv ij.1 ij.2
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (R := R[X][Y]) (M := Sxy)
      (S := (Localization S)[X][Y]) F
  have hb' (a : (Localization S)[X][Y]) (ha : a ∈ F) :
      IsLocalization.IsInteger (R := R[X][Y]) ((b : R[X][Y]) • a) := hb a ha
  have hbW (i j : s) : IsLocalization.IsInteger (R := R[X][Y]) ((b : R[X][Y]) • W i j) := by
    refine hb' (W i j) ?_
    refine (Finset.mem_union.2 (Or.inl ?_))
    refine Finset.mem_image.2 ?_
    refine ⟨(i, j), ?_, rfl⟩
    exact Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ j⟩
  have hbWinv (i j : s) : IsLocalization.IsInteger (R := R[X][Y]) ((b : R[X][Y]) • Winv i j) := by
    refine hb' (Winv i j) ?_
    refine (Finset.mem_union.2 (Or.inr ?_))
    refine Finset.mem_image.2 ?_
    refine ⟨(i, j), ?_, rfl⟩
    exact Finset.mem_product.2 ⟨Finset.mem_univ i, Finset.mem_univ j⟩
  obtain ⟨c, hbC⟩ : ∃ c : S, (C (C (c : R)) : R[X][Y]) = (b : R[X][Y]) := by
    have hbmem : (b : R[X][Y]) ∈ Sxy := b.property
    rcases (Submonoid.mem_map).1 hbmem with ⟨q, hq, hbq⟩
    rcases (Submonoid.mem_map).1 hq with ⟨c, hc, hcq⟩
    refine ⟨⟨c, hc⟩, ?_⟩
    have hcq' : (C (C (c : R)) : R[X][Y]) = C q := by
      simpa using congrArg (fun p : R[X] => (C : R[X] →+* R[X][Y]) p) hcq
    exact hcq'.trans hbq
  refine ⟨c, ?_⟩
  let σR : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) ((c : R) • (Polynomial.X : R[X][Y]))
  let σA : (Localization S)[X][Y] →+* (Localization S)[X][Y] :=
    Polynomial.eval₂RingHom (C : (Localization S)[X] →+* (Localization S)[X][Y])
      ((ι (c : R)) • (Polynomial.X : (Localization S)[X][Y]))
  have hcomm :
      σA.comp (algebraMap R[X][Y] (Localization S)[X][Y]) =
        (algebraMap R[X][Y] (Localization S)[X][Y]).comp σR := by
    change σA.comp fXY = fXY.comp σR
    refine Polynomial.ringHom_ext (R := R[X]) (S := (Localization S)[X][Y]) ?_ ?_
    · intro p
      have hfXY_C : fXY (C p) = C (fX p) := by simp [fXY]
      have hσR_C : σR (C p) = C p := by
        dsimp [σR]
        simp only [eval₂_C]
      calc
        σA (fXY (C p)) = σA (C (fX p)) := by simp only [hfXY_C]
        _ = C (fX p) := by
          dsimp [σA]
          have hcoe :=
            congrArg (fun g => g (C (fX p)))
              (Polynomial.coe_eval₂RingHom
                (f := (C : (Localization S)[X] →+* (Localization S)[X][Y]))
                ((ι (c : R)) • (Polynomial.X : (Localization S)[X][Y])))
          -- `hcoe` rewrites `eval₂RingHom` into `eval₂`, so we can use `eval₂_C`.
          -- We keep this as a single step to avoid `simp` timeouts.
          simp only [eval₂_C]
        _ = fXY (C p) := hfXY_C.symm
        _ = fXY (σR (C p)) := by rw [hσR_C]
    · have hfXY_X :
          fXY (Polynomial.X : R[X][Y]) = (Polynomial.X : (Localization S)[X][Y]) := by simp [fXY]
      have hfXY_CC :
          fXY (C (C (c : R)) : R[X][Y]) = (C (C (ι (c : R))) : (Localization S)[X][Y]) := by
        simp [fXY, fX]
      have hσR_X : σR (Polynomial.X : R[X][Y]) = (c : R) • (Polynomial.X : R[X][Y]) := by
        dsimp [σR]
        simp only [eval₂_X]
      have hsmul_dom :
          (c : R) • (Polynomial.X : R[X][Y]) = (C (C (c : R)) : R[X][Y]) * Polynomial.X := by
        simp [Algebra.smul_def]
      have hsmul_cod :
          (ι (c : R)) • (Polynomial.X : (Localization S)[X][Y]) =
            (C (C (ι (c : R))) : (Localization S)[X][Y]) * Polynomial.X := by
        simp [Algebra.smul_def]
      calc
        σA (fXY (Polynomial.X : R[X][Y])) = σA (Polynomial.X : (Localization S)[X][Y]) := by
          simp only [hfXY_X]
        _ = (ι (c : R)) • (Polynomial.X : (Localization S)[X][Y]) := by
          dsimp [σA]
          simp only [eval₂_X]
        _ = (C (C (ι (c : R))) : (Localization S)[X][Y]) * Polynomial.X := by simp only [hsmul_cod]
        _ = fXY ((C (C (c : R)) : R[X][Y]) * Polynomial.X) := by
          simp [hfXY_CC, hfXY_X, map_mul]
        _ = fXY ((c : R) • (Polynomial.X : R[X][Y])) := by simp only [map_mul, hsmul_dom]
        _ = fXY (σR (Polynomial.X : R[X][Y])) := by simp only [hσR_X]
  have hσR_b : σR (b : R[X][Y]) = b := by
    rw [← hbC]
    simp only [coe_eval₂RingHom, eval₂_C, σR]
  have hσA_b :
      σA (algebraMap R[X][Y] (Localization S)[X][Y] (b : R[X][Y])) =
        algebraMap R[X][Y] (Localization S)[X][Y] (b : R[X][Y]) := by
    have := congrArg (fun f => f (b : R[X][Y])) hcomm
    simpa [hσR_b] using this
  have isInteger_map {x : (Localization S)[X][Y]} (hx : IsLocalization.IsInteger (R := R[X][Y]) x) :
      IsLocalization.IsInteger (R := R[X][Y]) (σA x) := by
    rcases hx with ⟨r, rfl⟩
    refine ⟨σR r, ?_⟩
    have := congrArg (fun f => f r) hcomm
    simpa using this.symm
  have hbW' (i j : s) :
      IsLocalization.IsInteger (R := R[X][Y]) ((b : R[X][Y]) • σA (W i j)) := by
    have hsmul :
        σA ((b : R[X][Y]) • W i j) = (b : R[X][Y]) • σA (W i j) := by
      simp [Algebra.smul_def, map_mul, hσA_b]
      sorry
    have h' : IsLocalization.IsInteger (R := R[X][Y]) (σA ((b : R[X][Y]) • W i j)) :=
      isInteger_map (hbW i j)
    simpa [hsmul] using h'
  have hbWinv' (i j : s) :
      IsLocalization.IsInteger (R := R[X][Y]) ((b : R[X][Y]) • σA (Winv i j)) := by
    have hsmul :
        σA ((b : R[X][Y]) • Winv i j) = (b : R[X][Y]) • σA (Winv i j) := by
      simp [Algebra.smul_def, map_mul, hσA_b]
      sorry
    have h' : IsLocalization.IsInteger (R := R[X][Y]) (σA ((b : R[X][Y]) • Winv i j)) :=
      isInteger_map (hbWinv i j)
    simpa [hsmul] using h'
  let Ncy : Matrix.GeneralLinearGroup s (Localization S)[X][Y] := Matrix.GeneralLinearGroup.map σA N
  let NcyInv : Matrix.GeneralLinearGroup s (Localization S)[X][Y] := Matrix.GeneralLinearGroup.map σA (N⁻¹)
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := Polynomial.eval₂RingHom (RingHom.id _) 0
  have hev0C : ev0.comp CAY = RingHom.id (Localization S)[X] := by
    refine Polynomial.ringHom_ext (R := Localization S) (S := (Localization S)[X])
      (fun a => by simp [ev0, CAY]) ?_
    simp [ev0, CAY]
  have hev0φ : ev0.comp φ = RingHom.id (Localization S)[X] := by
    refine Polynomial.ringHom_ext (R := Localization S) (S := (Localization S)[X])
      (fun a => by simp [ev0, φ, CAY]) ?_
    simp [ev0, φ, CAY, add_assoc, add_comm, add_left_comm]
  have hmap_ev0_Mx : Matrix.GeneralLinearGroup.map (n := s) ev0 Mx = M := by
    have hcomp :=
      congrArg (fun h => h M)
        (Matrix.GeneralLinearGroup.map_comp (n := s) (f := CAY) (g := ev0))
    have hcomp' :
        Matrix.GeneralLinearGroup.map (n := s) ev0 ((Matrix.GeneralLinearGroup.map (n := s) CAY) M) =
          Matrix.GeneralLinearGroup.map (n := s) (ev0.comp CAY) M := by
      simp [MonoidHom.comp_apply]
    calc
      Matrix.GeneralLinearGroup.map (n := s) ev0 Mx =
          Matrix.GeneralLinearGroup.map (n := s) ev0 ((Matrix.GeneralLinearGroup.map (n := s) CAY) M) := by
            simp [Mx]
      _ = Matrix.GeneralLinearGroup.map (n := s) (ev0.comp CAY) M := hcomp'
      _ = M := by rw [hev0C]; simp
  have hmap_ev0_Mxy : Matrix.GeneralLinearGroup.map (n := s) ev0 Mxy = M := by
    have hcomp :=
      congrArg (fun h => h M)
        (Matrix.GeneralLinearGroup.map_comp (n := s) (f := φ) (g := ev0))
    have hcomp' :
        Matrix.GeneralLinearGroup.map (n := s) ev0 ((Matrix.GeneralLinearGroup.map (n := s) φ) M) =
          Matrix.GeneralLinearGroup.map (n := s) (ev0.comp φ) M := by
      simp [MonoidHom.comp_apply]
    calc
      Matrix.GeneralLinearGroup.map (n := s) ev0 Mxy =
          Matrix.GeneralLinearGroup.map (n := s) ev0 ((Matrix.GeneralLinearGroup.map (n := s) φ) M) := by
            simp only [Mxy]
      _ = Matrix.GeneralLinearGroup.map (n := s) (ev0.comp φ) M := hcomp'
      _ = M := by rw [hev0φ]; simp
  have hN0g : Matrix.GeneralLinearGroup.map (n := s) ev0 N = 1 := by
    simp only [map_mul, map_inv, hmap_ev0_Mx, hmap_ev0_Mxy, inv_mul_cancel, N]
  have hN0m : (Matrix.GeneralLinearGroup.map (n := s) ev0 N : Matrix s s (Localization S)[X]) = 1 := by
    simpa using
      congrArg
        (fun g : Matrix.GeneralLinearGroup s (Localization S)[X] =>
          (g : Matrix s s (Localization S)[X]))
        hN0g
  have hcoeff0N :
      ∀ i j : s,
        ((N : Matrix s s (Localization S)[X][Y]) i j).coeff 0 = if i = j then 1 else 0 := by
    intro i j
    have hij :
        ev0 ((N : Matrix s s (Localization S)[X][Y]) i j) =
          (1 : Matrix s s (Localization S)[X]) i j := by
      simpa using congrArg (fun M => M i j) hN0m
    simpa [ev0, Polynomial.coeff_zero_eq_eval_zero, Matrix.one_apply] using hij
  have hN_entry (i j : s) :
      (N : Matrix s s (Localization S)[X][Y]) i j = Y * W i j + C (if i = j then 1 else 0) := by
    have h := (Polynomial.X_mul_divX_add (p := (N : Matrix s s (Localization S)[X][Y]) i j))
    simpa [W, hcoeff0N i j, add_comm, add_left_comm, add_assoc] using h.symm
  have hcoeff0Ninv :
      ∀ i j : s,
        ((N⁻¹ : Matrix s s (Localization S)[X][Y]) i j).coeff 0 = if i = j then 1 else 0 := by
    have hNinv0g : Matrix.GeneralLinearGroup.map (n := s) ev0 (N⁻¹) = 1 := by
      simp only [map_inv, hN0g, inv_one]
    have hNinv0m :
        (Matrix.GeneralLinearGroup.map (n := s) ev0 (N⁻¹) : Matrix s s (Localization S)[X]) = 1 := by
      simpa using
        congrArg
          (fun g : Matrix.GeneralLinearGroup s (Localization S)[X] =>
            (g : Matrix s s (Localization S)[X]))
          hNinv0g
    intro i j
    have hij :
        ev0 ((N⁻¹ : Matrix s s (Localization S)[X][Y]) i j) =
          (1 : Matrix s s (Localization S)[X]) i j := by
      sorry
    simpa [ev0, Polynomial.coeff_zero_eq_eval_zero, Matrix.one_apply] using hij
  have hNinv_entry (i j : s) :
      (N⁻¹ : Matrix s s (Localization S)[X][Y]) i j = Y * Winv i j + C (if i = j then 1 else 0) := by
    have h := (Polynomial.X_mul_divX_add (p := (N⁻¹ : Matrix s s (Localization S)[X][Y]) i j))
    simpa only [MonoidWithZeroHom.map_ite_one_zero, add_comm, hcoeff0Ninv i j] using h.symm
  have hNcyInt (i j : s) :
      IsLocalization.IsInteger (R := R[X][Y]) ((Ncy : Matrix s s (Localization S)[X][Y]) i j) := by
    sorry
  have hNcyInvInt (i j : s) :
      IsLocalization.IsInteger (R := R[X][Y]) ((NcyInv : Matrix s s (Localization S)[X][Y]) i j) := by
    sorry
  let N0 : Matrix s s R[X][Y] := fun i j => (hNcyInt i j).choose
  have hN0 (i j : s) :
      algebraMap R[X][Y] (Localization S)[X][Y] (N0 i j) =
        (Ncy : Matrix s s (Localization S)[X][Y]) i j :=
    (hNcyInt i j).choose_spec
  let N0inv : Matrix s s R[X][Y] := fun i j => (hNcyInvInt i j).choose
  have hN0inv (i j : s) :
      algebraMap R[X][Y] (Localization S)[X][Y] (N0inv i j) =
        (NcyInv : Matrix s s (Localization S)[X][Y]) i j :=
    (hNcyInvInt i j).choose_spec
  have hinjMat :
      Function.Injective fun M : Matrix s s R[X][Y] =>
        (algebraMap R[X][Y] (Localization S)[X][Y]).mapMatrix M := by
    sorry
  have hN0mat :
      (algebraMap R[X][Y] (Localization S)[X][Y]).mapMatrix N0 = (Ncy : Matrix s s (Localization S)[X][Y]) := by
    ext i j
    sorry
  have hN0invmat :
      (algebraMap R[X][Y] (Localization S)[X][Y]).mapMatrix N0inv =
        (NcyInv : Matrix s s (Localization S)[X][Y]) := by
    ext i j
    sorry
  have hNcy_mul : Ncy * NcyInv = 1 := by simp [Ncy, NcyInv]
  have hNcyInv_mul : NcyInv * Ncy = 1 := by simp [Ncy, NcyInv]
  have hNcy_mul_mat :
      (Ncy : Matrix s s (Localization S)[X][Y]) * (NcyInv : Matrix s s (Localization S)[X][Y]) = 1 := by
    simpa using
      congrArg
        (fun g : Matrix.GeneralLinearGroup s (Localization S)[X][Y] =>
          (g : Matrix s s (Localization S)[X][Y]))
        hNcy_mul
  have hNcyInv_mul_mat :
      (NcyInv : Matrix s s (Localization S)[X][Y]) * (Ncy : Matrix s s (Localization S)[X][Y]) = 1 := by
    simpa using
      congrArg
        (fun g : Matrix.GeneralLinearGroup s (Localization S)[X][Y] =>
          (g : Matrix s s (Localization S)[X][Y]))
        hNcyInv_mul
  have hN0_mul : N0 * N0inv = 1 := by
    refine hinjMat ?_
    sorry
  have hN0inv_mul : N0inv * N0 = 1 := by
    refine hinjMat ?_
    sorry
  let U : Matrix.GeneralLinearGroup s R[X][Y] := ⟨N0, N0inv, hN0_mul, hN0inv_mul⟩
  have hmulVec :
      (U⁻¹ : Matrix s s R[X][Y]).mulVec (fun i => C (v i)) =
        fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y) := by
    sorry
  refine ⟨U⁻¹, ?_⟩
  sorry

/-
\begin{definition}
	Let $A$ be any ring. A vector ${v} \in A^s$ is unimodular if its components generate the unit ideal in $A$. For two unimodular vectors ${v}, {w}$, we write
	$$\displaystyle {v} \sim {w}$$
	if there is a matrix $M \in \mathrm{GL}_s(A)$ such that $M {v} = {w}$. This is clearly an equivalence relation.
\end{definition}

\begin{proposition}\label{prop:6}
	Over a principal ideal domain $R$, any two unimodular vectors are equivalent.
\end{proposition}

\begin{theorem}[Horrocks]\label{thm:8}
	Let $A = R[x]$ for $(R, \mathfrak{m})$ a local ring. Then any unimodular vector in $A^s$ one of whose elements has leading coefficient one is equivalent to $e_1$.
\end{theorem}

\begin{corollary}\label{cor:9}
	If $R$ is local and $v(x) \in R[x]^s$ is a unimodular vector one of whose elements is monic, then $v(x) \sim v(0)$.
\end{corollary}

\begin{lemma}\label{lem:10}
	Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such that $v(x) \sim v(x + cy)$ over $R[x, y]$.
\end{lemma}

\begin{proof}
	As before, we can choose a matrix $M(x) \in \mathrm{GL}_s(R_S[x])$ such that $M(x) v(x) = v(0)$, and then the matrix $N(x,y) := M(x)^{-1}M(x+y)$ has the property that
	\[ \displaystyle N(x,y) v(x+y) = v(x). \]
	It follows that if we substitute $cy$ for $y$, then we have
	\[ \displaystyle N(x,cy) v(x+cy) = v(x). \]
	The claim is that we can choose $c \in S$ such that $N(x,cy)$ actually has $R$-coefficients. In fact, this is because $N(x, 0) = I$, which implies that $N(x,y) = I + y W$ for some matrix $W$ with values in $R_S[x,y]$. If we replace $y$ with $cy$ for $c$ an element of $S$, then we can clear the denominators in $W$ and arrange it so that $N(x,cy) \in R[x, y]$.
\end{proof}
-/
