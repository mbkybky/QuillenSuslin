import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (M : GL s (Localization S)[X])
  (hM : (M.1.mulVec fun i ↦ map (algebraMap R (Localization S)) (v i)) =
    fun i ↦ C ((algebraMap R (Localization S)) (eval 0 (v i))))
  {c : S} (hc : ∀ i j : s, IsLocalization.IsInteger R[X][Y]
    ((C (C (c : R)) : R[X][Y]) • σA c ((W (S := S) (M := M)) i j)))

noncomputable section

include hs

lemma N_entry_decomp (M : GL s (Localization S)[X]) (i j : s) :
    (N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j =
      X * (W (S := S) (M := M) i j) + C (if i = j then 1 else 0) := by
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := eval₂RingHom (RingHom.id _) 0
  let map0 :
      GL s (Localization S)[X][Y] →* GL s (Localization S)[X] :=
    Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y]) (S := (Localization S)[X]) ev0
  have hMx0 : map0 (Mx (S := S) (M := M)) = M := by
    ext i j
    simp [map0, Mx, ev0, CAY]
  have hev0φ : ev0.comp (φ (S := S)) = RingHom.id (Localization S)[X] := by
    refine ringHom_ext (fun a => ?_) ?_
    · simp [ev0, φ, CAY]
    · simp [ev0, φ, CAY]
  have hφ0 (p : (Localization S)[X]) : ev0 (φ (S := S) p) = p := by
    have := congrArg (fun f => f p) hev0φ
    simpa [RingHom.comp_apply] using this
  have hMxy0 : map0 (Mxy (S := S) (M := M)) = M := by
    ext i j
    simp [map0, Mxy, Matrix.GeneralLinearGroup.map_apply, hφ0]
  have hN0 : map0 (N (S := S) (M := M)) = 1 := by
    simp [map0, N, hMx0, hMxy0]
  have hcoeff0N :
      ((N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j).coeff 0 =
        (if i = j then 1 else 0) := by
    have hmat :=
      congrArg (fun g : GL s (Localization S)[X] => (g : Matrix s s (Localization S)[X])) hN0
    have hij := congrArg (fun A : Matrix s s (Localization S)[X] => A i j) hmat
    have hij' :
        ev0 ((N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j) =
          (if i = j then 1 else 0) := by
      simpa [map0, Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply] using hij
    simpa [ev0, coeff_zero_eq_eval_zero] using hij'
  have h :=
    (X_mul_divX_add (p :=
      (N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j))
  simpa [W, hcoeff0N, add_comm] using h.symm

lemma ncy_isInteger_eq (i j : s) (w : R[X][Y])
    (hw : (algebraMap R[X][Y] (Localization S)[X][Y]) w =
      (C (C (c : R)) : R[X][Y]) • σA c ((W (S := S) (M := M)) i j)) :
    algebraMap R[X][Y] (Localization S)[X][Y] (X * w + C (if i = j then 1 else 0 : R[X])) =
      (Ncy c M).1 i j := by
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let b : R[X][Y] := C (C (c : R))
  have hN_entry := N_entry_decomp (hs := hs) (S := S) (M := M) i j
  let ι : R →+* Localization S := algebraMap R (Localization S)
  have hCι : mapRingHom ι (C (c : R)) = C (ι (c : R)) := by
    have h :=
      congrArg (fun g : R →+* (Localization S)[X] => g (c : R))
        (mapRingHom_comp_C (f := ι))
    dsimp at h
    rw [← RingHom.comp_apply]
    exact h
  have hbMap :
      algebraMap R[X][Y] (Localization S)[X][Y] b =
        (C (C (ι (c : R))) : (Localization S)[X][Y]) := by
    simp [b, ι, map_C, hCι]
  have hσA_X :
      σA c (X : (Localization S)[X][Y]) =
        algebraMap R[X][Y] (Localization S)[X][Y] b * X := by
    have hσA_X0 : σA c (X : (Localization S)[X][Y]) = (ι (c : R)) • (X : (Localization S)[X][Y]) := by
      dsimp [σA, ι]
      show
        eval₂ (C : (Localization S)[X] →+* (Localization S)[X][Y])
            (((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y]))
            (X : (Localization S)[X][Y]) =
          ((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y])
      exact
        eval₂_X (f := (C : (Localization S)[X] →+* (Localization S)[X][Y]))
          (x := (((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y])))
    calc
      σA c (X : (Localization S)[X][Y]) = (ι (c : R)) • (X : (Localization S)[X][Y]) := hσA_X0
      _ = (C (C (ι (c : R))) : (Localization S)[X][Y]) * X := by simp [Algebra.smul_def]
      _ = algebraMap R[X][Y] (Localization S)[X][Y] b * X := by
        exact congrArg (fun t => t * X) hbMap.symm
  have hNcyij :
      ((Ncy c M : GL s (Localization S)[X][Y]).1 i j) =
        σA c ((N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j) := by
    simp [Ncy, Matrix.GeneralLinearGroup.map_apply]
  have hmap :
      algebraMap R[X][Y] (Localization S)[X][Y] (X * w + C (if i = j then 1 else 0 : R[X])) =
        X * algebraMap R[X][Y] (Localization S)[X][Y] w + C (if i = j then 1 else 0) := by
    let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
    show f (X * w + C (if i = j then 1 else 0 : R[X])) = X * f w + C (if i = j then 1 else 0 : (Localization S)[X])
    have hadd : f (X * w + C (if i = j then 1 else 0 : R[X])) = f (X * w) + f (C (if i = j then 1 else 0 : R[X])) := by
      exact f.map_add (X * w) (C (if i = j then 1 else 0 : R[X]))
    have hmul : f (X * w) = f X * f w := by exact f.map_mul X w
    have hC : f (C (if i = j then 1 else 0 : R[X])) = C (if i = j then 1 else 0 : (Localization S)[X]) := by
      simp [f]
    have hX : f X = X := by simp [f]
    rw [hadd, hmul, hC, hX]
  rw [hmap, hw]
  rw [hNcyij, hN_entry]
  rw [(σA c).map_add (X * W (S := S) (M := M) i j) (C (if i = j then 1 else 0 : (Localization S)[X]))]
  rw [(σA c).map_mul X (W (S := S) (M := M) i j)]
  have hσA_C :
      σA c (C (if i = j then 1 else 0 : (Localization S)[X])) =
        C (if i = j then 1 else 0 : (Localization S)[X]) := by
    unfold σA
    show
        eval₂ (C : (Localization S)[X] →+* (Localization S)[X][Y])
            (((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y]))
            (C (if i = j then 1 else 0 : (Localization S)[X])) =
          C (if i = j then 1 else 0 : (Localization S)[X])
    rw [eval₂_C]
  rw [hσA_X, hbMap, hσA_C]
  rw [Algebra.smul_def]
  have hbMapC :
      algebraMap R[X][Y] (Localization S)[X][Y] (C (C (c : R))) = C (C (ι (c : R))) := by
    simpa [b] using hbMap
  rw [hbMapC]
  have hmul :
      Y * (C (C (ι (c : R))) * (σA c) (W (S := S) (M := M) i j)) =
        C (C (ι (c : R))) * (Y * (σA c) (W (S := S) (M := M) i j)) := by
    calc
      Y * (C (C (ι (c : R))) * (σA c) (W (S := S) (M := M) i j)) =
          (Y * C (C (ι (c : R)))) * (σA c) (W (S := S) (M := M) i j) := by
            rw [← mul_assoc]
      _ = (C (C (ι (c : R))) * Y) * (σA c) (W (S := S) (M := M) i j) := by
            rw [mul_comm Y (C (C (ι (c : R))))]
      _ = C (C (ι (c : R))) * (Y * (σA c) (W (S := S) (M := M) i j)) := by
            rw [mul_assoc]
  simp [hmul, mul_assoc]

lemma det_N_eq_one (M : GL s (Localization S)[X]) :
    Matrix.det ((N (S := S) (M := M)).1) = 1 := by
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization (M := S) hs
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := eval₂RingHom (RingHom.id _) 0
  have hev0_X : ev0 X = 0 := by simp [ev0]
  have hN0mat : ev0.mapMatrix ((N (S := S) (M := M)).1) = 1 := by
    apply Matrix.ext
    intro i j
    have hNij := N_entry_decomp (hs := hs) (S := S) (M := M) i j
    rw [Matrix.one_apply]
    rw [RingHom.mapMatrix_apply]
    rw [Matrix.map_apply]
    rw [hNij]
    rw [ev0.map_add, ev0.map_mul, hev0_X]
    simp [ev0]
  have hdet_ev0 : ev0 (Matrix.det ((N (S := S) (M := M)).1)) = 1 := by
    calc
      ev0 (Matrix.det ((N (S := S) (M := M)).1)) =
          Matrix.det (ev0.mapMatrix ((N (S := S) (M := M)).1)) := by
        simpa using (RingHom.map_det ev0 ((N (S := S) (M := M)).1))
      _ = 1 := by simp [hN0mat]
  have hdet_isUnit : IsUnit (Matrix.det ((N (S := S) (M := M)).1)) := by
    simp
  let p : (Localization S)[X][Y] := Matrix.det ((N (S := S) (M := M)).1)
  have hp_isUnit : IsUnit p := by simp [p]
  have hp0_unit : IsUnit (p.coeff 0) ∧ ∀ n : ℕ, n ≠ 0 → IsNilpotent (p.coeff n) :=
    (isUnit_iff_coeff_isUnit_isNilpotent (P := p)).1 hp_isUnit
  haveI : IsDomain (Localization S)[X] := by infer_instance
  haveI : IsReduced (Localization S)[X] := by infer_instance
  have hp_coeff : ∀ n : ℕ, n ≠ 0 → p.coeff n = 0 := by
    intro n hn
    exact (hp0_unit.2 n hn).eq_zero
  have hpC : C (p.coeff 0) = p := by
    apply Polynomial.ext
    intro n
    by_cases hn : n = 0
    · subst hn; simp
    · simp [coeff_C, hn, hp_coeff n hn]
  have hp0 : p.coeff 0 = 1 := by
    have : ev0 p = 1 := by simpa [p] using hdet_ev0
    simpa [ev0, eval₂_at_zero] using this
  have : p = 1 := by
    calc
      p = C (p.coeff 0) := by simp [hpC]
      _ = C (1 : (Localization S)[X]) := by simp [hp0]
      _ = 1 := by simp
  simpa [p] using this

lemma det_Ncy_eq_one (c : S) (M : GL s (Localization S)[X]) :
    Matrix.det ((Ncy c M).1) = 1 := by
  have hdetN : Matrix.det ((N (S := S) (M := M)).1) = 1 := det_N_eq_one (hs := hs) (S := S) M
  have hdetVal :
      Matrix.det ((Ncy c M).1) = σA c (Matrix.det ((N (S := S) (M := M)).1)) := by
    have h := RingHom.map_det (σA c) ((N (S := S) (M := M)).1)
    have hNcy :
        (σA c).mapMatrix (N (S := S) (M := M)).1 = (Ncy c M).1 := by
      ext i j
      simp [Ncy, Matrix.GeneralLinearGroup.map_apply]
    simpa [hNcy] using h.symm
  rw [hdetVal, hdetN]
  simp

lemma inv_Ncy_val_eq_adjugate (c : S) (M : GL s (Localization S)[X]) :
    ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 = ((Ncy c M).1).adjugate := by
  have hdetNcy : Matrix.det ((Ncy c M).1) = 1 := det_Ncy_eq_one (hs := hs) (S := S) c M
  let A : Matrix s s (Localization S)[X][Y] := (Ncy c M).1
  have hA_mul_adj : A * A.adjugate = 1 := by
    have h : A * A.adjugate = A.det • (1 : Matrix s s (Localization S)[X][Y]) := Matrix.mul_adjugate A
    have hdet : A.det = 1 := by simpa [A] using hdetNcy
    have hone : (1 : (Localization S)[X][Y]) • (1 : Matrix s s (Localization S)[X][Y]) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    simpa [hdet, hone] using h
  have hInvMul : ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 * A = 1 := by
    have := congrArg (fun g : GL s (Localization S)[X][Y] => (g : Matrix s s (Localization S)[X][Y]))
      (inv_mul_cancel (Ncy c M))
    dsimp [A]
    exact this
  have := congrArg (fun B => ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 * B) hA_mul_adj
  simpa [mul_assoc, hInvMul, A] using this.symm

include hc

theorem ncy_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) := by
  rcases hc i j with ⟨w, hw⟩
  refine ⟨X * w + C (if i = j then 1 else 0 : R[X]), ?_⟩
  exact ncy_isInteger_eq (hs := hs) (S := S) (c := c) (M := M) (i := i) (j := j) w hw

theorem ncyInv_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((NcyInv c M).1 i j) := by
  let A : Matrix s s (Localization S)[X][Y] := (Ncy c M).1
  have hInv_eq_adj : ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 = A.adjugate := by
    dsimp [A]
    exact inv_Ncy_val_eq_adjugate (hs := hs) (S := S) c M
  have hNcyInv : (NcyInv c M) = (Ncy c M)⁻¹ := by
    show
        Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y]) (S := (Localization S)[X][Y])
            (σA c) (N (S := S) (M := M))⁻¹ =
          (Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y]) (S := (Localization S)[X][Y])
              (σA c) (N (S := S) (M := M)))⁻¹
    exact Matrix.GeneralLinearGroup.map_inv (f := σA c) (g := N (S := S) (M := M))
  have hA0_entry (i j : s) :
      IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) := by
    exact ncy_isInteger (hs := hs) (c := c) (M := M) (hc := hc) i j
  let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
  let A0 : Matrix s s R[X][Y] := fun i j => (hA0_entry i j).choose
  have hA0 : f.mapMatrix A0 = A := by
    apply Matrix.ext
    intro i j
    dsimp [f, A0, A]
    exact (hA0_entry i j).choose_spec
  refine ⟨(A0.adjugate) i j, ?_⟩
  have hAdj : f.mapMatrix A0.adjugate = A.adjugate := by simpa [hA0] using f.map_adjugate A0
  rw [hNcyInv]
  rw [hInv_eq_adj]
  have hij := congrArg (fun B : Matrix s s (Localization S)[X][Y] => B i j) hAdj
  simpa [f] using hij

def N0 : Matrix s s R[X][Y] := fun i j => (ncy_isInteger hs M hc i j).choose

def N0Inv : Matrix s s R[X][Y] := fun i j => (ncyInv_isInteger hs M hc i j).choose

theorem hN0_mul : N0 hs M hc * N0Inv hs M hc = 1 := by
  sorry

theorem hN0inv_mul : N0Inv hs M hc * N0 hs M hc = 1 := by
  sorry

def U : Matrix.GeneralLinearGroup s R[X][Y] :=
  ⟨N0 hs M hc, N0Inv hs M hc, hN0_mul hs M hc , hN0inv_mul hs M hc⟩

theorem hU : ((U hs M hc)⁻¹ : Matrix s s R[X][Y]).mulVec (fun i => C (v i)) =
    fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y) := by
  sorry
