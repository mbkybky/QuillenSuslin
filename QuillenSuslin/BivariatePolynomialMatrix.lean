import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (M : GL s (Localization S)[X])
  (hM : (M.1.mulVec fun i ↦ map (algebraMap R (Localization S)) (v i)) =
    fun i ↦ C ((algebraMap R (Localization S)) (eval 0 (v i))))
  {c : S} (hc : ∀ i j : s, IsLocalization.IsInteger R[X][Y]
    ((C (C (c : R)) : R[X][Y]) • σA c ((W M) i j)))

noncomputable section

include hs

lemma N_entry_decomp (M : GL s (Localization S)[X]) (i j : s) :
    (N M).1 i j = X * (W M i j) + C (if i = j then 1 else 0) := by
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := eval₂RingHom (RingHom.id _) 0
  let map0 : GL s (Localization S)[X][Y] →* GL s (Localization S)[X] :=
    Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y])
      (S := (Localization S)[X]) ev0
  have hMx0 : map0 (Mx (S := S) (M := M)) = M := by
    ext i j
    simp [map0, Mx, ev0, CAY]
  have hev0φ : ev0.comp (φ (S := S)) = RingHom.id (Localization S)[X] := by
    refine ringHom_ext (fun a => ?_) ?_
    · simp [ev0, φ, CAY]
    · simp [ev0, φ, CAY]
  have hφ0 (p : (Localization S)[X]) : ev0 (φ (S := S) p) = p := by
    simpa [RingHom.comp_apply] using congrArg (fun f => f p) hev0φ
  have hMxy0 : map0 (Mxy (S := S) (M := M)) = M := by
    ext i j
    simp [map0, Mxy, Matrix.GeneralLinearGroup.map_apply, hφ0]
  have hN0 : map0 (N M) = 1 := by
    simp [map0, N, hMx0, hMxy0]
  have hcoeff0N : ((N M).1 i j).coeff 0 =
      (if i = j then 1 else 0) := by
    have hij := congrArg (fun A : Matrix s s (Localization S)[X] => A i j) <|
      congrArg (fun g : GL s (Localization S)[X] => (g : Matrix s s (Localization S)[X])) hN0
    have hij' : ev0 ((N M).1 i j) = (if i = j then 1 else 0) := by
      simpa [map0, Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply] using hij
    simpa [ev0, coeff_zero_eq_eval_zero] using hij'
  simpa [W, hcoeff0N, add_comm] using ( X_mul_divX_add ((N M) i j)).symm

lemma ncy_isInteger_eq (i j : s) (w : R[X][Y]) (hw : (algebraMap R[X][Y] (Localization S)[X][Y]) w =
    (C (C (c : R)) : R[X][Y]) • σA c ((W M) i j)) :
    algebraMap R[X][Y] (Localization S)[X][Y] (X * w + C (if i = j then 1 else 0 : R[X])) =
      (Ncy c M).1 i j := by
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let b : R[X][Y] := C (C (c : R))
  have hN_entry := N_entry_decomp (hs := hs) (S := S) (M := M) i j
  let ι : R →+* Localization S := algebraMap R (Localization S)
  have hCι : mapRingHom ι (C (c : R)) = C (ι (c : R)) := by
    rw [← RingHom.comp_apply]
    exact congrArg (fun g : R →+* (Localization S)[X] => g (c : R)) (mapRingHom_comp_C (f := ι))
  have hbMap : algebraMap R[X][Y] (Localization S)[X][Y] b = (C (C (ι (c : R)))) := by
    simp [b, ι, map_C, hCι]
  have hσA_X : σA c Y = algebraMap R[X][Y] (Localization S)[X][Y] b * X := by
    have hσA_X0 : σA c Y = (ι (c : R)) • Y := by
      dsimp [σA, ι]
      exact eval₂_X _ ((algebraMap R (Localization S) (c : R)) • Y)
    calc _ = (ι (c : R)) • Y := hσA_X0
      _ = (C (C (ι (c : R)))) * X := by simp [Algebra.smul_def]
      _ = algebraMap R[X][Y] (Localization S)[X][Y] b * X := congrArg (fun t => t * X) hbMap.symm
  have hNcyij : ((Ncy c M).1 i j) = σA c ((N M : Matrix s s (Localization S)[X][Y]) i j) := by
    simp only [Ncy, Matrix.GeneralLinearGroup.map_apply]
  have hmap : algebraMap R[X][Y] (Localization S)[X][Y] (X * w + C (if i = j then 1 else 0 : R[X]))
      = X * algebraMap R[X][Y] (Localization S)[X][Y] w + C (if i = j then 1 else 0) := by
    let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
    have hadd : f (X * w + C (if i = j then 1 else 0 : R[X])) =
        f (X * w) + f (C (if i = j then 1 else 0 : R[X])) :=
      f.map_add (X * w) (C (if i = j then 1 else 0 : R[X]))
    have hmul : f (X * w) = f X * f w := f.map_mul X w
    have hC : f (C (if i = j then 1 else 0 : R[X])) =
        C (if i = j then 1 else 0 : (Localization S)[X]) := by simp [f]
    have hX : f X = X := by simp [f]
    rw [hadd, hmul, hC, hX]
  rw [hmap, hw, hNcyij, hN_entry]
  rw [(σA c).map_add (X * W M i j) (C (if i = j then 1 else 0 : (Localization S)[X]))]
  rw [(σA c).map_mul X (W M i j)]
  have hσA_C : σA c (C (if i = j then 1 else 0 : (Localization S)[X])) =
      C (if i = j then 1 else 0 : (Localization S)[X]) := by
    show eval₂ C _ _ = _
    rw [eval₂_C]
  rw [hσA_X, hbMap, hσA_C, Algebra.smul_def]
  have hbMapC : algebraMap R[X][Y] (Localization S)[X][Y] (C (C (c : R))) = C (C (ι (c : R))) := by
    simpa [b] using hbMap
  rw [hbMapC]
  have hmul : Y * (C (C (ι (c : R))) * (σA c) (W M i j)) =
      C (C (ι (c : R))) * (Y * (σA c) (W M i j)) := by
    calc _ = (Y * C (C (ι (c : R)))) * (σA c) (W M i j) := by rw [← mul_assoc]
      _ = (C (C (ι (c : R))) * Y) * (σA c) (W M i j) := by rw [mul_comm Y (C (C (ι (c : R))))]
      _ = C (C (ι (c : R))) * (Y * (σA c) (W M i j)) := by rw [mul_assoc]
  simp [hmul, mul_assoc]

lemma det_N_eq_one (M : GL s (Localization S)[X]) :
    Matrix.det ((N M).1) = 1 := by
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization (M := S) hs
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := eval₂RingHom (RingHom.id _) 0
  have hev0_X : ev0 X = 0 := by simp [ev0]
  have hN0mat : ev0.mapMatrix ((N M).1) = 1 := by
    apply Matrix.ext
    intro i j
    rw [Matrix.one_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [N_entry_decomp hs M i j, ev0.map_add, ev0.map_mul, hev0_X]
    simp [ev0]
  have hdet_ev0 : ev0 (Matrix.det ((N M).1)) = 1 := by
    calc _ = Matrix.det (ev0.mapMatrix ((N M).1)) := by simpa using (RingHom.map_det ev0 ((N M).1))
      _ = 1 := by simp [hN0mat]
  have hdet_isUnit : IsUnit (Matrix.det ((N M).1)) := by simp
  let p : (Localization S)[X][Y] := Matrix.det ((N M).1)
  have hp_isUnit : IsUnit p := by simp [p]
  have hp0_unit : IsUnit (p.coeff 0) ∧ ∀ n : ℕ, n ≠ 0 → IsNilpotent (p.coeff n) :=
    (isUnit_iff_coeff_isUnit_isNilpotent (P := p)).1 hp_isUnit
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
    calc p = C (p.coeff 0) := by simp [hpC]
      _ = C (1 : (Localization S)[X]) := by simp [hp0]
      _ = 1 := by simp
  simpa [p] using this

lemma det_Ncy_eq_one (c : S) (M : GL s (Localization S)[X]) :
    Matrix.det ((Ncy c M).1) = 1 := by
  have hdetN : Matrix.det ((N M).1) = 1 := det_N_eq_one (hs := hs) (S := S) M
  have hdetVal : Matrix.det ((Ncy c M).1) = σA c (Matrix.det ((N M).1)) := by
    have h := RingHom.map_det (σA c) ((N M).1)
    have hNcy : (σA c).mapMatrix (N M).1 = (Ncy c M).1 := by
      ext i j
      simp [Ncy, Matrix.GeneralLinearGroup.map_apply]
    simpa [hNcy] using h.symm
  rw [hdetVal, hdetN]
  simp

lemma inv_Ncy_val_eq_adjugate (c : S) (M : GL s (Localization S)[X]) :
    ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 = ((Ncy c M).1).adjugate := by
  have hdetNcy : Matrix.det ((Ncy c M).1) = 1 := det_Ncy_eq_one hs c M
  let A : Matrix s s (Localization S)[X][Y] := (Ncy c M).1
  have hA_mul_adj : A * A.adjugate = 1 := by
    have h : A * A.adjugate = A.det • (1 : Matrix s s (Localization S)[X][Y]) :=
      Matrix.mul_adjugate A
    have hdet : A.det = 1 := by simpa [A] using hdetNcy
    have hone : (1 : (Localization S)[X][Y]) • (1 : Matrix s s (Localization S)[X][Y]) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    simpa [hdet, hone] using h
  have hInvMul : ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 * A = 1 :=
    congrArg (fun g : GL s (Localization S)[X][Y] => (g : Matrix s s (Localization S)[X][Y]))
      (inv_mul_cancel (Ncy c M))
  simpa [mul_assoc, hInvMul, A] using
    (congrArg (fun B => ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 * B) hA_mul_adj).symm

include hc

theorem ncy_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) := by
  rcases hc i j with ⟨w, hw⟩
  refine ⟨X * w + C (if i = j then 1 else 0 : R[X]), ?_⟩
  exact ncy_isInteger_eq hs M i j w hw

theorem ncyInv_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((NcyInv c M).1 i j) := by
  let A : Matrix s s (Localization S)[X][Y] := (Ncy c M).1
  have hInv_eq_adj : ((Ncy c M)⁻¹ : GL s (Localization S)[X][Y]).1 = A.adjugate :=
    inv_Ncy_val_eq_adjugate hs c M
  have hNcyInv : (NcyInv c M) = (Ncy c M)⁻¹ := by
    show Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y])
          (S := (Localization S)[X][Y]) (σA c) (N M)⁻¹ =
        (Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y])
              (S := (Localization S)[X][Y]) (σA c) (N M))⁻¹
    exact Matrix.GeneralLinearGroup.map_inv (σA c) (N M)
  have hA0_entry (i j : s) : IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) :=
    ncy_isInteger hs M hc i j
  let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
  let A0 : Matrix s s R[X][Y] := fun i j => (hA0_entry i j).choose
  have hA0 : f.mapMatrix A0 = A := by
    apply Matrix.ext
    intro i j
    exact (hA0_entry i j).choose_spec
  refine ⟨(A0.adjugate) i j, ?_⟩
  have hAdj : f.mapMatrix A0.adjugate = A.adjugate := by simpa [hA0] using f.map_adjugate A0
  rw [hNcyInv, hInv_eq_adj]
  simpa [f] using congrArg (fun B : Matrix s s (Localization S)[X][Y] => B i j) hAdj

def N0 : Matrix s s R[X][Y] := fun i j => (ncy_isInteger hs M hc i j).choose

def N0Inv : Matrix s s R[X][Y] := fun i j => (ncyInv_isInteger hs M hc i j).choose

theorem hN0_mul : N0 hs M hc * N0Inv hs M hc = 1 := by
  classical
  let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
  have hf : Function.Injective f := by
    have hR : Function.Injective (algebraMap R (Localization S)) :=
      IsLocalization.injective (Localization S) hs
    have hRX : Function.Injective (algebraMap R[X] (Localization S)[X]) := by
      simpa [Polynomial.algebraMap_def] using Polynomial.map_injective (algebraMap R _) hR
    simpa [f, Polynomial.algebraMap_def] using
      Polynomial.map_injective (algebraMap R[X] (Localization S)[X]) hRX
  have hfMat :
      Function.Injective
        (f.mapMatrix : Matrix s s R[X][Y] → Matrix s s (Localization S)[X][Y]) := by
    intro A B h
    apply Matrix.ext
    intro i j
    apply hf
    have hij := congrArg (fun M : Matrix s s (Localization S)[X][Y] => M i j) h
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hij
  have hN0 : f.mapMatrix (N0 hs M hc) = (Ncy c M).1 := by
    apply Matrix.ext
    intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply, N0, f] using
      (ncy_isInteger hs M hc i j).choose_spec
  have hN0Inv : f.mapMatrix (N0Inv hs M hc) = (NcyInv c M).1 := by
    apply Matrix.ext
    intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply, N0Inv, f] using
      (ncyInv_isInteger hs M hc i j).choose_spec
  have hNcyInv : NcyInv c M = (Ncy c M)⁻¹ := by
    simp [NcyInv, Ncy]
  have hMul : (Ncy c M).1 * (NcyInv c M).1 = 1 := by
    have hGL : Ncy c M * NcyInv c M = 1 := by
      rw [hNcyInv]
      simp
    simpa using
      congrArg (fun g : GL s (Localization S)[X][Y] => (g : Matrix s s (Localization S)[X][Y]))
        hGL
  have hmapProd : f.mapMatrix (N0 hs M hc * N0Inv hs M hc) = 1 := by
    calc
      f.mapMatrix (N0 hs M hc * N0Inv hs M hc) =
          f.mapMatrix (N0 hs M hc) * f.mapMatrix (N0Inv hs M hc) := by
        simp
      _ = (Ncy c M).1 * (NcyInv c M).1 := by simp [hN0, hN0Inv]
      _ = 1 := hMul
  have hmapProd1 :
      f.mapMatrix (N0 hs M hc * N0Inv hs M hc) = f.mapMatrix (1 : Matrix s s R[X][Y]) := by
    calc
      f.mapMatrix (N0 hs M hc * N0Inv hs M hc) = 1 := hmapProd
      _ = f.mapMatrix (1 : Matrix s s R[X][Y]) := by simp
  exact hfMat hmapProd1

theorem hN0inv_mul : N0Inv hs M hc * N0 hs M hc = 1 := by
  classical
  let f : R[X][Y] →+* (Localization S)[X][Y] := algebraMap R[X][Y] (Localization S)[X][Y]
  have hf : Function.Injective f := by
    have hR : Function.Injective (algebraMap R (Localization S)) :=
      IsLocalization.injective (Localization S) hs
    have hRX : Function.Injective (algebraMap R[X] (Localization S)[X]) := by
      simpa [Polynomial.algebraMap_def] using Polynomial.map_injective (algebraMap R _) hR
    simpa [f, Polynomial.algebraMap_def] using
      Polynomial.map_injective (algebraMap R[X] (Localization S)[X]) hRX
  have hfMat :
      Function.Injective
        (f.mapMatrix : Matrix s s R[X][Y] → Matrix s s (Localization S)[X][Y]) := by
    intro A B h
    apply Matrix.ext
    intro i j
    apply hf
    have hij := congrArg (fun M : Matrix s s (Localization S)[X][Y] => M i j) h
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hij
  have hN0 : f.mapMatrix (N0 hs M hc) = (Ncy c M).1 := by
    apply Matrix.ext
    intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply, N0, f] using
      (ncy_isInteger hs M hc i j).choose_spec
  have hN0Inv : f.mapMatrix (N0Inv hs M hc) = (NcyInv c M).1 := by
    apply Matrix.ext
    intro i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply, N0Inv, f] using
      (ncyInv_isInteger hs M hc i j).choose_spec
  have hNcyInv : NcyInv c M = (Ncy c M)⁻¹ := by
    simp [NcyInv, Ncy]
  have hMul : (NcyInv c M).1 * (Ncy c M).1 = 1 := by
    have hGL : NcyInv c M * Ncy c M = 1 := by
      rw [hNcyInv]
      simp
    simpa using
      congrArg (fun g : GL s (Localization S)[X][Y] => (g : Matrix s s (Localization S)[X][Y]))
        hGL
  have hmapProd : f.mapMatrix (N0Inv hs M hc * N0 hs M hc) = 1 := by
    calc
      f.mapMatrix (N0Inv hs M hc * N0 hs M hc) =
          f.mapMatrix (N0Inv hs M hc) * f.mapMatrix (N0 hs M hc) := by simp
      _ = (NcyInv c M).1 * (Ncy c M).1 := by simp [hN0, hN0Inv]
      _ = 1 := hMul
  have hmapProd1 :
      f.mapMatrix (N0Inv hs M hc * N0 hs M hc) = f.mapMatrix (1 : Matrix s s R[X][Y]) := by
    calc
      f.mapMatrix (N0Inv hs M hc * N0 hs M hc) = 1 := hmapProd
      _ = f.mapMatrix (1 : Matrix s s R[X][Y]) := by simp
  exact hfMat hmapProd1

def U : Matrix.GeneralLinearGroup s R[X][Y] :=
  ⟨N0 hs M hc, N0Inv hs M hc, hN0_mul hs M hc , hN0inv_mul hs M hc⟩

theorem hU : ((U hs M hc)⁻¹ : Matrix s s R[X][Y]).mulVec (fun i => C (v i)) =
    fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y) := by
  sorry
