import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (c : S) (M : GL s (Localization S)[X])
  (hM : (M.1.mulVec fun i ↦ map (algebraMap R (Localization S)) (v i)) =
    fun i ↦ C ((algebraMap R (Localization S)) (eval 0 (v i))))
  (hW : ∀ i j : s, IsLocalization.IsInteger R[X][Y]
    ((C (C (c : R)) : R[X][Y]) • σA c ((W (S := S) (M := M)) i j)))

noncomputable section

include hs hW in
theorem ncy_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) := by
  classical
  have : Nontrivial (Localization S) := OreLocalization.nontrivial_of_nonZeroDivisors hs
  let b : R[X][Y] := C (C (c : R))
  let ev0 : (Localization S)[X][Y] →+* (Localization S)[X] := Polynomial.eval₂RingHom (RingHom.id _) 0
  let map0 :
      GL s (Localization S)[X][Y] →* GL s (Localization S)[X] :=
    Matrix.GeneralLinearGroup.map (n := s) (R := (Localization S)[X][Y]) (S := (Localization S)[X]) ev0
  have hMx0 : map0 (Mx (S := S) (M := M)) = M := by
    ext i j
    simp [map0, Mx, ev0, CAY]
  have hev0φ : ev0.comp (φ (S := S)) = RingHom.id (Localization S)[X] := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro a
      simp [ev0, φ, CAY]
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
      congrArg
        (fun g : GL s (Localization S)[X] => (g : Matrix s s (Localization S)[X])) hN0
    have hij := congrArg (fun A : Matrix s s (Localization S)[X] => A i j) hmat
    have hij' :
        ev0 ((N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j) =
          (if i = j then 1 else 0) := by
      simpa [map0, Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply] using hij
    simpa [ev0, Polynomial.coeff_zero_eq_eval_zero] using hij'
  have hN_entry :
      (N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j =
        X * ((W (S := S) (M := M)) i j) + C (if i = j then 1 else 0) := by
    have h :=
      (Polynomial.X_mul_divX_add (p :=
        (N (S := S) (M := M) : Matrix s s (Localization S)[X][Y]) i j))
    simpa [W, hcoeff0N, add_comm] using h.symm
  rcases hW i j with ⟨w, hw⟩
  refine ⟨X * w + C (if i = j then 1 else 0 : R[X]), ?_⟩
  let ι : R →+* Localization S := algebraMap R (Localization S)
  have hCι : mapRingHom ι (C (c : R)) = C (ι (c : R)) := by
    have :=
      congrArg (fun g : R →+* (Localization S)[X] => g (c : R)) (Polynomial.mapRingHom_comp_C (f := ι))
    simpa [RingHom.comp_apply] using this
  have hbMap :
      algebraMap R[X][Y] (Localization S)[X][Y] b =
        (C (C (ι (c : R))) : (Localization S)[X][Y]) := by
    simpa [b, ι, Polynomial.map_C, hCι]
  have hσA_X :
      σA c (X : (Localization S)[X][Y]) =
        algebraMap R[X][Y] (Localization S)[X][Y] b * X := by
    have hσA_X0 : σA c (X : (Localization S)[X][Y]) = (ι (c : R)) • (X : (Localization S)[X][Y]) := by
      dsimp [σA, ι]
      change
        eval₂ (C : (Localization S)[X] →+* (Localization S)[X][Y])
            (((algebraMap R (Localization S)) (c : R)) • (Polynomial.X : (Localization S)[X][Y]))
            (Polynomial.X : (Localization S)[X][Y]) =
          ((algebraMap R (Localization S)) (c : R)) • (Polynomial.X : (Localization S)[X][Y])
      exact
        Polynomial.eval₂_X (f := (C : (Localization S)[X] →+* (Localization S)[X][Y]))
          (x := (((algebraMap R (Localization S)) (c : R)) • (Polynomial.X : (Localization S)[X][Y])))
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
    simp [map_add, map_mul, mul_assoc, add_assoc]
  rw [hmap, hw]
  rw [hNcyij, hN_entry, map_add, map_mul]
  sorry

theorem ncyInv_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((NcyInv c M).1 i j) := sorry

/-
def N0 : Matrix s s R[X][Y] := fun i j => (ncy_isInteger (c := c) (M := M) i j).choose

def N0Inv : Matrix s s R[X][Y] := fun i j => (ncyInv_isInteger c M i j).choose

theorem hN0_mul : N0 c M * N0Inv c M = 1 := by
  sorry

theorem hN0inv_mul : N0Inv c M * N0 c M = 1 := by
  sorry

def U : Matrix.GeneralLinearGroup s R[X][Y] := ⟨N0 c M, N0Inv c M, hN0_mul c M , hN0inv_mul c M⟩

theorem hU : ((U c M)⁻¹ : Matrix s s R[X][Y]).mulVec (fun i => C (v i)) =
    fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y) := by
  sorry
 -/
