import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (c : S) (M : GL s (Localization S)[X])
  (hM : (M.1.mulVec fun i ↦ map (algebraMap R (Localization S)) (v i)) =
    fun i ↦ C ((algebraMap R (Localization S)) (eval 0 (v i))))

noncomputable section

theorem ncy_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((Ncy c M).1 i j) := sorry

theorem ncyInv_isInteger (i j : s) : IsLocalization.IsInteger R[X][Y] ((NcyInv c M).1 i j) := sorry

def N0 : Matrix s s R[X][Y] := fun i j => (ncy_isInteger c M i j).choose

def N0Inv : Matrix s s R[X][Y] := fun i j => (ncyInv_isInteger c M i j).choose

theorem hN0_mul : N0 c M * N0Inv c M = 1 := by
  sorry

theorem hN0inv_mul : N0Inv c M * N0 c M = 1 := by
  sorry

def U : Matrix.GeneralLinearGroup s R[X][Y] := ⟨N0 c M, N0Inv c M, hN0_mul c M , hN0inv_mul c M⟩

theorem hU : ((U c M)⁻¹ : Matrix s s R[X][Y]).mulVec (fun i => C (v i)) =
    fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y) := by
  sorry
