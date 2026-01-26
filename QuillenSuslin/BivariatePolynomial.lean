import Mathlib

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (c : S) {M : GL s (Localization S)[X]}
  (hM : (M.1.mulVec fun i ↦ map (algebraMap R (Localization S)) (v i)) =
    fun i ↦ C ((algebraMap R (Localization S)) (eval 0 (v i))))

noncomputable section

instance : Algebra R[X][Y] (Localization S)[X][Y] :=
  RingHom.toAlgebra (mapRingHom (mapRingHom (algebraMap R (Localization S))))

def σR : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) ((c : R) • (Polynomial.X : R[X][Y]))

def σA : (Localization S)[X][Y] →+* (Localization S)[X][Y] :=
  Polynomial.eval₂RingHom (C : (Localization S)[X] →+* (Localization S)[X][Y])
    (((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y]))

theorem σA_comp : (σA c).comp (algebraMap R[X][Y] (Localization S)[X][Y]) =
    (algebraMap R[X][Y] (Localization S)[X][Y]).comp (σR c) := by
  sorry

theorem isInteger_σA (hx : IsLocalization.IsInteger R[X][Y] x) :
    IsLocalization.IsInteger R[X][Y] (σA c x) := by
  rcases hx with ⟨r, rfl⟩
  refine ⟨σR c r, ?_⟩
  have := congrArg (fun f => f r) (σA_comp c)
  simpa using this.symm
/-
section S

variable (S)

def CAY : (Localization S)[X] →+* (Localization S)[X][Y] :=
    (C : (Localization S)[X] →+* (Localization S)[X][Y])

def φ : (Localization S)[X] →+* (Localization S)[X][Y] :=
    Polynomial.eval₂RingHom (((CAY S).comp (C : Localization S →+* (Localization S)[X])))
      ((CAY S (X : (Localization S)[X])) + (Y : (Localization S)[X][Y]))

end S

section M

variable (M)

def Mx : GL s (Localization S)[X][Y] :=
  (Matrix.GeneralLinearGroup.map (CAY S)) M

def Mxy : GL s (Localization S)[X][Y] :=
  (Matrix.GeneralLinearGroup.map (φ S)) M

def N : GL s (Localization S)[X][Y] := (Mx M)⁻¹ * (Mxy M)

def W : Matrix s s (Localization S)[X][Y] :=
  fun i j => ((N M: Matrix s s (Localization S)[X][Y]) i j).divX

def Ncy : GL s (Localization S)[X][Y] :=
  Matrix.GeneralLinearGroup.map (σA c) (N M)

def NcyInv : GL s (Localization S)[X][Y] :=
  Matrix.GeneralLinearGroup.map (σA c) (N M)⁻¹

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

end M
 -/
