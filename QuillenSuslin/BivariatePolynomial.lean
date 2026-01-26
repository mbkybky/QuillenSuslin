import Mathlib

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]
variable {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
  {x : (Localization S)[X][Y]} (c : S) (M : GL s (Localization S)[X])

noncomputable section

instance : Algebra R[X] (Localization S)[X] :=
  (mapRingHom (algebraMap R (Localization S))).toAlgebra

/-- The canonical `R[X][Y]`-algebra structure on `(Localization S)[X][Y]`. -/
instance : Algebra R[X][Y] (Localization S)[X][Y] :=
  (mapRingHom (algebraMap R[X] (Localization S)[X])).toAlgebra

/-- The `R[X][Y]`-endomorphism scaling `Y` by `c`. -/
def σR : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) ((c : R) • (Polynomial.X : R[X][Y]))

/-- The `(Localization S)[X][Y]`-endomorphism scaling `Y` by the image of `c`. -/
def σA : (Localization S)[X][Y] →+* (Localization S)[X][Y] :=
  Polynomial.eval₂RingHom C
    (((algebraMap R (Localization S)) (c : R)) • (X : (Localization S)[X][Y]))

/-- `σA` commutes with the canonical map `R[X][Y] → (Localization S)[X][Y]`. -/
theorem σA_comp : (σA c).comp (algebraMap R[X][Y] (Localization S)[X][Y]) =
    (algebraMap R[X][Y] (Localization S)[X][Y]).comp (σR c) := by
  have hAlg : algebraMap R[X][Y] (Localization S)[X][Y] =
    (mapRingHom (algebraMap R[X] (Localization S)[X])) := rfl
  refine Polynomial.ringHom_ext ?_ ?_
  · intro p
    have hC : algebraMap R[X][Y] (Localization S)[X][Y] (C p) =
        C (algebraMap R[X] (Localization S)[X] p) := by
      rw [hAlg]
      simp
    have hσR : σR c (C p) = C p := by
      show (C p).eval₂ (C : R[X] →+* R[X][Y]) ((c : R) • (Polynomial.X : R[X][Y])) = C p
      rw [Polynomial.eval₂_C]
    simp only [RingHom.comp_apply]
    rw [hσR, hC]
    show (C (algebraMap R[X] (Localization S)[X] p)).eval₂ C _ = _
    rw [Polynomial.eval₂_C]
  · have hX : algebraMap R[X][Y] (Localization S)[X][Y] X = X := by
      rw [hAlg]
      simp [Polynomial.mapRingHom]
    have hσR : σR c X = (c : R) • X := by
      show X.eval₂ (C : R[X] →+* R[X][Y]) ((c : R) • (Polynomial.X : R[X][Y])) = (c : R) • X
      rw [Polynomial.eval₂_X]
    have hσA : σA c X = ((algebraMap R (Localization S)) (c : R)) • X := by
      show X.eval₂ C (((algebraMap R (Localization S)) (c : R)) • X) = _
      rw [Polynomial.eval₂_X]
    simp only [RingHom.comp_apply]
    rw [hσR, hX, hσA, Algebra.smul_def, Algebra.smul_def]
    simp

theorem isInteger_σA (hx : IsLocalization.IsInteger R[X][Y] x) :
    IsLocalization.IsInteger R[X][Y] (σA c x) := by
  rcases hx with ⟨r, rfl⟩
  refine ⟨σR c r, ?_⟩
  have := congrArg (fun f => f r) (σA_comp c)
  simpa using this.symm

section S

variable (S)

def CAY : (Localization S)[X] →+* (Localization S)[X][Y] :=
    (C : (Localization S)[X] →+* (Localization S)[X][Y])

def φ : (Localization S)[X] →+* (Localization S)[X][Y] :=
    Polynomial.eval₂RingHom (((CAY S).comp (C : Localization S →+* (Localization S)[X])))
      ((CAY S (X : (Localization S)[X])) + (Y : (Localization S)[X][Y]))

end S

section M

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

end M
