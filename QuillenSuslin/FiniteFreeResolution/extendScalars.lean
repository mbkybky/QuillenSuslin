import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.Basic

universe v u u'

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable (R : Type u) [CommRing R] (A : Type u') [CommRing A]

section extendScalars'

variable [Algebra R A]

/-- A direct version of extension of scalars whose object is definitionally `A ⊗[R] M`. -/
def extendScalars' : ModuleCat.{v} R ⥤ ModuleCat.{max u' v} A where
  obj X := ModuleCat.of A (A ⊗[R] X)
  map f := ModuleCat.ofHom (AlgebraTensorModule.lTensor A A f.hom)
  map_id := by simp
  map_comp _ _ := by
    ext
    simp

instance extendScalars'_additive : (extendScalars' R A).Additive where
  map_add {_} _ _ _ := by
    simp [extendScalars']
    rfl

lemma extendScalars'_map_exact [Module.Flat R A]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.Exact) :
    (S.map (extendScalars' R A)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact (R := R) A hS

instance [Module.Flat R A] : PreservesFiniteLimits (extendScalars' R A) := by
  have h := ((Functor.exact_tfae (extendScalars' R A)).out 1 3).mp (extendScalars'_map_exact R A)
  exact h.1

instance [Module.Flat R A] : PreservesFiniteColimits (extendScalars' R A) := by
  have h := ((Functor.exact_tfae (extendScalars' R A)).out 1 3).mp (extendScalars'_map_exact R A)
  exact h.2

end extendScalars'

instance extendScalars_additive (f : R →+* A) : (extendScalars f).Additive where
  map_add {_} _ _ _ := by
    simp [extendScalars, ExtendScalars.map']
    rfl

variable [Algebra R A] [Module.Flat R A]

lemma extendScalars_map_exact
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.Exact) :
    (S.map (extendScalars (algebraMap R A))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  let B := (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)
  let e : B ≃ₗ[R] A :=
    { __ := AddEquiv.refl A
      map_smul' := by simp [B, Algebra.smul_def] }
  have : Module.Flat R B := Module.Flat.of_linearEquiv e
  apply Module.Flat.lTensor_exact B hS

instance : PreservesFiniteLimits (extendScalars (algebraMap R A)) := by
  have h := ((Functor.exact_tfae (extendScalars (algebraMap R A))).out 1 3).mp
    (extendScalars_map_exact R A)
  exact h.1

instance : PreservesFiniteColimits (extendScalars (algebraMap R A)) := by
  have h := ((Functor.exact_tfae (extendScalars (algebraMap R A))).out 1 3).mp
    (extendScalars_map_exact R A)
  exact h.2

end ModuleCat
