import QuillenSuslin.Linter.HaveLetI
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

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
  exact Module.Flat.lTensor_exact A hS

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

lemma extendScalars_map_exact (f : R →+* A) (hf : f.Flat)
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.Exact) :
    (S.map (extendScalars f)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  algebraize [f]
  have : Module.Flat R A := hf
  apply Module.Flat.lTensor_exact A hS

variable [Algebra R A] [Module.Flat R A]

instance : PreservesFiniteLimits (extendScalars (algebraMap R A)) := by
  have h := ((Functor.exact_tfae (extendScalars (algebraMap R A))).out 1 3).mp
    (extendScalars_map_exact R A (algebraMap R A)
      (RingHom.flat_algebraMap_iff.mpr inferInstance))
  exact h.1

instance : PreservesFiniteColimits (extendScalars (algebraMap R A)) := by
  have h := ((Functor.exact_tfae (extendScalars (algebraMap R A))).out 1 3).mp
    (extendScalars_map_exact R A (algebraMap R A)
      (RingHom.flat_algebraMap_iff.mpr inferInstance))
  exact h.2

end ModuleCat

variable (R : Type u) [CommRing R] (S : Type u') [CommRing S] [Algebra R S] (M : ModuleCat.{v} R)

example [Module.Flat R S] :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) := by
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { __ := AddEquiv.refl S
      map_smul' := by simp [Algebra.smul_def] }
  exact Module.Flat.of_linearEquiv e

example : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) = S := rfl

example [h : Module.Flat R M] : Module.Flat S ((ModuleCat.extendScalars (algebraMap R S)).obj M) :=
  sorry

#check ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ⊗[R] M
