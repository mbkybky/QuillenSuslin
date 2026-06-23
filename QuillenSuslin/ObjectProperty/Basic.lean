/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Objects admitting finite resolutions by an object property

Let `P : ObjectProperty A` be a property of objects in an abelian category `A`.
We say that `X : A` has a finite `P`-resolution of length `n` if it can be built by
iterating short exact sequences
`0 ⟶ K ⟶ F ⟶ X ⟶ 0`
where the middle object `F` satisfies `P`, and the left object `K` has a finite
`P`-resolution of the previous length.

This specializes to finite free resolutions for
`A = ModuleCat R` and `P = ModuleCat.finiteFree R`, and to bounded projective
resolutions when `P = CategoryTheory.isProjective A`.

## Main definitions

* `CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength`:
  finite resolutions of a specified length by objects satisfying `P`.
* `CategoryTheory.ObjectProperty.HasFiniteResolution`:
  finite resolutions of some length by objects satisfying `P`.
* `CategoryTheory.HasFiniteProjectiveResolutionOfLength` and
  `CategoryTheory.HasFiniteProjectiveResolution`:
  the projective special case.
* `ModuleCat.finiteFree`:
  the object property of finite free modules.
-/

public section

universe v u

namespace CategoryTheory

open Category Limits ZeroObject

namespace ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- An object `X` has a finite `P`-resolution of length `n` if either `n = 0` and `P X`,
or `X` sits at the end of a short exact sequence `0 ⟶ K ⟶ F ⟶ X ⟶ 0` with `P F`
and `K` admitting a finite `P`-resolution of length `n - 1`. -/
inductive HasFiniteResolutionOfLength (P : ObjectProperty A) : A → ℕ → Prop
  | zero (X : A) (hX : P X) : HasFiniteResolutionOfLength P X 0
  | succ (S : ShortComplex A) (n : ℕ) (hS : S.ShortExact) (h₂ : P S.X₂)
      (h₁ : HasFiniteResolutionOfLength P S.X₁ n) :
      HasFiniteResolutionOfLength P S.X₃ (n + 1)

/-- An object has a finite `P`-resolution if it has one of some finite length. -/
class HasFiniteResolution (P : ObjectProperty A) (X : A) : Prop where
  out (P X) : ∃ n : ℕ, P.HasFiniteResolutionOfLength X n

namespace HasFiniteResolutionOfLength

variable {P Q : ObjectProperty A} {X : A} {n : ℕ}

theorem property_of_zero (hX : P.HasFiniteResolutionOfLength X 0) : P X := by
  cases hX with
  | zero _ hX => exact hX

theorem mono (hPQ : P ≤ Q) (hX : P.HasFiniteResolutionOfLength X n) :
    Q.HasFiniteResolutionOfLength X n := by
  induction hX with
  | zero X hX => exact HasFiniteResolutionOfLength.zero X (hPQ X hX)
  | succ S n hS h₂ _ ih => exact HasFiniteResolutionOfLength.succ S n hS (hPQ S.X₂ h₂) ih

theorem property_of_le_closedUnderQuotients [Q.IsClosedUnderQuotients] (hPQ : P ≤ Q)
    (hX : P.HasFiniteResolutionOfLength X n) : Q X := by
  induction hX with
  | zero X hX => exact hPQ X hX
  | succ S _ hS h₂ _ _ => exact Q.prop_X₃_of_shortExact hS (hPQ S.X₂ h₂)

theorem property [P.IsClosedUnderQuotients] (hX : P.HasFiniteResolutionOfLength X n) : P X :=
  property_of_le_closedUnderQuotients (le_refl P) hX

/-- A short exact sequence whose middle object satisfies `P` extends a finite `P`-resolution
of the left object to one of the right object. -/
theorem succ' {S : ShortComplex A} (hS : S.ShortExact) (h₂ : P S.X₂)
    (h₁ : P.HasFiniteResolutionOfLength S.X₁ n) :
    P.HasFiniteResolutionOfLength S.X₃ (n + 1) :=
  HasFiniteResolutionOfLength.succ S n hS h₂ h₁

/-- Finite `P`-resolutions are invariant under isomorphism when `P` is. -/
theorem of_iso [P.IsClosedUnderIsomorphisms] {Y : A} (e : X ≅ Y)
    (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolutionOfLength Y n := by
  induction hX generalizing Y with
  | zero _ hX => exact HasFiniteResolutionOfLength.zero Y (P.prop_of_iso e hX)
  | succ S n hS h₂ h₁ _ =>
      let S' : ShortComplex A := ShortComplex.mk S.f (S.g ≫ e.hom) (by simp)
      have hS' : S'.ShortExact := by
        refine ShortComplex.shortExact_of_iso ?_ hS
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [S']) (by simp [S'])
      exact HasFiniteResolutionOfLength.succ S' n hS' h₂ h₁

/-- If the zero object satisfies `P`, a finite `P`-resolution can be padded by one step. -/
theorem succ_of_zero_mem (h0 : P (0 : A)) (hX : P.HasFiniteResolutionOfLength X n) :
    P.HasFiniteResolutionOfLength X (n + 1) := by
  induction hX with
  | zero X hX =>
      let S : ShortComplex A := ShortComplex.mk (0 : (0 : A) ⟶ X) (𝟙 X) (by simp)
      have hS : S.ShortExact := by
        refine (ShortComplex.Splitting.ofIsZeroOfIsIso S ?_ ?_).shortExact
        · simpa [S] using isZero_zero A
        · dsimp [S]
          infer_instance
      exact HasFiniteResolutionOfLength.succ S 0 hS hX
        (HasFiniteResolutionOfLength.zero (0 : A) h0)
  | succ S n hS h₂ _ ih =>
      exact HasFiniteResolutionOfLength.succ S (n + 1) hS h₂ ih

theorem of_ge {m : ℕ} (h0 : P (0 : A)) (hX : P.HasFiniteResolutionOfLength X n)
    (h : n ≤ m) : P.HasFiniteResolutionOfLength X m :=
  Nat.le.rec hX (fun _ ↦ succ_of_zero_mem h0) h

theorem hasFiniteResolution (hX : P.HasFiniteResolutionOfLength X n) :
    P.HasFiniteResolution X :=
  ⟨n, hX⟩

end HasFiniteResolutionOfLength

namespace HasFiniteResolution

variable {P Q : ObjectProperty A} {X : A}

theorem of_property (hX : P X) : P.HasFiniteResolution X :=
  ⟨0, HasFiniteResolutionOfLength.zero X hX⟩

instance of_is [P.Is X] : P.HasFiniteResolution X :=
  of_property (P.prop_of_is X)

theorem mono (hPQ : P ≤ Q) [P.HasFiniteResolution X] : Q.HasFiniteResolution X := by
  obtain ⟨n, hX⟩ := HasFiniteResolution.out (P := P) (X := X)
  exact ⟨n, hX.mono hPQ⟩

theorem property_of_le_closedUnderQuotients [Q.IsClosedUnderQuotients] (hPQ : P ≤ Q)
    [P.HasFiniteResolution X] : Q X := by
  obtain ⟨n, hX⟩ := HasFiniteResolution.out (P := P) (X := X)
  exact hX.property_of_le_closedUnderQuotients hPQ

theorem property [P.IsClosedUnderQuotients] [P.HasFiniteResolution X] : P X :=
  property_of_le_closedUnderQuotients (le_refl P)

theorem of_length {n : ℕ} (hX : P.HasFiniteResolutionOfLength X n) :
    P.HasFiniteResolution X :=
  hX.hasFiniteResolution

theorem of_iso [P.IsClosedUnderIsomorphisms] {Y : A} (e : X ≅ Y)
    [P.HasFiniteResolution X] : P.HasFiniteResolution Y := by
  obtain ⟨n, hX⟩ := HasFiniteResolution.out (P := P) (X := X)
  exact ⟨n, hX.of_iso e⟩

theorem of_shortExact {S : ShortComplex A} (hS : S.ShortExact) (h₂ : P S.X₂)
    [P.HasFiniteResolution S.X₁] : P.HasFiniteResolution S.X₃ := by
  obtain ⟨n, h₁⟩ := HasFiniteResolution.out (P := P) (X := S.X₁)
  exact ⟨n + 1, HasFiniteResolutionOfLength.succ S n hS h₂ h₁⟩

end HasFiniteResolution

end ObjectProperty

end CategoryTheory
