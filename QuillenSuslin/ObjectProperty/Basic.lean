/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Finite resolutions by objects satisfying `P : ObjectProperty A`

## Main definitions

* `CategoryTheory.ObjectProperty.HasFiniteResolutionOfLength`:
  Let `A` be an abelian category and `P : ObjectProperty A` be a property of objects in `A`.
  We say that `X : A` has a `P`-resolution of length `n` if there exists an
  exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ M ⟶ 0` such that each `Eᵢ : A` satisfies `P`.
* `CategoryTheory.ObjectProperty.HasFiniteResolution`:
  finite resolutions of some length by objects satisfying `P`.
* `CategoryTheory.HasFiniteProjectiveResolutionOfLength` and
  `CategoryTheory.HasFiniteProjectiveResolution`:
  the projective special case.
* `ModuleCat.finiteFree`:
  the object property of finite free modules.
-/

public section

universe v u v' u'

namespace CategoryTheory

open Category Limits ZeroObject

namespace ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Let `A` be an abelian category and `P : ObjectProperty A` be a property of objects in `A`.
We say that `X : A` has a `P`-resolution of length `n` if there exists an
exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ M ⟶ 0` such that each `Eᵢ : A` satisfies `P`. -/
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
theorem succ_of_zero_mem (h0 : P 0) (hX : P.HasFiniteResolutionOfLength X n) :
    P.HasFiniteResolutionOfLength X (n + 1) := by
  induction hX with
  | zero X hX =>
      let S : ShortComplex A := ShortComplex.mk (0 : 0 ⟶ X) (𝟙 X) (by simp)
      exact HasFiniteResolutionOfLength.succ S 0
        ((ShortComplex.Splitting.ofIsZeroOfIsIso S (isZero_zero A) inferInstance).shortExact)
          hX (HasFiniteResolutionOfLength.zero 0 h0)
  | succ S n hS h₂ _ ih => exact HasFiniteResolutionOfLength.succ S (n + 1) hS h₂ ih

theorem of_ge {m : ℕ} (h0 : P 0) (hX : P.HasFiniteResolutionOfLength X n) (h : n ≤ m) :
    P.HasFiniteResolutionOfLength X m :=
  Nat.le.rec hX (fun _ ↦ succ_of_zero_mem h0) h

theorem map_exactFunctor {B : Type u'} [Category.{v'} B] [Abelian B]
    {Q : ObjectProperty B} (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ X, P X → Q (F.obj X)) (hX : P.HasFiniteResolutionOfLength X n) :
    Q.HasFiniteResolutionOfLength (F.obj X) n := by
  induction hX with
  | zero X hX =>
      exact HasFiniteResolutionOfLength.zero (F.obj X) (hF X hX)
  | succ S n hS h₂ _ ih =>
      exact HasFiniteResolutionOfLength.succ (S.map F) n (hS.map_of_exact F) (hF S.X₂ h₂) ih

theorem hasFiniteResolution (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolution X :=
  ⟨n, hX⟩

end HasFiniteResolutionOfLength

namespace HasFiniteResolution

variable {P Q : ObjectProperty A} {X : A}

theorem of_property (hX : P X) : P.HasFiniteResolution X :=
  ⟨0, HasFiniteResolutionOfLength.zero X hX⟩

instance [P.Is X] : P.HasFiniteResolution X :=
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

theorem of_length {n : ℕ} (hX : P.HasFiniteResolutionOfLength X n) : P.HasFiniteResolution X :=
  hX.hasFiniteResolution

theorem of_iso [P.IsClosedUnderIsomorphisms] [P.HasFiniteResolution X] {Y : A} (e : X ≅ Y) :
    P.HasFiniteResolution Y := by
  obtain ⟨n, hX⟩ := HasFiniteResolution.out (P := P) (X := X)
  exact ⟨n, hX.of_iso e⟩

theorem of_shortExact {S : ShortComplex A} (hS : S.ShortExact) (h₂ : P S.X₂)
    [P.HasFiniteResolution S.X₁] : P.HasFiniteResolution S.X₃ := by
  obtain ⟨n, h₁⟩ := HasFiniteResolution.out (P := P) (X := S.X₁)
  exact ⟨n + 1, HasFiniteResolutionOfLength.succ S n hS h₂ h₁⟩

theorem map_exactFunctor {B : Type u'} [Category.{v'} B] [Abelian B]
    {Q : ObjectProperty B} (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hF : ∀ X, P X → Q (F.obj X)) [P.HasFiniteResolution X] :
    Q.HasFiniteResolution (F.obj X) := by
  obtain ⟨n, hX⟩ := HasFiniteResolution.out P X
  exact ⟨n, hX.map_exactFunctor F hF⟩

end HasFiniteResolution

end ObjectProperty

end CategoryTheory
