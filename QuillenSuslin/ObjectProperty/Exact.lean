/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import QuillenSuslin.ObjectProperty.Basic

public section

universe v u

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

namespace ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

theorem prop_biprod (P : ObjectProperty A)
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms] {X Y : A}
    (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_iso (biprod.isoProd X Y).symm (P.prop_prod X Y hX hY)

private theorem rightPresentation_shortExact {X₁ X₂ X₃ K F : A}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {i : K ⟶ F} {p : F ⟶ X₃}
    {wS : f ≫ g = 0} {wT : i ≫ p = 0}
    (hS : (ShortComplex.mk f g wS).ShortExact)
    (hT : (ShortComplex.mk i p wT).ShortExact) (l : F ⟶ X₂) (t : K ⟶ X₁)
    (hl : l ≫ g = p) (ht : t ≫ f = i ≫ l) :
    (ShortComplex.mk (biprod.lift (- t) i) (biprod.desc f l)
      (by simp [biprod.lift_desc, ht])).ShortExact := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  haveI := hT.mono_f
  haveI := hT.epi_g
  let U : ShortComplex A :=
    ShortComplex.mk (biprod.lift (- t) i) (biprod.desc f l) (by simp [biprod.lift_desc, ht])
  have hker {W : A} (a : W ⟶ X₁ ⊞ F) (ha : a ≫ biprod.desc f l = 0) :
      (a ≫ biprod.snd) ≫ p = 0 := by
    have hcomp : a ≫ biprod.desc f l = (a ≫ biprod.fst) ≫ f + (a ≫ biprod.snd) ≫ l := by
      simp [biprod.desc_eq, comp_add, Category.assoc]
    have h1 : (a ≫ biprod.snd) ≫ l = -((a ≫ biprod.fst) ≫ f) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [hcomp, add_comm] using ha
    rw [← hl, ← Category.assoc, h1]
    simp [Category.assoc, wS]
  have hmono : Mono U.f := by
    dsimp [U]
    apply mono_of_cancel_zero
    intro W a ha
    apply (cancel_mono i).1
    have h := congrArg (fun e => e ≫ biprod.snd) ha
    simpa [Category.assoc] using h
  have hepi : Epi U.g := by
    apply epi_of_cancel_zero
    intro Z q hq
    have hSf_q : f ≫ q = 0 := by
      simpa [U, Category.assoc] using congrArg (fun e => biprod.inl ≫ e) hq
    obtain ⟨d, hd⟩ := hS.exact.desc' q hSf_q
    have hd0 : d = 0 := by
      have hlq : l ≫ q = 0 := by
        simpa [U, Category.assoc] using congrArg (fun e => biprod.inr ≫ e) hq
      have hpd : p ≫ d = 0 := by
        simpa [← hl, Category.assoc, hd] using hlq
      exact (cancel_epi p).1 (by simpa using hpd)
    simpa [hd0] using hd.symm
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      exact hT.exact.lift (a ≫ biprod.snd) (hker a ha)
    · intro W a ha
      dsimp [U] at ha
      let m : W ⟶ K := hT.exact.lift (a ≫ biprod.snd) (hker a ha)
      have hm : m ≫ i = a ≫ biprod.snd := hT.exact.lift_f (a ≫ biprod.snd)
        (hker a ha)
      apply biprod.hom_ext
      · have hsum : (a ≫ biprod.fst) ≫ f + (a ≫ biprod.snd) ≫ l = 0 := by
          simpa [biprod.desc_eq, comp_add, Category.assoc] using ha
        apply (cancel_mono f).1
        change ((m ≫ biprod.lift (-t) i) ≫ biprod.fst) ≫ f = (a ≫ biprod.fst) ≫ f
        trans -((a ≫ biprod.snd) ≫ l)
        · rw [show ((m ≫ biprod.lift (-t) i) ≫ biprod.fst) ≫ f = - ((m ≫ i) ≫ l) by
            simp [Category.assoc, ht]]
          rw [hm]
        · simpa [neg_eq_iff_add_eq_zero, add_comm] using hsum
      · change (m ≫ biprod.lift (-t) i) ≫ biprod.snd = a ≫ biprod.snd
        simpa [Category.assoc] using hm
    · intro W a ha b hb
      let m : W ⟶ K := hT.exact.lift (a ≫ biprod.snd) (hker a ha)
      have hm : m ≫ i = a ≫ biprod.snd := hT.exact.lift_f (a ≫ biprod.snd)
        (hker a ha)
      apply (cancel_mono i).1
      have hb_snd : b ≫ i = a ≫ biprod.snd := by
        simpa [U, Category.assoc] using congrArg (fun e => e ≫ biprod.snd) hb
      rw [hb_snd, hm]
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

private theorem biprodRight_shortExact {K F X Y : A}
    {i : K ⟶ F} {p : F ⟶ X} {w : i ≫ p = 0}
    (hT : (ShortComplex.mk i p w).ShortExact) :
    (ShortComplex.mk (biprod.lift i 0) (biprod.map p (𝟙 Y)) (by
      ext <;> simp [w])).ShortExact := by
  haveI := hT.mono_f
  haveI := hT.epi_g
  let U : ShortComplex A := ShortComplex.mk (biprod.lift i 0) (biprod.map p (𝟙 Y)) (by
    ext <;> simp [w])
  have hmono : Mono U.f := by
    apply mono_of_cancel_zero
    intro W a ha
    apply (cancel_mono i).1
    simpa [U, Category.assoc] using congrArg (fun e => e ≫ biprod.fst) ha
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      dsimp [U] at ha
      have ha₁ : (a ≫ biprod.fst) ≫ p = 0 := by
        have h := congrArg (fun e => e ≫ biprod.fst) ha
        simpa [Category.assoc] using h
      exact hT.exact.lift (a ≫ biprod.fst) ha₁
    · intro W a ha
      dsimp [U] at ha
      have ha₁ : (a ≫ biprod.fst) ≫ p = 0 := by
        have h := congrArg (fun e => e ≫ biprod.fst) ha
        simpa [Category.assoc] using h
      let m : W ⟶ K := hT.exact.lift (a ≫ biprod.fst) ha₁
      have hm : m ≫ i = a ≫ biprod.fst := hT.exact.lift_f (a ≫ biprod.fst) ha₁
      have ha₂ : a ≫ biprod.snd = 0 := by
        have h := congrArg (fun e => e ≫ biprod.snd) ha
        simpa [Category.assoc] using h
      change m ≫ biprod.lift i 0 = a
      apply biprod.hom_ext
      · simpa [Category.assoc] using hm
      · simp [ha₂]
    · intro W a ha b hb
      dsimp [U] at ha hb
      have ha₁ : (a ≫ biprod.fst) ≫ p = 0 := by
        have h := congrArg (fun e => e ≫ biprod.fst) ha
        simpa [Category.assoc] using h
      let m : W ⟶ K := hT.exact.lift (a ≫ biprod.fst) ha₁
      have hm : m ≫ i = a ≫ biprod.fst := hT.exact.lift_f (a ≫ biprod.fst) ha₁
      apply (cancel_mono i).1
      have hb₁ : b ≫ i = a ≫ biprod.fst := by
        have h := congrArg (fun e => e ≫ biprod.fst) hb
        simpa [Category.assoc] using h
      exact hb₁.trans hm.symm
  exact ShortComplex.ShortExact.mk' hexact hmono inferInstance

private theorem HasFiniteResolutionOfLength.biprod_right (P : ObjectProperty A)
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms] {X Y : A} {n : ℕ}
    (hX : P.HasFiniteResolutionOfLength X n) (hY : P Y) :
    P.HasFiniteResolutionOfLength (X ⊞ Y) n := by
  cases hX with
  | zero X hX => exact HasFiniteResolutionOfLength.zero _ (prop_biprod P hX hY)
  | succ S n hS h₂ h₁ =>
      exact HasFiniteResolutionOfLength.succ
        (ShortComplex.mk (biprod.lift S.f 0) (biprod.map S.g (𝟙 Y)) (by
          ext <;> simp [S.zero]))
        n (biprodRight_shortExact hS) (prop_biprod P h₂ hY) h₁

private theorem pullback_shortExact {K F X Y : A}
    {i : K ⟶ F} {p : F ⟶ X} {w : i ≫ p = 0}
    (hT : (ShortComplex.mk i p w).ShortExact) (t : Y ⟶ X) :
    (ShortComplex.mk (pullback.lift i 0 (by rw [w, zero_comp])) (pullback.snd p t) (by
      rw [pullback.lift_snd])).ShortExact := by
  haveI := hT.mono_f
  haveI := hT.epi_g
  let U : ShortComplex A := ShortComplex.mk (pullback.lift i 0 (by rw [w, zero_comp]))
    (pullback.snd p t) (by rw [pullback.lift_snd])
  have hmono : Mono U.f := by
    dsimp [U]
    apply mono_of_cancel_zero
    intro W a ha
    apply (cancel_mono i).1
    have h := congrArg (fun e => e ≫ pullback.fst p t) ha
    simpa [Category.assoc, pullback.lift_fst] using h
  have hker {W : A} (a : W ⟶ pullback p t) (ha : a ≫ pullback.snd p t = 0) :
      (a ≫ pullback.fst p t) ≫ p = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, zero_comp]
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      exact hT.exact.lift (a ≫ pullback.fst p t) (hker a ha)
    · intro W a ha
      let m : W ⟶ K := hT.exact.lift (a ≫ pullback.fst p t) (hker a ha)
      have hm : m ≫ i = a ≫ pullback.fst p t := hT.exact.lift_f _ _
      change m ≫ pullback.lift i 0 (by rw [w, zero_comp]) = a
      apply pullback.hom_ext
      · simpa [Category.assoc, pullback.lift_fst] using hm
      · simpa [Category.assoc, pullback.lift_snd] using ha.symm
    · intro W a ha b hb
      dsimp [U] at ha hb
      let m : W ⟶ K := hT.exact.lift (a ≫ pullback.fst p t) (hker a ha)
      have hm : m ≫ i = a ≫ pullback.fst p t := hT.exact.lift_f _ _
      apply (cancel_mono i).1
      have hb₁ : b ≫ i = a ≫ pullback.fst p t := by
        have h := congrArg (fun e => e ≫ pullback.fst p t) hb
        simpa [Category.assoc, pullback.lift_fst] using h
      exact hb₁.trans hm.symm
  exact ShortComplex.ShortExact.mk' hexact hmono inferInstance

private theorem horseshoe_middle_shortExact {X₁ X₂ X₃ K₁ F₁ K₃ F₃ : A}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {i₁ : K₁ ⟶ F₁} {p₁ : F₁ ⟶ X₁}
    {i₃ : K₃ ⟶ F₃} {p₃ : F₃ ⟶ X₃}
    {wS : f ≫ g = 0} {wT₁ : i₁ ≫ p₁ = 0} {wT₃ : i₃ ≫ p₃ = 0}
    (hT₁ : (ShortComplex.mk i₁ p₁ wT₁).ShortExact)
    (hS : (ShortComplex.mk f g wS).ShortExact)
    (hT₃ : (ShortComplex.mk i₃ p₃ wT₃).ShortExact)
    (l : F₃ ⟶ X₂) (t : K₃ ⟶ X₁)
    (hl : l ≫ g = p₃) (ht : t ≫ f = i₃ ≫ l) :
    (ShortComplex.mk
      (biprod.lift (pullback.fst p₁ (-t)) (pullback.snd p₁ (-t) ≫ i₃))
      (biprod.desc (p₁ ≫ f) l) (by
        rw [biprod.lift_desc, pullback.condition_assoc]
        simp [Category.assoc, ht])).ShortExact := by
  haveI := hT₁.epi_g
  haveI := hS.mono_f
  haveI := hS.epi_g
  haveI := hT₃.mono_f
  haveI := hT₃.epi_g
  let j : pullback p₁ (-t) ⟶ F₁ ⊞ F₃ :=
    biprod.lift (pullback.fst p₁ (-t)) (pullback.snd p₁ (-t) ≫ i₃)
  let m : F₁ ⊞ F₃ ⟶ X₂ := biprod.desc (p₁ ≫ f) l
  let U : ShortComplex A := ShortComplex.mk j m (by
    rw [biprod.lift_desc, pullback.condition_assoc]
    simp [Category.assoc, ht])
  have hmono : Mono U.f := by
    dsimp [U, j]
    apply mono_of_cancel_zero
    intro W a ha
    apply pullback.hom_ext
    · have h := congrArg (fun e => e ≫ biprod.fst) ha
      simpa [Category.assoc] using h
    · apply (cancel_mono i₃).1
      have h := congrArg (fun e => e ≫ biprod.snd) ha
      simpa [Category.assoc] using h
  have hepi : Epi U.g := by
    apply epi_of_cancel_zero
    intro Z q hq
    have hpq : (p₁ ≫ f) ≫ q = 0 := by
      simpa [U, m, Category.assoc] using congrArg (fun e => biprod.inl ≫ e) hq
    have hfq : f ≫ q = 0 := (cancel_epi p₁).1 (by simpa [Category.assoc] using hpq)
    obtain ⟨d, hd⟩ := hS.exact.desc' q hfq
    have hd0 : d = 0 := by
      have hlq : l ≫ q = 0 := by
        simpa [U, m, Category.assoc] using congrArg (fun e => biprod.inr ≫ e) hq
      have hpd : p₃ ≫ d = 0 := by
        simpa [← hl, Category.assoc, hd] using hlq
      exact (cancel_epi p₃).1 (by simpa using hpd)
    simpa [hd0] using hd.symm
  have hker₃ {W : A} (a : W ⟶ F₁ ⊞ F₃) (ha : a ≫ m = 0) :
      (a ≫ biprod.snd) ≫ p₃ = 0 := by
    have hsum : (a ≫ biprod.fst) ≫ p₁ ≫ f + (a ≫ biprod.snd) ≫ l = 0 := by
      simpa [m, biprod.desc_eq, comp_add, Category.assoc] using ha
    have hcomp : ((a ≫ biprod.fst) ≫ p₁ ≫ f + (a ≫ biprod.snd) ≫ l) ≫ g = 0 := by
      rw [hsum, zero_comp]
    have hqg : (a ≫ biprod.snd) ≫ l ≫ g = 0 := by
      simpa [add_comp, Category.assoc, wS] using hcomp
    simpa [hl, Category.assoc] using hqg
  have mk_hpb {W : A} (a : W ⟶ F₁ ⊞ F₃) (ha : a ≫ m = 0)
      (k₃ : W ⟶ K₃) (hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd) :
      (a ≫ biprod.fst) ≫ p₁ = k₃ ≫ (-t) := by
    have hsum : (a ≫ biprod.fst) ≫ p₁ ≫ f + (a ≫ biprod.snd) ≫ l = 0 := by
      simpa [m, biprod.desc_eq, comp_add, Category.assoc] using ha
    have ht' : (k₃ ≫ i₃) ≫ l = (k₃ ≫ t) ≫ f := by
      simpa [Category.assoc] using congrArg (fun e => k₃ ≫ e) ht.symm
    apply (cancel_mono f).1
    trans - (a ≫ biprod.snd) ≫ l
    · simpa [eq_neg_iff_add_eq_zero, Category.assoc, add_comm] using hsum
    · simp [← hk₃, ht']
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      let k₃ : W ⟶ K₃ := hT₃.exact.lift (a ≫ biprod.snd) (hker₃ a ha)
      have hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd := hT₃.exact.lift_f _ _
      exact pullback.lift (a ≫ biprod.fst) k₃ (mk_hpb a ha k₃ hk₃)
    · intro W a ha
      let k₃ : W ⟶ K₃ := hT₃.exact.lift (a ≫ biprod.snd) (hker₃ a ha)
      have hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd := hT₃.exact.lift_f _ _
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, biprod.lift_snd, ← Category.assoc, pullback.lift_snd, hk₃]
    · intro W a ha b hb
      let k₃ : W ⟶ K₃ := hT₃.exact.lift (a ≫ biprod.snd) (hker₃ a ha)
      have hk₃ : k₃ ≫ i₃ = a ≫ biprod.snd := hT₃.exact.lift_f _ _
      let n : W ⟶ pullback p₁ (-t) := pullback.lift (a ≫ biprod.fst) k₃ (mk_hpb a ha k₃ hk₃)
      apply pullback.hom_ext
      · simpa [pullback.lift_fst, U, j, Category.assoc] using congrArg (fun e => e ≫ biprod.fst) hb
      · apply (cancel_mono i₃).1
        have hb_snd : (b ≫ pullback.snd p₁ (-t)) ≫ i₃ = a ≫ biprod.snd := by
          simpa [U, j, Category.assoc] using congrArg (fun e => e ≫ biprod.snd) hb
        rw [pullback.lift_snd, hb_snd, hk₃]
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

private theorem pullbackKernelComp_shortExact {X₁ X₂ X₃ K F : A}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {i : K ⟶ F} {p : F ⟶ X₂}
    {wS : f ≫ g = 0} {wT : i ≫ p = 0}
    (hS : (ShortComplex.mk f g wS).ShortExact)
    (hT : (ShortComplex.mk i p wT).ShortExact) :
    (ShortComplex.mk (pullback.fst p f) (p ≫ g) (by
      rw [← Category.assoc, pullback.condition, Category.assoc, wS, comp_zero])).ShortExact := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  haveI := hT.epi_g
  let U : ShortComplex A := ShortComplex.mk (pullback.fst p f) (p ≫ g) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, wS, comp_zero])
  have hker {W : A} (a : W ⟶ F) (ha : a ≫ p ≫ g = 0) :
      (a ≫ p) ≫ g = 0 := by simpa [Category.assoc] using ha
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      exact pullback.lift a (hS.exact.lift (a ≫ p) (hker a ha)) (by
        exact (hS.exact.lift_f (a ≫ p) (hker a ha)).symm)
    · intro W a ha
      rw [pullback.lift_fst]
    · intro W a ha b hb
      let m : W ⟶ pullback p f := pullback.lift a
        (hS.exact.lift (a ≫ p) (hker a ha)) (by
          exact (hS.exact.lift_f (a ≫ p) (hker a ha)).symm)
      apply pullback.hom_ext
      · rw [pullback.lift_fst, hb]
      · apply (cancel_mono f).1
        have hm : hS.exact.lift (a ≫ p) (hker a ha) ≫ f = a ≫ p :=
          hS.exact.lift_f (a ≫ p) (hker a ha)
        have hcond : (b ≫ pullback.snd p f) ≫ f = (b ≫ pullback.fst p f) ≫ p := by
          simpa [Category.assoc] using congrArg (fun e => b ≫ e)
            (pullback.condition : pullback.fst p f ≫ p = pullback.snd p f ≫ f).symm
        rw [hcond, hb, pullback.lift_snd, hm]
  exact ShortComplex.ShortExact.mk' hexact inferInstance inferInstance

private theorem pullbackLeft_shortExact {X₁ X₂ X₃ F : A}
    {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {p : F ⟶ X₃} {wS : f ≫ g = 0}
    (hS : (ShortComplex.mk f g wS).ShortExact) :
    (ShortComplex.mk (pullback.lift 0 f (by rw [zero_comp, wS])) (pullback.fst p g) (by
      rw [pullback.lift_fst])).ShortExact := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  let U : ShortComplex A := ShortComplex.mk (pullback.lift 0 f (by rw [zero_comp, wS]))
    (pullback.fst p g) (by rw [pullback.lift_fst])
  have hmono : Mono U.f := by
    apply mono_of_cancel_zero
    intro W a ha
    apply (cancel_mono f).1
    simpa [U, Category.assoc, pullback.lift_snd] using congrArg (fun e => e ≫ pullback.snd p g) ha
  have hker {W : A} (a : W ⟶ pullback p g) (ha : a ≫ pullback.fst p g = 0) :
      (a ≫ pullback.snd p g) ≫ g = 0 := by
    have hcond : (a ≫ pullback.snd p g) ≫ g = (a ≫ pullback.fst p g) ≫ p := by
      simpa [Category.assoc] using congrArg (fun e => a ≫ e)
        (pullback.condition : pullback.fst p g ≫ p = pullback.snd p g ≫ g).symm
    rw [hcond, ha, zero_comp]
  have hexact : U.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι U.f U.zero ?lift ?fac ?uniq
    · intro W a ha
      exact hS.exact.lift (a ≫ pullback.snd p g) (hker a ha)
    · intro W a ha
      let m : W ⟶ X₁ := hS.exact.lift (a ≫ pullback.snd p g) (hker a ha)
      have hm : m ≫ f = a ≫ pullback.snd p g := hS.exact.lift_f _ _
      change m ≫ pullback.lift 0 f (by rw [zero_comp, wS]) = a
      apply pullback.hom_ext
      · simpa [Category.assoc, pullback.lift_fst] using ha.symm
      · simpa [Category.assoc, pullback.lift_snd] using hm
    · intro W a ha b hb
      let m : W ⟶ X₁ := hS.exact.lift (a ≫ pullback.snd p g) (hker a ha)
      have hm : m ≫ f = a ≫ pullback.snd p g := hS.exact.lift_f _ _
      apply (cancel_mono f).1
      have hb_snd : b ≫ f = a ≫ pullback.snd p g := by
        simpa [U, Category.assoc, pullback.lift_snd] using
          congrArg (fun e => e ≫ pullback.snd p g) hb
      rw [hb_snd, hm]
  exact ShortComplex.ShortExact.mk' hexact hmono inferInstance

private theorem biprodInrFst_shortExact (X Y : A) :
    (ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y) (biprod.fst : X ⊞ Y ⟶ X)
      (BinaryBicone.inr_fst _)).ShortExact := by
  let S : ShortComplex A := ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y)
    (biprod.fst : X ⊞ Y ⟶ X) (BinaryBicone.inr_fst _)
  refine (ShortComplex.Splitting.mk biprod.snd biprod.inl ?_ ?_ ?_).shortExact
  · exact biprod.inr_snd
  · exact biprod.inl_fst
  · rw [add_comm]
    exact biprod.total

namespace HasFiniteResolution

/-- In a short exact sequence, if the left and right objects have finite `P`-resolutions,
then so does the middle object. -/
theorem of_shortExact_of_left_of_right {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₁] [P.HasFiniteResolution S.X₃] :
    P.HasFiniteResolution S.X₂ := by
  obtain ⟨n₁, h₁⟩ := HasFiniteResolution.out P S.X₁
  suffices ∀ {X₀ : A} {n₁ : ℕ} (_ : P.HasFiniteResolutionOfLength X₀ n₁)
      {X₂ X₃ : A} (f : X₀ ⟶ X₂) (g : X₂ ⟶ X₃) (w : f ≫ g = 0)
        (_ : (ShortComplex.mk f g w).ShortExact),
          P.HasFiniteResolution X₃ → P.HasFiniteResolution X₂ from
    this h₁ S.f S.g S.zero hS inferInstance
  intro X₀ n₁ h₁
  induction h₁ with
  | zero X₁ hX₁ =>
      intro X₂ X₃ f g w hS hX₃fin
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨_, h₃⟩ := hX₃fin.out
      cases h₃ with
      | zero X₃ hX₃ =>
          letI : Projective X₃ := hP X₃ hX₃
          let e : X₂ ≅ X₁ ⊞ X₃ := hS.splittingOfProjective.isoBinaryBiproduct
          have : P.HasFiniteResolution (X₁ ⊞ X₃) :=
            HasFiniteResolution.of_property (prop_biprod P hX₁ hX₃)
          exact HasFiniteResolution.of_iso e.symm
      | succ T₃ n hT₃ hF₃ hK₃ =>
          letI : Projective T₃.X₂ := hP T₃.X₂ hF₃
          let l : T₃.X₂ ⟶ X₂ := Projective.factorThru T₃.g g
          have hl : l ≫ g = T₃.g := Projective.factorThru_comp T₃.g g
          let t : T₃.X₁ ⟶ X₁ := hS.exact.lift (T₃.f ≫ l) (by rw [Category.assoc, hl, T₃.zero])
          have ht : t ≫ f = T₃.f ≫ l := hS.exact.lift_f _ _
          haveI : P.HasFiniteResolution T₃.X₁ := ⟨n, hK₃⟩
          exact HasFiniteResolution.of_shortExact
            (rightPresentation_shortExact hS hT₃ l t hl ht)
            (prop_biprod P hX₁ hF₃)
  | succ T₁ n hT₁ hF₁ hK₁ ih =>
      intro X₂ X₃ f g w hS hX₃fin
      haveI := hS.mono_f
      haveI := hS.epi_g
      obtain ⟨_, h₃⟩ := hX₃fin.out
      cases h₃ with
      | zero X₃ hX₃ =>
          letI : Projective X₃ := hP X₃ hX₃
          let e : X₂ ≅ T₁.X₃ ⊞ X₃ := hS.splittingOfProjective.isoBinaryBiproduct
          have hleft : P.HasFiniteResolutionOfLength T₁.X₃ (n + 1) :=
            HasFiniteResolutionOfLength.succ T₁ n hT₁ hF₁ hK₁
          exact ⟨n + 1, (hleft.biprod_right P hX₃).of_iso e.symm⟩
      | succ T₃ n₃ hT₃ hF₃ hK₃ =>
          letI : Projective T₃.X₂ := hP T₃.X₂ hF₃
          let l : T₃.X₂ ⟶ X₂ := Projective.factorThru T₃.g g
          have hl : l ≫ g = T₃.g := Projective.factorThru_comp T₃.g g
          let t : T₃.X₁ ⟶ T₁.X₃ := hS.exact.lift (T₃.f ≫ l) (by
            rw [Category.assoc, hl, T₃.zero])
          have ht : t ≫ f = T₃.f ≫ l := hS.exact.lift_f _ _
          have hpb : P.HasFiniteResolution (pullback T₁.g (-t)) := by
            have hK₃fin : P.HasFiniteResolution T₃.X₁ := ⟨n₃, hK₃⟩
            exact ih (pullback.lift T₁.f 0 (by rw [T₁.zero, zero_comp]))
              (pullback.snd T₁.g (-t)) (by rw [pullback.lift_snd])
              (pullback_shortExact hT₁ (-t)) hK₃fin
          exact HasFiniteResolution.of_shortExact
            (horseshoe_middle_shortExact hT₁ hS hT₃ l t hl ht)
            (prop_biprod P hF₁ hF₃)

/-- In a short exact sequence, if the left and middle objects have finite `P`-resolutions,
then so does the right object. -/
theorem of_shortExact_of_left_of_middle {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₁] [P.HasFiniteResolution S.X₂] :
    P.HasFiniteResolution S.X₃ := by
  obtain ⟨n₂, h₂⟩ := HasFiniteResolution.out P S.X₂
  suffices ∀ {X₀ : A} {n₂ : ℕ} (_ : P.HasFiniteResolutionOfLength X₀ n₂)
      {X₁ X₃ : A} (f : X₁ ⟶ X₀) (g : X₀ ⟶ X₃) (w : f ≫ g = 0)
        (_ : (ShortComplex.mk f g w).ShortExact),
          P.HasFiniteResolution X₁ → P.HasFiniteResolution X₃ from
    this h₂ S.f S.g S.zero hS inferInstance
  intro X₀ n₂ h₂
  induction h₂ with
  | zero X₂ hX₂ =>
    intro X₁ X₃ f g w hS hX₁fin
    exact HasFiniteResolution.of_shortExact hS hX₂
  | succ T₂ n hT₂ hF₂ hK₂ _ =>
    intro X₁ X₃ f g w hS hX₁fin
    have hL : P.HasFiniteResolution (pullback T₂.g f) := by
      haveI : P.HasFiniteResolution T₂.X₁ := ⟨n, hK₂⟩
      exact of_shortExact_of_left_of_right hP (pullback_shortExact hT₂ f)
    exact HasFiniteResolution.of_shortExact (pullbackKernelComp_shortExact hS hT₂) hF₂

/-- In a short exact sequence, if the middle and right objects have finite `P`-resolutions,
then so does the left object. -/
theorem of_shortExact_of_middle_of_right {P : ObjectProperty A}
    [P.IsClosedUnderBinaryProducts] [P.IsClosedUnderIsomorphisms]
    (hP : P ≤ isProjective A) {S : ShortComplex A} (hS : S.ShortExact)
    [P.HasFiniteResolution S.X₂] [P.HasFiniteResolution S.X₃] :
    P.HasFiniteResolution S.X₁ := by
  obtain ⟨n₃, h₃⟩ := HasFiniteResolution.out P S.X₃
  suffices ∀ {X₀ : A} {n₃ : ℕ} (_ : P.HasFiniteResolutionOfLength X₀ n₃)
      {X₁ X₂ : A} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₀) (w : f ≫ g = 0)
        (_ : (ShortComplex.mk f g w).ShortExact),
          P.HasFiniteResolution X₂ → P.HasFiniteResolution X₁ from
    this h₃ S.f S.g S.zero hS inferInstance
  intro X₀ n₃ h₃
  induction h₃ with
  | zero X₃ hX₃ =>
    intro X₁ X₂ f g w hS hX₂fin
    letI : Projective X₃ := hP X₃ hX₃
    let e : X₂ ≅ X₁ ⊞ X₃ := hS.splittingOfProjective.isoBinaryBiproduct
    have hB : P.HasFiniteResolution (X₁ ⊞ X₃) := by
      exact HasFiniteResolution.of_iso e
    haveI : P.HasFiniteResolution X₃ := HasFiniteResolution.of_property hX₃
    exact of_shortExact_of_left_of_middle hP (biprodInrFst_shortExact X₁ X₃)
  | succ T₃ n hT₃ hF₃ hK₃ _ =>
    intro X₁ X₂ f g w hS hX₂fin
    have hN : P.HasFiniteResolution (pullback T₃.g g) := by
      haveI : P.HasFiniteResolution T₃.X₁ := ⟨n, hK₃⟩
      exact of_shortExact_of_left_of_right hP (pullback_shortExact hT₃ g)
    have hU : (ShortComplex.mk (pullback.lift 0 f (by rw [zero_comp, w]))
        (pullback.fst T₃.g g) (by rw [pullback.lift_fst])).ShortExact :=
      pullbackLeft_shortExact hS
    letI : Projective T₃.X₂ := hP T₃.X₂ hF₃
    let e : pullback T₃.g g ≅ X₁ ⊞ T₃.X₂ :=
      hU.splittingOfProjective.isoBinaryBiproduct
    have hB : P.HasFiniteResolution (X₁ ⊞ T₃.X₂) := by
      exact HasFiniteResolution.of_iso e
    haveI : P.HasFiniteResolution T₃.X₂ := HasFiniteResolution.of_property hF₃
    exact of_shortExact_of_left_of_middle hP (biprodInrFst_shortExact X₁ T₃.X₂)

end HasFiniteResolution

end ObjectProperty

end CategoryTheory
