/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Polynomial.Quotient
public import QuillenSuslin.FiniteFreeResolution.BaseChange
public import QuillenSuslin.FiniteFreeResolution.Exact

public section

universe u v w

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal TensorProduct

private theorem smul_zero_of_smul_mem {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [Module A M]
    (K : Submodule A M) {a : A} (hmem : ∀ y : M, a • y ∈ K) (x : M ⧸ K) : a • x = 0 :=
  Quotient.inductionOn' x <| fun y ↦
    (Submodule.Quotient.mk_smul K a y).symm.trans ((Submodule.Quotient.mk_eq_zero K).2 (hmem y))

private theorem mem_ideal_of_smul_eq_zero_of_equiv_quotient
    {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) (eM : M ≃ₗ[A] A ⧸ I) {a : A} (hAnn : ∀ x : M, a • x = 0) : a ∈ I := by
  have h0 : a • (1 : A ⧸ I) = 0 := by simpa using congrArg eM (hAnn (eM.symm (1 : A ⧸ I)))
  have hmk : (Ideal.Quotient.mk I a : A ⧸ I) = 0 := by simpa [Algebra.smul_def] using h0
  exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk

instance Module.HasFiniteFreeResolution.of_quotient_of_submodule
    {A : Type u} [CommRing A] [Small.{u} A] {M : Type u} [AddCommGroup M] [Module A M]
    (K : Submodule A M) [HasFiniteFreeResolution A K] [HasFiniteFreeResolution A M] :
    HasFiniteFreeResolution A (M ⧸ K) :=
  of_shortExact_of_left_of_middle K.subtype (Submodule.mkQ K)
    Subtype.coe_injective (Submodule.mkQ_surjective K) (LinearMap.exact_subtype_mkQ K)

section polynomial

private noncomputable def polynomialModuleIdealMapCLinearEquiv (I : Ideal R) :
    PolynomialModule R I ≃ₗ[R[X]] I.map C :=
  let eR : R[X] ⊗[R] R ≃ₗ[R[X]] R[X] := AlgebraTensorModule.rid R R[X] R[X]
  let φ : R[X] ⊗[R] I →ₗ[R[X]] R[X] :=
    eR.toLinearMap.comp (AlgebraTensorModule.lTensor R[X] R[X] (I.subtype.restrictScalars R))
  have hφ_eq : φ = LinearMap.liftBaseChange R[X] ((Algebra.linearMap R R[X]).comp I.subtype) := by
    ext
    simp [coeff_one, coeff_C, φ, eR]
  have hφi : Function.Injective φ :=
    eR.injective.comp <| Module.Flat.lTensor_preserves_injective_linearMap
      (I.subtype.restrictScalars R) Subtype.coe_injective
  (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R I).symm.trans <|
    (LinearEquiv.ofInjective φ hφi).trans <| LinearEquiv.ofEq _ _ <| by
      simp [hφ_eq, LinearMap.range_comp, Ideal.map]

instance Module.HasFiniteFreeResolution.polynomialModule
    {P : Type u} [AddCommGroup P] [Module R P] [HasFiniteFreeResolution R P] :
    HasFiniteFreeResolution R[X] (PolynomialModule R P) :=
  of_linearEquiv (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R P)

/-- Push a finite free resolution of an `R`-ideal `I` to a resolution of `I · R[X]`. -/
instance Module.HasFiniteFreeResolution.map_C_of_hasFiniteFreeResolution
    (I : Ideal R) [HasFiniteFreeResolution R I] :
    HasFiniteFreeResolution R[X] (Ideal.map (C : R →+* R[X]) I) :=
  of_linearEquiv (polynomialModuleIdealMapCLinearEquiv I)

/-- Over a domain, the principal ideal `(f)` is linearly equivalent to the ambient ring. -/
noncomputable def linearEquiv_mul_spanSingleton [IsDomain R] {f : R}
    (hf : f ≠ 0) : R ≃ₗ[R] (Ideal.span ({f} : Set R) : Ideal R) :=
  Ideal.isoBaseOfIsPrincipal <| (Submodule.ne_bot_iff (span {f})).mpr
    ⟨f, mem_span_singleton_self f, hf⟩

/-- If `P ⊂ R[X]` is an ideal over a Noetherian domain `R`, then there exists
  `d ≠ 0` and `f ∈ P` such that `d • P ⊆ (f)`. -/
theorem exists_nonzero_C_mul_mem_span_singleton [IsDomain R] {P : Ideal (R[X])}
   (hPne : P ≠ ⊥) (hPfg : P.FG) : ∃ d : R, d ≠ 0 ∧ ∃ f : R[X], f ∈ P ∧ f ≠ 0 ∧
      ∀ g ∈ P, C d * g ∈ Ideal.span ({f} : Set (R[X])) := by
  classical
  rcases hPfg with ⟨s, hs⟩
  let K := FractionRing R
  let i : R →+* K := algebraMap R K
  have hi : Function.Injective i := IsFractionRing.injective R K
  let : Algebra R[X] K[X] := (Polynomial.mapRingHom i).toAlgebra
  have : IsLocalization ((nonZeroDivisors R).map (C : R →+* R[X])) K[X] :=
    (isLocalization (nonZeroDivisors R) K)
  let Pext : Ideal K[X] := Ideal.map (Polynomial.mapRingHom i) P
  have hPext_ne : Pext ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨p0, hp0P⟩, hp0ne⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.2 hPne)
    have hp0eq0 : (p0 : R[X]) = 0 := by
      apply (Polynomial.map_injective i hi)
      have hp0Pext : Polynomial.map i p0 ∈ Pext := Ideal.mem_map_of_mem (Polynomial.mapRingHom i) hp0P
      simpa [Pext, hbot] using hp0Pext
    apply hp0ne
    simp [Subtype.ext_iff, hp0eq0]
  let fK : K[X] := Submodule.IsPrincipal.generator Pext
  have hPext_span : Ideal.span ({fK} : Set K[X]) = Pext := Ideal.span_singleton_generator Pext
  have hfK_mem : fK ∈ Pext := by
    rw [← hPext_span]
    exact Ideal.subset_span (by simp)
  have hfK_ne : fK ≠ 0 := by
    intro hfK0
    apply hPext_ne
    rw [← hPext_span, hfK0, Ideal.span_singleton_zero]
  have hq0 : ∀ a : s, ∃ q : K[X], q * fK = (a : R[X]).map i := by
    intro a
    have haP : (a : R[X]) ∈ P := by
      simpa [hs] using (Ideal.subset_span a.2 : (a : R[X]) ∈ Ideal.span (s : Set (R[X])))
    have haPext : (a : R[X]).map i ∈ Pext := Ideal.mem_map_of_mem (Polynomial.mapRingHom i) haP
    have haSpan : (a : R[X]).map i ∈ Ideal.span ({fK} : Set K[X]) := by
      simpa [hPext_span] using haPext
    exact (Ideal.mem_span_singleton'.1 haSpan)
  choose q hq using hq0
  let v : s → K[X] := fun a => (a : R[X]).map i
  have hspan : Ideal.span (Set.range v) = Pext := by
    simp [Pext, ← hs, Ideal.map_span]
    congr
    ext x
    simp [v]
  have hfK_mem' : fK ∈ Ideal.span (Set.range v) := by simpa [hspan] using hfK_mem
  rcases (Ideal.mem_span_range_iff_exists_fun).1 hfK_mem' with ⟨c, hc⟩
  let fracs : Finset K[X] := s.attach.biUnion fun a => ({q a, c a} : Finset K[X])
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    ((nonZeroDivisors R).map (C : R →+* R[X])) fracs
  rcases b.2 with ⟨d, hd, hdEq⟩
  have hbEq : (b : R[X]) = C d := hdEq.symm
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hid0 : i d ≠ 0 := by
    intro h0
    apply hd0
    exact hi (by simpa using h0)
  have hqInt : ∀ a : s, IsLocalization.IsInteger (R[X]) ((b : R[X]) • q a) := by
    intro a
    exact hb (q a) (Finset.mem_biUnion.2 ⟨a, by simp, by simp⟩)
  choose qR hqR using hqInt
  have hcInt : ∀ a : s, IsLocalization.IsInteger (R[X]) ((b : R[X]) • c a) := by
    intro a
    exact hb (c a) (Finset.mem_biUnion.2 ⟨a, by simp, by simp⟩)
  choose cR hcR using hcInt
  have hqR' : ∀ a : s, Polynomial.map i (qR a) = C (i d) * q a := by
    intro a
    simpa [Algebra.smul_def, hbEq, Polynomial.map_C] using hqR a
  have hcR' : ∀ a : s, Polynomial.map i (cR a) = C (i d) * c a := by
    intro a
    simpa [Algebra.smul_def, hbEq, Polynomial.map_C] using hcR a
  let f : R[X] := ∑ a, cR a * (a : R[X])
  have hfP : f ∈ P := by
    refine Ideal.sum_mem _ ?_
    intro a _
    exact P.mul_mem_left _ (by
      simpa [hs] using (Ideal.subset_span a.2 : (a : R[X]) ∈ Ideal.span (s : Set (R[X]))))
  have hmap_f : Polynomial.map i f = C (i d) * fK := by
    simp only [f, Polynomial.map_sum, Polynomial.map_mul]
    simp_rw [hcR']
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [hc]
  have hf_ne : f ≠ 0 := by
    have hCd_ne : (C (i d) : K[X]) ≠ 0 := by simpa using hid0
    intro hf0
    have : Polynomial.map i f ≠ 0 := by
      rw [hmap_f]
      exact mul_ne_zero hCd_ne hfK_ne
    exact this (by simp [hf0])
  have hgen : ∀ a : s, C (d * d) * (a : R[X]) ∈ Ideal.span ({f} : Set (R[X])) := by
    intro a
    refine Ideal.mem_span_singleton'.2 ?_
    refine ⟨qR a, ?_⟩
    apply (Polynomial.map_injective i hi)
    rw [Polynomial.map_mul, hqR' a, hmap_f, Polynomial.map_mul, Polynomial.map_C]
    simp [map_mul, mul_left_comm, mul_comm, ← hq a, mul_assoc]
  refine ⟨d * d, mul_ne_zero hd0 hd0, f, hfP, hf_ne, ?_⟩
  intro g hgP
  have hgspan : g ∈ Ideal.span (s : Set (R[X])) := by simpa [hs] using hgP
  exact Submodule.span_induction (fun a ha => by simpa using hgen ⟨a, ha⟩) (by simp)
    (fun x y _ _ hx hy => by simpa [mul_add] using Ideal.add_mem _ hx hy)
    (fun a x _ hx => by
      have hy : a * (C (d * d) * x) ∈ Ideal.span ({f} : Set (R[X])) := Ideal.mul_mem_left _ a hx
      have hmul : C (d * d) * (a * x) = a * (C (d * d) * x) := by group
      exact hmul ▸ hy) hgspan

private theorem Module.HasFiniteFreeResolution.quotient_prime_aux [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P) : ∀ I : Ideal R, ∀ q : PrimeSpectrum R[X],
    Ideal.comap (C : R →+* R[X]) q.1 = I → HasFiniteFreeResolution (R[X]) (R[X] ⧸ q.1) := by
  -- Noetherian induction on the contraction `p.1 ∩ R`.
  let A : Type u := R[X]
  refine IsNoetherian.induction ?_
  intro I ih q hqI
  have hcomap : Ideal.comap (C : R →+* A) q.1 = I := hqI
  have hIA_le_P : Ideal.map (C : R →+* A) I ≤ q.1 :=
    (Ideal.map_le_iff_le_comap).2 <| by simp [hcomap]
  let IA : Ideal A := Ideal.map (C : R →+* A) I
  let B : Type u := A ⧸ IA
  have hI_res : HasFiniteFreeResolution R I := hR I inferInstance
  by_cases hPIA : q.1 = IA
  · exact of_linearEquiv (Submodule.quotEquivOfEq IA q.1 hPIA.symm)
  · have hIprime : Ideal.IsPrime I := by
      simpa [hcomap] using show (Ideal.comap (C : R →+* A) q.1).IsPrime from inferInstance
    let R₀ : Type u := R ⧸ I
    let A₀ : Type u := R₀[X]
    let π : A →+* B := Ideal.Quotient.mk IA
    let Pbar : Ideal B := Ideal.map π q.1
    let e : A₀ ≃+* B := Ideal.polynomialQuotientEquivQuotientPolynomial I
    let P₀ : Ideal A₀ := Ideal.comap e.toRingHom Pbar
    have hPbar_ne : Pbar ≠ ⊥ := by
      intro hbot
      have hle : q.1 ≤ RingHom.ker π := (q.1.map_eq_bot_iff_le_ker π).1 hbot
      have hker : RingHom.ker π = IA := IA.mk_ker
      have hP_le_IA : q.1 ≤ IA := hker ▸ hle
      exact hPIA (le_antisymm hP_le_IA hIA_le_P)
    have hP₀_ne : P₀ ≠ ⊥ := by
      intro hbot
      have : Ideal.map e.toRingHom P₀ = Pbar :=
        Ideal.map_comap_of_surjective e.toRingHom e.surjective Pbar
      have : Pbar = Ideal.map e.toRingHom ⊥ := by rw [← this, hbot]
      rw [show (Ideal.map e.toRingHom ⊥ : Ideal B) = ⊥ by simp] at this
      exact hPbar_ne this
    obtain ⟨d₀, hd₀, f₀, hf₀P₀, hf₀ne, hmul₀⟩ :=
      exists_nonzero_C_mul_mem_span_singleton hP₀_ne (fg_of_isNoetherianRing P₀)
    rcases Ideal.Quotient.mk_surjective d₀ with ⟨d, rfl⟩
    have hd_not_mem : d ∉ I := fun hdI ↦ hd₀ ((Ideal.Quotient.eq_zero_iff_mem).2 hdI)
    let fbar : B := e f₀
    have hfbar_mem : fbar ∈ Pbar := by
      have : f₀ ∈ P₀ := hf₀P₀
      simpa [P₀, Ideal.mem_comap, fbar] using this
    have hfbar_ne : fbar ≠ 0 := by
      intro h0
      apply hf₀ne
      exact e.injective (by simpa [fbar] using h0)
    let Fbar : Ideal B := Ideal.span ({fbar} : Set B)
    have hFbar_le : Fbar ≤ Pbar := by
      intro x hx
      rcases (Ideal.mem_span_singleton.1 hx) with ⟨y, rfl⟩
      exact Pbar.mul_mem_right y hfbar_mem
    have hmul_bar : ∀ g : B, g ∈ Pbar → (Ideal.Quotient.mk IA (C d) : B) * g ∈ Fbar := by
      intro g hg
      let g₀ : A₀ := e.symm g
      have hg₀ : g₀ ∈ P₀ := by
        have : (e g₀) ∈ Pbar := by simpa [g₀] using hg
        simpa [P₀, Ideal.mem_comap] using this
      have h0 : (C (Ideal.Quotient.mk I d) : A₀) * g₀ ∈ Ideal.span ({f₀} : Set A₀) :=
        hmul₀ g₀ hg₀
      have hCd : e (C (Ideal.Quotient.mk I d) : A₀) = (Ideal.Quotient.mk IA) (C d) := by
        simpa [IA, Polynomial.map_C] using
          (Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I (C d : A))
      have hmem : e ((C (Ideal.Quotient.mk I d) : A₀) * g₀) ∈
          Ideal.map e.toRingHom (Ideal.span ({f₀} : Set A₀)) :=
        Ideal.mem_map_of_mem e.toRingHom h0
      have hspan :
          Ideal.map (e : A₀ →+* B) (Ideal.span ({f₀} : Set A₀)) = Ideal.span ({fbar} : Set B) := by
        simpa [fbar] using (Ideal.map_span e.toRingHom ({f₀} : Set A₀))
      have : e (C (Ideal.Quotient.mk I d) : A₀) * e g₀ ∈ Fbar := by
        simpa [Fbar, hspan, map_mul] using hmem
      simpa [g₀, hCd] using this
    let Kbar : Submodule A Pbar :=
      Submodule.comap (Pbar.subtype.restrictScalars A) (Fbar.restrictScalars A)
    let N := Pbar ⧸ Kbar
    let : AddCommGroup N := Submodule.Quotient.addCommGroup Kbar
    have hsmul_d_mem_Kbar : ∀ y : Pbar, (C d : A) • y ∈ Kbar := by
      intro y
      change ((C d : A) • (y : B)) ∈ Fbar.restrictScalars A
      have hyFmul : (π (C d) : B) * (y : B) ∈ Fbar := by
        simpa [π] using hmul_bar (y : B) y.2
      have hsmul : ((C d : A) • (y : B)) = (π (C d) : B) * (y : B) := by
        have hAlgebraMap : (algebraMap A B) = π := rfl
        simpa [hAlgebraMap] using (Algebra.smul_def (C d : A) (y : B))
      exact hsmul ▸ hyFmul
    have hN : HasFiniteFreeResolution A N := by
      have hsmul_I_mem_Kbar : ∀ r : R, r ∈ I → ∀ y : Pbar, (C r : A) • y ∈ Kbar := by
        intro r hrI y
        change ((C r : A) • (y : B)) ∈ Fbar.restrictScalars A
        have hCrIA : (C r : A) ∈ IA := Ideal.mem_map_of_mem (C : R →+* A) hrI
        have hπCr : (π (C r) : B) = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hCrIA
        have hy0 : (C r : A) • (y : B) = 0 := by
          have hAlgebraMap : (algebraMap A B) = π := rfl
          rw [Algebra.smul_def, hAlgebraMap, hπCr]
          exact zero_mul _
        simp [hy0]
      let motive : ∀ (M : Type u), [AddCommGroup M] → [Module A M] → [Module.Finite A M] → Prop :=
        fun M _ _ _ => (∀ x : M, (C d : A) • x = 0) →
          (∀ r : R, r ∈ I → ∀ x : M, (C r : A) • x = 0) → HasFiniteFreeResolution A M
      have hN' : motive N := by
        refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A
          inferInstance (motive := motive) ?_ ?_ ?_
        · intro M _ _ _ _ _ _
          infer_instance
        · intro M _ _ _ p' eM hAnn_dM hAnn_IM
          have hCd_mem : (C d : A) ∈ p'.1 :=
            mem_ideal_of_smul_eq_zero_of_equiv_quotient p'.1 eM hAnn_dM
          have hI_le_contr : I ≤ Ideal.comap (C : R →+* A) p'.1 := by
            intro r hrI
            exact mem_ideal_of_smul_eq_zero_of_equiv_quotient p'.1 eM (hAnn_IM r hrI)
          have hlt : Ideal.comap (C : R →+* A) p'.1 > I := by
            refine lt_of_le_of_ne hI_le_contr ?_
            intro hEq
            have : d ∈ I := by simpa [hEq] using hCd_mem
            exact hd_not_mem this
          have hquot : HasFiniteFreeResolution A (A ⧸ p'.1) :=
            ih (Ideal.comap (C : R →+* A) p'.1) hlt p' rfl
          exact of_linearEquiv eM.symm
        · intro M₁ _ _ _ M₂ _ _ _ M₃ _ _ _ f g hf hg hfg h₁ h₃ hAnn_d2 hAnn_I2
          have hAnn_d1 : ∀ x : M₁, (C d : A) • x = 0 := by
            intro x
            apply hf
            simpa using hAnn_d2 (f x)
          have hAnn_I1 : ∀ r : R, r ∈ I → ∀ x : M₁, (C r : A) • x = 0 := by
            intro r hrI x
            apply hf
            simpa using hAnn_I2 r hrI (f x)
          have hAnn_d3 : ∀ x : M₃, (C d : A) • x = 0 := by
            intro z
            rcases hg z with ⟨y, rfl⟩
            simpa only [map_smul, map_zero] using congrArg g (hAnn_d2 y)
          have hAnn_I3 : ∀ r : R, r ∈ I → ∀ x : M₃, (C r : A) • x = 0 := by
            intro r hrI z
            rcases hg z with ⟨y, rfl⟩
            simpa only [map_smul, map_zero] using congrArg g (hAnn_I2 r hrI y)
          have : HasFiniteFreeResolution A M₁ := h₁ hAnn_d1 hAnn_I1
          have : HasFiniteFreeResolution A M₃ := h₃ hAnn_d3 hAnn_I3
          exact of_shortExact_of_left_of_right f g hf hg hfg
      exact hN' (smul_zero_of_smul_mem Kbar hsmul_d_mem_Kbar) <|
        fun r hrI => smul_zero_of_smul_mem Kbar (hsmul_I_mem_Kbar r hrI)
    have : IsDomain B := MulEquiv.isDomain A₀ e.symm.toMulEquiv
    have hFbar : HasFiniteFreeResolution A (Submodule.restrictScalars A Fbar) :=
      of_linearEquiv ((linearEquiv_mul_spanSingleton hfbar_ne).restrictScalars A)
    have hKbar : HasFiniteFreeResolution A Kbar :=
      have hFbar_leA : Fbar.restrictScalars A ≤ Pbar.restrictScalars A := hFbar_le
      of_linearEquiv (Submodule.comapSubtypeEquivOfLe hFbar_leA).symm
    have hPbar : HasFiniteFreeResolution A Pbar :=
      -- Short exact sequence `0 → Kbar → Pbar → Pbar/Fbar → 0`.
      of_shortExact_of_left_of_right Kbar.subtype (Submodule.mkQ Kbar) Subtype.coe_injective
        (Submodule.mkQ_surjective Kbar) <| LinearMap.exact_subtype_mkQ Kbar
    let fIP : IA →ₗ[A] q.1 := Submodule.inclusion hIA_le_P
    let gPP : q.1 →ₗ[A] Pbar :=
      { toFun := fun x => ⟨π x.1, Ideal.mem_map_of_mem π x.2⟩
        map_add' := fun _ _ => by congr
        map_smul' := by
          intro m x
          ext
          show π (m • x.1) = m • π x.1
          rw [smul_eq_mul]
          have hAlgebraMap : (algebraMap A B) = π := rfl
          have hsmulB : m • π x.1 = (π m : B) * π x.1 := by
            simpa [hAlgebraMap] using Algebra.smul_def m (π (x : A) : B)
          rw [hsmulB]
          exact π.map_mul m x.1 }
    have hfIP : Function.Injective fIP := by
      intro x y hxy
      apply Subtype.ext
      simpa [fIP] using congrArg (fun z : q.1 => (z : A)) hxy
    have hgPP : Function.Surjective gPP := by
      intro y
      rcases (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).1 y.2 with
        ⟨a, haP, haEq⟩
      refine ⟨⟨a, haP⟩, ?_⟩
      apply Subtype.ext
      simpa [gPP] using haEq
    have hexPP : Function.Exact fIP gPP := by
      intro x
      constructor
      · intro hx0
        refine ⟨⟨x.1, (Ideal.Quotient.eq_zero_iff_mem).1 <| congrArg (fun z : Pbar => z.1) hx0⟩, ?_⟩
        apply Subtype.ext
        rfl
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        simpa [gPP, fIP] using (Ideal.Quotient.eq_zero_iff_mem).2 y.2
    have : HasFiniteFreeResolution A q.1 := of_shortExact_of_left_of_right fIP gPP hfIP hgPP hexPP
    infer_instance

variable (R)

theorem Module.HasFiniteFreeResolution.quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) :=
  quotient_prime_aux hR (Ideal.comap (C : R →+* R[X]) p.1) p rfl

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem Module.HasFiniteFreeResolution.polynomial_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] [Small.{v} R[X]] :
    HasFiniteFreeResolution R[X] P :=
  IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R[X]
    inferInstance (motive := fun N _ _ _ => HasFiniteFreeResolution R[X] N)
      (fun _ _ _ _ _ => inferInstance)
      (fun _ _ _ _ p e => have := quotient_prime R hR p; of_linearEquiv e.symm)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ f g hf hg he _ _ => of_shortExact_of_left_of_right f g hf hg he)

end polynomial

section MvPolynomial

theorem Module.HasFiniteFreeResolution.mvPolynomial_of_isNoetherianRing
    [IsNoetherianRing R] [Small.{v, u} R] (σ : Type w) [Finite σ]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial σ R) P]
    [Module.Finite (MvPolynomial σ R) P] : HasFiniteFreeResolution (MvPolynomial σ R) P := by
  have : Small.{max u w} R := small_lift.{u, w, u} R
  let motive : Type w → Prop := fun σ =>
    ∀ (M : Type (max u w)) [AddCommGroup M] [Module (MvPolynomial σ R) M]
      [Module.Finite (MvPolynomial σ R) M], HasFiniteFreeResolution (MvPolynomial σ R) M
  have hm : motive σ := by
    refine Finite.induction_empty_option ?_ ?_ ?_ σ
    · intro α β e hα M _ _ _
      let eσ : MvPolynomial α R ≃+* MvPolynomial β R := (MvPolynomial.renameEquiv R e).toRingEquiv
      let : Module (MvPolynomial α R) M := Module.compHom M eσ.toRingHom
      have : RingHomInvPair eσ.toRingHom eσ.symm.toRingHom := RingHomInvPair.of_ringEquiv eσ
      have : RingHomInvPair eσ.symm.toRingHom eσ.toRingHom := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := Module.compHom.self_equiv eσ.symm.toRingHom eσ.toRingHom M
      have : Module.Finite (MvPolynomial α R) M := Module.Finite.of_surjective _ eM.surjective
      exact of_semilinearEquiv (MvPolynomial α R) M (MvPolynomial β R) M eM.symm
    · intro M _ _ _
      let eσ : R ≃+* MvPolynomial PEmpty R := (MvPolynomial.isEmptyAlgEquiv.{u, w} R PEmpty).symm
      let : Module R M := Module.compHom M eσ.toRingHom
      have : RingHomInvPair eσ.toRingHom eσ.symm.toRingHom := RingHomInvPair.of_ringEquiv eσ
      have : RingHomInvPair eσ.symm.toRingHom eσ.toRingHom := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := Module.compHom.self_equiv eσ.symm.toRingHom eσ.toRingHom M
      have : Module.Finite R M := Module.Finite.of_surjective _ eM.surjective
      have : Small.{u} M := Module.Finite.small.{u} R M
      have : HasFiniteFreeResolution R (Shrink.{u} M) := hR (Shrink.{u} M) inferInstance
      have : HasFiniteFreeResolution R M := of_shrink.{u} R M
      exact of_semilinearEquiv R M (MvPolynomial PEmpty R) M eM.symm
    · intro α _ hα M _ _ _
      let A := Polynomial (MvPolynomial α R)
      let B := MvPolynomial (Option α) R
      let eσ : A ≃+* B := (MvPolynomial.optionEquivLeft R α).symm.toRingEquiv
      let : Module A M := Module.compHom M eσ.toRingHom
      have : RingHomInvPair eσ.toRingHom eσ.symm.toRingHom := RingHomInvPair.of_ringEquiv eσ
      have : RingHomInvPair eσ.symm.toRingHom eσ.toRingHom := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := Module.compHom.self_equiv eσ.symm.toRingHom eσ.toRingHom M
      have : Module.Finite A M := Module.Finite.of_surjective _ eM.surjective
      have : HasFiniteFreeResolution A M := polynomial_of_isNoetherianRing
        (MvPolynomial α R) (fun N _ _ hN => hα N) M
      exact of_semilinearEquiv A M B M eM.symm
  have : Small.{max u w, v} P := Module.Finite.small (MvPolynomial σ R) P
  have : HasFiniteFreeResolution (MvPolynomial σ R) (Shrink.{max u w} P) := hm (Shrink.{max u w} P)
  exact of_shrink.{max u w} (MvPolynomial σ R) P

end MvPolynomial
