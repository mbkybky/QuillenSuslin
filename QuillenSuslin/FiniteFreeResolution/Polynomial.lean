/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.Quotient
import QuillenSuslin.FiniteFreeResolution.Exact

universe u v w z

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal

section polyMap

variable {P Q S : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup S] [Module R S] (f : P →ₗ[R] Q) (g : Q →ₗ[R] S)

private noncomputable def polyMap : PolynomialModule R P →ₗ[R[X]] PolynomialModule R Q where
  toFun := PolynomialModule.map R f
  map_add' _ _ := by simp
  map_smul' p q := by simp [PolynomialModule.map_smul R f p q]

@[simp]
private theorem polyMap_apply (p : PolynomialModule R P) (n : ℕ) :
    polyMap f p n = f (p n) := by
  rfl

private theorem polyMap_injective (hf : Function.Injective f) :
    Function.Injective (polyMap f) := by
  intro x y hxy
  apply Finsupp.ext
  intro n
  exact hf <| by simpa using congrArg (fun q => q n) hxy

private theorem polyMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (polyMap f) := by
  intro y
  induction y using PolynomialModule.induction_linear with
  | zero =>
      refine ⟨0, ?_⟩
      apply Finsupp.ext
      intro n
      simp
  | add y z hy hz =>
      rcases hy with ⟨y', rfl⟩
      rcases hz with ⟨z', rfl⟩
      refine ⟨y' + z', ?_⟩
      apply Finsupp.ext
      intro n
      simp
  | single n y =>
      rcases hf y with ⟨x, rfl⟩
      refine ⟨PolynomialModule.single R n x, ?_⟩
      apply Finsupp.ext
      intro m
      by_cases h : m = n
      · subst h
        simp [polyMap]
      · simp [polyMap]

private theorem polyMap_exact (h : Function.Exact f g) :
    Function.Exact (polyMap f) (polyMap g) := by
  intro y
  constructor
  · intro hy
    let z : PolynomialModule R P :=
      Finsupp.onFinset y.support
        (fun n =>
          if hn : n ∈ y.support then
            Classical.choose <| (h (y n)).1 <| by
              simpa using congrArg (fun q => q n) hy
          else
            0)
        (by
          intro n hn
          by_cases hmem : n ∈ y.support
          · exact hmem
          · simp [hmem] at hn)
    refine ⟨z, ?_⟩
    apply Finsupp.ext
    intro n
    by_cases hn : n ∈ y.support
    · have hy0 : g (y n) = 0 := by
        simpa using congrArg (fun q => q n) hy
      have hyn : y n ≠ 0 := Finsupp.mem_support_iff.mp hn
      have hchoose : f (Classical.choose ((h (y n)).1 hy0)) = y n :=
        Classical.choose_spec ((h (y n)).1 hy0)
      simpa [z, Finsupp.onFinset_apply, hyn] using hchoose
    · have hyn : y n = 0 := by
        simpa [Finsupp.mem_support_iff] using hn
      simp [z, Finsupp.onFinset_apply, hyn]
  · rintro ⟨z, rfl⟩
    apply Finsupp.ext
    intro n
    exact Function.Exact.apply_apply_eq_zero h (z n)

end polyMap

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

section polynomial

private noncomputable def polynomialModuleIdealMapCLinearMap (I : Ideal R) :
    PolynomialModule R I →ₗ[R[X]] Ideal.map (C : R →+* R[X]) I := by
  let inclX : PolynomialModule R I →ₗ[R[X]] PolynomialModule R R := polyMap I.subtype
  let φ0 : PolynomialModule R I →ₗ[R[X]] R[X] :=
    PolynomialModule.equivPolynomialSelf.toLinearMap.comp inclX
  refine LinearMap.codRestrict (Ideal.map (C : R →+* R[X]) I) φ0 ?_
  intro p
  refine Ideal.mem_map_C_iff.2 ?_
  intro n
  have hφ : (φ0 p).coeff n = (inclX p) n := by
    simp [φ0, PolynomialModule.equivPolynomialSelf, toFinsuppIso, coeff_ofFinsupp]
  rw [hφ]
  simp [inclX]

private theorem polynomialModuleIdealMapCLinearMap_coeff (I : Ideal R)
    (p : PolynomialModule R I) (n : ℕ) :
    (((polynomialModuleIdealMapCLinearMap I p : Ideal.map (C : R →+* R[X]) I) :
      R[X]).coeff n) = (p n : R) := by
  simp [polynomialModuleIdealMapCLinearMap, PolynomialModule.equivPolynomialSelf, toFinsuppIso,
    coeff_ofFinsupp]

private noncomputable def polynomialModuleIdealMapCLinearEquiv (I : Ideal R) :
    PolynomialModule R I ≃ₗ[R[X]] Ideal.map (C : R →+* R[X]) I := by
  let φ := polynomialModuleIdealMapCLinearMap I
  let ψ : Ideal.map (C : R →+* R[X]) I → PolynomialModule R I := fun f =>
    Finsupp.onFinset f.1.support
      (fun n => ⟨f.1.coeff n, Ideal.mem_map_C_iff.1 f.2 n⟩) <| by
        intro n hn
        have : f.1.coeff n ≠ 0 := by
          intro h0
          apply hn
          apply Subtype.ext
          simp [h0]
        exact (Polynomial.mem_support_iff).2 this
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    apply Finsupp.ext
    intro n
    apply Subtype.ext
    have hcoeff := congrArg (fun f : Ideal.map (C : R →+* R[X]) I => (f : R[X]).coeff n) hpq
    simpa [φ, polynomialModuleIdealMapCLinearMap_coeff] using hcoeff
  have hright : ∀ f : Ideal.map (C : R →+* R[X]) I, φ (ψ f) = f := by
    intro f
    apply Subtype.ext
    apply Polynomial.ext
    intro n
    rw [polynomialModuleIdealMapCLinearMap_coeff I (ψ f) n]
    by_cases hn : n ∈ f.1.support
    · simp [ψ, Finsupp.onFinset_apply]
    · have h0 : f.1.coeff n = 0 := by
        by_contra h0
        exact hn <| (Polynomial.mem_support_iff).2 h0
      simp [ψ, Finsupp.onFinset_apply, h0]
  have hleft : ∀ p : PolynomialModule R I, ψ (φ p) = p := by
    intro p
    exact hφ_inj (hright (φ p))
  exact
    { toLinearMap := φ
      invFun := ψ
      left_inv := hleft
      right_inv := hright }

/-- Push a finite free resolution of an `R`-ideal `I` to a resolution of `I · R[X]`. -/
theorem hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution
    (I : Ideal R) (hI : HasFiniteFreeResolution R I) :
    HasFiniteFreeResolution R[X] (Ideal.map (C : R →+* R[X]) I) := by
  rcases hI with ⟨n, hn⟩
  have liftLength : ∀ {P : Type u} [AddCommGroup P] [Module R P] {n : ℕ},
      HasFiniteFreeResolutionOfLength R P n →
        HasFiniteFreeResolutionOfLength R[X] (PolynomialModule R P) n := by
    intro P _ _ n hn
    induction hn with
    | zero P =>
        let e := PolynomialModule.polynomialTensorProductLEquivPolynomialModule R P
        let : Module.Finite R[X] (PolynomialModule R P) :=
          Module.Finite.of_surjective e.toLinearMap e.surjective
        let : Module.Free R[X] (PolynomialModule R P) := Module.Free.of_equiv e
        refine HasFiniteFreeResolutionOfLength.zero (PolynomialModule R P)
    | succ P n F K f g hf hg he hk ih =>
        let eF := PolynomialModule.polynomialTensorProductLEquivPolynomialModule R F
        let : Module.Finite R[X] (PolynomialModule R F) :=
          Module.Finite.of_surjective eF.toLinearMap eF.surjective
        let : Module.Free R[X] (PolynomialModule R F) := Module.Free.of_equiv eF
        let eK := PolynomialModule.polynomialTensorProductLEquivPolynomialModule R K
        let : Module.Finite R[X] (PolynomialModule R K) :=
          Module.Finite.of_surjective eK.toLinearMap eK.surjective
        refine HasFiniteFreeResolutionOfLength.succ (PolynomialModule R P) n
          (PolynomialModule R F) (PolynomialModule R K) (polyMap f) (polyMap g) ?_ ?_ ?_ ih
        · exact polyMap_injective f hf
        · exact polyMap_surjective g hg
        · exact polyMap_exact f g he
  exact hasFiniteFreeResolution_of_linearEquiv
    (polynomialModuleIdealMapCLinearEquiv I) ⟨n, liftLength hn⟩

/-- The canonical `R`-algebra equivalence `(R ⧸ I)[X] ≃ R[X] ⧸ I·R[X]`. -/
noncomputable def polynomialQuotientEquiv (I : Ideal R) :
    (R ⧸ I)[X] ≃ₐ[R] R[X] ⧸ I.map (C : R →+* R[X]) :=
  have h : RingHom.ker (mapAlgHom (Ideal.Quotient.mkₐ R I)) = I.map (C : R →+* R[X]) := by
    apply Eq.trans (ker_mapRingHom (Ideal.Quotient.mkₐ R I).toRingHom)
    congr
    simp
  (quotientKerAlgEquivOfSurjective <| map_surjective _ <| Quotient.mkₐ_surjective R I).symm.trans <|
    quotientEquivAlgOfEq _ h

/-- Over a domain, the principal ideal `(f)` is linearly equivalent to the ambient ring. -/
noncomputable def linearEquiv_mul_spanSingleton [IsDomain R] {f : R}
    (hf : f ≠ 0) : R ≃ₗ[R] (Ideal.span ({f} : Set R) : Ideal R) :=
  Ideal.isoBaseOfIsPrincipal <| (Submodule.ne_bot_iff (span {f})).mpr
    ⟨f, mem_span_singleton_self f, hf⟩

/-- If `P ⊂ R[X]` is an ideal over a Noetherian domain `R` with `P ∩ R = (0)`, then there exists
  `d ≠ 0` and `f ∈ P` such that `d • P ⊆ (f)`. -/
theorem exists_nonzero_C_mul_mem_span_singleton [IsDomain R] [IsNoetherianRing R] {P : Ideal (R[X])}
   (hPne : P ≠ ⊥) : ∃ d : R, d ≠ 0 ∧ ∃ f : R[X], f ∈ P ∧ f ≠ 0 ∧
      ∀ g ∈ P, C d * g ∈ Ideal.span ({f} : Set (R[X])) := by
  classical
  have hPfg : P.FG := IsNoetherian.noetherian P
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
      have : Polynomial.map i p0 = 0 := by simpa [Pext, hbot] using hp0Pext
      simpa using this
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
  have hq0 : ∀ a : ↥s, ∃ q : K[X], q * fK = (a : R[X]).map i := by
    intro a
    have haP : (a : R[X]) ∈ P := by
      simpa [hs] using (Ideal.subset_span a.2 : (a : R[X]) ∈ Ideal.span (s : Set (R[X])))
    have haPext : (a : R[X]).map i ∈ Pext := Ideal.mem_map_of_mem (Polynomial.mapRingHom i) haP
    have haSpan : (a : R[X]).map i ∈ Ideal.span ({fK} : Set K[X]) := by
      simpa [hPext_span] using haPext
    exact (Ideal.mem_span_singleton'.1 haSpan)
  choose q hq using hq0
  let v : ↥s → K[X] := fun a => (a : R[X]).map i
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
  have hqInt : ∀ a : ↥s, IsLocalization.IsInteger (R[X]) ((b : R[X]) • q a) := by
    intro a
    exact hb (q a) (Finset.mem_biUnion.2 ⟨a, by simp, by simp⟩)
  choose qR hqR using hqInt
  have hcInt : ∀ a : ↥s, IsLocalization.IsInteger (R[X]) ((b : R[X]) • c a) := by
    intro a
    exact hb (c a) (Finset.mem_biUnion.2 ⟨a, by simp, by simp⟩)
  choose cR hcR using hcInt
  have hqR' : ∀ a : ↥s, Polynomial.map i (qR a) = C (i d) * q a := by
    intro a
    simpa [Algebra.smul_def, hbEq, Polynomial.map_C] using hqR a
  have hcR' : ∀ a : ↥s, Polynomial.map i (cR a) = C (i d) * c a := by
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
  have hgen : ∀ a : ↥s, C (d * d) * (a : R[X]) ∈ Ideal.span ({f} : Set (R[X])) := by
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

private theorem hasFiniteFreeResolution_quotient_prime_aux [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P) : ∀ I : Ideal R, ∀ q : PrimeSpectrum R[X],
    Ideal.comap (C : R →+* R[X]) q.1 = I → HasFiniteFreeResolution (R[X]) (R[X] ⧸ q.1) := by
  -- Noetherian induction on the contraction `p.1 ∩ R`.
  let A : Type u := R[X]
  let contr : PrimeSpectrum A → Ideal R := fun q => Ideal.comap (C : R →+* A) q.1
  refine IsNoetherian.induction ?_
  intro I ih q hqI
  let P : Ideal A := q.1
  have : P.IsPrime := q.2
  have hcomap : Ideal.comap (C : R →+* A) P = I := hqI
  have hIA_le_P : Ideal.map (C : R →+* A) I ≤ P :=
    (Ideal.map_le_iff_le_comap).2 <| by simp [hcomap]
  let IA : Ideal A := Ideal.map (C : R →+* A) I
  by_cases hPIA : P = IA
  · have hI_res : HasFiniteFreeResolution R I := hR I inferInstance
    have hIA_res : HasFiniteFreeResolution A IA :=
      hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution I hI_res
    have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free A
    have hquot : HasFiniteFreeResolution A (A ⧸ IA) :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle IA.subtype (Submodule.mkQ IA)
        Subtype.coe_injective (Submodule.mkQ_surjective IA)
        (by exact LinearMap.exact_subtype_mkQ IA) hIA_res hA
    have hquotP : HasFiniteFreeResolution A (A ⧸ P) :=
      hasFiniteFreeResolution_of_linearEquiv (Submodule.quotEquivOfEq IA P hPIA.symm) hquot
    exact hquotP
  · have hIprime : Ideal.IsPrime I := by
      simpa [hcomap] using show (Ideal.comap (C : R →+* A) P).IsPrime from inferInstance
    let R₀ : Type u := R ⧸ I
    let A₀ : Type u := R₀[X]
    let B : Type u := A ⧸ IA
    let π : A →+* B := Ideal.Quotient.mk IA
    let Pbar : Ideal B := Ideal.map π P
    let e : A₀ ≃+* B := Ideal.polynomialQuotientEquivQuotientPolynomial I
    let P₀ : Ideal A₀ := Ideal.comap e.toRingHom Pbar
    have hPbar_ne : Pbar ≠ ⊥ := by
      intro hbot
      have hle : P ≤ RingHom.ker π := (P.map_eq_bot_iff_le_ker π).1 hbot
      have hker : RingHom.ker π = IA := IA.mk_ker
      have hP_le_IA : P ≤ IA := hker ▸ hle
      exact hPIA (le_antisymm hP_le_IA hIA_le_P)
    have hP₀_ne : P₀ ≠ ⊥ := by
      intro hbot
      have : Ideal.map e.toRingHom P₀ = Pbar :=
        Ideal.map_comap_of_surjective e.toRingHom e.surjective Pbar
      have : Pbar = Ideal.map e.toRingHom ⊥ := by rw [← this, hbot]
      rw [show (Ideal.map e.toRingHom ⊥ : Ideal B) = ⊥ by simp] at this
      exact hPbar_ne this
    obtain ⟨d₀, hd₀, f₀, hf₀P₀, hf₀ne, hmul₀⟩ := exists_nonzero_C_mul_mem_span_singleton hP₀_ne
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
    let Psub : Submodule A B := (Pbar : Submodule B B).restrictScalars A
    let Fsub : Submodule A B := (Fbar : Submodule B B).restrictScalars A
    have hFsub_le : Fsub ≤ Psub := by
      intro x hx
      exact hFbar_le hx
    let K : Submodule A Psub := Submodule.comap Psub.subtype Fsub
    let N := Psub ⧸ K
    let acgN : AddCommGroup N := Submodule.Quotient.addCommGroup K
    let : AddCommMonoid N := acgN.toAddCommMonoid
    have hsmul_d_mem_K : ∀ y : Psub, (C d : A) • y ∈ K := by
      intro y
      have hyF : ((C d : A) • (y : B)) ∈ Fsub := by
        have hyFmul : (π (C d) : B) * (y : B) ∈ Fsub := by
          have : (Ideal.Quotient.mk IA (C d) : B) * (y : B) ∈ Fbar := hmul_bar (y : B) y.2
          simpa [Fsub, π] using this
        have hsmul : ((C d : A) • (y : B)) = (π (C d) : B) * (y : B) := by
          have hAlgebraMap : (algebraMap A B) = π := rfl
          simpa [hAlgebraMap] using (Algebra.smul_def (C d : A) (y : B))
        exact hsmul ▸ hyFmul
      exact hyF
    have hN : HasFiniteFreeResolution A N := by
      have hsmul_I_mem_K : ∀ r : R, r ∈ I → ∀ y : Psub, (C r : A) • y ∈ K := by
        intro r hrI y
        have hCrIA : (C r : A) ∈ IA := Ideal.mem_map_of_mem (C : R →+* A) hrI
        have hπCr : (π (C r) : B) = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hCrIA
        have hy0 : (C r : A) • (y : B) = 0 := by
          have hAlgebraMap : (algebraMap A B) = π := rfl
          rw [Algebra.smul_def, hAlgebraMap, hπCr]
          exact zero_mul _
        have hyF : (C r : A) • (y : B) ∈ Fsub := by simp [hy0]
        exact hyF
      let motive : ∀ (M : Type u), [AddCommGroup M] → [Module A M] → [Module.Finite A M] → Prop :=
        fun M _ _ _ => (∀ x : M, (C d : A) • x = 0) →
          (∀ r : R, r ∈ I → ∀ x : M, (C r : A) • x = 0) → HasFiniteFreeResolution A M
      have hN' : motive N := by
        refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A
          inferInstance (motive := motive) ?_ ?_ ?_
        · intro M _ _ _ _ _ _
          exact hasFiniteFreeResolution_of_subsingleton M
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
          exact hasFiniteFreeResolution_of_linearEquiv eM.symm hquot
        · intro M₁ _ _ _ M₂ _ _ _ M₃ _ _ _ f g hf hg hfg h₁ h₃ hAnn_d2 hAnn_I2
          have hAnn_d1 : ∀ x : M₁, (C d : A) • x = 0 := by
            intro x
            apply hf
            have : f ((C d : A) • x) = 0 := by simpa using hAnn_d2 (f x)
            simpa using this
          have hAnn_I1 : ∀ r : R, r ∈ I → ∀ x : M₁, (C r : A) • x = 0 := by
            intro r hrI x
            apply hf
            have : f ((C r : A) • x) = 0 := by simpa using hAnn_I2 r hrI (f x)
            simpa using this
          have hAnn_d3 : ∀ x : M₃, (C d : A) • x = 0 := by
            intro z
            rcases hg z with ⟨y, rfl⟩
            simpa only [map_smul, map_zero] using congrArg g (hAnn_d2 y)
          have hAnn_I3 : ∀ r : R, r ∈ I → ∀ x : M₃, (C r : A) • x = 0 := by
            intro r hrI z
            rcases hg z with ⟨y, rfl⟩
            simpa only [map_smul, map_zero] using congrArg g (hAnn_I2 r hrI y)
          have h₁' : HasFiniteFreeResolution A M₁ := h₁ hAnn_d1 hAnn_I1
          have h₃' : HasFiniteFreeResolution A M₃ := h₃ hAnn_d3 hAnn_I3
          exact hasFiniteFreeResolution_of_shortExact_of_left_of_right f g hf hg hfg h₁' h₃'
      exact hN' (smul_zero_of_smul_mem K hsmul_d_mem_K) <|
        fun r hrI => smul_zero_of_smul_mem K (hsmul_I_mem_K r hrI)
    have hI_res : HasFiniteFreeResolution R I := hR I inferInstance
    have hIA_res : HasFiniteFreeResolution A IA :=
      hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution I hI_res
    have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free A
    have hB : HasFiniteFreeResolution A B :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle IA.subtype (Submodule.mkQ IA)
        Subtype.coe_injective (Submodule.mkQ_surjective IA)
        (by exact LinearMap.exact_subtype_mkQ IA) hIA_res hA
    have : IsDomain B := MulEquiv.isDomain A₀ e.symm.toMulEquiv
    have hFbar : HasFiniteFreeResolution A Fbar :=
      hasFiniteFreeResolution_of_linearEquiv
        ((linearEquiv_mul_spanSingleton hfbar_ne).restrictScalars A) hB
    have hK : HasFiniteFreeResolution A K :=
      have hFsub : HasFiniteFreeResolution A Fsub := by exact hFbar
      hasFiniteFreeResolution_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hFsub_le).symm hFsub
    have hPbar : HasFiniteFreeResolution A Psub := by
      -- Short exact sequence `0 → K → Psub → N → 0`.
      refine hasFiniteFreeResolution_of_shortExact_of_left_of_right
        ((K.subtype).restrictScalars A) (Submodule.mkQ K) Subtype.coe_injective
        (Submodule.mkQ_surjective K) ?_ hK hN
      exact LinearMap.exact_subtype_mkQ K
    let fIP : IA →ₗ[A] P := Submodule.inclusion hIA_le_P
    let gPP : P →ₗ[A] Pbar :=
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
      simpa [fIP] using congrArg (fun z : P => (z : A)) hxy
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
    have hP : HasFiniteFreeResolution A P :=
      -- Use `0 → IA → P → Pbar → 0`.
      hasFiniteFreeResolution_of_shortExact_of_left_of_right fIP gPP hfIP hgPP hexPP
        hIA_res <| by exact hPbar
    -- Finally, `0 → P → A → A ⧸ P → 0`.
    have hquot : HasFiniteFreeResolution A (A ⧸ P) :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle P.subtype (Submodule.mkQ P)
        Subtype.coe_injective (Submodule.mkQ_surjective P)
        (by exact LinearMap.exact_subtype_mkQ P) hP hA
    exact hquot

variable (R)

theorem hasFiniteFreeResolution_quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) := by
  exact hasFiniteFreeResolution_quotient_prime_aux hR (Ideal.comap (C : R →+* R[X]) p.1) p rfl

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem polynomial_hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] [Small.{v} R[X]] :
    HasFiniteFreeResolution R[X] P := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R[X]
    inferInstance (motive := fun N _ _ _ => HasFiniteFreeResolution R[X] N)
      (fun N _ _ _ _ => hasFiniteFreeResolution_of_subsingleton N)
      (fun _ _ _ _ p e => hasFiniteFreeResolution_of_linearEquiv e.symm
        (hasFiniteFreeResolution_quotient_prime R hR p))
      (fun N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ =>
        hasFiniteFreeResolution_of_shortExact_of_left_of_right f g hf hg hfg h₁ h₃)

end polynomial

private noncomputable def compatLinearEquiv {A : Type u} {B : Type w}
    [Semiring A] [Semiring B] {M : Type z} [AddCommMonoid M] [Module A M] [Module B M]
    (e : A ≃+* B) (hcompat : ∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) := by
  let : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
  show M ≃ₛₗ[(e : A →+* B)] M
  exact {
    toFun := id
    invFun := id
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' := by
      intro a x
      exact (hcompat a x).symm
  }

private theorem hasFiniteFreeResolutionOfLength_of_ringEquiv
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Small.{z} A] [Small.{z} B]
    (e : A ≃+* B) :
    ∀ {M : Type z} [AddCommGroup M] [Module A M] {n : ℕ},
      HasFiniteFreeResolutionOfLength A M n →
      ∀ [Module B M], (∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) →
        HasFiniteFreeResolutionOfLength B M n := by
  intro M _ _ n hn
  induction hn with
  | zero M =>
      intro _ hcompat
      letI : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
      letI : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
      let eM := compatLinearEquiv e hcompat
      have : Module.Finite B M := (LinearMap.finite_iff_of_bijective
        (eM : M →ₛₗ[(e : A →+* B)] M) eM.bijective).1 inferInstance
      have : Module.Free B M := Module.Free.of_equiv eM
      exact HasFiniteFreeResolutionOfLength.zero M
  | succ M n F K f g hf hg he hk ih =>
      intro _ hcompatM
      letI : RingHomInvPair (e : A →+* B) (e.symm : B →+* A) := RingHomInvPair.of_ringEquiv e
      letI : RingHomInvPair (e.symm : B →+* A) (e : A →+* B) := RingHomInvPair.of_ringEquiv_symm e
      let : Module B F := Module.compHom F (e.symm : B →+* A)
      let : Module B K := Module.compHom K (e.symm : B →+* A)
      have hcompatF : ∀ (a : A) (x : F), (e a : B) • x = (a : A) • x := by
        intro a x
        change ((e.symm (e a) : A) • x) = a • x
        simp
      have hcompatK : ∀ (a : A) (x : K), (e a : B) • x = (a : A) • x := by
        intro a x
        change ((e.symm (e a) : A) • x) = a • x
        simp
      let eF := compatLinearEquiv e hcompatF
      let eK := compatLinearEquiv e hcompatK
      have : Module.Finite B F := (LinearMap.finite_iff_of_bijective
        (eF : F →ₛₗ[(e : A →+* B)] F) eF.bijective).1 inferInstance
      have : Module.Free B F := Module.Free.of_equiv eF
      have : Module.Finite B K := (LinearMap.finite_iff_of_bijective
        (eK : K →ₛₗ[(e : A →+* B)] K) eK.bijective).1 inferInstance
      let fB : K →ₗ[B] F :=
        { toFun := f
          map_add' := f.map_add
          map_smul' := by
            intro b x
            exact f.map_smul (e.symm b) x }
      let gB : F →ₗ[B] M :=
        { toFun := g
          map_add' := g.map_add
          map_smul' := by
            intro b x
            change g ((e.symm b : A) • x) = b • g x
            rw [g.map_smul]
            simpa using (hcompatM (e.symm b) (g x)).symm }
      refine HasFiniteFreeResolutionOfLength.succ M n F K fB gB
        hf
        hg
        he
        (ih hcompatK)

private theorem hasFiniteFreeResolution_of_ringEquiv
    {A : Type u} {B : Type w} [CommRing A] [CommRing B] [Small.{z} A] [Small.{z} B]
    (e : A ≃+* B) :
    ∀ {M : Type z} [AddCommGroup M] [Module A M],
      HasFiniteFreeResolution A M →
      ∀ [Module B M], (∀ (a : A) (x : M), (e a : B) • x = (a : A) • x) →
        HasFiniteFreeResolution B M := by
  intro M _ _ hM _ hcompat
  rcases hM with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionOfLength_of_ringEquiv e hn hcompat⟩

section MvPolynomial

theorem mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing
    [IsNoetherianRing R] [Small.{v, u} R] (σ : Type w) [Finite σ]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial σ R) P]
    [Module.Finite (MvPolynomial σ R) P] : HasFiniteFreeResolution (MvPolynomial σ R) P := by
  have : Small.{max u w} R := small_lift.{u, w, u} R
  let motive : Type w → Prop := fun σ =>
    ∀ (M : Type (max u w)) [AddCommGroup M] [Module (MvPolynomial σ R) M]
      [Module.Finite (MvPolynomial σ R) M], HasFiniteFreeResolution (MvPolynomial σ R) M
  have hmotive : motive σ := by
    refine Finite.induction_empty_option ?_ ?_ ?_ σ
    · intro α β e hα M _ _ _
      let eσ : MvPolynomial α R ≃+* MvPolynomial β R := (MvPolynomial.renameEquiv R e).toRingEquiv
      let : Module (MvPolynomial α R) M := Module.compHom M (eσ : MvPolynomial α R →+* MvPolynomial β R)
      letI : RingHomInvPair (eσ : MvPolynomial α R →+* MvPolynomial β R)
        (eσ.symm : MvPolynomial β R →+* MvPolynomial α R) := RingHomInvPair.of_ringEquiv eσ
      letI : RingHomInvPair (eσ.symm : MvPolynomial β R →+* MvPolynomial α R)
        (eσ : MvPolynomial α R →+* MvPolynomial β R) := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := compatLinearEquiv eσ (fun _ (_ : M) => rfl)
      have : Module.Finite (MvPolynomial α R) M := (LinearMap.finite_iff_of_bijective
        (eM : M →ₛₗ[(eσ : MvPolynomial α R →+* MvPolynomial β R)] M) eM.bijective).2
          inferInstance
      exact hasFiniteFreeResolution_of_ringEquiv eσ (hα M) (fun a (x : M) => rfl)
    · intro M _ _ _
      let eσ : R ≃+* MvPolynomial PEmpty R := (MvPolynomial.isEmptyAlgEquiv R PEmpty).symm.toRingEquiv
      let : Module R M := Module.compHom M (eσ : R →+* MvPolynomial PEmpty R)
      letI : RingHomInvPair (eσ : R →+* MvPolynomial PEmpty R)
        (eσ.symm : MvPolynomial PEmpty R →+* R) := RingHomInvPair.of_ringEquiv eσ
      letI : RingHomInvPair (eσ.symm : MvPolynomial PEmpty R →+* R)
        (eσ : R →+* MvPolynomial PEmpty R) := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := compatLinearEquiv eσ (fun _ (_ : M) => rfl)
      have : Module.Finite R M := (LinearMap.finite_iff_of_bijective
        (eM : M →ₛₗ[(eσ : R →+* MvPolynomial PEmpty R)] M) eM.bijective).2 inferInstance
      refine hasFiniteFreeResolution_of_ringEquiv eσ ?_ (fun _ _ => rfl)
      have : Small.{u} M := Module.Finite.small.{u} R M
      let eM : Shrink.{u} M ≃ₗ[R] M := Shrink.linearEquiv R M
      have : Module.Finite R (Shrink.{u} M) := Module.Finite.equiv eM.symm
      refine hasFiniteFreeResolution_of_linearEquiv eM (hR (Shrink.{u} M) inferInstance)
    · intro α _ hα M _ _ _
      let A := Polynomial (MvPolynomial α R)
      let B := MvPolynomial (Option α) R
      let eσ : A ≃+* B := (MvPolynomial.optionEquivLeft R α).symm.toRingEquiv
      let : Module A M := Module.compHom M (eσ : A →+* B)
      letI : RingHomInvPair (eσ : A →+* B) (eσ.symm : B →+* A) := RingHomInvPair.of_ringEquiv eσ
      letI : RingHomInvPair (eσ.symm : B →+* A) (eσ : A →+* B) := RingHomInvPair.of_ringEquiv_symm eσ
      let eM := compatLinearEquiv eσ (fun _ (_ : M) => rfl)
      have : Module.Finite A M := (LinearMap.finite_iff_of_bijective
        (eM : M →ₛₗ[(eσ : A →+* B)] M) eM.bijective).2 inferInstance
      have hA : HasFiniteFreeResolution A M :=
        polynomial_hasFiniteFreeResolution_of_isNoetherianRing (MvPolynomial α R)
          (fun N _ _ hN => hα N) M
      exact hasFiniteFreeResolution_of_ringEquiv eσ hA (fun _ _ => rfl)
  have : Small.{max u w, v} P := Module.Finite.small (MvPolynomial σ R) P
  let eP : Shrink.{max u w} P ≃ₗ[MvPolynomial σ R] P := Shrink.linearEquiv (MvPolynomial σ R) P
  have : Module.Finite (MvPolynomial σ R) (Shrink.{max u w} P) := Module.Finite.equiv eP.symm
  exact hasFiniteFreeResolution_of_linearEquiv eP (hmotive (Shrink.{max u w} P))

end MvPolynomial
