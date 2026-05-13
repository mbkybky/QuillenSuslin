/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

public section

namespace Module

open scoped TensorProduct

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

section Free

lemma exists_isLocalizedModule_map_surjective_of_surjective [Module.FinitePresentation R M]
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    {Mₚ : Type*} [AddCommGroup Mₚ] [Module R Mₚ] [Module (Rₚ) Mₚ] [IsScalarTower R (Rₚ) Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    {Nₚ : Type*} [AddCommGroup Nₚ] [Module R Nₚ] [Module (Rₚ) Nₚ] [IsScalarTower R (Rₚ) Nₚ]
    (g : N →ₗ[R] Nₚ) [IsLocalizedModule.AtPrime p g] {ϕ : Mₚ →ₗ[Rₚ] Nₚ} (hϕ : Function.Surjective ϕ) :
    ∃ φ : M →ₗ[R] N, Function.Surjective (IsLocalizedModule.map p.primeCompl f g φ) := by
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl g (ϕ.restrictScalars R ∘ₗ f)
  refine ⟨φ, ?_⟩
  have hmap : IsLocalizedModule.map p.primeCompl f g φ = s • ϕ.restrictScalars R := by
    apply IsLocalizedModule.ext p.primeCompl f (IsLocalizedModule.map_units g)
    ext x
    simpa only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply] using
      LinearMap.congr_fun hφ x
  rw [hmap]
  intro y
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units (S := p.primeCompl) (f := g) s)).2 y
  obtain ⟨x, rfl⟩ := hϕ z
  exact ⟨x, hz⟩

lemma exists_localizedModule_map_away_surjective_of_map_atPrime_surjective [Module.Finite R N]
    (p : Ideal R) [p.IsPrime]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (LocalizedModule.map p.primeCompl φ)) :
    ∃ a ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Q := N ⧸ LinearMap.range φ
  have hQp : Subsingleton (LocalizedModule p.primeCompl Q) := by
    rw [LocalizedModule.subsingleton_iff]
    intro q
    refine Submodule.Quotient.induction_on (p := LinearMap.range φ) q ?_
    intro n
    obtain ⟨x, hx⟩ := hφ (LocalizedModule.mk n (1 : p.primeCompl))
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hx
      obtain ⟨u, hu⟩ := hx
      refine ⟨u * s, (u * s).2, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨(u : R) • m, ?_⟩
      have hu' : (u : R) • φ m = (u : R) • ((s : R) • n) := by
        simpa using hu
      calc
        φ ((u : R) • m) = (u : R) • φ m := map_smul φ (u : R) m
        _ = (u : R) • ((s : R) • n) := hu'
        _ = ((u : R) * (s : R)) • n := by rw [mul_smul]
  obtain ⟨a, ha, hQa⟩ := LocalizedModule.exists_subsingleton_away (M := Q) p
  refine ⟨a, ha, ?_⟩
  intro y
  induction y using LocalizedModule.induction_on with
  | h n s =>
    obtain ⟨r, hrmem, hr⟩ := (LocalizedModule.subsingleton_iff (S := Submonoid.powers a)
      (M := Q)).mp hQa (Submodule.Quotient.mk n)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hr
    obtain ⟨m, hm⟩ := hr
    refine ⟨LocalizedModule.mk m (⟨r, hrmem⟩ * s), ?_⟩
    rw [LocalizedModule.map_mk, hm]
    exact LocalizedModule.mk_cancel_common_left ⟨r, hrmem⟩ s n

lemma bijective_of_surjective_of_finite_of_free_of_finrank_eq
    [Module.Finite R M] [Module.Free R M] [Module.Free R N]
    (h : finrank R M = finrank R N) {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Bijective f := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨fun x y _ ↦ ?_, hf⟩
    calc
      x = (1 : R) • x := (one_smul R x).symm
      _ = (0 : R) • x := by rw [Subsingleton.elim (1 : R) 0]
      _ = 0 := zero_smul R x
      _ = (0 : R) • y := (zero_smul R y).symm
      _ = (1 : R) • y := by rw [Subsingleton.elim (0 : R) 1]
      _ = y := one_smul R y
  · have : Module.Finite R N := Module.Finite.of_surjective f hf
    let e : M ≃ₗ[R] N := LinearEquiv.ofFinrankEq M N h
    have hsurj : Function.Surjective (e.symm.toLinearMap ∘ₗ f : Module.End R M) :=
      e.symm.surjective.comp hf
    have hinj : Function.Injective (e.symm.toLinearMap ∘ₗ f : Module.End R M) :=
      Module.End.injective_of_surjective (R := R) (M := M) hsurj
    exact ⟨fun x y hxy ↦ hinj (by simp [hxy]), hf⟩

lemma isLocalizedModule_away_map_atPrime_away
    (a : R) (m : Ideal R) [m.IsPrime] (P : Type*) [AddCommGroup P] [Module R P] :
    IsLocalizedModule.Away (algebraMap R (Localization.AtPrime m) a)
      (LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) P) :
        LocalizedModule.AtPrime m P →ₗ[Localization.AtPrime m]
          LocalizedModule.AtPrime m (LocalizedModule.Away a P)) := by
  let aₘ : Localization.AtPrime m := algebraMap R (Localization.AtPrime m) a
  let fP : LocalizedModule.AtPrime m P →ₗ[Localization.AtPrime m]
      LocalizedModule.AtPrime m (LocalizedModule.Away a P) :=
    LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) P)
  have hK_smul_target (n : ℕ) (z : LocalizedModule.Away a P) (t : m.primeCompl) :
      aₘ ^ n • (LocalizedModule.mk z t : LocalizedModule.AtPrime m (LocalizedModule.Away a P)) =
        LocalizedModule.mk ((a ^ n) • z) t := by
    rw [show aₘ ^ n = LocalizedModule.mk (a ^ n) (1 : m.primeCompl) by
      change ((algebraMap R (Localization.AtPrime m)) a) ^ n = _
      rw [← map_pow]
      rfl]
    trans LocalizedModule.mk ((a ^ n) • z) ((1 : m.primeCompl) * t)
    · exact LocalizedModule.mk_smul_mk (a ^ n) z (1 : m.primeCompl) t
    · simp
  have hK_smul_source (n : ℕ) (p : P) (t : m.primeCompl) :
      aₘ ^ n • (LocalizedModule.mk p t : LocalizedModule.AtPrime m P) =
        LocalizedModule.mk ((a ^ n) • p) t := by
    rw [show aₘ ^ n = LocalizedModule.mk (a ^ n) (1 : m.primeCompl) by
      change ((algebraMap R (Localization.AtPrime m)) a) ^ n = _
      rw [← map_pow]
      rfl]
    trans LocalizedModule.mk ((a ^ n) • p) ((1 : m.primeCompl) * t)
    · exact LocalizedModule.mk_smul_mk (a ^ n) p (1 : m.primeCompl) t
    · simp
  have hscalar (r : R) (p : P) (u : Submonoid.powers a) :
      r • (LocalizedModule.mk p u : LocalizedModule.Away a P) =
        LocalizedModule.mk (r • p) u := by
    rw [IsLocalizedModule.mk_eq_mk']
    rw [← IsLocalizedModule.mk'_smul]
    rw [← IsLocalizedModule.mk_eq_mk']
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro q
    rcases q.2 with ⟨n, hn⟩
    rw [← hn]
    refine (Module.End.isUnit_iff _).mpr ?_
    change Function.Bijective (fun y : LocalizedModule.AtPrime m (LocalizedModule.Away a P) =>
      aₘ ^ n • y)
    have hunit : IsUnit ((algebraMap R (Module.End R (LocalizedModule.Away a P))) (a ^ n)) :=
      IsLocalizedModule.map_units (S := Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) P) ⟨a ^ n, ⟨n, rfl⟩⟩
    have hbij : Function.Bijective (fun z : LocalizedModule.Away a P => (a ^ n) • z) := by
      convert (Module.End.isUnit_iff _).mp hunit using 1
    refine ⟨?_, ?_⟩
    · intro y₁ y₂ hy
      induction y₁, y₂ using LocalizedModule.induction_on₂ with
      | h z₁ z₂ s t =>
        change aₘ ^ n •
            (LocalizedModule.mk z₁ s : LocalizedModule.AtPrime m (LocalizedModule.Away a P)) =
          aₘ ^ n •
            (LocalizedModule.mk z₂ t : LocalizedModule.AtPrime m (LocalizedModule.Away a P)) at hy
        rw [hK_smul_target n z₁ s, hK_smul_target n z₂ t] at hy
        rw [LocalizedModule.mk_eq] at hy ⊢
        obtain ⟨u, hu⟩ := hy
        refine ⟨u, ?_⟩
        apply hbij.1
        calc
          (a ^ n) • (u • t • z₁) = u • t • ((a ^ n) • z₁) := by
            simp [Submonoid.smul_def, smul_smul, mul_comm, mul_left_comm, mul_assoc]
          _ = u • s • ((a ^ n) • z₂) := hu
          _ = (a ^ n) • (u • s • z₂) := by
            simp [Submonoid.smul_def, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    · intro y
      induction y using LocalizedModule.induction_on with
      | h z t =>
        obtain ⟨z', hz'⟩ := hbij.2 z
        refine ⟨LocalizedModule.mk z' t, ?_⟩
        change aₘ ^ n •
            (LocalizedModule.mk z' t : LocalizedModule.AtPrime m (LocalizedModule.Away a P)) =
          LocalizedModule.mk z t
        rw [hK_smul_target n z' t]
        simp [hz']
  · intro y
    induction y using LocalizedModule.induction_on with
    | h z t =>
      induction z using LocalizedModule.induction_on with
      | h p u =>
        rcases u.2 with ⟨n, hn⟩
        refine ⟨⟨LocalizedModule.mk p t, ⟨aₘ ^ n, ⟨n, rfl⟩⟩⟩, ?_⟩
        change aₘ ^ n • (LocalizedModule.mk (LocalizedModule.mk p u) t :
            LocalizedModule.AtPrime m (LocalizedModule.Away a P)) = fP (LocalizedModule.mk p t)
        rw [hK_smul_target n (LocalizedModule.mk p u) t]
        have hcancel : (a ^ n) • (LocalizedModule.mk p u : LocalizedModule.Away a P) =
            LocalizedModule.mk p (1 : Submonoid.powers a) := by
          rw [IsLocalizedModule.mk_eq_mk']
          rw [← IsLocalizedModule.mk'_smul]
          rw [← IsLocalizedModule.mk_eq_mk']
          convert LocalizedModule.mk_cancel_common_left u (1 : Submonoid.powers a) p using 1
          simp [Submonoid.smul_def, hn]
        rw [hcancel]
        rw [LocalizedModule.map_mk, LocalizedModule.mkLinearMap_apply]
  · intro x₁ x₂ hxy
    induction x₁, x₂ using LocalizedModule.induction_on₂ with
    | h p q s t =>
      change fP (LocalizedModule.mk p s) = fP (LocalizedModule.mk q t) at hxy
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.mkLinearMap_apply,
        LocalizedModule.mkLinearMap_apply] at hxy
      rw [LocalizedModule.mk_eq] at hxy
      obtain ⟨u, hu⟩ := hxy
      simp only [Submonoid.smul_def, smul_smul] at hu
      rw [hscalar ((u : R) * (t : R)) p (1 : Submonoid.powers a),
        hscalar ((u : R) * (s : R)) q (1 : Submonoid.powers a)] at hu
      rw [LocalizedModule.mk_eq] at hu
      obtain ⟨v, hv⟩ := hu
      rcases v.2 with ⟨n, hn⟩
      refine ⟨⟨aₘ ^ n, ⟨n, rfl⟩⟩, ?_⟩
      change aₘ ^ n • (LocalizedModule.mk p s : LocalizedModule.AtPrime m P) =
        aₘ ^ n • (LocalizedModule.mk q t : LocalizedModule.AtPrime m P)
      rw [hK_smul_source n p s, hK_smul_source n q t]
      rw [LocalizedModule.mk_eq]
      refine ⟨u, ?_⟩
      calc
        u • t • ((a ^ n) • p) = v • (((u : R) * (t : R)) • p) := by
          simp [Submonoid.smul_def, hn, smul_smul, mul_comm, mul_left_comm]
        _ = v • (((u : R) * (s : R)) • q) := by
          simpa [Submonoid.smul_def, smul_smul, mul_assoc] using hv
        _ = u • s • ((a ^ n) • q) := by
          simp [Submonoid.smul_def, hn, smul_smul, mul_comm, mul_left_comm]

lemma localized_map_bijective_of_surjective_of_rankAtStalk_eq [Module.Finite R M] [Module.Flat R M]
    [Module.Finite R N] [Module.Flat R N] (a : R) {φ : M →ₗ[R] N}
    (hφs : Function.Surjective (LocalizedModule.map (Submonoid.powers a) φ))
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) φ) := by
  let Rₐ := Localization.Away a
  let Mₐ := LocalizedModule.Away a M
  let Nₐ := LocalizedModule.Away a N
  let φₐ : Mₐ →ₗ[Rₐ] Nₐ := LocalizedModule.map (Submonoid.powers a) φ
  refine bijective_of_localized_maximal (φₐ.restrictScalars R) (fun m _ ↦ ?_)
  have : Function.Surjective (φₐ.restrictScalars R) := hφs
  have hφₐ : Function.Surjective (LocalizedModule.map m.primeCompl (φₐ.restrictScalars R)) :=
    LocalizedModule.map_surjective _ _ hφs
  let aₘ : Localization.AtPrime m := algebraMap R (Localization.AtPrime m) a
  let L := LocalizedModule m.primeCompl Rₐ
  letI : Algebra (Localization.AtPrime m) L :=
    LocalizedModule.algebraOfIsLocalization (T := Localization m.primeCompl) (S := m.primeCompl)
  letI : SMul (Localization.AtPrime m) L :=
    (inferInstance : Algebra (Localization.AtPrime m) L).toSMul
  letI : Algebra Rₐ L :=
    (LocalizedModule.numeratorRingHom (S := m.primeCompl) : Rₐ →+* L).toAlgebra
  have h_alg (r : R) (s : m.primeCompl) :
      (algebraMap (Localization.AtPrime m) L) (LocalizedModule.mk r s) =
        LocalizedModule.mk (algebraMap R Rₐ r) s := by
    exact LocalizedModule.algebraMap_mk (S := m.primeCompl) (A := Rₐ) r s
  have h_alg_one (r : R) :
      (algebraMap (Localization.AtPrime m) L) ((algebraMap R (Localization.AtPrime m)) r) =
        LocalizedModule.mk (algebraMap R Rₐ r) (1 : m.primeCompl) := by
    simpa using h_alg r 1
  haveI : IsLocalization.Away aₘ L := by
    refine IsLocalization.Away.mk aₘ ?_ ?_ ?_
    · change IsUnit ((algebraMap (Localization.AtPrime m) L)
        ((algebraMap R (Localization.AtPrime m)) a))
      rw [h_alg_one]
      simpa using (IsLocalization.Away.algebraMap_isUnit (S := Rₐ) a).map (algebraMap Rₐ L)
    · intro z
      induction z using LocalizedModule.induction_on with
      | h x t =>
        obtain ⟨⟨r, u⟩, hx⟩ := IsLocalization.surj (Submonoid.powers a) x
        rcases u.2 with ⟨n, hn⟩
        refine ⟨n, LocalizedModule.mk r t, ?_⟩
        rw [h_alg]
        change LocalizedModule.mk x t *
            ((algebraMap (Localization.AtPrime m) L) ((algebraMap R (Localization.AtPrime m)) a)) ^ n =
          LocalizedModule.mk (algebraMap R Rₐ r) t
        rw [h_alg_one]
        have hpow : LocalizedModule.mk ((algebraMap R Rₐ) a) (1 : m.primeCompl) ^ n =
            LocalizedModule.mk ((algebraMap R Rₐ) (a ^ n)) (1 : m.primeCompl) := by
          clear x r u hn hx
          induction n with
          | zero =>
            simp only [pow_zero, map_one]
            rw [← map_one (algebraMap Rₐ L)]
            rfl
          | succ n ih =>
            rw [pow_succ, ih, LocalizedModule.mk_mul_mk]
            simp [pow_succ, map_mul]
        rw [hpow, LocalizedModule.mk_mul_mk]
        simpa [hn, map_pow, mul_comm, mul_left_comm, mul_assoc] using
          congr_arg (fun y ↦ LocalizedModule.mk y t) hx
    · intro x y hxy
      induction x, y using LocalizedModule.induction_on₂ with
      | h r r' s t =>
        have hxy' : LocalizedModule.mk (algebraMap R Rₐ r) s =
            LocalizedModule.mk (algebraMap R Rₐ r') t := by
          simpa [h_alg] using hxy
        rw [LocalizedModule.mk_eq] at hxy'
        obtain ⟨u, hu⟩ := hxy'
        have hu' : algebraMap R Rₐ ((u : R) * (t : R) * r) =
            algebraMap R Rₐ ((u : R) * (s : R) * r') := by
          simpa [Algebra.smul_def, Submonoid.smul_def, mul_assoc] using hu
        obtain ⟨v, hv⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a) Rₐ).mp hu'
        rcases v.2 with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [show aₘ ^ n * LocalizedModule.mk r s = LocalizedModule.mk ((a ^ n) * r) s by
            rw [← map_pow]
            trans LocalizedModule.mk ((a ^ n) * r) ((1 : m.primeCompl) * s)
            · exact LocalizedModule.mk_mul_mk (S := m.primeCompl) (A := R)
            · simp,
          show aₘ ^ n * LocalizedModule.mk r' t = LocalizedModule.mk ((a ^ n) * r') t by
            rw [← map_pow]
            trans LocalizedModule.mk ((a ^ n) * r') ((1 : m.primeCompl) * t)
            · exact LocalizedModule.mk_mul_mk (S := m.primeCompl) (A := R)
            · simp]
        rw [LocalizedModule.mk_eq]
        refine ⟨u, ?_⟩
        simpa [Submonoid.smul_def, hn, mul_assoc, mul_left_comm, mul_comm] using hv
  let f : LocalizedModule.AtPrime m M →ₗ[Localization.AtPrime m] LocalizedModule.AtPrime m Mₐ :=
    LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  haveI : IsLocalizedModule.Away aₘ f := by
    dsimp [aₘ, f, Mₐ]
    exact isLocalizedModule_away_map_atPrime_away a m M
  let g : LocalizedModule.AtPrime m N →ₗ[Localization.AtPrime m] LocalizedModule.AtPrime m Nₐ :=
    LocalizedModule.map m.primeCompl (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
  haveI : IsLocalizedModule.Away aₘ g := by
    dsimp [aₘ, g, Nₐ]
    exact isLocalizedModule_away_map_atPrime_away a m N
  letI : Module L (LocalizedModule.AtPrime m Mₐ) :=
    IsLocalizedModule.module (A := L) (Submonoid.powers aₘ) f
  letI : IsScalarTower (Localization.AtPrime m) L (LocalizedModule.AtPrime m Mₐ) :=
    IsLocalizedModule.isScalarTower_module (A := L) (Submonoid.powers aₘ) f
  letI : Module L (LocalizedModule.AtPrime m Nₐ) :=
    IsLocalizedModule.module (A := L) (Submonoid.powers aₘ) g
  letI : IsScalarTower (Localization.AtPrime m) L (LocalizedModule.AtPrime m Nₐ) :=
    IsLocalizedModule.isScalarTower_module (A := L) (Submonoid.powers aₘ) g
  let ψ : LocalizedModule.AtPrime m Mₐ →ₗ[L] LocalizedModule.AtPrime m Nₐ :=
    (LocalizedModule.map m.primeCompl (φₐ.restrictScalars R)).extendScalarsOfIsLocalization
      (Submonoid.powers aₘ) L
  change Function.Bijective ψ
  rcases subsingleton_or_nontrivial L with hL | hL
  · refine ⟨fun x y _ ↦ ?_, hφₐ⟩
    calc
      x = (1 : L) • x := (one_smul L x).symm
      _ = (0 : L) • x := by rw [Subsingleton.elim (1 : L) 0]
      _ = 0 := zero_smul L x
      _ = (0 : L) • y := (zero_smul L y).symm
      _ = (1 : L) • y := by rw [Subsingleton.elim (0 : L) 1]
      _ = y := one_smul L y
  · haveI : Module.Free (Localization.AtPrime m) (LocalizedModule.AtPrime m M) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Free (Localization.AtPrime m) (LocalizedModule.AtPrime m N) :=
      Module.free_of_flat_of_isLocalRing
    haveI : Module.Finite L (LocalizedModule.AtPrime m Mₐ) :=
      Module.Finite.of_isLocalizedModule (Submonoid.powers aₘ) f
    haveI : Module.Free L (LocalizedModule.AtPrime m Mₐ) :=
      Module.free_of_isLocalizedModule (Submonoid.powers aₘ) f
    haveI : Module.Free L (LocalizedModule.AtPrime m Nₐ) :=
      Module.free_of_isLocalizedModule (Submonoid.powers aₘ) g
    have hfinM :
        finrank L (LocalizedModule.AtPrime m Mₐ) =
          finrank (Localization.AtPrime m) (LocalizedModule.AtPrime m M) :=
      Module.finrank_of_isLocalizedModule_of_free L (Submonoid.powers aₘ) f
    have hfinN :
        finrank L (LocalizedModule.AtPrime m Nₐ) =
          finrank (Localization.AtPrime m) (LocalizedModule.AtPrime m N) :=
      Module.finrank_of_isLocalizedModule_of_free L (Submonoid.powers aₘ) g
    have hfin :
        finrank L (LocalizedModule.AtPrime m Mₐ) =
          finrank L (LocalizedModule.AtPrime m Nₐ) := by
      rw [hfinM, hfinN]
      simpa [rankAtStalk] using h m
    exact bijective_of_surjective_of_finite_of_free_of_finrank_eq hfin hφₐ

variable (M) in
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant [Module.Finite R M] [Module.Flat R M]
    (p : Ideal R) [p.IsPrime] (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    ∃ (f : R) (_ : f ∉ p), Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  let n := rankAtStalk M ⟨p, inferInstance⟩
  have : Module.Free (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
    Module.free_of_flat_of_isLocalRing
  let b : Basis (Fin n) (Localization.AtPrime p) (LocalizedModule.AtPrime p M) :=
    finBasisOfFinrankEq (Localization.AtPrime p) (LocalizedModule.AtPrime p M) rfl
  obtain ⟨φ, hφs⟩ := exists_isLocalizedModule_map_surjective_of_surjective p (Localization.AtPrime p)
    (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime p)))
      (LocalizedModule.mkLinearMap p.primeCompl M) <| LinearEquiv.surjective <|
        (finBasisOfFinrankEq (Localization.AtPrime p) (LocalizedModule.AtPrime p M) rfl).repr.symm
  obtain ⟨a, hap, hφs⟩ := by
    refine exists_localizedModule_map_away_surjective_of_map_atPrime_surjective p φ ?_
    exact (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
      (Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization.AtPrime p)))
      (LocalizedModule.mkLinearMap p.primeCompl M)).mp hφs
  refine ⟨a, hap, ?_⟩
  let Rₐ := Localization.Away a
  let Mₐ := LocalizedModule.Away a M
  let Fₐ := LocalizedModule.Away a (Fin n →₀ R)
  have : Module.Free Rₐ Fₐ := Module.free_of_isLocalizedModule (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) (Fin n →₀ R))
  let φₐ : Fₐ →ₗ[Rₐ] Mₐ := LocalizedModule.map (Submonoid.powers a) φ
  have hφbij : Function.Bijective φₐ := by
    refine localized_map_bijective_of_surjective_of_rankAtStalk_eq a hφs (fun m _ ↦ ?_)
    simp [Module.rankAtStalk_eq_finrank_of_free, n, h m]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φₐ hφbij)

end Free

section FinitePresentation

-- porved in [#39109](https://github.com/leanprover-community/mathlib4/pull/39109)
theorem FinitePresentation.of_localizationSpan (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    Module.FinitePresentation R M :=
  sorry

theorem FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant
    [Module.Finite R M] [Module.Flat R M] (n : ℕ)
    (h : ∀ (p : Ideal R) [p.IsMaximal], rankAtStalk M ⟨p, inferInstance⟩ = n) :
    Module.FinitePresentation R M := by
  let s : Set R := {g | Module.Free (Localization.Away g) (LocalizedModule.Away g M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra! hs
    obtain ⟨m, _, hsm⟩ := Ideal.exists_le_maximal _ hs
    obtain ⟨g, hgm, hfree⟩ :=
      Free.away_of_finite_of_flat_of_rankAtStalk_constant M m (fun p _ ↦ by simp [h p, h m])
    exact hgm (hsm (Submodule.mem_span_of_mem hfree))
  refine FinitePresentation.of_localizationSpan s hs (fun ⟨g, hg⟩ ↦ ?_)
  simp only [Set.mem_setOf_eq, s] at hg
  exact finitePresentation_of_projective (Localization.Away g) (LocalizedModule.Away g M)

end FinitePresentation

section Invertible

open IsLocalizedModule IsLocalization

open scoped TensorProduct

theorem Invertible.of_isLocalized_maximal [Module.Finite R M]
    (Rₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], CommRing (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Algebra R (Rₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalization.AtPrime (Rₚ m) m]
    (Mₚ : ∀ (m : Ideal R) [m.IsMaximal], Type*)
    [∀ (m : Ideal R) [m.IsMaximal], AddCommGroup (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module R (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], Module (Rₚ m) (Mₚ m)]
    [∀ (m : Ideal R) [m.IsMaximal], IsScalarTower R (Rₚ m) (Mₚ m)]
    (f : ∀ (m : Ideal R) [m.IsMaximal], M →ₗ[R] Mₚ m)
    [∀ (m : Ideal R) [m.IsMaximal], IsLocalizedModule.AtPrime m (f m)]
    (h : ∀ (m : Ideal R) [m.IsMaximal], Module.Invertible (Rₚ m) (Mₚ m)) :
    Module.Invertible R M where
  bijective := by
    have : Flat R M := by
      refine flat_of_isLocalized_maximal R M Mₚ f (fun m _ ↦ ?_)
      have : Flat R (Rₚ m) := IsLocalization.flat (Rₚ m) m.primeCompl
      exact Flat.trans R (Rₚ m) (Mₚ m)
    have : Module.FinitePresentation R M := by
      refine Module.FinitePresentation.of_finite_of_flat_of_rankAtStalk_constant 1 (fun m _ ↦ ?_)
      have : IsLocalRing (Rₚ m) := IsLocalization.AtPrime.isLocalRing (Rₚ m) m
      have hfree : Module.Free (Rₚ m) (Mₚ m) := Module.free_of_flat_of_isLocalRing
      let e : LocalizedModule.AtPrime m M ≃ₗ[R] Localization.AtPrime m :=
        IsLocalizedModule.linearEquiv m.primeCompl (LocalizedModule.mkLinearMap _ M) (f m) ≪≫ₗ
          (Invertible.free_iff_linearEquiv.mp hfree).some.restrictScalars R ≪≫ₗ
            (algEquiv m.primeCompl (Localization.AtPrime m) (Rₚ m)).symm.toLinearEquiv
      exact (e.extendScalarsOfIsLocalization m.primeCompl (Localization.AtPrime m)).finrank_eq.trans
        (CommSemiring.finrank_self (Localization.AtPrime m))
    let ϕ (m : Ideal R) [m.IsMaximal] := TensorProduct.map
      (mapExtendScalars m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) (Rₚ m)) (f m)
    refine bijective_of_isLocalized_maximal _ ϕ Rₚ
      (fun m _ ↦ Algebra.linearMap R (Rₚ m)) (contractLeft R M) (fun m _ ↦ ?_)
    let ψ : Module.Dual (Rₚ m) (Mₚ m) ⊗[Rₚ m] Mₚ m ≃ₗ[R] Module.Dual (Rₚ m) (Mₚ m) ⊗[R] Mₚ m :=
      (moduleTensorEquiv m.primeCompl (Rₚ m) (Module.Dual (Rₚ m) (Mₚ m)) (Mₚ m)).restrictScalars R
    have hψ : (map m.primeCompl (ϕ m) (Algebra.linearMap R (Rₚ m))) (contractLeft R M) =
        (contractLeft (Rₚ m) (Mₚ m)).restrictScalars R ∘ₗ ψ.symm.toLinearMap := by
      apply IsLocalizedModule.ext m.primeCompl (ϕ m) (map_units (Algebra.linearMap R (Rₚ m)))
      ext α x
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply]
      change _ = mapExtendScalars m.primeCompl (f m) (Algebra.linearMap R (Rₚ m)) (Rₚ m) α (f m x)
      simp
    simp [hψ, (h m).bijective.comp ψ.symm.bijective]

theorem Invertible.of_localized_maximal [Module.Finite R M]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M)) :
    Module.Invertible R M :=
  of_isLocalized_maximal (fun m _ ↦ Localization.AtPrime m) (fun m _ ↦ LocalizedModule.AtPrime m M)
    (fun m _ ↦ LocalizedModule.mkLinearMap m.primeCompl M) h

end Invertible

end Module
