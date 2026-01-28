import QuillenSuslin.FiniteFreeResolution

universe u v w

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal

section ringEquiv

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]

attribute [local instance] RingHomInvPair.of_ringEquiv

noncomputable def semilinearEquiv_compHom (e : A ≃+* B) (M : Type v) [AddCommGroup M] [Module B M] :
    let : Module A M := Module.compHom M (e : A →+* B)
    M ≃ₛₗ[(e : A →+* B)] M := by
  classical
  let : Module A M := Module.compHom M (e : A →+* B)
  refine
    { toEquiv := Equiv.refl M
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem moduleFinite_of_ringEquiv (e : A ≃+* B) (M : Type v) [AddCommGroup M] [Module B M]
    [Module.Finite B M] :
    let : Module A M := Module.compHom M e.toRingHom
    Module.Finite A M := by
  let : Module A M := Module.compHom M (e : A →+* B)
  have hfgB : (⊤ : Submodule B M).FG := Module.Finite.fg_top
  rcases (Submodule.fg_def.mp hfgB) with ⟨S, hSfin, hSspan⟩
  refine Module.Finite.of_fg_top <| (Submodule.fg_def).2 ⟨S, hSfin, ?_⟩
  apply le_antisymm le_top
  show (⊤ : Submodule A M) ≤ Submodule.span A S
  intro x hx
  have hxB : x ∈ Submodule.span B S := by simp [hSspan]
  -- Show `span B S ≤ span A S`, using surjectivity of `e`.
  have hBA : (Submodule.span B S : Set M) ⊆ (Submodule.span A S : Set M) := by
    intro y
    refine Submodule.span_induction
      (p := fun z _ => z ∈ (Submodule.span A S : Submodule A M))
        (fun z hz => Submodule.subset_span hz) (by simp)
          (fun _ _ _ _ hz₁ hz₂ => by simpa using Submodule.add_mem (Submodule.span A S) hz₁ hz₂) ?_
    intro b z _ hz
    rcases e.surjective b with ⟨a, rfl⟩
    simpa [Module.compHom] using Submodule.smul_mem (Submodule.span A S) a hz
  exact hBA hxB

theorem hasFiniteFreeResolutionLength_of_ringEquiv (e : A ≃+* B) (P : Type u) [AddCommGroup P]
    [Module B P] {n : ℕ} (hn : HasFiniteFreeResolutionLength B P n) :
    let : Module A P := Module.compHom P e.toRingHom
    HasFiniteFreeResolutionLength A P n := by
  let : Module A P := Module.compHom P e.toRingHom
  induction hn with
  | zero P =>
      have : Module.Finite A P := moduleFinite_of_ringEquiv e P
      have : Module.Free A P :=
        (Module.Free.iff_of_ringEquiv e (semilinearEquiv_compHom e P)).2 inferInstance
      exact HasFiniteFreeResolutionLength.zero P
  | succ P n F f hf hker ih =>
      let : Module A F := Module.compHom F e.toRingHom
      have : Module.Finite A F := moduleFinite_of_ringEquiv e F
      have : Module.Free A F :=
        (Module.Free.iff_of_ringEquiv e (semilinearEquiv_compHom e F)).2 inferInstance
      let fA : F →ₗ[A] P :=
        { toFun := f
          map_add' := fun _ _ => by simp
          map_smul' := by
            intro a x
            show f ((e a) • x) = (e a) • f x
            simp }
      have hkerA : HasFiniteFreeResolutionLength A (LinearMap.ker fA) n := by simpa [fA] using ih
      exact HasFiniteFreeResolutionLength.succ P n F fA hf hkerA

theorem hasFiniteFreeResolution_of_ringEquiv (e : A ≃+* B) (P : Type v) [AddCommGroup P]
    [Module B P] (h : HasFiniteFreeResolution B P) :
    let : Module A P := Module.compHom P e.toRingHom
    HasFiniteFreeResolution A P := by
  let : Module A P := Module.compHom P e.toRingHom
  rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
  let : Module A F := Module.compHom F e.toRingHom
  have : Module.Finite A F := moduleFinite_of_ringEquiv e F
  have : Module.Free A F :=
    (Module.Free.iff_of_ringEquiv e (semilinearEquiv_compHom e F)).2 inferInstance
  let fA : F →ₗ[A] P :=
    { toFun := f
      map_add' := fun _ _ => by simp
      map_smul' := by
        intro a x
        show f ((e a) • x) = (e a) • f x
        simp }
  have hnA : HasFiniteFreeResolutionLength A (LinearMap.ker fA) n := by
    simpa [fA] using hasFiniteFreeResolutionLength_of_ringEquiv e _ hn
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, fA, hf, n, hnA⟩

theorem hasFiniteFreeResolution_of_ringEquiv_left (e : A ≃+* B) (P : Type v) [AddCommGroup P]
    [Module A P]
    (h : (let : Module B P := Module.compHom P e.symm.toRingHom; HasFiniteFreeResolution B P)) :
    HasFiniteFreeResolution A P := by
  let instA₀ : Module A P := inferInstance
  let instB : Module B P := Module.compHom P e.symm.toRingHom
  have hB : HasFiniteFreeResolution B P := by simpa using h
  let instA₁ : Module A P := Module.compHom P e.toRingHom
  have hA₁ : @HasFiniteFreeResolution A P _ _ instA₁ := by
    simpa [instA₁] using hasFiniteFreeResolution_of_ringEquiv e P hB
  have hinst : instA₁ = instA₀ := by
    refine Module.ext' instA₁ instA₀ ?_
    intro a x
    show (have := instA₀; (e.symm (e a)) • x) = (have := instA₀; a • x)
    simp
  simpa [hinst] using hA₁

theorem hasFiniteFreeResolution_of_ringEquiv_right (e : A ≃+* B) (P : Type v) [AddCommGroup P]
    [Module B P]
    (h : (let : Module A P := Module.compHom P e.toRingHom; HasFiniteFreeResolution A P)) :
    HasFiniteFreeResolution B P := by
  let instB₀ : Module B P := inferInstance
  let instA : Module A P := Module.compHom P e.toRingHom
  have hA : HasFiniteFreeResolution A P := by simpa using h
  let instB₁ : Module B P := Module.compHom P e.symm.toRingHom
  have hB₁ : @HasFiniteFreeResolution B P _ _ instB₁ := by
    simpa [instB₁] using hasFiniteFreeResolution_of_ringEquiv e.symm P hA
  have hinst : instB₁ = instB₀ := by
    refine Module.ext' instB₁ instB₀ ?_
    intro b x
    show (have := instB₀; (e (e.symm b)) • x) = (have := instB₀; b • x)
    simp
  simpa [hinst] using hB₁

end ringEquiv

theorem mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing_aux [IsNoetherianRing R]
    (s : Type) [Finite s]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type u) [AddCommGroup P] [Module (MvPolynomial s R) P]
    [Module.Finite (MvPolynomial s R) P] : HasFiniteFreeResolution (MvPolynomial s R) P := by
  let Q : Type → Prop := fun t =>
    ∀ (M : Type u) [AddCommGroup M] [Module (MvPolynomial t R) M]
      [Module.Finite (MvPolynomial t R) M], HasFiniteFreeResolution (MvPolynomial t R) M
  have hs : Q s := by
    refine Finite.induction_empty_option ?_ ?_ ?_ s
    · intro α β a hα M _ _ _
      let e : MvPolynomial α R ≃+* MvPolynomial β R := (MvPolynomial.renameEquiv R a).toRingEquiv
      let : Module (MvPolynomial α R) M := Module.compHom M e.toRingHom
      have hA : HasFiniteFreeResolution (MvPolynomial α R) M := by
        have : Module.Finite (MvPolynomial α R) M := moduleFinite_of_ringEquiv (e := e) M
        simpa using hα M
      simpa using hasFiniteFreeResolution_of_ringEquiv_right e M hA
    · intro M _ _ _
      let e : MvPolynomial PEmpty R ≃+* R := MvPolynomial.isEmptyRingEquiv R PEmpty
      let : Module R M := Module.compHom M e.symm.toRingHom
      have hRM : HasFiniteFreeResolution R M := by
        have : Module.Finite R M := moduleFinite_of_ringEquiv e.symm M
        exact hR M (inferInstance : Module.Finite R M)
      simpa using hasFiniteFreeResolution_of_ringEquiv_left e M hRM
    · intro α _ hα M _ _ _
      let e : MvPolynomial (Option α) R ≃+* (MvPolynomial α R)[X] :=
        (MvPolynomial.optionEquivLeft R α).toRingEquiv
      let : Module (MvPolynomial α R)[X] M := Module.compHom M e.symm.toRingHom
      have hPoly : HasFiniteFreeResolution (MvPolynomial α R)[X] M := by
        have : Module.Finite (MvPolynomial α R)[X] M := moduleFinite_of_ringEquiv e.symm M
        simpa using polynomial_hasFiniteFreeResolution_of_isNoetherianRing (MvPolynomial α R) hα M
      simpa using hasFiniteFreeResolution_of_ringEquiv_left e M hPoly
  exact hs P

theorem mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (s : Type w) [Finite s]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial s R) P]
    [Module.Finite (MvPolynomial s R) P] : HasFiniteFreeResolution (MvPolynomial s R) P := by
  sorry
