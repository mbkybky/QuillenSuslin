import Mathlib

universe u v w

variable {R : Type u} [CommRing R]

/-- `HasFiniteFreeResolutionLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionLength (R : Type u) [CommRing R] :
    ∀ (P : Type u), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P] :
      HasFiniteFreeResolutionLength R P 0
  | succ (P : Type u) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type u) [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      (f : F →ₗ[R] P) (hf : Function.Surjective f)
      (hker : HasFiniteFreeResolutionLength R (LinearMap.ker f) n) :
      HasFiniteFreeResolutionLength R P (n + 1)

theorem module_finite_of_hasFiniteFreeResolutionLength {P : Type u} [AddCommGroup P] [Module R P]
    {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) : Module.Finite R P := by
  induction hn with
  | zero P => infer_instance
  | succ P n F f hf hker ih => exact Module.Finite.of_surjective f hf

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) (P : Type v)
    [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ (F : Type u) ( _ : AddCommGroup F) (_ : Module R F) (_ : Module.Finite R F)
    (_ : Module.Free R F) (f : F →ₗ[R] P) (_ : Function.Surjective f) (n : ℕ),
      HasFiniteFreeResolutionLength R (LinearMap.ker f) n

/-- A finitely generated free module has a finite free resolution (of length `0`). -/
theorem hasFiniteFreeResolution_of_finite_of_free (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P] : HasFiniteFreeResolution R P := by
  let ι := Module.Free.ChooseBasisIndex R P
  let b : Module.Basis ι R P := Module.Free.chooseBasis R P
  let n : ℕ := Fintype.card ι
  let eι : Fin n ≃ ι := (Fintype.equivFin ι).symm
  have ePi : (ι → R) ≃ₗ[R] (Fin n → R) := (LinearEquiv.piCongrLeft R (fun _ : ι => R) eι).symm
  have eP : (Fin n → R) ≃ₗ[R] P := (b.equivFun.trans ePi).symm
  have : Subsingleton eP.toLinearMap.ker := Submodule.subsingleton_iff_eq_bot.mpr eP.ker
  exact ⟨Fin n → R, inferInstance, inferInstance, inferInstance, inferInstance, eP.toLinearMap,
    eP.surjective, 0, HasFiniteFreeResolutionLength.zero eP.toLinearMap.ker⟩

private theorem hasFiniteFreeResolutionLength_of_linearEquiv_aux (P : Type u) [AddCommGroup P]
    [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) :
    ∀ {Q : Type u} [AddCommGroup Q] [Module R Q], (e : P ≃ₗ[R] Q) →
      HasFiniteFreeResolutionLength R Q n := by
  induction hn with
  | zero P =>
      intro Q _ _ e
      let : Module.Finite R Q := Module.Finite.of_surjective e.toLinearMap e.surjective
      let : Module.Free R Q := Module.Free.of_equiv e
      exact HasFiniteFreeResolutionLength.zero Q
  | succ P n F π hπ hker ih =>
      intro Q _ _ e
      exact HasFiniteFreeResolutionLength.succ Q n F (e.toLinearMap.comp π) (e.surjective.comp hπ)
        <| ih (LinearEquiv.ofEq (e.toLinearMap.comp π).ker π.ker (e.ker_comp π)).symm

theorem hasFiniteFreeResolutionLength_of_linearEquiv {P Q : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) : HasFiniteFreeResolutionLength R Q n :=
  hasFiniteFreeResolutionLength_of_linearEquiv_aux P hn e

/-- Transport `HasFiniteFreeResolution` along an `R`-linear equivalence. -/
theorem hasFiniteFreeResolution_of_linearEquiv {P : Type v} {Q : Type w} [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q]
    (e : P ≃ₗ[R] Q) (h : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, e.toLinearMap.comp f,
    e.surjective.comp hf, n,
      hasFiniteFreeResolutionLength_of_linearEquiv (LinearEquiv.ofEq _ _ (e.ker_comp f).symm) hn⟩

theorem hasFiniteFreeResolutionLength_of_hasFiniteFreeResolution
    (P : Type u) [AddCommGroup P] [Module R P] :
    HasFiniteFreeResolution R P → ∃ n : ℕ, HasFiniteFreeResolutionLength R P n := by
  rintro ⟨F, _, _, _, _, f, hf, n, hn⟩
  exact ⟨n + 1, HasFiniteFreeResolutionLength.succ P n F f hf hn⟩

-- add a lemma : P HasFiniteFreeResolution ↔ Shrink.{u} P HasFiniteFreeResolution
theorem hasFiniteFreeResolution_iff_shrink (P : Type v) [AddCommGroup P] [Module R P] [Small.{u} P] :
    HasFiniteFreeResolution R P ↔ HasFiniteFreeResolution R (Shrink.{u} P) :=
  ⟨hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv R P).symm,
    hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv R P)⟩

section ringEquiv

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]

attribute [local instance] RingHomInvPair.of_ringEquiv

noncomputable def semilinearEquiv_compHom (e : A ≃+* B) (M : Type v) [AddCommGroup M]
    [Module B M] :
    let : Module A M := Module.compHom M (e : A →+* B)
    M ≃ₛₗ[(e : A →+* B)] M := by
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

variable {S : Type u} [CommRing S]

noncomputable def ringEquivULift : ULift.{w} S ≃+* S :=
  { toEquiv := Equiv.ulift
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

noncomputable def semilinearEquivULift (M : Type u) [AddCommGroup M] [Module S M] :
    ULift.{w} M ≃ₛₗ[(ringEquivULift (S := S) : ULift.{w} S →+* S)] M :=
  { toEquiv := Equiv.ulift
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

noncomputable def linearEquivULift (M : Type u) [AddCommGroup M] [Module S M] :
    ULift.{w} M ≃ₗ[S] M :=
  { toEquiv := Equiv.ulift
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem moduleFinite_of_ringEquiv' {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (M : Type w) [AddCommGroup M] [Module B M] [Module.Finite B M] :
    let : Module A M := Module.compHom M e.toRingHom
    Module.Finite A M := by
  let : Module A M := Module.compHom M e.toRingHom
  have hfgB : (⊤ : Submodule B M).FG := Module.Finite.fg_top
  rcases (Submodule.fg_def.mp hfgB) with ⟨T, hTfin, hTspan⟩
  refine Module.Finite.of_fg_top <| (Submodule.fg_def).2 ⟨T, hTfin, ?_⟩
  apply le_antisymm le_top
  show (⊤ : Submodule A M) ≤ Submodule.span A T
  intro x hx
  have hxB : x ∈ Submodule.span B T := by simp [hTspan]
  have hBA : (Submodule.span B T : Set M) ⊆ (Submodule.span A T : Set M) := by
    intro y
    refine Submodule.span_induction
      (p := fun z _ => z ∈ (Submodule.span A T : Submodule A M))
        (fun z hz => Submodule.subset_span hz) (by simp)
          (fun _ _ _ _ hz₁ hz₂ => by simpa using Submodule.add_mem (Submodule.span A T) hz₁ hz₂) ?_
    intro b z _ hz
    rcases e.surjective b with ⟨a, rfl⟩
    simpa [Module.compHom] using Submodule.smul_mem (Submodule.span A T) a hz
  exact hBA hxB

theorem hasFiniteFreeResolutionLength_ulift {P : Type u} [AddCommGroup P] [Module S P] {n : ℕ}
    (hn : HasFiniteFreeResolutionLength S P n) :
    HasFiniteFreeResolutionLength (ULift.{w} S) (ULift.{w} P) n := by
  induction hn with
  | zero P =>
      have : Module.Free (ULift.{w} S) (ULift.{w} P) :=
        (Module.Free.iff_of_ringEquiv ringEquivULift
          (semilinearEquivULift P)).2 inferInstance
      have : Module.Finite (ULift.{w} S) (ULift.{w} P) := by
        have : Module.Finite S (ULift.{w} P) :=
          Module.Finite.equiv (linearEquivULift P).symm
        simpa using
          (moduleFinite_of_ringEquiv' (A := ULift.{w} S) (B := S)
            ringEquivULift (ULift.{w} P))
      exact HasFiniteFreeResolutionLength.zero (ULift.{w} P)
  | succ P n F f hf hker ih =>
      let f' : ULift.{w} F →ₗ[ULift.{w} S] ULift.{w} P :=
        { toFun := fun x => ULift.up (f x.down)
          map_add' := by
            intro x y
            ext
            simp [f.map_add]
          map_smul' := by
            intro a x
            ext
            simp [f.map_smul] }
      have hf' : Function.Surjective f' := by
        intro y
        rcases hf y.down with ⟨x, hx⟩
        refine ⟨ULift.up x, ?_⟩
        ext
        simp [f', hx]
      have : Module.Free (ULift.{w} S) (ULift.{w} F) :=
        (Module.Free.iff_of_ringEquiv ringEquivULift (semilinearEquivULift F)).2 inferInstance
      have : Module.Finite (ULift.{w} S) (ULift.{w} F) := by
        have : Module.Finite S (ULift.{w} F) :=
          Module.Finite.equiv (linearEquivULift F).symm
        simpa using (moduleFinite_of_ringEquiv' (B := S) ringEquivULift (ULift.{w} F))
      have hk' : HasFiniteFreeResolutionLength (ULift.{w} S) (LinearMap.ker f') n := by
        have hk0 :
            HasFiniteFreeResolutionLength (ULift.{w} S) (ULift.{w} (LinearMap.ker f)) n := by
          simpa using ih
        let eKer : ULift.{w} (LinearMap.ker f) ≃ₗ[ULift.{w} S] LinearMap.ker f' :=
          { toEquiv :=
              { toFun := fun x => ⟨ULift.up x.down.1, by
                  ext
                  simp [f']⟩
                invFun := fun y =>
                  ULift.up ⟨y.1.down, by
                    have hy : f' y.1 = 0 := (LinearMap.mem_ker).1 y.2
                    dsimp [f'] at hy
                    have hy' : f y.1.down = 0 := by simpa using congrArg ULift.down hy
                    exact (LinearMap.mem_ker).2 hy'⟩
                left_inv := fun _ => by congr
                right_inv := fun y => by congr }
            map_add' := fun _ _ => by congr
            map_smul' := fun _ _ => by congr }
        exact hasFiniteFreeResolutionLength_of_linearEquiv eKer hk0
      exact HasFiniteFreeResolutionLength.succ (ULift.{w} P) n (ULift.{w} F) f' hf' hk'

theorem hasFiniteFreeResolution_ulift (P : Type v) [AddCommGroup P] [Module S P]
    (h : HasFiniteFreeResolution S P) : HasFiniteFreeResolution (ULift.{w} S) P := by
  rcases h with ⟨F, _, _, _, _, f, hf, n, hn⟩
  let f' : ULift.{w} F →ₗ[ULift.{w} S] P :=
    { toFun := fun x => f x.down
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  have hf' : Function.Surjective f' := by
    intro y
    rcases hf y with ⟨x, rfl⟩
    exact ⟨ULift.up x, rfl⟩
  have hn' : HasFiniteFreeResolutionLength (ULift.{w} S) (LinearMap.ker f') n := by
    have hk0 : HasFiniteFreeResolutionLength (ULift.{w} S) (ULift.{w} (LinearMap.ker f)) n := by
      simpa using hasFiniteFreeResolutionLength_ulift (S := S) (hn := hn)
    let eKer :
        ULift.{w} (LinearMap.ker f) ≃ₗ[ULift.{w} S] LinearMap.ker f' :=
      { toEquiv :=
          { toFun := fun x => ⟨ULift.up x.down.1, by simp [f']⟩
            invFun := fun y =>
            ULift.up ⟨y.1.down, by
              have hy : f' y.1 = 0 := (LinearMap.mem_ker).1 y.2
              dsimp [f'] at hy
              exact (LinearMap.mem_ker).2 hy⟩
            left_inv := fun _ => by congr
            right_inv := fun _ => by congr }
        map_add' := fun _ _ => by congr
        map_smul' := fun _ _ => by congr }
    exact hasFiniteFreeResolutionLength_of_linearEquiv eKer hk0
  have : Module.Free (ULift.{w} S) (ULift.{w} F) :=
    (Module.Free.iff_of_ringEquiv ringEquivULift (semilinearEquivULift F)).2 inferInstance
  have : Module.Finite (ULift.{w} S) (ULift.{w} F) := by
    have : Module.Finite S (ULift.{w} F) := Module.Finite.equiv (linearEquivULift F).symm
    simpa using moduleFinite_of_ringEquiv' (B := S) ringEquivULift (ULift.{w} F)
  exact ⟨ULift.{w} F, inferInstance, inferInstance, inferInstance, inferInstance, f', hf', n, hn'⟩

end ringEquiv

section exact_seq

/-- Extract a surjection `F →ₗ[R] P` from a finite free resolution of `P`.
For length `0` we use the identity map. -/
theorem exists_surjective_of_hasFiniteFreeResolutionLength (P : Type u)
    [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) :
      ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Finite R F)
        (_ : Module.Free R F) (π : F →ₗ[R] P), Function.Surjective π ∧
          HasFiniteFreeResolutionLength R (LinearMap.ker π) (Nat.pred n) := by
  cases hn with
  | zero P =>
      refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, LinearMap.id,
          Function.surjective_id, ?_⟩
      simpa using (HasFiniteFreeResolutionLength.zero (⊥ : Submodule R P))
  | succ P n F π hπ hker =>
      refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, π, hπ, ?_⟩
      simpa using hker

theorem hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength
    (P : Type u) [AddCommGroup P] [Module R P] :
    (∃ n : ℕ, HasFiniteFreeResolutionLength R P n) → HasFiniteFreeResolution R P := by
  rintro ⟨n, hn⟩
  rcases exists_surjective_of_hasFiniteFreeResolutionLength P hn with
    ⟨F, _, _, _, _, π, hπ, hker⟩
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, π, hπ, Nat.pred n, hker⟩

/-- Horseshoe lemma for finite free resolutions (2-out-of-3: left + right ⇒ middle). -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right_length (P₁ P₂ P₃ : Type u)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) {n₁ n₃ : ℕ} (h₁ : HasFiniteFreeResolutionLength R P₁ n₁)
      (h₃ : HasFiniteFreeResolutionLength R P₃ n₃) : HasFiniteFreeResolution R P₂ := by
  induction h₁ generalizing P₂ P₃ g n₃ with
  | zero P₁ =>
      -- Choose the first step of the resolution of `P₃`.
      rcases exists_surjective_of_hasFiniteFreeResolutionLength P₃ h₃ with
        ⟨F₃, _, _, _, _, π₃, hπ₃, hK₃⟩
      -- Lift `π₃` to a map into `P₂` using projectivity of `F₃`.
      obtain ⟨l, hl⟩ := Module.projective_lifting_property (f := g) (g := π₃) hg
      -- Define the surjection `P₁ × F₃ → P₂`.
      let φ : (P₁ × F₃) →ₗ[R] P₂ := f.coprod l
      have hφsurj : Function.Surjective φ := by
        intro p₂
        rcases hπ₃ (g p₂) with ⟨y₃, hy₃⟩
        have hg0 : g (p₂ - l y₃) = 0 := by
          have hgl : g (l y₃) = π₃ y₃ := by
            simpa [LinearMap.comp_apply] using congrArg (fun m => m y₃) hl
          simp [map_sub, hgl, hy₃]
        have : p₂ - l y₃ ∈ LinearMap.ker g := hg0
        have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
        rcases (show p₂ - l y₃ ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
        exact ⟨(x₁, y₃), by simp [φ, LinearMap.coprod_apply, hx₁]⟩
      -- Compare `ker φ` with `ker π₃` via projection to `F₃`.
      let p : (LinearMap.ker φ) →ₗ[R] (LinearMap.ker π₃) :=
        LinearMap.codRestrict (LinearMap.ker π₃)
          ((LinearMap.snd R P₁ F₃).comp (Submodule.subtype (LinearMap.ker φ))) (by
            intro y
            have hy : φ y.1 = 0 := y.2
            have hgf : g.comp f = 0 := h.linearMap_comp_eq_zero
            have hgf' : g (f y.1.1) = 0 := by
              simpa [LinearMap.comp_apply] using congrArg (fun m => m y.1.1) hgf
            have hgl : g (l y.1.2) = π₃ y.1.2 := by
              simpa [LinearMap.comp_apply] using congrArg (fun m => m y.1.2) hl
            have hgy : g (φ y.1) = 0 := by simp [hy]
            have hgl0 : g (l y.1.2) = 0 := by
              simpa [hgf'] using (g.map_add (f y.1.1) (l y.1.2)).symm.trans hgy
            have : π₃ y.1.2 = 0 := by
              calc _ = g (l y.1.2) := by simpa using hgl.symm
                _ = 0 := hgl0
            simpa [LinearMap.mem_ker] using this)
      have hp_surj : Function.Surjective p := by
        intro z
        have hz : π₃ z.1 = 0 := z.2
        have : g (l z.1) = 0 := by
          have : g (l z.1) = π₃ z.1 := by
            simpa [LinearMap.comp_apply] using congrArg (fun m => m z.1) hl
          simp [this, hz]
        have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
        have : l z.1 ∈ LinearMap.ker g := by simpa [LinearMap.mem_ker] using this
        rcases (show l z.1 ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
        refine ⟨⟨(-x₁, z.1), ?_⟩, ?_⟩
        · -- membership in `ker φ`
          have : f (-x₁) + l z.1 = 0 := by simp [map_neg, hx₁]
          simpa [φ, LinearMap.mem_ker, LinearMap.coprod_apply] using this
        · apply Subtype.ext
          simp [p]
      have hp_inj : Function.Injective p := by
        intro x y hxy
        apply Subtype.ext
        have h2 : x.1.2 = y.1.2 := by simpa [p] using congrArg Subtype.val hxy
        have h1 : x.1.1 = y.1.1 := by
          have hx : φ x.1 = 0 := x.2
          have hy : φ y.1 = 0 := y.2
          -- Subtract the equalities `φ x = 0` and `φ y = 0`, using `h2`.
          have : f x.1.1 = f y.1.1 := by
            calc _ = -l x.1.2 := (eq_neg_iff_add_eq_zero).2 hx
              _ = -l y.1.2 := by simp [h2]
              _ = f y.1.1 := ((eq_neg_iff_add_eq_zero).2 hy).symm
          exact hf this
        exact Prod.ext h1 h2
      exact hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength P₂
        ⟨Nat.pred n₃ + 1,
          HasFiniteFreeResolutionLength.succ P₂ (Nat.pred n₃) (P₁ × F₃) φ hφsurj <|
            hasFiniteFreeResolutionLength_of_linearEquiv
              (LinearEquiv.ofBijective p ⟨hp_inj, hp_surj⟩).symm hK₃⟩
  | succ P₁ n F₁ π₁ hπ₁ hK₁ ih =>
      -- Choose the first step of the resolution of `P₃`.
      rcases exists_surjective_of_hasFiniteFreeResolutionLength P₃ h₃ with
        ⟨F₃, _, _, _, _, π₃, hπ₃, hK₃⟩
      obtain ⟨l, hl⟩ := Module.projective_lifting_property g π₃ hg
      let φ : (F₁ × F₃) →ₗ[R] P₂ := (f.comp π₁).coprod l
      have hφsurj : Function.Surjective φ := by
        intro p₂
        rcases hπ₃ (g p₂) with ⟨y₃, hy₃⟩
        have hg0 : g (p₂ - l y₃) = 0 := by
          have hgl : g (l y₃) = π₃ y₃ := by
            simpa [LinearMap.comp_apply] using congrArg (fun m => m y₃) hl
          simp [map_sub, hgl, hy₃]
        have : p₂ - l y₃ ∈ LinearMap.ker g := hg0
        have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
        rcases (show p₂ - l y₃ ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
        rcases hπ₁ x₁ with ⟨y₁, rfl⟩
        refine ⟨(y₁, y₃), ?_⟩
        simp [φ, LinearMap.coprod_apply, LinearMap.comp_apply, hx₁]
      -- Define the short exact sequence `ker π₁ → ker φ → ker π₃`.
      let i : (LinearMap.ker π₁) →ₗ[R] (LinearMap.ker φ) :=
        LinearMap.codRestrict (LinearMap.ker φ)
          ((LinearMap.inl R F₁ F₃).comp (Submodule.subtype (LinearMap.ker π₁))) (by
            intro x
            have hx : π₁ x.1 = 0 := x.2
            -- `φ (x, 0) = 0`.
            simp [φ, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply, hx])
      let p : (LinearMap.ker φ) →ₗ[R] (LinearMap.ker π₃) :=
        LinearMap.codRestrict (LinearMap.ker π₃)
          ((LinearMap.snd R F₁ F₃).comp (Submodule.subtype (LinearMap.ker φ))) (by
            intro y
            have hgf : g.comp f = 0 := h.linearMap_comp_eq_zero
            have hgf' : g (f (π₁ y.1.1)) = 0 := by
              simpa [LinearMap.comp_apply] using congrArg (fun m => m (π₁ y.1.1)) hgf
            have hgl : g (l y.1.2) = π₃ y.1.2 := by
              simpa [LinearMap.comp_apply] using congrArg (fun m => m y.1.2) hl
            have hgy : g (φ y.1) = 0 := by simp
            have hsum : g (f (π₁ y.1.1)) + g (l y.1.2) = 0 := by
              calc _ = g (f (π₁ y.1.1) + l y.1.2) := (g.map_add (f (π₁ y.1.1)) (l y.1.2)).symm
                _ = 0 := hgy
            have hgl0 : g (l y.1.2) = 0 := by simpa [hgf'] using hsum
            have : π₃ y.1.2 = 0 := by
              calc _ = g (l y.1.2) := by simpa using hgl.symm
                _ = 0 := hgl0
            simpa [LinearMap.mem_ker] using this)
      have hi : Function.Injective i := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg Prod.fst (congrArg Subtype.val hxy)
      have hp : Function.Surjective p := by
        intro z
        have hz : π₃ z.1 = 0 := z.2
        have : g (l z.1) = 0 := by
          have : g (l z.1) = π₃ z.1 := by
            simpa [LinearMap.comp_apply] using congrArg (fun m => m z.1) hl
          simp [this, hz]
        have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
        have : l z.1 ∈ LinearMap.ker g := by simpa [LinearMap.mem_ker] using this
        rcases (show l z.1 ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
        rcases hπ₁ (-x₁) with ⟨y₁, hy₁⟩
        refine ⟨⟨(y₁, z.1), ?_⟩, ?_⟩
        · have : f (π₁ y₁) + l z.1 = 0 := by
            -- use `hy₁` and `hx₁`
            have : f (π₁ y₁) = -l z.1 := by
              simpa [hy₁, map_neg] using congrArg Neg.neg hx₁
            simp [this]
          simpa [φ, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply] using this
        · apply Subtype.ext
          simp [p]
      have hexact : Function.Exact i p := by
        -- Use the characterization `ker p = range i`.
        rw [LinearMap.exact_iff]
        ext x
        constructor
        · intro hx
          -- `p x = 0` means the second component is `0`.
          have hx2 : x.1.2 = 0 := by
            have : p x = 0 := by simpa [LinearMap.mem_ker] using hx
            have : (p x).1 = 0 := congrArg Subtype.val this
            simpa [p] using this
          have hx1 : π₁ x.1.1 = 0 := by
            have hxφ : φ x.1 = 0 := x.2
            have hxφ' : f (π₁ x.1.1) + l x.1.2 = 0 := by
              have hxφ'' := hxφ
              dsimp [φ] at hxφ''
              simpa using hxφ''
            have hfEq : f (π₁ x.1.1) = -l x.1.2 := (eq_neg_iff_add_eq_zero).2 hxφ'
            have hf0 : f (π₁ x.1.1) = 0 := by simpa [hx2] using hfEq
            exact hf (by simpa using hf0)
          refine ⟨⟨x.1.1, hx1⟩, ?_⟩
          apply Subtype.ext
          ext
          · simp [i]
          · simp [i, hx2]
        · rintro ⟨x₁, rfl⟩
          -- `p (i x₁) = 0`.
          apply Subtype.ext
          simp [p, i, LinearMap.codRestrict_apply]
      have hK₂ : HasFiniteFreeResolution R (LinearMap.ker φ) :=
        ih (P₂ := LinearMap.ker φ) (P₃ := LinearMap.ker π₃) (f := i) (g := p)
          (hf := hi) (hg := hp) (h := hexact) (n₃ := Nat.pred n₃) hK₃
      rcases hasFiniteFreeResolutionLength_of_hasFiniteFreeResolution (LinearMap.ker φ) hK₂ with
        ⟨m, hm⟩
      exact hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength P₂
        ⟨m + 1, HasFiniteFreeResolutionLength.succ P₂ m (F₁ × F₃) φ hφsurj hm⟩

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right (P₁ P₂ P₃ : Type*)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₂ := by
  rcases h₁ with ⟨F₁, _, _, _, _, π₁, hπ₁, n₁, hK₁⟩
  rcases h₃ with ⟨F₃, _, _, _, _, π₃, hπ₃, n₃, hK₃⟩
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (f := g) (g := π₃) hg
  let φ : (F₁ × F₃) →ₗ[R] P₂ := (f.comp π₁).coprod l
  have hφsurj : Function.Surjective φ := by
    intro p₂
    rcases hπ₃ (g p₂) with ⟨y₃, hy₃⟩
    have hg0 : g (p₂ - l y₃) = 0 := by
      have hgl : g (l y₃) = π₃ y₃ := by
        simpa [LinearMap.comp_apply] using congrArg (fun m => m y₃) hl
      simp [map_sub, hgl, hy₃]
    have : p₂ - l y₃ ∈ LinearMap.ker g := hg0
    have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
    rcases (show p₂ - l y₃ ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
    rcases hπ₁ x₁ with ⟨y₁, rfl⟩
    refine ⟨(y₁, y₃), ?_⟩
    simp [φ, LinearMap.coprod_apply, LinearMap.comp_apply, hx₁]
  -- Define the short exact sequence `ker π₁ → ker φ → ker π₃`.
  let i : (LinearMap.ker π₁) →ₗ[R] (LinearMap.ker φ) :=
    LinearMap.codRestrict (LinearMap.ker φ)
      ((LinearMap.inl R F₁ F₃).comp (Submodule.subtype (LinearMap.ker π₁))) (by
        intro x
        have hx : π₁ x.1 = 0 := x.2
        simp [φ, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply, hx])
  let p : (LinearMap.ker φ) →ₗ[R] (LinearMap.ker π₃) :=
    LinearMap.codRestrict (LinearMap.ker π₃)
      ((LinearMap.snd R F₁ F₃).comp (Submodule.subtype (LinearMap.ker φ))) (by
        intro y
        have hgf : g.comp f = 0 := h.linearMap_comp_eq_zero
        have hgf' : g (f (π₁ y.1.1)) = 0 := by
          simpa [LinearMap.comp_apply] using congrArg (fun m => m (π₁ y.1.1)) hgf
        have hgl : g (l y.1.2) = π₃ y.1.2 := by
          simpa [LinearMap.comp_apply] using congrArg (fun m => m y.1.2) hl
        have hgy : g (φ y.1) = 0 := by simp
        have hsum : g (f (π₁ y.1.1)) + g (l y.1.2) = 0 := by
          calc _ = g (f (π₁ y.1.1) + l y.1.2) := (g.map_add (f (π₁ y.1.1)) (l y.1.2)).symm
            _ = 0 := hgy
        have hgl0 : g (l y.1.2) = 0 := by simpa [hgf'] using hsum
        have : π₃ y.1.2 = 0 := by
          calc _ = g (l y.1.2) := by simpa using hgl.symm
            _ = 0 := hgl0
        simpa [LinearMap.mem_ker] using this)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Prod.fst (congrArg Subtype.val hxy)
  have hp : Function.Surjective p := by
    intro z
    have hz : π₃ z.1 = 0 := z.2
    have : g (l z.1) = 0 := by
      have : g (l z.1) = π₃ z.1 := by
        simpa [LinearMap.comp_apply] using congrArg (fun m => m z.1) hl
      simp [this, hz]
    have hker : LinearMap.ker g = LinearMap.range f := h.linearMap_ker_eq
    have : l z.1 ∈ LinearMap.ker g := by simpa [LinearMap.mem_ker] using this
    rcases (show l z.1 ∈ LinearMap.range f by simpa [hker] using this) with ⟨x₁, hx₁⟩
    rcases hπ₁ (-x₁) with ⟨y₁, hy₁⟩
    refine ⟨⟨(y₁, z.1), ?_⟩, ?_⟩
    · have : f (π₁ y₁) + l z.1 = 0 := by
        have : f (π₁ y₁) = -l z.1 := by
          simpa [hy₁, map_neg] using congrArg Neg.neg hx₁
        simp [this]
      simpa [φ, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply] using this
    · apply Subtype.ext
      simp [p]
  have hexact : Function.Exact i p := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hx2 : x.1.2 = 0 := by
        have : p x = 0 := by simpa [LinearMap.mem_ker] using hx
        have : (p x).1 = 0 := congrArg Subtype.val this
        simpa [p] using this
      have hx1 : π₁ x.1.1 = 0 := by
        have hxφ : φ x.1 = 0 := x.2
        have hxφ' : f (π₁ x.1.1) + l x.1.2 = 0 := by
          have hxφ'' := hxφ
          dsimp [φ] at hxφ''
          simpa using hxφ''
        have hfEq : f (π₁ x.1.1) = -l x.1.2 := (eq_neg_iff_add_eq_zero).2 hxφ'
        have hf0 : f (π₁ x.1.1) = 0 := by simpa [hx2] using hfEq
        exact hf (by simpa using hf0)
      refine ⟨⟨x.1.1, hx1⟩, ?_⟩
      apply Subtype.ext
      ext
      · simp [i]
      · simp [i, hx2]
    · rintro ⟨x₁, rfl⟩
      apply Subtype.ext
      simp [p, i, LinearMap.codRestrict_apply]
  have hK₂ : HasFiniteFreeResolution R (LinearMap.ker φ) :=
    hasFiniteFreeResolution_of_shortExact_of_left_of_right_length (R := R)
      (P₁ := LinearMap.ker π₁) (P₂ := LinearMap.ker φ) (P₃ := LinearMap.ker π₃) hi hp hexact hK₁ hK₃
  rcases hasFiniteFreeResolutionLength_of_hasFiniteFreeResolution (LinearMap.ker φ) hK₂ with ⟨m, hm⟩
  exact ⟨F₁ × F₃, inferInstance, inferInstance, inferInstance, inferInstance, φ, hφsurj, m, hm⟩

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle (P₁ P₂ P₃ : Type*)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₃ := by
  rcases h₂ with ⟨F₂, _, _, _, _, π₂, hπ₂, n₂, hK₂len⟩
  have hK₂ : HasFiniteFreeResolution R (LinearMap.ker π₂) :=
    hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength (LinearMap.ker π₂) ⟨n₂, hK₂len⟩
  let q : F₂ →ₗ[R] P₃ := g.comp π₂
  have hq : Function.Surjective q := hg.comp hπ₂
  -- Define the short exact sequence `ker π₂ → ker q → P₁`.
  let i : (LinearMap.ker π₂) →ₗ[R] (LinearMap.ker q) :=
    LinearMap.codRestrict (LinearMap.ker q) (Submodule.subtype (LinearMap.ker π₂)) (by
      intro x
      have hx : π₂ x.1 = 0 := x.2
      simp [q, LinearMap.mem_ker, LinearMap.comp_apply, hx])
  let e : P₁ ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  let toRange : (LinearMap.ker q) →ₗ[R] (LinearMap.range f) :=
    LinearMap.codRestrict (LinearMap.range f) (π₂.comp (Submodule.subtype (LinearMap.ker q))) <| by
      simpa using fun y hy => (h _).mp hy
  let p : (LinearMap.ker q) →ₗ[R] P₁ := e.symm.toLinearMap.comp toRange
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    simpa [i] using congrArg Subtype.val hxy
  have hp : Function.Surjective p := by
    intro x₁
    rcases hπ₂ (f x₁) with ⟨x, hx⟩
    have hgf : g.comp f = 0 := h.linearMap_comp_eq_zero
    have : g (f x₁) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun m => m x₁) hgf
    have hxL : x ∈ LinearMap.ker q := by
      simp [LinearMap.mem_ker, q, LinearMap.comp_apply, hx, this]
    refine ⟨⟨x, hxL⟩, e.injective <| Subtype.ext ?_⟩
    simp [p, toRange, e, hx, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  have hexact : Function.Exact i p := by
    rw [LinearMap.exact_iff]
    ext y
    constructor
    · intro hy
      have hy0 : p y = 0 := by simpa [LinearMap.mem_ker] using hy
      have hyTo : toRange y = 0 := by
        have : e (p y) = e 0 := by simp [hy0]
        simp [p] at this
        exact this
      have hyπ : π₂ y.1 = 0 := by
        have : (toRange y).1 = 0 := congrArg Subtype.val hyTo
        simpa [toRange, LinearMap.codRestrict_apply, LinearMap.comp_apply] using this
      refine ⟨⟨y.1, hyπ⟩, ?_⟩
      apply Subtype.ext
      simp [i]
    · rintro ⟨x, rfl⟩
      have : π₂ x.1 = 0 := x.2
      change p (i x) = 0
      have hto : toRange (i x) = 0 := by
        apply Subtype.ext
        simp [toRange, i, this, LinearMap.codRestrict_apply, LinearMap.comp_apply]
      simp [p, hto]
  have hL : HasFiniteFreeResolution R (LinearMap.ker q) :=
    hasFiniteFreeResolution_of_shortExact_of_left_of_right (LinearMap.ker π₂) (LinearMap.ker q) P₁
      hi hp hexact hK₂ h₁
  rcases hasFiniteFreeResolutionLength_of_hasFiniteFreeResolution (LinearMap.ker q) hL with ⟨m, hm⟩
  exact ⟨F₂, inferInstance, inferInstance, inferInstance, inferInstance, q, hq, m, hm⟩

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right (P₁ P₂ P₃ : Type*)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₂ : HasFiniteFreeResolution R P₂)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₁ := by
  rcases h₂ with ⟨F₂, _, _, _, _, π₂, hπ₂, n₂, hK₂len⟩
  have hK₂ : HasFiniteFreeResolution R (LinearMap.ker π₂) :=
    hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength (LinearMap.ker π₂) ⟨n₂, hK₂len⟩
  have hF₂ : HasFiniteFreeResolution R F₂ := hasFiniteFreeResolution_of_finite_of_free F₂
  let q : F₂ →ₗ[R] P₃ := g.comp π₂
  have hq : Function.Surjective q := hg.comp hπ₂
  rcases h₃ with ⟨F₃, _, _, _, _, π₃, hπ₃, n₃, hK₃len⟩
  have hK₃ : HasFiniteFreeResolution R (LinearMap.ker π₃) :=
    hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength (LinearMap.ker π₃) ⟨n₃, hK₃len⟩
  have hF₃ : HasFiniteFreeResolution R F₃ := hasFiniteFreeResolution_of_finite_of_free F₃
  -- Compare `q : F₂ → P₃` with the chosen surjection `π₃ : F₃ → P₃`.
  let d : (F₂ × F₃) →ₗ[R] P₃ := q.coprod (-π₃)
  let Kd := LinearMap.ker d
  -- Short exact sequence `ker π₃ → ker d → F₂`.
  let j : (LinearMap.ker π₃) →ₗ[R] Kd :=
    LinearMap.codRestrict Kd ((LinearMap.inr R F₂ F₃).comp (Submodule.subtype π₃.ker)) <| by
      intro y
      change d ((0 : F₂), y.1) = 0
      simp [d, LinearMap.coprod_apply]
  let pr₁ : Kd →ₗ[R] F₂ := (LinearMap.fst R F₂ F₃).comp (Submodule.subtype Kd)
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    simpa [j] using congrArg Prod.snd (congrArg Subtype.val hxy)
  have hpr₁ : Function.Surjective pr₁ := by
    intro x₂
    rcases hπ₃ (q x₂) with ⟨y₃, hy₃⟩
    have hx : d (x₂, y₃) = 0 := by
      -- `q x₂ - π₃ y₃ = 0`
      simp [d, LinearMap.coprod_apply, hy₃]
    exact ⟨⟨(x₂, y₃), by simpa [LinearMap.mem_ker] using hx⟩, rfl⟩
  have hexact₁ : Function.Exact j pr₁ := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hx0 : pr₁ x = 0 := by simpa [LinearMap.mem_ker] using hx
      have hxF₂ : x.1.1 = 0 := by simpa [pr₁] using hx0
      refine ⟨⟨x.1.2, ?_⟩, ?_⟩
      · -- `x.1.2 ∈ ker π₃` since `x ∈ ker d` and `x.1.1 = 0`.
        have hxker : d x.1 = 0 := x.2
        have : π₃ x.1.2 = 0 := by
          -- expand `d` at `x.1 = (0, x.1.2)`
          have hxpair : x.1 = (0, x.1.2) := by
            ext <;> simp [hxF₂]
          have hxker' := hxker
          rw [hxpair] at hxker'
          have : d (0, x.1.2) = 0 := hxker'
          -- `d (0,y) = -π₃ y`
          simpa [d, LinearMap.coprod_apply] using this
        simpa [LinearMap.mem_ker] using this
      · apply Subtype.ext
        ext <;> simp [j, hxF₂]
    · rintro ⟨y, rfl⟩
      -- `pr₁ (j y) = 0`.
      change pr₁ (j y) = 0
      simp [pr₁, j, LinearMap.codRestrict_apply]
  have hKd : HasFiniteFreeResolution R Kd :=
    hasFiniteFreeResolution_of_shortExact_of_left_of_right (LinearMap.ker π₃) Kd F₂ hj hpr₁
      hexact₁ hK₃ hF₂
  -- Use projectivity of `F₃` to lift `π₃` along `q`.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (f := q) (g := π₃) hq
  -- Short exact sequence `F₃ → ker d → ker q`.
  let k : F₃ →ₗ[R] Kd := LinearMap.codRestrict Kd (LinearMap.prod s LinearMap.id) <| by
    intro y
    have hs' : q (s y) = π₃ y := by
      simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hs
    change d (s y, y) = 0
    simp [d, LinearMap.coprod_apply, hs']
  let r0 : Kd →ₗ[R] F₂ := ((LinearMap.fst R F₂ F₃).comp (Submodule.subtype Kd)) -
    (s.comp ((LinearMap.snd R F₂ F₃).comp (Submodule.subtype Kd)))
  let r : Kd →ₗ[R] (LinearMap.ker q) := LinearMap.codRestrict (LinearMap.ker q) r0 <| by
    intro x
    have hxker : d x.1 = 0 := x.2
    have hxEq : q x.1.1 = π₃ x.1.2 := by
      dsimp [d] at hxker
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg, LinearMap.neg_apply] using hxker)
    have hs' : q (s x.1.2) = π₃ x.1.2 := by
      simpa [LinearMap.comp_apply] using congrArg (fun m => m x.1.2) hs
    simp [LinearMap.mem_ker, r0, map_sub, hxEq, hs', LinearMap.comp_apply]
  have hk : Function.Injective k := by
    intro x y hxy
    have : (k x).1.2 = (k y).1.2 := congrArg Prod.snd (congrArg Subtype.val hxy)
    simpa [k] using this
  have hr : Function.Surjective r := by
    intro z
    refine ⟨⟨(z.1, 0), ?_⟩, ?_⟩
    · -- membership in `ker d`
      have hz : q z.1 = 0 := z.2
      have : d (z.1, 0) = 0 := by simp [d, LinearMap.coprod_apply, hz]
      simpa [LinearMap.mem_ker] using this
    · apply Subtype.ext
      simp [r, r0, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  have hexact₂ : Function.Exact k r := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · intro hx
      have hx0 : r x = 0 := by simpa [LinearMap.mem_ker] using hx
      have hx0' : r0 x = 0 := congrArg Subtype.val hx0
      have hxEq : x.1.1 = s x.1.2 := by
        -- from `x.1.1 - s x.1.2 = 0`.
        have : x.1.1 - s x.1.2 = 0 := by
          simpa [r0, LinearMap.sub_apply, LinearMap.comp_apply] using hx0'
        exact sub_eq_zero.mp this
      refine ⟨x.1.2, ?_⟩
      apply Subtype.ext
      ext <;> simp [k, hxEq]
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simp [r, r0, k, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  have hL : HasFiniteFreeResolution R (LinearMap.ker q) :=
    hasFiniteFreeResolution_of_shortExact_of_left_of_middle F₃ Kd (LinearMap.ker q) hk hr hexact₂
      hF₃ hKd
  -- Finally, use the short exact sequence `ker π₂ → ker q → P₁`.
  let i : (LinearMap.ker π₂) →ₗ[R] (LinearMap.ker q) :=
    LinearMap.codRestrict (LinearMap.ker q) (Submodule.subtype (LinearMap.ker π₂)) <| by
      simp [q, LinearMap.mem_ker, LinearMap.comp_apply]
  let e : P₁ ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  let toRange : (LinearMap.ker q) →ₗ[R] (LinearMap.range f) :=
    LinearMap.codRestrict (LinearMap.range f) (π₂.comp (Submodule.subtype q.ker)) <| by
      simpa using fun y hy => (h _).mp hy
  let p : (LinearMap.ker q) →ₗ[R] P₁ := e.symm.toLinearMap.comp toRange
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    simpa [i] using congrArg Subtype.val hxy
  have hp : Function.Surjective p := by
    intro x₁
    rcases hπ₂ (f x₁) with ⟨x, hx⟩
    have hgf : g.comp f = 0 := h.linearMap_comp_eq_zero
    have : g (f x₁) = 0 := by simpa [LinearMap.comp_apply] using congrArg (fun m => m x₁) hgf
    have hxL : x ∈ LinearMap.ker q := by simp [q, LinearMap.comp_apply, hx, this]
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply e.injective
    apply Subtype.ext
    simp [p, toRange, e, hx, LinearMap.codRestrict_apply, LinearMap.comp_apply]
  have hexact₃ : Function.Exact i p := by
    rw [LinearMap.exact_iff]
    ext y
    constructor
    · intro hy
      have hy0 : p y = 0 := by simpa [LinearMap.mem_ker] using hy
      have hyTo : toRange y = 0 := by
        have : e (p y) = e 0 := by simp [hy0]
        simp [p] at this
        exact this
      have hyπ : π₂ y.1 = 0 := by
        have : (toRange y).1 = 0 := congrArg Subtype.val hyTo
        simpa [toRange, LinearMap.codRestrict_apply, LinearMap.comp_apply] using this
      refine ⟨⟨y.1, hyπ⟩, ?_⟩
      apply Subtype.ext
      simp [i]
    · rintro ⟨x, rfl⟩
      have : π₂ x.1 = 0 := x.2
      change p (i x) = 0
      have hto : toRange (i x) = 0 := by
        apply Subtype.ext
        simp [toRange, i, this, LinearMap.codRestrict_apply, LinearMap.comp_apply]
      simp [p, hto]
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_middle π₂.ker q.ker P₁ hi hp hexact₃ hK₂ hL

end exact_seq

open Polynomial Module Ideal

section polynomial

/-- A subsingleton finitely generated module has a finite free resolution. -/
theorem hasFiniteFreeResolution_of_subsingleton (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    HasFiniteFreeResolution R M :=
  hasFiniteFreeResolution_of_finite_of_free M

/-- Push a finite free resolution of an `R`-ideal `I` to a resolution of `I · R[X]`. -/
theorem hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution
    (I : Ideal R) (hI : HasFiniteFreeResolution R I) :
    HasFiniteFreeResolution R[X] (Ideal.map (C : R →+* R[X]) I) := by
  rcases hasFiniteFreeResolutionLength_of_hasFiniteFreeResolution I hI with ⟨n, hn⟩
  let polyMap {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
      (f : P →ₗ[R] Q) : PolynomialModule R P →ₗ[R[X]] PolynomialModule R Q :=
    { toFun := PolynomialModule.map R f
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro p q
        simp [PolynomialModule.map_smul R f p q] }
  have liftLength : ∀ {P : Type u} [AddCommGroup P] [Module R P] {n : ℕ},
      HasFiniteFreeResolutionLength R P n →
        HasFiniteFreeResolutionLength R[X] (PolynomialModule R P) n := by
    intro P _ _ n hn
    induction hn with
    | zero P =>
        let e := PolynomialModule.polynomialTensorProductLEquivPolynomialModule R P
        let : Module.Finite R[X] (PolynomialModule R P) :=
          Module.Finite.of_surjective e.toLinearMap e.surjective
        let : Module.Free R[X] (PolynomialModule R P) := Module.Free.of_equiv e
        exact HasFiniteFreeResolutionLength.zero (PolynomialModule R P)
    | succ P n F f hf hker ih =>
        let eF := PolynomialModule.polynomialTensorProductLEquivPolynomialModule R F
        let : Module.Finite R[X] (PolynomialModule R F) :=
          Module.Finite.of_surjective eF.toLinearMap eF.surjective
        let : Module.Free R[X] (PolynomialModule R F) := Module.Free.of_equiv eF
        let fX := polyMap f
        have hfX : Function.Surjective fX := by
          intro y
          induction y using PolynomialModule.induction_linear with
          | zero => exact ⟨0, by simp [fX, polyMap]⟩
          | add y z hy hz =>
              rcases hy with ⟨y, rfl⟩
              rcases hz with ⟨z, rfl⟩
              refine ⟨y + z, by simp [fX, polyMap]⟩
          | single i m =>
              rcases hf m with ⟨x, rfl⟩
              refine ⟨PolynomialModule.single R i x, by simp [fX, polyMap]⟩
        let sub : LinearMap.ker f →ₗ[R] F := (LinearMap.ker f).subtype
        let kX : PolynomialModule R (LinearMap.ker f) →ₗ[R[X]] PolynomialModule R F :=
          polyMap sub
        have hkX : LinearMap.ker fX = LinearMap.range kX := by
          ext y
          constructor
          · intro hy
            have hy0 : fX y = 0 := by simpa using hy
            let z : PolynomialModule R (LinearMap.ker f) :=
              Finsupp.onFinset y.support
                (fun a => ⟨y a, by
                  have : (fX y) a = 0 := congrArg (fun g => g a) hy0
                  simpa [fX, polyMap, PolynomialModule.map, Finsupp.mapRange_apply] using this⟩)
                (by
                  intro a ha
                  have : y a ≠ 0 := by
                    intro hya
                    apply ha
                    apply Subtype.ext
                    simp [hya]
                  exact (Finsupp.mem_support_iff).2 this)
            refine ⟨z, ?_⟩
            apply Finsupp.ext
            intro a
            have hz : ((Finsupp.mapRange.linearMap sub) z) a = sub (z a) := by
              simp [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
            simp [kX, polyMap, PolynomialModule.map]
            refine hz.trans ?_
            simp [z, Finsupp.onFinset_apply, sub]
          · rintro ⟨z, rfl⟩
            show fX (kX z) = 0
            apply Finsupp.ext
            intro a
            dsimp [fX, kX, polyMap, PolynomialModule.map]
            have hz : ((Finsupp.mapRange.linearMap sub) z) a = sub (z a) := by
              simp [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
            have hzKer : f (sub (z a)) = 0 := (z a).2
            have hcoeff : ((Finsupp.mapRange.linearMap f) ((Finsupp.mapRange.linearMap sub) z)) a =
                f (((Finsupp.mapRange.linearMap sub) z) a) := by
              simp [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
            exact hcoeff.trans ((congrArg f hz).trans hzKer)
        have hkerX : HasFiniteFreeResolutionLength R[X] (LinearMap.ker fX) n := by
          have hkX' : LinearMap.range kX = LinearMap.ker fX := hkX.symm
          have hinj : Function.Injective kX := by
            intro x y hxy
            apply Finsupp.ext
            intro a
            apply Subtype.ext
            have hxy' : (kX x) a = (kX y) a := congrArg (fun g => g a) hxy
            let mx := Finsupp.mapRange.linearMap (α := ℕ) sub
            have hxy0 : (mx x) a = (mx y) a := by
              simp [kX, polyMap, PolynomialModule.map] at hxy'
              exact hxy'
            have hx0 : (mx x) a = sub (x a) := by
              simp [mx, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
            have hy0 : (mx y) a = sub (y a) := by
              simp [mx, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
            have hsub : sub (x a) = sub (y a) := by
              calc _ = (mx x) a := hx0.symm
                _ = (mx y) a := hxy0
                _ = sub (y a) := hy0
            dsimp [sub] at hsub
            exact hsub
          exact hasFiniteFreeResolutionLength_of_linearEquiv
            ((LinearEquiv.ofInjective kX hinj).trans (LinearEquiv.ofEq _ _ hkX')) ih
        exact HasFiniteFreeResolutionLength.succ (PolynomialModule R P) n
          (PolynomialModule R F) fX hfX hkerX
  have hPoly : HasFiniteFreeResolution R[X] (PolynomialModule R I) :=
    hasFiniteFreeResolution_of_hasFiniteFreeResolutionLength (PolynomialModule R I)
      ⟨n, liftLength hn⟩
  let incl : I →ₗ[R] R := I.subtype
  let inclX : PolynomialModule R I →ₗ[R[X]] PolynomialModule R R := polyMap incl
  have inclX_apply (p : PolynomialModule R I) (n : ℕ) : (inclX p) n = (p n : R) := by
    simp [inclX, polyMap, PolynomialModule.map]
    change (fun q => q n) ((Finsupp.mapRange.linearMap incl) p) = p n
    have h := congrArg (fun q => q n) (Finsupp.mapRange.linearMap_apply (f := incl) p)
    rw [h]
    simp [Finsupp.mapRange_apply, incl]
  let φ0 : PolynomialModule R I →ₗ[R[X]] R[X] :=
    PolynomialModule.equivPolynomialSelf.toLinearMap.comp inclX
  have hφ0inj : Function.Injective φ0 := by
    intro x y hxy
    have hxy' : inclX x = inclX y := by
      simpa [φ0] using congrArg PolynomialModule.equivPolynomialSelf.symm hxy
    apply Finsupp.ext
    intro a
    apply Subtype.ext
    have hxy0 : (inclX x) a = (inclX y) a := congrArg (fun g => g a) hxy'
    let mx := Finsupp.mapRange.linearMap (α := ℕ) incl
    have hxy1 : (mx x) a = (mx y) a := by
      have h := hxy0
      simp [inclX, polyMap, PolynomialModule.map] at h
      exact h
    have hx0 : (mx x) a = incl (x a) := by
      simp [mx, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    have hy0 : (mx y) a = incl (y a) := by
      simp [mx, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    have hincl : incl (x a) = incl (y a) := by
      calc _ = (mx x) a := hx0.symm
        _ = (mx y) a := hxy1
        _ = incl (y a) := hy0
    dsimp [incl] at hincl
    exact hincl
  have hφ0range : LinearMap.range φ0 = (Ideal.map (C : R →+* R[X]) I : Ideal R[X]) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      refine (Ideal.mem_map_C_iff (I := I)).2 fun n => ?_
      have : (φ0 p).coeff n = (inclX p) n := by
        simp [φ0, PolynomialModule.equivPolynomialSelf, toFinsuppIso,
          coeff_ofFinsupp]
      have hp : (inclX p) n = (p n : R) := inclX_apply p n
      rw [this, hp]
      exact (p n).2
    · intro hf
      have hf' : ∀ n, f.coeff n ∈ I := (Ideal.mem_map_C_iff (I := I)).1 hf
      let p : PolynomialModule R I := Finsupp.onFinset f.support (fun n => ⟨f.coeff n, hf' n⟩) <| by
          intro n hn
          have : f.coeff n ≠ 0 := by
            intro h0
            apply hn
            apply Subtype.ext
            simp [h0]
          exact (Polynomial.mem_support_iff).2 this
      refine ⟨p, ?_⟩
      apply Polynomial.ext
      intro n
      have hφ : (φ0 p).coeff n = (inclX p) n := by
        simp [φ0, PolynomialModule.equivPolynomialSelf, toFinsuppIso,
          coeff_ofFinsupp]
      rw [hφ, inclX_apply p n]
      simp [p, Finsupp.onFinset_apply]
  exact hasFiniteFreeResolution_of_linearEquiv
    ((LinearEquiv.ofInjective φ0 hφ0inj).trans (LinearEquiv.ofEq _ _ hφ0range)) hPoly

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
    (hP : ∀ x : R, C x ∈ P → x = 0) (hPne : P ≠ ⊥) :
    ∃ d : R, d ≠ 0 ∧ ∃ f : R[X], f ∈ P ∧ f ≠ 0 ∧
      ∀ g ∈ P, C d * g ∈ Ideal.span ({f} : Set (R[X])) := by
  classical
  have hPfg : P.FG := IsNoetherian.noetherian P
  rcases hPfg with ⟨s, hs⟩
  obtain ⟨⟨p0, hp0P⟩, hp0ne⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.2 hPne)
  have hp0ne' : p0 ≠ 0 := by
    intro h0
    apply hp0ne
    simp [Subtype.ext_iff, h0]
  -- Pick `f ∈ P` of minimal `natDegree` among the nonzero elements of `P`.
  let Q : ℕ → Prop := fun n => ∃ f : R[X], f ∈ P ∧ f ≠ 0 ∧ f.natDegree = n
  have hQ : ∃ n, Q n := ⟨p0.natDegree, p0, hp0P, hp0ne', rfl⟩
  set nmin : ℕ := Nat.find hQ
  have hspec : Q nmin := Nat.find_spec hQ
  rcases hspec with ⟨f, hfP, hfne, hfnat⟩
  have hfmin : ∀ g : R[X], g ∈ P → g ≠ 0 → f.natDegree ≤ g.natDegree := by
    intro g hg hgne
    have : Q g.natDegree := ⟨g, hg, hgne, rfl⟩
    have hle : nmin ≤ g.natDegree := Nat.find_min' hQ this
    simpa [hfnat] using hle
  -- `f` cannot have degree `0`, because `P ∩ R = (0)`.
  have hf_natDegree_ne_zero : f.natDegree ≠ 0 := by
    intro hdeg0
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
    have hmem : C (f.coeff 0) ∈ P := hfC ▸ hfP
    have hcoeff0 : f.coeff 0 = 0 := hP (f.coeff 0) hmem
    apply hfne
    calc f = C (f.coeff 0) := hfC
      _ = C 0 := by simp [hcoeff0]
      _ = 0 := by simp
  let K := FractionRing R
  let i : R →+* K := algebraMap R K
  have hi : Function.Injective i := IsFractionRing.injective R K
  let fK : K[X] := f.map i
  have hfKne : fK ≠ 0 := by
    intro h0
    apply hfne
    exact (Polynomial.map_injective i hi) (by simpa [fK] using h0)
  have hfK_natDegree_ne_zero : fK.natDegree ≠ 0 := by
    have hfKdeg : fK.natDegree = f.natDegree := by
      simpa [fK] using (natDegree_map_eq_of_injective (f := i) hi f)
    simpa only [hfKdeg, ne_eq] using hf_natDegree_ne_zero
  -- `K[X]` is the localization of `R[X]` at constant nonzero divisors.
  let : Algebra R[X] K[X] := (mapRingHom (algebraMap R K)).toAlgebra
  have : IsLocalization ((nonZeroDivisors R).map (C : R →+* R[X])) K[X] := by
    simpa using (isLocalization (nonZeroDivisors R) K)
  -- Define quotients and remainders in `K[X]` for the generators.
  let q (g : R[X]) : K[X] := (g.map i) / fK
  let r (g : R[X]) : K[X] := (g.map i) % fK
  let fracs : Finset K[X] := s.biUnion fun g => ({q g, r g} : Finset K[X])
  -- Clear denominators of all `q g` and `r g` simultaneously in the localization `K[X]`.
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    ((nonZeroDivisors R).map (C : R →+* R[X])) fracs
  -- Extract `d ≠ 0` from the denominator `b`, which lives in `((nonZeroDivisors R).map C)`.
  rcases b.2 with ⟨d, hd, hdEq⟩
  have hbEq : (b : R[X]) = C d := by
    simpa using hdEq.symm
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hid0 : i d ≠ 0 := by
    intro h0
    apply hd0
    exact hi (by simpa only [map_zero] using h0)
  -- First handle the generators.
  have hgen : ∀ g, g ∈ (s : Set R[X]) → C d * g ∈ Ideal.span ({f} : Set R[X]) := by
    intro g hg
    have hg' : g ∈ s := by simpa using hg
    have hq : IsLocalization.IsInteger (R[X]) ((b : R[X]) • q g) := by
      have : q g ∈ fracs := by
        refine Finset.mem_biUnion.2 ⟨g, hg', ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
      simpa only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] using hb (q g) this
    have hr : IsLocalization.IsInteger (R[X]) ((b : R[X]) • r g) := by
      have : r g ∈ fracs := by
        refine Finset.mem_biUnion.2 ⟨g, hg', ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
      simpa [Algebra.smul_def] using hb (r g) this
    rcases hq with ⟨qR, hqR⟩
    rcases hr with ⟨rR, hrR⟩
    have hdiv : q g * fK + r g = (g.map i) := by
      simpa only [mul_comm, add_comm] using (EuclideanDomain.div_add_mod (g.map i) fK)
    -- Pull back the equality `b • (g.map i) = (b • q g) * fK + (b • r g)` to `R[X]`.
    have hEq : (b : R[X]) * g = qR * f + rR := by
      apply (map_injective i hi)
      have : (mapRingHom i) ((b : R[X]) * g) = (mapRingHom i) (qR * f + rR) := by
        have hqR' : (mapRingHom i) (b : R[X]) * q g = (mapRingHom i) qR := by
          simpa [Algebra.smul_def, mul_assoc] using (Eq.symm hqR)
        have hrR' : (mapRingHom i) (b : R[X]) * r g = (mapRingHom i) rR := by
          simpa [Algebra.smul_def, mul_assoc] using (Eq.symm hrR)
        calc _ = (mapRingHom i) (b : R[X]) * (g.map i) := by simp only [coe_mapRingHom, map_mul]
          _ = (mapRingHom i) (b : R[X]) * (q g * fK + r g) := by simp only [coe_mapRingHom, hdiv]
          _ = (mapRingHom i) (b : R[X]) * (q g * fK) + (mapRingHom i) (b : R[X]) * r g := by
            simp only [coe_mapRingHom, mul_add]
          _ = (mapRingHom i) qR * fK + (mapRingHom i) rR := by
            have hqRmul : (mapRingHom i) (b : R[X]) * (q g * fK) = (mapRingHom i) qR * fK := by
              calc _ = ((mapRingHom i) (b : R[X]) * q g) * fK := by simp [mul_assoc]
                _ = (mapRingHom i) qR * fK := by simpa using congrArg (fun t => t * fK) hqR'
            calc _ = (mapRingHom i) qR * fK + (mapRingHom i) (b : R[X]) * r g := by simpa [hqRmul]
              _ = (mapRingHom i) qR * fK + (mapRingHom i) rR := by
                simpa only [coe_mapRingHom, add_right_inj]
          _ = (mapRingHom i) (qR * f) + (mapRingHom i) rR := by simp [fK, map_mul]
          _ = (mapRingHom i) (qR * f + rR) := by simp [map_add, map_mul]
      simpa only [Polynomial.map_mul, Polynomial.map_add, coe_mapRingHom] using this
    -- `rR ∈ P` because `rR = b * g - qR * f` and `P` is an ideal.
    have hrRP : rR ∈ P := by
      have hgP : g ∈ P := by
        -- `g` is a generator, hence belongs to `P`.
        simpa [hs] using (Ideal.subset_span hg)
      have hbgg : (b : R[X]) * g ∈ P := P.mul_mem_left _ hgP
      have hqff : qR * f ∈ P := P.mul_mem_left _ hfP
      have : rR = (b : R[X]) * g - qR * f := by
        -- First get `b*g - qR*f = rR`, then flip.
        have hsub : (b : R[X]) * g - qR * f = rR := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg (fun t => t - qR * f) hEq
        simpa only [sub_eq_add_neg] using hsub.symm
      have hmem : (b : R[X]) * g - qR * f ∈ P := P.sub_mem hbgg hqff
      simpa [this] using hmem
    -- Compare degrees to show the remainder vanishes.
    have hdegK : (r g).natDegree < fK.natDegree := by
      simpa only using natDegree_mod_lt (g.map i) hfK_natDegree_ne_zero
    have hdegK' : (rR.map i).natDegree < fK.natDegree := by
      -- `rR.map i = (C (i d)) * (r g)`
      have hrR' : rR.map i = C (i d) * r g := by
        simpa [Algebra.smul_def, hbEq, map_mul] using hrR
      simpa [hrR', natDegree_C_mul (p := r g) hid0] using hdegK
    have hrdeg : rR.natDegree < f.natDegree := by
      have hrRdeg : (rR.map i).natDegree = rR.natDegree := by
        simpa only [natDegree_map_eq_iff, ne_eq] using (natDegree_map_eq_of_injective hi rR)
      have hfKdeg : fK.natDegree = f.natDegree := by
        simpa [fK] using (natDegree_map_eq_of_injective hi f)
      simpa [hrRdeg, hfKdeg] using hdegK'
    have hrR0 : rR = 0 := by
      by_contra hrR0
      have hle : f.natDegree ≤ rR.natDegree := hfmin rR hrRP hrR0
      exact (not_lt_of_ge hle) hrdeg
    have hEq' : (b : R[X]) * g = qR * f := by
      simpa [hrR0] using hEq
    have hbmem : (b : R[X]) * g ∈ Ideal.span ({f} : Set R[X]) := by
      refine (Ideal.mem_span_singleton.2 ?_)
      refine ⟨qR, ?_⟩
      -- `Ideal.mem_span_singleton` is divisibility: provide `b*g = f*qR`.
      calc _ = qR * f := hEq'
        _ = f * qR := by simp [mul_comm]
    simpa [hbEq] using hbmem
  refine ⟨d, hd0, f, hfP, hfne, ?_⟩
  intro g hgP
  have hgspan : g ∈ Ideal.span (s : Set R[X]) := by simpa [hs] using hgP
  -- Extend from generators to all of `P = Ideal.span s`.
  exact Submodule.span_induction hgen (by simp only [mul_zero, zero_mem])
    (fun x y _ _ hx hy => by simpa only [mul_add] using Ideal.add_mem _ hx hy)
    (fun a x _ hx => by
      have : C d * (a * x) = a * (C d * x) := by simp only [mul_comm, mul_assoc]
      simpa only [smul_eq_mul, this] using Ideal.mul_mem_left _ a hx) hgspan

set_option maxHeartbeats 600000 in
private theorem hasFiniteFreeResolution_quotient_prime_aux [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P) : ∀ I : Ideal R, ∀ q : PrimeSpectrum R[X],
    Ideal.comap (C : R →+* R[X]) q.1 = I → HasFiniteFreeResolution (R[X]) (R[X] ⧸ q.1) := by
  -- Noetherian induction on the contraction `p.1 ∩ R`.
  let A : Type u := R[X]
  let contr : PrimeSpectrum A → Ideal R := fun q => Ideal.comap (C : R →+* A) q.1
  refine IsNoetherian.induction (P := fun I : Ideal R =>
    ∀ q : PrimeSpectrum A, contr q = I → HasFiniteFreeResolution A (A ⧸ q.1)) ?_
  intro I ih q hqI
  let P : Ideal A := q.1
  have : P.IsPrime := q.2
  have hcomap : Ideal.comap (C : R →+* A) P = I := by simpa [contr, P] using hqI
  have hIA_le_P : Ideal.map (C : R →+* A) I ≤ P :=
    (Ideal.map_le_iff_le_comap).2 <| by simp [hcomap]
  let IA : Ideal A := Ideal.map (C : R →+* A) I
  -- If `P = I·A`, then `A ⧸ P` is the polynomial ring over `R ⧸ I`.
  by_cases hPIA : P = IA
  · have hI_res : HasFiniteFreeResolution R I := hR I inferInstance
    have hIA_res : HasFiniteFreeResolution A IA :=
      hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution I hI_res
    have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free A
    have hquot : HasFiniteFreeResolution A (A ⧸ IA) :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle IA A (A ⧸ IA)
        (f := IA.subtype) (g := IA.mkQ) Subtype.coe_injective (Submodule.mkQ_surjective IA)
          (by simpa using LinearMap.exact_subtype_mkQ IA) hIA_res hA
    have hquotP : HasFiniteFreeResolution A (A ⧸ P) :=
      hasFiniteFreeResolution_of_linearEquiv (Submodule.quotEquivOfEq IA P hPIA.symm) hquot
    simpa [P] using hquotP
  -- Otherwise, reduce mod `I` and use the "clearing denominators" lemma over the domain `R ⧸ I`.
  · -- `I` is prime since it is the contraction of the prime ideal `P`.
    have hIprime : Ideal.IsPrime I := by
      simpa [hcomap] using show (Ideal.comap (C : R →+* A) P).IsPrime from inferInstance
    let R₀ : Type u := R ⧸ I
    let A₀ : Type u := R₀[X]
    -- Quotient of `A` by `I·A`, and the corresponding prime ideal `P₀` in `(R ⧸ I)[X]`.
    let B : Type u := A ⧸ IA
    let π : A →+* B := Ideal.Quotient.mk IA
    let Pbar : Ideal B := Ideal.map π P
    let e : A₀ ≃+* B := Ideal.polynomialQuotientEquivQuotientPolynomial I
    let P₀ : Ideal A₀ := Ideal.comap e.toRingHom Pbar
    have hPbar_ne : Pbar ≠ ⊥ := by
      intro hbot
      have hle : P ≤ RingHom.ker π := (P.map_eq_bot_iff_le_ker π).1 hbot
      have hker : RingHom.ker π = IA := IA.mk_ker
      have hP_le_IA : P ≤ IA := by
        simpa [A, hker] using hle
      exact hPIA (le_antisymm hP_le_IA hIA_le_P)
    have hP₀_ne : P₀ ≠ ⊥ := by
      intro hbot
      have : Ideal.map e.toRingHom P₀ = Pbar := by
        simpa [P₀] using (Ideal.map_comap_of_surjective e.toRingHom e.surjective Pbar)
      have : Pbar = ⊥ := by simpa [hbot] using this.symm
      exact hPbar_ne this
    -- `P₀ ∩ R₀ = (0)`, i.e. `C x ∈ P₀ → x = 0`.
    have hP₀_contr : ∀ x : R₀, (C x : A₀) ∈ P₀ → x = 0 := by
      intro x hx
      rcases Ideal.Quotient.mk_surjective x with ⟨r, rfl⟩
      have hx' : (e (C (Ideal.Quotient.mk I r) : A₀)) ∈ Pbar := by
        simpa [P₀, Ideal.mem_comap] using hx
      have hCr : e (C (Ideal.Quotient.mk I r) : A₀) = (Ideal.Quotient.mk IA) (C r) := by
        -- use the computation lemma for `polynomialQuotientEquivQuotientPolynomial`.
        simpa [IA, Polynomial.map_C] using
          (Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk I (C r : A))
      have hx'' : (Ideal.Quotient.mk IA) (C r) ∈ Pbar := by simpa [hCr] using hx'
      rcases (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).1 hx'' with
        ⟨a, haP, haEq⟩
      have hab : a - C r ∈ IA := (Ideal.Quotient.eq).1 haEq
      have habP : a - C r ∈ P := hIA_le_P hab
      have hCrP : (C r : A) ∈ P := by
        have : (C r : A) = a - (a - C r) := by abel
        exact this ▸ P.sub_mem haP habP
      have hrI : r ∈ I := by
        have : r ∈ Ideal.comap (C : R →+* A) P := by simpa [Ideal.mem_comap] using hCrP
        simpa [hcomap] using this
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hrI
    -- Apply the clearing-denominators lemma to `P₀`.
    obtain ⟨d₀, hd₀, f₀, hf₀P₀, hf₀ne, hmul₀⟩ :=
      exists_nonzero_C_mul_mem_span_singleton hP₀_contr hP₀_ne
    -- Choose a lift `d : R` of `d₀` (so `d ∉ I`).
    rcases Ideal.Quotient.mk_surjective (I := I) d₀ with ⟨d, rfl⟩
    have hd_not_mem : d ∉ I := by
      intro hdI
      apply hd₀
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hdI
    -- Transport `f₀` to `B` and define the principal ideal `(f̄) ⊆ P̄`.
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
      -- `x ∈ (f̄)` implies `x = y * f̄`.
      rcases (Ideal.mem_span_singleton.1 hx) with ⟨y, rfl⟩
      exact Pbar.mul_mem_right y hfbar_mem
    -- Translate `d₀·P₀ ⊆ (f₀)` to `d·P̄ ⊆ (f̄)` in `B`.
    have hmul_bar : ∀ g : B, g ∈ Pbar → (Ideal.Quotient.mk IA (C d) : B) * g ∈ Fbar := by
      intro g hg
      -- Pull back along the ring equivalence `e`.
      let g₀ : A₀ := e.symm g
      have hg₀ : g₀ ∈ P₀ := by
        -- membership in the comap is exactly membership of the image.
        have : (e g₀) ∈ Pbar := by simpa [g₀] using hg
        simpa [P₀, Ideal.mem_comap] using this
      have h0 : (C (Ideal.Quotient.mk I d) : A₀) * g₀ ∈ Ideal.span ({f₀} : Set A₀) :=
        hmul₀ g₀ hg₀
      have hCd : e (C (Ideal.Quotient.mk I d) : A₀) = (Ideal.Quotient.mk IA) (C d) := by
        simpa [IA, Polynomial.map_C] using
          (Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk (I := I) (f := (C d : A)))
      -- Map the containment through `e` and rewrite the image of the principal ideal.
      have hmem : e ((C (Ideal.Quotient.mk I d) : A₀) * g₀) ∈
          Ideal.map e.toRingHom (Ideal.span ({f₀} : Set A₀)) :=
        Ideal.mem_map_of_mem e.toRingHom h0
      -- Convert `Ideal.map` of a principal ideal to a principal ideal.
      have hspan :
          Ideal.map (e : A₀ →+* B) (Ideal.span ({f₀} : Set A₀)) = Ideal.span ({fbar} : Set B) := by
        -- `e '' {f₀} = {f̄}`.
        simpa [fbar] using (Ideal.map_span e.toRingHom ({f₀} : Set A₀))
      -- Finish.
      have : e (C (Ideal.Quotient.mk I d) : A₀) * e g₀ ∈ Fbar := by
        -- rewrite and use the membership above
        simpa [Fbar, hspan, map_mul] using hmem
      simpa [g₀, hCd] using this
    -- Define the quotient module `N := P̄/(f̄)`, viewed as an `A`-module via `A → B`.
    let Psub : Submodule A B := (Pbar : Submodule B B).restrictScalars A
    let Fsub : Submodule A B := (Fbar : Submodule B B).restrictScalars A
    have hFsub_le : Fsub ≤ Psub := by
      intro x hx
      exact hFbar_le hx
    let K : Submodule A Psub := Submodule.comap Psub.subtype Fsub
    let N := Psub ⧸ K
    let acgN : AddCommGroup N := Submodule.Quotient.addCommGroup K
    let : AddCommMonoid N := acgN.toAddCommMonoid
    -- `C d` annihilates `N`.
    have hAnn_d : ∀ x : N, (C d : A) • x = 0 := by
      intro x
      refine Quotient.inductionOn' x ?_
      intro y
      -- Reduce to membership in `K`.
      have hyF : ((C d : A) • (y : B)) ∈ Fsub := by
        have hyFmul : (π (C d) : B) * (y : B) ∈ Fsub := by
          have : (Ideal.Quotient.mk IA (C d) : B) * (y : B) ∈ Fbar := hmul_bar (y : B) y.2
          simpa [Fsub, π] using this
        have hsmul : ((C d : A) • (y : B)) = (π (C d) : B) * (y : B) := by
          have hAlgebraMap : (algebraMap A B) = π := rfl
          simpa [hAlgebraMap] using
            (Algebra.smul_def (R := A) (A := B) (r := (C d : A)) (x := (y : B)))
        simpa [hsmul] using hyFmul
      have hyK : (C d : A) • y ∈ K := by
        -- By definition of `K` as a comap.
        simpa [K] using hyF
      have h0 : Submodule.Quotient.mk ((C d : A) • y) = (0 : N) :=
        (Submodule.Quotient.mk_eq_zero K).2 hyK
      -- Rewrite `r • mk y` as `mk (r • y)`.
      have hmksmul : Submodule.Quotient.mk ((C d : A) • y) = (C d : A) • Submodule.Quotient.mk y :=
        Submodule.Quotient.mk_smul K (C d : A) y
      exact hmksmul.symm.trans h0
    -- `N` has a finite free resolution, by decomposing into prime quotients.
    have hN : HasFiniteFreeResolution A N := by
      have hAnn_I : ∀ r : R, r ∈ I → ∀ x : N, (C r : A) • x = 0 := by
        intro r hrI x
        refine Quotient.inductionOn' x ?_
        intro y
        have hCrIA : (C r : A) ∈ IA := Ideal.mem_map_of_mem (C : R →+* A) hrI
        have hπCr : (π (C r) : B) = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hCrIA
        have hy0 : (C r : A) • (y : B) = 0 := by
          have hAlgebraMap : (algebraMap A B) = π := rfl
          -- rewrite the scalar action on `B`, then use `hπCr`.
          have hsmul : (C r : A) • (y : B) = (π (C r) : B) * (y : B) := by
            simpa [hAlgebraMap] using (Algebra.smul_def (C r : A) (y : B))
          -- now `π (C r) = 0`.
          simp [hsmul, hπCr]
        have hyF : (C r : A) • (y : B) ∈ Fsub := by simp [hy0]
        have hyK : (C r : A) • y ∈ K := by simpa [K] using hyF
        have h0 : Submodule.Quotient.mk (p := K) ((C r : A) • y) = (0 : N) :=
          (Submodule.Quotient.mk_eq_zero K).2 hyK
        have hmksmul : Submodule.Quotient.mk (p := K) ((C r : A) • y) =
            (C r : A) • Submodule.Quotient.mk (p := K) y :=
          Submodule.Quotient.mk_smul K (r := (C r : A)) (x := y)
        exact hmksmul.symm.trans h0
      let motive : ∀ (M : Type u), [AddCommGroup M] → [Module A M] → [Module.Finite A M] → Prop :=
        fun M _ _ _ => (∀ x : M, (C d : A) • x = 0) →
          (∀ r : R, r ∈ I → ∀ x : M, (C r : A) • x = 0) → HasFiniteFreeResolution A M
      have hN' : motive N := by
        refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A
          inferInstance (motive := motive) ?_ ?_ ?_
        · intro M _ _ _ _ _ _
          exact hasFiniteFreeResolution_of_subsingleton M
        · intro M _ _ _ p' eM hAnn_dM hAnn_IM
          -- Show the contraction of `p'` is strictly larger than `I`.
          have hCd0_M : (C d : A) • (1 : A ⧸ p'.1) = 0 := by
            have h := hAnn_dM (eM.symm (1 : A ⧸ p'.1))
            have h' : eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := congrArg eM h
            have hs :
                eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) = (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) :=
              eM.map_smul (C d : A) (eM.symm (1 : A ⧸ p'.1))
            have h'' : (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := by
              calc _ = eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) := hs.symm
                _ = eM (0 : M) := h'
            have : (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) = (0 : A ⧸ p'.1) :=
              h''.trans eM.map_zero
            have h1 : eM (eM.symm (1 : A ⧸ p'.1)) = (1 : A ⧸ p'.1) :=
              eM.apply_symm_apply (1 : A ⧸ p'.1)
            rwa [← h1]
          have hCd_mem : (C d : A) ∈ p'.1 := by
            have hmk : (Ideal.Quotient.mk p'.1 (C d : A) : A ⧸ p'.1) = 0 := by
              have h := hCd0_M
              rw [Algebra.smul_def] at h
              rw [mul_one] at h
              -- `algebraMap` for the quotient algebra is definitional.
              have hAlgebraMap : (algebraMap A (A ⧸ p'.1)) = Ideal.Quotient.mk p'.1 := rfl
              -- Rewrite the `algebraMap` in `h` using `rw`.
              simpa using by
                -- `rw` shows `algebraMap` to the quotient map.
                rwa [hAlgebraMap] at h
            exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk
          have hI_le_contr : I ≤ Ideal.comap (C : R →+* A) p'.1 := by
            intro r hrI
            have hCr0_M : (C r : A) • (1 : A ⧸ p'.1) = 0 := by
              have h := hAnn_IM r hrI (eM.symm (1 : A ⧸ p'.1))
              have h' : eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := congrArg eM h
              have hs : eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) =
                  (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) :=
                eM.map_smul (C r : A) (eM.symm (1 : A ⧸ p'.1))
              have h'' : (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := by
                calc _ = eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) := hs.symm
                  _ = eM (0 : M) := h'
              have : (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) = (0 : A ⧸ p'.1) :=
                h''.trans eM.map_zero
              have h1 : eM (eM.symm (1 : A ⧸ p'.1)) = (1 : A ⧸ p'.1) :=
                eM.apply_symm_apply (1 : A ⧸ p'.1)
              rwa [← h1]
            have hCr_mem : (C r : A) ∈ p'.1 := by
              have hmk : (Ideal.Quotient.mk p'.1 (C r : A) : A ⧸ p'.1) = 0 := by
                have h := hCr0_M
                rw [Algebra.smul_def] at h
                rw [mul_one] at h
                have hAlgebraMap : (algebraMap A (A ⧸ p'.1)) = Ideal.Quotient.mk p'.1 := rfl
                simpa using by
                  rwa [hAlgebraMap] at h
              exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk
            simpa [Ideal.mem_comap] using hCr_mem
          have hlt : Ideal.comap (C : R →+* A) p'.1 > I := by
            refine lt_of_le_of_ne hI_le_contr ?_
            intro hEq
            have : d ∈ I := by
              have : d ∈ Ideal.comap (C : R →+* A) p'.1 := by
                simpa [Ideal.mem_comap] using hCd_mem
              simpa [hEq] using this
            exact hd_not_mem this
          have hquot : HasFiniteFreeResolution A (A ⧸ p'.1) :=
            ih (Ideal.comap (C : R →+* A) p'.1) hlt p' rfl
          exact hasFiniteFreeResolution_of_linearEquiv (R := A) eM.symm hquot
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
          exact hasFiniteFreeResolution_of_shortExact_of_left_of_right M₁ M₂ M₃ hf hg hfg h₁' h₃'
      exact hN' hAnn_d hAnn_I
    -- `B` has a finite free resolution as an `A`-module.
    have hI_res : HasFiniteFreeResolution R I := hR I inferInstance
    have hIA_res : HasFiniteFreeResolution A IA :=
      hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution I hI_res
    have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free (R := A) A
    have hB : HasFiniteFreeResolution A B :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle IA A (A ⧸ IA)
        (f := IA.subtype) (g := IA.mkQ) Subtype.coe_injective (Submodule.mkQ_surjective IA)
          (by simpa using (LinearMap.exact_subtype_mkQ IA)) hIA_res hA
    -- `(f̄)` has a finite free resolution since `B` is a domain.
    have : IsDomain B := MulEquiv.isDomain (A := B) (B := A₀) e.symm.toMulEquiv
    have hFbar : HasFiniteFreeResolution A Fbar :=
      hasFiniteFreeResolution_of_linearEquiv
        ((linearEquiv_mul_spanSingleton hfbar_ne).restrictScalars A) hB
    -- Identify `K` with `Fbar` and conclude `Pbar` has a finite free resolution from
    -- `0 → K → Psub → N → 0`.
    have hK : HasFiniteFreeResolution A K :=
      have hFsub : HasFiniteFreeResolution A Fsub := by simpa [Fsub] using hFbar
      hasFiniteFreeResolution_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hFsub_le).symm hFsub
    have hPbar : HasFiniteFreeResolution A Psub := by
      -- Short exact sequence `0 → K → Psub → N → 0`.
      refine hasFiniteFreeResolution_of_shortExact_of_left_of_right K Psub N
        (f := (K.subtype).restrictScalars A) (g := (K.mkQ).restrictScalars A)
        (hf := Subtype.coe_injective) (hg := Submodule.mkQ_surjective K)
        (h := by simpa using LinearMap.exact_subtype_mkQ K) hK hN
    -- Lift back to `P ⊂ A` using `0 → IA → P → Pbar → 0`, then conclude for `A ⧸ P`.
    -- Map `P` to `Pbar` by the quotient map `π`.
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
      rcases (Ideal.mem_map_iff_of_surjective π (Ideal.Quotient.mk_surjective (I := IA))).1 y.2 with
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
      hasFiniteFreeResolution_of_shortExact_of_left_of_right IA P Pbar hfIP hgPP hexPP
        hIA_res <| by simpa only [Psub] using hPbar
    -- Finally, `0 → P → A → A ⧸ P → 0`.
    have hquot : HasFiniteFreeResolution A (A ⧸ P) :=
      hasFiniteFreeResolution_of_shortExact_of_left_of_middle P A (A ⧸ P)
        (f := P.subtype) (g := P.mkQ) Subtype.coe_injective (Submodule.mkQ_surjective P)
          (by simpa only [Submodule.coe_subtype] using (LinearMap.exact_subtype_mkQ P)) hP hA
    exact hquot

variable (R)

theorem hasFiniteFreeResolution_quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) := by
  simpa using hasFiniteFreeResolution_quotient_prime_aux hR (Ideal.comap (C : R →+* R[X]) p.1) p rfl

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem polynomial_hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] :
    HasFiniteFreeResolution R[X] P :=
  IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R[X]
    inferInstance (motive := fun N _ _ _ => HasFiniteFreeResolution R[X] N)
      (fun N _ _ _ _ => hasFiniteFreeResolution_of_subsingleton N)
      (fun _ _ _ _ p e => hasFiniteFreeResolution_of_linearEquiv e.symm
        (hasFiniteFreeResolution_quotient_prime R hR p))
      (fun N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ _ _ hf hg hfg h₁ h₃ =>
        hasFiniteFreeResolution_of_shortExact_of_left_of_right N₁ N₂ N₃ hf hg hfg h₁ h₃)

end polynomial

section MvPolynomial

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
  let : Fintype s := Fintype.ofFinite s
  let n : ℕ := Fintype.card s
  let a : s ≃ Fin n := Fintype.equivFin s
  let e : MvPolynomial s R ≃+* MvPolynomial (Fin n) R := (MvPolynomial.renameEquiv R a).toRingEquiv
  let B : Type u := MvPolynomial (Fin n) R
  let : Module B P := Module.compHom P e.symm.toRingHom
  have : Module.Finite B P := by simpa [B] using (moduleFinite_of_ringEquiv' e.symm P)
  have : Small.{u} P := Module.Finite.small B P
  let P' : Type u := Shrink.{u} P
  have : Module.Finite B P' :=
    Module.Finite.of_surjective ((Shrink.linearEquiv B P).symm.toLinearMap)
      (Shrink.linearEquiv B P).symm.surjective
  have hP' : HasFiniteFreeResolution B P' :=
    mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing_aux (Fin n) hR P'
  have hPB : HasFiniteFreeResolution B P := by
    simpa [P'] using hasFiniteFreeResolution_of_linearEquiv (Shrink.linearEquiv B P) hP'
  let UB : Type (max u w) := ULift.{w} B
  let eU : MvPolynomial s R ≃+* UB := e.trans ringEquivULift.symm
  let instUB₀ : Module UB P := Module.compHom P ringEquivULift.toRingHom
  have hUB₀ : HasFiniteFreeResolution UB P := by
    simpa [UB] using (hasFiniteFreeResolution_ulift P hPB)
  let instUB₁ : Module UB P := Module.compHom P eU.symm.toRingHom
  have hinst : instUB₀ = instUB₁ := by
    refine Module.ext' instUB₀ instUB₁ ?_
    intro b x
    simp [instUB₀, instUB₁, eU, Module.compHom]
  have hUB₁ : @HasFiniteFreeResolution UB P _ _ instUB₁ := by
    simpa [hinst] using (show @HasFiniteFreeResolution UB P _ _ instUB₀ from hUB₀)
  have hU' : (let : Module UB P := instUB₁; HasFiniteFreeResolution UB P) := by simpa using hUB₁
  simpa [UB] using hasFiniteFreeResolution_of_ringEquiv_left eU P hU'

end MvPolynomial
