import Mathlib

universe u v w

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

variable {R : Type u} [CommRing R]

section exact_seq

/-- Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third. -/
theorem isStablyFree_two_of_three_of_shortExact (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [AddCommGroup P₂] [Module R P₂]
    [AddCommGroup P₃] [Module R P₃] [Module.Finite R P₃] [Module.Projective R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
      (IsStablyFree R P₁ → IsStablyFree R P₂ → IsStablyFree R P₃) ∧
        (IsStablyFree R P₁ → IsStablyFree R P₃ → IsStablyFree R P₂) ∧
          (IsStablyFree R P₂ → IsStablyFree R P₃ → IsStablyFree R P₁) := by
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.2 hg)
  set eSigma := h.splitSurjectiveEquiv hf ⟨l, hl⟩ with heSigma
  set e : P₂ ≃ₗ[R] P₁ × P₃ := eSigma.1 with he
  refine ⟨?_, ?_⟩
  · intro hP₁ hP₂
    rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
    rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
    refine ⟨(P₁ × N₁) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    -- Rewrite `P₃ × ((P₁ × N₁) × N₂)` as `((P₂ × N₂) × N₁)` using the splitting `P₂ ≃ P₁ × P₃`.
    let eP₃ : (P₃ × ((P₁ × N₁) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₁) :=
      (LinearEquiv.prodAssoc R P₃ (P₁ × N₁) N₂).symm ≪≫ₗ
        (LinearEquiv.prodAssoc R P₃ P₁ N₁).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
          ((LinearEquiv.prodComm R P₃ P₁).prodCongr (LinearEquiv.refl R N₁)).prodCongr
              (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₁ N₂ ≪≫ₗ
              (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₁ N₂) ≪≫ₗ
                (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₁).symm ≪≫ₗ
                  (((e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₁)))
    exact Module.Free.of_equiv eP₃.symm
  · refine ⟨?_, ?_⟩
    · intro hP₁ hP₃
      rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨N₁ × N₃, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₂ : (P₂ × (N₁ × N₃)) ≃ₗ[R] ((P₁ × N₁) × (P₃ × N₃)) :=
        e.prodCongr (LinearEquiv.refl R (N₁ × N₃)) ≪≫ₗ LinearEquiv.prodProdProdComm R P₁ P₃ N₁ N₃
      exact Module.Free.of_equiv eP₂.symm
    · intro hP₂ hP₃
      rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨(P₃ × N₃) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₁ : (P₁ × ((P₃ × N₃) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₃) :=
        (LinearEquiv.prodAssoc R P₁ (P₃ × N₃) N₂).symm ≪≫ₗ
          (LinearEquiv.prodAssoc R P₁ P₃ N₃).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
            ((LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.refl R N₃)).prodCongr
                (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₃ N₂ ≪≫ₗ
                (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₃ N₂) ≪≫ₗ
                  (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₃).symm ≪≫ₗ
                    (e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₃)
      exact Module.Free.of_equiv eP₁.symm

/-- `HasFiniteFreeResolutionLength R P n` means `P` admits a free resolution of length `n`
by finitely generated free modules. We use the convention that length `0` means `P` itself is
finitely generated and free, and the successor step is given by a surjection from a finitely
generated free module with kernel admitting a shorter resolution. -/
inductive HasFiniteFreeResolutionLength (R : Type u) [CommRing R] :
    ∀ (P : Type v), [AddCommGroup P] → [Module R P] → ℕ → Prop
  | zero (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Free R P] :
      HasFiniteFreeResolutionLength R P 0
  | succ (P : Type v) [AddCommGroup P] [Module R P] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]
      (f : F →ₗ[R] P) (hf : Function.Surjective f)
      (hker : HasFiniteFreeResolutionLength R (LinearMap.ker f) n) :
      HasFiniteFreeResolutionLength R P (n + 1)

/-- A module `P` over a commutative ring `R` has a finite free resolution if it has a resolution
of some finite length by finitely generated free `R`-modules. -/
def HasFiniteFreeResolution (R : Type u) (P : Type v)
    [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ n : ℕ, HasFiniteFreeResolutionLength R P n

/-- A finitely generated free module has a finite free resolution (of length `0`). -/
theorem hasFiniteFreeResolution_of_finite_of_free (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Free R P] : HasFiniteFreeResolution R P :=
  ⟨0, HasFiniteFreeResolutionLength.zero P⟩

private theorem hasFiniteFreeResolutionLength_of_linearEquiv_aux (P : Type v) [AddCommGroup P]
    [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) :
    ∀ {Q : Type v} [AddCommGroup Q] [Module R Q], (e : P ≃ₗ[R] Q) →
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

theorem hasFiniteFreeResolutionLength_of_linearEquiv {P Q : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) : HasFiniteFreeResolutionLength R Q n :=
  hasFiniteFreeResolutionLength_of_linearEquiv_aux P hn e

/-- Transport `HasFiniteFreeResolution` along an `R`-linear equivalence. -/
theorem hasFiniteFreeResolution_of_linearEquiv {P Q : Type v}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (h : HasFiniteFreeResolution R P) : HasFiniteFreeResolution R Q := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, hasFiniteFreeResolutionLength_of_linearEquiv e hn⟩

/-- Extract a surjection `F →ₗ[R] P` from a finite free resolution of `P`.
For length `0` we use the identity map. -/
theorem exists_surjective_of_hasFiniteFreeResolutionLength (P : Type v)
    [AddCommGroup P] [Module R P] {n : ℕ} (hn : HasFiniteFreeResolutionLength R P n) :
      ∃ (F : Type v) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Finite R F)
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

/-- Horseshoe lemma for finite free resolutions (2-out-of-3: left + right ⇒ middle). -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right_length (P₁ P₂ P₃ : Type v)
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
      exact ⟨Nat.pred n₃ + 1,
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
      rcases hK₂ with ⟨m, hm⟩
      refine ⟨m + 1, ?_⟩
      exact HasFiniteFreeResolutionLength.succ P₂ m (F₁ × F₃) φ hφsurj hm

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₃` have finite free
resolutions, then so does `P₂`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_right (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₂ := by
  rcases h₁ with ⟨n₁, hn₁⟩
  rcases h₃ with ⟨n₃, hn₃⟩
  exact hasFiniteFreeResolution_of_shortExact_of_left_of_right_length P₁ P₂ P₃ hf hg h hn₁ hn₃

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₁` and `P₂` have finite free
resolutions, then so does `P₃`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_left_of_middle (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₁ : HasFiniteFreeResolution R P₁)
    (h₂ : HasFiniteFreeResolution R P₂) : HasFiniteFreeResolution R P₃ := by
  rcases h₁ with ⟨n₁, hn₁⟩
  rcases h₂ with ⟨n₂, hn₂⟩
  rcases exists_surjective_of_hasFiniteFreeResolutionLength P₂ hn₂ with
    ⟨F₂, _, _, _, _, π₂, hπ₂, hK₂len⟩
  have hK₂ : HasFiniteFreeResolution R (LinearMap.ker π₂) := ⟨Nat.pred n₂, hK₂len⟩
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
      hi hp hexact hK₂ ⟨n₁, hn₁⟩
  rcases hL with ⟨m, hm⟩
  refine ⟨m + 1, ?_⟩
  exact HasFiniteFreeResolutionLength.succ P₃ m F₂ q hq hm

/-- In a short exact sequence `0 → P₁ → P₂ → P₃ → 0`, if `P₂` and `P₃` have finite free
resolutions, then so does `P₁`. -/
theorem hasFiniteFreeResolution_of_shortExact_of_middle_of_right (P₁ P₂ P₃ : Type v)
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup P₃] [Module R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) (h₂ : HasFiniteFreeResolution R P₂)
    (h₃ : HasFiniteFreeResolution R P₃) : HasFiniteFreeResolution R P₁ := by
  rcases h₂ with ⟨n₂, hn₂⟩
  rcases h₃ with ⟨n₃, hn₃⟩
  rcases exists_surjective_of_hasFiniteFreeResolutionLength P₂ hn₂ with
    ⟨F₂, _, _, _, _, π₂, hπ₂, hK₂len⟩
  have hK₂ : HasFiniteFreeResolution R (LinearMap.ker π₂) := ⟨Nat.pred n₂, hK₂len⟩
  have hF₂ : HasFiniteFreeResolution R F₂ := hasFiniteFreeResolution_of_finite_of_free F₂
  let q : F₂ →ₗ[R] P₃ := g.comp π₂
  have hq : Function.Surjective q := hg.comp hπ₂
  rcases exists_surjective_of_hasFiniteFreeResolutionLength P₃ hn₃ with
    ⟨F₃, _, _, _, _, π₃, hπ₃, hK₃len⟩
  have hK₃ : HasFiniteFreeResolution R (LinearMap.ker π₃) := ⟨Nat.pred n₃, hK₃len⟩
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

section polynomial

open Polynomial Module Ideal

/-- A subsingleton finitely generated module has a finite free resolution. -/
theorem hasFiniteFreeResolution_of_subsingleton (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    HasFiniteFreeResolution R M :=
  hasFiniteFreeResolution_of_finite_of_free M

/-- Push a finite free resolution of an `R`-ideal `I` to a resolution of `I · R[X]`. -/
theorem hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution
    (I : Ideal R) (hI : HasFiniteFreeResolution R I) :
    HasFiniteFreeResolution R[X] (Ideal.map (C : R →+* R[X]) I) := by
  rcases hI with ⟨n, hn⟩
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
        exact HasFiniteFreeResolutionLength.zero (P := PolynomialModule R P)
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
  have hPoly : HasFiniteFreeResolution R[X] (PolynomialModule R I) := ⟨n, liftLength hn⟩
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
noncomputable def linearEquiv_mul_spanSingleton [IsDomain R] (f : R)
    (hf : f ≠ 0) : R ≃ₗ[R] (Ideal.span ({f} : Set R) : Ideal R) :=
  Ideal.isoBaseOfIsPrincipal <| (Submodule.ne_bot_iff (span {f})).mpr
    ⟨f, mem_span_singleton_self f, hf⟩

/-- If `P ⊂ R[X]` is an ideal over a Noetherian domain `R` with `P ∩ R = (0)`, then there exists
  `d ≠ 0` and `f ∈ P` such that `d • P ⊆ (f)`. -/
theorem exists_nonzero_C_mul_mem_span_singleton [IsDomain R] [IsNoetherianRing R] (P : Ideal (R[X]))
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
/-
theorem hasFiniteFreeResolution_quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) := by
  sorry

/-- Reduce the prime-quotient case to the corresponding prime ideal as an `R[X]`-module. -/
theorem hasFiniteFreeResolution_primeIdeal [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Ideal (R[X])) (hP : P.IsPrime) : HasFiniteFreeResolution (R[X]) P := by
  classical
  let p : PrimeSpectrum (R[X]) := ⟨P, hP⟩
  have hquot : HasFiniteFreeResolution (R[X]) (R[X] ⧸ P) :=
    hasFiniteFreeResolution_quotient_prime (R := R) hR p
  have hA : HasFiniteFreeResolution (R[X]) (R[X]) :=
    hasFiniteFreeResolution_of_finite_of_free (R := (R[X])) (R[X])
  -- Use `0 → P → R[X] → R[X]/P → 0`.
  refine hasFiniteFreeResolution_of_shortExact_of_middle_of_right (R := (R[X])) P (R[X]) (R[X] ⧸ P)
    (f := P.subtype) (g := P.mkQ) (hf := Subtype.coe_injective)
    (hg := Submodule.mkQ_surjective P)
    (h := by simpa using (LinearMap.exact_subtype_mkQ P))
    hA hquot

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type u) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] :
    HasFiniteFreeResolution (Polynomial R) P := by
  classical
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := R[X]) (M := P)
    (by infer_instance) (motive := fun N _ _ _ => HasFiniteFreeResolution R[X] N)
    (subsingleton := fun N _ _ _ _ => hasFiniteFreeResolution_of_subsingleton (R := R[X]) N)
    (quotient := fun N _ _ _ p e =>
      hasFiniteFreeResolution_of_linearEquiv (R := R[X]) e.symm
        (hasFiniteFreeResolution_quotient_prime (R := R) hR p))
    (exact := fun N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ =>
      hasFiniteFreeResolution_of_shortExact_of_left_of_right (R := R[X]) N₁ N₂ N₃ hf hg hfg h₁ h₃)
 -/
end polynomial
