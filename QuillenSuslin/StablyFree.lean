import Mathlib

universe u v

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
    [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂] [Module.Projective R P₂]
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
    ∀ {Q : Type v} [AddCommGroup Q] [Module R Q], (P ≃ₗ[R] Q) →
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
  let k : F₃ →ₗ[R] Kd :=
    LinearMap.codRestrict Kd (LinearMap.prod s LinearMap.id) <| by
      intro y
      have hs' : q (s y) = π₃ y := by
        simpa [LinearMap.comp_apply] using congrArg (fun m => m y) hs
      change d (s y, y) = 0
      simp [d, LinearMap.coprod_apply, hs']
  let r0 : Kd →ₗ[R] F₂ := ((LinearMap.fst R F₂ F₃).comp (Submodule.subtype Kd)) -
    (s.comp ((LinearMap.snd R F₂ F₃).comp (Submodule.subtype Kd)))
  let r : Kd →ₗ[R] (LinearMap.ker q) :=
    LinearMap.codRestrict (LinearMap.ker q) r0 <| by
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

open Polynomial Module

/-- Let `R` be a noetherian ring such that every finitely generated `R`-module admits a finite
free resolution. Then the same property holds for finitely generated `R[X]`-modules. -/
theorem hasFiniteFreeResolution_of_isNoetherianRing [IsNoetherianRing R]
    (hR : ∀ (P : Type v), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type v) [AddCommGroup P] [Module R[X] P] [Module.Finite R[X] P] :
    HasFiniteFreeResolution (Polynomial R) P :=
  sorry

end polynomial

/-
\begin{definition}
	A finitely generated module $P$ over a commutative ring $R$ is said to be stably free if there exists a finitely generated free module $F$ such that the direct sum $P \oplus F$ is a free module.
\end{definition}

\begin{lemma}\label{exact_seq}
	Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third.
\end{lemma}

\begin{proposition}
	Let $R$ be a commutative Noetherian ring. Let $x$ be a variable. If every finite $R$-module has a finite free resolution, then every finite $R[x]$-module has a finite free resolution.
\end{proposition}

\begin{proof}
	Let $M$ be a finite $R[x]$-module. $M$ has a finite filtration
	$$M = M_0 \supset M_1 \supset \dots \supset M_n = 0$$
	such that each factor $M_i/M_{i+1}$ is isomorphic to $R[x]/P_i$ for some prime $P_i$. In light of Lemma \ref{exact_seq}, it suffices to prove the theorem in case $M = R[x]/P$ where $P$ is prime, which we now assume. In light of the exact sequence
	$$0 \to P \to R[x] \to R[x]/P \to 0$$
	and Lemma \ref{exact_seq}, we note that $M$ has a finite free resolution if and only if $P$ does.

	Let $\mathfrak{p} = P \cap R$. Then $\mathfrak{p}$ is prime in $R$. Suppose there is some $M = R[x]/P$ which does not admit a finite free resolution. Among all such $M$ we select one for which the intersection $\mathfrak{p}$ is maximal in the family of prime ideals obtained as above. This is possible in light of one of the basic properties characterizing Noetherian rings.

	Let $R_0 = R/\mathfrak{p}$ so $R_0$ is entire. Let $P_0 = P/\mathfrak{p}R[x]$. Then we may view $M$ as an $R_0[x]$-module, equal to $R_0/P_0$. Let $f_1, \dots, f_n$ be a finite set of generators for $P_0$, and let $f$ be a polynomial of minimal degree in $P_0$. Let $K_0$ be the quotient field of $R_0$. By the euclidean algorithm, we can write
	$$f_i = q_i f + r_i \quad \text{for } i = 1, \dots, n$$
	with $q_i, r_i \in K_0[x]$ and $\deg r_i < \deg f$. Let $d_0$ be a common denominator for the coefficients of all $q_i, r_i$. Then $d_0 \neq 0$ and
	$$d_0 f_i = q'_i f + r'_i$$
	where $q'_i = d_0 q_i$ and $r'_i = d_0 r_i$ lie in $R_0[x]$. Since $\deg f$ is minimal in $P_0$ it follows that $r'_i = 0$ for all $i$, so
	$$d_0 P_0 \subset R_0[x]f = (f).$$

	Let $N_0 = P_0/(f)$, so $N_0$ is a module over $R_0[x]$, and we can also view $N_0$ as a module over $R[x]$. When so viewed, we denote $N_0$ by $N$. Let $d \in R$ be any element reducing to $d_0 \pmod{\mathfrak{p}}$. Then $d \notin \mathfrak{p}$ since $d_0 \neq 0$. The module $N_0$ has a finite filtration such that each factor module of the filtration is isomorphic to some $R_0[x]/\bar{Q}_0$ where $\bar{Q}_0$ is an associated prime of $N_0$. Let $Q$ be the inverse image of $\bar{Q}_0$ in $R[x]$. These prime ideals $Q$ are precisely the associated primes of $N$ in $R[x]$. Since $d_0$ kills $N_0$ it follows that $d$ kills $N$ and therefore $d$ lies in every associated prime of $N$. By the maximality property in the selection of $P$, it follows that every one of the factor modules in the filtration of $N$ has a finite free resolution, and by Lemma \ref{exact_seq} it follows that $N$ itself has a finite free resolution.

	Now we view $R_0[x]$ as an $R[x]$-module, via the canonical homomorphism
	$$R[x] \to R_0[x] = R[x]/\mathfrak{p}R[x].$$
	By assumption, $\mathfrak{p}$ has a finite free resolution as $R$-module, say
	$$0 \to E_n \to \dots \to E_0 \to \mathfrak{p} \to 0.$$
	Then we may simply form the modules $E_i[x]$ in the obvious sense to obtain a finite free resolution of $\mathfrak{p}[x] = \mathfrak{p}R[x]$. From the exact sequence
	$$0 \to \mathfrak{p}R[x] \to R[x] \to R_0[x] \to 0$$
	we conclude that $R_0[x]$ has a finite free resolution as $R[x]$-module.

	Since $R_0$ is entire, it follows that the principal ideal $(f)$ in $R_0[x]$ is $R[x]$-isomorphic to $R_0[x]$, and therefore has a finite free resolution as $R[x]$-module. Lemma \ref{exact_seq} applied to the exact sequence of $R[x]$-modules
	$$0 \to (f) \to P_0 \to N \to 0$$
	shows that $P_0$ has a finite free resolution, and further applied to the exact sequence
	$$0 \to \mathfrak{p}R[x] \to P \to P_0 \to 0$$
	shows that $P$ has a finite free resolution, thereby concluding the proof.
\end{proof}

-/
