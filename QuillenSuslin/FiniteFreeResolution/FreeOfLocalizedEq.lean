import Mathlib.LinearAlgebra.Determinant
import QuillenSuslin.FiniteFreeResolution.StablyFree

universe u

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

noncomputable def stableMatrix {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (m : M) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j =>
    if h : j = 0 then e.toFun (m, 0) i
    else e.toFun (0, Pi.basisFun R (Fin n) (Fin.pred j (by simpa using h))) i

noncomputable def stableBaseMatrix {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  stableMatrix e 0

noncomputable def stableMap {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) : M →ₗ[R] R where
  toFun m := (stableMatrix e m).det
  map_add' m₁ m₂ := by
    have hm :
        stableMatrix e (m₁ + m₂) =
          (stableBaseMatrix e).updateCol 0
            (e.toFun (m₁, 0) + e.toFun (m₂, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simpa [stableMatrix, stableBaseMatrix] using
          congrFun (map_add e (m₁, 0) (m₂, 0)) i
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm₁ :
        stableMatrix e m₁ =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m₁, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simp [stableMatrix, stableBaseMatrix]
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm₂ :
        stableMatrix e m₂ =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m₂, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simp [stableMatrix, stableBaseMatrix]
      · simp [stableMatrix, stableBaseMatrix, h]
    rw [hm, Matrix.det_updateCol_add, hm₁, hm₂]
  map_smul' r m := by
    have hm :
        stableMatrix e (r • m) =
          (stableBaseMatrix e).updateCol 0 (r • e.toFun (m, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simpa [stableMatrix, stableBaseMatrix, smul_eq_mul] using
          congrFun (map_smulₛₗ e r (m, 0)) i
      · simp [stableMatrix, stableBaseMatrix, h]
    have hm' :
        stableMatrix e m =
          (stableBaseMatrix e).updateCol 0 (e.toFun (m, 0)) := by
      ext i j
      by_cases h : j = 0
      · subst h
        simp [stableMatrix, stableBaseMatrix]
      · simp [stableMatrix, stableBaseMatrix, h]
    rw [hm, Matrix.det_updateCol_smul, hm']
    simp

theorem isUnit_stableMap_of_linearEquiv {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (u : M ≃ₗ[R] R) :
    IsUnit (stableMap e (u.symm 1)) := by
  let e' : (R × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R) :=
    (u.symm.prodCongr (LinearEquiv.refl R (Fin n → R))) ≪≫ₗ e
  have hmatrix :
      stableMatrix e (u.symm 1) =
        LinearMap.toMatrix
          (Pi.basisFun R (Fin (n + 1)))
          (Pi.basisFun R (Fin (n + 1)))
          (((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm ≪≫ₗ e').toLinearMap) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    by_cases h : j = 0
    · subst h
      have htail :
          Fin.tail (show Fin (n + 1) → R from Pi.single (0 : Fin (n + 1)) (1 : R)) = 0 := by
        funext k
        simp [Fin.tail_def]
      simp [stableMatrix, e', htail]
    · simp [stableMatrix, e', h]
      have htail :
          Fin.tail (show Fin (n + 1) → R from Pi.single j (1 : R)) =
            Pi.basisFun R (Fin n) (j.pred (by simpa using h)) := by
        funext k
        rw [Fin.tail_def, Pi.basisFun_apply]
        show (show Fin (n + 1) → R from Pi.single j (1 : R)) k.succ =
          (show Fin n → R from Pi.single (j.pred (by simpa using h)) (1 : R)) k
        by_cases hk : k = j.pred (by simpa using h)
        · subst hk
          simp [Pi.single, Fin.succ_pred j (by simpa using h)]
        · have hne : k.succ ≠ j := by
            intro hEq
            apply hk
            exact Fin.succ_injective _ <| by
              simpa [Fin.succ_pred j (by simpa using h)] using hEq
          simp [Pi.single, hne, hk]
      simp [htail]
  show IsUnit ((stableMatrix e (u.symm 1)).det)
  rw [hmatrix]
  exact LinearEquiv.isUnit_det
    (((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).symm ≪≫ₗ e')
      : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (Pi.basisFun R (Fin (n + 1)))
    (Pi.basisFun R (Fin (n + 1)))

theorem stableMap_bijective_of_linearEquiv {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) (u : M ≃ₗ[R] R) :
    Function.Bijective (stableMap e) := by
  let a : R := stableMap e (u.symm 1)
  have ha : IsUnit a := by
    simpa [a] using isUnit_stableMap_of_linearEquiv e u
  have hrepr : ∀ m, m = (u m) • u.symm 1 := by
    intro m
    apply u.injective
    simp
  have hm : ∀ m, stableMap e m = u m * a := by
    intro m
    rw [hrepr m, LinearMap.map_smul]
    simp [a, smul_eq_mul, mul_comm]
  constructor
  · intro m₁ m₂ h
    apply u.injective
    rcases ha with ⟨a', ha'⟩
    have h' : u m₁ * ↑a' = u m₂ * ↑a' := by
      simpa [hm m₁, hm m₂, ha'] using h
    have h'' := congrArg (fun x : R => x * ↑a'⁻¹) h'
    simpa [mul_assoc] using h''
  · intro b
    rcases ha with ⟨a', ha'⟩
    refine ⟨(b * ↑a'⁻¹) • u.symm 1, ?_⟩
    rw [hm]
    rw [← ha']
    simp [mul_assoc]

@[simp] lemma IsLocalizedModule.linearEquiv_apply_mk'
    {A : Type u} [AddCommGroup A] [Module R A]
    {B : Type u} [AddCommGroup B] [Module R B]
    {C : Type u} [AddCommGroup C] [Module R C]
    (S : Submonoid R) (f : A →ₗ[R] B) [IsLocalizedModule S f]
    (g : A →ₗ[R] C) [IsLocalizedModule S g]
    (x : A) (s : S) :
    (IsLocalizedModule.linearEquiv S f g) (IsLocalizedModule.mk' f x s) =
      IsLocalizedModule.mk' g x s := by
  apply (IsLocalizedModule.smul_inj (f := g) s _ _).1
  show ((s : R) • (IsLocalizedModule.linearEquiv S f g (IsLocalizedModule.mk' f x s))) =
    ((s : R) • IsLocalizedModule.mk' g x s)
  calc
    (s : R) • (IsLocalizedModule.linearEquiv S f g (IsLocalizedModule.mk' f x s))
        = IsLocalizedModule.linearEquiv S f g ((s : R) • IsLocalizedModule.mk' f x s) := by simp
    _ = IsLocalizedModule.linearEquiv S f g (f x) := by
          exact congrArg (IsLocalizedModule.linearEquiv S f g)
            (IsLocalizedModule.mk'_cancel' (f := f) x s)
    _ = g x := IsLocalizedModule.linearEquiv_apply S f g x
    _ = (s : R) • IsLocalizedModule.mk' g x s := by
          symm
          exact IsLocalizedModule.mk'_cancel' (f := g) x s

@[simp] lemma IsLocalizedModule.linearEquiv_symm_apply_mk'
    {A : Type u} [AddCommGroup A] [Module R A]
    {B : Type u} [AddCommGroup B] [Module R B]
    {C : Type u} [AddCommGroup C] [Module R C]
    (S : Submonoid R) (f : A →ₗ[R] B) [IsLocalizedModule S f]
    (g : A →ₗ[R] C) [IsLocalizedModule S g]
    (x : A) (s : S) :
    (IsLocalizedModule.linearEquiv S f g).symm (IsLocalizedModule.mk' g x s) =
      IsLocalizedModule.mk' f x s := by
  apply (IsLocalizedModule.linearEquiv S f g).injective
  simp

noncomputable def localizedProdMap (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    (M × N) →ₗ[R] (LocalizedModule S M × LocalizedModule S N) :=
  LinearMap.prod (LocalizedModule.mkLinearMap S M ∘ₗ LinearMap.fst R M N)
    (LocalizedModule.mkLinearMap S N ∘ₗ LinearMap.snd R M N)

instance localizedProdMap_isLocalizedModule (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    IsLocalizedModule S (localizedProdMap S M N) := by
  let f := localizedProdMap S M N
  show IsLocalizedModule S f
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    refine (Module.End.isUnit_iff _).2 ?_
    have hM := (Module.End.isUnit_iff _).1
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) s)
    have hN := (Module.End.isUnit_iff _).1
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S N) s)
    constructor
    · intro x y hxy
      apply Prod.ext
      · exact hM.1 <| congrArg Prod.fst hxy
      · exact hN.1 <| congrArg Prod.snd hxy
    · intro y
      rcases hM.2 y.1 with ⟨x, hx⟩
      rcases hN.2 y.2 with ⟨z, hz⟩
      refine ⟨(x, z), ?_⟩
      apply Prod.ext
      · simpa [f, localizedProdMap] using hx
      · simpa [f, localizedProdMap] using hz
  · intro y
    rcases IsLocalizedModule.surj (S := S) (LocalizedModule.mkLinearMap S M) y.1 with ⟨x, hx⟩
    rcases IsLocalizedModule.surj (S := S) (LocalizedModule.mkLinearMap S N) y.2 with ⟨z, hz⟩
    refine ⟨((z.2 • x.1, x.2 • z.1), x.2 * z.2), ?_⟩
    apply Prod.ext
    · have hx' := congrArg (fun t => z.2 • t) hx
      simpa [f, localizedProdMap, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hx'
    · have hz' := congrArg (fun t => x.2 • t) hz
      simpa [f, localizedProdMap, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hz'
  · intro x₁ x₂ h
    have h₁ :
        (LocalizedModule.mkLinearMap S M) x₁.1 =
          (LocalizedModule.mkLinearMap S M) x₂.1 := by
      exact congrArg Prod.fst h
    have h₂ :
        (LocalizedModule.mkLinearMap S N) x₁.2 =
          (LocalizedModule.mkLinearMap S N) x₂.2 := by
      exact congrArg Prod.snd h
    rcases IsLocalizedModule.exists_of_eq (S := S) (f := LocalizedModule.mkLinearMap S M) h₁
      with ⟨c₁, hc₁⟩
    rcases IsLocalizedModule.exists_of_eq (S := S) (f := LocalizedModule.mkLinearMap S N) h₂
      with ⟨c₂, hc₂⟩
    refine ⟨c₁ * c₂, ?_⟩
    apply Prod.ext
    · have hc₁' := congrArg (fun t => c₂ • t) hc₁
      simpa [f, localizedProdMap, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hc₁'
    · have hc₂' := congrArg (fun t => c₁ • t) hc₂
      simpa [f, localizedProdMap, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hc₂'

noncomputable def localizedProdEquiv (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    LocalizedModule S (M × N) ≃ₗ[Localization S]
      (LocalizedModule S M × LocalizedModule S N) := by
  exact (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (M × N))
    (localizedProdMap S M N)).extendScalarsOfIsLocalization S _

@[simp] lemma localizedProdMap_mk' (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M × N) (s : S) :
    IsLocalizedModule.mk' (localizedProdMap S M N) x s =
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x.1 s,
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x.2 s) := by
  apply Prod.ext
  · apply (IsLocalizedModule.smul_inj (f := LocalizedModule.mkLinearMap S M) s _ _).1
    show ((s : R) • (IsLocalizedModule.mk' (localizedProdMap S M N) x s).1) =
      ((s : R) • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x.1 s)
    calc
      ((s : R) • (IsLocalizedModule.mk' (localizedProdMap S M N) x s).1)
          = ((localizedProdMap S M N) x).1 := by
              exact congrArg Prod.fst
                (IsLocalizedModule.mk'_cancel' (f := localizedProdMap S M N) x s)
      _ = (LocalizedModule.mkLinearMap S M) x.1 := rfl
      _ = ((s : R) • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x.1 s) := by
            symm
            exact IsLocalizedModule.mk'_cancel' (f := LocalizedModule.mkLinearMap S M) x.1 s
  · apply (IsLocalizedModule.smul_inj (f := LocalizedModule.mkLinearMap S N) s _ _).1
    show ((s : R) • (IsLocalizedModule.mk' (localizedProdMap S M N) x s).2) =
      ((s : R) • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x.2 s)
    calc
      ((s : R) • (IsLocalizedModule.mk' (localizedProdMap S M N) x s).2)
          = ((localizedProdMap S M N) x).2 := by
              exact congrArg Prod.snd
                (IsLocalizedModule.mk'_cancel' (f := localizedProdMap S M N) x s)
      _ = (LocalizedModule.mkLinearMap S N) x.2 := rfl
      _ = ((s : R) • IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x.2 s) := by
            symm
            exact IsLocalizedModule.mk'_cancel' (f := LocalizedModule.mkLinearMap S N) x.2 s

@[simp] lemma localizedProdEquiv_apply_mk' (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M × N) (s : S) :
    localizedProdEquiv S M N
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M × N)) x s) =
        (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x.1 s,
          IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x.2 s) := by
  simp [localizedProdEquiv, LinearEquiv.extendScalarsOfIsLocalization_apply]

@[simp] lemma localizedProdEquiv_apply_mk (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M × N) :
    localizedProdEquiv S M N (LocalizedModule.mk x 1) =
      (LocalizedModule.mk x.1 1, LocalizedModule.mk x.2 1) := by
  simpa using localizedProdEquiv_apply_mk' (R := R) S M N x (1 : S)

@[simp] lemma localizedProdEquiv_symm_apply_mk' (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M × N) (s : S) :
    (localizedProdEquiv S M N).symm
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x.1 s,
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S N) x.2 s) =
          IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M × N)) x s := by
  apply (localizedProdEquiv S M N).injective
  simp

@[simp] lemma localizedProdEquiv_symm_apply_mk (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M × N) :
    (localizedProdEquiv S M N).symm
      (LocalizedModule.mk x.1 1, LocalizedModule.mk x.2 1) =
        LocalizedModule.mk x 1 := by
  simpa using localizedProdEquiv_symm_apply_mk' (R := R) S M N x (1 : S)

@[simp] lemma localizedProdEquiv_symm_apply_mk'_zero_right (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : M) (s : S) :
    (localizedProdEquiv S M N).symm
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) x s, 0) =
        IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (M × N)) (x, 0) s := by
  simpa using localizedProdEquiv_symm_apply_mk' (R := R) S M N (x, 0) s

@[simp] lemma localizedProdEquiv_symm_apply_zero_mk (S : Submonoid R) (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (y : N) :
    (localizedProdEquiv S M N).symm
      (0, LocalizedModule.mk y 1) =
        LocalizedModule.mk (0, y) 1 := by
  simpa using localizedProdEquiv_symm_apply_mk (R := R) S M N (0, y)

noncomputable def localizedRingEquiv (S : Submonoid R) :
    LocalizedModule S R ≃ₗ[Localization S] Localization S :=
  IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S R)
    (Algebra.linearMap R (Localization S)) (Localization S) (LinearEquiv.refl R R)

noncomputable def localizedPiEquiv (S : Submonoid R) (n : ℕ) :
    LocalizedModule S (Fin n → R) ≃ₗ[Localization S] (Fin n → Localization S) := by
  let b : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let bS := b.ofIsLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin n → R))
  exact bS.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite (Localization S) (Localization S) (Fin n)

@[simp] lemma localizedPiEquiv_apply_mk' (S : Submonoid R) (n : ℕ)
    (v : Fin n → R) (s : S) :
    localizedPiEquiv S n
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s) =
        fun i => IsLocalization.mk' (Localization S) (v i) s := by
  ext i
  let b : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let bS := b.ofIsLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin n → R))
  show (bS.repr (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s)) i = _
  apply (IsLocalizedModule.smul_inj (f := Algebra.linearMap R (Localization S)) s _ _).1
  show ((s : R) • (bS.repr
      (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s)) i) =
    ((s : R) • IsLocalization.mk' (Localization S) (v i) s)
  calc
    (s : R) • (bS.repr
        (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s)) i
        = (bS.repr ((s : R) •
            IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s)) i := by
            simpa using congrArg (fun f => f i)
              (LinearEquiv.map_smul bS.repr ((algebraMap R (Localization S)) s)
                (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S (Fin n → R)) v s)).symm
    _ = (bS.repr ((LocalizedModule.mkLinearMap S (Fin n → R)) v)) i := by
          exact congrArg (fun w => (bS.repr w) i)
            (IsLocalizedModule.mk'_cancel' (f := LocalizedModule.mkLinearMap S (Fin n → R)) v s)
    _ = algebraMap R (Localization S) (v i) := by
          rw [Module.Basis.ofIsLocalizedModule_repr_apply]
          simp [b, Pi.basisFun_repr]
    _ = (s : R) • IsLocalization.mk' (Localization S) (v i) s := by
          symm
          exact IsLocalization.smul_mk'_self (S := Localization S) (m := s) (r := v i)

@[simp] lemma localizedPiEquiv_apply_mk (S : Submonoid R) (n : ℕ) (v : Fin n → R) :
    localizedPiEquiv S n (LocalizedModule.mk v 1) =
      fun i => algebraMap R (Localization S) (v i) := by
  ext i
  let b : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  let bS := b.ofIsLocalizedModule (Localization S) S
    (LocalizedModule.mkLinearMap S (Fin n → R))
  show (bS.repr ((LocalizedModule.mkLinearMap S (Fin n → R)) v)) i = _
  rw [Module.Basis.ofIsLocalizedModule_repr_apply]
  simp [b, Pi.basisFun_repr]

@[simp] lemma localizedPiEquiv_symm_apply_algebraMap (S : Submonoid R) (n : ℕ)
    (v : Fin n → R) :
    (localizedPiEquiv S n).symm (fun i => algebraMap R (Localization S) (v i)) =
      LocalizedModule.mk v 1 := by
  apply (localizedPiEquiv S n).injective
  simp

@[simp] lemma localizedPiEquiv_symm_apply_basis (S : Submonoid R) (n : ℕ) (j : Fin n) :
    (localizedPiEquiv S n).symm (Pi.single j 1) =
      LocalizedModule.mk (Pi.single j 1) 1 := by
  apply (localizedPiEquiv S n).injective
  ext i
  by_cases h : i = j
  · subst h
    simp
  · simp [Pi.single, h]

lemma localizedPiEquiv_apply_map_mk'
    (S : Submonoid R) {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (h : A →ₗ[R] (Fin n → R)) (x : A) (s : S) :
    localizedPiEquiv S n
      (((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S A)
          (LocalizedModule.mkLinearMap S (Fin n → R))) h)
        (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S A) x s)) =
          fun i => IsLocalization.mk' (Localization S) (h x i) s := by
  rw [IsLocalizedModule.map_mk']
  simp

lemma localizedPiEquiv_apply_map_mk
    (S : Submonoid R) {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (h : A →ₗ[R] (Fin n → R)) (x : A) :
    localizedPiEquiv S n
      (((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S A)
          (LocalizedModule.mkLinearMap S (Fin n → R))) h)
        (LocalizedModule.mk x 1)) =
          fun i => algebraMap R (Localization S) (h x i) := by
  have hmk : IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S A) x (1 : S) =
      LocalizedModule.mk x 1 := by simp
  rw [← hmk]
  ext i
  have hi := congrFun (localizedPiEquiv_apply_map_mk' (R := R) S h x (1 : S)) i
  rw [show IsLocalization.mk' (Localization S) (h x i) (1 : S) =
      algebraMap R (Localization S) (h x i) by
        simpa using
          (IsLocalization.smul_mk'_self (S := Localization S) (m := (1 : S)) (r := h x i))] at hi
  exact hi

theorem exists_fin_linearEquiv_of_isStablyFree_of_localized_eq_ring [IsDomain R]
    [Module.Finite R M] (hstable : IsStablyFree R M)
    (P : Ideal R) [P.IsPrime]
    (u : LocalizedModule P.primeCompl M ≃ₗ[Localization.AtPrime P] Localization.AtPrime P) :
    ∃ n, Nonempty ((M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) := by
  rcases hstable with ⟨N, _instNAdd, _instNMod, hNfinite, hNfree, hMNfree⟩
  let n := Module.finrank R N
  let m := Module.finrank R (M × N)
  let eN : N ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.ofFinrankEq (R := R) (M := N) (M' := Fin n → R) (by simp [n])
  let eMN : (M × N) ≃ₗ[R] (Fin m → R) :=
    LinearEquiv.ofFinrankEq (R := R) (M := M × N) (M' := Fin m → R) (by simp [m])
  let e : (M × (Fin n → R)) ≃ₗ[R] (Fin m → R) :=
    ((LinearEquiv.refl R M).prodCongr eN.symm) ≪≫ₗ eMN
  let Rp := Localization.AtPrime P
  have hfinN : Module.finrank Rp (LocalizedModule P.primeCompl N) = n := by
    let eNLoc := IsLocalizedModule.mapEquiv P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl N)
      (LocalizedModule.mkLinearMap P.primeCompl (Fin n → R))
      Rp eN
    calc
      Module.finrank Rp (LocalizedModule P.primeCompl N)
          = Module.finrank Rp (LocalizedModule P.primeCompl (Fin n → R)) := eNLoc.finrank_eq
      _ = Module.finrank Rp (Fin n → Rp) := (localizedPiEquiv P.primeCompl n).finrank_eq
      _ = n := by simp [Rp]
  have hfinMN : Module.finrank Rp (LocalizedModule P.primeCompl (M × (Fin n → R))) = m := by
    let eLoc := IsLocalizedModule.mapEquiv P.primeCompl
      (LocalizedModule.mkLinearMap P.primeCompl (M × (Fin n → R)))
      (LocalizedModule.mkLinearMap P.primeCompl (Fin m → R))
      Rp e
    calc
      Module.finrank Rp (LocalizedModule P.primeCompl (M × (Fin n → R)))
          = Module.finrank Rp (LocalizedModule P.primeCompl (Fin m → R)) := eLoc.finrank_eq
      _ = Module.finrank Rp (Fin m → Rp) := (localizedPiEquiv P.primeCompl m).finrank_eq
      _ = m := by simp [Rp]
  have hm : m = n + 1 := by
    letI : Module.Free Rp Rp := Module.Free.self Rp
    letI : Module.Free Rp (Fin n → Rp) := Module.Free.of_basis (Pi.basisFun Rp (Fin n))
    letI : Module.Free Rp (LocalizedModule P.primeCompl M) := Module.Free.of_equiv u.symm
    letI : Module.Free Rp (LocalizedModule P.primeCompl (Fin n → R)) :=
      Module.Free.of_equiv (localizedPiEquiv P.primeCompl n).symm
    have hself : Module.finrank Rp Rp = 1 := by simp
    have hpi : Module.finrank Rp (Fin n → Rp) = n := by simp
    calc
      m = Module.finrank Rp (LocalizedModule P.primeCompl (M × (Fin n → R))) := hfinMN.symm
      _ = Module.finrank Rp (LocalizedModule P.primeCompl M × LocalizedModule P.primeCompl (Fin n → R)) := by
        exact (localizedProdEquiv P.primeCompl M (Fin n → R)).finrank_eq
      _ = Module.finrank Rp (LocalizedModule P.primeCompl M) +
            Module.finrank Rp (LocalizedModule P.primeCompl (Fin n → R)) := by
        rw [Module.finrank_prod]
      _ = Module.finrank Rp Rp + Module.finrank Rp (Fin n → Rp) := by
        rw [u.finrank_eq, (localizedPiEquiv P.primeCompl n).finrank_eq]
      _ = 1 + n := by
        rw [hself, hpi]
      _ = n + 1 := by omega
  refine ⟨n, ?_⟩
  refine ⟨e ≪≫ₗ ?_⟩
  exact LinearEquiv.ofFinrankEq (R := R) (M := Fin m → R) (M' := Fin (n + 1) → R) (by simp [hm])

theorem localized_stableMap_eq_restrict (P : Ideal R) [P.IsPrime] {n : ℕ}
    (e : (M × (Fin n → R)) ≃ₗ[R] (Fin (n + 1) → R)) :
    let eRawLoc :
        LocalizedModule P.primeCompl (M × (Fin n → R)) ≃ₗ[Localization.AtPrime P]
          LocalizedModule P.primeCompl (Fin (n + 1) → R) :=
      IsLocalizedModule.mapEquiv P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (M × (Fin n → R)))
        (LocalizedModule.mkLinearMap P.primeCompl (Fin (n + 1) → R))
        (Localization.AtPrime P) e
    let eLoc :
        (LocalizedModule P.primeCompl M × (Fin n → Localization.AtPrime P)) ≃ₗ[Localization.AtPrime P]
          (Fin (n + 1) → Localization.AtPrime P) :=
      ((LinearEquiv.refl _ _).prodCongr (localizedPiEquiv P.primeCompl n).symm) ≪≫ₗ
        (localizedProdEquiv P.primeCompl M (Fin n → R)).symm ≪≫ₗ eRawLoc ≪≫ₗ
        localizedPiEquiv P.primeCompl (n + 1)
    IsLocalizedModule.map P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (Algebra.linearMap R (Localization.AtPrime P)) (stableMap e) =
      (stableMap eLoc).restrictScalars R := by
  ext x
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (S := P.primeCompl)
    (LocalizedModule.mkLinearMap P.primeCompl M) x
  apply (IsLocalizedModule.smul_inj (f := Algebra.linearMap R (Localization.AtPrime P)) s _ _).1
  simp [stableMap, stableMatrix, localizedPiEquiv_apply_map_mk]
  let Rp := Localization.AtPrime P
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) Rp := Matrix.of fun i j =>
    if h : j = 0 then
      IsLocalization.mk' Rp (e (m, 0) i) s
    else
      algebraMap R Rp (e (0, Pi.single (j.pred (by simpa using h)) 1) i)
  let c : Fin (n + 1) → Rp := fun i => IsLocalization.mk' Rp (e (m, 0) i) s
  have hA :
      A = ((RingHom.mapMatrix (algebraMap R Rp)) (stableBaseMatrix e)).updateCol 0 c := by
    ext i j
    by_cases h : j = 0
    · subst h
      simp [A, c, stableBaseMatrix, stableMatrix]
    · simp [A, c, stableBaseMatrix, stableMatrix, h]
  have hsc :
      (algebraMap R Rp (s : R)) • c = fun i => algebraMap R Rp (e (m, 0) i) := by
    ext i
    simp [c, smul_eq_mul]
  have hmap :
      (RingHom.mapMatrix (algebraMap R Rp)) (stableMatrix e m) =
        ((RingHom.mapMatrix (algebraMap R Rp)) (stableBaseMatrix e)).updateCol 0
          ((algebraMap R Rp (s : R)) • c) := by
    ext i j
    by_cases h : j = 0
    · subst h
      simp [stableBaseMatrix, stableMatrix, hsc]
    · simp [stableBaseMatrix, stableMatrix, h]
  have hdet :
      (algebraMap R Rp) (stableMatrix e m).det = (algebraMap R Rp (s : R)) * A.det := by
    calc
      (algebraMap R Rp) (stableMatrix e m).det
          = ((RingHom.mapMatrix (algebraMap R Rp)) (stableMatrix e m)).det := by
              rw [RingHom.map_det]
      _ = (((RingHom.mapMatrix (algebraMap R Rp)) (stableBaseMatrix e)).updateCol 0
            ((algebraMap R Rp (s : R)) • c)).det := by
              rw [hmap]
      _ = (algebraMap R Rp (s : R)) *
            (((RingHom.mapMatrix (algebraMap R Rp)) (stableBaseMatrix e)).updateCol 0 c).det := by
              rw [Matrix.det_updateCol_smul]
      _ = (algebraMap R Rp (s : R)) * A.det := by rw [hA]
  calc _ = (algebraMap R Rp (s : R)) * A.det := by simpa [A, Rp, stableMatrix] using hdet
    _ = s • A.det := by simpa using (Algebra.smul_def (R := R) (A := Rp) (s : R) A.det).symm

theorem free_of_isStablyFree_of_localized_eq_ring [IsDomain R] [Module.Finite R M]
    (hstable : IsStablyFree R M) (P0 : Ideal R) [P0.IsMaximal]
    (u0 : LocalizedModule P0.primeCompl M ≃ₗ[Localization.AtPrime P0] Localization.AtPrime P0)
    (hloc : ∀ (P : Ideal R) [P.IsMaximal],
      Nonempty (LocalizedModule P.primeCompl M ≃ₗ[Localization.AtPrime P] Localization.AtPrime P)) :
    Module.Free R M := by
  have hprime0 : P0.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  obtain ⟨n, ⟨e⟩⟩ := exists_fin_linearEquiv_of_isStablyFree_of_localized_eq_ring
    (R := R) (M := M) hstable P0 u0
  let F : M →ₗ[R] R := stableMap e
  have hbij : Function.Bijective F := by
    refine bijective_of_isLocalized_maximal
      (fun P _ => LocalizedModule P.primeCompl M)
      (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap R (Localization.AtPrime P)) F ?_
    intro P _
    obtain ⟨uP⟩ := hloc P
    let eRawLoc :
        LocalizedModule P.primeCompl (M × (Fin n → R)) ≃ₗ[Localization.AtPrime P]
          LocalizedModule P.primeCompl (Fin (n + 1) → R) :=
      IsLocalizedModule.mapEquiv P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl (M × (Fin n → R)))
        (LocalizedModule.mkLinearMap P.primeCompl (Fin (n + 1) → R))
        (Localization.AtPrime P) e
    let eLoc :
        (LocalizedModule P.primeCompl M × (Fin n → Localization.AtPrime P))
          ≃ₗ[Localization.AtPrime P] (Fin (n + 1) → Localization.AtPrime P) :=
      ((LinearEquiv.refl _ _).prodCongr (localizedPiEquiv P.primeCompl n).symm) ≪≫ₗ
        (localizedProdEquiv P.primeCompl M (Fin n → R)).symm ≪≫ₗ eRawLoc ≪≫ₗ
          localizedPiEquiv P.primeCompl (n + 1)
    have hcompat :
        IsLocalizedModule.map P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
          (Algebra.linearMap R (Localization.AtPrime P)) F =
            (stableMap eLoc).restrictScalars R := by
      simpa [F, eRawLoc, eLoc] using localized_stableMap_eq_restrict (R := R) (M := M) P e
    simpa [F, hcompat] using stableMap_bijective_of_linearEquiv eLoc uP
  let eF : M ≃ₗ[R] R := LinearEquiv.ofBijective F hbij
  exact Module.Free.of_equiv (LinearEquiv.ofBijective F hbij).symm
