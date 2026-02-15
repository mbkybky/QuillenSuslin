import Mathlib

open PowerSeries MvPowerSeries

open scoped BigOperators

/-! ### Tate algebra (restricted power series)

This file ultimately aims to formalize a coefficient estimate for iterates of a nonarchimedean
analytic self-map of the unit bidisc, as in `new/Temp.md`.

As mathlib does not currently provide a bundled `k{X,Y}` Tate algebra API, we model the *bivariate*
Tate algebra as the subtype of `MvPowerSeries (Fin 2) k` whose coefficients tend to `0` along the
cofinite filter on multi-indices.
-/

section TateAlgebra

/-- Restricted multivariate power series: coefficients tend to `0` along `Filter.cofinite`. -/
def IsTate (k : Type*) [NormedRing k] (σ : Type*) (F : MvPowerSeries σ k) : Prop :=
  Filter.Tendsto (fun e : σ →₀ ℕ => MvPowerSeries.coeff e F) Filter.cofinite (nhds 0)

/-- The Tate algebra in variables `σ` over `k`, modelled as restricted multivariate power series. -/
abbrev TateAlgebra (k : Type*) [NormedRing k] (σ : Type*) :=
  {F : MvPowerSeries σ k // IsTate k σ F}

instance (k : Type*) [NormedRing k] (σ : Type*) :
    Coe (TateAlgebra k σ) (MvPowerSeries σ k) :=
  ⟨Subtype.val⟩

/-- The bivariate Tate algebra `k{X,Y}`. -/
abbrev TateAlgebra2 (k : Type*) [NormedRing k] :=
  TateAlgebra k (Fin 2)

end TateAlgebra

/-- A radius-`1` Gauss-type bound: all coefficients have norm bounded by `c`. -/
def GaussBound (k : Type*) [NormedRing k] {σ : Type*} (c : ℝ) (F : MvPowerSeries σ k) : Prop :=
  ∀ e : σ →₀ ℕ, ‖(MvPowerSeries.coeff e) F‖ ≤ c

lemma GaussBound.mono {k : Type*} [NormedRing k] {σ : Type*} {c₁ c₂ : ℝ}
    {F : MvPowerSeries σ k} (hc : c₁ ≤ c₂) (hF : GaussBound k c₁ F) : GaussBound k c₂ F := by
  intro e
  exact (hF e).trans hc

lemma gaussBound_one_one (k : Type*) [NormedField k] [IsUltrametricDist k] {σ : Type*} :
    GaussBound k (1 : ℝ) (1 : MvPowerSeries σ k) := by
  classical
  intro e
  by_cases he : e = 0
  · subst he
    simp
  · simp [MvPowerSeries.coeff_one, he]

lemma gaussBound_one_mul {k : Type*} [NormedField k] [IsUltrametricDist k] {σ : Type*}
    {F G : MvPowerSeries σ k}
    (hF : GaussBound k (1 : ℝ) F) (hG : GaussBound k (1 : ℝ) G) :
    GaussBound k (1 : ℝ) (F * G) := by
  classical
  intro e
  -- Coefficient formula for multiplication and ultrametric triangle inequality.
  rw [MvPowerSeries.coeff_mul (φ := F) (ψ := G) (n := e)]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
  intro p hp
  have hF' : ‖MvPowerSeries.coeff p.1 F‖ ≤ (1 : ℝ) := hF p.1
  have hG' : ‖MvPowerSeries.coeff p.2 G‖ ≤ (1 : ℝ) := hG p.2
  calc
    ‖MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 G‖
        ≤ ‖MvPowerSeries.coeff p.1 F‖ * ‖MvPowerSeries.coeff p.2 G‖ := norm_mul_le _ _
    _ ≤ (1 : ℝ) := by
      have : ‖MvPowerSeries.coeff p.1 F‖ * ‖MvPowerSeries.coeff p.2 G‖ ≤ (1 : ℝ) * 1 :=
        mul_le_mul hF' hG' (norm_nonneg _) (by norm_num)
      simpa using this

lemma gaussBound_one_pow {k : Type*} [NormedField k] [IsUltrametricDist k] {σ : Type*}
    {F : MvPowerSeries σ k} (hF : GaussBound k (1 : ℝ) F) (n : ℕ) :
    GaussBound k (1 : ℝ) (F ^ n) := by
  classical
  induction n with
  | zero =>
      simpa using gaussBound_one_one (k := k)
  | succ n ih =>
      simpa [pow_succ] using gaussBound_one_mul (F := F ^ n) (G := F) ih hF

lemma gaussBound_one_finset_prod {k : Type*} [NormedField k] [IsUltrametricDist k]
    {σ : Type*} {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ k)
    (hf : ∀ i ∈ s, GaussBound k (1 : ℝ) (f i)) :
    GaussBound k (1 : ℝ) (∏ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using gaussBound_one_one (k := k)
  · intro a s ha ih hs
    have hfa : GaussBound k (1 : ℝ) (f a) := hs a (by simp [ha])
    have hfs : ∀ i ∈ s, GaussBound k (1 : ℝ) (f i) := fun i hi => hs i (by simp [hi])
    have hprod : GaussBound k (1 : ℝ) (∏ i ∈ s, f i) := ih hfs
    simpa [Finset.prod_insert, ha] using
      gaussBound_one_mul (F := f a) (G := ∏ i ∈ s, f i) hfa hprod

lemma gaussBound_one_finsupp_prod {k : Type*} [NormedField k] [IsUltrametricDist k]
    {σ : Type*} {a : Fin 2 → MvPowerSeries σ k} (ha : ∀ i, GaussBound k (1 : ℝ) (a i))
    (d : Fin 2 →₀ ℕ) :
    GaussBound k (1 : ℝ) (d.prod fun i n => (a i) ^ n) := by
  classical
  -- Expand `Finsupp.prod` as a finite product over the support.
  simpa [Finsupp.prod] using
    (gaussBound_one_finset_prod (k := k) (s := d.support) (f := fun i => (a i) ^ (d i))
      (fun i hi => gaussBound_one_pow (k := k) (F := a i) (ha i) (d i)))

lemma gaussBound_subst {k : Type*} [NormedField k] [IsUltrametricDist k]
    {τ : Type*} {c : ℝ} (hc0 : 0 ≤ c)
    {F : MvPowerSeries (Fin 2) k} (hF : GaussBound k c F)
    {a : Fin 2 → MvPowerSeries τ k} (ha : MvPowerSeries.HasSubst a)
    (ha1 : ∀ i, GaussBound k (1 : ℝ) (a i)) :
    GaussBound k c (MvPowerSeries.subst a F) := by
  classical
  intro e
  -- Expand the coefficient as a finite sum (Bourbaki substitution formula).
  rw [MvPowerSeries.coeff_subst (a := a) ha (f := F) (e := e)]
  -- Turn the `finsum` into a finite sum, then use the ultrametric triangle inequality.
  set g : (Fin 2 →₀ ℕ) → k := fun d =>
    MvPowerSeries.coeff d F • MvPowerSeries.coeff e (d.prod fun s n => (a s) ^ n)
  have hfinite : (Function.support g).Finite :=
    MvPowerSeries.coeff_subst_finite (a := a) ha (f := F) (e := e)
  -- Rewrite `finsum` as a `Finset.sum` over the finite support.
  rw [finsum_eq_sum g hfinite]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc0 ?_
  intro d hd
  have hcoeffF : ‖MvPowerSeries.coeff d F‖ ≤ c := hF d
  have hprod1 :
      GaussBound k (1 : ℝ) (d.prod fun s n => (a s) ^ n) := by
    -- Each factor has Gauss bound `1`, hence so does any finite product of powers.
    have ha_pow : ∀ s, GaussBound k (1 : ℝ) ((a s) ^ (d s)) := fun s =>
      by simpa using gaussBound_one_pow (k := k) (F := a s) (ha1 s) (d s)
    -- Unfold `Finsupp.prod` and apply the finite-product lemma.
    simpa [Finsupp.prod] using
      (gaussBound_one_finset_prod (k := k) (s := d.support)
        (f := fun s => (a s) ^ (d s)) (fun s hs => ha_pow s))
  have hcoeffProd : ‖MvPowerSeries.coeff e (d.prod fun s n => (a s) ^ n)‖ ≤ (1 : ℝ) :=
    hprod1 e
  calc
    ‖g d‖
        = ‖MvPowerSeries.coeff d F * MvPowerSeries.coeff e (d.prod fun s n => (a s) ^ n)‖ := by
          simp [g, smul_eq_mul]
    _ ≤ ‖MvPowerSeries.coeff d F‖ * ‖MvPowerSeries.coeff e (d.prod fun s n => (a s) ^ n)‖ :=
        norm_mul_le _ _
    _ ≤ c := by
        have : ‖MvPowerSeries.coeff d F‖ * ‖MvPowerSeries.coeff e (d.prod fun s n => (a s) ^ n)‖ ≤
            c * (1 : ℝ) :=
          mul_le_mul hcoeffF hcoeffProd (norm_nonneg _) hc0
        simpa using this

/-- The substitution map `(x,y) ↦ (P,Q)` used for composition of bivariate power series. -/
noncomputable def substMap {k : Type*} [CommRing k]
    (P Q : MvPowerSeries (Fin 2) k) : Fin 2 → MvPowerSeries (Fin 2) k
  | 0 => P
  | 1 => Q

/-- Iterates of the bivariate map `f(x,y) = (P(x,y), Q(x,y))` on formal power series:
`iterPQ P Q n = (Pₙ, Qₙ)` with `(P₀,Q₀) = (x,y)` and
`(P_{n+1},Q_{n+1}) = (P(Pₙ,Qₙ), Q(Pₙ,Qₙ))`. -/
noncomputable def iterPQ {k : Type*} [CommRing k]
    (P Q : MvPowerSeries (Fin 2) k) : ℕ → (MvPowerSeries (Fin 2) k × MvPowerSeries (Fin 2) k)
  | 0 => (MvPowerSeries.X 0, MvPowerSeries.X 1)
  | n + 1 => (MvPowerSeries.subst (substMap (iterPQ P Q n).1 (iterPQ P Q n).2) P,
      MvPowerSeries.subst (substMap (iterPQ P Q n).1 (iterPQ P Q n).2) Q)

/-- Specialization `(x,y) ↦ (X,0)` turning a bivariate series into a univariate series. -/
noncomputable def xOnlySubst (k : Type*) [CommRing k] : Fin 2 → k⟦X⟧
  | 0 => X
  | 1 => 0

/-- The univariate series `Q_d(x,0)` attached to the `d`-th iterate. -/
noncomputable def qIter (k : Type*) [CommRing k]
    (P Q : MvPowerSeries (Fin 2) k) (d : ℕ) : k⟦X⟧ :=
  MvPowerSeries.subst (xOnlySubst k) (iterPQ P Q d).2

lemma xOnlySubst_hasSubst (k : Type*) [CommRing k] : MvPowerSeries.HasSubst (xOnlySubst k) := by
  classical
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Fin 2) (τ := Unit) (a := xOnlySubst k) ?_
  intro s
  fin_cases s <;> simp [xOnlySubst, PowerSeries.X, MvPowerSeries.constantCoeff_X]

lemma qIter_zero (k : Type*) [CommRing k] (P Q : MvPowerSeries (Fin 2) k) : qIter k P Q 0 = 0 := by
  simp [qIter, iterPQ, MvPowerSeries.subst_X (xOnlySubst_hasSubst k), xOnlySubst]

/-! ### Normal form lemmas (to be proved)

The proof strategy suggested by `new/Temp.md` goes through an analytic Poincaré–Dulac normal form.
We record below the *statements* of the key normal-form inputs needed to reduce coefficient bounds
for the iterates to explicit estimates on a triangular map.
-/

section NormalForm

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

/-- A coordinate map `(x,y) ↦ (F₀(x,y), F₁(x,y))` as a pair of bivariate power series. -/
abbrev CoordMap2 (k : Type*) [CommRing k] := Fin 2 → MvPowerSeries (Fin 2) k

/-- Composition of coordinate maps by substitution. -/
noncomputable def CoordMap2.comp {k : Type*} [CommRing k] (F G : CoordMap2 k) : CoordMap2 k :=
  fun i => MvPowerSeries.subst (substMap (G 0) (G 1)) (F i)

/-- Identity coordinate map. -/
noncomputable def CoordMap2.id {k : Type*} [CommRing k] : CoordMap2 k :=
  fun i => MvPowerSeries.X i

/-- An analytic Poincaré–Dulac normal form for a contracting map of the unit bidisc.

This is the main "black box" used in Step 3 of `new/Temp.md`: after an analytic change of
coordinates, the map becomes triangular with at most one nonlinear resonant term in the second
coordinate. -/
theorem exists_poincare_dulac_normal_form
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)
    (P Q : TateAlgebra2 k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcP : GaussBound k c (P : MvPowerSeries (Fin 2) k))
    (hcQ : GaussBound k c (Q : MvPowerSeries (Fin 2) k))
    (hP0 : MvPowerSeries.constantCoeff (P : MvPowerSeries (Fin 2) k) = 0)
    (hQ0 : MvPowerSeries.constantCoeff (Q : MvPowerSeries (Fin 2) k) = 0) :
    ∃ (H K : Fin 2 → TateAlgebra2 k) (lam mu tau b : k) (m : ℕ),
      (∀ i, MvPowerSeries.constantCoeff (H i : MvPowerSeries (Fin 2) k) = 0) ∧
      (∀ i, MvPowerSeries.constantCoeff (K i : MvPowerSeries (Fin 2) k) = 0) ∧
      -- `K` is a two-sided inverse of `H` under composition.
      CoordMap2.comp (k := k) (fun i => (H i : MvPowerSeries (Fin 2) k))
          (fun i => (K i : MvPowerSeries (Fin 2) k)) = CoordMap2.id (k := k) ∧
      CoordMap2.comp (k := k) (fun i => (K i : MvPowerSeries (Fin 2) k))
          (fun i => (H i : MvPowerSeries (Fin 2) k)) = CoordMap2.id (k := k) ∧
      -- Conjugating `f = (P,Q)` by `H` yields the triangular normal form.
      let P' : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K 0 : MvPowerSeries (Fin 2) k) (K 1 : MvPowerSeries (Fin 2) k))
            (P : MvPowerSeries (Fin 2) k)
      let Q' : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K 0 : MvPowerSeries (Fin 2) k) (K 1 : MvPowerSeries (Fin 2) k))
            (Q : MvPowerSeries (Fin 2) k)
      let g₁ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P' Q') (H 0 : MvPowerSeries (Fin 2) k)
      let g₂ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P' Q') (H 1 : MvPowerSeries (Fin 2) k)
      g₁ = MvPowerSeries.C lam * MvPowerSeries.X 0 + MvPowerSeries.C tau * MvPowerSeries.X 1 ∧
      g₂ = MvPowerSeries.C mu * MvPowerSeries.X 1 + MvPowerSeries.monomial (Finsupp.single 0 m) b := by
  sorry

end NormalForm

/-- Formal statement of the coefficient estimate for `Q_d(x,0)` (cf. `new/Temp.md`). -/
theorem iter_coeff_bound {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)
    (P Q : TateAlgebra2 k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcP : GaussBound k c (P : MvPowerSeries (Fin 2) k))
    (hcq : GaussBound k c (Q : MvPowerSeries (Fin 2) k))
    (hP0 : MvPowerSeries.constantCoeff (P : MvPowerSeries (Fin 2) k) = 0)
    (hQ0 : MvPowerSeries.constantCoeff (Q : MvPowerSeries (Fin 2) k) = 0)
    (hq : ∀ d : ℕ, d > 0 → qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d ≠ 0) :
    ∃ (M r : ℝ), 0 < M ∧ 0 < r ∧ r < 1 ∧ ∀ (d m : ℕ), d > 0 → m > 0 →
      r ^ m *
          ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat + m)
              (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ ≤
        M *
          ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat)
              (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ := by
  sorry
