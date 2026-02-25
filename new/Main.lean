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

/-! For convenience we also record the first coordinate specialized to `(x,0)`. -/
noncomputable def pIter (k : Type*) [CommRing k]
    (P Q : MvPowerSeries (Fin 2) k) (d : ℕ) : k⟦X⟧ :=
  MvPowerSeries.subst (xOnlySubst k) (iterPQ P Q d).1

/-- A `Fin 2`-indexed pair of univariate power series, used as a substitution map. -/
noncomputable def substMap1 {k : Type*} [CommRing k] (p q : k⟦X⟧) : Fin 2 → k⟦X⟧
  | 0 => p
  | 1 => q

lemma xOnlySubst_hasSubst (k : Type*) [CommRing k] : MvPowerSeries.HasSubst (xOnlySubst k) := by
  classical
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Fin 2) (τ := Unit) (a := xOnlySubst k) ?_
  intro s
  fin_cases s <;> simp [xOnlySubst, PowerSeries.X, MvPowerSeries.constantCoeff_X]

lemma qIter_zero (k : Type*) [CommRing k] (P Q : MvPowerSeries (Fin 2) k) : qIter k P Q 0 = 0 := by
  simp [qIter, iterPQ, MvPowerSeries.subst_X (xOnlySubst_hasSubst k), xOnlySubst]

/-! ### Weighted Gauss norms (basic definitions)

To express analyticity on smaller polydiscs as in `new/Temp.md`, we use weighted Gauss bounds at a
radius `ρ`.
-/

section WeightedGaussBounds

variable {k : Type*} [NormedRing k]

/-- Weighted Gauss bound for a univariate power series at radius `ρ`. -/
def WeightedGaussBound1 (ρ C : ℝ) (f : k⟦X⟧) : Prop :=
  ∀ n : ℕ, ‖coeff n f‖ * ρ ^ n ≤ C

/-- Weighted Gauss bound for a bivariate power series with weight `i+j` at radius `ρ`. -/
def WeightedGaussBound2 (ρ C : ℝ) (F : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, ‖MvPowerSeries.coeff e F‖ * ρ ^ (e 0 + e 1) ≤ C

end WeightedGaussBounds

/-! ### Normal form lemmas (to be proved)

The proof strategy suggested by `new/Temp.md` goes through an analytic Poincaré–Dulac normal form.
We record below the *statements* of the key normal-form inputs needed to reduce coefficient bounds
for the iterates to explicit estimates on a triangular map.
-/

section NormalForm

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

/-- A coordinate map `(x,y) ↦ (F₀(x,y), F₁(x,y))` as a pair of bivariate power series. -/
abbrev CoordMap2 (k : Type*) [CommRing k] := Fin 2 → MvPowerSeries (Fin 2) k

/-- A bivariate coordinate map is tangent to the identity at the origin. -/
def TangentToId2 {k : Type*} [CommRing k] (H : CoordMap2 k) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (H i) = 0) ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (H 0) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (H 0) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (H 1) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (H 1) = 1

/-- A bivariate coordinate map is (formally) linear: it has no terms of total degree `≥ 2`. -/
def IsLinearCoordMap2 {k : Type*} [CommRing k] (L : CoordMap2 k) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (L i) = 0) ∧
    ∀ i (e : Fin 2 →₀ ℕ), 2 ≤ e 0 + e 1 → MvPowerSeries.coeff e (L i) = 0

/-- Composition of coordinate maps by substitution. -/
noncomputable def CoordMap2.comp {k : Type*} [CommRing k] (F G : CoordMap2 k) : CoordMap2 k :=
  fun i => MvPowerSeries.subst (substMap (G 0) (G 1)) (F i)

/-- Identity coordinate map. -/
noncomputable def CoordMap2.id {k : Type*} [CommRing k] : CoordMap2 k :=
  fun i => MvPowerSeries.X i

/-- An analytic Poincaré–Dulac normal form for a contracting map of the unit bidisc.

This is the main black box used in Step 3 of `new/Temp.md`: after a (local) change of coordinates,
the map is in Poincare-Dulac normal form, i.e. beyond the linear part only resonant monomials remain.
-/
theorem exists_poincare_dulac_normal_form
    [IsAlgClosed k]
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)
    (P Q : TateAlgebra2 k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcP : GaussBound k c (P : MvPowerSeries (Fin 2) k))
    (hcQ : GaussBound k c (Q : MvPowerSeries (Fin 2) k))
    (hP0 : MvPowerSeries.constantCoeff (P : MvPowerSeries (Fin 2) k) = 0)
    (hQ0 : MvPowerSeries.constantCoeff (Q : MvPowerSeries (Fin 2) k) = 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧
      ∃ (L Linv H K : CoordMap2 k) (lam mu tau : k),
       IsLinearCoordMap2 (k := k) L ∧
       IsLinearCoordMap2 (k := k) Linv ∧
       (∀ i, WeightedGaussBound2 (k := k) ρ₀ ρ₀ (H i)) ∧
       (∀ i, WeightedGaussBound2 (k := k) ρ₀ ρ₀ (K i)) ∧
       (∀ i, MvPowerSeries.constantCoeff (H i) = 0) ∧
       (∀ i, MvPowerSeries.constantCoeff (K i) = 0) ∧
       -- `Linv` is a two-sided inverse of `L` under composition (linear change of coordinates).
       CoordMap2.comp (k := k) L Linv = CoordMap2.id (k := k) ∧
       CoordMap2.comp (k := k) Linv L = CoordMap2.id (k := k) ∧
       -- `K` is a two-sided inverse of `H` under composition.
       CoordMap2.comp (k := k) H K = CoordMap2.id (k := k) ∧
       CoordMap2.comp (k := k) K H = CoordMap2.id (k := k) ∧
       -- Tangency data used in Temp.md: `H(0)=0`, `DH(0)=Id`, hence `K(0)=0`, `DK(0)=Id`.
       TangentToId2 H ∧ TangentToId2 K ∧
      -- Conjugating `f = (P,Q)` by the composite change of coordinates `(H ∘ L)` yields an
      -- attracting Poincaré–Dulac normal form. Here `L` is the initial linear change putting the
      -- linear part in Jordan form, and `H` is tangent-to-identity.
      let K₀ : CoordMap2 k := CoordMap2.comp (k := k) Linv K
      let P₀ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K₀ 0) (K₀ 1))
            (P : MvPowerSeries (Fin 2) k)
      let Q₀ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K₀ 0) (K₀ 1))
            (Q : MvPowerSeries (Fin 2) k)
      let P₁ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P₀ Q₀) (L 0)
      let Q₁ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P₀ Q₀) (L 1)
      let g₁ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P₁ Q₁) (H 0)
      let g₂ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P₁ Q₁) (H 1)
      MvPowerSeries.constantCoeff g₁ = 0 ∧
        MvPowerSeries.constantCoeff g₂ = 0 ∧
          -- Linear part put in upper-triangular Jordan form by an initial linear change of coordinates
          -- (Temp.md Thm 3.2): we record it directly as a property of the normal form.
          MvPowerSeries.coeff (Finsupp.single 0 1) g₁ = lam ∧
            MvPowerSeries.coeff (Finsupp.single 1 1) g₁ = tau ∧
              MvPowerSeries.coeff (Finsupp.single 0 1) g₂ = 0 ∧
                MvPowerSeries.coeff (Finsupp.single 1 1) g₂ = mu ∧
                  ‖lam‖ < 1 ∧ ‖mu‖ < 1 ∧ ‖mu‖ ≤ ‖lam‖ ∧ (tau = 0 ∨ tau = 1) ∧
                    (lam ≠ mu → tau = 0) ∧
                    (∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 →
                      MvPowerSeries.coeff e g₁ ≠ 0 → lam ^ (e 0) * mu ^ (e 1) = lam) ∧
                      (∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 →
                        MvPowerSeries.coeff e g₂ ≠ 0 → lam ^ (e 0) * mu ^ (e 1) = mu) ∧
                        -- Temp.md Thm 3.2(1): if `lam ≠ 0`, then `g₁` is purely linear.
                        (lam ≠ 0 → ∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 → MvPowerSeries.coeff e g₁ = 0) ∧
                          -- Temp.md Thm 3.2(2): if `mu ≠ 0`, then `g₂ = mu*Y + B(X)` with `B = 0` or `b*X^m`.
                          (mu ≠ 0 →
                            ∃ (b : k) (m : ℕ),
                              2 ≤ m ∧ (b = 0 ∨ lam ^ m = mu) ∧
                                g₂ =
                                  MvPowerSeries.C mu * MvPowerSeries.X 1 +
                                    MvPowerSeries.C b * (MvPowerSeries.X 0) ^ m) ∧
                          -- Temp.md Thm 3.2(3): if `mu = 0` and `lam ≠ 0`, then every monomial of `g₂` is divisible by `Y`.
                          ((mu = 0 ∧ lam ≠ 0) →
                            ∃ R : MvPowerSeries (Fin 2) k,
                              MvPowerSeries.constantCoeff R = 0 ∧ g₂ = MvPowerSeries.X 1 * R) := by
  sorry

end NormalForm

/-! ### Ultrametric lemmas about integer casts

The hypothesis `hnat : ∀ n ≠ 0, ‖(n : k)‖ = 1` is a convenient formal substitute for the usual
assumption `char(𝑘̃) = 0`: it implies that distinct integers are at distance `1`, hence an
expression of the form `u + (d : k)` can have norm `< 1` for at most one integer `d`.
-/

section NatCastNorm

variable {k : Type*} [NormedField k] [IsUltrametricDist k]

lemma norm_intCast_eq_one_of_ne_zero
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1) :
    ∀ z : ℤ, z ≠ 0 → ‖(z : k)‖ = 1 := by
  intro z hz
  cases z with
  | ofNat n =>
      have hn : n ≠ 0 := by
        intro hn0
        apply hz
        simpa [hn0]
      simpa using hnat n hn
  | negSucc n =>
      -- `z = -(n+1)` and `‖-x‖ = ‖x‖`.
      -- Avoid `simp` rewriting `↑(n+1)` as `↑n + 1`.
      have hn1 : ‖((n + 1 : ℕ) : k)‖ = 1 := hnat (n + 1) (Nat.succ_ne_zero n)
      have hcast : ((Int.negSucc n : ℤ) : k) = -((n + 1 : ℕ) : k) := by
        simpa [Int.cast_negSucc]
      calc
        ‖((Int.negSucc n : ℤ) : k)‖ = ‖-((n + 1 : ℕ) : k)‖ := by simpa [hcast]
        _ = ‖((n + 1 : ℕ) : k)‖ := by simpa using (norm_neg ((n + 1 : ℕ) : k))
        _ = 1 := hn1

lemma norm_sub_natCast_eq_one_of_ne
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1) {a b : ℕ} (hab : a ≠ b) :
    ‖(a : k) - (b : k)‖ = 1 := by
  have hz : ((a : ℤ) - (b : ℤ)) ≠ 0 := by
    intro hz
    have hab' : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp hz
    exact hab (by exact_mod_cast hab')
  -- Cast the integer difference back to `k`.
  have : ((a : ℤ) - (b : ℤ) : k) = (a : k) - (b : k) := by
    -- `simp` turns `Int.cast_sub` into the desired equality.
    simpa using
      (Int.cast_sub (a : ℤ) (b : ℤ) :
        ((a : ℤ) - (b : ℤ) : k) = ((a : ℤ) : k) - ((b : ℤ) : k))
  -- Now use the integer-cast lemma.
  simpa [this] using norm_intCast_eq_one_of_ne_zero (k := k) hnat ((a : ℤ) - (b : ℤ)) hz

lemma natCast_add_norm_lt_one_unique
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1) (u : k) {a b : ℕ}
    (ha : ‖u + (a : k)‖ < 1) (hb : ‖u + (b : k)‖ < 1) : a = b := by
  by_contra hab
  have hdiff : ‖(a : k) - (b : k)‖ < 1 := by
    -- Use the ultrametric triangle inequality on `(u+a) - (u+b)`.
    have : ‖(u + (a : k)) + (-(u + (b : k)))‖ < 1 := by
      refine (IsUltrametricDist.norm_add_le_max (u + (a : k)) (-(u + (b : k)))).trans_lt ?_
      have hb' : ‖-(u + (b : k))‖ < 1 := lt_of_eq_of_lt (norm_neg (u + (b : k))) hb
      exact max_lt ha hb'
    -- Simplify the inside by cancellation.
    have habel : (u + (a : k)) + (-(u + (b : k))) = (a : k) - (b : k) := by
      -- `abel` works in the additive commutative group `k`.
      abel
    have hnorm :
        ‖(a : k) - (b : k)‖ = ‖(u + (a : k)) + (-(u + (b : k)))‖ :=
      (congrArg (fun x : k => ‖x‖) habel).symm
    exact lt_of_eq_of_lt hnorm this
  have h1 : ‖(a : k) - (b : k)‖ = 1 :=
    norm_sub_natCast_eq_one_of_ne (k := k) hnat (a := a) (b := b) (by simpa using hab)
  have : (1 : ℝ) < 1 := by simpa [h1] using hdiff
  exact lt_irrefl _ this

end NatCastNorm

/-! ### Coordinate-map iteration lemmas

To relate the recursive definition `iterPQ` to conjugation by `H` and `K`, it is convenient to
work with coordinate maps `Fin 2 → MvPowerSeries (Fin 2) k` and their composition `CoordMap2.comp`.
-/

section CoordMap2Iter

variable {k : Type*} [CommRing k]

lemma substMap_hasSubst {P Q : MvPowerSeries (Fin 2) k}
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0) :
    MvPowerSeries.HasSubst (substMap P Q) := by
  classical
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Fin 2) (τ := Fin 2) (a := substMap P Q) ?_
  intro i
  fin_cases i <;> simpa [substMap, hP0, hQ0]

lemma CoordMap2.comp_id_right (F : CoordMap2 k) : CoordMap2.comp F (CoordMap2.id (k := k)) = F := by
  funext i
  -- Rewrite the substitution map as `MvPowerSeries.X` and use `MvPowerSeries.subst_self`.
  have hsub :
      (substMap (MvPowerSeries.X 0) (MvPowerSeries.X 1) : Fin 2 → MvPowerSeries (Fin 2) k) =
        (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k) := by
    funext j
    fin_cases j <;> simp [substMap]
  have hself :
      MvPowerSeries.subst (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k) (F i) = F i := by
    simpa using
      congrArg (fun f : MvPowerSeries (Fin 2) k → MvPowerSeries (Fin 2) k => f (F i))
        (MvPowerSeries.subst_self (σ := Fin 2) (R := k))
  simpa [CoordMap2.comp, CoordMap2.id, hsub] using hself

lemma CoordMap2.comp_id_left (F : CoordMap2 k)
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    CoordMap2.comp (CoordMap2.id (k := k)) F = F := by
  funext i
  have hsub : MvPowerSeries.HasSubst (substMap (F 0) (F 1)) :=
    substMap_hasSubst (k := k) (P := F 0) (Q := F 1) (hF0 0) (hF0 1)
  fin_cases i
  · simpa [CoordMap2.comp, CoordMap2.id, substMap] using
      (MvPowerSeries.subst_X (R := k) (a := substMap (F 0) (F 1)) hsub 0)
  · simpa [CoordMap2.comp, CoordMap2.id, substMap] using
      (MvPowerSeries.subst_X (R := k) (a := substMap (F 0) (F 1)) hsub 1)

lemma CoordMap2.comp_assoc (F G H : CoordMap2 k)
    (hG0 : ∀ i, MvPowerSeries.constantCoeff (G i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0) :
    CoordMap2.comp (CoordMap2.comp F G) H = CoordMap2.comp F (CoordMap2.comp G H) := by
  funext i
  have hG : MvPowerSeries.HasSubst (substMap (G 0) (G 1)) :=
    substMap_hasSubst (k := k) (P := G 0) (Q := G 1) (hG0 0) (hG0 1)
  have hH : MvPowerSeries.HasSubst (substMap (H 0) (H 1)) :=
    substMap_hasSubst (k := k) (P := H 0) (Q := H 1) (hH0 0) (hH0 1)
  -- Associate substitutions using `subst_comp_subst_apply`.
  have hmap :
      (fun s : Fin 2 =>
          MvPowerSeries.subst (substMap (H 0) (H 1))
            (substMap (G 0) (G 1) s)) =
        substMap (MvPowerSeries.subst (substMap (H 0) (H 1)) (G 0))
          (MvPowerSeries.subst (substMap (H 0) (H 1)) (G 1)) := by
    funext s
    fin_cases s <;> simp [substMap]
  simpa [CoordMap2.comp, hmap] using
    (MvPowerSeries.subst_comp_subst_apply (R := k) (a := substMap (G 0) (G 1))
      (b := substMap (H 0) (H 1)) hG hH (F i))

/-- Iteration of a coordinate map by composition. -/
noncomputable def CoordMap2.iter (F : CoordMap2 k) : ℕ → CoordMap2 k
  | 0 => CoordMap2.id (k := k)
  | n + 1 => CoordMap2.comp F (CoordMap2.iter F n)

lemma CoordMap2.iter_zero (F : CoordMap2 k) : CoordMap2.iter F 0 = CoordMap2.id (k := k) := rfl

lemma CoordMap2.iter_succ (F : CoordMap2 k) (n : ℕ) :
    CoordMap2.iter F (n + 1) = CoordMap2.comp F (CoordMap2.iter F n) := rfl

lemma CoordMap2.constantCoeff_comp_eq_zero (F G : CoordMap2 k)
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (hG0 : ∀ i, MvPowerSeries.constantCoeff (G i) = 0) :
    ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) F G) i) = 0 := by
  classical
  intro i
  have ha : MvPowerSeries.HasSubst (substMap (G 0) (G 1)) :=
    substMap_hasSubst (k := k) (P := G 0) (Q := G 1) (hG0 0) (hG0 1)
  have ha' : ∀ j : Fin 2, MvPowerSeries.constantCoeff (substMap (G 0) (G 1) j) = 0 := by
    intro j
    fin_cases j <;> simpa [substMap, hG0 0, hG0 1]
  simpa [CoordMap2.comp] using
    (MvPowerSeries.constantCoeff_subst_eq_zero (R := k) (a := substMap (G 0) (G 1)) ha ha'
      (f := F i) (hF0 i))

lemma CoordMap2.constantCoeff_iter_eq_zero (F : CoordMap2 k)
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    ∀ n i, MvPowerSeries.constantCoeff ((CoordMap2.iter (k := k) F n) i) = 0 := by
  intro n
  induction n with
  | zero =>
      intro i
      simpa [CoordMap2.iter, CoordMap2.id] using (MvPowerSeries.constantCoeff_X (R := k) i)
  | succ n ih =>
      intro i
      simpa [CoordMap2.iter, CoordMap2.iter_succ] using
        (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := F) (G := CoordMap2.iter (k := k) F n)
          hF0 ih i)

lemma CoordMap2.iter_conj (f g H K : CoordMap2 k)
    (hf0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0)
    (hK0 : ∀ i, MvPowerSeries.constantCoeff (K i) = 0)
    (hHK : CoordMap2.comp (k := k) H K = CoordMap2.id (k := k))
    (hKH : CoordMap2.comp (k := k) K H = CoordMap2.id (k := k))
    (hg : g = CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) f K)) :
    ∀ n : ℕ, CoordMap2.iter (k := k) f n =
      CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H) := by
  intro n
  have hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := by
    -- `g = H ∘ (f ∘ K)` and all components have zero constant coefficient.
    have hfK0 : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) f K) i) = 0 :=
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := f) (G := K) hf0 hK0
    simpa [hg] using
      (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := H) (G := CoordMap2.comp (k := k) f K) hH0 hfK0)
  induction n with
  | zero =>
      -- `f⁰ = id` and `K ∘ id ∘ H = K ∘ H = id`.
      have hidH : CoordMap2.comp (k := k) (CoordMap2.id (k := k)) H = H := by
        simpa using (CoordMap2.comp_id_left (k := k) (F := H) hH0)
      simpa [CoordMap2.iter, hidH] using hKH.symm
  | succ n ih =>
      -- Use the induction hypothesis and `K ∘ g = f ∘ K`.
      have hiterg0 :
          ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.iter (k := k) g n) i) = 0 :=
        CoordMap2.constantCoeff_iter_eq_zero (k := k) (F := g) hg0 n
      have hfK : CoordMap2.comp (k := k) f K = CoordMap2.comp (k := k) K g := by
        -- Multiply `g = H ∘ f ∘ K` on the left by `K` and use `K ∘ H = id`.
        have hfK0' : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) f K) i) = 0 :=
          CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := f) (G := K) hf0 hK0
        calc
          CoordMap2.comp (k := k) f K
              = CoordMap2.comp (k := k) (CoordMap2.id (k := k)) (CoordMap2.comp (k := k) f K) := by
                  simpa using (CoordMap2.comp_id_left (k := k) (F := CoordMap2.comp (k := k) f K) hfK0').symm
          _ = CoordMap2.comp (k := k) (CoordMap2.comp (k := k) K H) (CoordMap2.comp (k := k) f K) := by
                  simpa [hKH]
          _ = CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) f K)) := by
                  simpa using
                    (CoordMap2.comp_assoc (k := k) (F := K) (G := H) (H := CoordMap2.comp (k := k) f K) hH0 hfK0')
          _ = CoordMap2.comp (k := k) K g := by simpa [hg]
      -- Now compute `f ∘ (K ∘ gⁿ ∘ H)` and reassociate.
      calc
        CoordMap2.iter (k := k) f (n + 1)
            = CoordMap2.comp (k := k) f (CoordMap2.iter (k := k) f n) := by rfl
        _ = CoordMap2.comp (k := k) f (CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H)) := by
              simpa [ih]
        _ = CoordMap2.comp (k := k) (CoordMap2.comp (k := k) f K)
              (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H) := by
              -- reassociate: `f ∘ (K ∘ X) = (f ∘ K) ∘ X`
              simpa using
                (CoordMap2.comp_assoc (k := k) (F := f) (G := K)
                  (H := CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H) hK0
                  (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := CoordMap2.iter (k := k) g n) (G := H)
                    hiterg0 hH0)).symm
        _ = CoordMap2.comp (k := k) (CoordMap2.comp (k := k) K g)
              (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H) := by simpa [hfK]
        _ = CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) g (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H)) := by
              -- reassociate: `(K ∘ g) ∘ X = K ∘ (g ∘ X)`
              simpa using
                (CoordMap2.comp_assoc (k := k) (F := K) (G := g)
                  (H := CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g n) H) hg0
                  (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := CoordMap2.iter (k := k) g n) (G := H)
                    hiterg0 hH0))
        _ = CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g (n + 1)) H) := by
              simp [CoordMap2.iter, CoordMap2.iter_succ, CoordMap2.comp_assoc, hg0, hiterg0, hH0]

lemma iterPQ_eq_iter (P Q : MvPowerSeries (Fin 2) k) :
    ∀ n : ℕ,
      CoordMap2.iter (k := k) (substMap P Q) n = substMap (iterPQ P Q n).1 (iterPQ P Q n).2 := by
  intro n
  induction n with
  | zero =>
      ext i
      fin_cases i <;> simp [CoordMap2.iter, iterPQ, CoordMap2.id, substMap]
  | succ n ih =>
      ext i
      fin_cases i <;> simp [CoordMap2.iter, iterPQ, CoordMap2.comp, substMap, ih]

end CoordMap2Iter

section QIterLemmas

variable {k : Type*} [CommRing k]

lemma qIter_eq_subst_iter (P Q : MvPowerSeries (Fin 2) k) (d : ℕ) :
    qIter k P Q d =
      MvPowerSeries.subst (xOnlySubst k) ((CoordMap2.iter (k := k) (substMap P Q) d) 1) := by
  -- Unfold `qIter` and rewrite the iterate using `iterPQ_eq_iter`.
  simp [qIter, (iterPQ_eq_iter (k := k) (P := P) (Q := Q) d), substMap]

end QIterLemmas

/-! ### Specializing compositions to the `x`-axis

The normal form argument in `new/Temp.md` repeatedly uses the identity

`F(G(x,0)) = F(G₀(x,0), G₁(x,0))`.

In terms of `MvPowerSeries.subst`, this is an instance of `subst_subst`. We record the exact
rewrite used later when we express `qIter` via the conjugacy `f^d = K ∘ g^d ∘ H`.
-/

section RestrictXAxis

variable {k : Type*} [CommRing k]

/-- Restriction `(x,y) ↦ (x,0)` applied to a bivariate power series. -/
noncomputable abbrev restrictX (F : MvPowerSeries (Fin 2) k) : k⟦X⟧ :=
  MvPowerSeries.subst (xOnlySubst k) F

lemma restrictX_subst {F : MvPowerSeries (Fin 2) k} {G : CoordMap2 k}
    (hG0 : ∀ i, MvPowerSeries.constantCoeff (G i) = 0) :
    restrictX (k := k) (MvPowerSeries.subst (substMap (G 0) (G 1)) F) =
      MvPowerSeries.subst
        (substMap1 (restrictX (k := k) (G 0)) (restrictX (k := k) (G 1))) F := by
  classical
  have hG : MvPowerSeries.HasSubst (substMap (G 0) (G 1)) :=
    substMap_hasSubst (k := k) (P := G 0) (Q := G 1) (hG0 0) (hG0 1)
  have hmap :
      (fun s : Fin 2 => MvPowerSeries.subst (xOnlySubst k) (substMap (G 0) (G 1) s)) =
        substMap1 (restrictX (k := k) (G 0)) (restrictX (k := k) (G 1)) := by
    funext s
    fin_cases s <;> simp [restrictX, substMap1, substMap]
  -- `subst (x,0)` after a substitution is the same as substituting the restrictions.
  simpa [restrictX, hmap] using
    (MvPowerSeries.subst_comp_subst_apply (a := substMap (G 0) (G 1)) (b := xOnlySubst k)
      hG (xOnlySubst_hasSubst k) F)

end RestrictXAxis

section ConjugacyQIter

variable {k : Type*} [CommRing k]

/-- Rewriting `qIter` using a conjugacy `g = H ∘ f ∘ K` and the formula `f^d = K ∘ g^d ∘ H`. -/
lemma qIter_eq_subst_conj (P Q : MvPowerSeries (Fin 2) k) (g H K : CoordMap2 k)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0)
    (hK0 : ∀ i, MvPowerSeries.constantCoeff (K i) = 0)
    (hHK : CoordMap2.comp (k := k) H K = CoordMap2.id (k := k))
    (hKH : CoordMap2.comp (k := k) K H = CoordMap2.id (k := k))
    (hg : g = CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) (substMap P Q) K)) (d : ℕ) :
    qIter k P Q d =
      MvPowerSeries.subst
        (substMap1
          (restrictX (k := k) ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) 0))
          (restrictX (k := k) ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) 1)))
        (K 1) := by
  classical
  have hf0 : ∀ i, MvPowerSeries.constantCoeff ((substMap P Q) i) = 0 := by
    intro i
    fin_cases i <;> simpa [substMap, hP0, hQ0]
  have hiter :
      CoordMap2.iter (k := k) (substMap P Q) d =
        CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) :=
    (CoordMap2.iter_conj (k := k) (f := substMap P Q) (g := g) (H := H) (K := K) hf0 hH0 hK0 hHK hKH
        hg) d
  -- Express `qIter` using `CoordMap2.iter`.
  have hq :
      qIter k P Q d =
        MvPowerSeries.subst (xOnlySubst k) ((CoordMap2.iter (k := k) (substMap P Q) d) 1) := by
    simpa using (qIter_eq_subst_iter (k := k) (P := P) (Q := Q) d)
  -- Push the restriction through the conjugacy formula and use `restrictX_subst`.
  have hGH0 :
      ∀ i,
        MvPowerSeries.constantCoeff
            ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i) =
          0 := by
    have hiterg0 :
        ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.iter (k := k) g d) i) = 0 :=
      CoordMap2.constantCoeff_iter_eq_zero (k := k) (F := g) hg0 d
    exact
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := CoordMap2.iter (k := k) g d) (G := H) hiterg0 hH0
  -- Apply the specialization lemma to the outer substitution `K ∘ (g^d ∘ H)`.
  -- Set `GH := g^d ∘ H`.
  let GH : CoordMap2 k := CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H
  have hq' :
      qIter k P Q d =
        restrictX (k := k) (MvPowerSeries.subst (substMap (GH 0) (GH 1)) (K 1)) := by
    -- Rewrite using `hiter` and unfold `CoordMap2.comp`.
    simpa [hq, hiter, CoordMap2.comp, GH, restrictX, substMap] using rfl
  -- Now commute the restriction with substitution.
  simpa [hq', GH] using (restrictX_subst (k := k) (F := K 1) (G := GH) (by simpa [GH] using hGH0))

end ConjugacyQIter

/-! ### Iterating the triangular normal form on the `x`-axis

In `new/Temp.md` §3.3 one studies the univariate series obtained by restricting the conjugated map
`g^d ∘ H` to the `x`-axis. The key input is that in normal form the map `g` is *triangular*:

`g₀(x,y) = λ x + τ y`, `g₁(x,y) = μ y + b x^m`.

The following lemmas package the resulting recurrences for the restricted iterates.
-/

section TriangularAxisIter

variable {k : Type*} [CommRing k]

lemma substMap1_hasSubst {p q : k⟦X⟧}
    (hp0 : PowerSeries.constantCoeff p = 0) (hq0 : PowerSeries.constantCoeff q = 0) :
    MvPowerSeries.HasSubst (substMap1 p q) := by
  classical
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Fin 2) (τ := Unit) (a := substMap1 p q) ?_
  intro i
  fin_cases i
  · simpa [substMap1] using (show MvPowerSeries.constantCoeff p = 0 from hp0)
  · simpa [substMap1] using (show MvPowerSeries.constantCoeff q = 0 from hq0)

lemma subst_C_fin2 (a : Fin 2 → k⟦X⟧) (ha : MvPowerSeries.HasSubst a) (r : k) :
    MvPowerSeries.subst (R := k) (S := k) a (MvPowerSeries.C (σ := Fin 2) (R := k) r) =
      (PowerSeries.C r : k⟦X⟧) := by
  -- Reduce to the `monomial` substitution formula at `e = 0`.
  rw [← MvPowerSeries.monomial_zero_eq_C_apply (σ := Fin 2) (R := k) r]
  rw [MvPowerSeries.subst_monomial (R := k) (S := k) (a := a) ha (e := (0 : Fin 2 →₀ ℕ)) (r := r)]
  -- The empty product is `1`.
  rw [Finsupp.prod_zero_index, mul_one]
  simp [PowerSeries.C_eq_algebraMap]

/-- The triangular normal form coordinate map. -/
noncomputable def triangularMap (lam mu tau b : k) (m : ℕ) : CoordMap2 k
  | 0 => MvPowerSeries.C lam * MvPowerSeries.X 0 + MvPowerSeries.C tau * MvPowerSeries.X 1
  | 1 =>
      MvPowerSeries.C mu * MvPowerSeries.X 1 + MvPowerSeries.monomial (Finsupp.single 0 m) b

/-- The univariate restriction of `(g^d ∘ H)` to the `x`-axis. -/
noncomputable def axisIter (g H : CoordMap2 k) (d : ℕ) : Fin 2 → k⟦X⟧ :=
  fun i =>
    restrictX (k := k)
      ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i)

lemma axisIter_constantCoeff_eq_zero (g H : CoordMap2 k)
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0) (d : ℕ) (i : Fin 2) :
    PowerSeries.constantCoeff (axisIter (k := k) g H d i) = 0 := by
  classical
  -- First show the bivariate series has zero constant coefficient.
  have hiterg0 :
      ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.iter (k := k) g d) i) = 0 :=
    CoordMap2.constantCoeff_iter_eq_zero (k := k) (F := g) hg0 d
  have hcomp0 :
      ∀ i,
        MvPowerSeries.constantCoeff
            ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i) =
          0 :=
    CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := CoordMap2.iter (k := k) g d) (G := H) hiterg0 hH0
  -- Now apply `constantCoeff_subst_eq_zero` to the restriction map `(x,y) ↦ (X,0)`.
  have hx0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff (xOnlySubst k s) = 0 := by
    intro s
    fin_cases s <;> simp [xOnlySubst, PowerSeries.X, MvPowerSeries.constantCoeff_X]
  have : MvPowerSeries.constantCoeff (MvPowerSeries.subst (xOnlySubst k)
      ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i)) = 0 := by
    -- `xOnlySubst_hasSubst` gives `HasSubst` for the restriction map.
    simpa using
      (MvPowerSeries.constantCoeff_subst_eq_zero (a := xOnlySubst k) (ha := xOnlySubst_hasSubst k) hx0
        (f := ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i)) (hcomp0 i))
  simpa [axisIter, restrictX] using this

lemma axisIter_succ (g H : CoordMap2 k)
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0) (d : ℕ) :
    axisIter (k := k) g H (d + 1) =
      fun i =>
        MvPowerSeries.subst
            (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1))
            (g i) := by
  classical
  funext i
  -- Reassociate `(g ∘ g^d) ∘ H = g ∘ (g^d ∘ H)`.
  have hiterg0 :
      ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.iter (k := k) g d) i) = 0 :=
    CoordMap2.constantCoeff_iter_eq_zero (k := k) (F := g) hg0 d
  have hG0 :
      ∀ i,
        MvPowerSeries.constantCoeff
            ((CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) i) =
          0 :=
    CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := CoordMap2.iter (k := k) g d) (G := H) hiterg0 hH0
  -- Use `restrictX_subst` to commute restriction with the outer substitution.
  have hcomp :
      CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g (d + 1)) H =
        CoordMap2.comp (k := k) g (CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H) := by
    -- Expand the iterate and use associativity.
    simpa [CoordMap2.iter, CoordMap2.iter_succ] using
      (CoordMap2.comp_assoc (k := k) (F := g) (G := CoordMap2.iter (k := k) g d) (H := H) hiterg0 hH0)
  -- Now compute the `i`-th coordinate.
  -- `axisIter` is `restrictX` applied to the bivariate coordinate.
  -- The right-hand side is the univariate substitution into `g i`.
  --
  -- Start from the left-hand side, reassociate using `hcomp`, then apply `restrictX_subst`.
  -- Set `GH := g^d ∘ H`.
  let GH : CoordMap2 k := CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g d) H
  have hcomp' :
      CoordMap2.comp (k := k) (CoordMap2.iter (k := k) g (d + 1)) H =
        CoordMap2.comp (k := k) g GH := by
    simpa [GH] using hcomp
  have haxis :
      axisIter (k := k) g H (d + 1) i =
        restrictX (k := k) ((CoordMap2.comp (k := k) g GH) i) := by
    simpa [axisIter, hcomp'] using rfl
  -- Rewrite the right-hand side as a `subst`-expression and apply `restrictX_subst`.
  have haxis' :
      axisIter (k := k) g H (d + 1) i =
        restrictX (k := k) (MvPowerSeries.subst (substMap (GH 0) (GH 1)) (g i)) := by
    simpa [CoordMap2.comp] using haxis
  -- `GH` has zero constant coefficients, so we may commute restriction with substitution.
  have hGH0 : ∀ i, MvPowerSeries.constantCoeff (GH i) = 0 := by
    simpa [GH] using hG0
  -- Apply the specialization lemma to `g i` and the substitution map `GH`.
  have hspec :
      restrictX (k := k) (MvPowerSeries.subst (substMap (GH 0) (GH 1)) (g i)) =
        MvPowerSeries.subst
            (substMap1 (restrictX (k := k) (GH 0)) (restrictX (k := k) (GH 1)))
            (g i) :=
    restrictX_subst (k := k) (F := g i) (G := GH) hGH0
  -- Identify the restrictions of `GH` with the previous iterate.
  have hGH_restrict0 : restrictX (k := k) (GH 0) = axisIter (k := k) g H d 0 := by
    simp [axisIter, GH]
  have hGH_restrict1 : restrictX (k := k) (GH 1) = axisIter (k := k) g H d 1 := by
    simp [axisIter, GH]
  -- Put everything together.
  simpa [haxis', hGH_restrict0, hGH_restrict1] using hspec

/-- Recurrence for the first coordinate on the `x`-axis, assuming `g₀ = λ X₀ + τ X₁`. -/
lemma axisIter_succ_fst_of_eq (g H : CoordMap2 k)
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0)
    (lam tau : k)
    (hg₁ : g 0 =
      MvPowerSeries.C lam * MvPowerSeries.X 0 + MvPowerSeries.C tau * MvPowerSeries.X 1)
    (d : ℕ) :
    axisIter (k := k) g H (d + 1) 0 =
      (PowerSeries.C lam : k⟦X⟧) * axisIter (k := k) g H d 0 +
        (PowerSeries.C tau : k⟦X⟧) * axisIter (k := k) g H d 1 := by
  classical
  -- Extract the one-step formula from `axisIter_succ`.
  have hsucc0 :
      axisIter (k := k) g H (d + 1) 0 =
        MvPowerSeries.subst
            (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1))
            (g 0) := by
    simpa using congrArg (fun f => f 0) (axisIter_succ (k := k) g H hg0 hH0 d)
  -- The substitution map has zero constant coefficients.
  have h0 :
      PowerSeries.constantCoeff (axisIter (k := k) g H d 0) = 0 :=
    axisIter_constantCoeff_eq_zero (k := k) g H hg0 hH0 d 0
  have h1 :
      PowerSeries.constantCoeff (axisIter (k := k) g H d 1) = 0 :=
    axisIter_constantCoeff_eq_zero (k := k) g H hg0 hH0 d 1
  have ha : MvPowerSeries.HasSubst
      (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1)) :=
    substMap1_hasSubst (k := k) h0 h1
  -- Evaluate the substitution explicitly.
  -- (We keep `simp` local by providing `ha` explicitly.)
  simpa [hsucc0, hg₁, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
    subst_C_fin2 (k := k) (a := substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1))
      (ha := ha),
    MvPowerSeries.subst_X ha, substMap1]

/-- Recurrence for the second coordinate on the `x`-axis, assuming `g₁ = μ X₁ + b X₀^m`. -/
lemma axisIter_succ_snd_of_eq (g H : CoordMap2 k)
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0)
    (mu b : k) (m : ℕ)
    (hg₂ : g 1 =
      MvPowerSeries.C mu * MvPowerSeries.X 1 + MvPowerSeries.monomial (Finsupp.single 0 m) b)
    (d : ℕ) :
    axisIter (k := k) g H (d + 1) 1 =
      (PowerSeries.C mu : k⟦X⟧) * axisIter (k := k) g H d 1 +
        (PowerSeries.C b : k⟦X⟧) * (axisIter (k := k) g H d 0) ^ m := by
  classical
  -- Extract the one-step formula from `axisIter_succ`.
  have hsucc1 :
      axisIter (k := k) g H (d + 1) 1 =
        MvPowerSeries.subst
            (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1))
            (g 1) := by
    simpa using congrArg (fun f => f 1) (axisIter_succ (k := k) g H hg0 hH0 d)
  -- The substitution map has zero constant coefficients.
  have h0 :
      PowerSeries.constantCoeff (axisIter (k := k) g H d 0) = 0 :=
    axisIter_constantCoeff_eq_zero (k := k) g H hg0 hH0 d 0
  have h1 :
      PowerSeries.constantCoeff (axisIter (k := k) g H d 1) = 0 :=
    axisIter_constantCoeff_eq_zero (k := k) g H hg0 hH0 d 1
  have ha : MvPowerSeries.HasSubst
      (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1)) :=
    substMap1_hasSubst (k := k) h0 h1
  -- Evaluate the substitution explicitly.
  -- The monomial term becomes `b * X_d^m`.
  have hprod :
      (Finsupp.single (0 : Fin 2) m).prod
          (fun s n =>
            (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1) s) ^ n) =
        (axisIter (k := k) g H d 0) ^ m := by
    -- `Finsupp.prod_single_index` computes the product over a single support element.
    simpa [substMap1] using
      (Finsupp.prod_single_index (a := (0 : Fin 2)) (b := m)
        (h := fun s n =>
          (substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1) s) ^ n) (by simp))
  -- Now finish by rewriting `g 1` and expanding `subst`.
  -- We use `simp` for the constant and linear terms, and the explicit `hprod` for the monomial term.
  -- Note: `algebraMap k k⟦X⟧` is `PowerSeries.C`.
  simpa [hsucc1, hg₂, MvPowerSeries.subst_add ha, MvPowerSeries.subst_mul ha,
    subst_C_fin2 (k := k) (a := substMap1 (axisIter (k := k) g H d 0) (axisIter (k := k) g H d 1))
      (ha := ha),
    MvPowerSeries.subst_X ha, MvPowerSeries.subst_monomial (a := substMap1 (axisIter (k := k) g H d 0)
      (axisIter (k := k) g H d 1)) (ha := ha),
    hprod, PowerSeries.C_eq_algebraMap, substMap1]

end TriangularAxisIter

/-! ### Rewriting the goal using `divXPowOrder`

The statement of `iter_coeff_bound` is naturally expressed in terms of the normalized series
`q_d.divXPowOrder`. The lemmas in `Mathlib/RingTheory/PowerSeries/Order.lean` turn the coefficients
appearing in the goal into coefficients and the constant coefficient of `divXPowOrder`.
-/

section DivXPowOrderRewrite

variable {k : Type*} [NormedRing k]

lemma coeff_order_toNat_eq_constantCoeff_divXPowOrder (f : k⟦X⟧) :
    coeff f.order.toNat f = PowerSeries.constantCoeff (divXPowOrder f) := by
  simpa [constantCoeff_divXPowOrder, ← PowerSeries.coeff_zero_eq_constantCoeff] using
    (constantCoeff_divXPowOrder (f := f)).symm

lemma coeff_order_toNat_eq_constantCoeff_divXPowOrder_norm (f : k⟦X⟧) :
    ‖coeff f.order.toNat f‖ = ‖PowerSeries.constantCoeff (divXPowOrder f)‖ := by
  simpa [coeff_order_toNat_eq_constantCoeff_divXPowOrder (k := k) (f := f)]

lemma coeff_order_toNat_add_eq_coeff_divXPowOrder (f : k⟦X⟧) (m : ℕ) :
    coeff (f.order.toNat + m) f = coeff m (divXPowOrder f) := by
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (coeff_divXPowOrder (f := f) (n := m)).symm

lemma norm_coeff_order_toNat_add_eq_norm_coeff_divXPowOrder (f : k⟦X⟧) (m : ℕ) :
    ‖coeff (f.order.toNat + m) f‖ = ‖coeff m (divXPowOrder f)‖ := by
  simpa [coeff_order_toNat_add_eq_coeff_divXPowOrder (k := k) (f := f) (m := m)]

lemma coeff_bound_iff_divXPowOrder (f : k⟦X⟧) (M r : ℝ) (m : ℕ) :
    r ^ m * ‖coeff (f.order.toNat + m) f‖ ≤ M * ‖coeff f.order.toNat f‖ ↔
      r ^ m * ‖coeff m (divXPowOrder f)‖ ≤ M * ‖PowerSeries.constantCoeff (divXPowOrder f)‖ := by
  -- Rewrite both coefficients in terms of `divXPowOrder`.
  simpa [norm_coeff_order_toNat_add_eq_norm_coeff_divXPowOrder (k := k) (f := f) (m := m),
    coeff_order_toNat_eq_constantCoeff_divXPowOrder_norm (k := k) (f := f)]

end DivXPowOrderRewrite

/-! ### Coefficient bounds for normalized series (framework)

The conclusion of `iter_coeff_bound` is most naturally expressed for the *normalized* univariate
series `divXPowOrder f`. We package the exact inequality we want as a predicate, to make the final
Step 3.3 reductions in the proof more legible.
-/

section NormalizedCoeffBound

variable {k : Type*} [NormedRing k]

/-- A bound on the normalized coefficients of a univariate power series at a radius `r`. -/
def NormalizedCoeffBound (f : k⟦X⟧) (M r : ℝ) : Prop :=
  ∀ m : ℕ,
    r ^ m * ‖coeff m (divXPowOrder f)‖ ≤ M * ‖PowerSeries.constantCoeff (divXPowOrder f)‖

lemma normalizedCoeffBound_iff {f : k⟦X⟧} {M r : ℝ} :
    NormalizedCoeffBound (k := k) f M r ↔
      ∀ m : ℕ, r ^ m * ‖coeff (f.order.toNat + m) f‖ ≤ M * ‖coeff f.order.toNat f‖ := by
  constructor
  · intro h m
    exact (coeff_bound_iff_divXPowOrder (k := k) (f := f) (M := M) (r := r) (m := m)).2 (h m)
  · intro h m
    exact (coeff_bound_iff_divXPowOrder (k := k) (f := f) (M := M) (r := r) (m := m)).1 (h m)

lemma NormalizedCoeffBound.mono {f : k⟦X⟧} {M₁ M₂ r : ℝ} (hM : M₁ ≤ M₂)
    (h : NormalizedCoeffBound (k := k) f M₁ r) :
    NormalizedCoeffBound (k := k) f M₂ r := by
  intro m
  exact (h m).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

end NormalizedCoeffBound

/-! ### Weighted Gauss norms / Weierstrass / inverse function (statements)

`new/Temp.md` uses three standard analytic ingredients:

* weighted Gauss norms on a closed disc of radius `ρ`,
* Weierstrass-type factorizations (`f = X^n * unit`),
* inverse-function-type control for coordinate changes tangent to the identity.

Mathlib already provides the formal factorization via `divXPowOrder` (and that `divXPowOrder f` is a
unit when `f ≠ 0`). The remaining *quantitative* estimates are recorded below as statements to be
used later in the proof of the normal-form estimate.
-/

section AnalyticStatements

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

/-! #### Weighted Gauss bounds -/

lemma WeightedGaussBound1.mono {ρ C₁ C₂ : ℝ} {f : k⟦X⟧} (hC : C₁ ≤ C₂)
    (h : WeightedGaussBound1 (k := k) ρ C₁ f) :
    WeightedGaussBound1 (k := k) ρ C₂ f := by
  intro n
  exact (h n).trans hC

lemma WeightedGaussBound2.mono {ρ C₁ C₂ : ℝ} {F : MvPowerSeries (Fin 2) k} (hC : C₁ ≤ C₂)
    (h : WeightedGaussBound2 (k := k) ρ C₁ F) :
    WeightedGaussBound2 (k := k) ρ C₂ F := by
  intro e
  exact (h e).trans hC

/-- Temp.md Lemma 3.3.2 (univariate): if `f` has no constant term and is restricted, then after shrinking the
radius its weighted Gauss bound can be made arbitrarily small. -/
theorem exists_radius_weightedGaussBound1_of_constantCoeff_eq_zero
    {f : k⟦X⟧} (hfT : IsTate k Unit (f : MvPowerSeries Unit k))
    (hf0 : PowerSeries.constantCoeff f = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ WeightedGaussBound1 (k := k) ρ ε f := by
  classical
  -- Coefficients tend to `0`, hence are eventually in the ball of radius `ε`.
  have hball :
      ∀ᶠ e : Unit →₀ ℕ in Filter.cofinite,
        MvPowerSeries.coeff e (f : MvPowerSeries Unit k) ∈ Metric.ball (0 : k) ε := by
    have hnear : ∀ᶠ x : k in nhds (0 : k), x ∈ Metric.ball (0 : k) ε := by
      change Metric.ball (0 : k) ε ∈ nhds (0 : k)
      exact Metric.ball_mem_nhds (0 : k) hε
    exact hfT.eventually hnear
  have hsmall :
      ∀ᶠ e : Unit →₀ ℕ in Filter.cofinite,
        ‖MvPowerSeries.coeff e (f : MvPowerSeries Unit k)‖ < ε := by
    refine hball.mono ?_
    intro e he
    simpa [Metric.mem_ball, dist_eq_norm] using he

  -- Let `S` be the set of indices with coefficients of size at least `ε`.
  let T : Set (Unit →₀ ℕ) :=
    {e : Unit →₀ ℕ | ¬ ‖MvPowerSeries.coeff e (f : MvPowerSeries Unit k)‖ < ε}
  have hTfin : T.Finite := (Filter.eventually_cofinite.1 hsmall)
  let S : Set ℕ := (fun n : ℕ => (Finsupp.single () n : Unit →₀ ℕ)) ⁻¹' T
  have hSfin : S.Finite :=
    hTfin.preimage (Set.injOn_of_injective (Finsupp.single_injective ()))
  let sFin : Finset ℕ := hSfin.toFinset

  -- The index `0` is not exceptional since the constant coefficient is `0`.
  have h0not : (0 : ℕ) ∉ sFin := by
    intro h0
    have h0S : (0 : ℕ) ∈ S := (Set.Finite.mem_toFinset hSfin).1 h0
    have h0T : (Finsupp.single () (0 : ℕ) : Unit →₀ ℕ) ∈ T := h0S
    have hnot :
        ¬ ‖MvPowerSeries.coeff (Finsupp.single () (0 : ℕ)) (f : MvPowerSeries Unit k)‖ < ε := by
      simpa [T] using h0T
    have hlt :
        ‖MvPowerSeries.coeff (Finsupp.single () (0 : ℕ)) (f : MvPowerSeries Unit k)‖ < ε := by
      have : ‖PowerSeries.coeff 0 f‖ < ε := by
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hε]
      simpa using this
    exact hnot hlt

  by_cases hs : sFin.Nonempty
  · -- Nonempty exceptional set: choose `ρ = min 1 (ε / A)` where `A` bounds the exceptional coefficients.
    let A : ℝ := sFin.sup' hs (fun n => ‖coeff n f‖)
    have hA_ge : ∀ {n}, n ∈ sFin → ‖coeff n f‖ ≤ A := by
      intro n hn
      exact Finset.le_sup' (s := sFin) (f := fun n => ‖coeff n f‖) hn
    have hA_pos : 0 < A := by
      rcases hs with ⟨n, hn⟩
      have hnS : n ∈ S := (Set.Finite.mem_toFinset hSfin).1 hn
      have hnT : (Finsupp.single () n : Unit →₀ ℕ) ∈ T := hnS
      have hnot : ¬ ‖coeff n f‖ < ε := by
        simpa [T] using hnT
      have hε_le : ε ≤ ‖coeff n f‖ := le_of_not_gt hnot
      have hε_leA : ε ≤ A := le_trans hε_le (hA_ge (n := n) hn)
      exact lt_of_lt_of_le hε hε_leA

    let ρ : ℝ := min 1 (ε / A)
    have hρ_pos : 0 < ρ := by
      have hpos : 0 < ε / A := div_pos hε hA_pos
      have : 0 < min (1 : ℝ) (ε / A) := lt_min (by norm_num) hpos
      simpa [ρ] using this
    have hρ_le1 : ρ ≤ 1 := by simp [ρ]
    have hρ_le : ρ ≤ ε / A := by
      simpa [ρ] using (min_le_right (1 : ℝ) (ε / A))
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hmul : A * ρ ≤ ε := by
      have hA0 : 0 ≤ A := le_of_lt hA_pos
      have : A * ρ ≤ A * (ε / A) := mul_le_mul_of_nonneg_left hρ_le hA0
      simpa [mul_div_cancel₀ (a := ε) hA_ne] using this

    refine ⟨ρ, hρ_pos, hρ_le1, ?_⟩
    intro n
    by_cases hn : n ∈ sFin
    · have hn_ne0 : n ≠ 0 := by
        intro h
        subst h
        exact h0not hn
      have hpow_le : ρ ^ n ≤ ρ := by
        rcases Nat.exists_eq_succ_of_ne_zero hn_ne0 with ⟨m, rfl⟩
        have hρ0 : 0 ≤ ρ := le_of_lt hρ_pos
        have hρm : ρ ^ m ≤ 1 := pow_le_one₀ hρ0 hρ_le1
        simpa [pow_succ] using mul_le_mul_of_nonneg_right hρm hρ0
      have hcoeff_leA : ‖coeff n f‖ ≤ A := hA_ge (n := n) hn
      calc
        ‖coeff n f‖ * ρ ^ n ≤ ‖coeff n f‖ * ρ :=
          mul_le_mul_of_nonneg_left hpow_le (norm_nonneg _)
        _ ≤ A * ρ := mul_le_mul_of_nonneg_right hcoeff_leA (le_of_lt hρ_pos)
        _ ≤ ε := hmul
    · have hnS : n ∉ S := by
        intro hnS
        have : n ∈ sFin := (Set.Finite.mem_toFinset hSfin).2 hnS
        exact hn this
      have hcoeff_lt : ‖coeff n f‖ < ε := by
        have : (Finsupp.single () n : Unit →₀ ℕ) ∉ T := by
          simpa [S] using hnS
        have :
            ¬ ¬ ‖MvPowerSeries.coeff (Finsupp.single () n) (f : MvPowerSeries Unit k)‖ < ε := by
          simpa [T] using this
        have :
            ‖MvPowerSeries.coeff (Finsupp.single () n) (f : MvPowerSeries Unit k)‖ < ε :=
          not_not.mp this
        simpa using this
      have hcoeff_le : ‖coeff n f‖ ≤ ε := le_of_lt hcoeff_lt
      have hρ0 : 0 ≤ ρ := le_of_lt hρ_pos
      have hpow_le1 : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρ_le1
      calc
        ‖coeff n f‖ * ρ ^ n ≤ ‖coeff n f‖ * 1 :=
          mul_le_mul_of_nonneg_left hpow_le1 (norm_nonneg _)
        _ ≤ ε := by simpa using hcoeff_le
  · -- Empty exceptional set: take `ρ = 1`.
    have hs_empty : sFin = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
    refine ⟨1, by simp, le_rfl, ?_⟩
    intro n
    have hnS : n ∉ S := by
      intro hnS
      have : n ∈ sFin := (Set.Finite.mem_toFinset hSfin).2 hnS
      simpa [hs_empty] using this
    have hcoeff_lt : ‖coeff n f‖ < ε := by
      have : (Finsupp.single () n : Unit →₀ ℕ) ∉ T := by
        simpa [S] using hnS
      have :
          ¬ ¬ ‖MvPowerSeries.coeff (Finsupp.single () n) (f : MvPowerSeries Unit k)‖ < ε := by
        simpa [T] using this
      have : ‖MvPowerSeries.coeff (Finsupp.single () n) (f : MvPowerSeries Unit k)‖ < ε :=
        not_not.mp this
      simpa using this
    have hcoeff_le : ‖coeff n f‖ ≤ ε := le_of_lt hcoeff_lt
    simpa [one_pow] using hcoeff_le

/-- Temp.md Lemma 3.3.2 (bivariate): shrinking the radius makes the weighted Gauss bound small for a restricted
series with zero constant term. -/
theorem exists_radius_weightedGaussBound2_of_constantCoeff_eq_zero
    {F : MvPowerSeries (Fin 2) k} (hFT : IsTate k (Fin 2) F)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ WeightedGaussBound2 (k := k) ρ ε F := by
  classical
  -- Coefficients tend to `0`, hence are eventually in the ball of radius `ε`.
  have hball :
      ∀ᶠ e : Fin 2 →₀ ℕ in Filter.cofinite, MvPowerSeries.coeff e F ∈ Metric.ball (0 : k) ε := by
    have hnear : ∀ᶠ x : k in nhds (0 : k), x ∈ Metric.ball (0 : k) ε := by
      change Metric.ball (0 : k) ε ∈ nhds (0 : k)
      exact Metric.ball_mem_nhds (0 : k) hε
    exact hFT.eventually hnear
  have hsmall :
      ∀ᶠ e : Fin 2 →₀ ℕ in Filter.cofinite, ‖MvPowerSeries.coeff e F‖ < ε := by
    refine hball.mono ?_
    intro e he
    simpa [Metric.mem_ball, dist_eq_norm] using he

  -- Let `S` be the set of indices with coefficients of size at least `ε`.
  let S : Set (Fin 2 →₀ ℕ) := {e : Fin 2 →₀ ℕ | ¬ ‖MvPowerSeries.coeff e F‖ < ε}
  have hSfin : S.Finite := (Filter.eventually_cofinite.1 hsmall)
  let sFin : Finset (Fin 2 →₀ ℕ) := hSfin.toFinset

  -- The constant coefficient is `0`, hence not exceptional.
  have h0not : (0 : Fin 2 →₀ ℕ) ∉ sFin := by
    intro h0
    have h0S : (0 : Fin 2 →₀ ℕ) ∈ S := (Set.Finite.mem_toFinset hSfin).1 h0
    have hnot : ¬ ‖MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F‖ < ε := by
      simpa [S] using h0S
    have hlt : ‖MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F‖ < ε := by
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF0, hε]
    exact hnot hlt

  by_cases hs : sFin.Nonempty
  · -- Nonempty exceptional set: choose `ρ = min 1 (ε / A)` where `A` bounds the exceptional coefficients.
    let A : ℝ := sFin.sup' hs (fun e => ‖MvPowerSeries.coeff e F‖)
    have hA_ge : ∀ {e}, e ∈ sFin → ‖MvPowerSeries.coeff e F‖ ≤ A := by
      intro e he
      exact Finset.le_sup' (s := sFin) (f := fun e => ‖MvPowerSeries.coeff e F‖) he
    have hA_pos : 0 < A := by
      rcases hs with ⟨e, he⟩
      have heS : e ∈ S := (Set.Finite.mem_toFinset hSfin).1 he
      have hnot : ¬ ‖MvPowerSeries.coeff e F‖ < ε := by
        simpa [S] using heS
      have hε_le : ε ≤ ‖MvPowerSeries.coeff e F‖ := le_of_not_gt hnot
      have hε_leA : ε ≤ A := le_trans hε_le (hA_ge (e := e) he)
      exact lt_of_lt_of_le hε hε_leA

    let ρ : ℝ := min 1 (ε / A)
    have hρ_pos : 0 < ρ := by
      have hpos : 0 < ε / A := div_pos hε hA_pos
      have : 0 < min (1 : ℝ) (ε / A) := lt_min (by norm_num) hpos
      simpa [ρ] using this
    have hρ_le1 : ρ ≤ 1 := by simp [ρ]
    have hρ_le : ρ ≤ ε / A := by
      simpa [ρ] using (min_le_right (1 : ℝ) (ε / A))
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hmul : A * ρ ≤ ε := by
      have hA0 : 0 ≤ A := le_of_lt hA_pos
      have : A * ρ ≤ A * (ε / A) := mul_le_mul_of_nonneg_left hρ_le hA0
      simpa [mul_div_cancel₀ (a := ε) hA_ne] using this

    refine ⟨ρ, hρ_pos, hρ_le1, ?_⟩
    intro e
    by_cases he : e ∈ sFin
    · have he_ne0 : e ≠ 0 := by
        intro h
        subst h
        exact h0not he
      have hdeg_pos : 0 < e 0 + e 1 := by
        have : e 0 + e 1 ≠ 0 := by
          intro hsum
          have h0 : e 0 = 0 := Nat.eq_zero_of_add_eq_zero_right hsum
          have h1 : e 1 = 0 := Nat.eq_zero_of_add_eq_zero_left hsum
          apply he_ne0
          ext i
          fin_cases i <;> simp [h0, h1]
        exact Nat.pos_of_ne_zero this
      have hpow_le : ρ ^ (e 0 + e 1) ≤ ρ := by
        rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hdeg_pos) with ⟨m, hm⟩
        rw [hm]
        have hρ0 : 0 ≤ ρ := le_of_lt hρ_pos
        have hρm : ρ ^ m ≤ 1 := pow_le_one₀ hρ0 hρ_le1
        simpa [pow_succ] using mul_le_mul_of_nonneg_right hρm hρ0
      have hcoeff_leA : ‖MvPowerSeries.coeff e F‖ ≤ A := hA_ge (e := e) he
      calc
        ‖MvPowerSeries.coeff e F‖ * ρ ^ (e 0 + e 1) ≤ ‖MvPowerSeries.coeff e F‖ * ρ :=
          mul_le_mul_of_nonneg_left hpow_le (norm_nonneg _)
        _ ≤ A * ρ := mul_le_mul_of_nonneg_right hcoeff_leA (le_of_lt hρ_pos)
        _ ≤ ε := hmul
    · have heS : e ∉ S := by
        intro heS
        have : e ∈ sFin := (Set.Finite.mem_toFinset hSfin).2 heS
        exact he this
      have hcoeff_lt : ‖MvPowerSeries.coeff e F‖ < ε := by
        have : ¬ ¬ ‖MvPowerSeries.coeff e F‖ < ε := by
          simpa [S] using heS
        exact not_not.mp this
      have hcoeff_le : ‖MvPowerSeries.coeff e F‖ ≤ ε := le_of_lt hcoeff_lt
      have hρ0 : 0 ≤ ρ := le_of_lt hρ_pos
      have hpow_le1 : ρ ^ (e 0 + e 1) ≤ 1 := pow_le_one₀ hρ0 hρ_le1
      calc
        ‖MvPowerSeries.coeff e F‖ * ρ ^ (e 0 + e 1) ≤ ‖MvPowerSeries.coeff e F‖ * 1 :=
          mul_le_mul_of_nonneg_left hpow_le1 (norm_nonneg _)
        _ ≤ ε := by simpa using hcoeff_le
  · -- Empty exceptional set: take `ρ = 1`.
    have hs_empty : sFin = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
    refine ⟨1, by simp, le_rfl, ?_⟩
    intro e
    have heS : e ∉ S := by
      intro heS
      have : e ∈ sFin := (Set.Finite.mem_toFinset hSfin).2 heS
      simpa [hs_empty] using this
    have hcoeff_lt : ‖MvPowerSeries.coeff e F‖ < ε := by
      have : ¬ ¬ ‖MvPowerSeries.coeff e F‖ < ε := by
        simpa [S] using heS
      exact not_not.mp this
    have hcoeff_le : ‖MvPowerSeries.coeff e F‖ ≤ ε := le_of_lt hcoeff_lt
    have :
        ‖MvPowerSeries.coeff e F‖ * (1 : ℝ) ^ (e 0 + e 1) ≤ ε * (1 : ℝ) ^ (e 0 + e 1) :=
      mul_le_mul_of_nonneg_right hcoeff_le (by positivity)
    simpa [one_pow] using this

/-- Temp.md Lemma 3.3.3: substitution does not increase the weighted Gauss bound, provided the substituted
series stay inside the same closed disc. -/
lemma weightedGaussBound1_one {ρ : ℝ} :
    WeightedGaussBound1 (k := k) ρ (1 : ℝ) (1 : k⟦X⟧) := by
  intro n
  by_cases hn : n = 0
  · subst hn
    simp [WeightedGaussBound1]
  · simp [WeightedGaussBound1, PowerSeries.coeff_one, hn]

lemma weightedGaussBound1_mul {ρ C₁ C₂ : ℝ} (hρ : 0 < ρ) {f g : k⟦X⟧}
    (hf : WeightedGaussBound1 (k := k) ρ C₁ f) (hg : WeightedGaussBound1 (k := k) ρ C₂ g) :
    WeightedGaussBound1 (k := k) ρ (C₁ * C₂) (f * g) := by
  classical
  intro n
  have hρn_pos : 0 < ρ ^ n := pow_pos hρ n
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg (PowerSeries.coeff 0 f)).trans (by simpa using hf 0)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg (PowerSeries.coeff 0 g)).trans (by simpa using hg 0)
  have hC0 : 0 ≤ (C₁ * C₂) / ρ ^ n :=
    div_nonneg (mul_nonneg hC₁0 hC₂0) (le_of_lt hρn_pos)
  -- Coefficient formula for multiplication and ultrametric triangle inequality.
  rw [PowerSeries.coeff_mul]
  have hterm :
      ∀ p ∈ Finset.antidiagonal n,
        ‖coeff p.1 f * coeff p.2 g‖ ≤ (C₁ * C₂) / ρ ^ n := by
    intro p hp
    have hp_add : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hf' : ‖coeff p.1 f‖ ≤ C₁ / ρ ^ p.1 := by
      have hρp_pos : 0 < ρ ^ p.1 := pow_pos hρ p.1
      exact (le_div_iff₀ hρp_pos).2 (by simpa [mul_assoc] using hf p.1)
    have hg' : ‖coeff p.2 g‖ ≤ C₂ / ρ ^ p.2 := by
      have hρp_pos : 0 < ρ ^ p.2 := pow_pos hρ p.2
      exact (le_div_iff₀ hρp_pos).2 (by simpa [mul_assoc] using hg p.2)
    have hC₁_div0 : 0 ≤ C₁ / ρ ^ p.1 := div_nonneg hC₁0 (le_of_lt (pow_pos hρ _))
    have hmul :
        ‖coeff p.1 f * coeff p.2 g‖ ≤ (C₁ / ρ ^ p.1) * (C₂ / ρ ^ p.2) := by
      calc
        ‖coeff p.1 f * coeff p.2 g‖ ≤ ‖coeff p.1 f‖ * ‖coeff p.2 g‖ := norm_mul_le _ _
        _ ≤ (C₁ / ρ ^ p.1) * (C₂ / ρ ^ p.2) :=
          mul_le_mul hf' hg' (norm_nonneg _) hC₁_div0
    -- Simplify the RHS to `(C₁ * C₂) / ρ^n`.
    have hρpow_ne : (ρ ^ p.1) * (ρ ^ p.2) ≠ 0 := by
      have : 0 < (ρ ^ p.1) * (ρ ^ p.2) :=
        mul_pos (pow_pos hρ _) (pow_pos hρ _)
      exact ne_of_gt this
    have hρn_ne : ρ ^ n ≠ 0 := ne_of_gt hρn_pos
    have :
        (C₁ / ρ ^ p.1) * (C₂ / ρ ^ p.2) = (C₁ * C₂) / ρ ^ n := by
      -- Clear denominators using `pow_add` and commutativity.
      -- We work in `ℝ`, so `simp` can handle this.
      -- `hp_add` allows rewriting `ρ^n` as `ρ^(p.1+p.2)`.
      -- Then `pow_add` gives `ρ^(p.1+p.2) = ρ^p.1 * ρ^p.2`.
      calc
        (C₁ / ρ ^ p.1) * (C₂ / ρ ^ p.2)
            = (C₁ * C₂) / ((ρ ^ p.1) * (ρ ^ p.2)) := by
                field_simp [hρpow_ne]
        _ = (C₁ * C₂) / (ρ ^ (p.1 + p.2)) := by
                simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
        _ = (C₁ * C₂) / (ρ ^ n) := by
                simpa [hp_add]
    simpa [this] using hmul
  have hsum :
      ‖∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 g‖ ≤ (C₁ * C₂) / ρ ^ n :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC0 hterm
  -- Multiply by `ρ^n` to obtain the desired bound.
  have :=
      mul_le_mul_of_nonneg_right hsum (le_of_lt hρn_pos)
  -- `(C₁ * C₂) / ρ^n * ρ^n = C₁ * C₂` since `ρ^n ≠ 0`.
  simpa [WeightedGaussBound1, div_eq_mul_inv, hρn_pos.ne'] using this

lemma weightedGaussBound1_pow {ρ C : ℝ} (hρ : 0 < ρ) {f : k⟦X⟧}
    (hf : WeightedGaussBound1 (k := k) ρ C f) :
    ∀ n : ℕ, WeightedGaussBound1 (k := k) ρ (C ^ n) (f ^ n) := by
  classical
  intro n
  induction n with
  | zero =>
      simpa using (weightedGaussBound1_one (k := k) (ρ := ρ))
  | succ n ih =>
      simpa [pow_succ] using
        (weightedGaussBound1_mul (k := k) (ρ := ρ) (C₁ := C ^ n) (C₂ := C) hρ ih hf)

theorem weightedGaussBound1_subst_of_weightedGaussBound2
    {ρ C : ℝ} {F : MvPowerSeries (Fin 2) k} (hF : WeightedGaussBound2 (k := k) ρ C F)
    {p q : k⟦X⟧} (ha : MvPowerSeries.HasSubst (substMap1 p q))
    (hp : WeightedGaussBound1 (k := k) ρ ρ p) (hq : WeightedGaussBound1 (k := k) ρ ρ q) :
    WeightedGaussBound1 (k := k) ρ C (MvPowerSeries.subst (substMap1 p q) F) := by
  classical
  have hC0 : 0 ≤ C := (norm_nonneg (MvPowerSeries.constantCoeff F)).trans (by simpa using hF 0)
  have hρ0 : 0 ≤ ρ := (norm_nonneg (PowerSeries.coeff 0 p)).trans (by simpa using hp 0)
  by_cases hρ : ρ = 0
  · subst hρ
    intro n
    by_cases hn : n = 0
    · subst hn
      -- The constant coefficient is preserved by substitution when `p(0)=q(0)=0`.
      have hp0 : PowerSeries.constantCoeff p = 0 := by
        have : ‖PowerSeries.constantCoeff p‖ ≤ (0 : ℝ) := by simpa using hp 0
        simpa [norm_eq_zero] using le_antisymm this (by positivity : (0 : ℝ) ≤ ‖PowerSeries.constantCoeff p‖)
      have hq0 : PowerSeries.constantCoeff q = 0 := by
        have : ‖PowerSeries.constantCoeff q‖ ≤ (0 : ℝ) := by simpa using hq 0
        simpa [norm_eq_zero] using le_antisymm this (by positivity : (0 : ℝ) ≤ ‖PowerSeries.constantCoeff q‖)
      have hconst :
          PowerSeries.constantCoeff (MvPowerSeries.subst (substMap1 p q) F) =
            MvPowerSeries.constantCoeff F := by
        classical
        have hp0' : MvPowerSeries.constantCoeff p = 0 := by
          simpa using hp0
        have hq0' : MvPowerSeries.constantCoeff q = 0 := by
          simpa using hq0
        have ha0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (substMap1 p q i) = 0 := by
          intro i
          fin_cases i
          · simpa [substMap1] using hp0'
          · simpa [substMap1] using hq0'
        -- Expand the constant coefficient as a `finsum` and observe only `d = 0` contributes.
        change
            MvPowerSeries.constantCoeff (MvPowerSeries.subst (substMap1 p q) F) =
              MvPowerSeries.constantCoeff F
        rw [MvPowerSeries.constantCoeff_subst ha F]
        rw [finsum_eq_single (a := (0 : Fin 2 →₀ ℕ))]
        · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        · intro d hd
          have : MvPowerSeries.constantCoeff (d.prod fun s e => (substMap1 p q s) ^ e) = 0 := by
            classical
            obtain ⟨i, hi⟩ : ∃ i : Fin 2, d i ≠ 0 := by
              by_contra! hc
              exact hd (Finsupp.ext hc)
            simp [map_finsuppProd, Finsupp.prod]
            refine Finset.prod_eq_zero (s := d.support)
              (f := fun j => MvPowerSeries.constantCoeff (substMap1 p q j) ^ d j) (i := i) ?_ ?_
            · simpa [Finsupp.mem_support_iff] using hi
            · simpa [ha0 i, zero_pow hi]
          -- Rewrite first so `simp` doesn't expand the product before using `this`.
          rw [this]
          simp
      -- Now use the bivariate bound at `e=0`.
      simpa [WeightedGaussBound1, hconst] using (hF 0)
    · -- For `n>0`, the left-hand side is `0`.
      have hpow : (0 : ℝ) ^ n = 0 := by
        exact zero_pow (M₀ := ℝ) hn
      simpa [WeightedGaussBound1, hpow] using (show (0 : ℝ) ≤ C from hC0)
  · have hρpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρ)
    intro n
    -- Rewrite the coefficient using the substitution formula (finite `finsum`).
    -- We work with `MvPowerSeries.coeff (Finsupp.single () n)` for uniformity.
    have hρn_pos : 0 < ρ ^ n := pow_pos hρpos n
    -- Coefficient identity.
    have hcoeff :
        coeff n (MvPowerSeries.subst (substMap1 p q) F) =
          finsum (fun d : Fin 2 →₀ ℕ =>
            MvPowerSeries.coeff d F *
              coeff n (d.prod fun s m => (substMap1 p q s) ^ m)) := by
      -- `MvPowerSeries.coeff_subst` specialized to the univariate index `Finsupp.single () n`.
      -- In the univariate case, `coeff n` is the same as `MvPowerSeries.coeff (single () n)`.
      simpa [PowerSeries.coeff, smul_eq_mul] using
        (MvPowerSeries.coeff_subst (a := substMap1 p q) ha (f := F) (e := (Finsupp.single () n)))
    -- Turn the `finsum` into a finite sum and apply the ultrametric bound.
    set g : (Fin 2 →₀ ℕ) → k := fun d =>
      MvPowerSeries.coeff d F * coeff n (d.prod fun s m => (substMap1 p q s) ^ m)
    have hfinite : (Function.support g).Finite := by
      simpa [g, smul_eq_mul] using
        (MvPowerSeries.coeff_subst_finite (a := substMap1 p q) ha (f := F) (e := Finsupp.single () n))
    -- Uniform bound for each term.
    have hterm :
        ∀ d ∈ Function.support g, ‖g d‖ ≤ C / ρ ^ n := by
      intro d hd
      have hd0 : d.prod (fun i m => ρ ^ m) = ρ ^ (d 0 + d 1) := by
        -- `d.prod` over `Fin 2` is the product of the two powers.
        classical
        -- Expand as a product over all indices.
        calc
          d.prod (fun i m => ρ ^ m) = ∏ i : Fin 2, ρ ^ (d i) := by
              simpa using (Finsupp.prod_fintype d (fun i m => ρ ^ m) (fun _ => by simp))
          _ = ρ ^ (d 0) * ρ ^ (d 1) := by simp
          _ = ρ ^ (d 0 + d 1) := by simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
      have hF_d : ‖MvPowerSeries.coeff d F‖ ≤ C / ρ ^ (d 0 + d 1) := by
        have hρd_pos : 0 < ρ ^ (d 0 + d 1) := pow_pos hρpos (d 0 + d 1)
        exact (le_div_iff₀ hρd_pos).2 (by simpa [mul_assoc] using hF d)
      have hprod_bound :
          WeightedGaussBound1 (k := k) ρ (ρ ^ (d 0 + d 1))
            (d.prod fun s m => (substMap1 p q s) ^ m) := by
        -- Reduce to the explicit product `p^(d0) * q^(d1)`.
        have hpPow :
            WeightedGaussBound1 (k := k) ρ (ρ ^ (d 0)) (p ^ (d 0)) := by
          simpa using (weightedGaussBound1_pow (k := k) (ρ := ρ) (C := ρ) hρpos hp (d 0))
        have hqPow :
            WeightedGaussBound1 (k := k) ρ (ρ ^ (d 1)) (q ^ (d 1)) := by
          simpa using (weightedGaussBound1_pow (k := k) (ρ := ρ) (C := ρ) hρpos hq (d 1))
        have hmul :
            WeightedGaussBound1 (k := k) ρ (ρ ^ (d 0) * ρ ^ (d 1)) (p ^ (d 0) * q ^ (d 1)) :=
          weightedGaussBound1_mul (k := k) (ρ := ρ) (C₁ := ρ ^ (d 0)) (C₂ := ρ ^ (d 1)) hρpos hpPow hqPow
        -- Rewrite `d.prod` and the bound.
        simpa [Finsupp.prod_fintype, substMap1, pow_add, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hcoeffProd :
          ‖coeff n (d.prod fun s m => (substMap1 p q s) ^ m)‖ ≤ ρ ^ (d 0 + d 1) / ρ ^ n := by
        have hρn_pos' : 0 < ρ ^ n := pow_pos hρpos n
        exact (le_div_iff₀ hρn_pos').2 (by simpa [mul_assoc] using hprod_bound n)
      have hρn_ne : ρ ^ n ≠ 0 := ne_of_gt hρn_pos
      have hC_div0 : 0 ≤ C / ρ ^ n := div_nonneg hC0 (le_of_lt hρn_pos)
      -- Now bound the term `g d`.
      have : ‖g d‖ ≤ C / ρ ^ n := by
        calc
          ‖g d‖ = ‖MvPowerSeries.coeff d F * coeff n (d.prod fun s m => (substMap1 p q s) ^ m)‖ := by
              simp [g]
          _ ≤ ‖MvPowerSeries.coeff d F‖ * ‖coeff n (d.prod fun s m => (substMap1 p q s) ^ m)‖ :=
              norm_mul_le _ _
          _ ≤ (C / ρ ^ (d 0 + d 1)) * (ρ ^ (d 0 + d 1) / ρ ^ n) := by
              refine mul_le_mul hF_d hcoeffProd (norm_nonneg _) ?_
              exact div_nonneg hC0 (le_of_lt (pow_pos hρpos _))
          _ = (C / ρ ^ n) := by
              -- Simplify using `field_simp`.
              have hρd_ne : ρ ^ (d 0 + d 1) ≠ 0 := ne_of_gt (pow_pos hρpos _)
              field_simp [hρd_ne, hρn_ne, mul_comm, mul_left_comm, mul_assoc]
        -- done
      simpa [Function.mem_support, g] using this
    -- Apply the ultrametric inequality to the finite sum.
    have hsum :
        ‖∑ d ∈ hfinite.toFinset, g d‖ ≤ C / ρ ^ n := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ?_ ?_
      · exact div_nonneg hC0 (le_of_lt hρn_pos)
      · intro d hd
        have : d ∈ Function.support g := by
          simpa [Set.Finite.mem_toFinset] using (Set.Finite.mem_toFinset hfinite).1 hd
        exact hterm d this
    -- Relate back to the coefficient and multiply by `ρ^n`.
    have hcoeff_sum :
        ‖coeff n (MvPowerSeries.subst (substMap1 p q) F)‖ ≤ C / ρ ^ n := by
      -- Rewrite the coefficient using `hcoeff`, then use the bound `hsum`.
      have hcoeff_norm := congrArg (fun x => ‖x‖) hcoeff
      -- The RHS is exactly our `g`.
      have hsum' : ‖finsum g‖ ≤ C / ρ ^ n := by
        -- Rewrite `finsum` as a finite sum over the support.
        simpa [finsum_eq_sum g hfinite] using hsum
      -- Conclude by rewriting the LHS using `hcoeff_norm`.
      exact (le_of_eq (by simpa [g] using hcoeff_norm)).trans hsum'
    have := mul_le_mul_of_nonneg_right hcoeff_sum (le_of_lt hρn_pos)
    simpa [WeightedGaussBound1, div_eq_mul_inv, hρn_pos.ne'] using this

theorem weightedGaussBound_qIter_iterate
    (P Q : TateAlgebra2 k) {c ρ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hcP : GaussBound k c (P : MvPowerSeries (Fin 2) k))
    (hcQ : GaussBound k c (Q : MvPowerSeries (Fin 2) k))
    (hP0 : MvPowerSeries.constantCoeff (P : MvPowerSeries (Fin 2) k) = 0)
    (hQ0 : MvPowerSeries.constantCoeff (Q : MvPowerSeries (Fin 2) k) = 0) :
    ∀ d : ℕ, d > 0 →
      WeightedGaussBound1 (k := k) ρ (c ^ d * ρ)
        (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d) := by
  -- Temp.md Step 1: `‖q_d‖_ρ ≤ c^d ρ` for `0 < ρ ≤ 1`.
  -- The proof uses substitution estimates in the ultrametric setting and induction on `d`.
  sorry

/-- Derivatives do not amplify weighted Gauss bounds when `‖(n : k)‖ = 1` for all `n ≠ 0`. -/
theorem weightedGaussBound1_derivative
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1) {ρ C : ℝ} (hρ : 0 < ρ)
    {f : k⟦X⟧} (hf : WeightedGaussBound1 (k := k) ρ C f) :
    WeightedGaussBound1 (k := k) ρ (C / ρ) (d⁄dX k f) := by
  -- Temp.md §3.1(1): `‖f'‖_ρ ≤ ρ⁻¹ ‖f‖_ρ` (in bound form).
  sorry

/-! #### Weierstrass-type factorizations -/

/-- Formal Weierstrass decomposition: any `f` factors as `X^(order f) * divXPowOrder f`. -/
theorem X_pow_order_mul_divXPowOrder' (f : k⟦X⟧) :
    (X : k⟦X⟧) ^ f.order.toNat * divXPowOrder f = f := by
  simpa using (X_pow_order_mul_divXPowOrder (f := f))

/-- If `f ≠ 0`, then `divXPowOrder f` is a unit (hence plays the role of `u_d` in Temp.md). -/
theorem isUnit_divXPowOrder_of_ne_zero {f : k⟦X⟧} (hf : f ≠ 0) : IsUnit (divXPowOrder f) := by
  simpa using (PowerSeries.isUnit_divided_by_X_pow_order (k := k) hf)

/-- A quantitative unit bound: if `u = 1 + h` with `‖h‖_ρ < 1`, then `u` and `u⁻¹` have Gauss bound `1`. -/
theorem weightedGaussBound1_unit_of_sub_lt_one
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ε < 1) {u : k⟦X⟧}
    (hu0 : PowerSeries.constantCoeff u = 1)
    (hu : WeightedGaussBound1 (k := k) ρ ε (u - 1)) :
    WeightedGaussBound1 (k := k) ρ (1 : ℝ) u ∧
      WeightedGaussBound1 (k := k) ρ (1 : ℝ) u⁻¹ := by
  -- Temp.md §3.3(i): geometric series in the nonarchimedean Gauss norm.
  classical
  have hu' : WeightedGaussBound1 (k := k) ρ (1 : ℝ) u := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [WeightedGaussBound1, hu0]
    · have hcoeff : ‖coeff n u‖ * ρ ^ n ≤ ε := by
        -- For `n>0`, the `n`-th coefficient of `u` equals that of `u-1`.
        simpa [WeightedGaussBound1, PowerSeries.coeff_one, hn] using hu n
      exact hcoeff.trans (le_of_lt hε)
  have huinv' : WeightedGaussBound1 (k := k) ρ (1 : ℝ) u⁻¹ := by
    -- Strong induction on the coefficient index using the recursive formula for inverse coefficients.
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih
    by_cases hn : n = 0
    · subst hn
      -- Base case: the constant coefficient of `u⁻¹` is `(constantCoeff u)⁻¹ = 1`.
      change ‖PowerSeries.coeff 0 u⁻¹‖ * ρ ^ 0 ≤ (1 : ℝ)
      simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv, hu0]
    · have hn0 : n ≠ 0 := hn
      have hρn_pos : 0 < ρ ^ n := pow_pos hρ n
      -- Use the recursive formula for the inverse coefficients.
      have hcoeffInv :
          (coeff n) u⁻¹ =
            -(PowerSeries.constantCoeff u)⁻¹ *
              ∑ x ∈ Finset.antidiagonal n,
                if x.2 < n then coeff x.1 u * coeff x.2 u⁻¹ else 0 := by
        simpa [hn] using (PowerSeries.coeff_inv (n := n) u)
      -- Bound the inner sum.
      have hinner :
          ‖∑ x ∈ Finset.antidiagonal n, if x.2 < n then coeff x.1 u * coeff x.2 u⁻¹ else 0‖ ≤
            ε / ρ ^ n := by
        have hε0 : 0 ≤ ε :=
          (norm_nonneg (PowerSeries.coeff 0 (u - 1))).trans (by simpa using hu 0)
        have hC0 : 0 ≤ ε / ρ ^ n := div_nonneg hε0 (le_of_lt hρn_pos)
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC0 ?_
        intro x hx
        by_cases hx2 : x.2 < n
        · -- Here `x.1 > 0`, so the coefficient of `u` is controlled by `u-1`.
          have hx_add : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
          have hx1_pos : 0 < x.1 := by
            have hx1_eq : x.1 = n - x.2 := Nat.eq_sub_of_add_eq hx_add
            have : 0 < n - x.2 := Nat.sub_pos_of_lt hx2
            simpa [hx1_eq] using this
          have hx1_ne0 : x.1 ≠ 0 := Nat.ne_of_gt hx1_pos
          have hu_x1 :
              ‖coeff x.1 u‖ ≤ ε / ρ ^ x.1 := by
            have hρx1_pos : 0 < ρ ^ x.1 := pow_pos hρ x.1
            exact (le_div_iff₀ hρx1_pos).2 (by
              -- `hu x.1` bounds `coeff x.1 (u-1)`; simplify.
              simpa [WeightedGaussBound1, PowerSeries.coeff_one, hx1_ne0, mul_assoc] using hu x.1)
          have huinv_x2 :
              ‖coeff x.2 u⁻¹‖ ≤ (1 : ℝ) / ρ ^ x.2 := by
            have hρx2_pos : 0 < ρ ^ x.2 := pow_pos hρ x.2
            have hx2_lt : x.2 < n := hx2
            have hx2_bound : ‖coeff x.2 u⁻¹‖ * ρ ^ x.2 ≤ (1 : ℝ) := ih x.2 hx2_lt
            exact (le_div_iff₀ hρx2_pos).2 (by simpa [mul_assoc] using hx2_bound)
          have hmul :
              ‖coeff x.1 u * coeff x.2 u⁻¹‖ ≤ (ε / ρ ^ x.1) * ((1 : ℝ) / ρ ^ x.2) := by
            have hε_div0 : 0 ≤ ε / ρ ^ x.1 := by
              have hε0 : 0 ≤ ε :=
                (norm_nonneg (PowerSeries.coeff 0 (u - 1))).trans (by simpa using hu 0)
              exact div_nonneg hε0 (le_of_lt (pow_pos hρ _))
            calc
              ‖coeff x.1 u * coeff x.2 u⁻¹‖ ≤ ‖coeff x.1 u‖ * ‖coeff x.2 u⁻¹‖ := norm_mul_le _ _
              _ ≤ (ε / ρ ^ x.1) * ((1 : ℝ) / ρ ^ x.2) :=
                mul_le_mul hu_x1 huinv_x2 (norm_nonneg _) hε_div0
          -- Simplify the RHS using `x.1 + x.2 = n`.
          have hρpow_ne : (ρ ^ x.1) * (ρ ^ x.2) ≠ 0 := by
            have : 0 < (ρ ^ x.1) * (ρ ^ x.2) := mul_pos (pow_pos hρ _) (pow_pos hρ _)
            exact ne_of_gt this
          have hdiv :
              (ε / ρ ^ x.1) * ((1 : ℝ) / ρ ^ x.2) = ε / ρ ^ n := by
            calc
              (ε / ρ ^ x.1) * ((1 : ℝ) / ρ ^ x.2) = ε / ((ρ ^ x.1) * (ρ ^ x.2)) := by
                field_simp [hρpow_ne]
              _ = ε / (ρ ^ (x.1 + x.2)) := by
                simp [pow_add]
              _ = ε / (ρ ^ n) := by simpa [hx_add]
          -- Use `hdiv` to reach the desired bound.
          have hmul' : ‖coeff x.1 u * coeff x.2 u⁻¹‖ ≤ ε / ρ ^ n :=
            le_trans hmul (le_of_eq hdiv)
          simpa [hx2] using hmul'
        · -- The term is `0`.
          simpa [hx2] using hC0
      -- Now bound `‖coeff n u⁻¹‖ * ρ^n`.
      have hnorm :
          ‖coeff n u⁻¹‖ * ρ ^ n ≤ ε := by
        have hcoeffEq : ‖coeff n u⁻¹‖ =
            ‖∑ x ∈ Finset.antidiagonal n, if x.2 < n then coeff x.1 u * coeff x.2 u⁻¹ else 0‖ := by
          -- From `hcoeffInv` and `hu0`.
          -- The scalar has norm `1`, and multiplication by `-1` is an isometry.
          -- We keep it simple by `simp`.
          simp [hcoeffInv, hu0]
        -- Multiply the bound on the inner sum by `ρ^n`.
        have hmul :=
            mul_le_mul_of_nonneg_right hinner (le_of_lt hρn_pos)
        have hsum :
            ‖∑ x ∈ Finset.antidiagonal n, if x.2 < n then coeff x.1 u * coeff x.2 u⁻¹ else 0‖ *
                ρ ^ n ≤
              ε := by
          have hρn_ne : (ρ ^ n) ≠ 0 := pow_ne_zero n (ne_of_gt hρ)
          have : (ε / ρ ^ n) * ρ ^ n = ε := by
            field_simp [hρn_ne]
          simpa [this] using hmul
        simpa [hcoeffEq] using hsum
      -- Finally, `ε < 1`.
      exact hnorm.trans (le_of_lt hε)
  exact ⟨hu', huinv'⟩

/-! #### Implicit-function / Weierstrass (degree `1`) -/

/-- A bivariate series depends only on the `X 0` variable (no `X 1`-terms). -/
def IsXOnly (F : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, e 1 ≠ 0 → MvPowerSeries.coeff e F = 0

/-!
`PowerSeries.exists_isWeierstrassFactorization` (used below) requires that the coefficient ring is complete
with respect to its maximal ideal. For `k⟦X⟧` this is true by construction: congruence modulo `(X^n)` is
exactly agreement of the first `n` coefficients.
-/

private lemma mem_span_X_pow_iff_dvd (n : ℕ) (φ : PowerSeries k) :
    φ ∈ (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ n ↔
      (PowerSeries.X : PowerSeries k) ^ n ∣ φ := by
  simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private instance isAdicComplete_span_X : IsAdicComplete
    (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) where
  haus' := by
    intro x hx
    -- Show all coefficients vanish using divisibility by `X^(n+1)` for each `n`.
    apply PowerSeries.ext
    intro n
    have hxmem : x ∈ (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (n + 1) := by
      have : x - 0 ∈
          ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (n + 1) •
            (⊤ : Submodule (PowerSeries k) (PowerSeries k))) :=
        (SModEq.sub_mem).1 (hx (n + 1))
      have : x ∈
          ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (n + 1) •
            (⊤ : Submodule (PowerSeries k) (PowerSeries k))) := by
        simpa using this
      simpa [smul_eq_mul, Ideal.mul_top] using this
    have hxdiv :
        (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ x :=
      (mem_span_X_pow_iff_dvd (k := k) (n := n + 1) x).1 hxmem
    have hcoeff0 :=
      (PowerSeries.X_pow_dvd_iff (n := n + 1) (φ := x)).1 hxdiv
    exact hcoeff0 n (Nat.lt_succ_self n)
  prec' := by
    intro f hf
    classical
    -- Define the limit series by the stabilized coefficients.
    let L : PowerSeries k := PowerSeries.mk (fun n : ℕ => PowerSeries.coeff n (f (n + 1)))
    refine ⟨L, ?_⟩
    intro n
    -- It suffices to show `f n - L ∈ (X)^n`, i.e. `X^n ∣ f n - L`.
    have hXdvd : (PowerSeries.X : PowerSeries k) ^ n ∣ (f n - L) := by
      refine (PowerSeries.X_pow_dvd_iff (n := n) (φ := (f n - L))).2 ?_
      intro m hm
      have hmle : m + 1 ≤ n := Nat.succ_le_of_lt hm
      have hmn :
          f (m + 1) ≡ f n [SMOD
            ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (m + 1) •
              (⊤ : Submodule (PowerSeries k) (PowerSeries k)))] :=
        hf (m := m + 1) (n := n) hmle
      have hdiffmem :
          f (m + 1) - f n ∈ (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (m + 1) := by
        have : f (m + 1) - f n ∈
            ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ (m + 1) •
              (⊤ : Submodule (PowerSeries k) (PowerSeries k))) :=
          (SModEq.sub_mem).1 hmn
        simpa [smul_eq_mul, Ideal.mul_top] using this
      have hdiffdiv :
          (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (f (m + 1) - f n) :=
        (mem_span_X_pow_iff_dvd (k := k) (n := m + 1) (f (m + 1) - f n)).1 hdiffmem
      have hcoeffdiff0 :
          PowerSeries.coeff m (f (m + 1) - f n) = 0 := by
        have hcoeff0 :=
          (PowerSeries.X_pow_dvd_iff (n := m + 1) (φ := f (m + 1) - f n)).1 hdiffdiv
        exact hcoeff0 m (Nat.lt_succ_self m)
      have hcoeff_eq :
          PowerSeries.coeff m (f n) = PowerSeries.coeff m (f (m + 1)) := by
        have : PowerSeries.coeff m (f (m + 1)) - PowerSeries.coeff m (f n) = 0 := by
          simpa using hcoeffdiff0
        exact (sub_eq_zero.mp this).symm
      -- Now compute the `m`-th coefficient of `f n - L`.
      have hcoeffL : PowerSeries.coeff m L = PowerSeries.coeff m (f (m + 1)) := by
        simp [L, PowerSeries.coeff_mk]
      calc
        PowerSeries.coeff m (f n - L)
            = PowerSeries.coeff m (f n) - PowerSeries.coeff m L := by simp
        _ = PowerSeries.coeff m (f n) - PowerSeries.coeff m (f (m + 1)) := by
            simp [hcoeffL]
        _ = 0 := by simp [hcoeff_eq]
    have hmem : f n - L ∈ (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ n := by
      -- Convert divisibility by `X^n` into membership in `(X)^n`.
      have : f n - L ∈ Ideal.span ({(PowerSeries.X : PowerSeries k) ^ n} : Set (PowerSeries k)) :=
        (Ideal.mem_span_singleton).2 hXdvd
      simpa [Ideal.span_singleton_pow] using this
    have hmem' :
        f n - L ∈
          ((Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) ^ n •
            (⊤ : Submodule (PowerSeries k) (PowerSeries k))) := by
      simpa [smul_eq_mul, Ideal.mul_top] using hmem
    exact (SModEq.sub_mem).2 hmem'

-- The maximal ideal of `k⟦X⟧` is generated by `X`, so the previous instance gives the desired one.
private instance isAdicComplete_maximalIdeal_powerSeries :
    IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) := by
  -- `PowerSeries.maximalIdeal_eq_span_X` rewrites the ideal.
  simpa [PowerSeries.maximalIdeal_eq_span_X] using
    (show IsAdicComplete (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k) from
      (by infer_instance :
        IsAdicComplete (Ideal.span ({PowerSeries.X} : Set (PowerSeries k))) (PowerSeries k)))

-- Temp.md Lemma 3.3.5: if `∂K/∂Y (0,0)=1`, then `K(X,Y) = (Y - Φ(X)) * W(X,Y)` with `W(0,0)=1`.
set_option maxHeartbeats 800000 in
theorem exists_implicitFunction_weierstrass_degreeOne
    {K : MvPowerSeries (Fin 2) k}
    (hK0 : MvPowerSeries.constantCoeff K = 0)
    (hKx : MvPowerSeries.coeff (Finsupp.single 0 1) K = 0)
    (hKy : MvPowerSeries.coeff (Finsupp.single 1 1) K = 1) :
    ∃ (Phi W : MvPowerSeries (Fin 2) k),
      IsXOnly (k := k) Phi ∧
        MvPowerSeries.constantCoeff Phi = 0 ∧
          MvPowerSeries.coeff (Finsupp.single 0 1) Phi = 0 ∧
            MvPowerSeries.constantCoeff W = 1 ∧
              K = (MvPowerSeries.X 1 - Phi) * W := by
  -- Nonarchimedean analytic implicit function theorem / Weierstrass division (degree `1` case).
  classical
  -- View `K(X,Y)` as a power series in `Y` with coefficients in `k⟦X⟧`.
  let g : (PowerSeries k)⟦X⟧ :=
    PowerSeries.mk (fun j : ℕ =>
      PowerSeries.mk (fun i : ℕ =>
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) K))
  have hcoeff_g : ∀ i j : ℕ,
      PowerSeries.coeff i (PowerSeries.coeff j g) =
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) K := by
    intro i j
    simp [g]

  -- The `Y`-linear coefficient has constant term `1`, hence is a unit; therefore the reduction of `g`
  -- modulo the maximal ideal is nonzero, so Weierstrass preparation applies.
  have hg_ne :
      (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) ≠ 0 := by
    -- It suffices to show the coefficient of `X^1` is nonzero in the residue field.
    have hunit :
        IsUnit (PowerSeries.coeff 1 g : PowerSeries k) := by
      -- `constantCoeff (coeff 1 g) = coeff (0,1) K = 1`.
      have hconst :
          PowerSeries.constantCoeff (PowerSeries.coeff 1 g : PowerSeries k) = 1 := by
        -- `constantCoeff` is `coeff 0` for univariate series.
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
          (hcoeff_g 0 1).trans (by simpa using hKy)
      -- Use the standard unit criterion for power series.
      exact (PowerSeries.isUnit_iff_constantCoeff).2 (hconst ▸ isUnit_one)
    have hcoeff1 :
        PowerSeries.coeff 1 (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) ≠ 0 := by
      -- Coefficients commute with `map`.
      have :
          PowerSeries.coeff 1 (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) =
            IsLocalRing.residue (PowerSeries k) (PowerSeries.coeff 1 g) := by
        simpa using (PowerSeries.coeff_map (IsLocalRing.residue (PowerSeries k)) 1 g)
      -- The image of a unit is a unit, hence nonzero.
      have hunit' :
          IsUnit (IsLocalRing.residue (PowerSeries k) (PowerSeries.coeff 1 g)) :=
        hunit.map (IsLocalRing.residue (PowerSeries k))
      simpa [this] using hunit'.ne_zero
    -- A power series is nonzero iff some coefficient is nonzero.
    exact
      (PowerSeries.exists_coeff_ne_zero_iff_ne_zero (φ := PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g)).1
        ⟨1, hcoeff1⟩

  -- Apply Weierstrass preparation in the `Y`-variable.
  obtain ⟨f, h, Hwh⟩ :=
    PowerSeries.exists_isWeierstrassFactorization (A := PowerSeries k) (g := g) hg_ne

  -- The reduction of `g` modulo the maximal ideal has order exactly `1`.
  have horder :
      (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g).order = (1 : ℕ) := by
    -- Coefficient `0` vanishes because `K(0,0)=0`, hence `coeff 0 g` lies in the maximal ideal.
    have hcoeff0 :
        PowerSeries.coeff 0 (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) = 0 := by
      have hconst0 :
          PowerSeries.constantCoeff (PowerSeries.coeff 0 g : PowerSeries k) = 0 := by
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
          (hcoeff_g 0 0).trans (by simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using hK0)
      -- `coeff 0 g ∈ maximalIdeal` because it is divisible by `X`.
      have hmem :
          (PowerSeries.coeff 0 g : PowerSeries k) ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
        -- Use `maximalIdeal_eq_span_X` and the divisibility criterion `X_dvd_iff`.
        have hXdvd : (PowerSeries.X : PowerSeries k) ∣ (PowerSeries.coeff 0 g : PowerSeries k) := by
          -- `X ∣ φ` iff `constantCoeff φ = 0`.
          simpa [PowerSeries.X_dvd_iff] using hconst0
        -- Membership in `Ideal.span {X}`.
        have hspan : (PowerSeries.coeff 0 g : PowerSeries k) ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries k)) := by
          simpa [Ideal.mem_span_singleton] using hXdvd
        simpa [PowerSeries.maximalIdeal_eq_span_X] using hspan
      -- Now `residue` of an element in the maximal ideal is `0`.
      have hres0 :
          IsLocalRing.residue (PowerSeries k) (PowerSeries.coeff 0 g) = 0 := by
        exact (IsLocalRing.residue_eq_zero_iff (R := PowerSeries k) (x := PowerSeries.coeff 0 g)).2 hmem
      -- Translate to the coefficient statement.
      -- We avoid `simpa` here, since it would also simplify the goal using
      -- `IsLocalRing.residue_eq_zero_iff` into a nonunit statement.
      rw [PowerSeries.coeff_map (IsLocalRing.residue (PowerSeries k)) 0 g]
      exact hres0

    -- Coefficient `1` is nonzero, as in the proof of `hg_ne`.
    have hcoeff1 :
        PowerSeries.coeff 1 (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) ≠ 0 := by
      have hunit :
          IsUnit (PowerSeries.coeff 1 g : PowerSeries k) := by
        have hconst :
            PowerSeries.constantCoeff (PowerSeries.coeff 1 g : PowerSeries k) = 1 := by
          simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
            (hcoeff_g 0 1).trans (by simpa using hKy)
        exact (PowerSeries.isUnit_iff_constantCoeff).2 (hconst ▸ isUnit_one)
      have :
          PowerSeries.coeff 1 (PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) =
            IsLocalRing.residue (PowerSeries k) (PowerSeries.coeff 1 g) := by
        simpa using (PowerSeries.coeff_map (IsLocalRing.residue (PowerSeries k)) 1 g)
      have hunit' :
          IsUnit (IsLocalRing.residue (PowerSeries k) (PowerSeries.coeff 1 g)) :=
        hunit.map (IsLocalRing.residue (PowerSeries k))
      simpa [this] using hunit'.ne_zero

    -- Characterize the order using `order_eq_nat`.
    refine (PowerSeries.order_eq_nat (φ := PowerSeries.map (IsLocalRing.residue (PowerSeries k)) g) (n := 1)).2 ?_
    refine ⟨hcoeff1, ?_⟩
    intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simpa using hcoeff0

  -- Hence the distinguished polynomial has degree `1`, so it is `X + C b`.
  have hf_nat : f.natDegree = 1 := by
    -- `natDegree f = order(map residue g).toNat`.
    have := PowerSeries.IsWeierstrassFactorization.natDegree_eq_toNat_order_map (H := Hwh)
    simpa [horder] using this
  have hfX : f = Polynomial.X + Polynomial.C (f.coeff 0) := by
    -- `f` is monic since it is distinguished.
    exact Hwh.isDistinguishedAt.monic.eq_X_add_C hf_nat

  -- Put `g` in the form `(Y - Φ) * W` where `Φ` only depends on `X`.
  let b : PowerSeries k := f.coeff 0
  let Phi : MvPowerSeries (Fin 2) k :=
    fun e : Fin 2 →₀ ℕ => if e 1 = 0 then -PowerSeries.coeff (e 0) b else 0
  let W : MvPowerSeries (Fin 2) k :=
    fun e : Fin 2 →₀ ℕ => PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) h)

  have hPhi_xOnly : IsXOnly (k := k) Phi := by
    intro e he1
    simpa [MvPowerSeries.coeff_apply, Phi, he1]

  -- Main identity `K = (Y - Φ) * W`, proved coefficientwise using the Weierstrass factorization of `g`.
  have hKW : K = (MvPowerSeries.X 1 - Phi) * W := by
    -- `MvPowerSeries` is just a function type; ext on coefficients.
    ext e
    -- Decompose multi-index `e` into its two coordinates.
    have he :
        e = Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single 1 (e 1) := by
      ext t <;> fin_cases t <;> simp
    -- Rewrite the coefficient of `K` via the definition of `g`.
    have hK_as_g :
        MvPowerSeries.coeff e K = PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) g) := by
      -- Use `he` to rewrite `e` as `single 0 i + single 1 j`.
      have : MvPowerSeries.coeff e K =
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single 1 (e 1)) K := by
        exact congrArg (fun d => MvPowerSeries.coeff d K) he
      -- Now use `hcoeff_g`.
      exact this.trans (hcoeff_g (e 0) (e 1)).symm

    -- Rewrite `g` using the Weierstrass factorization with `f = X + C b`.
    have hg_fac :
        g = (PowerSeries.X + PowerSeries.C b) * h := by
      -- `g = f * h` and `f = X + C b`.
      -- Coercions from polynomials to power series are handled by `simp`.
      -- Avoid `simp` here (it can hit the recursion-depth limit); rewrite step-by-step.
      calc
        g = (f : (PowerSeries k)⟦X⟧) * h := by
            simpa [Hwh.eq_mul]
        _ = ((Polynomial.X + Polynomial.C b : Polynomial (PowerSeries k)) : (PowerSeries k)⟦X⟧) * h := by
            -- Rewrite `f` and unfold `b` without `simp` (avoids recursion-depth issues).
            -- `Hwh.eq_mul` gives `g = f * h` where `f` is coerced to a power series.
            -- Here we only need to rewrite that polynomial factor.
            rw [hfX]
            -- `b` was defined as `f.coeff 0`.
            -- (No further work needed: the goal is definitional after rewriting.)
        _ = (PowerSeries.X + PowerSeries.C b) * h := by
            -- simplify the polynomial coercions
            simp [Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]

    -- It suffices to compare coefficients of both sides.
    -- We compute the coefficient of `(e 0, e 1)` in the RHS explicitly.
    -- First, compute the `Y`-shift term coming from `X 1 * W`.
    have hcoeff_X1W :
        MvPowerSeries.coeff e (MvPowerSeries.X 1 * W) =
          if (e 1 = 0) then 0 else PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1 - 1) h) := by
      -- Use the monomial multiplication formula for `X 1`.
      -- `X 1 = monomial (single 1 1) 1`.
      by_cases hj : e 1 = 0
      ·
        -- Not enough `Y`-degree, so the coefficient is `0`.
        have hle : ¬ (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≤ e := by
          intro hle
          have : (1 : ℕ) ≤ e 1 := by simpa using hle 1
          -- rewrite using `hj : e 1 = 0` to get `1 ≤ 0`, contradiction.
          have : (1 : ℕ) ≤ 0 := by simpa [hj] using this
          exact (Nat.not_succ_le_zero 0) this
        simp [MvPowerSeries.X, W, MvPowerSeries.coeff_monomial_mul, hle, hj]
      · -- `e 1 ≥ 1`, so the shift contributes.
        have hle : (Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≤ e := by
          intro t
          fin_cases t
          · simp
          · have : 1 ≤ e 1 := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hj)
            simpa using this
        have hsub :
            e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ) =
              Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single 1 (e 1 - 1) := by
          ext t <;> fin_cases t <;> simp [Finsupp.tsub_apply]
        -- Apply the formula.
        -- First rewrite the index `e - single 1 1` to a clean `single 0 + single 1` form, then unfold `W`.
        rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul, if_pos hle]
        -- `1` is the coefficient of `X 1`, so it disappears.
        simp [hsub, W, MvPowerSeries.coeff_apply, hj]

    -- Next, compute the `X`-convolution term coming from `Phi * W`.
    have hcoeff_PhiW :
        MvPowerSeries.coeff e (Phi * W) =
          -PowerSeries.coeff (e 0) (b * PowerSeries.coeff (e 1) h) := by
      -- Expand the coefficient using `MvPowerSeries.coeff_mul` and reindex the finite sum.
      -- Only pairs with `Y`-degree `0` on the left contribute, since `Phi` is `X`-only.
      set i : ℕ := e 0
      set j : ℕ := e 1
      -- Rewrite `e` as `single 0 i + single 1 j`.
      have he' :
          e = Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j := by
        simpa [i, j] using he
      -- Start from the coefficient formula.
      have hmul :
          MvPowerSeries.coeff e (Phi * W) =
            ∑ p ∈ Finset.antidiagonal e, MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W := by
        -- `coeff_mul` for multivariate series.
        simpa using (MvPowerSeries.coeff_mul (φ := Phi) (ψ := W) (n := e))
      -- Filter to the pairs where the left `Y`-exponent is `0`.
      have hfilter :
          (∑ p ∈ Finset.antidiagonal e, MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W) =
            ∑ p ∈ (Finset.antidiagonal e).filter (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => p.1 1 = 0),
              MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W := by
        classical
        -- If `p.1 1 ≠ 0`, then `coeff p.1 Phi = 0`, so the summand is `0`.
        have hne :
            ∀ p ∈ Finset.antidiagonal e,
              (MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W ≠ 0 →
                (p.1 1 = 0)) := by
          intro p hp hpnz
          by_contra hbad
          have hPhi0 : MvPowerSeries.coeff p.1 Phi = 0 := hPhi_xOnly p.1 hbad
          exact hpnz (by simp [hPhi0])
        -- Apply `sum_filter_of_ne`.
        simpa using (Finset.sum_filter_of_ne hne).symm

      -- Reindex the filtered sum by the ordinary antidiagonal of `i`.
      have hreindex :
          (∑ p ∈ (Finset.antidiagonal e).filter (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => p.1 1 = 0),
              MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W) =
            ∑ q ∈ Finset.antidiagonal i,
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W := by
        classical
        -- Bijection between decompositions in `x` and the filtered antidiagonal in `Fin 2 →₀ ℕ`.
        -- We use `Finset.sum_bij` with domain `t = filtered antidiagonal` and codomain `s = antidiagonal i`.
        -- This produces `∑_{p∈t} ... = ∑_{q∈s} ...`, exactly our goal.
        refine (Finset.sum_bij
          (s := (Finset.antidiagonal e).filter (fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => p.1 1 = 0))
          (t := Finset.antidiagonal i)
          (f := fun p => MvPowerSeries.coeff p.1 Phi * MvPowerSeries.coeff p.2 W)
          (g := fun q =>
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W)
          (i := fun p hp => (p.1 0, p.2 0)) ?_ ?_ ?_ ?_)
        · -- image membership in `antidiagonal i`
          intro p hp
          have hpanti : p ∈ Finset.antidiagonal e := (Finset.mem_filter.mp hp).1
          have hp_add : p.1 + p.2 = e := Finset.mem_antidiagonal.mp hpanti
          have h0 : (p.1 0) + (p.2 0) = e 0 := by
            have := congrArg (fun q : Fin 2 →₀ ℕ => q 0) hp_add
            simpa [Finsupp.add_apply] using this
          have he0 : e 0 = i := by
            have := congrArg (fun q : Fin 2 →₀ ℕ => q 0) he'
            simpa [Finsupp.add_apply] using this
          exact Finset.mem_antidiagonal.mpr (h0.trans he0)
        · -- injectivity
          intro p₁ hp₁ p₂ hp₂ h
          -- ext on both components using the `0`-coordinate and `hp₁, hp₂` to control the `1`-coordinate
          have h0 : p₁.1 0 = p₂.1 0 := congrArg Prod.fst h
          have h1 : p₁.2 0 = p₂.2 0 := congrArg Prod.snd h
          -- show p₁ = p₂ by ext on `Fin 2`
          apply Prod.ext <;> ext t <;> fin_cases t
          · simpa using h0
          ·
            -- from membership in filtered antidiagonal we get `p.1 1 = 0`, hence `p₁.1 1 = p₂.1 1 = 0`
            have hp1y₁ : p₁.1 1 = 0 := (Finset.mem_filter.mp hp₁).2
            have hp1y₂ : p₂.1 1 = 0 := (Finset.mem_filter.mp hp₂).2
            simpa [hp1y₁, hp1y₂]
          · simpa using h1
          ·
            -- for the second component, use `p.2 1 = j` coming from antidiagonal relation and `p.1 1 = 0`
            have hp1y₁ : p₁.1 1 = 0 := (Finset.mem_filter.mp hp₁).2
            have hp1y₂ : p₂.1 1 = 0 := (Finset.mem_filter.mp hp₂).2
            have hp2y₁ : p₁.2 1 = j := by
              have hpanti : p₁ ∈ Finset.antidiagonal e := (Finset.mem_filter.mp hp₁).1
              have hp_add : p₁.1 + p₁.2 = e := Finset.mem_antidiagonal.mp hpanti
              have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q 1) hp_add
              have h1' : p₁.1 1 + p₁.2 1 = e 1 := by
                simpa [Finsupp.add_apply] using h1
              have hp2y₁' : p₁.2 1 = e 1 := by
                simpa [hp1y₁] using h1'
              have he1 : e 1 = j := by
                have := congrArg (fun q : Fin 2 →₀ ℕ => q 1) he'
                simpa [Finsupp.add_apply] using this
              exact hp2y₁'.trans he1
            have hp2y₂ : p₂.2 1 = j := by
              have hpanti : p₂ ∈ Finset.antidiagonal e := (Finset.mem_filter.mp hp₂).1
              have hp_add : p₂.1 + p₂.2 = e := Finset.mem_antidiagonal.mp hpanti
              have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q 1) hp_add
              have h1' : p₂.1 1 + p₂.2 1 = e 1 := by
                simpa [Finsupp.add_apply] using h1
              have hp2y₂' : p₂.2 1 = e 1 := by
                simpa [hp1y₂] using h1'
              have he1 : e 1 = j := by
                have := congrArg (fun q : Fin 2 →₀ ℕ => q 1) he'
                simpa [Finsupp.add_apply] using this
              exact hp2y₂'.trans he1
            simpa [hp2y₁, hp2y₂]
        · -- surjectivity onto `antidiagonal i`
          intro q hq
          -- build the corresponding pair in the filtered antidiagonal
          have hq_add : q.1 + q.2 = i := Finset.mem_antidiagonal.mp hq
          refine ⟨(Finsupp.single (0 : Fin 2) q.1, Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j), ?_, ?_⟩
          · -- membership
            have hp_add :
                (Finsupp.single (0 : Fin 2) q.1 + (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j)) =
                  Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j := by
              ext t <;> fin_cases t <;> simp [hq_add, add_assoc, add_left_comm, add_comm]
            -- membership in the filtered antidiagonal
            refine Finset.mem_filter.2 ?_
            refine ⟨?_, ?_⟩
            · -- antidiagonal condition
              refine Finset.mem_antidiagonal.2 ?_
              -- use `hp_add` and rewrite `e` via `he'`
              simpa [he', add_assoc] using hp_add
            · -- filter condition: the first component has `Y`-degree `0`
              simp
          · -- mapping sends it back to `q`
            simp
        · -- summand compatibility
          intro p hp
          have hpanti : p ∈ Finset.antidiagonal e := (Finset.mem_filter.mp hp).1
          have hp_add : p.1 + p.2 = e := Finset.mem_antidiagonal.mp hpanti
          have hp1y : p.1 1 = 0 := (Finset.mem_filter.mp hp).2
          have hp2y : p.2 1 = j := by
            have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q 1) hp_add
            have h1' : p.1 1 + p.2 1 = e 1 := by
              simpa [Finsupp.add_apply] using h1
            have hp2y' : p.2 1 = e 1 := by
              simpa [hp1y] using h1'
            have he1 : e 1 = j := by
              have := congrArg (fun q : Fin 2 →₀ ℕ => q 1) he'
              simpa [Finsupp.add_apply] using this
            exact hp2y'.trans he1
          have hp1 : p.1 = Finsupp.single (0 : Fin 2) (p.1 0) := by
            ext t <;> fin_cases t <;> simp [hp1y]
          have hp2 : p.2 = Finsupp.single (0 : Fin 2) (p.2 0) + Finsupp.single 1 j := by
            ext t <;> fin_cases t <;> simp [hp2y]
          -- Rewrite both indices using the `Y`-degree facts and conclude by reflexivity.
          -- Work with the evaluation form of coefficients.
          simp [MvPowerSeries.coeff_apply]
          have hPhi' : Phi p.1 = Phi (Finsupp.single (0 : Fin 2) (p.1 0)) := by
            simpa using congrArg Phi hp1
          have hW' : W p.2 = W (Finsupp.single (0 : Fin 2) (p.2 0) + Finsupp.single 1 j) := by
            simpa using congrArg W hp2
          rw [hPhi', hW']
          -- goal is now definally true

      -- Finish: substitute the reindexed expression and simplify to the univariate coefficient formula.
      have hsum' :
          MvPowerSeries.coeff e (Phi * W) =
            ∑ q ∈ Finset.antidiagonal i,
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W := by
        simpa [hmul, hfilter, hreindex] using hmul
      -- Evaluate the coefficients of `Phi` and `W`.
      -- `Phi` is the embedding of `-b`, hence `coeff (single 0 a) Phi = -coeff a b`.
      -- `W` records the coefficients of `h`.
      -- Rewrite the RHS sum as `- coeff i (b * coeff j h)` using `PowerSeries.coeff_mul`.
      -- First, simplify the summand.
      have hsimp :
          (∑ q ∈ Finset.antidiagonal i,
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W) =
            -∑ q ∈ Finset.antidiagonal i,
              PowerSeries.coeff q.1 b * PowerSeries.coeff q.2 (PowerSeries.coeff j h) := by
        -- Push the minus sign out.
        classical
        -- `simp` on coefficients of `Phi` and `W`.
        have : ∀ q : ℕ × ℕ,
            MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W =
                -(PowerSeries.coeff q.1 b * PowerSeries.coeff q.2 (PowerSeries.coeff j h)) := by
          intro q
          -- Coefficients of `Phi` and `W` by definition.
          have hPhi :
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi = -PowerSeries.coeff q.1 b := by
            -- Here the `Y`-degree is `0`.
            simpa [MvPowerSeries.coeff_apply, Phi]
          have hW :
              MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W =
                PowerSeries.coeff q.2 (PowerSeries.coeff j h) := by
            simpa [MvPowerSeries.coeff_apply, W]
          simp [hPhi, hW, mul_assoc, mul_left_comm, mul_comm]
        -- Sum the pointwise identity.
        simpa [Finset.sum_congr rfl (fun q hq => this q)] using (by
          -- Replace each term and factor `-` outside using distributivity.
          simp)
      -- Now relate to the univariate product coefficient.
      have hmul_univ :
          ∑ q ∈ Finset.antidiagonal i,
              PowerSeries.coeff q.1 b * PowerSeries.coeff q.2 (PowerSeries.coeff j h) =
            PowerSeries.coeff i (b * PowerSeries.coeff j h) := by
        -- This is exactly the coefficient formula for multiplication in `PowerSeries k`.
        simpa [PowerSeries.coeff_mul] using (rfl : (PowerSeries.coeff i (b * PowerSeries.coeff j h) =
          ∑ q ∈ Finset.antidiagonal i, PowerSeries.coeff q.1 b * PowerSeries.coeff q.2 (PowerSeries.coeff j h)))
      -- Combine everything.
      have : MvPowerSeries.coeff e (Phi * W) = -PowerSeries.coeff i (b * PowerSeries.coeff j h) := by
        -- Use `hsum'` and simplify.
        -- This block is intentionally verbose to help later refactoring.
        calc
          MvPowerSeries.coeff e (Phi * W)
              = ∑ q ∈ Finset.antidiagonal i,
                  MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.1) Phi *
                    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) q.2 + Finsupp.single 1 j) W := by
                    simpa [i, j] using hsum'
          _ = -∑ q ∈ Finset.antidiagonal i,
                PowerSeries.coeff q.1 b * PowerSeries.coeff q.2 (PowerSeries.coeff j h) := by
                simpa [i, j] using hsimp
          _ = -PowerSeries.coeff i (b * PowerSeries.coeff j h) := by
                simpa [hmul_univ]
      simpa [i, j] using this

    -- Compute the coefficient of the RHS and match it with the coefficient of `g`.
    have hRHS :
        MvPowerSeries.coeff e ((MvPowerSeries.X 1 - Phi) * W) =
          PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) g) := by
      -- Expand `(X 1 - Phi) * W = X 1 * W - Phi * W` and use the computations above.
      have :
          MvPowerSeries.coeff e ((MvPowerSeries.X 1 - Phi) * W) =
            MvPowerSeries.coeff e (MvPowerSeries.X 1 * W) - MvPowerSeries.coeff e (Phi * W) := by
        -- `coeff` is a ring hom, so it respects `mul` and `sub`.
        -- Use distributivity and linearity of `MvPowerSeries.coeff`.
        simp [sub_mul]
      -- Rewrite the RHS using `hg_fac` and the corresponding univariate coefficient computation.
      -- We compute `coeff (e 0) (coeff (e 1) g)` from `hg_fac`.
      have hcoeffg :
          PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) g) =
            PowerSeries.coeff (e 0) (b * PowerSeries.coeff (e 1) h) +
              (if e 1 = 0 then 0 else PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1 - 1) h)) := by
        -- Use `hg_fac` and compute coefficients in the outer variable.
        have hg' :
            PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) g) =
              PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) ((PowerSeries.X + PowerSeries.C b) * h)) := by
          simpa [hg_fac] using
            congrArg (fun φ : PowerSeries k => PowerSeries.coeff (e 0) φ)
              (show PowerSeries.coeff (e 1) g =
                    PowerSeries.coeff (e 1) ((PowerSeries.X + PowerSeries.C b) * h) from by
                  simpa [hg_fac])
        -- Expand `(X + C b) * h` and split into the `X * h` shift term and the `C b * h` term.
        -- We keep the inner-variable multiplication `b * coeff _ h` unevaluated.
        by_cases hj : e 1 = 0
        · -- `e 1 = 0`: the shift term vanishes.
          -- `coeff 0` of `X * h` is `0`, and `coeff 0` of `C b * h` is `b * coeff 0 h`.
          have hcoeff0 :
              PowerSeries.coeff 0 ((PowerSeries.X + PowerSeries.C b) * h) =
                b * PowerSeries.coeff 0 h := by
            simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm,
              PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul]
          have hcoeff0' :
              PowerSeries.coeff (e 0) (PowerSeries.coeff 0 ((PowerSeries.X + PowerSeries.C b) * h)) =
                PowerSeries.coeff (e 0) (b * PowerSeries.coeff 0 h) :=
            congrArg (fun φ : PowerSeries k => PowerSeries.coeff (e 0) φ) hcoeff0
          have hg0 :
              PowerSeries.coeff (e 0) (PowerSeries.coeff 0 g) =
                PowerSeries.coeff (e 0) (PowerSeries.coeff 0 ((PowerSeries.X + PowerSeries.C b) * h)) := by
            simpa [hj] using hg'
          have : PowerSeries.coeff (e 0) (PowerSeries.coeff 0 g) =
              PowerSeries.coeff (e 0) (b * PowerSeries.coeff 0 h) :=
            hg0.trans hcoeff0'
          simpa [hj] using this
        · -- `e 1 ≠ 0`: use the successor formula.
          rcases Nat.exists_eq_succ_of_ne_zero hj with ⟨n, hn⟩
          -- rewrite `e 1` using `hn`
          have hshift : PowerSeries.coeff (e 1) (PowerSeries.X * h) = PowerSeries.coeff (e 1 - 1) h := by
            -- rewrite to the `succ` case
            -- `simp` turns `(n.succ - 1)` into `n`.
            simpa [hn] using (PowerSeries.coeff_succ_X_mul (n := n) (φ := h))
          -- Now simplify the coefficient computation.
          -- The `if` is in the "else" branch since `hj`.
          -- We also need `hn` to rewrite `e 1 - 1` to `n`.
          have hn' : e 1 - 1 = n := by
            -- `hn : e 1 = n.succ`
            simpa [hn] using rfl
          -- Finish by rewriting and simplifying.
          -- `coeff (n+1)` of `(X + C b) * h` is `coeff n h + b * coeff (n+1) h`.
          -- Applying `coeff (e 0)` gives the desired formula.
          -- We avoid `simp` loops by being explicit.
          have : PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) ((PowerSeries.X + PowerSeries.C b) * h)) =
              PowerSeries.coeff (e 0) (b * PowerSeries.coeff (e 1) h) +
                PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1 - 1) h) := by
            -- Expand and use `hshift` and `coeff_C_mul`.
            -- First compute the outer coefficient.
            -- `(X + C b) * h = X * h + C b * h`.
            -- Then take `coeff (e 1)`.
            -- Finally take `coeff (e 0)` in the coefficient ring.
            simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, hshift,
              PowerSeries.coeff_C_mul, hn, hj]
          -- Combine with `hg'` and the `if` simplification.
          -- `hj` ensures the `if` is in the else branch.
          simpa [hg', hj, this, add_assoc, add_left_comm, add_comm]
      -- Now compare with `hcoeff_X1W` and `hcoeff_PhiW`.
      -- Note that `hcoeff_PhiW` already includes a minus sign.
      calc
        MvPowerSeries.coeff e ((MvPowerSeries.X 1 - Phi) * W)
            = MvPowerSeries.coeff e (MvPowerSeries.X 1 * W) - MvPowerSeries.coeff e (Phi * W) := this
        _ = (if e 1 = 0 then 0 else PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1 - 1) h))
              - (-PowerSeries.coeff (e 0) (b * PowerSeries.coeff (e 1) h)) := by
                simp [hcoeff_X1W, hcoeff_PhiW]
        _ = PowerSeries.coeff (e 0) (b * PowerSeries.coeff (e 1) h) +
              (if e 1 = 0 then 0 else PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1 - 1) h)) := by
                ring
        _ = PowerSeries.coeff (e 0) (PowerSeries.coeff (e 1) g) := by
                simpa [hcoeffg, add_comm, add_left_comm, add_assoc]

    -- Combine the two representations.
    simpa [hK_as_g] using hRHS.symm

  -- Deduce the constant-term and `X`-linear-term conditions from the coefficient assumptions on `K`.
  have hW0 : MvPowerSeries.constantCoeff W = 1 := by
    -- Take the `(0,1)` coefficient in the identity `hKW`.
    have hconstW_ne : MvPowerSeries.constantCoeff W ≠ 0 := by
      -- `W` comes from a unit `h`, hence its constant coefficient is nonzero.
      have hu : IsUnit h := Hwh.isUnit
      have hu0 : IsUnit (PowerSeries.constantCoeff h : PowerSeries k) :=
        (PowerSeries.isUnit_iff_constantCoeff).1 hu
      have hWconst :
          MvPowerSeries.constantCoeff W =
            PowerSeries.constantCoeff (PowerSeries.constantCoeff h : PowerSeries k) := by
        -- Rewrite both sides as `(0,0)` coefficients of `h`.
        rw [(MvPowerSeries.coeff_zero_eq_constantCoeff_apply (φ := W)).symm]
        rw [(PowerSeries.coeff_zero_eq_constantCoeff_apply (φ := (PowerSeries.constantCoeff h : PowerSeries k))).symm]
        rw [(PowerSeries.coeff_zero_eq_constantCoeff_apply (φ := h)).symm]
        rfl
      have hconst :
          (PowerSeries.constantCoeff (PowerSeries.constantCoeff h : PowerSeries k)) ≠ 0 := by
        -- In a field, units are nonzero.
        have :
            IsUnit (PowerSeries.constantCoeff (PowerSeries.constantCoeff h : PowerSeries k)) :=
          (PowerSeries.isUnit_iff_constantCoeff).1 hu0
        exact this.ne_zero
      simpa [hWconst] using hconst
    -- Now compute the `(0,1)` coefficient of `K = (X 1 - Phi) * W`.
    have h01 :
        MvPowerSeries.coeff (Finsupp.single 1 1) K =
          MvPowerSeries.coeff (Finsupp.single 1 1) ((MvPowerSeries.X 1 - Phi) * W) := by
      simpa [hKW]
    -- Expand the RHS coefficient: since `constantCoeff Phi = 0` (proved next), only `X 1` contributes.
    -- We get `coeff (0,1) = constantCoeff W`.
    -- This step is kept simple by `simp` using the explicit definition of `Phi`.
    -- First show `constantCoeff Phi = 0` from the `(0,0)` coefficient and `hconstW_ne`.
    have hPhi0 : MvPowerSeries.constantCoeff Phi = 0 := by
      have h00 :
          MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) K =
            MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) ((MvPowerSeries.X 1 - Phi) * W) := by
        simpa [hKW]
      -- `coeff 0 K = 0`.
      have h00K : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) K = 0 := by
        simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using hK0
      -- Compute the constant coefficient of the RHS.
      -- Constant coefficient of `X 1` is `0`, so it is `-(constantCoeff Phi) * constantCoeff W`.
      have h00R :
          MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) ((MvPowerSeries.X 1 - Phi) * W) =
            -(MvPowerSeries.constantCoeff Phi) * MvPowerSeries.constantCoeff W := by
        -- Constant term computation, abstracted to avoid unfolding the (large) `Phi`.
        have coeff0_mul_sub (Φ Ω : MvPowerSeries (Fin 2) k) :
            MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) ((MvPowerSeries.X 1 - Φ) * Ω) =
              -(MvPowerSeries.constantCoeff Φ) * MvPowerSeries.constantCoeff Ω := by
          classical
          simp [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.constantCoeff_X]
        simpa using coeff0_mul_sub Phi W
      -- Solve for `constantCoeff Phi`.
      -- From `0 = -Phi₀ * W₀` and `W₀ ≠ 0`, deduce `Phi₀ = 0`.
      have hneg : -(MvPowerSeries.constantCoeff Phi) * MvPowerSeries.constantCoeff W = 0 := by
        -- Use `h00K` to rewrite the LHS and then compare with the RHS.
        have : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) ((MvPowerSeries.X 1 - Phi) * W) = 0 := by
          exact h00.symm.trans h00K
        -- Rewrite using `h00R`.
        simpa [h00R] using this
      -- Cancel `constantCoeff W`.
      have hcancel : MvPowerSeries.constantCoeff Phi = 0 := by
        have hneg' :
            -(MvPowerSeries.constantCoeff Phi * MvPowerSeries.constantCoeff W) = 0 := by
          simpa [neg_mul] using hneg
        have hmul : MvPowerSeries.constantCoeff Phi * MvPowerSeries.constantCoeff W = 0 :=
          (neg_eq_zero.mp hneg')
        exact (mul_eq_zero.mp hmul).resolve_right hconstW_ne
      simpa using hcancel
    -- Now compute the `(0,1)` coefficient.
    have h01R :
        MvPowerSeries.coeff (Finsupp.single 1 1) ((MvPowerSeries.X 1 - Phi) * W) =
          MvPowerSeries.constantCoeff W := by
      classical
      have hPhi_y1 : MvPowerSeries.coeff (Finsupp.single 1 1) Phi = 0 := by
        refine hPhi_xOnly (Finsupp.single 1 1) ?_
        simp
      -- Compute the `(0,1)` coefficient without unfolding `Phi`.
      have coeff_e01_mul_sub_eq_const (Φ Ω : MvPowerSeries (Fin 2) k)
          (hΦ0 : MvPowerSeries.constantCoeff Φ = 0)
          (hΦe01 : MvPowerSeries.coeff (Finsupp.single 1 1) Φ = 0) :
          MvPowerSeries.coeff (Finsupp.single 1 1) ((MvPowerSeries.X 1 - Φ) * Ω) =
            MvPowerSeries.constantCoeff Ω := by
        classical
        let e01 : Fin 2 →₀ ℕ := Finsupp.single 1 1
        have hantiNat : Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
          decide
        have hantiF : Finset.antidiagonal e01 =
            ({((0 : Fin 2 →₀ ℕ), e01), (e01, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
          ext p
          simp [e01, Finsupp.antidiagonal_single, hantiNat]
        rw [show (Finsupp.single 1 1 : Fin 2 →₀ ℕ) = e01 by rfl]
        rw [MvPowerSeries.coeff_mul]
        rw [hantiF]
        have hne0 : (0 : Fin 2 →₀ ℕ) ≠ e01 := by
          intro h
          have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
          simpa [e01] using h1
        have hne : ((0 : Fin 2 →₀ ℕ), e01) ≠ (e01, 0) := by
          intro h
          apply hne0
          exact congrArg Prod.fst h
        have hmem :
            ((0 : Fin 2 →₀ ℕ), e01) ∉ ({(e01, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
          simpa [Finset.mem_singleton] using hne
        rw [Finset.sum_insert hmem]
        rw [Finset.sum_singleton]
        simp [e01, MvPowerSeries.coeff_zero_eq_constantCoeff, hΦ0, hΦe01]
      exact coeff_e01_mul_sub_eq_const Phi W hPhi0 hPhi_y1
    -- Conclude `W(0,0)=1` from the `(0,1)` coefficient of `K`.
    calc
      MvPowerSeries.constantCoeff W =
          MvPowerSeries.coeff (Finsupp.single 1 1) ((MvPowerSeries.X 1 - Phi) * W) := by
            simpa using h01R.symm
      _ = MvPowerSeries.coeff (Finsupp.single 1 1) K := by
            simpa using h01.symm
      _ = (1 : k) := by
            simpa using hKy

  -- Now `constantCoeff Phi = 0` and `coeff (X) Phi = 0` follow from the corresponding coefficients of `K`.
  have hPhi0 : MvPowerSeries.constantCoeff Phi = 0 := by
    -- Compare constant coefficients in `K = (X 1 - Phi) * W`.
    have h00 :
        MvPowerSeries.constantCoeff K = MvPowerSeries.constantCoeff ((MvPowerSeries.X 1 - Phi) * W) := by
      simpa using congrArg (fun F => MvPowerSeries.constantCoeff F) hKW
    have hcc0 : MvPowerSeries.constantCoeff ((MvPowerSeries.X 1 - Phi) * W) = 0 :=
      h00.symm.trans hK0
    have h00R :
        MvPowerSeries.constantCoeff ((MvPowerSeries.X 1 - Phi) * W) =
          -(MvPowerSeries.constantCoeff Phi) * MvPowerSeries.constantCoeff W := by
      simp [MvPowerSeries.constantCoeff_X]
    have hneg : -(MvPowerSeries.constantCoeff Phi) * MvPowerSeries.constantCoeff W = 0 := by
      simpa [h00R] using hcc0
    have hneg1 : -(MvPowerSeries.constantCoeff Phi) = 0 := by
      have : -(MvPowerSeries.constantCoeff Phi) * (1 : k) = 0 := by
        simpa [hW0] using hneg
      simpa using this
    exact neg_eq_zero.mp hneg1

  have hPhiX : MvPowerSeries.coeff (Finsupp.single 0 1) Phi = 0 := by
    -- Compare the `(1,0)` coefficient in `K = (X 1 - Phi) * W`.
    let e10 : Fin 2 →₀ ℕ := Finsupp.single 0 1
    have h10 :
        MvPowerSeries.coeff e10 K =
          MvPowerSeries.coeff e10 ((MvPowerSeries.X 1 - Phi) * W) := by
      simpa [e10] using congrArg (fun F => MvPowerSeries.coeff e10 F) hKW
    have hRHS0 : MvPowerSeries.coeff e10 ((MvPowerSeries.X 1 - Phi) * W) = 0 :=
      (h10.symm.trans (by simpa [e10] using hKx))
    have h10R :
        MvPowerSeries.coeff e10 ((MvPowerSeries.X 1 - Phi) * W) =
          -(MvPowerSeries.coeff e10 Phi) * MvPowerSeries.constantCoeff W := by
      classical
      -- Work with an abstract `Φ` to avoid unfolding the (large) definition of `Phi`.
      have coeff_e10_mul_sub (Φ Ω : MvPowerSeries (Fin 2) k)
          (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) :
          MvPowerSeries.coeff e10 ((MvPowerSeries.X 1 - Φ) * Ω) =
            -(MvPowerSeries.coeff e10 Φ) * MvPowerSeries.constantCoeff Ω := by
        classical
        have hantiNat :
            Finset.antidiagonal 1 = ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
          decide
        have hantiF :
            Finset.antidiagonal e10 =
              ({((0 : Fin 2 →₀ ℕ), e10), (e10, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
          classical
          ext p
          simp [e10, Finsupp.antidiagonal_single, hantiNat]
        -- Expand the coefficient of the product using the explicit antidiagonal.
        rw [MvPowerSeries.coeff_mul]
        rw [hantiF]
        have hne0 : (0 : Fin 2 →₀ ℕ) ≠ e10 := by
          intro h
          have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
          simpa [e10] using h0
        have hne : ((0 : Fin 2 →₀ ℕ), e10) ≠ (e10, 0) := by
          intro h
          apply hne0
          exact congrArg Prod.fst h
        have hmem :
            ((0 : Fin 2 →₀ ℕ), e10) ∉ ({(e10, 0)} : Finset ((Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ))) := by
          simpa [Finset.mem_singleton] using hne
        rw [Finset.sum_insert hmem]
        rw [Finset.sum_singleton]
        -- The `(0,e10)` term vanishes using `hΦ0`.
        have hΦ_y0 : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) Φ = 0 := by
          simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using hΦ0
        have hX1_0 :
            MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ)
                (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) = 0 := by
          simpa using (MvPowerSeries.coeff_zero_X (σ := Fin 2) (R := k) (s := (1 : Fin 2)))
        have hX1_e10 :
            MvPowerSeries.coeff e10 (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) k) = 0 := by
          have hne : (e10 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
            intro h
            have h1 := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
            simpa [e10] using h1
          simp [MvPowerSeries.coeff_X, hne, e10]
        have hcoeff0 :
            MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (MvPowerSeries.X (1 : Fin 2) - Φ) = 0 := by
          simp [hX1_0, hΦ0]
        have hcoeff_e10 :
            MvPowerSeries.coeff e10 (MvPowerSeries.X (1 : Fin 2) - Φ) = -(MvPowerSeries.coeff e10 Φ) := by
          simp [hX1_e10]
        rw [hcoeff0]
        rw [zero_mul]
        rw [zero_add]
        rw [hcoeff_e10]
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff]
      -- Apply the abstract lemma to the concrete `Phi` and `W`.
      exact coeff_e10_mul_sub Phi W hPhi0
    have hneg : -(MvPowerSeries.coeff e10 Phi) * MvPowerSeries.constantCoeff W = 0 := by
      simpa [h10R] using hRHS0
    have hneg1 : -(MvPowerSeries.coeff e10 Phi) = 0 := by
      have : -(MvPowerSeries.coeff e10 Phi) * (1 : k) = 0 := by
        simpa [hW0] using hneg
      simpa using this
    exact neg_eq_zero.mp hneg1

  refine ⟨Phi, W, hPhi_xOnly, hPhi0, hPhiX, hW0, hKW⟩

/-! #### Inverse-function-type statements -/

/-- (Formal) inverse function theorem: a coordinate map tangent to the identity has a two-sided inverse. -/
theorem exists_formal_inverse_of_tangentToId2
    {H : CoordMap2 k} (hH : TangentToId2 (k := k) H) :
    ∃ K : CoordMap2 k,
      TangentToId2 (k := k) K ∧
        CoordMap2.comp (k := k) H K = CoordMap2.id (k := k) ∧
          CoordMap2.comp (k := k) K H = CoordMap2.id (k := k) := by
  -- Standard fact about the group of (bivariate) formal power series diffeomorphisms.
  sorry

/-- Quantitative inverse function theorem in the Gauss norm on a small disc (power series version). -/
theorem exists_analytic_inverse_of_closeToId
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : c < ρ) {H : CoordMap2 k}
    (hH0 : ∀ i, MvPowerSeries.constantCoeff (H i) = 0)
    (hHlin : TangentToId2 (k := k) H)
    (hHclose : ∀ i, WeightedGaussBound2 (k := k) ρ c (H i - MvPowerSeries.X i)) :
    ∃ K : CoordMap2 k,
      TangentToId2 (k := k) K ∧
        (∀ i, WeightedGaussBound2 (k := k) ρ c (K i - MvPowerSeries.X i)) ∧
          CoordMap2.comp (k := k) H K = CoordMap2.id (k := k) ∧
            CoordMap2.comp (k := k) K H = CoordMap2.id (k := k) := by
  -- Standard nonarchimedean analytic inverse function theorem in Gauss norms.
  -- (This is the quantitative input used implicitly in Temp.md §3.2–§3.3.)
  sorry

end AnalyticStatements

/-! ### Step 3.3: bound in triangular normal form (statement only)

This is the remaining analytic estimate in the strategy of `new/Temp.md`: after conjugating to the
triangular map `g`, one must show that the normalized series associated to

`q_d(x) = K₁( (g^d ∘ H)(x,0) )`

has uniformly bounded coefficients in a weighted Gauss norm, up to at most one exceptional iterate
(handled using `NatCastNorm.natCast_add_norm_lt_one_unique`).

We record the exact statement needed to close `iter_coeff_bound`. Its proof is currently left as a
`sorry`-free *subgoal* inside `iter_coeff_bound`, but this lemma is the intended standalone target
for a later formalization of the analytic normal form estimates.
-/

section NormalFormEstimate

open scoped BigOperators

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]

-- TODO (Temp.md §3.3): bound the normalized coefficients after conjugacy to normal form.
theorem normalizedCoeffBound_qIter_of_normalForm
    [IsAlgClosed k]
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)
    (P Q : TateAlgebra2 k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcP : GaussBound k c (P : MvPowerSeries (Fin 2) k))
    (hcQ : GaussBound k c (Q : MvPowerSeries (Fin 2) k))
    (hP0 : MvPowerSeries.constantCoeff (P : MvPowerSeries (Fin 2) k) = 0)
    (hQ0 : MvPowerSeries.constantCoeff (Q : MvPowerSeries (Fin 2) k) = 0)
    (hq : ∀ d : ℕ, d > 0 → qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d ≠ 0) :
    ∃ (M r : ℝ), 0 < M ∧ 0 < r ∧ r < 1 ∧ ∀ d : ℕ, d > 0 →
      NormalizedCoeffBound (k := k)
        (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d) M r := by
  classical
  /-
  Proof framework (Temp.md §3.3):

  1. Use `exists_poincare_dulac_normal_form` to conjugate the bivariate map `f = (P,Q)` to a
     triangular map `g` with coordinates
       `g₀ = λ X₀ + τ X₁`, `g₁ = μ X₁ + b X₀^m`.
  2. Rewrite `qIter d` via the conjugacy as
       `qIter d = K₁( (g^d ∘ H)(x,0) )`,
     i.e. as a univariate substitution into `K' 1`.
  3. Let `X_d, Y_d` be the restriction of `g^d ∘ H` to the `x`-axis; then
       `X_{d+1} = λ·X_d + τ·Y_d`, `Y_{d+1} = μ·Y_d + b·X_d^m`
     (proved below from `axisIter_succ_*_of_eq`).
  4. Use explicit estimates on these recurrences (case analysis in Temp.md) plus
     `NatCastNorm.natCast_add_norm_lt_one_unique` to handle at most one exceptional `d` where
     cancellation can occur in the leading coefficient.
  -/

  -- Step 1: obtain a Poincare-Dulac normal form conjugacy (formal statement).
  rcases
      exists_poincare_dulac_normal_form (k := k) hnat P Q (c := c) hc0 hc1 hcP hcQ hP0 hQ0 with
    ⟨ρ₀, hρ₀0, hρ₀1, L, Linv, H, K, lam, mu, tau, hLlin, hLinvlin, hHρ, hKρ, hH0, hK0,
      hLLinv, hLinvL, hHK, hKH, hHtan, hKtan, hPD⟩

  let f : CoordMap2 k := substMap (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k)
  -- The actual conjugating maps between `f` and the normal form `g` are the composites
  -- `Htot = H ∘ L` and `Ktot = Linv ∘ K`.
  let Htot : CoordMap2 k := CoordMap2.comp (k := k) H L
  let Ktot : CoordMap2 k := CoordMap2.comp (k := k) Linv K
  let g : CoordMap2 k := CoordMap2.comp (k := k) Htot (CoordMap2.comp (k := k) f Ktot)

  have hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0 := hLlin.1
  have hLinv0 : ∀ i, MvPowerSeries.constantCoeff (Linv i) = 0 := hLinvlin.1

  have hHtot0 : ∀ i, MvPowerSeries.constantCoeff (Htot i) = 0 :=
    CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := H) (G := L) hH0 hL0
  have hKtot0 : ∀ i, MvPowerSeries.constantCoeff (Ktot i) = 0 :=
    CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := Linv) (G := K) hLinv0 hK0

  have hHKtot : CoordMap2.comp (k := k) Htot Ktot = CoordMap2.id (k := k) := by
    have hLinvK0 : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) Linv K) i) = 0 :=
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := Linv) (G := K) hLinv0 hK0
    calc
      CoordMap2.comp (k := k) Htot Ktot
          = CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) L (CoordMap2.comp (k := k) Linv K)) := by
              simpa [Htot, Ktot] using
                (CoordMap2.comp_assoc (k := k) (F := H) (G := L) (H := CoordMap2.comp (k := k) Linv K) hL0 hLinvK0)
      _ = CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) (CoordMap2.comp (k := k) L Linv) K) := by
            simpa using
              congrArg (fun T => CoordMap2.comp (k := k) H T)
                (CoordMap2.comp_assoc (k := k) (F := L) (G := Linv) (H := K) hLinv0 hK0).symm
      _ = CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) (CoordMap2.id (k := k)) K) := by
            simpa [hLLinv]
      _ = CoordMap2.comp (k := k) H K := by
            have : CoordMap2.comp (k := k) (CoordMap2.id (k := k)) K = K := by
              simpa using (CoordMap2.comp_id_left (k := k) (F := K) hK0)
            simpa [this]
      _ = CoordMap2.id (k := k) := hHK

  have hKHtot : CoordMap2.comp (k := k) Ktot Htot = CoordMap2.id (k := k) := by
    have hHL0 : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) H L) i) = 0 :=
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := H) (G := L) hH0 hL0
    calc
      CoordMap2.comp (k := k) Ktot Htot
          = CoordMap2.comp (k := k) Linv (CoordMap2.comp (k := k) K (CoordMap2.comp (k := k) H L)) := by
              simpa [Htot, Ktot] using
                (CoordMap2.comp_assoc (k := k) (F := Linv) (G := K) (H := CoordMap2.comp (k := k) H L) hK0 hHL0)
      _ = CoordMap2.comp (k := k) Linv (CoordMap2.comp (k := k) (CoordMap2.comp (k := k) K H) L) := by
            simpa using
              congrArg (fun T => CoordMap2.comp (k := k) Linv T)
                (CoordMap2.comp_assoc (k := k) (F := K) (G := H) (H := L) hH0 hL0).symm
      _ = CoordMap2.comp (k := k) Linv (CoordMap2.comp (k := k) (CoordMap2.id (k := k)) L) := by
            simpa [hKH]
      _ = CoordMap2.comp (k := k) Linv L := by
            have : CoordMap2.comp (k := k) (CoordMap2.id (k := k)) L = L := by
              simpa using (CoordMap2.comp_id_left (k := k) (F := L) hL0)
            simpa [this]
      _ = CoordMap2.id (k := k) := hLinvL

  have hf0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0 := by
    intro i
    fin_cases i <;> simp [f, substMap, hP0, hQ0]

  have hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := by
    have hfK0 : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) f Ktot) i) = 0 :=
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := f) (G := Ktot) hf0 hKtot0
    simpa [g] using
      (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := Htot) (G := CoordMap2.comp (k := k) f Ktot) hHtot0 hfK0)

  -- Step 2: rewrite `qIter` via the conjugacy `f^d = K ∘ g^d ∘ H`.
  -- We package the axis restrictions `X_d, Y_d` and the conjugated univariate series `qConj d`.
  let X : ℕ → k⟦X⟧ := fun d => axisIter (k := k) g Htot d 0
  let Y : ℕ → k⟦X⟧ := fun d => axisIter (k := k) g Htot d 1
  let qConj : ℕ → k⟦X⟧ := fun d => MvPowerSeries.subst (substMap1 (X d) (Y d)) (Ktot 1)

  have hq_conj : ∀ d : ℕ,
      qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d = qConj d := by
    intro d
    -- Start from the general conjugacy rewrite lemma and simplify `restrictX` to `axisIter`.
    simpa [qConj, X, Y, axisIter, restrictX, f, g] using
      (qIter_eq_subst_conj (k := k) (P := (P : MvPowerSeries (Fin 2) k)) (Q := (Q : MvPowerSeries (Fin 2) k))
        (g := g) (H := Htot) (K := Ktot) hP0 hQ0 hg0 hHtot0 hKtot0 hHKtot hKHtot (by rfl) d)

  -- Step 3: analytic estimate on the normalized coefficients (Temp.md §3.3).
  -- This is where one uses the extra structure provided by the normal-form datum `hPD`.
  have hStep3 :
      ∃ (M r : ℝ), 0 < M ∧ 0 < r ∧ r < 1 ∧ ∀ d : ℕ, d > 0 → NormalizedCoeffBound (k := k) (qConj d) M r := by
    -- TODO: implement the nonarchimedean estimates following `new/Temp.md`.
    sorry

  rcases hStep3 with ⟨M, r, hM0, hr0, hr1, hqd⟩
  refine ⟨M, r, hM0, hr0, hr1, ?_⟩
  intro d hd
  -- Transfer the bound from the conjugated expression to `qIter` using `hq_conj`.
  simpa [hq_conj d] using hqd d hd

end NormalFormEstimate

/-! ### Proof skeleton following `new/Temp.md`

The proof in `new/Temp.md` proceeds in three conceptual steps.

* Step 1: uniform bounds for iterates in a weighted Gauss norm on a small disc.
* Step 2: reduce the coefficient inequality to a bound on the normalized series
  `divXPowOrder (qIter … d)`.
* Step 3: use the (analytic) Poincaré–Dulac normal form to explicitly control the normalized
  series, up to at most one exceptional iterate (handled using `NatCastNorm`).

In the current formal development we work with formal power series. To complete the Lean proof
one needs additional quantitative conclusions about the conjugating maps `H` and `K` (tangent-to-
identity and unit bounds on a small radius) which are used implicitly in `new/Temp.md` §3.3.
-/

/-- Formal statement of the coefficient estimate for `Q_d(x,0)` (cf. `new/Temp.md`). -/
theorem iter_coeff_bound {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    [IsAlgClosed k]
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
  classical
  -- Step 3.3 is isolated as the normal-form estimate `normalizedCoeffBound_qIter_of_normalForm`.
  rcases
      normalizedCoeffBound_qIter_of_normalForm (k := k) hnat P Q (c := c) hc0 hc1 hcP hcq hP0 hQ0 hq with
    ⟨M, r, hM0, hr0, hr1, hbound⟩
  refine ⟨M, r, hM0, hr0, hr1, ?_⟩
  intro d m hd hm
  have hNm :
      r ^ m *
          ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat + m)
              (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ ≤
        M *
          ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat)
              (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ := by
    -- Convert `NormalizedCoeffBound` to the coefficient inequality in the statement.
    have h' :
        ∀ n : ℕ,
          r ^ n *
              ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat + n)
                  (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ ≤
            M *
              ‖coeff ((qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d).order.toNat)
                  (qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d)‖ :=
      (normalizedCoeffBound_iff (k := k)
        (f := qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d) (M := M)
        (r := r)).1 (hbound d hd)
    exact h' m
  exact hNm
