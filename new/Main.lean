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
    ∃ (H K : CoordMap2 k) (lam mu tau : k),
      (∀ i, MvPowerSeries.constantCoeff (H i) = 0) ∧
      (∀ i, MvPowerSeries.constantCoeff (K i) = 0) ∧
      -- `H` and `K` are tangent to the identity at the origin.
      MvPowerSeries.coeff (Finsupp.single 0 1) (H 0) = 1 ∧
      MvPowerSeries.coeff (Finsupp.single 1 1) (H 0) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1) (H 1) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 1 1) (H 1) = 1 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1) (K 0) = 1 ∧
      MvPowerSeries.coeff (Finsupp.single 1 1) (K 0) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1) (K 1) = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 1 1) (K 1) = 1 ∧
      -- `K` is a two-sided inverse of `H` under composition.
      CoordMap2.comp (k := k) H K = CoordMap2.id (k := k) ∧
      CoordMap2.comp (k := k) K H = CoordMap2.id (k := k) ∧
      -- Conjugating `f = (P,Q)` by `H` yields a (formal) Poincare-Dulac normal form.
      let P' : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K 0) (K 1))
            (P : MvPowerSeries (Fin 2) k)
      let Q' : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap (K 0) (K 1))
            (Q : MvPowerSeries (Fin 2) k)
      let g₁ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P' Q') (H 0)
      let g₂ : MvPowerSeries (Fin 2) k :=
          MvPowerSeries.subst (substMap P' Q') (H 1)
      MvPowerSeries.constantCoeff g₁ = 0 ∧
        MvPowerSeries.constantCoeff g₂ = 0 ∧
          MvPowerSeries.coeff (Finsupp.single 0 1) g₁ = lam ∧
              MvPowerSeries.coeff (Finsupp.single 1 1) g₁ = tau ∧
              MvPowerSeries.coeff (Finsupp.single 0 1) g₂ = 0 ∧
                MvPowerSeries.coeff (Finsupp.single 1 1) g₂ = mu ∧
                  ‖lam‖ < 1 ∧ ‖mu‖ < 1 ∧ ‖mu‖ ≤ ‖lam‖ ∧ (tau = 0 ∨ tau = 1) ∧
                    (∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 →
                      MvPowerSeries.coeff e g₁ ≠ 0 → lam ^ (e 0) * mu ^ (e 1) = lam) ∧
                      (∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 →
                        MvPowerSeries.coeff e g₂ ≠ 0 → lam ^ (e 0) * mu ^ (e 1) = mu) ∧
                        (lam ≠ 0 → ∀ e : Fin 2 →₀ ℕ, 2 ≤ e 0 + e 1 → MvPowerSeries.coeff e g₁ = 0) ∧
                          ((mu = 0 ∧ lam ≠ 0) →
                            ∃ R : MvPowerSeries (Fin 2) k,
                              MvPowerSeries.constantCoeff R = 0 ∧ g₂ = MvPowerSeries.X 1 * R) ∧
                            (mu ≠ 0 →
                              ∃ (b : k) (m : ℕ),
                                2 ≤ m ∧ (b = 0 ∨ lam ^ m = mu) ∧
                                  g₂ =
                                    MvPowerSeries.C mu * MvPowerSeries.X 1 +
                                      MvPowerSeries.C b * (MvPowerSeries.X 0) ^ m) := by
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

/-- Weighted Gauss bound for a univariate power series at radius `ρ`. -/
def WeightedGaussBound1 (ρ C : ℝ) (f : k⟦X⟧) : Prop :=
  ∀ n : ℕ, ‖coeff n f‖ * ρ ^ n ≤ C

/-- Weighted Gauss bound for a bivariate power series with weight `i+j` at radius `ρ`. -/
def WeightedGaussBound2 (ρ C : ℝ) (F : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, ‖MvPowerSeries.coeff e F‖ * ρ ^ (e 0 + e 1) ≤ C

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
  -- Choose `ρ` small enough so that all coefficients satisfy `‖a_n‖ ρ^n ≤ ε`.
  sorry

/-- Temp.md Lemma 3.3.2 (bivariate): shrinking the radius makes the weighted Gauss bound small for a restricted
series with zero constant term. -/
theorem exists_radius_weightedGaussBound2_of_constantCoeff_eq_zero
    {F : MvPowerSeries (Fin 2) k} (hFT : IsTate k (Fin 2) F)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ WeightedGaussBound2 (k := k) ρ ε F := by
  -- Same argument as the univariate case, using the total degree `e 0 + e 1`.
  sorry

/-- Temp.md Lemma 3.3.3: substitution does not increase the weighted Gauss bound, provided the substituted
series stay inside the same closed disc. -/
theorem weightedGaussBound1_subst_of_weightedGaussBound2
    {ρ C : ℝ} {F : MvPowerSeries (Fin 2) k} (hF : WeightedGaussBound2 (k := k) ρ C F)
    {p q : k⟦X⟧} (ha : MvPowerSeries.HasSubst (substMap1 p q))
    (hp : WeightedGaussBound1 (k := k) ρ ρ p) (hq : WeightedGaussBound1 (k := k) ρ ρ q) :
    WeightedGaussBound1 (k := k) ρ C (MvPowerSeries.subst (substMap1 p q) F) := by
  -- Standard Gauss-norm estimate for substitution on a closed disc.
  sorry

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
  sorry

/-! #### Implicit-function / Weierstrass (degree `1`) -/

/-- A bivariate series depends only on the `X 0` variable (no `X 1`-terms). -/
def IsXOnly (F : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, e 1 ≠ 0 → MvPowerSeries.coeff e F = 0

/-- Temp.md Lemma 3.3.5: if `∂K/∂Y (0,0)=1`, then `K(X,Y) = (Y - Φ(X)) * W(X,Y)` with `W(0,0)=1`. -/
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
  sorry

/-! #### Inverse-function-type statements -/

/-- A bivariate coordinate map is tangent to the identity at the origin. -/
def TangentToId2 (H : CoordMap2 k) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (H i) = 0) ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (H 0) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (H 0) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (H 1) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (H 1) = 1

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
    ⟨H, K, lam, mu, tau, hH0, hK0, hH_x, hH_y, hH_yx, hH_yy, hK_x, hK_y, hK_yx, hK_yy, hHK, hKH, hPD⟩

  let f : CoordMap2 k := substMap (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k)
  let g : CoordMap2 k := CoordMap2.comp (k := k) H (CoordMap2.comp (k := k) f K)

  have hf0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0 := by
    intro i
    fin_cases i <;> simp [f, substMap, hP0, hQ0]

  have hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := by
    have hfK0 : ∀ i, MvPowerSeries.constantCoeff ((CoordMap2.comp (k := k) f K) i) = 0 :=
      CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := f) (G := K) hf0 hK0
    simpa [g] using
      (CoordMap2.constantCoeff_comp_eq_zero (k := k) (F := H) (G := CoordMap2.comp (k := k) f K) hH0 hfK0)

  -- Step 2: rewrite `qIter` via the conjugacy `f^d = K ∘ g^d ∘ H`.
  -- We package the axis restrictions `X_d, Y_d` and the conjugated univariate series `qConj d`.
  let X : ℕ → k⟦X⟧ := fun d => axisIter (k := k) g H d 0
  let Y : ℕ → k⟦X⟧ := fun d => axisIter (k := k) g H d 1
  let qConj : ℕ → k⟦X⟧ := fun d => MvPowerSeries.subst (substMap1 (X d) (Y d)) (K 1)

  have hq_conj : ∀ d : ℕ,
      qIter k (P : MvPowerSeries (Fin 2) k) (Q : MvPowerSeries (Fin 2) k) d = qConj d := by
    intro d
    -- Start from the general conjugacy rewrite lemma and simplify `restrictX` to `axisIter`.
    simpa [qConj, X, Y, axisIter, restrictX, f, g] using
      (qIter_eq_subst_conj (k := k) (P := (P : MvPowerSeries (Fin 2) k)) (Q := (Q : MvPowerSeries (Fin 2) k))
        (g := g) (H := H) (K := K) hP0 hQ0 hg0 hH0 hK0 hHK hKH (by rfl) d)

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
