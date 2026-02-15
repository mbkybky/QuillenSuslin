import Mathlib

open PowerSeries MvPowerSeries

/-- A radius-`1` Gauss-type bound: all coefficients have norm bounded by `c`. -/
def GaussBound (k : Type*) [NormedRing k] (c : ℝ) (F : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ e : Fin 2 →₀ ℕ, ‖(MvPowerSeries.coeff e) F‖ ≤ c

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

/-- Formal statement of the coefficient estimate for `Q_d(x,0)` (cf. `new/Temp.md`). -/
theorem iter_coeff_bound {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k]
    (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)
    (P Q : MvPowerSeries (Fin 2) k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcP : GaussBound k c P) (hcq : GaussBound k c Q)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hq : ∀ d : ℕ, d > 0 → qIter k P Q d ≠ 0) :
    ∃ (M r : ℝ),  0 < r ∧ ∀ (d m : ℕ),
      r ^ (m : ℕ) * ‖coeff ((qIter k P Q d).order.toNat + (m : ℕ)) (qIter k P Q d)‖ ≤
        M * ‖coeff ((qIter k P Q d).order.toNat) (qIter k P Q d)‖ := by
  sorry
