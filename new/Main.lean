import Mathlib

open PowerSeries

variable {k : Type*} [NormedField k] [CompleteSpace k] [IsUltrametricDist k] [IsAlgClosed k]
  (hnat : ∀ n : ℕ, n ≠ 0 → ‖(n : k)‖ = 1)

def TateAlgebra (R : Type*) [NormedRing R] : Type _ := { f : PowerSeries R // IsRestricted 1 f }

theorem temp_coeff_bound (q : ℕ → k⟦X⟧) (hq : ∀ d : ℕ+, q d ≠ 0) :
    ∃ (M r : ℝ), 0 < M ∧ 0 < r ∧ r < 1 ∧ ∀ (d n : ℕ),
      r ^ n * ‖coeff ((q d).order.toNat + n) (q d)‖ ≤ M * ‖coeff ((q d).order.toNat) (q d)‖ := by
  sorry
