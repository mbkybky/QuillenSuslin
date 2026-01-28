import QuillenSuslin.FiniteFreeResolution

universe u v w

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal

theorem mvPolynomial_hasFiniteFreeResolution_of_isNoetherianRing_u [IsNoetherianRing R]
    (s : Type) [Finite s]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Type u) [AddCommGroup P] [Module (MvPolynomial s R) P]
    [Module.Finite (MvPolynomial s R) P] : HasFiniteFreeResolution (MvPolynomial s R) P := by
  sorry
