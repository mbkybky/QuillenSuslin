import QuillenSuslin.Horrocks
import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R] [IsDomain R]
variable {s : Type*} [Fintype s] [DecidableEq s]

/-- Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such
  that $v(x) \sim v(x + cy)$ over $R[x, y]$. -/
theorem lem10 {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
    (h : UnimodularVectorEquiv (fun i => (v i).map (algebraMap R (Localization S)))
      (fun i => C (algebraMap R (Localization S) ((v i).eval 0)))) :
    ∃ c : S, UnimodularVectorEquiv (fun i => C (v i))
      (fun i => (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp C) (C X + (c : R) • Y)) := by
  rcases h with ⟨M, hM⟩
  let Sx : Submonoid R[X] := S.map (C : R →+* R[X])
  let Sxy : Submonoid R[X][Y] := Sx.map (C : R[X] →+* R[X][Y])
  let : IsLocalization Sx (Localization S)[X] := by
    simpa [Sx] using (Polynomial.isLocalization S (Localization S))
  let : IsLocalization Sxy ((Localization S)[X][Y]) := by
    simpa [Sxy] using (Polynomial.isLocalization Sx (Localization S)[X])
  rcases IsLocalization.exist_integer_multiples_of_finite Sxy (fun ij : s × s => W S M ij.1 ij.2)
    with ⟨b, hb⟩
  rcases b.property with ⟨rX, hrX, hrXb⟩
  rcases hrX with ⟨rR, hrR, hrRC⟩
  let c : S := ⟨rR, hrR⟩
  have hrXb : (C (C (c : R)) : R[X][Y]) = (b : R[X][Y]) :=
    (congrArg (C : R[X] →+* R[X][Y]) hrRC).trans <| by simpa [c] using hrXb
  have hb : ∀ ij : s × s, IsLocalization.IsInteger R[X][Y]
      ((C (C (c : R)) : R[X][Y]) • W S M ij.1 ij.2) := by
    intro ij
    simpa [hrXb, Algebra.smul_def] using hb ij
  have hc : ∀ i j : s,
      IsLocalization.IsInteger R[X][Y] ((C (C (c : R)) : R[X][Y]) • σA c (W S M i j)) := by
    intro i j
    have hfix : σA c (C (C ((algebraMap R (Localization S)) (c : R)))) =
        (C (C ((algebraMap R (Localization S)) (c : R)))) := by
      simp only [σA, algebraMap_smul, coe_eval₂RingHom, eval₂_C]
    simpa only [Algebra.smul_def, algebraMap_def, coe_mapRingHom, map_C, map_mul, hfix] using
      isInteger_σA c (hb (i, j))
  have hmulVec : ((U hs M hc)⁻¹.1).mulVec (fun i => C (v i)) = _ := hU hs v M hM hc
  exact ⟨c, (U hs M hc)⁻¹, by simpa only [Matrix.coe_units_inv] using hmulVec⟩

noncomputable section cor11

abbrev cor11ι : R →+* R[X][Y] := (C : R[X] →+* R[X][Y]).comp (C : R →+* R[X])

abbrev cor11vx (v : s → R[X]) : s → R[X][Y] := fun i => C (v i)

/-- The vector `v(x + qy)` in `R[X][Y]`. -/
abbrev cor11vxy (v : s → R[X]) (q : R) : s → R[X][Y] :=
  fun i => (v i).eval₂ cor11ι (C X + q • Y)

omit [IsDomain R] in
lemma cor11_hAlg : algebraMap R R[X][Y] = cor11ι := by
  ext r
  simp [cor11ι]

/-- Push a unimodular-vector equivalence along a ring homomorphism. -/
theorem unimodularVectorEquiv_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {v w : s → A} (hvw : UnimodularVectorEquiv v w) :
    UnimodularVectorEquiv (fun i => f (v i)) (fun i => f (w i)) := by
  rcases hvw with ⟨M, hM⟩
  refine ⟨Matrix.GeneralLinearGroup.map f M, ?_⟩
  ext i
  have hi : (M.1.mulVec v) i = w i := congrArg (fun u : s → A => u i) hM
  have hi' : f ((M.1.mulVec v) i) = f (w i) := congrArg f hi
  have hmap : (M.1.map f).mulVec (fun j => f (v j)) i = f ((M.1.mulVec v) i) := by
    simpa [Function.comp] using (RingHom.map_mulVec f M.1 v i).symm
  simpa [Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply] using hmap.trans hi'

/-- The ideal of `q : R` such that `v(x + qy) ∼ v(x)` in `R[X][Y]`. -/
def cor11IdealCarrier (v : s → R[X]) : Set R :=
  {q | UnimodularVectorEquiv (cor11vx v) (cor11vxy v q)}

omit [IsDomain R] in
/-- `0 ∈ cor11IdealCarrier v`. -/
lemma cor11Ideal_zero_mem (v : s → R[X]) : (0 : R) ∈ cor11IdealCarrier v := by
  have hC : (Polynomial.eval₂RingHom cor11ι (C X)) = (C : R[X] →+* R[X][Y]) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext r
      simp [cor11ι]
    · simp [cor11ι]
  have h0 : cor11vxy v 0 = cor11vx v := by
    funext i
    simpa [cor11vxy, cor11vx] using  congrArg (fun f : R[X] →+* R[X][Y] => f (v i)) hC
  simpa [cor11IdealCarrier, h0] using unimodularVectorEquiv_equivalence.refl (cor11vx v)

lemma cor11Ideal_add_mem (v : s → R[X]) {a b : R} (ha : a ∈ cor11IdealCarrier v)
    (hb : b ∈ cor11IdealCarrier v) :
    a + b ∈ cor11IdealCarrier v := by
  let shift : R[X][Y] →+* R[X][Y] := eval₂RingHom (Polynomial.eval₂RingHom cor11ι (C X + b • Y)) Y
  have hx : (fun i : s => shift (cor11vx v i)) = cor11vxy v b := by
    funext i
    dsimp [shift, cor11vx, cor11vxy]
    simp only [eval₂_C, coe_eval₂RingHom]
  have hxy : (fun i : s => shift (cor11vxy v a i)) = cor11vxy v (a + b) := by
    funext i
    have hcoeff : shift.comp cor11ι = cor11ι := by
      ext r
      dsimp [shift, cor11ι]
      simp only [eval₂_C, coe_eval₂RingHom, RingHom.coe_comp, Function.comp_apply]
    have hCX : shift (C X) = C X + b • Y := by
      dsimp [shift]
      simp only [eval₂_C, coe_eval₂RingHom, eval₂_X]
    have hY : shift Y = Y := by
      dsimp [shift]
      simp only [eval₂_X]
    have hιa : shift (cor11ι a) = cor11ι a := by
      have := congrArg (fun f : R →+* R[X][Y] => f a) hcoeff
      simpa [RingHom.comp_apply] using this
    have haY : shift (a • Y) = a • Y := by
      calc shift (a • Y) = shift (cor11ι a * Y) := by simp [Algebra.smul_def, cor11_hAlg]
        _ = shift (cor11ι a) * shift Y := by simp
        _ = shift (cor11ι a) * Y := by simp [hY]
        _ = cor11ι a * Y := by simpa [hιa]
        _ = a • Y := by simp [Algebra.smul_def, cor11_hAlg]
    have hX : shift (C X + a • Y) = C X + (a + b) • Y := by
      calc shift (C X + a • Y) = shift (C X) + shift (a • Y) := by simp only [map_add]
        _ = (C X + b • Y) + a • Y := by simp only [hCX, haY]
        _ = C X + (a + b) • Y := by simp only [add_comm, add_smul, add_assoc]
    have := Polynomial.hom_eval₂ (v i) cor11ι shift (C X + a • Y)
    simpa only [cor11vxy, hcoeff, hX] using this
  have hab : UnimodularVectorEquiv (cor11vxy v b) (cor11vxy v (a + b)) := by
    simpa [hx, hxy] using unimodularVectorEquiv_map shift ha
  exact (unimodularVectorEquiv_equivalence).trans hb hab

omit [IsDomain R] in
/-- `cor11IdealCarrier v` is closed under scalar multiplication (i.e. multiplication in `R`). -/
lemma cor11Ideal_smul_mem (v : s → R[X]) (r : R) {a : R} (ha : a ∈ cor11IdealCarrier v) :
    r * a ∈ cor11IdealCarrier v := by
  let scaleY : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) (r • Y)
  have hx : (fun i : s => scaleY (cor11vx v i)) = cor11vx v := by
    funext i
    dsimp [scaleY, cor11vx]
    simp only [eval₂_C]
  have hxy : (fun i : s => scaleY (cor11vxy v a i)) = cor11vxy v (r * a) := by
    funext i
    have hcoeff : scaleY.comp cor11ι = cor11ι := by
      ext x
      dsimp [scaleY, cor11ι]
      simp only [eval₂_C]
    have hCX : scaleY (C X) = C X := by
      dsimp [scaleY]
      simp only [eval₂_C]
    have hY : scaleY Y = r • Y := by
      dsimp [scaleY]
      simp only [eval₂_X]
    have hιa : scaleY (cor11ι a) = cor11ι a := by
      simpa [RingHom.comp_apply] using congrArg (fun f : R →+* R[X][Y] => f a) hcoeff
    have hYa : scaleY (a • Y) = (r * a) • Y := by
      have hιr : (r : R) • Y = cor11ι r * Y := by simp [Algebra.smul_def, cor11_hAlg, cor11ι]
      calc
        _ = scaleY (cor11ι a) * scaleY Y := by
          simp only [Algebra.smul_def, cor11_hAlg, RingHom.coe_comp, Function.comp_apply, map_mul]
        _ = cor11ι a * (cor11ι r * Y) := by rw [hY, hιa, hιr]
        _ = (cor11ι a * cor11ι r) * Y := by rw [mul_assoc]
        _ = cor11ι (a * r) * Y := by rw [map_mul]
        _ = cor11ι (r * a) * Y := by
          simp only [mul_comm, RingHom.coe_comp, Function.comp_apply, map_mul]
        _ = (r * a) • Y := by simp [Algebra.smul_def, cor11_hAlg, cor11ι]
    have hX : scaleY (C X + a • Y) = C X + (r * a) • Y := by
      simp only [map_add, hCX, hYa]
    have := Polynomial.hom_eval₂ (v i) cor11ι scaleY (C X + a • Y)
    simpa only [cor11vxy, hcoeff, hX] using this
  simpa [cor11IdealCarrier, hx, hxy] using unimodularVectorEquiv_map scaleY ha

def cor11Ideal (v : s → R[X]) : Ideal R :=
  { carrier := cor11IdealCarrier v
    zero_mem' := cor11Ideal_zero_mem v
    add_mem' := cor11Ideal_add_mem v
    smul_mem' := cor11Ideal_smul_mem v }

theorem cor11Ideal_eq_top (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    cor11Ideal v = ⊤ := by
  let I : Ideal R := cor11Ideal v
  by_contra hI
  rcases Ideal.exists_le_maximal I hI with ⟨m, hm, hIm⟩
  let S : Submonoid R := Ideal.primeCompl m
  have hS0 : (0 : R) ∉ S := by simp [S, Ideal.primeCompl]
  have hs : S ≤ nonZeroDivisors R := le_nonZeroDivisors_of_noZeroDivisors hS0
  let vS : s → (Localization S)[X] := fun i => (v i).map (algebraMap R (Localization S))
  have hvS : IsUnimodular vS := by
    have h1 : (1 : R[X]) ∈ Ideal.span (Set.range v) := by
      rw [hv]
      exact Submodule.mem_top
    rcases (Ideal.mem_span_range_iff_exists_fun).1 h1 with ⟨c, hc⟩
    let fX : R[X] →+* (Localization S)[X] := Polynomial.mapRingHom (algebraMap R (Localization S))
    have hc' : (∑ i : s, fX (c i) * fX (v i)) = 1 := by
      simpa [map_sum, map_mul, fX] using congrArg fX hc
    have : (1 : (Localization S)[X]) ∈ Ideal.span (Set.range vS) := by
      refine (Ideal.mem_span_range_iff_exists_fun).2 ?_
      refine ⟨fun i => fX (c i), ?_⟩
      simpa [vS, map_sum, map_mul, fX] using hc'
    unfold IsUnimodular
    exact (Ideal.eq_top_iff_one _).2 this
  have hmonicS : ∃ i : s, (vS i).Monic := by
    rcases h with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa [vS] using hi.map (algebraMap R (Localization S))
  have : IsLocalRing (Localization S) := by
    have : m.IsPrime := hm.isPrime
    simpa [S, Localization.AtPrime] using (Localization.AtPrime.isLocalRing (P := m))
  have hloc : UnimodularVectorEquiv vS
      (fun i => C (algebraMap R (Localization S) ((v i).eval 0))) := by
    have hev0 : (fun i => C ((vS i).eval 0)) = fun i => C (algebraMap R (Localization S) ((v i).eval 0)) := by
      funext i
      have : (vS i).eval 0 = algebraMap R (Localization S) ((v i).eval 0) := by
        simpa [vS] using (Polynomial.eval_zero_map (algebraMap R (Localization S)) (v i))
      simp [this]
    simpa [hev0] using cor9 vS hvS hmonicS
  rcases lem10 hs v hloc with ⟨c, hc⟩
  exact c.2 (hIm hc)

/-- From a localization equivalence `v(x) ∼ v(0)` at a maximal ideal, produce `q ∉ m` with
`v(x) ∼ v(x + qy)` over `R[x,y]`. -/
theorem cor11IdealCarrier_exists_not_mem_maximal_of_local_equiv (v : s → R[X]) (m : Ideal R)
    [hm : m.IsMaximal]
    (hloc :
      let Rm := Localization m.primeCompl
      let ι : R →+* Rm := algebraMap R Rm
      UnimodularVectorEquiv (fun i => (v i).map ι) (fun i => C (ι ((v i).eval 0)))) :
    ∃ q : R, q ∈ cor11IdealCarrier v ∧ q ∉ m := by
  classical
  haveI : m.IsPrime := hm.isPrime
  let S : Submonoid R := m.primeCompl
  have hS0 : (0 : R) ∉ S := by simp [S, Ideal.mem_primeCompl_iff]
  have hs : S ≤ nonZeroDivisors R := le_nonZeroDivisors_of_noZeroDivisors hS0
  rcases lem10 hs v (by simpa [S] using hloc) with ⟨c, hc⟩
  refine ⟨(c : R), ?_, ?_⟩
  · change UnimodularVectorEquiv (cor11vx v) (cor11vxy v (c : R))
    change
      UnimodularVectorEquiv (fun i : s => C (v i))
        (fun i : s =>
          (v i).eval₂ ((C : R[X] →+* R[X][Y]).comp (C : R →+* R[X])) (C X + (c : R) • Y))
    exact hc
  · exact (Ideal.mem_primeCompl_iff).1 c.2

/-- A maximal-ideal criterion for `cor11Ideal v = ⊤`. -/
theorem cor11Ideal_eq_top_of_forall_maximal (v : s → R[X])
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ q : R, q ∈ cor11IdealCarrier v ∧ q ∉ m) :
    cor11Ideal v = ⊤ := by
  classical
  by_contra hI
  rcases Ideal.exists_le_maximal (cor11Ideal v) hI with ⟨m, hm, hIm⟩
  rcases h m hm with ⟨q, hqI, hqnm⟩
  exact hqnm (hIm hqI)

/-- A local-to-global form of `cor11`: if `v(x) ∼ v(0)` holds after localizing at *every* maximal
ideal of the coefficient ring, then it already holds over the original ring. -/
theorem cor11_of_forall_maximal_local_equiv (v : s → R[X])
    (hloc :
      ∀ m : Ideal R, [m.IsMaximal] →
        let Rm := Localization m.primeCompl
        let ι : R →+* Rm := algebraMap R Rm
        UnimodularVectorEquiv (fun i => (v i).map ι) (fun i => C (ι ((v i).eval 0)))) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  classical
  let I : Ideal R := cor11Ideal v
  have hI : I = ⊤ := by
    have hmax :
        ∀ m : Ideal R, m.IsMaximal → ∃ q : R, q ∈ cor11IdealCarrier v ∧ q ∉ m := by
      intro m hm
      haveI : m.IsMaximal := hm
      exact cor11IdealCarrier_exists_not_mem_maximal_of_local_equiv (v := v) m (hloc m)
    simpa [I] using cor11Ideal_eq_top_of_forall_maximal (v := v) hmax
  have h1 : (1 : R) ∈ I := by simp [I, hI]
  have hI1 : UnimodularVectorEquiv (cor11vx v) (cor11vxy v 1) := h1
  let ev0 : R[X] →+* R[X] := Polynomial.eval₂RingHom (C : R →+* R[X]) 0
  let evXY : R[X][Y] →+* R[X] := Polynomial.eval₂RingHom ev0 X
  have hev0 (i : s) : ev0 (v i) = C ((v i).eval 0) := by
    simp [ev0, Polynomial.coeff_zero_eq_eval_zero]
  have hevXY_vx : (fun i => evXY (cor11vx v i)) = fun i => C ((v i).eval 0) := by
    funext i
    simp [evXY, ev0, hev0 i]
  have hevXY_vxy : (fun i => evXY (cor11vxy v 1 i)) = v := by
    funext i
    have hcoeff : evXY.comp cor11ι = (C : R →+* R[X]) := by
      ext r
      simp [evXY, ev0, cor11ι]
    have hX : evXY (C X + Y) = X := by simp [evXY, ev0]
    have hhom := Polynomial.hom_eval₂ (v i) cor11ι evXY (C X + Y)
    have : evXY (cor11vxy v 1 i) = (v i).eval₂ (C : R →+* R[X]) X := by
      simpa [cor11vxy, cor11ι, one_smul, hcoeff, hX] using hhom
    simpa [Polynomial.eval₂_C_X] using this
  have hmain : UnimodularVectorEquiv (fun i => C ((v i).eval 0)) v := by
    simpa [hevXY_vx, hevXY_vxy] using unimodularVectorEquiv_map evXY hI1
  exact unimodularVectorEquiv_equivalence.symm hmain

/-- Suppose $R$ is any ring, and $v(x) \in R[x]^s$ is a unimodular vector one of whose
  leading coefficients is one. Then $v(x) \sim v(0)$. -/
theorem cor11 (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) :=
  let I : Ideal R := cor11Ideal v
  have hI : I = ⊤ := cor11Ideal_eq_top v hv h
  have h1 : (1 : R) ∈ I := by simp [hI]
  have hI1 : UnimodularVectorEquiv (cor11vx v) (cor11vxy v 1) := h1
  let ev0 : R[X] →+* R[X] := Polynomial.eval₂RingHom (C : R →+* R[X]) 0
  let evXY : R[X][Y] →+* R[X] := Polynomial.eval₂RingHom ev0 X
  have hev0 (i : s) : ev0 (v i) = C ((v i).eval 0) := by
    simp [ev0, Polynomial.coeff_zero_eq_eval_zero]
  have hevXY_vx : (fun i => evXY (cor11vx v i)) = fun i => C ((v i).eval 0) := by
    funext i
    simp [evXY, ev0, hev0 i]
  have hevXY_vxy : (fun i => evXY (cor11vxy v 1 i)) = v := by
    funext i
    have hcoeff : evXY.comp cor11ι = (C : R →+* R[X]) := by
      ext r
      simp [evXY, ev0, cor11ι]
    have hX : evXY (C X + Y) = X := by simp [evXY, ev0]
    have hhom := Polynomial.hom_eval₂ (v i) cor11ι evXY (C X + Y)
    have : evXY (cor11vxy v 1 i) = (v i).eval₂ (C : R →+* R[X]) X := by
      simpa [cor11vxy, cor11ι, one_smul, hcoeff, hX] using hhom
    simpa [Polynomial.eval₂_C_X] using this
  have hmain : UnimodularVectorEquiv (fun i => C ((v i).eval 0)) v := by
    simpa [hevXY_vx, hevXY_vxy] using unimodularVectorEquiv_map evXY hI1
  unimodularVectorEquiv_equivalence.symm hmain

/-- A variant of `cor11`: it suffices that some component has *unit* leading coefficient. -/
theorem cor11_of_isUnit_leadingCoeff (v : s → R[X]) (hv : IsUnimodular v)
    (h : ∃ i : s, IsUnit (v i).leadingCoeff) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  classical
  rcases h with ⟨i, hi⟩
  rcases hi with ⟨u, hu⟩
  let b : R := (↑(u⁻¹) : R)
  have hb : b * (v i).leadingCoeff = 1 := by
    calc b * (v i).leadingCoeff = (↑(u⁻¹) : R) * (↑u : R) := by simp [b, hu]
      _ = 1 := by simp
  have hmonic : (Polynomial.C b * v i).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hb
  have hunitC : IsUnit (Polynomial.C b : R[X]) := by
    have : IsUnit b := ⟨u⁻¹, rfl⟩
    simpa [Polynomial.isUnit_C] using this
  let v' : s → R[X] := Function.update v i (Polynomial.C b * v i)
  have hvv' : UnimodularVectorEquiv v v' :=
    unimodularVectorEquiv_update_mul_isUnit (R := R) (s := s) i (Polynomial.C b) hunitC v
  have hv' : IsUnimodular v' :=
    (isUnimodular_iff_of_unimodularVectorEquiv (R := R) (s := s) hvv').1 hv
  have hmonic' : ∃ j : s, (v' j).Monic := by refine ⟨i, by simp [v', hmonic]⟩
  let w0 : s → R[X] := fun j => C ((v j).eval 0)
  let w1 : s → R[X] := fun j => C ((v' j).eval 0)
  have hcor : UnimodularVectorEquiv v' w1 := by simpa [w1] using cor11 v' hv' hmonic'
  have hw1 : w1 = Function.update w0 i (Polynomial.C b * w0 i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [mul_comm, Function.update_self, eval_mul, eval_C, map_mul, w1, v', w0]
    · simp [w1, w0, v', Function.update, hj]
  have hw0w1 : UnimodularVectorEquiv w0 w1 := by
    have := unimodularVectorEquiv_update_mul_isUnit (R := R) (s := s) i (Polynomial.C b) hunitC w0
    simpa [hw1] using this
  have hw1w0 : UnimodularVectorEquiv w1 w0 := unimodularVectorEquiv_equivalence.symm hw0w1
  exact unimodularVectorEquiv_equivalence.trans hvv' <|
    unimodularVectorEquiv_equivalence.trans hcor hw1w0

end cor11

section thm12_field

variable (R : Type*) [CommRing R] [IsDomain R]
variable {s : Type*}

/-- Unimodularity is preserved under a ring homomorphism. -/
theorem isUnimodular_map_ringHom {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (v : s → A) (hv : IsUnimodular v) : IsUnimodular fun i => f (v i) := by
  classical
  unfold IsUnimodular at hv ⊢
  have hmap : Ideal.map f (Ideal.span (Set.range v)) = ⊤ := by
    simpa [hv] using (Ideal.map_top (f := f) : Ideal.map f (⊤ : Ideal A) = (⊤ : Ideal B))
  have hrange : (f : A → B) '' Set.range v = Set.range fun i => f (v i) := by
    ext b
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  have hspan : Ideal.span ((f : A → B) '' Set.range v) = ⊤ := by
    simpa [Ideal.map_span] using hmap
  simpa [hrange] using hspan

/-- Unimodularity is preserved under an algebra equivalence. -/
theorem isUnimodular_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (v : s → A) (hv : IsUnimodular v) : IsUnimodular fun i => e (v i) := by
  classical
  unfold IsUnimodular at hv ⊢
  have hmap : Ideal.map (e : A →+* B) (Ideal.span (Set.range v)) = ⊤ := by
    have := congrArg (Ideal.map (e : A →+* B)) hv
    simpa using this.trans (by simpa using (Ideal.map_top (f := (e : A →+* B))))
  have hspan : Ideal.span ((e : A →+* B) '' Set.range v) = ⊤ := by
    simpa [Ideal.map_span] using hmap
  have hrange : (e : A → B) '' Set.range v = Set.range fun i => e (v i) := by
    ext b
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  simpa [hrange] using hspan

variable [Fintype s] [DecidableEq s]

/-- Unimodular-vector equivalence is preserved under an algebra equivalence. -/
theorem unimodularVectorEquiv_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (v w : s → A) (hvw : UnimodularVectorEquiv v w) :
    UnimodularVectorEquiv (fun i => e (v i)) (fun i => e (w i)) := by
  simpa using unimodularVectorEquiv_map (f := (e : A →+* B)) hvw

omit [IsDomain R] in
/-- Local Horrocks step: if a unimodular vector in `R[X]` becomes monic in some coordinate after
localizing the coefficient ring at a maximal ideal, then over that localization we have
`v(x) ∼ v(0)`. -/
theorem local_equiv_eval0_of_monic_localization (v : s → R[X]) (hv : IsUnimodular v) {m : Ideal R}
    (hm : m.IsMaximal)
    (hmonic : ∃ i : s, ((v i).map (algebraMap R (Localization m.primeCompl))).Monic) :
    UnimodularVectorEquiv
      (fun i => (v i).map (algebraMap R (Localization m.primeCompl)))
      (fun i => C (algebraMap R (Localization m.primeCompl) ((v i).eval 0))) := by
  classical
  haveI : m.IsPrime := hm.isPrime
  haveI : IsLocalRing (Localization m.primeCompl) :=
    by simpa using (Localization.AtPrime.isLocalRing (P := m))
  let f : R[X] →+* (Localization m.primeCompl)[X] :=
    Polynomial.mapRingHom (algebraMap R (Localization m.primeCompl))
  have hvS : IsUnimodular fun i => f (v i) := isUnimodular_map_ringHom f v hv
  have hloc0 : UnimodularVectorEquiv (fun i => f (v i)) (fun i => C ((f (v i)).eval 0)) :=
    cor9 (v := fun i => f (v i)) hvS (by simpa [f] using hmonic)
  have hev0 :
      (fun i => C ((f (v i)).eval 0)) = fun i => C (algebraMap R (Localization m.primeCompl) ((v i).eval 0)) := by
    funext i
    have : (f (v i)).eval 0 = algebraMap R (Localization m.primeCompl) ((v i).eval 0) := by
      simpa [f] using (Polynomial.eval_zero_map (algebraMap R (Localization m.primeCompl)) (v i))
    simp [this]
  simpa [hev0] using hloc0

omit [IsDomain R] in
/-- Local Horrocks step (unit leading coefficient): if a unimodular vector in `R[X]` has a
coordinate whose leading coefficient becomes a unit after localizing at a maximal ideal, then over
that localization we have `v(x) ∼ v(0)`. -/
theorem local_equiv_eval0_of_isUnit_leadingCoeff_localization (v : s → R[X]) (hv : IsUnimodular v)
    {m : Ideal R} (hm : m.IsMaximal)
    (hunit : ∃ i : s, IsUnit (((v i).map (algebraMap R (Localization m.primeCompl))).leadingCoeff)) :
    UnimodularVectorEquiv
      (fun i => (v i).map (algebraMap R (Localization m.primeCompl)))
      (fun i => C (algebraMap R (Localization m.primeCompl) ((v i).eval 0))) := by
  classical
  haveI : m.IsPrime := hm.isPrime
  haveI : IsLocalRing (Localization m.primeCompl) :=
    by simpa using (Localization.AtPrime.isLocalRing (P := m))
  let f : R[X] →+* (Localization m.primeCompl)[X] :=
    Polynomial.mapRingHom (algebraMap R (Localization m.primeCompl))
  let vS : s → (Localization m.primeCompl)[X] := fun i => f (v i)
  have hvS : IsUnimodular vS := isUnimodular_map_ringHom f v hv
  rcases hunit with ⟨i, hu⟩
  rcases hu with ⟨u, hu⟩
  let b : Localization m.primeCompl := (↑(u⁻¹) : Localization m.primeCompl)
  have hb : b * (vS i).leadingCoeff = 1 := by
    have : (vS i).leadingCoeff = (u : Localization m.primeCompl) := by
      simpa [vS, f] using hu.symm
    simp [b, this]
  have hmonic : (Polynomial.C b * vS i).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hb
  have hunitC : IsUnit (Polynomial.C b : (Localization m.primeCompl)[X]) := by
    have : IsUnit b := ⟨u⁻¹, rfl⟩
    simpa [Polynomial.isUnit_C] using this
  let vS' : s → (Localization m.primeCompl)[X] := Function.update vS i (Polynomial.C b * vS i)
  have hvv' : UnimodularVectorEquiv vS vS' :=
    unimodularVectorEquiv_update_mul_isUnit (R := Localization m.primeCompl) (s := s) i
      (Polynomial.C b) hunitC vS
  have hvS' : IsUnimodular vS' :=
    (isUnimodular_iff_of_unimodularVectorEquiv (R := Localization m.primeCompl) (s := s) hvv').1 hvS
  have hmonic' : ∃ j : s, (vS' j).Monic := by refine ⟨i, by simp [vS', hmonic]⟩
  let w0 : s → (Localization m.primeCompl)[X] := fun j => C ((vS j).eval 0)
  let w1 : s → (Localization m.primeCompl)[X] := fun j => C ((vS' j).eval 0)
  have hcor : UnimodularVectorEquiv vS' w1 := by simpa [w1] using cor9 vS' hvS' hmonic'
  have hw1 : w1 = Function.update w0 i (Polynomial.C b * w0 i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [mul_comm, Function.update_self, eval_mul, eval_C, map_mul, w1, vS', w0]
    · simp [w1, w0, vS', Function.update, hj]
  have hw0w1 : UnimodularVectorEquiv w0 w1 := by
    have :=
      unimodularVectorEquiv_update_mul_isUnit (R := Localization m.primeCompl) (s := s) i
        (Polynomial.C b) hunitC w0
    simpa [hw1] using this
  have hw1w0 : UnimodularVectorEquiv w1 w0 := unimodularVectorEquiv_equivalence.symm hw0w1
  have htotal : UnimodularVectorEquiv vS w0 :=
    unimodularVectorEquiv_equivalence.trans hvv' <|
      unimodularVectorEquiv_equivalence.trans hcor hw1w0
  have hev0 : w0 = fun j => C (algebraMap R (Localization m.primeCompl) ((v j).eval 0)) := by
    funext j
    have : (vS j).eval 0 = algebraMap R (Localization m.primeCompl) ((v j).eval 0) := by
      simpa [vS, f] using (Polynomial.eval_zero_map (algebraMap R (Localization m.primeCompl)) (v j))
    simp [w0, this]
  simpa [vS, f, hev0, w0] using htotal

/-- If `v ∼ w` and `w` has a coordinate with unit leading coefficient, then `v ∼ v(0)`. -/
theorem cor11_of_equiv_of_isUnit_leadingCoeff (v w : s → R[X]) (hv : IsUnimodular v)
    (hvw : UnimodularVectorEquiv v w) (hunit : ∃ i : s, IsUnit (w i).leadingCoeff) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  classical
  have hw : IsUnimodular w :=
    (isUnimodular_iff_of_unimodularVectorEquiv (R := R) (s := s) hvw).1 hv
  have hcor : UnimodularVectorEquiv w (fun i => C ((w i).eval 0)) :=
    cor11_of_isUnit_leadingCoeff (R := R) (s := s) w hw hunit
  let ev0 : R[X] →+* R := Polynomial.evalRingHom (R := R) 0
  have hev : UnimodularVectorEquiv (fun i => ev0 (v i)) (fun i => ev0 (w i)) :=
    by simpa [ev0] using unimodularVectorEquiv_map (s := s) ev0 hvw
  have hC :
      UnimodularVectorEquiv (fun i => C (ev0 (v i))) (fun i => C (ev0 (w i))) :=
    by simpa using unimodularVectorEquiv_map (s := s) (Polynomial.C : R →+* R[X]) hev
  have h0 : UnimodularVectorEquiv (fun i => C ((w i).eval 0)) (fun i => C ((v i).eval 0)) :=
    unimodularVectorEquiv_equivalence.symm (by simpa [ev0] using hC)
  exact unimodularVectorEquiv_equivalence.trans hvw <|
    unimodularVectorEquiv_equivalence.trans hcor h0

/-- If `w(x) ∼ w(0)` holds after localizing at every maximal ideal of `A`, then it holds globally;
combining with an equivalence for `w(0)` yields an equivalence for `w(x)`. -/
theorem unimodularVectorEquiv_stdBasis_of_forall_maximal_local (A : Type*) [CommRing A] [IsDomain A]
    (o : s) (w : s → Polynomial A)
    (hloc :
      ∀ m : Ideal A, [m.IsMaximal] →
        let Am := Localization m.primeCompl
        let ι : A →+* Am := algebraMap A Am
        UnimodularVectorEquiv (fun i => (w i).map ι) (fun i => C (ι ((w i).eval 0))))
    (h0 : UnimodularVectorEquiv (fun i => (w i).eval 0) (fun i : s => if i = o then 1 else 0)) :
    UnimodularVectorEquiv w (fun i : s => if i = o then 1 else 0) := by
  classical
  have hcor : UnimodularVectorEquiv w (fun i => C ((w i).eval 0)) :=
    cor11_of_forall_maximal_local_equiv (R := A) (s := s) w hloc
  have hmap :
      UnimodularVectorEquiv (fun i => C ((w i).eval 0))
        (fun i : s => if i = o then (1 : Polynomial A) else 0) := by
    have := unimodularVectorEquiv_map (s := s) (Polynomial.C : A →+* Polynomial A) h0
    simpa using this
  exact unimodularVectorEquiv_equivalence.trans hcor hmap

section monicize

variable {k : Type*} [Field k] {n : ℕ}

open scoped BigOperators

variable (f : MvPolynomial (Fin (n + 1)) k)

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

private lemma lt_up {v : Fin (n + 1) → ℕ} (vlt : ∀ i, v i < up) :
    ∀ l ∈ List.ofFn v, l < up := by
  intro l hl
  rcases ((List.mem_ofFn' v l).1 hl) with ⟨i, rfl⟩
  exact vlt i

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The triangular algebra endomorphism sending `X_i ↦ X_i + c * X_0^(r i)` for `i ≠ 0` and
fixing `X_0`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  MvPolynomial.aeval fun i ↦ if i = 0 then MvPolynomial.X 0 else MvPolynomial.X i + c • MvPolynomial.X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [MvPolynomial.comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp [T1, add_assoc, add_comm]

/-- `T1 f 1` leads to an algebra equivalence `T f`. -/
private noncomputable abbrev T :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1)) (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_neq {v w : Fin (n + 1) →₀ ℕ} (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up)
    (neq : v ≠ w) : (∑ x : Fin (n + 1), r x * v x) ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine neq <| Finsupp.ext <| congrFun <| (List.ofFn_inj.mp ?_)
  apply Nat.ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two) (by simp)
      (lt_up (f := f) vlt) (lt_up (f := f) wlt)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
      Fin.val_cast, mul_comm, List.sum_ofFn] using h

private lemma degreeOf_zero_t {v : Fin (n + 1) →₀ ℕ} {a : k} (ha : a ≠ 0) :
    ((T f) (MvPolynomial.monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← MvPolynomial.natDegree_finSuccEquiv, MvPolynomial.monomial_eq, Finsupp.prod_pow v fun a ↦ MvPolynomial.X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow, AlgEquiv.ofAlgHom_apply,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero, ite_false, one_smul,
    map_add, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (MvPolynomial.X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (Polynomial.leadingCoeff_ne_zero.mp <| by
      simp [add_comm, Polynomial.leadingCoeff_X_pow_add_C])
  rw [Polynomial.natDegree_mul (by simp [ha])
      (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i))),
    Polynomial.natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    Polynomial.natDegree_prod _ _ (fun i _ ↦ h i), MvPolynomial.natDegree_finSuccEquiv,
    MvPolynomial.degreeOf_C]
  simpa only [Polynomial.natDegree_pow, zero_add, Polynomial.natDegree_X, mul_one, Fin.val_zero,
      pow_zero, one_mul, add_right_inj] using
    Finset.sum_congr rfl (fun i _ ↦ by
      rw [add_comm (Polynomial.C _), Polynomial.natDegree_X_pow_add_C, mul_comm])

private lemma degreeOf_t_neq_of_neq {v w : Fin (n + 1) →₀ ℕ} (hv : v ∈ f.support) (hw : w ∈ f.support)
    (neq : v ≠ w) :
    (T f (MvPolynomial.monomial v (MvPolynomial.coeff v f))).degreeOf 0 ≠
      (T f (MvPolynomial.monomial w (MvPolynomial.coeff w f))).degreeOf 0 := by
  rw [degreeOf_zero_t (f := f) (a := MvPolynomial.coeff v f) (by exact (MvPolynomial.mem_support_iff.mp hv)),
    degreeOf_zero_t (f := f) (a := MvPolynomial.coeff w f) (by exact (MvPolynomial.mem_support_iff.mp hw))]
  refine sum_r_mul_neq (f := f) (v := v) (w := w) (fun i ↦ ?_) (fun i ↦ ?_) neq <;>
  · exact lt_of_le_of_lt ((MvPolynomial.monomial_le_degreeOf i ‹_›).trans (MvPolynomial.degreeOf_le_totalDegree f i))
      (by lia)

private lemma leadingCoeff_finSuccEquiv_t {v : Fin (n + 1) →₀ ℕ} :
    (MvPolynomial.finSuccEquiv k n (T f (MvPolynomial.monomial v (MvPolynomial.coeff v f)))).leadingCoeff =
      algebraMap k _ (MvPolynomial.coeff v f) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, Polynomial.leadingCoeff_C, map_pow,
      Polynomial.leadingCoeff_pow, MvPolynomial.algebraMap_eq]
    have : ∀ j, (MvPolynomial.finSuccEquiv k n ((T1 f) 1 (MvPolynomial.X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, MvPolynomial.finSuccEquiv_apply]
      · simp only [MvPolynomial.aeval_eq_bind₁, MvPolynomial.bind₁_X_right, if_neg h, one_smul,
          map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (MvPolynomial.finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f (MvPolynomial.monomial v (MvPolynomial.coeff v f))).degreeOf 0)
    (MvPolynomial.support_nonempty.mpr fne)
  set h := fun w ↦ MvPolynomial.monomial w (MvPolynomial.coeff w f)
  simp only [← MvPolynomial.natDegree_finSuccEquiv] at vs
  replace vs :
      ∀ x ∈ f.support \ {v},
        (MvPolynomial.finSuccEquiv k n (T f (h x))).degree <
          (MvPolynomial.finSuccEquiv k n (T f (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply Polynomial.degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [MvPolynomial.natDegree_finSuccEquiv] using
      degreeOf_t_neq_of_neq (f := f) (hv := h1) (hw := vin) (neq := by
        intro hxv
        exact h2 (Finset.mem_singleton.2 hxv))
  have coeff :
      (MvPolynomial.finSuccEquiv k n (T f (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
        (MvPolynomial.finSuccEquiv k n (T f (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply Polynomial.leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_)
    have h2 : h v ≠ 0 := by
      simpa [h] using (MvPolynomial.mem_support_iff.mp vin)
    have h2' : (MvPolynomial.finSuccEquiv k n (T f (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff (Ne.bot_lt (fun x ↦ h2' <| Polynomial.degree_eq_bot.mp x))).mpr vs
  nth_rw 2 [← MvPolynomial.support_sum_monomial_coeff f]
  rw [Finset.sum_eq_add_sum_diff_singleton vin h]
  rw [leadingCoeff_finSuccEquiv_t (f := f)] at coeff
  simpa only [coeff, MvPolynomial.algebraMap_eq] using (MvPolynomial.mem_support_iff.mp vin).isUnit.map MvPolynomial.C

/-- For a nonzero multivariable polynomial over a field, there exists an algebra automorphism which
makes its `finSuccEquiv` image have invertible leading coefficient (Nagata's trick). -/
theorem exists_algEquiv_isUnit_leadingCoeff_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) k) (fne : f ≠ 0) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (MvPolynomial.finSuccEquiv k n (e f)).leadingCoeff := by
  refine ⟨T f, ?_⟩
  simpa using T_leadingcoeff_isUnit (f := f) (n := n) fne

omit [DecidableEq s] in
/-- For a unimodular vector over `k[x₀,…,xₙ]` (with `k` a field), there exists an algebra
automorphism such that one component becomes a polynomial in `x₀` with invertible leading
coefficient, after identifying `k[x₀,…,xₙ] ≃ₐ[k] (k[x₁,…,xₙ])[X]` via `finSuccEquiv`. -/
theorem exists_algEquiv_exists_isUnit_leadingCoeff_finSuccEquiv (n : ℕ)
    (v : s → MvPolynomial (Fin (n + 1)) k) (hv : IsUnimodular v) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ∃ i : s, IsUnit (MvPolynomial.finSuccEquiv k n (e (v i))).leadingCoeff := by
  have h1 :
      (1 : MvPolynomial (Fin (n + 1)) k) ∈ Ideal.span (Set.range v) := by
    unfold IsUnimodular at hv
    simp [hv]
  rcases (Ideal.mem_span_range_iff_exists_fun).1 h1 with ⟨c, hc⟩
  have hex : ∃ i : s, v i ≠ 0 := by
    by_contra h0
    have hv0 : ∀ i : s, v i = 0 := by
      intro i
      by_contra hi
      exact h0 ⟨i, hi⟩
    have : (∑ i : s, c i * v i) = 0 := by simp [hv0]
    exact (one_ne_zero : (1 : MvPolynomial (Fin (n + 1)) k) ≠ 0) (by simpa [this] using hc.symm)
  rcases hex with ⟨i, hi⟩
  rcases exists_algEquiv_isUnit_leadingCoeff_finSuccEquiv (k := k) (n := n) (f := v i) hi with ⟨e, he⟩
  exact ⟨e, i, he⟩

omit [DecidableEq s] in
/-- Alias for `exists_algEquiv_exists_isUnit_leadingCoeff_finSuccEquiv`. This is the “monicization”
step in the proof sketch at the end of this file: in practice we first arrange that some component
has *invertible* leading coefficient in the distinguished variable. -/
theorem exists_algEquiv_exists_monic_finSuccEquiv (n : ℕ)
    (v : s → MvPolynomial (Fin (n + 1)) k) (hv : IsUnimodular v) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ∃ i : s, IsUnit (MvPolynomial.finSuccEquiv k n (e (v i))).leadingCoeff :=
  exists_algEquiv_exists_isUnit_leadingCoeff_finSuccEquiv (k := k) (s := s) (n := n) v hv

end monicize

/-- Field case of the “unimodular vector” theorem, with variables indexed by `Fin n`. -/
theorem thm12_fin {k : Type*} [Field k] (n : ℕ) (o : s) (v : s → MvPolynomial (Fin n) k)
    (hv : IsUnimodular v) : UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  classical
  induction n with
  | zero =>
    let e : MvPolynomial (Fin 0) k ≃+* k := MvPolynomial.isEmptyRingEquiv k (Fin 0)
    have hv' : IsUnimodular fun i => e (v i) := isUnimodular_map_ringEquiv e v hv
    have hstd : IsUnimodular fun i : s => if i = o then (1 : k) else 0 := by
      unfold IsUnimodular
      refine
        Ideal.eq_top_of_isUnit_mem
          (I := Ideal.span (Set.range fun i : s => if i = o then (1 : k) else 0)) (x := (1 : k)) ?_
          isUnit_one
      exact Ideal.subset_span ⟨o, by simp⟩
    have h' :
        UnimodularVectorEquiv (fun i => e (v i)) (fun i => if i = o then (1 : k) else 0) := by
      simpa using unimodularVectorEquiv_of_pid (R := k) (s := s) hv' hstd
    have h'' :
        UnimodularVectorEquiv v (fun i => if i = o then (1 : MvPolynomial (Fin 0) k) else 0) := by
      have := unimodularVectorEquiv_map_ringEquiv e.symm (fun i => e (v i))
        (fun i : s => if i = o then (1 : k) else 0) h'
      simpa using this
    simpa using h''
  | succ n ih =>
    let A := MvPolynomial (Fin n) k
    let φ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial A := MvPolynomial.finSuccEquiv k n
    rcases exists_algEquiv_exists_monic_finSuccEquiv (k := k) (s := s) (n := n) v hv with ⟨e, i, hu⟩
    let w : s → Polynomial A := fun j => φ (e (v j))
    have hw : IsUnimodular w := by
      have hv1 : IsUnimodular fun j => e (v j) := isUnimodular_map_ringEquiv e.toRingEquiv v hv
      simpa [w, φ] using isUnimodular_map_ringEquiv φ.toRingEquiv (fun j => e (v j)) hv1
    rcases hu with ⟨u, hu⟩
    let b : A := (↑(u⁻¹) : A)
    have hb : b * (w i).leadingCoeff = 1 := by
      have : (w i).leadingCoeff = (u : A) := by simpa [w, φ] using hu.symm
      simp [b, this]
    have hmonic : (Polynomial.C b * w i).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hb
    have hunitC : IsUnit (Polynomial.C b : Polynomial A) := by
      have : IsUnit b := ⟨u⁻¹, rfl⟩
      simpa [Polynomial.isUnit_C] using this
    let w' : s → Polynomial A := Function.update w i (Polynomial.C b * w i)
    have hww' : UnimodularVectorEquiv w w' :=
      unimodularVectorEquiv_update_mul_isUnit (R := A) (s := s) i (Polynomial.C b) hunitC w
    have hw' : IsUnimodular w' :=
      (isUnimodular_iff_of_unimodularVectorEquiv (R := A) (s := s) hww').1 hw
    have hmonic' : ∃ j : s, (w' j).Monic := by
      refine ⟨i, ?_⟩
      simp [w', hmonic]
    have hcor : UnimodularVectorEquiv w' (fun j => Polynomial.C ((w' j).eval 0)) :=
      cor11 (R := A) (s := s) w' hw' hmonic'
    let ev0 : Polynomial A →+* A := Polynomial.evalRingHom (R := A) 0
    let v0 : s → A := fun j => ev0 (w' j)
    have hv0 : IsUnimodular v0 := isUnimodular_map_ringHom ev0 w' hw'
    have hih : UnimodularVectorEquiv v0 (fun j => if j = o then (1 : A) else 0) := ih v0 hv0
    have hmap :
        UnimodularVectorEquiv (fun j => Polynomial.C (v0 j))
          (fun j : s => if j = o then (1 : Polynomial A) else 0) := by
      have := unimodularVectorEquiv_map (s := s) (Polynomial.C : A →+* Polynomial A) hih
      simpa [v0] using this
    have hcor' : UnimodularVectorEquiv w' (fun j : s => if j = o then (1 : Polynomial A) else 0) := by
      have hcor0 : UnimodularVectorEquiv w' (fun j => Polynomial.C (v0 j)) := by
        simpa [v0, ev0] using hcor
      exact unimodularVectorEquiv_equivalence.trans hcor0 hmap
    have hwstd : UnimodularVectorEquiv w (fun j : s => if j = o then (1 : Polynomial A) else 0) :=
      unimodularVectorEquiv_equivalence.trans hww' hcor'
    have h' :
        UnimodularVectorEquiv (fun j => e (v j))
          (fun j : s => if j = o then (1 : MvPolynomial (Fin (n + 1)) k) else 0) := by
      let φr : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial A := φ.toRingEquiv
      have := unimodularVectorEquiv_map_ringEquiv φr.symm w
        (fun j : s => if j = o then (1 : Polynomial A) else 0) hwstd
      have hcomp : (fun j => φr.symm (w j)) = fun j => e (v j) := by
        funext j
        simpa [w, φr] using φr.symm_apply_apply (e (v j))
      simpa [hcomp] using this
    have h'' :
        UnimodularVectorEquiv v (fun j : s => if j = o then (1 : MvPolynomial (Fin (n + 1)) k) else 0) := by
      let er : MvPolynomial (Fin (n + 1)) k ≃+* MvPolynomial (Fin (n + 1)) k := e.toRingEquiv
      have := unimodularVectorEquiv_map_ringEquiv er.symm (fun j => er (v j))
        (fun j : s => if j = o then (1 : MvPolynomial (Fin (n + 1)) k) else 0) h'
      have hcomp : (fun j => er.symm (er (v j))) = v := by
        funext j
        simpa [er] using er.symm_apply_apply (v j)
      simpa [hcomp] using this
    simpa using h''

/-- Let `k` be a field and `σ` a finite set of variables. Any unimodular vector in `k[σ]` is
equivalent to a standard basis vector. -/
theorem thm12_field {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (o : s) (v : s → MvPolynomial σ k) (hv : IsUnimodular v) :
    UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  classical
  let n : ℕ := Fintype.card σ
  let eσ : σ ≃ Fin n := Fintype.equivFin σ
  let ρ : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.renameEquiv k eσ
  let v' : s → MvPolynomial (Fin n) k := fun i => ρ (v i)
  have hv' : IsUnimodular v' := isUnimodular_map_ringEquiv ρ.toRingEquiv v hv
  have h' : UnimodularVectorEquiv v' (fun i : s => if i = o then 1 else 0) := thm12_fin n o v' hv'
  have := unimodularVectorEquiv_map_ringEquiv ρ.symm.toRingEquiv v'
    (fun i : s => if i = o then 1 else 0) h'
  simpa [v', ρ] using this

end thm12_field

section thm12_pid

variable {k : Type*} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
variable {s : Type*} [Fintype s] [DecidableEq s]

/-
Note: `Fintype s` is in scope for later theorems in this section, but not needed for the next
lemma. We explicitly omit it to avoid linter warnings about unused section variables.
-/
omit [Fintype s] in
/-- The standard basis vector `e_o` is unimodular. -/
theorem isUnimodular_stdBasis (R : Type*) [CommRing R] (o : s) :
    IsUnimodular (fun i : s => if i = o then (1 : R) else 0) := by
  unfold IsUnimodular
  refine
    Ideal.eq_top_of_isUnit_mem
      (I := Ideal.span (Set.range fun i : s => if i = o then (1 : R) else 0)) (x := (1 : R)) ?_
      isUnit_one
  exact Ideal.subset_span ⟨o, by simp⟩

def MonicAtMaximals : Prop :=
  ∀ n : ℕ,
    ∀ w : s → Polynomial (MvPolynomial (Fin n) k),
      IsUnimodular w →
        ∀ m : Ideal (MvPolynomial (Fin n) k),
          (hm : m.IsMaximal) →
            ∃ w' : s → Polynomial (Localization m.primeCompl),
              UnimodularVectorEquiv
                  (fun i =>
                    Polynomial.mapRingHom
                        (algebraMap (MvPolynomial (Fin n) k) (Localization m.primeCompl)) (w i))
                  w' ∧
                ∃ i : s, IsUnit (w' i).leadingCoeff

theorem thm12_pid_fin (H : MonicAtMaximals (k := k) (s := s)) (n : ℕ) (o : s)
    (v : s → MvPolynomial (Fin n) k) (hv : IsUnimodular v) :
    UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  classical
  induction n with
  | zero =>
      let e : MvPolynomial (Fin 0) k ≃+* k := MvPolynomial.isEmptyRingEquiv k (Fin 0)
      have hv' : IsUnimodular fun i => e (v i) := isUnimodular_map_ringEquiv e v hv
      have hstd : IsUnimodular fun i : s => if i = o then (1 : k) else 0 := by
        unfold IsUnimodular
        refine
          Ideal.eq_top_of_isUnit_mem
            (I := Ideal.span (Set.range fun i : s => if i = o then (1 : k) else 0)) (x := (1 : k)) ?_
            isUnit_one
        exact Ideal.subset_span ⟨o, by simp⟩
      have h' :
          UnimodularVectorEquiv (fun i => e (v i)) (fun i : s => if i = o then (1 : k) else 0) := by
        simpa using unimodularVectorEquiv_of_pid (R := k) (s := s) hv' hstd
      have h'' :
          UnimodularVectorEquiv v (fun i : s => if i = o then (1 : MvPolynomial (Fin 0) k) else 0) := by
        have := unimodularVectorEquiv_map_ringEquiv e.symm (fun i => e (v i))
          (fun i : s => if i = o then (1 : k) else 0) h'
        simpa using this
      simpa using h''
  | succ n ih =>
      let A := MvPolynomial (Fin n) k
      let φ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial A := MvPolynomial.finSuccEquiv k n
      let w : s → Polynomial A := fun j => φ (v j)
      have hw : IsUnimodular w := isUnimodular_map_ringEquiv φ.toRingEquiv v hv
      have hloc :
          ∀ m : Ideal A, [m.IsMaximal] →
            let Am := Localization m.primeCompl
            let ι : A →+* Am := algebraMap A Am
            UnimodularVectorEquiv (fun i => (w i).map ι) (fun i => C (ι ((w i).eval 0))) := by
        intro m hm
        classical
        haveI : m.IsPrime := hm.isPrime
        let Am := Localization m.primeCompl
        let ι : A →+* Am := algebraMap A Am
        let f : Polynomial A →+* Polynomial Am := Polynomial.mapRingHom ι
        rcases H n w hw m hm with ⟨w', hwvw', hunit⟩
        have hwS : IsUnimodular fun i : s => f (w i) := by
          classical
          unfold IsUnimodular at hw ⊢
          refine
            Ideal.eq_top_of_isUnit_mem
              (I := Ideal.span (Set.range fun i : s => f (w i))) (x := (1 : Polynomial Am)) ?_
              isUnit_one
          have h1 : (1 : Polynomial A) ∈ Ideal.span (Set.range w) := by
            simp [hw]
          rcases (Ideal.mem_span_range_iff_exists_fun).1 h1 with ⟨c, hc⟩
          refine (Ideal.mem_span_range_iff_exists_fun).2 ?_
          refine ⟨fun i : s => f (c i), ?_⟩
          have hc' := congrArg f hc
          simpa [map_sum, map_mul] using hc'
        have hwSw' : UnimodularVectorEquiv (fun i => f (w i)) w' := by simpa [f] using hwvw'
        have hcor :
            UnimodularVectorEquiv (fun i => f (w i)) (fun i => C ((f (w i)).eval 0)) :=
          cor11_of_equiv_of_isUnit_leadingCoeff (R := Am) (s := s)
            (fun i => f (w i)) w' hwS hwSw' hunit
        have hev0 : (fun i : s => C ((f (w i)).eval 0)) = fun i => C (ι ((w i).eval 0)) := by
          funext i
          have : (f (w i)).eval 0 = ι ((w i).eval 0) := by
            simp [f]
          simp [this]
        have hcor' :
            UnimodularVectorEquiv (fun i => f (w i)) (fun i => C (ι ((w i).eval 0))) := by
          have hcor0 := hcor
          rw [hev0] at hcor0
          exact hcor0
        change UnimodularVectorEquiv (fun i : s => f (w i)) (fun i => C (ι ((w i).eval 0)))
        exact hcor'
      let ev0 : Polynomial A →+* A := Polynomial.evalRingHom (R := A) 0
      let v0 : s → A := fun j => ev0 (w j)
      have hv0 : IsUnimodular v0 := isUnimodular_map_ringHom ev0 w hw
      have h0 : UnimodularVectorEquiv v0 (fun j : s => if j = o then (1 : A) else 0) := ih v0 hv0
      have hwstd : UnimodularVectorEquiv w (fun j : s => if j = o then (1 : Polynomial A) else 0) :=
        unimodularVectorEquiv_stdBasis_of_forall_maximal_local (A := A) (s := s) o w hloc h0
      let φr : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial A := φ
      have := unimodularVectorEquiv_map_ringEquiv φr.symm w
        (fun j : s => if j = o then (1 : Polynomial A) else 0) hwstd
      have hcomp : (fun j : s => φr.symm (w j)) = v := by
        funext j
        simpa [w, φr] using φr.symm_apply_apply (v j)
      simpa [hcomp] using this

theorem thm12_pid (H : MonicAtMaximals (k := k) (s := s)) {σ : Type*} [Fintype σ] [DecidableEq σ]
    (o : s) (v : s → MvPolynomial σ k) (hv : IsUnimodular v) :
    UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  classical
  let n : ℕ := Fintype.card σ
  let eσ : σ ≃ Fin n := Fintype.equivFin σ
  let ρ : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.renameEquiv k eσ
  let v' : s → MvPolynomial (Fin n) k := fun i => ρ (v i)
  have hv' : IsUnimodular v' := isUnimodular_map_ringEquiv ρ.toRingEquiv v hv
  have h' : UnimodularVectorEquiv v' (fun i : s => if i = o then 1 else 0) :=
    thm12_pid_fin (k := k) (s := s) H n o v' hv'
  have := unimodularVectorEquiv_map_ringEquiv ρ.symm.toRingEquiv v'
    (fun i : s => if i = o then 1 else 0) h'
  simpa [v', ρ] using this

theorem thm12 (o : s) {σ : Type*} [Fintype σ] [DecidableEq σ] (v : s → MvPolynomial σ k)
    (hv : IsUnimodular v) : UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  sorry

end thm12_pid

/-
\begin{definition}
	Let $A$ be any ring. A vector ${v} \in A^s$ is unimodular if its components generate the unit ideal in $A$. For two unimodular vectors ${v}, {w}$, we write
	$$\displaystyle {v} \sim {w}$$
	if there is a matrix $M \in \mathrm{GL}_s(A)$ such that $M {v} = {w}$. This is clearly an equivalence relation.
\end{definition}

\begin{proposition}\label{prop:6}
	Over a principal ideal domain $R$, any two unimodular vectors are equivalent.
\end{proposition}

\begin{theorem}[Horrocks]\label{thm:8}
	Let $A = R[x]$ for $(R, \mathfrak{m})$ a local ring. Then any unimodular vector in $A^s$ one of whose elements has leading coefficient one is equivalent to $e_1$.
\end{theorem}

\begin{corollary}\label{cor:9}
	If $R$ is local and $v(x) \in R[x]^s$ is a unimodular vector one of whose elements is monic, then $v(x) \sim v(0)$.
\end{corollary}

\begin{lemma}\label{lem:10}
	Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such that $v(x) \sim v(x + cy)$ over $R[x, y]$.
\end{lemma}

\begin{corollary}\label{cor:11}
	Suppose $R$ is any ring, and $v(x) \in R[x]^s$ is a unimodular vector one of whose leading coefficients is one. Then $v(x) \sim v(0)$.
\end{corollary}

\begin{theorem}\label{thm:12}
	Let $R = k[x_1, \dots, x_n]$ be a polynomial ring over a principal ideal domain $k$, and let $v \in R^n$ be a unimodular vector. Then $v \sim e_1$.
\end{theorem}

\begin{proof}
	We can now prove this by induction on $n$. When $n = 0$, it is immediate [by Proposition \ref{prop:6}].

	Suppose $n \geq 1$. Then we can treat $R$ as $k[x_1, \dots, x_{n-1}, X]$, where we replace $x_n$ by $X$ to make it stand out. We can think of $v = v(X)$ as a vector of polynomials in $X$ with coefficients in the smaller ring $k[x_1, \dots, x_{n-1}]$.

	If $v(X)$ has a term with leading coefficient one, then the previous results [Corollary \ref{cor:11}] enable us to conclude that $v(X) \sim v(0)$, and as $v(0)$ lies in $k[x_1, \dots, x_{n-1}]$ we can use induction to work downwards. The claim is that, possibly after a change of variables $x_1, \dots, x_n$, we can always arrange it so that the leading coefficient in $X = x_n$ is one. The relevant change of variables leaves $X = x_n$ constant and
	\[ \displaystyle x_i \mapsto x_i - X^{M^i}, \quad M \gg 0 \quad (1 \leq i < n). \]
	If $M$ is chosen very large, one makes by this substitution the leading term of each of the elements of $v$ a unit. So, without loss of generality we can assume that this is already the case. Thus, we can apply the inductive hypothesis on $n$ to complete the proof.
\end{proof}

-/
