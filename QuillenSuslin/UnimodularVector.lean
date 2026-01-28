import QuillenSuslin.Horrocks
import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R] [IsDomain R]
variable {s : Type*} [Fintype s] [DecidableEq s]

open Bivariate in
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

end cor11

/-- Let $R = k[x_1, \dots, x_n]$ be a polynomial ring over a principal ideal domain $k$, and let
  $v \in R^n$ be a unimodular vector. Then $v \sim e_1$.. -/
theorem thm12 (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {s : Type*} [Fintype s]
    [DecidableEq s] (o : s) (v : s → MvPolynomial s R) (hv : IsUnimodular v) :
    UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  sorry

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
