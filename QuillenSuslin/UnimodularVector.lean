import QuillenSuslin.Horrocks
import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R] [IsDomain R]
variable {s : Type*} [Fintype s] [DecidableEq s]

set_option maxHeartbeats 20000000

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

noncomputable section

/-- The ring hom `R →+* R[X][Y]` used in Corollary 11, sending `r` to `C (C r)`. -/
abbrev cor11ι : R →+* R[X][Y] := (C : R[X] →+* R[X][Y]).comp (C : R →+* R[X])

/-- The vector `v` seen in `R[X][Y]` via `C : R[X] →+* R[X][Y]`. -/
abbrev cor11vx (v : s → R[X]) : s → R[X][Y] := fun i => C (v i)

/-- The vector `v(x + qy)` in `R[X][Y]`. -/
abbrev cor11vxy (v : s → R[X]) (q : R) : s → R[X][Y] :=
  fun i => (v i).eval₂ cor11ι (C X + q • Y)

/-- For `R[X][Y]`, `algebraMap` agrees with `cor11ι`. -/
lemma cor11_hAlg : algebraMap R R[X][Y] = cor11ι := by
  ext r
  simp [cor11ι]

/-- Push a unimodular-vector equivalence along a ring homomorphism. -/
theorem unimodularVectorEquiv_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {v w : s → A} (hvw : UnimodularVectorEquiv (R := A) (s := s) v w) :
    UnimodularVectorEquiv (R := B) (s := s) (fun i => f (v i)) (fun i => f (w i)) := by
  rcases hvw with ⟨M, hM⟩
  refine ⟨Matrix.GeneralLinearGroup.map (n := s) (R := A) (S := B) f M, ?_⟩
  ext i
  have hi : (M.1.mulVec v) i = w i := congrArg (fun u : s → A => u i) hM
  have hi' : f ((M.1.mulVec v) i) = f (w i) := congrArg f hi
  have hmap : (M.1.map f).mulVec (fun j => f (v j)) i = f ((M.1.mulVec v) i) := by
    simpa [Function.comp] using (RingHom.map_mulVec f M.1 v i).symm
  simpa [Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply] using hmap.trans hi'

/-- The ideal of `q : R` such that `v(x + qy) ∼ v(x)` in `R[X][Y]`. -/
def cor11IdealCarrier (v : s → R[X]) : Set R :=
  {q | UnimodularVectorEquiv (R := R[X][Y]) (s := s) (cor11vx v) (cor11vxy v q)}

/-- `0 ∈ cor11IdealCarrier v`. -/
lemma cor11Ideal_zero_mem (v : s → R[X]) : (0 : R) ∈ cor11IdealCarrier (R := R) (s := s) v := by
  have hC :
      (Polynomial.eval₂RingHom cor11ι (C X) : R[X] →+* R[X][Y]) = (C : R[X] →+* R[X][Y]) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · ext r
      simp [cor11ι]
    · simp [cor11ι]
  have h0 : cor11vxy (R := R) (s := s) v 0 = cor11vx (R := R) (s := s) v := by
    funext i
    have := congrArg (fun f : R[X] →+* R[X][Y] => f (v i)) hC
    simpa [cor11vxy, cor11vx] using this
  simpa [cor11IdealCarrier, h0] using
    (unimodularVectorEquiv_equivalence (R := R[X][Y]) (s := s)).refl (cor11vx v)

/-- `cor11IdealCarrier v` is closed under addition. -/
lemma cor11Ideal_add_mem (v : s → R[X]) {a b : R} (ha : a ∈ cor11IdealCarrier (R := R) (s := s) v)
    (hb : b ∈ cor11IdealCarrier (R := R) (s := s) v) :
    a + b ∈ cor11IdealCarrier (R := R) (s := s) v := by
  let shift : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom cor11ι (C X + b • Y)) Y
  have hx : (fun i : s => shift (cor11vx (R := R) (s := s) v i)) = cor11vxy (R := R) (s := s) v b := by
    funext i
    dsimp [shift, cor11vx, cor11vxy]
    simp
  have hxy :
      (fun i : s => shift (cor11vxy (R := R) (s := s) v a i)) =
        cor11vxy (R := R) (s := s) v (a + b) := by
    funext i
    have hcoeff : shift.comp cor11ι = cor11ι := by
      ext r
      dsimp [shift, cor11ι]
      simp [coe_eval₂RingHom, eval₂_C]
    have hCX : shift (C X) = C X + b • Y := by
      dsimp [shift]
      simp [coe_eval₂RingHom, eval₂_C, eval₂_X]
    have hY : shift Y = Y := by
      dsimp [shift]
      simp [coe_eval₂RingHom, eval₂_X]
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
      calc shift (C X + a • Y) = shift (C X) + shift (a • Y) := by simp
        _ = (C X + b • Y) + a • Y := by simp [hCX, haY]
        _ = C X + (a + b) • Y := by simp [add_assoc, add_left_comm, add_comm, add_smul]
    have := Polynomial.hom_eval₂ (f := cor11ι) (g := shift) (p := v i) (x := C X + a • Y)
    simpa [cor11vxy, hcoeff, hX] using this
  have hab :
      UnimodularVectorEquiv (R := R[X][Y]) (s := s) (cor11vxy (R := R) (s := s) v b)
        (cor11vxy (R := R) (s := s) v (a + b)) := by
    have ha' :
        UnimodularVectorEquiv (R := R[X][Y]) (s := s) (cor11vx (R := R) (s := s) v)
          (cor11vxy (R := R) (s := s) v a) := ha
    have hmap := unimodularVectorEquiv_map (A := R[X][Y]) (B := R[X][Y]) shift ha'
    simpa [hx, hxy] using hmap
  have hb' :
      UnimodularVectorEquiv (R := R[X][Y]) (s := s) (cor11vx (R := R) (s := s) v)
        (cor11vxy (R := R) (s := s) v b) := hb
  exact (unimodularVectorEquiv_equivalence (R := R[X][Y]) (s := s)).trans hb' hab

/-- `cor11IdealCarrier v` is closed under scalar multiplication (i.e. multiplication in `R`). -/
lemma cor11Ideal_smul_mem (v : s → R[X]) (r : R) {a : R} (ha : a ∈ cor11IdealCarrier (R := R) (s := s) v) :
    r * a ∈ cor11IdealCarrier (R := R) (s := s) v := by
  let scaleY : R[X][Y] →+* R[X][Y] :=
    Polynomial.eval₂RingHom (C : R[X] →+* R[X][Y]) (r • Y)
  have hx : (fun i : s => scaleY (cor11vx (R := R) (s := s) v i)) = cor11vx (R := R) (s := s) v := by
    funext i
    dsimp [scaleY, cor11vx]
    simp [coe_eval₂RingHom, eval₂_C]
  have hxy :
      (fun i : s => scaleY (cor11vxy (R := R) (s := s) v a i)) =
        cor11vxy (R := R) (s := s) v (r * a) := by
    funext i
    have hcoeff : scaleY.comp cor11ι = cor11ι := by
      ext x
      dsimp [scaleY, cor11ι]
      simp [coe_eval₂RingHom, eval₂_C]
    have hCX : scaleY (C X) = C X := by
      dsimp [scaleY]
      simp [coe_eval₂RingHom, eval₂_C]
    have hY : scaleY Y = r • Y := by
      dsimp [scaleY]
      simp [coe_eval₂RingHom, eval₂_X]
    have hιa : scaleY (cor11ι a) = cor11ι a := by
      have := congrArg (fun f : R →+* R[X][Y] => f a) hcoeff
      simpa [RingHom.comp_apply] using this
    have hYa : scaleY (a • Y) = (r * a) • Y := by
      have hιr : (r : R) • Y = cor11ι r * Y := by simp [Algebra.smul_def, cor11_hAlg, cor11ι]
      calc scaleY (a • Y) = scaleY (cor11ι a * Y) := by simp [Algebra.smul_def, cor11_hAlg, cor11ι]
        _ = scaleY (cor11ι a) * scaleY Y := by simp
        _ = scaleY (cor11ι a) * (r • Y) := by simp [hY]
        _ = cor11ι a * (r • Y) := by rw [hιa]
        _ = cor11ι a * (cor11ι r * Y) := by simp [hιr]
        _ = (cor11ι a * cor11ι r) * Y := by simp [mul_assoc]
        _ = cor11ι (a * r) * Y := by simpa [map_mul]
        _ = cor11ι (r * a) * Y := by simpa [mul_comm]
        _ = (r * a) • Y := by simp [Algebra.smul_def, cor11_hAlg, cor11ι]
    have hX : scaleY (C X + a • Y) = C X + (r * a) • Y := by
      simpa [map_add, hCX, hYa]
    have := Polynomial.hom_eval₂ (f := cor11ι) (g := scaleY) (p := v i) (x := C X + a • Y)
    simpa [cor11vxy, hcoeff, hX] using this
  have hmap := unimodularVectorEquiv_map (A := R[X][Y]) (B := R[X][Y]) scaleY ha
  simpa [cor11IdealCarrier, hx, hxy] using hmap

/-- The ideal `I` appearing in the proof of Corollary 11. -/
def cor11Ideal (v : s → R[X]) : Ideal R :=
  { carrier := cor11IdealCarrier (R := R) (s := s) v
    zero_mem' := cor11Ideal_zero_mem (R := R) (s := s) v
    add_mem' := cor11Ideal_add_mem (R := R) (s := s) v
    smul_mem' := cor11Ideal_smul_mem (R := R) (s := s) v }

/-- In Corollary 11, the ideal `I` is the unit ideal. -/
theorem cor11Ideal_eq_top (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    cor11Ideal (R := R) (s := s) v = ⊤ := by
  classical
  let I : Ideal R := cor11Ideal (R := R) (s := s) v
  by_contra hI'
  rcases Ideal.exists_le_maximal I hI' with ⟨m, hm, hIm⟩
  let S : Submonoid R := Ideal.primeCompl m
  have hS0 : (0 : R) ∉ S := by simpa [S, Ideal.primeCompl] using (show (0 : R) ∈ m from m.zero_mem)
  have hs : S ≤ nonZeroDivisors R := le_nonZeroDivisors_of_noZeroDivisors (M₀ := R) hS0
  let vS : s → (Localization S)[X] := fun i => (v i).map (algebraMap R (Localization S))
  have hvS : IsUnimodular vS := by
    have h1 : (1 : R[X]) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
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
    letI : m.IsPrime := this
    simpa [S, Localization.AtPrime] using (Localization.AtPrime.isLocalRing (P := m))
  letI : IsLocalRing (Localization S) := this
  have hloc :
      UnimodularVectorEquiv (R := (Localization S)[X]) (s := s) vS
        (fun i => C (algebraMap R (Localization S) ((v i).eval 0))) := by
    have hcor9 :
        UnimodularVectorEquiv (R := (Localization S)[X]) (s := s) vS (fun i => C ((vS i).eval 0)) :=
      cor9 vS hvS hmonicS
    have hev0 : (fun i => C ((vS i).eval 0)) = fun i => C (algebraMap R (Localization S) ((v i).eval 0)) := by
      funext i
      have : (vS i).eval 0 = algebraMap R (Localization S) ((v i).eval 0) := by
        simpa [vS] using (Polynomial.eval_zero_map (algebraMap R (Localization S)) (v i))
      simpa [this]
    simpa [hev0] using hcor9
  rcases lem10 (hs := hs) (v := v) hloc with ⟨c, hc⟩
  have hcI : (c : R) ∈ I := hc
  have hc_not_mem : (c : R) ∉ m := c.2
  exact hc_not_mem (hIm hcI)

/-- Suppose $R$ is any ring, and $v(x) \in R[x]^s$ is a unimodular vector one of whose
  leading coefficients is one. Then $v(x) \sim v(0)$. -/
theorem cor11 (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
  classical
  let ι : R →+* R[X][Y] := cor11ι (R := R)
  let vx : s → R[X][Y] := cor11vx (R := R) (s := s) v
  let vxy : R → s → R[X][Y] := fun q => cor11vxy (R := R) (s := s) v q
  let I : Ideal R := cor11Ideal (R := R) (s := s) v
  have hI : I = ⊤ := cor11Ideal_eq_top (R := R) (s := s) v hv h
  have h1 : (1 : R) ∈ I := by simpa [hI] using (show (1 : R) ∈ (⊤ : Ideal R) from by simp)
  have hI1 : UnimodularVectorEquiv (R := R[X][Y]) (s := s) vx (vxy 1) := h1
  let ev0 : R[X] →+* R[X] := Polynomial.eval₂RingHom (C : R →+* R[X]) 0
  let evXY : R[X][Y] →+* R[X] := Polynomial.eval₂RingHom ev0 X
  have hev0 (i : s) : ev0 (v i) = C ((v i).eval 0) := by
    simp [ev0, Polynomial.coeff_zero_eq_eval_zero]
  have hevXY_vx : (fun i => evXY (vx i)) = fun i => C ((v i).eval 0) := by
    funext i
    simpa [vx, evXY, ev0, hev0 i] using (show evXY (C (v i)) = C ((v i).eval 0) from by simp)
  have hevXY_vxy : (fun i => evXY (vxy 1 i)) = v := by
    funext i
    have hcoeff : evXY.comp ι = (C : R →+* R[X]) := by
      ext r
      simp [evXY, ev0, ι]
    have hX : evXY (C X + Y) = X := by simp [evXY, ev0]
    have hhom := Polynomial.hom_eval₂ (f := ι) (g := evXY) (p := v i) (x := C X + Y)
    have : evXY (vxy 1 i) = (v i).eval₂ (C : R →+* R[X]) X := by
      simpa [cor11vxy, vxy, ι, one_smul, hcoeff, hX] using hhom
    simpa [Polynomial.eval₂_C_X] using this
  have hmap : UnimodularVectorEquiv (R := R[X]) (s := s)
      (fun i => evXY (vx i)) (fun i => evXY (vxy 1 i)) := unimodularVectorEquiv_map evXY hI1
  have hmain :
      UnimodularVectorEquiv (R := R[X]) (s := s) (fun i => C ((v i).eval 0)) v := by
    simpa [hevXY_vx, hevXY_vxy] using hmap
  exact (unimodularVectorEquiv_equivalence (R := R[X]) (s := s)).symm hmain

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

\begin{proof}
	Let us consider the set $I$ of $q \in R$ such that $v(x+qy) \sim v(x)$ in $R[x, y]$. If we can show that $1 \in I$, then we will be done, because after applying the homomorphism $x \mapsto 0, R[x, y] \rightarrow R[y]$, we will get that $v(y) \sim v(0)$ in $R[y]$.

	We start by observing that $I$ is an ideal. In fact, suppose $v(x+qy) \sim v(x)$ and $v(x + q'y) \sim v(x)$. Then, substituting $x \mapsto x + q'y$ in the first leads to
	\[ \displaystyle v(x + q'y + qy) \sim v(x + q'y) \in R[x,y] \]
	and since $v(x + q'y) \sim v(x)$, we get easily by transitivity that $q + q' \in I$. Similarly, we have to observe that if $q \in I$ and $r \in R$, then $v(x+qry) \sim v(x)$. But this is true because one can substitute $y \mapsto ry$.

	Since $I$ is an ideal, to show that $1 \in I$ we just need to show that $I$ is contained in no maximal ideal. Let $\mathfrak{m} \subset R$ be a maximal ideal. We then note that, by what we have already done for local rings [Corollary \ref{cor:9}], we have that
	\[ \displaystyle v(x) \sim v(0 ) \quad \text{in} \quad R_{\mathfrak{m}}[x]. \]
	By Lemma \ref{lem:10}, this means that there is a $q \in R - \mathfrak{m}$ such that $v(x+qy) \sim v(0)$; this means that $q \in I$. So $I$ cannot be contained in $\mathfrak{m}$. Since this applies to any maximal ideal $\mathfrak{m}$, it follows that $I$ must be the unit ideal.
\end{proof}

-/
