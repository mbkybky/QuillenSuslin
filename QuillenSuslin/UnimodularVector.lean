import QuillenSuslin.Horrocks
import QuillenSuslin.BivariatePolynomial

open Module Polynomial Finset BigOperators Bivariate

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]

open Bivariate in
/-- Suppose $v(x) \sim v(0)$ over the localization $R_S[x]$. Then there exists a $c \in S$ such
  that $v(x) \sim v(x + cy)$ over $R[x, y]$. -/
theorem lem10 [IsDomain R] {S : Submonoid R} (hs : S ≤ nonZeroDivisors R) (v : s → R[X])
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

/-- Suppose $R$ is any ring, and $v(x) \in R[x]^s$ is a unimodular vector one of whose
  leading coefficients is one. Then $v(x) \sim v(0)$. -/
theorem cor11 (v : s → R[X]) (hv : IsUnimodular v) (h : ∃ i : s, (v i).Monic) :
    UnimodularVectorEquiv v (fun i => C ((v i).eval 0)) := by
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
