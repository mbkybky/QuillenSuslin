import Mathlib

open Module

section

variable {R : Type*} [CommRing R]
variable {s : Type*} [Fintype s] [DecidableEq s]

/-- A vector `v : s → R` is *unimodular* if its components generate the unit ideal. -/
def IsUnimodular (v : s → R) : Prop := Ideal.span (Set.range v) = ⊤

/-- Two vectors `v w : s → R` are equivalent if they differ by left multiplication by an element
of `GL s R`. -/
def UnimodularVectorEquiv (v w : s → R) : Prop :=
  ∃ M : Matrix.GeneralLinearGroup s R, M.1.mulVec v = w

/-- `UnimodularVectorEquiv` is an equivalence relation. -/
theorem unimodularVectorEquiv_equivalence :
    Equivalence (UnimodularVectorEquiv (R := R) (s := s)) := by
  refine ⟨fun v ↦ ⟨1, by simp⟩, ?_, ?_⟩
  · intro v w h
    rcases h with ⟨M, hM⟩
    refine ⟨M⁻¹, ?_⟩
    calc _ = (M⁻¹).1.mulVec (M.1.mulVec v) := by simp [hM]
      _ = v := by simp
  · intro a b c ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨N * M, ?_⟩
    calc _ = N.1.mulVec (M.1.mulVec a) := by simp
      _ = c := by simp [hM, hN]

/-- Over a principal ideal domain, any two unimodular vectors are equivalent. -/
theorem unimodularVectorEquiv_of_pid [IsDomain R] [IsPrincipalIdealRing R]
    {v w : s → R} (hv : IsUnimodular v) (hw : IsUnimodular w) :
    UnimodularVectorEquiv v w := by
  -- Build, from `hu : IsUnimodular u`, a basis of `s → R` whose first basis vector is `u`.
  have buildBasis {u : s → R} (hu : IsUnimodular u) :
      Σ n : ℕ, { b : Basis (Sum (Fin 1) (Fin n)) R (s → R) // b (Sum.inl 0) = u } := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range u) := by
      rw [hu]
      exact Submodule.mem_top
    have hex : ∃ c : s → R, (∑ i, c i * u i) = 1 := Ideal.mem_span_range_iff_exists_fun.1 h1
    let c : s → R := Classical.choose hex
    have hc : (∑ i, c i * u i) = 1 := Classical.choose_spec hex
    let φ : (s → R) →ₗ[R] R :=
      { toFun := fun x => ∑ i, c i * x i
        map_add' _ _ := by
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' _ _ := by
          simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_comm] }
    let f : R →ₗ[R] (s → R) :=
      { toFun := fun r => r • u
        map_add' _ _ := by
          simp [add_smul]
        map_smul' _ _ := by
          simp [mul_smul] }
    have hφf : ∀ r : R, φ (f r) = r := by
      intro r
      calc
        _ = r * (∑ i : s, c i * u i) := by
          simp [φ, f, smul_eq_mul, mul_comm, Finset.mul_sum]
        _ = r := by simp [hc]
    have hf_inj : Function.Injective f := by
      intro a b hab
      simpa [hφf a, hφf b] using congrArg φ hab
    let p : Submodule R (s → R) := LinearMap.range f
    let proj : (s → R) →ₗ[R] p :=
      { toFun := fun x => ⟨f (φ x), ⟨φ x, rfl⟩⟩
        map_add' _ _ := by
          ext
          simp
        map_smul' _ _ := by
          ext
          simp [f, Pi.smul_apply, smul_eq_mul, mul_assoc] }
    have hproj : ∀ x : p, proj x = x := by
      rintro ⟨x, ⟨r, rfl⟩⟩
      ext
      simp [proj, hφf r]
    have bqSigma : Σ n : ℕ, Basis (Fin n) R (LinearMap.ker proj) :=
      Submodule.basisOfPid (Pi.basisFun R s) (LinearMap.ker proj)
    refine ⟨bqSigma.1, ?_⟩
    let eP : R ≃ₗ[R] p := LinearEquiv.ofInjective f hf_inj
    let bp : Basis (Fin 1) R p := (Basis.singleton (Fin 1) R).map eP
    let eSum : (p × LinearMap.ker proj) ≃ₗ[R] (s → R) :=
      Submodule.prodEquivOfIsCompl p _ <| LinearMap.isCompl_of_proj hproj
    let bM : Basis (Sum (Fin 1) (Fin bqSigma.1)) R (s → R) :=
      (bp.prod bqSigma.2).map eSum
    refine ⟨bM, ?_⟩
    have : (bp (0 : Fin 1) : (s → R)) = u := by
      -- `bp 0 = eP 1` and `eP 1` corresponds to `f 1 = u`.
      ext i
      -- First reduce `bp 0` to `eP 1`.
      simp [bp, Basis.map_apply, Basis.singleton_apply]
      -- Now unfold `eP` via `LinearEquiv.ofInjective_apply`.
      have he : ((eP (1 : R)) : s → R) = f 1 := by
        simpa [eP] using
          (LinearEquiv.ofInjective_apply (f := (f : R →ₗ[R] s → R)) (x := (1 : R)))
      -- Finally, compute `f 1`.
      simp [he, f, Pi.smul_apply, smul_eq_mul]
    simp [bM, eSum, this]
  rcases buildBasis hv with ⟨nv, ⟨bv, hbv⟩⟩
  rcases buildBasis hw with ⟨nw, ⟨bw, hbw⟩⟩
  -- Use a change-of-basis linear equivalence sending the basis containing `v` to the basis containing `w`.
  let σ : (Sum (Fin 1) (Fin nv)) ≃ (Sum (Fin 1) (Fin nw)) := bv.indexEquiv bw
  let j : Sum (Fin 1) (Fin nw) := σ (Sum.inl 0)
  let τ : (Sum (Fin 1) (Fin nw)) ≃ (Sum (Fin 1) (Fin nw)) := Equiv.swap (Sum.inl 0) j
  let bw' : Basis (Sum (Fin 1) (Fin nw)) R (s → R) := bw.reindex τ
  let eLin : (s → R) ≃ₗ[R] (s → R) :=
    (bv.repr.trans (Finsupp.domLCongr σ)).trans bw'.repr.symm
  have heLin : eLin v = w := by
    -- `eLin` sends `bv i` to `bw' (σ i)`, and `bw' (σ (Sum.inl 0)) = w` by construction.
    have : bw' (σ (Sum.inl 0)) = w := by simpa [j] using (by simp [bw', τ, j, hbw])
    rw [← hbv]
    simp [eLin, this]
  -- Convert the linear equivalence to a matrix in `GL` and conclude.
  let g : LinearMap.GeneralLinearGroup R (s → R) := LinearMap.GeneralLinearGroup.ofLinearEquiv eLin
  let A : Matrix.GeneralLinearGroup s R := (Matrix.GeneralLinearGroup.toLin).symm g
  refine ⟨(Matrix.GeneralLinearGroup.toLin).symm g, ?_⟩
  have htoLin : Matrix.GeneralLinearGroup.toLin A = g := by
    simp [A]
  have hlin : ((Matrix.GeneralLinearGroup.toLin A : (s → R) →ₗ[R] (s → R)) v) = w := by
    simp [htoLin, g, heLin]
  simpa [Matrix.mulVecLin_apply] using (by simpa [Matrix.GeneralLinearGroup.coe_toLin] using hlin)

end

/-
\begin{definition}
	Let $A$ be any ring. A vector ${v} \in A^s$ is unimodular if its components generate the unit ideal in $A$. For two unimodular vectors ${v}, {w}$, we write
	$$\displaystyle {v} \sim {w}$$
	if there is a matrix $M \in \mathrm{GL}_s(A)$ such that $M {v} = {w}$. This is clearly an equivalence relation.
\end{definition}

\begin{proposition}\label{prop:6}
	Over a principal ideal domain $R$, any two unimodular vectors are equivalent.
\end{proposition}

\begin{proof}
	In fact, unimodular vectors $v \in R^m$ correspond to imbeddings $R \rightarrow R^m$ which are split injections. But if we have a split injection in this way, the cokernel is free (as we are over a PID), and consequently there is a basis for $R^m$ one of whose elements is $v$. This implies that $v$ is conjugate to $e_1 = (1, 0, \dots, 0)$.
\end{proof}

\begin{theorem}[Horrocks]\label{thm:8}
	Let $A = R[x]$ for $(R, \mathfrak{m})$ a local ring. Then any unimodular vector in $A^s$ one of whose elements has leading coefficient one is equivalent to $e_1$.
\end{theorem}

\begin{proof}
	Let $v(x) = (v_1(x), \dots, v_s(x))$ be a unimodular vector. Suppose without loss of generality that the leading coefficient of $v_1(x)$ is one, so that $v_1 (x) = x^d + a_1 x^{d-1} + \dots$. If $d = 0$, then $v_1$ is a unit and there is nothing to prove. We will induct on $d$.

	Then, by making elementary row operations (which don't change the equivalence class of $v(x)$), we can assume that $v_2(x), \dots, v_s(x)$ all have degree $\leq d-1$. Consider the coefficients of these elements. At least one of them must be a unit. In fact, if we reduce mod $\mathfrak{m}$, then not all the $v_i, i \geq 2$ can go to zero or the $v_i(x)$ would not generate the unit ideal mod $\mathfrak{m}$. So let us assume that $v_2(x)$ contains a unit among its coefficients.

	The claim is now that we can make elementary row operations so as to find another unimodular vector, in the same equivalence class, one of whose elements is monic of degree $\leq d-1$. If we can show this, then induction on $d$ will easily complete the proof.

	Now, here is a lemma: If we have two polynomials $a(x), b(x) \in R[x]$, with $\deg a = d$ and $a$ monic, and $b$ of degree $\leq d-1$ containing at least one coefficient which is a unit, there is a polynomial $a(x) e(x) + b(x) f(x) \in (a(x), b(x))$ of degree $\leq d-1$ whose leading coefficient is one. This is easy to see with a bit of explicit manipulation.

	This means that there are $e(x), f(x)$, such that $e(x) v_1(x) + f(x) v_2(x)$ has degree $\leq d-1$ and leading coefficient a unit. If we keep this fact in mind, we can, using row and column operations, modify the vector $v(x)$ such that it contains a monic element of degree $\leq d-1$. We just add appropriate multiples of $v_1, v_2$ to $v_3$ to make the leading coefficient a unit. This works if $s \geq 3$. If $s =1$ or $s= 2$, the lemma can be checked directly.
\end{proof}

-/
