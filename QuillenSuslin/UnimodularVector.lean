import Mathlib

open Module Polynomial Finset BigOperators

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
  have buildBasis {u : s → R} (hu : IsUnimodular u) : Σ n : ℕ,
      { b : Basis (Sum (Fin 1) (Fin n)) R (s → R) // b (Sum.inl 0) = u } := by
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
      calc _ = r * (∑ i : s, c i * u i) := by simp [φ, f, smul_eq_mul, mul_comm, Finset.mul_sum]
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
  -- Change basis: send the basis containing `v` to the basis containing `w`.
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

section degree

/-- If `0 < p.natDegree`, then `p ≠ 1`. -/
lemma ne_one_of_natDegree_pos {p : R[X]} (hp : 0 < p.natDegree) : p ≠ 1 := by
  rintro rfl
  simp at hp

/-- If `a` is monic and `n < a.natDegree`, then the remainder of `X^n` modulo `a` is `X^n`. -/
lemma X_pow_modByMonic_eq_self [Nontrivial R] {a : R[X]} (ha : a.Monic) {n : ℕ}
    (hn : n < a.natDegree) : (X ^ n %ₘ a) = X ^ n :=
  (Polynomial.modByMonic_eq_self_iff ha).2 (by simpa using WithBot.coe_lt_coe.mpr hn)

/-- If we have two polynomials $a(x), b(x) \in R[x]$, with $\deg a = d$ and $a$ monic,
  and $b$ of degree $\leq d-1$ containing at least one coefficient which is a unit, there is a
  polynomial $a(x) e(x) + b(x) f(x) \in (a(x), b(x))$ of degree $\leq d-1$ whose leading coefficient
  is one. -/
theorem degree_lowering (a b : R[X]) (ha : a.Monic) (hb : b.natDegree < a.natDegree)
    (h : ∃ i : ℕ, IsUnit (b.coeff i)) :
    ∃ e f : R[X], (a * e + b * f).Monic ∧ (a * e + b * f).natDegree < a.natDegree := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have hab : a = b := Subsingleton.elim _ _
    have : ¬ b.natDegree < a.natDegree := by simp [hab]
    exact (this hb).elim
  · set d : ℕ := a.natDegree
    have hdpos : 0 < d := by simpa [d] using lt_of_le_of_lt (Nat.zero_le _) hb
    have ha_ne_one : a ≠ 1 := by
      apply ne_one_of_natDegree_pos
      simpa [d] using hdpos
    let I : Ideal R[X] := Ideal.span ({a, b} : Set R[X])
    let L : R[X] →ₗ[R] R := (Polynomial.lcoeff R (d - 1)).comp (Polynomial.modByMonicHom a)
    let J : Submodule R R := Submodule.map L (I.restrictScalars R)
    have ha_mem_I : a ∈ I := Ideal.subset_span (by simp)
    have hb_mem_I : b ∈ I := Ideal.subset_span (by simp)
    have hL_X_pow_lt : ∀ {n : ℕ}, n < d - 1 → L (X ^ n) = 0 := by
      intro n hn
      have hn' : n < d := lt_of_lt_of_le hn (Nat.sub_le d 1)
      have hx : X ^ n %ₘ a = X ^ n := by
        simpa [d] using X_pow_modByMonic_eq_self ha (by simpa [d] using hn')
      have hne : (d - 1 : ℕ) ≠ n := ne_of_gt hn
      simp [L, Polynomial.lcoeff_apply, hx, Polynomial.coeff_X_pow, hne]
    have hL_X_pow_eq : L (X ^ (d - 1)) = 1 := by
      have hlt : d - 1 < d := Nat.sub_lt hdpos Nat.one_pos
      have hx : X ^ (d - 1) %ₘ a = X ^ (d - 1) := by
        simpa [d] using X_pow_modByMonic_eq_self ha (by simpa [d] using hlt)
      simp [L, Polynomial.lcoeff_apply, hx, Polynomial.coeff_X_pow]
    have hbCoeff_mem_J (i : ℕ) : i < d → b.coeff i ∈ J := by
      let P (k : ℕ) : Prop := ∀ j : ℕ, k ≤ j → j < d → b.coeff j ∈ J
      have hP_top : P d := by
        intro j hj hlt
        exact (not_lt_of_ge hj hlt).elim
      have hStep : ∀ k : ℕ, k < d → 0 ≤ k → P (k + 1) → P k := by
        intro k hk _ ih j hjk hjd
        by_cases hkj : j = k
        · subst j
          let s : ℕ := d - 1 - k
          have hsI : X ^ s * b ∈ I := I.mul_mem_left _ hb_mem_I
          have hsJ : L (X ^ s * b) ∈ J := by
            refine (Submodule.mem_map).2 ?_
            refine ⟨X ^ s * b, ?_, rfl⟩
            exact hsI
          have hb_sum : b = ∑ i ∈ range d, C (b.coeff i) * X ^ i := by
            simpa using b.as_sum_range_C_mul_X_pow' (by simpa [d] using hb)
          have hs_sum : X ^ s * b = ∑ i ∈ range d, b.coeff i • X ^ (s + i) := by
            conv_lhs => rw [hb_sum]
            simp only [mul_sum]
            refine sum_congr rfl ?_
            intro i hi
            calc _ = C (b.coeff i) * (X ^ s * X ^ i) := by grind
              _ = b.coeff i • X ^ (s + i) := by simp [pow_add, Polynomial.smul_eq_C_mul]
          have hs_L : L (X ^ s * b) = ∑ i ∈ range d, b.coeff i * L (X ^ (s + i)) := by
            simp [hs_sum, L, map_sum, map_smul, smul_eq_mul]
          let f : ℕ → R := fun i => b.coeff i * L (X ^ (s + i))
          have hk1 : k + 1 ≤ d := Nat.succ_le_of_lt hk
          have hsplit : (∑ i ∈ range (k + 1), f i) + (∑ i ∈ Ico (k + 1) d, f i) =
              ∑ i ∈ range d, f i := by
            simpa using (Finset.sum_range_add_sum_Ico f hk1)
          have hprefix_zero : (∑ i ∈ range k, f i) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            have hik : i < k := mem_range.mp hi
            have hni : s + i < d - 1 := by
              have hk_le : k ≤ d - 1 := Nat.le_pred_of_lt hk
              simpa [s, Nat.sub_add_cancel (hk_le)] using Nat.add_lt_add_left hik s
            simp [f, hL_X_pow_lt hni]
          have hprefix : (∑ i ∈ range (k + 1), f i) = b.coeff k := by
            have hs_add : s + k = d - 1 := by
              simpa [s] using (Nat.sub_add_cancel (Nat.le_pred_of_lt hk))
            have hfk : f k = b.coeff k := by
              simp [f, hs_add, hL_X_pow_eq]
            simp [Finset.sum_range_succ, hprefix_zero, hfk]
          have hs_eq_total : L (X ^ s * b) =
              b.coeff k + ∑ i ∈ Ico (k + 1) d, f i := by
            calc _ = ∑ i ∈ range d, f i := by simp [hs_L, f]
              _ = (∑ i ∈ range (k + 1), f i) + (∑ i ∈ Ico (k + 1) d, f i) := by
                simpa [add_comm, add_left_comm, add_assoc] using hsplit.symm
              _ = b.coeff k + (∑ i ∈ Ico (k + 1) d, f i) := by simp [hprefix]
          have htail_mem : (∑ i ∈ Ico (k + 1) d, f i) ∈ J := by
            refine Submodule.sum_mem J ?_
            intro i hi
            simpa [f, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
              J.smul_mem (L (X ^ (s + i))) (ih i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2)
          have : L (X ^ s * b) - (∑ i ∈ Ico (k + 1) d, f i) = b.coeff k :=
            (sub_eq_iff_eq_add).2 <| by
              simpa [add_assoc, add_comm, add_left_comm] using hs_eq_total
          simpa [this] using J.sub_mem hsJ htail_mem
        · have hjk' : k < j := lt_of_le_of_ne hjk (Ne.symm hkj)
          have hjk1 : k + 1 ≤ j := Nat.succ_le_of_lt hjk'
          exact ih j hjk1 hjd
      have hP0 : P 0 := Nat.decreasingInduction' hStep (Nat.zero_le _) hP_top
      exact hP0 i (Nat.zero_le _)
    rcases h with ⟨i, hi_unit⟩
    have hi_le : i ≤ b.natDegree := le_natDegree_of_ne_zero (IsUnit.ne_zero hi_unit)
    have hi_lt : i < d := lt_of_le_of_lt hi_le (by simpa [d] using hb)
    have hbi_mem : b.coeff i ∈ J := hbCoeff_mem_J i hi_lt
    rcases hi_unit with ⟨u, hu⟩
    have hone_mem : (1 : R) ∈ J := by
      have : (↑u⁻¹ : R) • (b.coeff i) ∈ J := J.smul_mem (↑u⁻¹ : R) hbi_mem
      simpa [hu.symm, smul_eq_mul] using this
    rcases (Submodule.mem_map).1 hone_mem with ⟨p, hpI, hpL⟩
    let g : R[X] := p %ₘ a
    have hg_coeff : g.coeff (d - 1) = 1 := by simpa [g, L, Polynomial.lcoeff_apply] using hpL
    have hg_deg : g.natDegree < d := by
      simpa [d, g] using Polynomial.natDegree_modByMonic_lt p ha ha_ne_one
    have hg_mem_I : g ∈ I := by
      have hmul : a * (p /ₘ a) ∈ I := I.mul_mem_right _ ha_mem_I
      have hmod : p %ₘ a = p - a * (p /ₘ a) := Polynomial.modByMonic_eq_sub_mul_div p ha
      simpa [g, hmod] using I.sub_mem hpI hmul
    have hg_monic : g.Monic := by
      have hg_le : g.natDegree ≤ d - 1 := Nat.le_pred_of_lt (by simpa [d] using hg_deg)
      exact monic_of_natDegree_le_of_coeff_eq_one (d - 1) hg_le (by simpa using hg_coeff)
    rcases (Ideal.mem_span_pair).1 hg_mem_I with ⟨e, f, hef⟩
    have hcomb : a * e + b * f = g := by
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hef
    refine ⟨e, f, ?_, ?_⟩
    · simpa [hcomb] using hg_monic
    · simpa [hcomb, d] using hg_deg

end degree

section horrocks

/-- Let `A = R[X]` for a local ring `R`. Then any unimodular vector in `A^s` with a monic component
  is equivalent to `e₁`. -/
theorem horrocks [IsLocalRing R] (o : s) (v : s → R[X]) (huv : IsUnimodular v)
    (h : ∃ i : s, (v i).Monic) : UnimodularVectorEquiv v (fun i => if i = o then 1 else 0) := by
  sorry

end horrocks

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
