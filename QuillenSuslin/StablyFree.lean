import Mathlib

universe u v

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R : Type u) (P : Type v) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
  ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

/-- Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third. -/
theorem isStablyFree_two_of_three_of_shortExact (R : Type u) (P₁ P₂ P₃ : Type v) [CommRing R]
    [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂] [Module.Projective R P₂]
    [AddCommGroup P₃] [Module R P₃] [Module.Finite R P₃] [Module.Projective R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
      (IsStablyFree R P₁ → IsStablyFree R P₂ → IsStablyFree R P₃) ∧
        (IsStablyFree R P₁ → IsStablyFree R P₃ → IsStablyFree R P₂) ∧
          (IsStablyFree R P₂ → IsStablyFree R P₃ → IsStablyFree R P₁) := by
  obtain ⟨l, hl⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.2 hg)
  set eSigma := h.splitSurjectiveEquiv hf ⟨l, hl⟩ with heSigma
  set e : P₂ ≃ₗ[R] P₁ × P₃ := eSigma.1 with he
  refine ⟨?_, ?_⟩
  · intro hP₁ hP₂
    rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
    rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
    refine ⟨(P₁ × N₁) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    -- Rewrite `P₃ × ((P₁ × N₁) × N₂)` as `((P₂ × N₂) × N₁)` using the splitting `P₂ ≃ P₁ × P₃`.
    let eP₃ : (P₃ × ((P₁ × N₁) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₁) :=
      (LinearEquiv.prodAssoc R P₃ (P₁ × N₁) N₂).symm ≪≫ₗ
        (LinearEquiv.prodAssoc R P₃ P₁ N₁).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
          ((LinearEquiv.prodComm R P₃ P₁).prodCongr (LinearEquiv.refl R N₁)).prodCongr
              (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₁ N₂ ≪≫ₗ
              (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₁ N₂) ≪≫ₗ
                (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₁).symm ≪≫ₗ
                  (((e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₁)))
    exact Module.Free.of_equiv eP₃.symm
  · refine ⟨?_, ?_⟩
    · intro hP₁ hP₃
      rcases hP₁ with ⟨N₁, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨N₁ × N₃, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₂ : (P₂ × (N₁ × N₃)) ≃ₗ[R] ((P₁ × N₁) × (P₃ × N₃)) :=
        e.prodCongr (LinearEquiv.refl R (N₁ × N₃)) ≪≫ₗ LinearEquiv.prodProdProdComm R P₁ P₃ N₁ N₃
      exact Module.Free.of_equiv eP₂.symm
    · intro hP₂ hP₃
      rcases hP₂ with ⟨N₂, _, _, _, _, _⟩
      rcases hP₃ with ⟨N₃, _, _, _, _, _⟩
      refine ⟨(P₃ × N₃) × N₂, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
      let eP₁ : (P₁ × ((P₃ × N₃) × N₂)) ≃ₗ[R] ((P₂ × N₂) × N₃) :=
        (LinearEquiv.prodAssoc R P₁ (P₃ × N₃) N₂).symm ≪≫ₗ
          (LinearEquiv.prodAssoc R P₁ P₃ N₃).symm.prodCongr (LinearEquiv.refl R N₂) ≪≫ₗ
            ((LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.refl R N₃)).prodCongr
                (LinearEquiv.refl R N₂) ≪≫ₗ LinearEquiv.prodAssoc R (P₁ × P₃) N₃ N₂ ≪≫ₗ
                (LinearEquiv.refl R (P₁ × P₃)).prodCongr (LinearEquiv.prodComm R N₃ N₂) ≪≫ₗ
                  (LinearEquiv.prodAssoc R (P₁ × P₃) N₂ N₃).symm ≪≫ₗ
                    (e.symm.prodCongr (LinearEquiv.refl R N₂)).prodCongr (LinearEquiv.refl R N₃)
      exact Module.Free.of_equiv eP₁.symm

/-
\begin{definition}
	A finitely generated module $P$ over a commutative ring $R$ is said to be stably free if there exists a finitely generated free module $F$ such that the direct sum $P \oplus F$ is a free module.
\end{definition}

\begin{lemma}\label{exact_seq}
	Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third.
\end{lemma}

\begin{proof}
	Since the modules are projective, the sequence is split. Thus we can
	choose an isomorphism $P = P' \oplus P''$. If $P' \oplus R^{\oplus n}$
	and $P'' \oplus R^{\oplus m}$ are free, then we see that
	$P \oplus R^{\oplus n + m}$ is free. Suppose that $P'$ and $P$ are
	stably free, say $P \oplus R^{\oplus n}$ is free and $P' \oplus R^{\oplus m}$
	is free. Then
	$$
	P'' \oplus (P' \oplus R^{\oplus m}) \oplus R^{\oplus n} =
	(P'' \oplus P') \oplus R^{\oplus m} \oplus R^{\oplus n} =
	(P \oplus R^{\oplus n}) \oplus R^{\oplus m}
	$$
	is free. Thus $P''$ is stably free. By symmetry we get the last of the
	three cases.
\end{proof}
-/
