import Mathlib

universe u v

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R P : Type*) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
    ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

/-- Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third. -/
theorem isStablyFree_two_of_three_of_shortExact (R P₁ P₂ P₃ : Type*) [CommRing R]
    [AddCommGroup P₁] [Module R P₁] [Module.Finite R P₁] [Module.Projective R P₁]
    [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₂] [Module.Projective R P₂]
    [AddCommGroup P₃] [Module R P₃] [Module.Finite R P₃] [Module.Projective R P₃]
    {f : P₁ →ₗ[R] P₂} {g : P₂ →ₗ[R] P₃} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
      (IsStablyFree R P₁ → IsStablyFree R P₂ → IsStablyFree R P₃) ∧
        (IsStablyFree R P₁ → IsStablyFree R P₃ → IsStablyFree R P₂) ∧
          (IsStablyFree R P₂ → IsStablyFree R P₃ → IsStablyFree R P₁) := by
  sorry

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
