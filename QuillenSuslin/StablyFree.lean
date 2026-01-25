import Mathlib

/-- A module $P$ over a ring $R$ is \textit{stably free} if there exists a free finitely generated
  module $F$ over $R$ such that $P \oplus F$ is a free module. -/
def IsStablyFree (R : Type) (P : Type) [CommRing R] [AddCommGroup P] [Module R P] : Prop :=
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (P × N)

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
