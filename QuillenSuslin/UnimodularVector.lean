import Mathlib

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
  sorry

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

-/
