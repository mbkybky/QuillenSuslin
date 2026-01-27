import QuillenSuslin.StablyFree

universe u v w

variable {R : Type u} [CommRing R]

open Polynomial Module Ideal

set_option maxHeartbeats 600000 in
theorem hasFiniteFreeResolution_quotient_prime [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (p : PrimeSpectrum (R[X])) : HasFiniteFreeResolution (R[X]) (R[X] ⧸ p.1) := by
  classical
  -- Noetherian induction on the contraction `p.1 ∩ R`.
  let A : Type u := R[X]
  let contr : PrimeSpectrum A → Ideal R := fun q => Ideal.comap (C : R →+* A) q.1
  have hprop :
      ∀ I : Ideal R, (∀ q : PrimeSpectrum A, contr q = I → HasFiniteFreeResolution A (A ⧸ q.1)) := by
    refine IsNoetherian.induction (R := R) (M := R)
      (P := fun I : Ideal R => ∀ q : PrimeSpectrum A, contr q = I → HasFiniteFreeResolution A (A ⧸ q.1)) ?_
    intro I ih q hqI
    let P : Ideal A := q.1
    have hPprime : P.IsPrime := q.2
    have hcomap : Ideal.comap (C : R →+* A) P = I := by
      simpa [contr, P] using hqI
    have hIA_le_P : Ideal.map (C : R →+* A) I ≤ P := by
      refine (Ideal.map_le_iff_le_comap).2 ?_
      simpa [hcomap]
    let IA : Ideal A := Ideal.map (C : R →+* A) I

    -- If `P = I·A`, then `A ⧸ P` is the polynomial ring over `R ⧸ I`.
    by_cases hPIA : P = IA
    ·
      have hI_res : HasFiniteFreeResolution R I := hR I (by infer_instance)
      have hIA_res : HasFiniteFreeResolution A IA :=
        hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution (R := R) I hI_res
      have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free (R := A) A
      have hquot : HasFiniteFreeResolution A (A ⧸ IA) :=
        hasFiniteFreeResolution_of_shortExact_of_left_of_middle (R := A) IA A (A ⧸ IA)
          (f := IA.subtype) (g := IA.mkQ) (hf := Subtype.coe_injective)
          (hg := Submodule.mkQ_surjective IA)
          (h := by simpa using (LinearMap.exact_subtype_mkQ IA))
          hIA_res hA
      have hquotP : HasFiniteFreeResolution A (A ⧸ P) :=
        hasFiniteFreeResolution_of_linearEquiv (R := A)
          (Submodule.quotEquivOfEq IA P hPIA.symm) hquot
      simpa [P] using hquotP

    -- Otherwise, reduce mod `I` and use the "clearing denominators" lemma over the domain `R ⧸ I`.
    ·
      -- `I` is prime since it is the contraction of the prime ideal `P`.
      have hIprime : Ideal.IsPrime I := by
        have : (Ideal.comap (C : R →+* A) P).IsPrime := by infer_instance
        simpa [hcomap] using this
      letI : Ideal.IsPrime I := hIprime
      let R₀ : Type u := R ⧸ I
      let A₀ : Type u := R₀[X]
      haveI : IsDomain R₀ := by infer_instance
      haveI : IsNoetherianRing R₀ := by infer_instance

      -- Quotient of `A` by `I·A`, and the corresponding prime ideal `P₀` in `(R ⧸ I)[X]`.
      let B : Type u := A ⧸ IA
      let π : A →+* B := Ideal.Quotient.mk IA
      let Pbar : Ideal B := Ideal.map π P
      let e : A₀ ≃+* B := Ideal.polynomialQuotientEquivQuotientPolynomial (I := I)
      let P₀ : Ideal A₀ := Ideal.comap (e : A₀ →+* B) Pbar

      have hPbar_ne : Pbar ≠ ⊥ := by
        intro hbot
        have hle : P ≤ RingHom.ker π :=
          (Ideal.map_eq_bot_iff_le_ker (f := π) (I := P)).1 hbot
        have hker : RingHom.ker π = IA := by
          dsimp [π]
          exact Ideal.mk_ker (I := IA)
        have hP_le_IA : P ≤ IA := by
          simpa [A, hker] using hle
        have hEq : P = IA := le_antisymm hP_le_IA hIA_le_P
        exact hPIA hEq

      have hP₀_ne : P₀ ≠ ⊥ := by
        intro hbot
        have : Ideal.map (e : A₀ →+* B) P₀ = Pbar := by
          simpa [P₀] using (Ideal.map_comap_of_surjective (f := (e : A₀ →+* B)) e.surjective Pbar)
        have : Pbar = ⊥ := by simpa [hbot] using this.symm
        exact hPbar_ne this

      -- `P₀ ∩ R₀ = (0)`, i.e. `C x ∈ P₀ → x = 0`.
      have hP₀_contr : ∀ x : R₀, (C x : A₀) ∈ P₀ → x = 0 := by
        intro x hx
        rcases Ideal.Quotient.mk_surjective (I := I) x with ⟨r, rfl⟩
        have hx' : (e (C (Ideal.Quotient.mk I r) : A₀)) ∈ Pbar := by
          simpa [P₀, Ideal.mem_comap] using hx
        have hCr :
            e (C (Ideal.Quotient.mk I r) : A₀) =
              (Ideal.Quotient.mk IA) (C r) := by
          -- use the computation lemma for `polynomialQuotientEquivQuotientPolynomial`.
          simpa [IA, Polynomial.map_C] using
            (Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk (I := I) (f := (C r : A)))
        have hx'' : (Ideal.Quotient.mk IA) (C r) ∈ Pbar := by simpa [hCr] using hx'
        rcases (Ideal.mem_map_iff_of_surjective π (Ideal.Quotient.mk_surjective (I := IA))).1 hx'' with
          ⟨a, haP, haEq⟩
        have hab : a - C r ∈ IA := (Ideal.Quotient.eq).1 haEq
        have habP : a - C r ∈ P := hIA_le_P hab
        have hCrP : (C r : A) ∈ P := by
          have : (C r : A) = a - (a - C r) := by abel
          exact this ▸ P.sub_mem haP habP
        have hrI : r ∈ I := by
          have : r ∈ Ideal.comap (C : R →+* A) P := by simpa [Ideal.mem_comap] using hCrP
          simpa [hcomap] using this
        exact (Ideal.Quotient.eq_zero_iff_mem).2 hrI

      -- Apply the clearing-denominators lemma to `P₀`.
      obtain ⟨d₀, hd₀, f₀, hf₀P₀, hf₀ne, hmul₀⟩ :=
        exists_nonzero_C_mul_mem_span_singleton (R := R₀) (P := P₀) hP₀_contr hP₀_ne

      -- Choose a lift `d : R` of `d₀` (so `d ∉ I`).
      rcases Ideal.Quotient.mk_surjective (I := I) d₀ with ⟨d, rfl⟩
      have hd_not_mem : d ∉ I := by
        intro hdI
        apply hd₀
        exact (Ideal.Quotient.eq_zero_iff_mem).2 hdI

      -- Transport `f₀` to `B` and define the principal ideal `(f̄) ⊆ P̄`.
      let fbar : B := e f₀
      have hfbar_mem : fbar ∈ Pbar := by
        have : f₀ ∈ P₀ := hf₀P₀
        simpa [P₀, Ideal.mem_comap, fbar] using this
      have hfbar_ne : fbar ≠ 0 := by
        intro h0
        apply hf₀ne
        exact e.injective (by simpa [fbar] using h0)
      let Fbar : Ideal B := Ideal.span ({fbar} : Set B)
      have hFbar_le : Fbar ≤ Pbar := by
        intro x hx
        -- `x ∈ (f̄)` implies `x = y * f̄`.
        rcases (Ideal.mem_span_singleton.1 hx) with ⟨y, rfl⟩
        exact Pbar.mul_mem_right y hfbar_mem

      -- Translate `d₀·P₀ ⊆ (f₀)` to `d·P̄ ⊆ (f̄)` in `B`.
      have hmul_bar :
          ∀ g : B, g ∈ Pbar → (Ideal.Quotient.mk IA (C d) : B) * g ∈ Fbar := by
        intro g hg
        -- Pull back along the ring equivalence `e`.
        let g₀ : A₀ := e.symm g
        have hg₀ : g₀ ∈ P₀ := by
          -- membership in the comap is exactly membership of the image.
          have : (e g₀) ∈ Pbar := by simpa [g₀] using hg
          simpa [P₀, Ideal.mem_comap] using this
        have h0 : (C (Ideal.Quotient.mk I d) : A₀) * g₀ ∈ Ideal.span ({f₀} : Set A₀) :=
          hmul₀ g₀ hg₀
        have hCd :
            e (C (Ideal.Quotient.mk I d) : A₀) = (Ideal.Quotient.mk IA) (C d) := by
          simpa [IA, Polynomial.map_C] using
            (Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk (I := I) (f := (C d : A)))
        -- Map the containment through `e` and rewrite the image of the principal ideal.
        have : e ((C (Ideal.Quotient.mk I d) : A₀) * g₀) ∈ Ideal.map (e : A₀ →+* B) (Ideal.span ({f₀} : Set A₀)) :=
          Ideal.mem_map_of_mem (e : A₀ →+* B) h0
        -- Convert `Ideal.map` of a principal ideal to a principal ideal.
        have hspan :
            Ideal.map (e : A₀ →+* B) (Ideal.span ({f₀} : Set A₀)) = Ideal.span ({fbar} : Set B) := by
          -- `e '' {f₀} = {f̄}`.
          simpa [fbar] using (Ideal.map_span (e : A₀ →+* B) ({f₀} : Set A₀))
        -- Finish.
        have : e (C (Ideal.Quotient.mk I d) : A₀) * e g₀ ∈ Fbar := by
          -- rewrite and use the membership above
          simpa [Fbar, hspan, map_mul] using this
        simpa [g₀, hCd] using this

      -- Define the quotient module `N := P̄/(f̄)`, viewed as an `A`-module via `A → B`.
      letI : Algebra A B := π.toAlgebra
      letI : Module A B := by infer_instance
      let Psub : Submodule A B := (Pbar : Submodule B B).restrictScalars A
      let Fsub : Submodule A B := (Fbar : Submodule B B).restrictScalars A
      have hFsub_le : Fsub ≤ Psub := by
        intro x hx
        exact hFbar_le hx
      let K : Submodule A Psub := Submodule.comap Psub.subtype Fsub
      let N := Psub ⧸ K
      let acgN : AddCommGroup N := Submodule.Quotient.addCommGroup K
      letI : AddCommGroup N := acgN
      letI : AddCommMonoid N := acgN.toAddCommMonoid
      letI : Module A N := Submodule.Quotient.module K

      -- `C d` annihilates `N`.
      have hAnn_d : ∀ x : N, (C d : A) • x = 0 := by
        intro x
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce to membership in `K`.
        have hyF : ((C d : A) • (y : B)) ∈ Fsub := by
          have hyFmul : (π (C d) : B) * (y : B) ∈ Fsub := by
            have : (Ideal.Quotient.mk IA (C d) : B) * (y : B) ∈ Fbar := hmul_bar (y : B) y.2
            simpa [Fsub, π] using this
          have hsmul : ((C d : A) • (y : B)) = (π (C d) : B) * (y : B) := by
            rw [Algebra.smul_def]
            rfl
          simpa [hsmul] using hyFmul
        have hyK : (C d : A) • y ∈ K := by
          -- By definition of `K` as a comap.
          simpa [K] using hyF
        have h0 : Submodule.Quotient.mk (p := K) ((C d : A) • y) = (0 : N) :=
          (Submodule.Quotient.mk_eq_zero K).2 hyK
        -- Rewrite `r • mk y` as `mk (r • y)`.
        have hmksmul :
            Submodule.Quotient.mk (p := K) ((C d : A) • y) =
              (C d : A) • Submodule.Quotient.mk (p := K) y :=
          Submodule.Quotient.mk_smul K (r := (C d : A)) (x := y)
        exact hmksmul.symm.trans h0

      -- `N` has a finite free resolution, by decomposing into prime quotients.
      have hN : HasFiniteFreeResolution A N := by
        classical
        haveI : IsNoetherianRing A := by
          -- `R[X]` is noetherian.
          infer_instance
        haveI : Module.Finite A B := by
          dsimp [B]
          simpa using (Module.Finite.quotient A IA)
        haveI : IsNoetherianRing B := by infer_instance
        haveI : Module.Finite B Pbar := by infer_instance
        letI : Module A Pbar := by infer_instance
        letI : IsScalarTower A B Pbar := by infer_instance
        haveI : Module.Finite A Pbar := Module.Finite.trans (R := A) (A := B) (M := Pbar)
        haveI : Module.Finite A Psub := by
          simpa [Psub] using (show Module.Finite A (Pbar : Type u) from (by infer_instance))
        haveI : Module.Finite A N := by infer_instance
        have hAnn_I : ∀ r : R, r ∈ I → ∀ x : N, (C r : A) • x = 0 := by
          intro r hrI x
          refine Quotient.inductionOn' x ?_
          intro y
          have hCrIA : (C r : A) ∈ IA := Ideal.mem_map_of_mem (C : R →+* A) hrI
          have hπCr : (π (C r) : B) = 0 := by
            dsimp [π]
            exact (Ideal.Quotient.eq_zero_iff_mem).2 hCrIA
          have hy0 : (C r : A) • (y : B) = 0 := by
            rw [Algebra.smul_def]
            change (π (C r) : B) * (y : B) = 0
            rw [hπCr, zero_mul]
          have hyF : (C r : A) • (y : B) ∈ Fsub := by
            simpa [hy0] using (show (0 : B) ∈ Fsub from Fsub.zero_mem)
          have hyK : (C r : A) • y ∈ K := by
            simpa [K] using hyF
          have h0 : Submodule.Quotient.mk (p := K) ((C r : A) • y) = (0 : N) :=
            (Submodule.Quotient.mk_eq_zero K).2 hyK
          have hmksmul :
              Submodule.Quotient.mk (p := K) ((C r : A) • y) =
                (C r : A) • Submodule.Quotient.mk (p := K) y :=
            Submodule.Quotient.mk_smul K (r := (C r : A)) (x := y)
          exact hmksmul.symm.trans h0

        let motive :
            ∀ (M : Type u), [AddCommGroup M] → [Module A M] → [Module.Finite A M] → Prop :=
          fun M _ _ _ =>
            (∀ x : M, (C d : A) • x = 0) →
              (∀ r : R, r ∈ I → ∀ x : M, (C r : A) • x = 0) →
                HasFiniteFreeResolution A M

        have hN' : motive N := by
          refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime (A := A) (M := N)
            (by infer_instance) (motive := motive)
            (subsingleton := ?_) (quotient := ?_) (exact := ?_)
          · intro M _ _ _ _
            intro _ _
            exact hasFiniteFreeResolution_of_subsingleton (R := A) M
          · intro M _ _ _ p' eM
            intro hAnn_dM hAnn_IM
            -- Show the contraction of `p'` is strictly larger than `I`.
            have hCd0_M : (C d : A) • (1 : A ⧸ p'.1) = 0 := by
              have h := hAnn_dM (eM.symm (1 : A ⧸ p'.1))
              have h' : eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := congrArg eM h
              have hs :
                  eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) =
                    (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) :=
                eM.map_smul (C d : A) (eM.symm (1 : A ⧸ p'.1))
              have h'' : (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := by
                calc
                  (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) =
                      eM ((C d : A) • eM.symm (1 : A ⧸ p'.1)) := hs.symm
                  _ = eM (0 : M) := h'
              have h''0 : (C d : A) • eM (eM.symm (1 : A ⧸ p'.1)) = (0 : A ⧸ p'.1) :=
                h''.trans eM.map_zero
              have h1 :
                  eM (eM.symm (1 : A ⧸ p'.1)) = (1 : A ⧸ p'.1) :=
                eM.apply_symm_apply (1 : A ⧸ p'.1)
              -- Rewrite `1` as `eM (eM.symm 1)` and use `h''0`.
              -- (Using `rw` here avoids heavy `simp` typeclass search.)
              rw [← h1]
              exact h''0
            have hCd_mem : (C d : A) ∈ p'.1 := by
              have hmk : (Ideal.Quotient.mk p'.1 (C d : A) : A ⧸ p'.1) = 0 := by
                have h := hCd0_M
                rw [Algebra.smul_def] at h
                rw [mul_one] at h
                -- `algebraMap` for the quotient algebra is definitional.
                have hAlgebraMap :
                    (algebraMap A (A ⧸ p'.1)) = Ideal.Quotient.mk p'.1 := rfl
                -- Rewrite the `algebraMap` in `h` using `rw`.
                -- (Avoid `simp` here: it may trigger expensive typeclass search.)
                simpa using (by
                  -- `rw` changes `algebraMap` to the quotient map.
                  -- After that, `h` has the desired form.
                  -- (The final `simpa` is purely definitional.)
                  rw [hAlgebraMap] at h
                  exact h)
              exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk
            have hI_le_contr : I ≤ Ideal.comap (C : R →+* A) p'.1 := by
              intro r hrI
              have hCr0_M : (C r : A) • (1 : A ⧸ p'.1) = 0 := by
                have h := hAnn_IM r hrI (eM.symm (1 : A ⧸ p'.1))
                have h' : eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := congrArg eM h
                have hs :
                    eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) =
                      (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) :=
                  eM.map_smul (C r : A) (eM.symm (1 : A ⧸ p'.1))
                have h'' : (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) = eM (0 : M) := by
                  calc
                    (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) =
                        eM ((C r : A) • eM.symm (1 : A ⧸ p'.1)) := hs.symm
                    _ = eM (0 : M) := h'
                have h''0 : (C r : A) • eM (eM.symm (1 : A ⧸ p'.1)) = (0 : A ⧸ p'.1) :=
                  h''.trans eM.map_zero
                have h1 :
                    eM (eM.symm (1 : A ⧸ p'.1)) = (1 : A ⧸ p'.1) :=
                  eM.apply_symm_apply (1 : A ⧸ p'.1)
                rw [← h1]
                exact h''0
              have hCr_mem : (C r : A) ∈ p'.1 := by
                have hmk : (Ideal.Quotient.mk p'.1 (C r : A) : A ⧸ p'.1) = 0 := by
                  have h := hCr0_M
                  rw [Algebra.smul_def] at h
                  rw [mul_one] at h
                  have hAlgebraMap :
                      (algebraMap A (A ⧸ p'.1)) = Ideal.Quotient.mk p'.1 := rfl
                  simpa using (by
                    rw [hAlgebraMap] at h
                    exact h)
                exact (Ideal.Quotient.eq_zero_iff_mem).1 hmk
              simpa [Ideal.mem_comap] using hCr_mem
            have hlt : Ideal.comap (C : R →+* A) p'.1 > I := by
              refine lt_of_le_of_ne hI_le_contr ?_
              intro hEq
              have : d ∈ I := by
                have : d ∈ Ideal.comap (C : R →+* A) p'.1 := by
                  simpa [Ideal.mem_comap] using hCd_mem
                simpa [hEq] using this
              exact hd_not_mem this
            have hquot : HasFiniteFreeResolution A (A ⧸ p'.1) :=
              ih (Ideal.comap (C : R →+* A) p'.1) hlt p' rfl
            exact hasFiniteFreeResolution_of_linearEquiv (R := A) eM.symm hquot
          · intro M₁ _ _ _ M₂ _ _ _ M₃ _ _ _ f g hf hg hfg h₁ h₃
            intro hAnn_d2 hAnn_I2
            have hAnn_d1 : ∀ x : M₁, (C d : A) • x = 0 := by
              intro x
              apply hf
              have : (C d : A) • f x = 0 := hAnn_d2 (f x)
              have : f ((C d : A) • x) = 0 := by simpa using this
              simpa using this
            have hAnn_I1 : ∀ r : R, r ∈ I → ∀ x : M₁, (C r : A) • x = 0 := by
              intro r hrI x
              apply hf
              have : (C r : A) • f x = 0 := hAnn_I2 r hrI (f x)
              have : f ((C r : A) • x) = 0 := by simpa using this
              simpa using this
            have hAnn_d3 : ∀ x : M₃, (C d : A) • x = 0 := by
              intro z
              rcases hg z with ⟨y, rfl⟩
              have : g ((C d : A) • y) = g 0 := congrArg g (hAnn_d2 y)
              simpa using this
            have hAnn_I3 : ∀ r : R, r ∈ I → ∀ x : M₃, (C r : A) • x = 0 := by
              intro r hrI z
              rcases hg z with ⟨y, rfl⟩
              have : g ((C r : A) • y) = g 0 := congrArg g (hAnn_I2 r hrI y)
              simpa using this
            have h₁' : HasFiniteFreeResolution A M₁ := h₁ hAnn_d1 hAnn_I1
            have h₃' : HasFiniteFreeResolution A M₃ := h₃ hAnn_d3 hAnn_I3
            exact hasFiniteFreeResolution_of_shortExact_of_left_of_right (R := A) M₁ M₂ M₃
              hf hg hfg h₁' h₃'

        exact hN' hAnn_d hAnn_I

      -- `B` has a finite free resolution as an `A`-module.
      have hI_res : HasFiniteFreeResolution R I := hR I (by infer_instance)
      have hIA_res : HasFiniteFreeResolution A IA :=
        hasFiniteFreeResolution_map_C_of_hasFiniteFreeResolution (R := R) I hI_res
      have hA : HasFiniteFreeResolution A A := hasFiniteFreeResolution_of_finite_of_free (R := A) A
      have hB : HasFiniteFreeResolution A B :=
        hasFiniteFreeResolution_of_shortExact_of_left_of_middle (R := A) IA A (A ⧸ IA)
          (f := IA.subtype) (g := IA.mkQ) (hf := Subtype.coe_injective)
          (hg := Submodule.mkQ_surjective IA)
          (h := by simpa using (LinearMap.exact_subtype_mkQ IA))
          hIA_res hA

      -- `(f̄)` has a finite free resolution since `B` is a domain.
      haveI : IsDomain A₀ := by infer_instance
      haveI : IsDomain B := by
        -- transfer `IsDomain` across the ring equivalence `e.symm : B ≃+* A₀`
        exact MulEquiv.isDomain (A := B) (B := A₀) e.symm.toMulEquiv
      have hFbar : HasFiniteFreeResolution A Fbar :=
        hasFiniteFreeResolution_of_linearEquiv (R := A)
          ((linearEquiv_mul_spanSingleton (R := B) fbar hfbar_ne).restrictScalars A)
          hB

      -- Identify `K` with `Fbar` and conclude `Pbar` has a finite free resolution from `0 → K → Psub → N → 0`.
      have hK : HasFiniteFreeResolution A K := by
        have hFsub : HasFiniteFreeResolution A Fsub := by
          simpa [Fsub] using hFbar
        have eKF : (K : Type u) ≃ₗ[A] Fsub := (Submodule.comapSubtypeEquivOfLe hFsub_le)
        exact hasFiniteFreeResolution_of_linearEquiv (R := A) eKF.symm hFsub
      have hPbar : HasFiniteFreeResolution A Psub := by
        -- Short exact sequence `0 → K → Psub → N → 0`.
        refine hasFiniteFreeResolution_of_shortExact_of_left_of_right (R := A) K Psub N
          (f := (K.subtype).restrictScalars A) (g := (K.mkQ).restrictScalars A)
          (hf := Subtype.coe_injective) (hg := Submodule.mkQ_surjective K)
          (h := by simpa using (LinearMap.exact_subtype_mkQ K))
          hK hN

      -- Lift back to `P ⊂ A` using `0 → IA → P → Pbar → 0`, then conclude for `A ⧸ P`.
      -- Map `P` to `Pbar` by the quotient map `π`.
      let fIP : IA →ₗ[A] P := Submodule.inclusion hIA_le_P
      let gPP : P →ₗ[A] Pbar :=
        { toFun := fun x => ⟨π x.1, Ideal.mem_map_of_mem π x.2⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro m x
            ext
            -- Reduce to multiplicativity of `π : A →+* B`.
            change π (m • (↑x : A)) = m • π (↑x : A)
            have hAlgebraMap : (algebraMap A B) = π := rfl
            have hAlgId : (algebraMap A A) = RingHom.id A := rfl
            -- Unfold scalar actions via `Algebra.smul_def`, then use multiplicativity of `π`.
            simpa [Algebra.smul_def, hAlgebraMap, hAlgId] using (π.map_mul m (↑x : A)) }
      have hfIP : Function.Injective fIP := by
        intro x y hxy
        apply Subtype.ext
        have : (fIP x : A) = (fIP y : A) := congrArg (fun z : P => (z : A)) hxy
        simpa [fIP] using this
      have hgPP : Function.Surjective gPP := by
        intro y
        rcases (Ideal.mem_map_iff_of_surjective π (Ideal.Quotient.mk_surjective (I := IA))).1 y.2 with
          ⟨a, haP, haEq⟩
        refine ⟨⟨a, haP⟩, ?_⟩
        apply Subtype.ext
        simpa [gPP] using haEq
      have hexPP : Function.Exact fIP gPP := by
        intro x
        constructor
        · intro hx0
          have hx0' : π (x.1 : A) = 0 := congrArg (fun z : Pbar => (z : B)) hx0
          have hxIA : (x.1 : A) ∈ IA := (Ideal.Quotient.eq_zero_iff_mem).1 hx0'
          refine ⟨⟨(x.1 : A), hxIA⟩, ?_⟩
          apply Subtype.ext
          rfl
        · rintro ⟨y, rfl⟩
          -- elements from `IA` map to `0` in the quotient
          apply Subtype.ext
          have hy0 : π (y.1 : A) = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 y.2
          simpa [gPP, fIP] using hy0
      have hP : HasFiniteFreeResolution A P := by
        -- Use `0 → IA → P → Pbar → 0`.
        refine hasFiniteFreeResolution_of_shortExact_of_left_of_right (R := A) IA P Pbar hfIP hgPP hexPP
          hIA_res (by
            -- `Pbar` identifies with `Psub`.
            simpa [Psub] using hPbar)

      -- Finally, `0 → P → A → A ⧸ P → 0`.
      have hquot : HasFiniteFreeResolution A (A ⧸ P) :=
        hasFiniteFreeResolution_of_shortExact_of_left_of_middle (R := A) P A (A ⧸ P)
          (f := P.subtype) (g := P.mkQ) (hf := Subtype.coe_injective)
          (hg := Submodule.mkQ_surjective P)
          (h := by simpa using (LinearMap.exact_subtype_mkQ P))
          hP hA
      exact hquot

  have := hprop (contr p) p rfl
  simpa [A] using this
#print axioms hasFiniteFreeResolution_quotient_prime
/-- Reduce the prime-quotient case to the corresponding prime ideal as an `R[X]`-module. -/
theorem hasFiniteFreeResolution_primeIdeal [IsNoetherianRing R]
    (hR : ∀ (P : Type u), [AddCommGroup P] → [Module R P] → Module.Finite R P →
      HasFiniteFreeResolution R P)
    (P : Ideal (R[X])) (hP : P.IsPrime) : HasFiniteFreeResolution (R[X]) P := by
  classical
  let p : PrimeSpectrum (R[X]) := ⟨P, hP⟩
  have hquot : HasFiniteFreeResolution (R[X]) (R[X] ⧸ P) :=
    hasFiniteFreeResolution_quotient_prime (R := R) hR p
  have hA : HasFiniteFreeResolution (R[X]) (R[X]) :=
    hasFiniteFreeResolution_of_finite_of_free (R := (R[X])) (R[X])
  -- Use `0 → P → R[X] → R[X]/P → 0`.
  refine hasFiniteFreeResolution_of_shortExact_of_middle_of_right (R := (R[X])) P (R[X]) (R[X] ⧸ P)
    (f := P.subtype) (g := P.mkQ) (hf := Subtype.coe_injective)
    (hg := Submodule.mkQ_surjective P)
    (h := by simpa using (LinearMap.exact_subtype_mkQ P))
    hA hquot

/-
\begin{definition}
	A finitely generated module $P$ over a commutative ring $R$ is said to be stably free if there exists a finitely generated free module $F$ such that the direct sum $P \oplus F$ is a free module.
\end{definition}

\begin{lemma}\label{exact_seq}
	Let $R$ be a ring. Let $0 \to P' \to P \to P'' \to 0$ be a short
	exact sequence of finite projective $R$-modules. If $2$ out of $3$
	of these modules are stably free, then so is the third.
\end{lemma}

\begin{proposition}
	Let $R$ be a commutative Noetherian ring. Let $x$ be a variable. If every finite $R$-module has a finite free resolution, then every finite $R[x]$-module has a finite free resolution.
\end{proposition}

\begin{proof}
	Let $M$ be a finite $R[x]$-module. $M$ has a finite filtration
	$$M = M_0 \supset M_1 \supset \dots \supset M_n = 0$$
	such that each factor $M_i/M_{i+1}$ is isomorphic to $R[x]/P_i$ for some prime $P_i$. In light of Lemma \ref{exact_seq}, it suffices to prove the theorem in case $M = R[x]/P$ where $P$ is prime, which we now assume. In light of the exact sequence
	$$0 \to P \to R[x] \to R[x]/P \to 0$$
	and Lemma \ref{exact_seq}, we note that $M$ has a finite free resolution if and only if $P$ does.

	Let $\mathfrak{p} = P \cap R$. Then $\mathfrak{p}$ is prime in $R$. Suppose there is some $M = R[x]/P$ which does not admit a finite free resolution. Among all such $M$ we select one for which the intersection $\mathfrak{p}$ is maximal in the family of prime ideals obtained as above. This is possible in light of one of the basic properties characterizing Noetherian rings.

	Let $R_0 = R/\mathfrak{p}$ so $R_0$ is entire. Let $P_0 = P/\mathfrak{p}R[x]$. Then we may view $M$ as an $R_0[x]$-module, equal to $R_0/P_0$. Let $f_1, \dots, f_n$ be a finite set of generators for $P_0$, and let $f$ be a polynomial of minimal degree in $P_0$. Let $K_0$ be the quotient field of $R_0$. By the euclidean algorithm, we can write
	$$f_i = q_i f + r_i \quad \text{for } i = 1, \dots, n$$
	with $q_i, r_i \in K_0[x]$ and $\deg r_i < \deg f$. Let $d_0$ be a common denominator for the coefficients of all $q_i, r_i$. Then $d_0 \neq 0$ and
	$$d_0 f_i = q'_i f + r'_i$$
	where $q'_i = d_0 q_i$ and $r'_i = d_0 r_i$ lie in $R_0[x]$. Since $\deg f$ is minimal in $P_0$ it follows that $r'_i = 0$ for all $i$, so
	$$d_0 P_0 \subset R_0[x]f = (f).$$

	Let $N_0 = P_0/(f)$, so $N_0$ is a module over $R_0[x]$, and we can also view $N_0$ as a module over $R[x]$. When so viewed, we denote $N_0$ by $N$. Let $d \in R$ be any element reducing to $d_0 \pmod{\mathfrak{p}}$. Then $d \notin \mathfrak{p}$ since $d_0 \neq 0$. The module $N_0$ has a finite filtration such that each factor module of the filtration is isomorphic to some $R_0[x]/\bar{Q}_0$ where $\bar{Q}_0$ is an associated prime of $N_0$. Let $Q$ be the inverse image of $\bar{Q}_0$ in $R[x]$. These prime ideals $Q$ are precisely the associated primes of $N$ in $R[x]$. Since $d_0$ kills $N_0$ it follows that $d$ kills $N$ and therefore $d$ lies in every associated prime of $N$. By the maximality property in the selection of $P$, it follows that every one of the factor modules in the filtration of $N$ has a finite free resolution, and by Lemma \ref{exact_seq} it follows that $N$ itself has a finite free resolution.

	Now we view $R_0[x]$ as an $R[x]$-module, via the canonical homomorphism
	$$R[x] \to R_0[x] = R[x]/\mathfrak{p}R[x].$$
	By assumption, $\mathfrak{p}$ has a finite free resolution as $R$-module, say
	$$0 \to E_n \to \dots \to E_0 \to \mathfrak{p} \to 0.$$
	Then we may simply form the modules $E_i[x]$ in the obvious sense to obtain a finite free resolution of $\mathfrak{p}[x] = \mathfrak{p}R[x]$. From the exact sequence
	$$0 \to \mathfrak{p}R[x] \to R[x] \to R_0[x] \to 0$$
	we conclude that $R_0[x]$ has a finite free resolution as $R[x]$-module.

	Since $R_0$ is entire, it follows that the principal ideal $(f)$ in $R_0[x]$ is $R[x]$-isomorphic to $R_0[x]$, and therefore has a finite free resolution as $R[x]$-module. Lemma \ref{exact_seq} applied to the exact sequence of $R[x]$-modules
	$$0 \to (f) \to P_0 \to N \to 0$$
	shows that $P_0$ has a finite free resolution, and further applied to the exact sequence
	$$0 \to \mathfrak{p}R[x] \to P \to P_0 \to 0$$
	shows that $P$ has a finite free resolution, thereby concluding the proof.
\end{proof}

-/
