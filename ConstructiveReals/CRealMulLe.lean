/-
`CReal.leRat_mul` — product upper bound for constructive reals.

If `A`, `C` have limits in `[0, Ba]`, `[0, Bc]` respectively (upper bounds via
`CReal.leRat`, lower bounds via `ExpPos.geRat … 0`), then the pointwise product
`A·C` has limit `≤ Ba·Bc`.

The estimate: for tolerance `ε`, pick a division-free `δ ≤ min(δ₀,1)` with
`S·δ ≤ ε` where `S = Ba + Bc + 1`.  Eventually
`-(Ba+δ) ≤ A_n ≤ Ba+δ` and `-(Bc+δ) ≤ C_n ≤ Bc+δ`, so by
`Q'.mul_le_of_bounds`,
`A_n·C_n ≤ (Ba+δ)(Bc+δ) = Ba·Bc + (Ba·δ + δ·Bc + δ·δ) ≤ Ba·Bc + S·δ ≤ Ba·Bc + ε`.
The cross terms are bounded using `δ·δ ≤ δ` (as `δ ≤ 1`).

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.ExpAdd

namespace ConstructiveReals

open ConstructiveReals

namespace CReal

open Q'

/-- **Product upper bound.**  If the limit of `A` lies in `[0, Ba]` and the
limit of `C` lies in `[0, Bc]`, then the limit of `A·C` is `≤ Ba·Bc`. -/
theorem leRat_mul {A C : CReal} {Ba Bc : Q'}
    (hA : CReal.leRat A Ba) (hC : CReal.leRat C Bc)
    (hA0 : ExpPos.geRat A 0) (hC0 : ExpPos.geRat C 0)
    (hBa : (0:Q') ≤ Ba) (hBc : (0:Q') ≤ Bc) :
    CReal.leRat (CReal.mul A C) (Ba * Bc) := by
  intro ε hε
  -- `S := Ba + Bc + 1 ≥ 0`.
  have hS : (0 : Q') ≤ Ba + Bc + 1 := by
    have h1 : (0 : Q') ≤ Ba + Bc := Q'.zero_le_add _ _ hBa hBc
    have h2 : (0 : Q') ≤ (1 : Q') := by
      show (0 : Int) * ((1 : Q').den : Int) ≤ (1 : Q').num * ((0 : Q').den : Int)
      decide
    exact Q'.zero_le_add _ _ h1 h2
  -- division-free `δ₀` with `S·δ₀ ≤ ε`.
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := CReal.exists_mul_le hS hε
  -- `δ := min'(δ₀, 1)`.  Then `0 < δ`, `δ ≤ 1`, `δ ≤ δ₀`.
  have hδle1 : Q'.min' δ₀ 1 ≤ 1 := by
    unfold Q'.min'
    by_cases h : δ₀ ≤ 1
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact Q'.le_refl' 1
  have hδleδ₀ : Q'.min' δ₀ 1 ≤ δ₀ := by
    unfold Q'.min'
    by_cases h : δ₀ ≤ 1
    · rw [if_pos h]; exact Q'.le_refl' δ₀
    · rw [if_neg h]
      -- ¬(δ₀ ≤ 1) ⟹ 1 ≤ δ₀.
      have hnot : ¬ (δ₀.num * ((1:Q').den : Int) ≤ (1:Q').num * (δ₀.den : Int)) := h
      show (1:Q').num * (δ₀.den : Int) ≤ δ₀.num * ((1:Q').den : Int)
      exact Int.le_of_lt (Int.not_le.mp hnot)
  have hδpos : (0 : Q') < Q'.min' δ₀ 1 := by
    unfold Q'.min'
    by_cases h : δ₀ ≤ 1
    · rw [if_pos h]; exact hδ₀pos
    · rw [if_neg h]
      show (0 : Int) * ((1:Q').den : Int) < (1:Q').num * ((0:Q').den : Int)
      decide
  generalize hδdef : Q'.min' δ₀ 1 = δ at hδle1 hδleδ₀ hδpos
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  -- `S·δ ≤ S·δ₀ ≤ ε`.
  have hSδ : (Ba + Bc + 1) * δ ≤ ε := by
    have hstep : (Ba + Bc + 1) * δ ≤ (Ba + Bc + 1) * δ₀ :=
      Q'.mul_le_mul_of_nonneg_left δ δ₀ (Ba + Bc + 1) hδleδ₀ hS
    exact Q'.le_trans' _ _ _ hstep hδ₀
  -- eventual bounds.
  obtain ⟨Na, hNa⟩ := hA δ hδpos
  obtain ⟨Nc, hNc⟩ := hC δ hδpos
  obtain ⟨Na', hNa'⟩ := hA0 δ hδpos
  obtain ⟨Nc', hNc'⟩ := hC0 δ hδpos
  refine ⟨max (max Na Nc) (max Na' Nc'), fun n hn => ?_⟩
  have lna : Na ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have lnc : Nc ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have lna' : Na' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have lnc' : Nc' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  -- upper bounds: `A_n ≤ Ba + δ`, `C_n ≤ Bc + δ`.
  have hAub : A.approx n ≤ Ba + δ := hNa n lna
  have hCub : C.approx n ≤ Bc + δ := hNc n lnc
  -- lower bounds: `-δ ≤ A_n`, hence `-(Ba+δ) ≤ A_n` (since `0 ≤ Ba ≤ Ba+δ`).
  have hAlb0 : -δ ≤ A.approx n := Q'.neg_le_of_zero_le_add (hNa' n lna')
  have hClb0 : -δ ≤ C.approx n := Q'.neg_le_of_zero_le_add (hNc' n lnc')
  -- `-(Ba+δ) ≤ -δ`: from `δ ≤ Ba + δ`.
  have hδleBaδ : δ ≤ Ba + δ := by
    have hstep : (0:Q') + δ ≤ Ba + δ := Q'.add_le_add_right 0 Ba δ hBa
    rw [Q'.zero_add' δ] at hstep
    exact hstep
  have hAlb : -(Ba + δ) ≤ A.approx n :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hδleBaδ) hAlb0
  have hδleBcδ : δ ≤ Bc + δ := by
    have hstep : (0:Q') + δ ≤ Bc + δ := Q'.add_le_add_right 0 Bc δ hBc
    rw [Q'.zero_add' δ] at hstep
    exact hstep
  have hClb : -(Bc + δ) ≤ C.approx n :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hδleBcδ) hClb0
  -- nonnegativity of the bounds.
  have hBaδ : (0 : Q') ≤ Ba + δ := Q'.zero_le_add _ _ hBa hδnn
  have hBcδ : (0 : Q') ≤ Bc + δ := Q'.zero_le_add _ _ hBc hδnn
  -- `A_n·C_n ≤ (Ba+δ)·(Bc+δ)`.
  have hprod : A.approx n * C.approx n ≤ (Ba + δ) * (Bc + δ) :=
    Q'.mul_le_of_bounds hBaδ hBcδ hAlb hAub hClb hCub
  -- expand `(Ba+δ)(Bc+δ) = Ba·Bc + (Ba·δ + (δ·Bc + δ·δ))`.
  -- step 1: `(Ba+δ)(Bc+δ) ≃ Ba·(Bc+δ) + δ·(Bc+δ)`.
  have e1 : ((Ba + δ) * (Bc + δ)).eqv (Ba * (Bc + δ) + δ * (Bc + δ)) :=
    Q'.add_mul_eqv Ba δ (Bc + δ)
  -- step 2: `Ba·(Bc+δ) ≃ Ba·Bc + Ba·δ`.
  have e2 : (Ba * (Bc + δ)).eqv (Ba * Bc + Ba * δ) := Q'.mul_add_eqv Ba Bc δ
  -- step 3: `δ·(Bc+δ) ≃ δ·Bc + δ·δ`.
  have e3 : (δ * (Bc + δ)).eqv (δ * Bc + δ * δ) := Q'.mul_add_eqv δ Bc δ
  -- combine: `(Ba+δ)(Bc+δ) ≃ (Ba·Bc + Ba·δ) + (δ·Bc + δ·δ)`.
  have e4 : ((Ba + δ) * (Bc + δ)).eqv
      ((Ba * Bc + Ba * δ) + (δ * Bc + δ * δ)) :=
    Q'.eqv_trans _ _ _ e1
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ e2)
        (Q'.add_eqv_congr_left _ _ _ e3))
  -- bound the remainder `Ba·δ + (δ·Bc + δ·δ) ≤ (Ba + Bc + 1)·δ`.
  -- `δ·δ ≤ δ` since `δ ≤ 1` and `δ ≥ 0`.
  have hδδ : δ * δ ≤ δ := by
    have h : δ * δ ≤ δ * 1 :=
      Q'.mul_le_mul_of_nonneg_left δ 1 δ hδle1 hδnn
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv δ))
  -- `δ·Bc + δ·δ ≤ Bc·δ + δ` (commute `δ·Bc`, weaken `δ·δ`).
  have hcross : δ * Bc + δ * δ ≤ Bc * δ + δ := by
    have c1 : δ * Bc ≤ Bc * δ := Q'.le_of_eqv (Q'.mul_comm_eqv δ Bc)
    have s1 : δ * Bc + δ * δ ≤ Bc * δ + δ * δ :=
      Q'.add_le_add_right _ _ (δ * δ) c1
    have s2 : Bc * δ + δ * δ ≤ Bc * δ + δ :=
      Q'.add_le_add_left (Bc * δ) (δ * δ) δ hδδ
    exact Q'.le_trans' _ _ _ s1 s2
  -- `Ba·δ + (δ·Bc + δ·δ) ≤ Ba·δ + (Bc·δ + δ)`.
  have hrem1 : Ba * δ + (δ * Bc + δ * δ) ≤ Ba * δ + (Bc * δ + δ) :=
    Q'.add_le_add_left (Ba * δ) (δ * Bc + δ * δ) (Bc * δ + δ) hcross
  -- `Ba·δ + (Bc·δ + δ) ≃ (Ba + Bc + 1)·δ`.
  -- RHS: `(Ba+Bc+1)·δ ≃ (Ba+Bc)·δ + 1·δ ≃ (Ba·δ + Bc·δ) + δ`.
  have r1 : ((Ba + Bc + 1) * δ).eqv ((Ba + Bc) * δ + 1 * δ) :=
    Q'.add_mul_eqv (Ba + Bc) 1 δ
  have r2 : ((Ba + Bc) * δ).eqv (Ba * δ + Bc * δ) := Q'.add_mul_eqv Ba Bc δ
  have r3 : ((1 : Q') * δ).eqv δ := Q'.one_mul_eqv δ
  -- `(Ba+Bc+1)·δ ≃ (Ba·δ + Bc·δ) + δ`.
  have rA : ((Ba + Bc + 1) * δ).eqv ((Ba * δ + Bc * δ) + δ) :=
    Q'.eqv_trans _ _ _ r1
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ r2)
        (Q'.add_eqv_congr_left _ _ _ r3))
  -- `Ba·δ + (Bc·δ + δ) ≃ (Ba·δ + Bc·δ) + δ` (reassociate).
  have rB : (Ba * δ + (Bc * δ + δ)).eqv ((Ba * δ + Bc * δ) + δ) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (Ba * δ) (Bc * δ) δ)
  -- hence `Ba·δ + (Bc·δ + δ) ≃ (Ba+Bc+1)·δ`.
  have rC : (Ba * δ + (Bc * δ + δ)).eqv ((Ba + Bc + 1) * δ) :=
    Q'.eqv_trans _ _ _ rB (Q'.eqv_symm rA)
  -- combine the remainder bound with `(Ba+Bc+1)·δ ≤ ε`.
  have hremε : Ba * δ + (δ * Bc + δ * δ) ≤ ε :=
    Q'.le_trans' _ _ _ hrem1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv rC) hSδ)
  -- assemble: `(Ba·Bc + Ba·δ) + (δ·Bc + δ·δ) ≃ Ba·Bc + (Ba·δ + (δ·Bc + δ·δ))`.
  have hassoc : ((Ba * Bc + Ba * δ) + (δ * Bc + δ * δ)).eqv
      (Ba * Bc + (Ba * δ + (δ * Bc + δ * δ))) :=
    Q'.add_assoc_eqv (Ba * Bc) (Ba * δ) (δ * Bc + δ * δ)
  -- `Ba·Bc + (remainder) ≤ Ba·Bc + ε`.
  have hfin : Ba * Bc + (Ba * δ + (δ * Bc + δ * δ)) ≤ Ba * Bc + ε :=
    Q'.add_le_add_left (Ba * Bc) (Ba * δ + (δ * Bc + δ * δ)) ε hremε
  -- chain everything.
  have hexp : (Ba + δ) * (Bc + δ) ≤ Ba * Bc + ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv e4)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) hfin)
  -- goal: `(mul A C).approx n ≤ Ba·Bc + ε`, i.e. `A_n·C_n ≤ Ba·Bc + ε`.
  show A.approx n * C.approx n ≤ Ba * Bc + ε
  exact Q'.le_trans' _ _ _ hprod hexp

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gate (see README: axiom policy) -/

#print axioms ConstructiveReals.CReal.leRat_mul
