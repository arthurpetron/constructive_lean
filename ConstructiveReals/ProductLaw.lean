/-
Product law L4a — `eˣ·e⁻ˣ = 1` (the sound rational bounds).

`(mul (expPos x) (expNeg x)).approx n = P⁺ₙ·P⁻ₙ`, and L3a gives
`P⁺_{n+1}·P⁻_{n+1} ≃ 1 + corner_{n+1}` while L3b gives `|corner_{n+1}| ≤ ε`
past an explicit modulus.  Hence the limit is `1`, two-sidedly:

- `expProd_leRat`  — `eˣ·e⁻ˣ ≤ 1`  (uses `corner ≤ cornerAbs`),
- `expProd_geRat`  — `eˣ·e⁻ˣ ≥ 1`  (uses `−corner ≤ cornerAbs`).

`expProd_leRat` is the bound U.5 soundness needs (`Sheaf`/`ExpUBInstance`).

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.CornerBound

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.ExpPos

/-- **`eˣ·e⁻ˣ ≤ 1`.**  The product of the constructive exponentials has limit
`≤ 1`. -/
theorem expProd_leRat (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.leRat (CReal.mul (ExpPos.expPos x hx) (ExpNeg.expNeg x hx)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := cornerAbs_le x hx ε hε
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show partialSumAbs x (k + 1) * partialSum x (k + 1) ≤ 1 + ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (prod_eqv_one_add_corner x k)) ?_
  refine Q'.add_le_add_left 1 (corner x (k + 1)) ε ?_
  exact Q'.le_trans' _ _ _ (corner_le_cornerAbs x hx (k + 1)) (hN (k + 1) (by omega))

/-- **`eˣ·e⁻ˣ ≥ 1`.**  The product has limit `≥ 1`. -/
theorem expProd_geRat (x : Q') (hx : (0 : Q') ≤ x) :
    ExpPos.geRat (CReal.mul (ExpPos.expPos x hx) (ExpNeg.expNeg x hx)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := cornerAbs_le x hx ε hε
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (1 : Q') ≤ partialSumAbs x (k + 1) * partialSum x (k + 1) + ε
  -- 1 ≤ (1 + corner) + ε ≤ Q + ε
  refine Q'.le_trans' _ _ _ ?_
    (Q'.add_le_add_right _ _ ε (Q'.ge_of_eqv (prod_eqv_one_add_corner x k)))
  -- 1 ≤ (1 + corner x (k+1)) + ε
  have hcε : (0 : Q') ≤ corner x (k + 1) + ε := by
    have hneg : -(corner x (k + 1)) ≤ ε :=
      Q'.le_trans' _ _ _ (neg_corner_le_cornerAbs x hx (k + 1)) (hN (k + 1) (by omega))
    have hstep : -(corner x (k + 1)) + corner x (k + 1) ≤ ε + corner x (k + 1) :=
      Q'.add_le_add_right _ _ (corner x (k + 1)) hneg
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_self_eqv (corner x (k + 1)))) ?_
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.add_comm_eqv ε (corner x (k + 1))))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv 1 (corner x (k + 1)) ε)))
  exact Q'.add_le_self_of_nonneg 1 (corner x (k + 1) + ε) hcε

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.expProd_leRat
#print axioms ConstructiveReals.expProd_geRat
