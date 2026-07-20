/-
Shared constructive-real ring / `csum` / `ofQ'` algebra — the canonical home for
the pointwise `CReal` arithmetic helpers that several Track-B modules had each
rebuilt locally.

`CReal.mul`, `CReal.add`, and `CReal.csum` all act approx-wise (no clamping), so
every `CReal` ring identity that does NOT move past a genuine limit (associativity,
commutativity, the multiplicative unit, the `ofQ'` ring homomorphism, finite-sum
additivity) reduces to the corresponding `Q'` identity at each approximation index
via `SumOfSquares.Equiv_of_approx_eqv`.  This file proves each such identity ONCE,
in its most general (arbitrary-`CReal`) form, so the matched-retune / fusion modules
can `open` this namespace instead of re-deriving the same lemmas.

These are the pointwise (limit-free) laws only; the genuinely non-pointwise
congruences (`CReal.Equiv` under `mul`, which needs a local-bound product estimate)
live with the per-step product machinery, not here.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `Nat` arithmetic enters.  No `Classical.*`,
no `native_decide`, no `sorryAx`.  Every helper is a closed pointwise reduction.
-/

import ConstructiveReals.CRealMul
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealSum
import ConstructiveReals.SumOfSquares
import ConstructiveReals.CRealAbs
import ConstructiveReals.Soundness

namespace ConstructiveReals.CRealAlg

open ConstructiveReals
open ConstructiveReals.CReal

/-! ## 1. `CReal` multiplication: associativity, commutativity, the unit -/

/-- **`CReal` multiplication associates** (pointwise): `(A·B)·C ≃ A·(B·C)`. -/
theorem cmul_assoc (A B C : CReal) :
    CReal.Equiv (CReal.mul (CReal.mul A B) C) (CReal.mul A (CReal.mul B C)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_assoc_eqv (A.approx n) (B.approx n) (C.approx n))

/-- **`CReal` multiplication commutes** (pointwise): `A·B ≃ B·A`. -/
theorem cmul_comm (A B : CReal) :
    CReal.Equiv (CReal.mul A B) (CReal.mul B A) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_comm_eqv (A.approx n) (B.approx n))

/-- **Left multiplicative unit** (pointwise): `cone·x ≃ x`. -/
theorem cone_mul (x : CReal) : CReal.Equiv (CReal.mul CReal.cone x) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.one_mul_eqv (x.approx n))

/-- **Right multiplicative unit** (pointwise): `x·cone ≃ x`. -/
theorem cmul_cone (x : CReal) : CReal.Equiv (CReal.mul x CReal.cone) x :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_one_eqv (x.approx n))

/-! ## 2. The `ofQ'` ring homomorphism (multiplicative) -/

/-- **`ofQ'` is multiplicative** (pointwise; both sides are the constant `a·b`):
`ofQ'(a·b) ≃ ofQ' a · ofQ' b`. -/
theorem ofQ'_mul (a b : Q') :
    CReal.Equiv (CReal.ofQ' (a * b)) (CReal.mul (CReal.ofQ' a) (CReal.ofQ' b)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 3. Finite `csum` additivity -/

/-- **`csum` is additive**: `∑(A + B) ≃ ∑A + ∑B` (pointwise via `finSum_add`). -/
theorem csum_add (A B : Nat → CReal) (n : Nat) :
    CReal.Equiv (CReal.csum (fun i => CReal.add (A i) (B i)) n)
      (CReal.add (CReal.csum A n) (CReal.csum B n)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  rw [CReal.csum_approx (fun i => CReal.add (A i) (B i)) n p]
  show (RationalTail.finSum (fun i => (A i).approx p + (B i).approx p) n).eqv
    ((CReal.csum A n).approx p + (CReal.csum B n).approx p)
  rw [CReal.csum_approx A n p, CReal.csum_approx B n p]
  exact RationalTail.finSum_add (fun i => (A i).approx p) (fun i => (B i).approx p) n

/-! ## 4. AM-GM at the `Q'` level -/

/-- **AM-GM (cleared, summed form).**  `(x·y) + (x·y) ≤ x·x + y·y`, from
`0 ≤ (x + -y)·(x + -y)` (a sum-of-squares: the two-term AM-GM `2xy ≤ x²+y²`). -/
theorem amgm_two (x y : Q') : (x * y) + (x * y) ≤ x * x + y * y := by
  -- 0 ≤ (x-y)² = x·x + -(x·y) + (-(x·y) + y·y), rearranged.
  have hsq : (0 : Q') ≤ (x + -y) * (x + -y) := SumOfSquares.q_mul_self_nonneg (x + -y)
  -- Expand (x + -y)·(x + -y).
  -- (x + -y)·(x + -y) = x·(x + -y) + (-y)·(x + -y)
  have e1 : ((x + -y) * (x + -y)).eqv (x * (x + -y) + (-y) * (x + -y)) :=
    Q'.add_mul_eqv x (-y) (x + -y)
  -- x·(x + -y) = x·x + x·(-y)
  have e2 : (x * (x + -y)).eqv (x * x + x * (-y)) := Q'.mul_add_eqv x x (-y)
  -- (-y)·(x + -y) = (-y)·x + (-y)·(-y)
  have e3 : ((-y) * (x + -y)).eqv ((-y) * x + (-y) * (-y)) := Q'.mul_add_eqv (-y) x (-y)
  -- Identify the cross terms with -(x·y) and the square term with y·y.
  -- x·(-y) ≃ -(x·y)
  have hxny : (x * (-y)).eqv (-(x * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv x (-y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y x) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y x)
  -- (-y)·x ≃ -(x·y)
  have hnyx : ((-y) * x).eqv (-(x * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y x) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y x)
  -- (-y)·(-y) ≃ y·y
  have hnyny : ((-y) * (-y)).eqv (y * y) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv y (-y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv y (-y))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv y y)) ?_
    exact Q'.neg_neg_eqv (y * y)
  -- Assemble: (x-y)² ≃ (x·x + -(x·y)) + (-(x·y) + y·y)
  have hexp : ((x + -y) * (x + -y)).eqv
      ((x * x + -(x * y)) + (-(x * y) + y * y)) := by
    refine Q'.eqv_trans _ _ _ e1 ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · -- x·(x + -y) ≃ x·x + -(x·y)
      refine Q'.eqv_trans _ _ _ e2 (Q'.add_eqv_congr_left (x * x) _ _ hxny)
    · -- (-y)·(x + -y) ≃ -(x·y) + y·y
      refine Q'.eqv_trans _ _ _ e3 ?_
      exact Q'.add_eqv_congr' hnyx hnyny
  -- So 0 ≤ (x·x + -(x·y)) + (-(x·y) + y·y), regroup to (x·y)+(x·y) ≤ x·x + y·y.
  have hge : (0 : Q') ≤ (x * x + -(x * y)) + (-(x * y) + y * y) :=
    Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hexp)
  -- Add (x·y)+(x·y) to both sides and cancel.
  -- (x·x + -(x·y)) + (-(x·y) + y·y) ≃ (x·x + y·y) + (-(x·y) + -(x·y))
  have hregroup : ((x * x + -(x * y)) + (-(x * y) + y * y)).eqv
      ((x * x + y * y) + (-(x * y) + -(x * y))) := by
    -- (A + s) + (s + B) ≃ (A + s) + (B + s) ≃ (A + B) + (s + s) (A=x·x, B=y·y, s=-(x·y)).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv (-(x * y)) (y * y))) ?_
    exact Q'.eqv_symm (Q'.add_swap_inner (x * x) (y * y) (-(x * y)) (-(x * y)))
  have hge2 : (0 : Q') ≤ (x * x + y * y) + (-(x * y) + -(x * y)) :=
    Q'.le_trans' _ _ _ hge (Q'.le_of_eqv hregroup)
  -- 0 ≤ (x·x+y·y) + -( (x·y)+(x·y) ).  Then (x·y)+(x·y) ≤ x·x+y·y.
  have hneg : (-(x * y) + -(x * y)).eqv (-((x * y) + (x * y))) :=
    Q'.eqv_symm (Q'.neg_add_eqv (x * y) (x * y))
  have hge3 : (0 : Q') ≤ (x * x + y * y) + -((x * y) + (x * y)) :=
    Q'.le_trans' _ _ _ hge2 (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hneg))
  exact Q'.le_of_sub_nonneg hge3

end ConstructiveReals.CRealAlg

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CRealAlg.cmul_assoc
#print axioms ConstructiveReals.CRealAlg.cmul_comm
#print axioms ConstructiveReals.CRealAlg.cone_mul
#print axioms ConstructiveReals.CRealAlg.cmul_cone
#print axioms ConstructiveReals.CRealAlg.ofQ'_mul
#print axioms ConstructiveReals.CRealAlg.csum_add
#print axioms ConstructiveReals.CRealAlg.amgm_two
