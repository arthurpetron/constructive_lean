/-
Additional `Q'` absolute-value lemmas: congruence under `eqv`,
`|−x| ≈ |x|`, the product bound `|x·y| ≤ |x|·|y|`, and the two-term
triangle inequality `|u+v| ≤ |u|+|v|`.

`AbsQ.lean` provides `abs`, `abs_le`, `le_abs_self`, `neg_le_abs`, and
`mul_le_of_bounds`; this module adds the derived facts that series and
convolution estimates need.

# Axiom-gate

Every theorem reports `[propext]` (plus `Quot.sound` only via reused
`Nat`/`Int` helpers).  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Rationals
import ConstructiveReals.RationalsMul
import ConstructiveReals.AbsQ
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealMul

namespace ConstructiveReals.AbsQExtra

open ConstructiveReals
open ConstructiveReals.Q'

local infix:50 " ≈ " => Q'.eqv

namespace Q'

/-- Build `eqv` from `≤` both ways (the cross-product representation is `Int`,
where `≤` is antisymmetric). -/
theorem eqv_of_le_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a ≈ b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm h1 h2

/-- `abs` respects `eqv`: `a ≈ b ⟹ abs a ≈ abs b`. -/
theorem abs_eqv_congr {a b : Q'} (h : a ≈ b) : (Q'.abs a) ≈ (Q'.abs b) := by
  have hab : a ≤ b := Q'.le_of_eqv h
  have hba : b ≤ a := Q'.ge_of_eqv h
  have h1 : Q'.abs a ≤ Q'.abs b := by
    refine Q'.abs_le ?_ ?_
    · have hnb : -(Q'.abs b) ≤ b := by
        have := Q'.neg_le_abs b
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv b))
      exact Q'.le_trans' _ _ _ hnb hba
    · exact Q'.le_trans' _ _ _ hab (Q'.le_abs_self b)
  have h2 : Q'.abs b ≤ Q'.abs a := by
    refine Q'.abs_le ?_ ?_
    · have hna : -(Q'.abs a) ≤ a := by
        have := Q'.neg_le_abs a
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv a))
      exact Q'.le_trans' _ _ _ hna hab
    · exact Q'.le_trans' _ _ _ hba (Q'.le_abs_self a)
  exact Q'.eqv_of_le_le h1 h2

/-- `abs (−x) ≈ abs x`. -/
theorem abs_neg (x : Q') : (Q'.abs (-x)) ≈ (Q'.abs x) := by
  have h1 : Q'.abs (-x) ≤ Q'.abs x := by
    refine Q'.abs_le ?_ ?_
    · exact Q'.neg_le_neg (Q'.le_abs_self x)
    · exact Q'.neg_le_abs x
  have h2 : Q'.abs x ≤ Q'.abs (-x) := by
    refine Q'.abs_le ?_ ?_
    · have := Q'.le_abs_self (-x)
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv x))
    · have := Q'.neg_le_abs (-x)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv x)) this
  exact Q'.eqv_of_le_le h1 h2

/-- `abs (x·y) ≤ abs x · abs y`.  (Sign-cased via `mul_le_of_bounds`.) -/
theorem abs_mul_le (x y : Q') : Q'.abs (x * y) ≤ Q'.abs x * Q'.abs y := by
  refine Q'.abs_le ?_ ?_
  · have hup : -(x * y) ≤ Q'.abs x * Q'.abs y := by
      have e : (-(x * y)) ≈ ((-x) * y) := Q'.eqv_symm (Q'.neg_mul_eqv x y)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
      exact Q'.mul_le_of_bounds (Q'.abs_nonneg x) (Q'.abs_nonneg y)
        (by exact Q'.neg_le_neg (Q'.le_abs_self x))
        (by exact Q'.neg_le_abs x)
        (by have := Q'.neg_le_abs y
            have hh := Q'.neg_le_neg this
            exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv y)))
        (Q'.le_abs_self y)
    have hh := Q'.neg_le_neg hup
    exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv (x * y)))
  · exact Q'.mul_le_of_bounds (Q'.abs_nonneg x) (Q'.abs_nonneg y)
      (by have := Q'.neg_le_abs x
          have hh := Q'.neg_le_neg this
          exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv x)))
      (Q'.le_abs_self x)
      (by have := Q'.neg_le_abs y
          have hh := Q'.neg_le_neg this
          exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv y)))
      (Q'.le_abs_self y)

end Q'

/-- Reverse-triangle for a sum of two: `abs (u + v) ≤ abs u + abs v`. -/
theorem abs_add_le (u v : Q') : Q'.abs (u + v) ≤ Q'.abs u + Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · have hu : -(Q'.abs u) ≤ u := by
      have := Q'.neg_le_abs u
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv u))
    have hv : -(Q'.abs v) ≤ v := by
      have := Q'.neg_le_abs v
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv v))
    have hneg : (-(Q'.abs u + Q'.abs v)) ≈ ((-(Q'.abs u)) + (-(Q'.abs v))) :=
      Q'.neg_add_eqv (Q'.abs u) (Q'.abs v)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) ?_
    exact Q'.add_le_add hu hv
  · exact Q'.add_le_add (Q'.le_abs_self u) (Q'.le_abs_self v)

end ConstructiveReals.AbsQExtra

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.AbsQExtra.Q'.abs_eqv_congr
#print axioms ConstructiveReals.AbsQExtra.Q'.abs_neg
#print axioms ConstructiveReals.AbsQExtra.Q'.abs_mul_le
#print axioms ConstructiveReals.AbsQExtra.abs_add_le
