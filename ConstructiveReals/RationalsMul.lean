/-
`Q'` multiplicative laws at semantic equivalence — the keystone the
geometric-tail closed form, `expNeg`'s Cauchy modulus, and the `ExpUB`
seed all share.

`Rationals.lean` provides `mul_nonneg` and `mul_le_mul_of_nonneg_right`
but flags (in `Geometric.lean`'s "Open work") that the geometric series
needs commutativity, associativity, left-distributivity at `eqv`, and
left-monotonicity — none of which were built.  This module supplies
exactly those, via cross-product reduction to `Int` (no `ring`/`linarith`,
which are unavailable without Mathlib and would risk the axiom gate).

`Q'` equality is *structural*, so these laws hold only up to `eqv`
(`a*b ≃ b*a`, not `a*b = b*a`); the `eqv↔≤` bridges (`le_of_eqv`,
`ge_of_eqv`, `le_trans'` from `Rationals.lean`) chain them into the
`≤`-facts the closures consume.

# Axiom-gate (see README: axiom policy)

Every theorem reports `[propext]` or empty.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import ConstructiveReals.Rationals

namespace ConstructiveReals

namespace Q'

/-! ## Denominator-cast helpers

`(a*b).den` and `(a+b).den` are both stored as `a.den*b.den - 1`; cast to
`Int` they are `a.den * b.den` (the product of positive Nats is ≥ 1, so
the truncated subtraction is exact).  These two lemmas package the
`Nat.sub_add_cancel` idiom used throughout `Rationals.lean`. -/

/-- `((a*b).den : Int) = a.den * b.den`. -/
theorem mul_den_cast (a b : Q') :
    ((a * b).den : Int) = (a.den : Int) * (b.den : Int) := by
  show (((a.den * b.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (b.den : Int)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos b))))]
  exact Int.natCast_mul a.den b.den

/-- `((a+b).den : Int) = a.den * b.den` (the `Q'.add` denominator has the
same `a.den*b.den - 1` shape as `Q'.mul`). -/
theorem add_den_cast (a b : Q') :
    ((a + b).den : Int) = (a.den : Int) * (b.den : Int) := by
  show (((a.den * b.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (b.den : Int)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos b))))]
  exact Int.natCast_mul a.den b.den

/-! ## Commutativity, associativity, left-distributivity (at `eqv`) -/

/-- `a * b ≃ b * a`. -/
theorem mul_comm_eqv (a b : Q') : (a * b).eqv (b * a) := by
  show (a * b).num * ((b * a).den : Int) = (b * a).num * ((a * b).den : Int)
  show (a.num * b.num) * ((b * a).den : Int)
      = (b.num * a.num) * ((a * b).den : Int)
  rw [mul_den_cast a b, mul_den_cast b a,
      Int.mul_comm a.num b.num, Int.mul_comm b.den a.den]

/-- `(a * b) * c ≃ a * (b * c)`. -/
theorem mul_assoc_eqv (a b c : Q') : ((a * b) * c).eqv (a * (b * c)) := by
  show ((a * b) * c).num * ((a * (b * c)).den : Int)
      = (a * (b * c)).num * (((a * b) * c).den : Int)
  show ((a.num * b.num) * c.num) * ((a * (b * c)).den : Int)
      = (a.num * (b.num * c.num)) * (((a * b) * c).den : Int)
  rw [mul_den_cast (a * b) c, mul_den_cast a (b * c),
      mul_den_cast a b, mul_den_cast b c,
      Int.mul_assoc a.num b.num c.num, Int.mul_assoc a.den b.den c.den]

/-- `a * (b + c) ≃ a * b + a * c` (left-distributivity). -/
theorem mul_add_eqv (a b c : Q') : (a * (b + c)).eqv (a * b + a * c) := by
  show (a * (b + c)).num * ((a * b + a * c).den : Int)
      = (a * b + a * c).num * ((a * (b + c)).den : Int)
  have hL_num : (a * (b + c)).num
      = a.num * (b.num * (c.den : Int) + c.num * (b.den : Int)) := rfl
  have hR_num : (a * b + a * c).num
      = (a.num * b.num) * ((a * c).den : Int)
        + (a.num * c.num) * ((a * b).den : Int) := rfl
  rw [hL_num, hR_num,
      mul_den_cast a c, mul_den_cast a b,
      add_den_cast (a * b) (a * c), mul_den_cast a b, mul_den_cast a c,
      mul_den_cast a (b + c), add_den_cast b c]
  simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-! ## `1 * a ≃ a`, additive commutativity/associativity (at `eqv`) -/

/-- `1 * a ≃ a`. -/
theorem one_mul_eqv (a : Q') : ((1 : Q') * a).eqv a := by
  show ((1 : Q') * a).num * (a.den : Int) = a.num * (((1 : Q') * a).den : Int)
  rw [mul_den_cast (1 : Q') a]
  show ((1 : Int) * a.num) * (a.den : Int)
      = a.num * ((1 : Int) * (a.den : Int))
  rw [Int.one_mul, Int.one_mul, Int.mul_comm a.num (a.den : Int)]

/-- `a + b ≃ b + a`. -/
theorem add_comm_eqv (a b : Q') : (a + b).eqv (b + a) := by
  show (a + b).num * ((b + a).den : Int) = (b + a).num * ((a + b).den : Int)
  have hL : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
  have hR : (b + a).num = b.num * (a.den : Int) + a.num * (b.den : Int) := rfl
  rw [hL, hR, add_den_cast a b, add_den_cast b a]
  simp only [Int.add_mul, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm,
    Int.add_comm]

/-- `(a + b) + c ≃ a + (b + c)`. -/
theorem add_assoc_eqv (a b c : Q') : ((a + b) + c).eqv (a + (b + c)) := by
  show ((a + b) + c).num * ((a + (b + c)).den : Int)
      = (a + (b + c)).num * (((a + b) + c).den : Int)
  have hL_num : ((a + b) + c).num
      = (a.num * (b.den : Int) + b.num * (a.den : Int)) * (c.den : Int)
        + c.num * ((a + b).den : Int) := rfl
  have hR_num : (a + (b + c)).num
      = a.num * ((b + c).den : Int)
        + (b.num * (c.den : Int) + c.num * (b.den : Int)) * (a.den : Int) := rfl
  rw [hL_num, hR_num,
      add_den_cast a b, add_den_cast b c,
      add_den_cast (a + b) c, add_den_cast a b,
      add_den_cast a (b + c), add_den_cast b c]
  simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm, Int.add_comm, Int.add_left_comm, Int.add_assoc]

/-! ## Congruence of `*` over `eqv` (right factor fixed) -/

/-- `x * y * (z * w) = x * z * (y * w)` — swap the two inner factors. -/
private theorem int_AABB (x y z w : Int) :
    (x * y) * (z * w) = (x * z) * (y * w) := by
  rw [Int.mul_assoc x y (z * w), ← Int.mul_assoc y z w, Int.mul_comm y z,
      Int.mul_assoc z y w, ← Int.mul_assoc x z (y * w)]

/-- `a ≃ b → a * c ≃ b * c`.  Congruence lets us rewrite a factor inside a
product up to `eqv` (needed to commute nested powers in the geometric
step). -/
theorem mul_eqv_congr_right (a b c : Q') (h : a.eqv b) : (a * c).eqv (b * c) := by
  show (a * c).num * ((b * c).den : Int) = (b * c).num * ((a * c).den : Int)
  show (a.num * c.num) * ((b * c).den : Int)
      = (b.num * c.num) * ((a * c).den : Int)
  rw [mul_den_cast b c, mul_den_cast a c,
      int_AABB a.num c.num (b.den : Int) (c.den : Int),
      int_AABB b.num c.num (a.den : Int) (c.den : Int),
      show a.num * (b.den : Int) = b.num * (a.den : Int) from h]

/-! ## Negation laws (at `eqv`)

The sign algebra the alternating `expNeg` series needs: `(−a)·b`, `a·(−b)`,
and `−(−a)` reduce to `−(a·b)` / `a` up to `eqv`, and negation is an `eqv`
congruence.  Each is an `Int.neg_mul`/`Int.mul_neg`/`Int.neg_neg` rewrite
after the cross-product reduction. -/

/-- `(−a).den = a.den` (negation preserves the stored `denPred`). -/
theorem neg_den (a : Q') : (-a).den = a.den := rfl

/-- `(−a) * b ≃ −(a * b)`. -/
theorem neg_mul_eqv (a b : Q') : ((-a) * b).eqv (-(a * b)) := by
  show ((-a.num) * b.num) * ((a * b).den : Int)
      = (-(a.num * b.num)) * (((-a) * b).den : Int)
  rw [Int.neg_mul, mul_den_cast a b, mul_den_cast (-a) b, neg_den a]

/-- `a * (−b) ≃ −(a * b)`. -/
theorem mul_neg_eqv (a b : Q') : (a * (-b)).eqv (-(a * b)) := by
  show (a.num * (-b.num)) * ((a * b).den : Int)
      = (-(a.num * b.num)) * ((a * (-b)).den : Int)
  rw [Int.mul_neg, mul_den_cast a b, mul_den_cast a (-b), neg_den b]

/-- `−(−a) ≃ a`. -/
theorem neg_neg_eqv (a : Q') : (-(-a)).eqv a := by
  show (-(-a.num)) * (a.den : Int) = a.num * (a.den : Int)
  rw [Int.neg_neg]

/-- `−a + a ≃ 0`. -/
theorem neg_add_self_eqv (a : Q') : ((-a) + a).eqv 0 := by
  show ((-a.num) * (a.den : Int) + a.num * (a.den : Int)) * ((0 : Q').den : Int)
      = (0 : Int) * (((-a) + a).den : Int)
  have h0 : (-a.num) * (a.den : Int) + a.num * (a.den : Int) = 0 := by
    rw [← Int.add_mul, Int.add_left_neg, Int.zero_mul]
  rw [h0, Int.zero_mul, Int.zero_mul]

/-- Negation is an `eqv` congruence: `a ≃ b → −a ≃ −b`. -/
theorem neg_eqv_congr (a b : Q') (h : a.eqv b) : (-a).eqv (-b) := by
  show (-a.num) * (b.den : Int) = (-b.num) * (a.den : Int)
  rw [Int.neg_mul, Int.neg_mul,
      show a.num * (b.den : Int) = b.num * (a.den : Int) from h]

/-- `b ≃ c → a * b ≃ a * c` (congruence, left factor fixed). -/
theorem mul_eqv_congr_left (a b c : Q') (h : b.eqv c) : (a * b).eqv (a * c) := by
  show (a.num * b.num) * ((a * c).den : Int) = (a.num * c.num) * ((a * b).den : Int)
  rw [mul_den_cast a c, mul_den_cast a b,
      int_AABB a.num b.num (a.den : Int) (c.den : Int),
      int_AABB a.num c.num (a.den : Int) (b.den : Int),
      show b.num * (c.den : Int) = c.num * (b.den : Int) from h]

/-! ## Transitivity of `eqv`, additive congruence, inner swap

`eqv` is transitive (cancel the common denominator), and `+` is an `eqv`
congruence on each side.  With `add_comm_eqv`/`add_assoc_eqv` these compose
into the 4-term inner swap `(w+x)+(y+z) ≃ (w+y)+(x+z)` the block bound
needs — built from proven small steps, not AC-`simp` (which times out at
this term size). -/

/-- `a * b * c = a * c * b` on `Int` (right commutation). -/
private theorem int_mrc (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- `eqv` is transitive (cancel the common denominator `b.den > 0`). -/
theorem eqv_trans (a b c : Q') (hab : a.eqv b) (hbc : b.eqv c) : a.eqv c := by
  have hbne : (b.den : Int) ≠ 0 := by
    intro heq
    exact (Nat.pos_iff_ne_zero.mp b.den_pos) (by exact_mod_cast heq)
  show a.num * (c.den : Int) = c.num * (a.den : Int)
  apply Int.eq_of_mul_eq_mul_right hbne
  calc a.num * (c.den : Int) * (b.den : Int)
      = a.num * (b.den : Int) * (c.den : Int) := int_mrc _ _ _
    _ = b.num * (a.den : Int) * (c.den : Int) := by
        rw [show a.num * (b.den : Int) = b.num * (a.den : Int) from hab]
    _ = b.num * (c.den : Int) * (a.den : Int) := int_mrc _ _ _
    _ = c.num * (b.den : Int) * (a.den : Int) := by
        rw [show b.num * (c.den : Int) = c.num * (b.den : Int) from hbc]
    _ = c.num * (a.den : Int) * (b.den : Int) := int_mrc _ _ _

/-- `a ≃ b → a + c ≃ b + c`. -/
theorem add_eqv_congr_right (a b c : Q') (h : a.eqv b) : (a + c).eqv (b + c) := by
  show (a.num * (c.den : Int) + c.num * (a.den : Int)) * ((b + c).den : Int)
      = (b.num * (c.den : Int) + c.num * (b.den : Int)) * ((a + c).den : Int)
  rw [add_den_cast b c, add_den_cast a c, Int.add_mul, Int.add_mul,
      int_AABB a.num (c.den : Int) (b.den : Int) (c.den : Int),
      int_AABB c.num (a.den : Int) (b.den : Int) (c.den : Int),
      int_AABB b.num (c.den : Int) (a.den : Int) (c.den : Int),
      show a.num * (b.den : Int) = b.num * (a.den : Int) from h]

/-- `b ≃ c → a + b ≃ a + c` (via `add_comm` + `add_eqv_congr_right`). -/
theorem add_eqv_congr_left (a b c : Q') (h : b.eqv c) : (a + b).eqv (a + c) :=
  eqv_trans (a + b) (b + a) (a + c) (add_comm_eqv a b)
    (eqv_trans (b + a) (c + a) (a + c)
      (add_eqv_congr_right b c a h) (add_comm_eqv c a))

/-- Inner swap: `(w + x) + (y + z) ≃ (w + y) + (x + z)`. -/
theorem add_swap_inner (w x y z : Q') :
    ((w + x) + (y + z)).eqv ((w + y) + (x + z)) :=
  eqv_trans ((w + x) + (y + z)) ((w + x) + y + z) ((w + y) + (x + z))
    (eqv_symm (add_assoc_eqv (w + x) y z))
    (eqv_trans ((w + x) + y + z) (w + (x + y) + z) ((w + y) + (x + z))
      (add_eqv_congr_right ((w + x) + y) (w + (x + y)) z (add_assoc_eqv w x y))
      (eqv_trans (w + (x + y) + z) (w + (y + x) + z) ((w + y) + (x + z))
        (add_eqv_congr_right (w + (x + y)) (w + (y + x)) z
          (add_eqv_congr_left w (x + y) (y + x) (add_comm_eqv x y)))
        (eqv_trans (w + (y + x) + z) ((w + y) + x + z) ((w + y) + (x + z))
          (add_eqv_congr_right (w + (y + x)) ((w + y) + x) z
            (eqv_symm (add_assoc_eqv w y x)))
          (add_assoc_eqv (w + y) x z))))

/-- `a * 1 ≃ a` (base case of the geometric domination). -/
theorem mul_one_eqv (a : Q') : (a * 1).eqv a := by
  show (a * 1).num * (a.den : Int) = a.num * ((a * 1).den : Int)
  rw [mul_den_cast a 1]
  show (a.num * (1 : Int)) * (a.den : Int) = a.num * ((a.den : Int) * (1 : Int))
  rw [Int.mul_one, Int.mul_one]

/-! ## Left-monotonicity of `*` -/

/-- `a ≤ b → 0 ≤ c → c * a ≤ c * b`.  Derived from the right-mono lemma
in `Rationals.lean` plus commutativity, via the `eqv↔≤` bridges. -/
theorem mul_le_mul_of_nonneg_left
    (a b c : Q') (h_ab : a ≤ b) (h_c : (0 : Q') ≤ c) :
    c * a ≤ c * b := by
  have h1 : a * c ≤ b * c := mul_le_mul_of_nonneg_right a b c h_ab h_c
  exact le_trans' (c * a) (a * c) (c * b)
    (le_of_eqv (mul_comm_eqv c a))
    (le_trans' (a * c) (b * c) (c * b) h1 (le_of_eqv (mul_comm_eqv b c)))

end Q'

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.mul_den_cast
#print axioms ConstructiveReals.Q'.add_den_cast
#print axioms ConstructiveReals.Q'.mul_comm_eqv
#print axioms ConstructiveReals.Q'.mul_assoc_eqv
#print axioms ConstructiveReals.Q'.mul_add_eqv
#print axioms ConstructiveReals.Q'.one_mul_eqv
#print axioms ConstructiveReals.Q'.add_comm_eqv
#print axioms ConstructiveReals.Q'.add_assoc_eqv
#print axioms ConstructiveReals.Q'.mul_eqv_congr_right
#print axioms ConstructiveReals.Q'.neg_mul_eqv
#print axioms ConstructiveReals.Q'.mul_neg_eqv
#print axioms ConstructiveReals.Q'.neg_neg_eqv
#print axioms ConstructiveReals.Q'.neg_add_self_eqv
#print axioms ConstructiveReals.Q'.neg_eqv_congr
#print axioms ConstructiveReals.Q'.mul_eqv_congr_left
#print axioms ConstructiveReals.Q'.eqv_trans
#print axioms ConstructiveReals.Q'.add_eqv_congr_right
#print axioms ConstructiveReals.Q'.add_eqv_congr_left
#print axioms ConstructiveReals.Q'.add_swap_inner
#print axioms ConstructiveReals.Q'.mul_one_eqv
#print axioms ConstructiveReals.Q'.mul_le_mul_of_nonneg_left
