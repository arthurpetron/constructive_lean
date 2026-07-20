/-
Constructive rationals — a minimal axiom-clean ℚ built from scratch
atop Lean core's `Int` and `Nat`.

# Why this module exists

This library's constructivity policy (README) forbids Mathlib's `ℝ` (which uses
`Classical.choice` for completeness) and demands that every limit,
bound, and rate carry an explicit modulus.  For a large class of
per-step budget quantities — each naturally bounded above by an
explicit rational expression — **a rational upper bound IS an
explicit modulus**.  Full constructive reals are not required for
stating per-step bounds; exact rationals suffice.

Lean 4 core's built-in `Rat` cannot be used here: it was
empirically established that even the reflexive equality
`(3 : Rat) / 4 = (3 : Rat) / 4` proved by `rfl` reports
`depends on axioms: [propext, Classical.choice, Quot.sound]` via
`Rat.decEq`.  The axiom policy (README) forbids `Classical.choice` in
load-bearing theorems.  We therefore reconstruct ℚ from scratch
here, atop `Int` and `Nat` (both axiom-clean in Lean core).

# Representation

`Q'` carries a numerator `num : Int` and the *predecessor* of its
denominator `denPred : Nat`; the actual denominator
`den := denPred + 1` is therefore positive structurally.  We do
**not** enforce normalization (no `gcd(num, den) = 1` field).  Two
`Q'` values can represent the same rational but differ
structurally — e.g.\ `mk 1 2 = ⟨1, 1⟩` and `mk 2 4 = ⟨2, 3⟩` both
represent `1/2`.  For the intended use (constructing explicit constants
with simple denominators, then performing limited arithmetic),
this is acceptable; semantic equality and order are decidable
via cross-product comparison on `Int`.

Trade-off: unnormalized terms can grow.  The base layer does not chain
deeply enough for this to matter.  If a later phase needs
normalization, a `Q'.reduce` operation can be added without
breaking the interface.

# Boundary — what this module does NOT cover

**The ℚ-only representation handles per-step bounds, not infinite
sums.**  A statement like "f(k) ≤ q for some q : Q'" at a fixed
index `k` is a complete explicit modulus.  But global closures —

  `Σ_k a_k < ∞`
  `Σ_k a_k < B`
  `inf_k b_k > 0`

— are statements about an infinite-sum's convergence (or an
infinite-infimum's positivity).  Per-term rational bounds do
**not** automatically yield these limit facts.  The convergence
of `Σ_k a_k` to a value below a budget is a constructive-limit
statement that may require either:

  (a) A separate constructive-limit / Cauchy-style argument
      built on Q' (a small additional module, much smaller than
      full `Reals.lean`); or
  (b) A direct rational majorization showing each tail
      `Σ_{k ≥ K} a_k ≤ q` for some `q : Q'` parametrized by `K`,
      where the tail bound itself is rational; or
  (c) Full `Reals.lean` (and the completion machinery above it)
      if (a) and (b) prove insufficient.

This boundary is named here, in the very docstring of the base
module, so that no consumer silently assumes `Q'` alone is
sufficient for limit statements.
-/

namespace ConstructiveReals

/-! ## The `Q'` representation -/

/-- A rational number.  `num` is the integer numerator; `denPred + 1`
is the (positive) denominator.  See module docstring for the design
rationale (unnormalized; not Lean-core `Rat`). -/
structure Q' where
  num     : Int
  denPred : Nat
deriving DecidableEq, Repr

namespace Q'

/-- The denominator of `q`, always positive. -/
@[inline] def den (q : Q') : Nat := q.denPred + 1

theorem den_pos (q : Q') : 0 < q.den := Nat.succ_pos _

/-- Construct `n/d` for `n : Int`, `d : Nat`, `0 < d`.

The positivity hypothesis `_h` is required of the caller (so users
cannot construct nonsensical `mkPos n 0 _`) but is not used in the
body: by Nat structure, `d ≥ 1` implies `d = d.pred + 1`, so storing
`d.pred` recovers `d` as `den`.  See `mkPos_den` below for the proof. -/
@[inline] def mkPos (n : Int) (d : Nat) (_h : 0 < d) : Q' :=
  ⟨n, d.pred⟩

/-- `mkPos` produces a `Q'` with the requested denominator. -/
theorem mkPos_den (n : Int) (d : Nat) (h : 0 < d) :
    (mkPos n d h).den = d := by
  unfold mkPos den
  exact Nat.succ_pred_eq_of_pos h

/-- `mkPos` produces a `Q'` with the requested numerator. -/
theorem mkPos_num (n : Int) (d : Nat) (h : 0 < d) :
    (mkPos n d h).num = n := rfl

/-- Construct from a `Nat` numerator over denominator `d.pred + 1`. -/
@[inline] def mkN (n : Nat) (denPred : Nat) : Q' :=
  ⟨Int.ofNat n, denPred⟩

/-- Coerce an integer to `Q'` (denominator 1). -/
@[inline] def ofInt (n : Int) : Q' := ⟨n, 0⟩

/-- Coerce a natural to `Q'` (denominator 1). -/
@[inline] def ofNat (n : Nat) : Q' := ⟨Int.ofNat n, 0⟩

/-! ### Numeric literals -/

instance : Zero Q' := ⟨ofInt 0⟩
instance : One Q' := ⟨ofInt 1⟩
instance (n : Nat) : OfNat Q' n := ⟨ofNat n⟩

/-! ### Arithmetic — unnormalized, exact at the value level -/

/-- Negation: `-(n/d) = (-n)/d`. -/
@[inline] def neg (q : Q') : Q' := ⟨-q.num, q.denPred⟩

instance : Neg Q' := ⟨neg⟩

/-- Addition: `a/b + c/d = (ad + cb) / (bd)`.  Denominator is `b*d`,
both positive, so the predecessor is `b*d - 1` (Nat truncating
subtraction is well-defined here since `b*d ≥ 1`). -/
@[inline] def add (p q : Q') : Q' :=
  ⟨p.num * (q.den : Int) + q.num * (p.den : Int),
   p.den * q.den - 1⟩

instance : Add Q' := ⟨add⟩

/-- Subtraction: `p - q = p + (-q)`. -/
@[inline] def sub (p q : Q') : Q' := p + (-q)

instance : Sub Q' := ⟨sub⟩

/-- Multiplication: `(a/b) * (c/d) = (ac)/(bd)`. -/
@[inline] def mul (p q : Q') : Q' :=
  ⟨p.num * q.num, p.den * q.den - 1⟩

instance : Mul Q' := ⟨mul⟩

/-! ### Semantic equivalence and ordering

Structural equality on `Q'` is decidable (auto-derived) but
distinguishes representations of the same rational
(`mk 1 2 ≠ mk 2 4` structurally).  We additionally provide
*semantic* equivalence and order, via cross-product comparison on
`Int`.  Both are decidable because `Int` has decidable equality
and order. -/

/-- Semantic equivalence: `a/b ≃ c/d` iff `a*d = c*b`. -/
@[inline] def eqv (p q : Q') : Prop :=
  p.num * (q.den : Int) = q.num * (p.den : Int)

instance : DecidableRel Q'.eqv := fun p q =>
  decEq (p.num * (q.den : Int)) (q.num * (p.den : Int))

/-- Semantic ≤: `a/b ≤ c/d` iff `a*d ≤ c*b`  (assuming `b, d > 0`,
which is structural here). -/
@[inline] def le (p q : Q') : Prop :=
  p.num * (q.den : Int) ≤ q.num * (p.den : Int)

instance : LE Q' := ⟨le⟩

instance : DecidableRel ((· ≤ ·) : Q' → Q' → Prop) := fun p q =>
  inferInstanceAs (Decidable (p.num * (q.den : Int) ≤ q.num * (p.den : Int)))

/-- Semantic <. -/
@[inline] def lt (p q : Q') : Prop :=
  p.num * (q.den : Int) < q.num * (p.den : Int)

instance : LT Q' := ⟨lt⟩

instance : DecidableRel ((· < ·) : Q' → Q' → Prop) := fun p q =>
  inferInstanceAs (Decidable (p.num * (q.den : Int) < q.num * (p.den : Int)))

/-! ### Min and Max -/

/-- Semantic min via the decidable ≤. -/
@[inline] def min' (p q : Q') : Q' := if p ≤ q then p else q

/-- Semantic max via the decidable ≤. -/
@[inline] def max' (p q : Q') : Q' := if p ≤ q then q else p

instance : Min Q' := ⟨min'⟩
instance : Max Q' := ⟨max'⟩

/-! ### Reflexivity and identity laws

These are the load-bearing arithmetic facts needed by the Phase-3 Lean
closures downstream.  Each proof
uses only `Int.le_refl` / `Int` arithmetic identities — axiom-clean
from Lean core. -/

/-- Semantic ≤ is reflexive on `Q'`.  Follows from `Int.le_refl` on the
cross-product representation. -/
theorem le_refl' (p : Q') : p ≤ p := by
  show p.num * (p.den : Int) ≤ p.num * (p.den : Int)
  exact Int.le_refl _

/-- `p + 0 = p` structurally on `Q'`, by reduction through the `Q'.add`
formula at `q = 0` (which has `den = 1` and `num = 0`). -/
theorem add_zero' (p : Q') : p + (0 : Q') = p := by
  show Q'.add p 0 = p
  cases p with | mk num denPred =>
  -- Q'.add ⟨num, denPred⟩ ⟨0,0⟩
  --   = ⟨num*1 + 0*(denPred+1), (denPred+1)*1 - 1⟩
  --   = ⟨num, denPred⟩
  show (⟨num * ((1 : Nat) : Int) + (0 : Int) * ((denPred + 1 : Nat) : Int),
         (denPred + 1) * 1 - 1⟩ : Q') = ⟨num, denPred⟩
  congr 1
  · -- num * 1 + 0 * (denPred + 1 : Int) = num
    simp
  · -- (denPred + 1) * 1 - 1 = denPred
    simp

/-- `0 + p = p` structurally on `Q'`.  Mirror of `add_zero'` for the
left-zero case. -/
theorem zero_add' (p : Q') : (0 : Q') + p = p := by
  show Q'.add 0 p = p
  cases p with | mk num denPred =>
  -- Q'.add ⟨0, 0⟩ ⟨num, denPred⟩
  --   = ⟨0 * (denPred+1) + num * 1, 1 * (denPred+1) - 1⟩
  --   = ⟨num, denPred⟩
  show (⟨(0 : Int) * ((denPred + 1 : Nat) : Int) + num * ((1 : Nat) : Int),
         1 * (denPred + 1) - 1⟩ : Q') = ⟨num, denPred⟩
  congr 1
  · -- 0 * (denPred + 1) + num * 1 = num
    simp
  · -- 1 * (denPred + 1) - 1 = denPred
    simp

/-- `p - 0 = p` structurally on `Q'`, via `p - 0 = p + (-0) = p + 0 = p`. -/
theorem sub_zero' (p : Q') : p - (0 : Q') = p := by
  show Q'.sub p 0 = p
  unfold Q'.sub
  -- Q'.sub p 0 = p + (-0).  Q'.neg 0 = ⟨-0, 0⟩ which is structurally 0
  -- since -(0 : Int) = 0.  Then p + 0 = p by `add_zero'`.
  show p + (-(0 : Q')) = p
  have h : (-(0 : Q')) = (0 : Q') := by
    show Q'.neg 0 = 0
    -- Q'.neg ⟨0, 0⟩ = ⟨-0, 0⟩ = ⟨0, 0⟩ since -(0 : Int) = 0.
    rfl
  rw [h]
  exact add_zero' p

/-! ### Nonnegativity lemmas (for the [P2.1] concrete-`P` closure)

These let us state and discharge the simplest substantive
`KPCertificate` predicate at Q': nonnegativity of both `ρ` and `K`.
Each proof reduces to `Int.add_nonneg` / `Int.mul_nonneg`, both
axiom-free in Lean core. -/

/-- `0 ≤ p` iff its numerator is nonnegative.  Both sides reduce to
`0 ≤ p.num` after evaluating `(0 : Q').num = 0` and `(0 : Q').den = 1`. -/
theorem zero_le_iff_num_nonneg (p : Q') : (0 : Q') ≤ p ↔ (0 : Int) ≤ p.num := by
  -- LHS unfolds to (0 : Int) * p.den ≤ p.num * 1.
  show (0 : Int) * (p.den : Int) ≤ p.num * (((0 : Q').den) : Int) ↔
       (0 : Int) ≤ p.num
  show (0 : Int) * (p.den : Int) ≤ p.num * (1 : Int) ↔ (0 : Int) ≤ p.num
  simp

/-- Sum of two nonnegative `Q'` values is nonnegative.

Reduces to: if `0 ≤ p.num` and `0 ≤ q.num`, then
`0 ≤ p.num * q.den + q.num * p.den` (sum of products of nonnegs). -/
theorem zero_le_add (p q : Q') (h_p : (0 : Q') ≤ p) (h_q : (0 : Q') ≤ q) :
    (0 : Q') ≤ p + q := by
  rw [zero_le_iff_num_nonneg] at h_p h_q
  rw [zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (p + q).num
  show (0 : Int) ≤ p.num * ((q.den : Nat) : Int) + q.num * ((p.den : Nat) : Int)
  have h_q_den : (0 : Int) ≤ ((q.den : Nat) : Int) := Int.natCast_nonneg _
  have h_p_den : (0 : Int) ≤ ((p.den : Nat) : Int) := Int.natCast_nonneg _
  exact Int.add_nonneg (Int.mul_nonneg h_p h_q_den) (Int.mul_nonneg h_q h_p_den)

/-- `min` of two nonnegative `Q'` values is nonnegative.

`min p q = if p ≤ q then p else q`, so the result is one of the two
inputs — both nonnegative by hypothesis. -/
theorem zero_le_min (p q : Q') (h_p : (0 : Q') ≤ p) (h_q : (0 : Q') ≤ q) :
    (0 : Q') ≤ min p q := by
  show (0 : Q') ≤ min' p q
  unfold min'
  split <;> assumption

/-! ### Adding a nonnegative number is monotone

The Q' analog of `Int.le_add_of_nonneg_right`.  Needed by the
`prefix_plus_tail_closure` extension in `ConstructiveReals/RationalTail.lean`
for the infinite-trajectory closure framework (monotonicity of partial sums
for nonneg sequences). -/

/-- Adding a nonnegative `Q'` value cannot decrease the result: `0 ≤ b → a ≤ a + b`.

Cross-product unfolding: the goal `a.num · (a+b).den ≤ (a+b).num · a.den`
reduces, after expanding `(a+b).num = a.num·b.den + b.num·a.den` and
`(a+b).den = a.den·b.den`, to `0 ≤ b.num · a.den²`.  The latter holds
since `b.num ≥ 0` (from `0 ≤ b`) and `a.den² ≥ 0` (Nat cast).

Avoids `ring`/`linarith` to keep the axiom-gate at `[propext]` only;
proof goes through `Int.mul_assoc`, `Int.mul_comm`, `Int.add_mul`, and
`Int.le_add_of_nonneg_right` (all Lean core, axiom-clean). -/
theorem add_le_self_of_nonneg (a b : Q') (h : (0 : Q') ≤ b) : a ≤ a + b := by
  -- The goal unfolds to a cross-product inequality on Int.
  show a.num * ((a + b).den : Int) ≤ (a + b).num * (a.den : Int)
  -- Get b.num ≥ 0 from the Q' hypothesis.
  have h_b_num_nn : (0 : Int) ≤ b.num := (zero_le_iff_num_nonneg b).mp h
  -- (a + b).den as a Nat is (a.den * b.den - 1) + 1 = a.den * b.den, since
  -- the product of positive Nats is at least 1.
  have h_ab_pos : 0 < a.den * b.den :=
    Nat.mul_pos (den_pos a) (den_pos b)
  have h_ab_den_eq : (a + b).den = a.den * b.den := by
    show (Q'.add a b).denPred + 1 = a.den * b.den
    show (a.den * b.den - 1) + 1 = a.den * b.den
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp h_ab_pos))
  -- (a + b).num as Int: a.num * b.den + b.num * a.den (definition of Q'.add).
  have h_ab_num : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) :=
    rfl
  rw [h_ab_num, h_ab_den_eq]
  -- Cast Nat product to Int product: ((a.den * b.den : Nat) : Int) = a.den * b.den.
  show a.num * (((a.den * b.den : Nat) : Int))
        ≤ (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  rw [Int.natCast_mul]
  -- After expansion, we need:
  --   a.num · (a.den · b.den) ≤ (a.num · b.den + b.num · a.den) · a.den.
  -- Set up the RHS as LHS + (b.num · a.den²) via algebra; then conclude via
  -- Int.le_add_of_nonneg_right on the nonneg term b.num · a.den².
  have h_RHS_decomp :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
        = a.num * ((a.den : Int) * (b.den : Int))
          + b.num * (a.den : Int) * (a.den : Int) := by
    calc (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
        = a.num * (b.den : Int) * (a.den : Int)
          + b.num * (a.den : Int) * (a.den : Int) := Int.add_mul _ _ _
      _ = a.num * ((b.den : Int) * (a.den : Int))
          + b.num * (a.den : Int) * (a.den : Int) := by
          rw [Int.mul_assoc a.num (b.den : Int) (a.den : Int)]
      _ = a.num * ((a.den : Int) * (b.den : Int))
          + b.num * (a.den : Int) * (a.den : Int) := by
          rw [Int.mul_comm (b.den : Int) (a.den : Int)]
  rw [h_RHS_decomp]
  -- Now: a.num * (a.den * b.den) ≤ a.num * (a.den * b.den) + b.num * a.den * a.den.
  have h_a_den_nn : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have h_diff_nn : (0 : Int) ≤ b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_nonneg (Int.mul_nonneg h_b_num_nn h_a_den_nn) h_a_den_nn
  exact Int.le_add_of_nonneg_right h_diff_nn

/-! ### Left-monotonicity of `+`

Adding a Q' value on the left preserves ≤: `b ≤ c → a + b ≤ a + c`.
Needed downstream for the formal Conjecture
7.4 closure downstream.

Proof: cross-product expansion gives
``(a + b).num · (a + c).den ≤ (a + c).num · (a + b).den``
⟺ ``a.den · b.den · c.den · a.num + a.den² · c.den · b.num
   ≤ a.den · b.den · c.den · a.num + a.den² · b.den · c.num``
⟺ ``a.den² · (b.num · c.den) ≤ a.den² · (c.num · b.den)``
which follows from `b ≤ c` (which IS `b.num · c.den ≤ c.num · b.den`)
multiplied by `a.den² ≥ 0`. -/

/-- Algebraic rearrangement helper: `x · y · (z · w) = x · z · (y · w)`
when only `y, z` are swapped.  Used in `add_le_add_left` proof. -/
private theorem int_swap_middle (x y z w : Int) :
    x * y * (z * w) = x * z * (y * w) := by
  rw [Int.mul_assoc x y (z * w), Int.mul_assoc x z (y * w)]
  congr 1
  rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm y z]

/-- Algebraic rearrangement helper: `x · y · (y · z) = x · z · (y · y)`. -/
private theorem int_pull_square (x y z : Int) :
    x * y * (y * z) = x * z * (y * y) := by
  -- Strategy: y · (y · z) = (y · y) · z = z · (y · y).
  rw [Int.mul_assoc x y (y * z)]            -- x * (y * (y * z))
  rw [← Int.mul_assoc y y z]                 -- x * (y * y * z)
  rw [Int.mul_comm (y * y) z]                -- x * (z * (y * y))
  rw [← Int.mul_assoc x z (y * y)]           -- x * z * (y * y)

/-- A specialization of `Int.mul_comm`/`Int.mul_assoc`: swap the second and
third factors of a triple product. -/
private theorem int_mul_right_comm (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- Adding a Q' value on the left preserves ≤: `b ≤ c → a + b ≤ a + c`. -/
theorem add_le_add_left (a b c : Q') (h_bc : b ≤ c) : a + b ≤ a + c := by
  show (a + b).num * ((a + c).den : Int) ≤ (a + c).num * ((a + b).den : Int)
  -- Get the underlying b ≤ c cross-product.
  have h_b_le_c : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h_bc
  -- Compute the denominators definitionally.
  have h_ab_den : ((a + b).den : Int) = (a.den : Int) * (b.den : Int) := by
    show (((a.den * b.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (b.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos b))))]
    exact Int.natCast_mul a.den b.den
  have h_ac_den : ((a + c).den : Int) = (a.den : Int) * (c.den : Int) := by
    show (((a.den * c.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (c.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos c))))]
    exact Int.natCast_mul a.den c.den
  -- Numerators are definitional.
  have h_ab_num : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
  have h_ac_num : (a + c).num = a.num * (c.den : Int) + c.num * (a.den : Int) := rfl
  rw [h_ab_num, h_ac_num, h_ab_den, h_ac_den]
  -- Goal: (a.num·b.den + b.num·a.den)·(a.den·c.den)
  --        ≤ (a.num·c.den + c.num·a.den)·(a.den·b.den).
  -- Distribute via Int.add_mul on both sides.
  rw [Int.add_mul, Int.add_mul]
  -- Goal: a.num·b.den·(a.den·c.den) + b.num·a.den·(a.den·c.den)
  --        ≤ a.num·c.den·(a.den·b.den) + c.num·a.den·(a.den·b.den).
  -- Rewrite the first term on each side to a common form
  -- a.num·a.den·(b.den·c.den) via int_swap_middle.
  rw [int_swap_middle a.num (b.den : Int) (a.den : Int) (c.den : Int)]
  -- LHS first term: a.num·a.den·(b.den·c.den).  Same target for RHS:
  rw [int_swap_middle a.num (c.den : Int) (a.den : Int) (b.den : Int)]
  -- RHS first term: a.num·a.den·(c.den·b.den).  Make them match via mul_comm:
  rw [show ((c.den : Int) * (b.den : Int)) = ((b.den : Int) * (c.den : Int))
       from Int.mul_comm _ _]
  -- Now both first terms are a.num·a.den·(b.den·c.den).  Use Int.add_le_add_left.
  -- Reduce the second-term inequality:
  --   b.num·a.den·(a.den·c.den) ≤ c.num·a.den·(a.den·b.den)
  -- Rewrite each side via int_pull_square:
  rw [int_pull_square b.num (a.den : Int) (c.den : Int)]
  rw [int_pull_square c.num (a.den : Int) (b.den : Int)]
  -- Goal: a.num·a.den·(b.den·c.den) + b.num·c.den·(a.den·a.den)
  --        ≤ a.num·a.den·(b.den·c.den) + c.num·b.den·(a.den·a.den).
  -- Strip the common first term:
  apply Int.add_le_add_left
  -- Goal: b.num·c.den·(a.den·a.den) ≤ c.num·b.den·(a.den·a.den).
  -- This is h_b_le_c (b.num·c.den ≤ c.num·b.den) scaled by a.den² ≥ 0.
  have h_a_den_nn : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  exact Int.mul_le_mul_of_nonneg_right h_b_le_c
    (Int.mul_nonneg h_a_den_nn h_a_den_nn)

/-! ### Multiplication: nonneg-preservation and right-monotonicity

Needed by `ConstructiveReals/Geometric.lean` for the geometric-tail
closure downstream.  Proofs use cross-product
manipulation + `Int.mul_le_mul_of_nonneg_right` / `Int.mul_nonneg`. -/

/-- Product of two nonneg `Q'` values is nonneg.  Reduces to `0 ≤ a.num · b.num`
via `(a*b).num = a.num · b.num` definitionally. -/
theorem mul_nonneg (a b : Q') (h_a : (0 : Q') ≤ a) (h_b : (0 : Q') ≤ b) :
    (0 : Q') ≤ a * b := by
  rw [zero_le_iff_num_nonneg] at h_a h_b
  rw [zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (a * b).num
  show (0 : Int) ≤ a.num * b.num
  exact Int.mul_nonneg h_a h_b

/-- Multiplying both sides of `a ≤ b` by `c ≥ 0` preserves `≤`:
`a ≤ b → 0 ≤ c → a * c ≤ b * c`. -/
theorem mul_le_mul_of_nonneg_right
    (a b c : Q') (h_ab : a ≤ b) (h_c : (0 : Q') ≤ c) :
    a * c ≤ b * c := by
  show (a * c).num * ((b * c).den : Int)
      ≤ (b * c).num * ((a * c).den : Int)
  -- (a*c).num = a.num * c.num; (a*c).den = a.den * c.den.
  have h_ab_num : (a * c).num = a.num * c.num := rfl
  have h_bc_num : (b * c).num = b.num * c.num := rfl
  have h_ac_den : ((a * c).den : Int) = (a.den : Int) * (c.den : Int) := by
    show (((a.den * c.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (c.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos c))))]
    exact Int.natCast_mul a.den c.den
  have h_bc_den : ((b * c).den : Int) = (b.den : Int) * (c.den : Int) := by
    show (((b.den * c.den - 1) + 1 : Nat) : Int) = (b.den : Int) * (c.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos b) (den_pos c))))]
    exact Int.natCast_mul b.den c.den
  rw [h_ab_num, h_bc_num, h_ac_den, h_bc_den]
  -- Goal: (a.num · c.num) · (b.den · c.den) ≤ (b.num · c.num) · (a.den · c.den).
  -- Rearrange both sides using int_swap_middle and int_pull_square-style helpers.
  -- LHS = (a.num · b.den) · (c.num · c.den) (swap middle: c.num ↔ b.den)
  -- RHS = (b.num · a.den) · (c.num · c.den) (swap middle: c.num ↔ a.den)
  -- Then h_ab gives (a.num · b.den) ≤ (b.num · a.den), and c.num · c.den ≥ 0.
  rw [int_swap_middle a.num c.num (b.den : Int) (c.den : Int)]
  rw [int_swap_middle b.num c.num (a.den : Int) (c.den : Int)]
  -- Goal: a.num · b.den · (c.num · c.den) ≤ b.num · a.den · (c.num · c.den).
  -- Both sides have (c.num · c.den) on the right; use Int.mul_le_mul_of_nonneg_right.
  have h_c_nn_num : (0 : Int) ≤ c.num :=
    (zero_le_iff_num_nonneg c).mp h_c
  have h_c_den_nn : (0 : Int) ≤ (c.den : Int) := Int.natCast_nonneg _
  have h_c_prod_nn : (0 : Int) ≤ c.num * (c.den : Int) :=
    Int.mul_nonneg h_c_nn_num h_c_den_nn
  have h_ab_cp : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h_ab
  exact Int.mul_le_mul_of_nonneg_right h_ab_cp h_c_prod_nn

/-- Adding a Q' value on the right preserves ≤: `a ≤ b → a + c ≤ b + c`.
Mirror of `add_le_add_left`. Proof structure is symmetric: cross-product
expansion yields a target that decomposes as (common term in a, b, c.den²)
+ (term comparison after scaling h_ab by c.den²). -/
theorem add_le_add_right (a b c : Q') (h_ab : a ≤ b) : a + c ≤ b + c := by
  show (a + c).num * ((b + c).den : Int)
      ≤ (b + c).num * ((a + c).den : Int)
  have h_a_le_b : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h_ab
  have h_ac_den : ((a + c).den : Int) = (a.den : Int) * (c.den : Int) := by
    show (((a.den * c.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (c.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos c))))]
    exact Int.natCast_mul a.den c.den
  have h_bc_den : ((b + c).den : Int) = (b.den : Int) * (c.den : Int) := by
    show (((b.den * c.den - 1) + 1 : Nat) : Int) = (b.den : Int) * (c.den : Int)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos b) (den_pos c))))]
    exact Int.natCast_mul b.den c.den
  have h_ac_num : (a + c).num = a.num * (c.den : Int) + c.num * (a.den : Int) := rfl
  have h_bc_num : (b + c).num = b.num * (c.den : Int) + c.num * (b.den : Int) := rfl
  rw [h_ac_num, h_bc_num, h_ac_den, h_bc_den]
  -- Goal: (a.num·c.den + c.num·a.den) · (b.den·c.den)
  --      ≤ (b.num·c.den + c.num·b.den) · (a.den·c.den)
  -- After distribution and rearrangement, this reduces to
  --   c.num·a.den·b.den·c.den + a.num·c.den·b.den·c.den
  --   ≤ c.num·a.den·b.den·c.den + b.num·c.den·a.den·c.den
  -- where the first terms cancel and the remaining inequality is
  -- (a.num·b.den) · (c.den·c.den) ≤ (b.num·a.den) · (c.den·c.den),
  -- which follows from h_a_le_b scaled by c.den² ≥ 0.
  -- We bypass step-by-step rewriting and prove via a single calc chain:
  have h_c_den_nn : (0 : Int) ≤ (c.den : Int) := Int.natCast_nonneg _
  have h_c_den_sq_nn : (0 : Int) ≤ (c.den : Int) * (c.den : Int) :=
    Int.mul_nonneg h_c_den_nn h_c_den_nn
  have h_scaled :
      a.num * (b.den : Int) * ((c.den : Int) * (c.den : Int))
        ≤ b.num * (a.den : Int) * ((c.den : Int) * (c.den : Int)) :=
    Int.mul_le_mul_of_nonneg_right h_a_le_b h_c_den_sq_nn
  -- Show that both sides of the goal equal a "common term + the scaled term":
  -- LHS = (a.num·c.den + c.num·a.den) · (b.den·c.den)
  --     = a.num·c.den·b.den·c.den + c.num·a.den·b.den·c.den
  -- RHS = (b.num·c.den + c.num·b.den) · (a.den·c.den)
  --     = b.num·c.den·a.den·c.den + c.num·b.den·a.den·c.den
  -- We need: a.num·c.den·b.den·c.den ≤ b.num·c.den·a.den·c.den (after equating the c.num terms).
  -- Use int_swap_middle: a.num·c.den·(b.den·c.den) = a.num·b.den·(c.den·c.den).
  --                       b.num·c.den·(a.den·c.den) = b.num·a.den·(c.den·c.den).
  -- Same for the c.num terms.
  have h_LHS_eq :
      (a.num * (c.den : Int) + c.num * (a.den : Int))
        * ((b.den : Int) * (c.den : Int))
      = a.num * (b.den : Int) * ((c.den : Int) * (c.den : Int))
        + c.num * (a.den : Int) * ((b.den : Int) * (c.den : Int)) := by
    rw [Int.add_mul]
    congr 1
    exact int_swap_middle a.num (c.den : Int) (b.den : Int) (c.den : Int)
  have h_RHS_eq :
      (b.num * (c.den : Int) + c.num * (b.den : Int))
        * ((a.den : Int) * (c.den : Int))
      = b.num * (a.den : Int) * ((c.den : Int) * (c.den : Int))
        + c.num * (b.den : Int) * ((a.den : Int) * (c.den : Int)) := by
    rw [Int.add_mul]
    congr 1
    exact int_swap_middle b.num (c.den : Int) (a.den : Int) (c.den : Int)
  rw [h_LHS_eq, h_RHS_eq]
  -- Need: a.num·b.den·c.den² + c.num·a.den·(b.den·c.den)
  --     ≤ b.num·a.den·c.den² + c.num·b.den·(a.den·c.den)
  -- The second terms are equal: c.num·a.den·(b.den·c.den) = c.num·b.den·(a.den·c.den).
  -- (Both equal c.num·a.den·b.den·c.den after expansion.)
  have h_second_eq :
      c.num * (a.den : Int) * ((b.den : Int) * (c.den : Int))
      = c.num * (b.den : Int) * ((a.den : Int) * (c.den : Int)) := by
    -- c.num·a.den·(b.den·c.den) = c.num·(a.den·b.den·c.den)
    rw [Int.mul_assoc (c.num) (a.den : Int) ((b.den : Int) * (c.den : Int))]
    rw [Int.mul_assoc (c.num) (b.den : Int) ((a.den : Int) * (c.den : Int))]
    congr 1
    -- a.den·(b.den·c.den) = b.den·(a.den·c.den)
    rw [← Int.mul_assoc (a.den : Int) (b.den : Int) (c.den : Int)]
    rw [← Int.mul_assoc (b.den : Int) (a.den : Int) (c.den : Int)]
    congr 1
    exact Int.mul_comm (a.den : Int) (b.den : Int)
  rw [h_second_eq]
  -- Now: a.num·b.den·c.den² + X ≤ b.num·a.den·c.den² + X.
  -- Use Int.add_le_add_right (= add_le_add_right on Int):
  exact Int.add_le_add_right h_scaled _

/-! ### Semantic equivalence: refl, symm, and the `eqv → le` bridge

`Q'.eqv` was defined above as `a.num · b.den = b.num · a.den`.  The
following lemmas turn `eqv` into a usable chaining tool: refl/symm/trans,
and the bridge to `Q'.le`. -/

/-- Reflexivity of `Q'.eqv`. -/
theorem eqv_refl (a : Q') : a.eqv a := rfl

/-- Symmetry of `Q'.eqv`. -/
theorem eqv_symm {a b : Q'} (h : a.eqv b) : b.eqv a := h.symm

/-- `a.eqv b → a ≤ b`: semantic-equality implies semantic-≤. -/
theorem le_of_eqv {a b : Q'} (h : a.eqv b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  exact Int.le_of_eq h

/-- `a.eqv b → b ≤ a`: the symmetric direction. -/
theorem ge_of_eqv {a b : Q'} (h : a.eqv b) : b ≤ a := by
  show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  exact Int.le_of_eq h.symm

/-! ### Transitivity of `≤`

The key arithmetic identity for chaining inequalities at Q'.  Proof goes
through the cross-product representation and uses `Int.le_of_mul_le_mul_right`
to cancel the middle denominator. -/

/-- Transitivity of `Q'.le`: `p ≤ q ≤ r ⟹ p ≤ r`.

Proof:
- `p ≤ q` unfolds to `p.num * q.den ≤ q.num * p.den`.
- `q ≤ r` unfolds to `q.num * r.den ≤ r.num * q.den`.
- Multiply each by a positive denominator factor and chain via the
  `int_mul_right_comm` helper to rearrange triple products.
- Cancel the resulting `q.den > 0` via `Int.le_of_mul_le_mul_right`. -/
theorem le_trans' (p q r : Q') (h_pq : p ≤ q) (h_qr : q ≤ r) : p ≤ r := by
  show p.num * (r.den : Int) ≤ r.num * (p.den : Int)
  have h1 : p.num * (q.den : Int) ≤ q.num * (p.den : Int) := h_pq
  have h2 : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := h_qr
  have h_p_nn : (0 : Int) ≤ (p.den : Int) := Int.natCast_nonneg _
  have h_r_nn : (0 : Int) ≤ (r.den : Int) := Int.natCast_nonneg _
  have step1 : p.num * (q.den : Int) * (r.den : Int)
             ≤ q.num * (p.den : Int) * (r.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h1 h_r_nn
  have step2 : q.num * (r.den : Int) * (p.den : Int)
             ≤ r.num * (q.den : Int) * (p.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h2 h_p_nn
  have e1 : q.num * (p.den : Int) * (r.den : Int)
          = q.num * (r.den : Int) * (p.den : Int) :=
    int_mul_right_comm q.num (p.den : Int) (r.den : Int)
  have e2 : r.num * (q.den : Int) * (p.den : Int)
          = r.num * (p.den : Int) * (q.den : Int) :=
    int_mul_right_comm r.num (q.den : Int) (p.den : Int)
  have e3 : p.num * (q.den : Int) * (r.den : Int)
          = p.num * (r.den : Int) * (q.den : Int) :=
    int_mul_right_comm p.num (q.den : Int) (r.den : Int)
  have chain :
      p.num * (r.den : Int) * (q.den : Int)
        ≤ r.num * (p.den : Int) * (q.den : Int) := by
    calc p.num * (r.den : Int) * (q.den : Int)
        = p.num * (q.den : Int) * (r.den : Int) := e3.symm
      _ ≤ q.num * (p.den : Int) * (r.den : Int) := step1
      _ = q.num * (r.den : Int) * (p.den : Int) := e1
      _ ≤ r.num * (q.den : Int) * (p.den : Int) := step2
      _ = r.num * (p.den : Int) * (q.den : Int) := e2
  have h_q_pos : (0 : Int) < (q.den : Int) := by
    exact_mod_cast Q'.den_pos q
  exact Int.le_of_mul_le_mul_right chain h_q_pos

/-! ## Spec-quoted SU(2) Casimir constants (P1.1 mirror, ℚ form)

The Casimirs that representation-theoretic consumers expose as
`4 · C_2(j) ∈ ℕ` can now be exposed at their natural rational form
`C_2(j) ∈ Q'`.  These are the constants Phase-3 milestones consume
via `Q'`.  All are `rfl`-equal in their canonical `Q'.mk`
representation. -/

/-- `C_2(0) = 0`. -/
def C2_zero : Q' := 0

/-- `C_2(1/2) = 3/4` — the smallest nonzero Casimir, the κ_{SU(2)}
input to downstream buffer-overlap measures. -/
def C2_oneHalf : Q' := mkPos 3 4 (by decide)

/-- `C_2(1) = 2`. -/
def C2_one : Q' := ofNat 2

/-- `C_2(3/2) = 15/4`. -/
def C2_threeHalves : Q' := mkPos 15 4 (by decide)

/-- `C_2(2) = 6`. -/
def C2_two : Q' := ofNat 6

/-! ## Spec values, verified by computation -/

theorem C2_oneHalf_num : C2_oneHalf.num = 3 := rfl
theorem C2_oneHalf_den : C2_oneHalf.den = 4 := rfl
theorem C2_one_num : C2_one.num = 2 := rfl
theorem C2_one_den : C2_one.den = 1 := rfl
theorem C2_threeHalves_num : C2_threeHalves.num = 15 := rfl
theorem C2_threeHalves_den : C2_threeHalves.den = 4 := rfl

/-- `C_2(1/2) = 3/4` as a semantic equivalence to the canonical
representation `mkPos 3 4 _`.  Holds by `rfl` since both sides have
identical numerator and denominator. -/
theorem C2_oneHalf_eqv : C2_oneHalf.eqv (mkPos 3 4 (by decide)) := by
  unfold Q'.eqv
  rfl

/-- `C_2(1/2) ≤ C_2(1)` — the spectrum is monotone. -/
theorem C2_oneHalf_le_one : C2_oneHalf ≤ C2_one := by
  show (3 : Int) * (1 : Int) ≤ (2 : Int) * (4 : Int)
  decide

/-- `0 < C_2(1/2)` — the smallest *nonzero* Casimir is positive. -/
theorem C2_oneHalf_pos : (0 : Q') < C2_oneHalf := by
  show (0 : Int) * (4 : Int) < (3 : Int) * (1 : Int)
  decide

end Q'

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.den_pos
#print axioms ConstructiveReals.Q'.mkPos_den
#print axioms ConstructiveReals.Q'.mkPos_num
#print axioms ConstructiveReals.Q'.C2_oneHalf_num
#print axioms ConstructiveReals.Q'.C2_oneHalf_den
#print axioms ConstructiveReals.Q'.C2_one_num
#print axioms ConstructiveReals.Q'.C2_threeHalves_num
#print axioms ConstructiveReals.Q'.C2_oneHalf_eqv
#print axioms ConstructiveReals.Q'.C2_oneHalf_le_one
#print axioms ConstructiveReals.Q'.C2_oneHalf_pos
#print axioms ConstructiveReals.Q'.le_refl'
#print axioms ConstructiveReals.Q'.add_zero'
#print axioms ConstructiveReals.Q'.zero_add'
#print axioms ConstructiveReals.Q'.sub_zero'
#print axioms ConstructiveReals.Q'.zero_le_iff_num_nonneg
#print axioms ConstructiveReals.Q'.zero_le_add
#print axioms ConstructiveReals.Q'.zero_le_min
#print axioms ConstructiveReals.Q'.add_le_self_of_nonneg
#print axioms ConstructiveReals.Q'.add_le_add_left
#print axioms ConstructiveReals.Q'.mul_nonneg
#print axioms ConstructiveReals.Q'.mul_le_mul_of_nonneg_right
#print axioms ConstructiveReals.Q'.add_le_add_right
#print axioms ConstructiveReals.Q'.eqv_refl
#print axioms ConstructiveReals.Q'.eqv_symm
#print axioms ConstructiveReals.Q'.le_of_eqv
#print axioms ConstructiveReals.Q'.ge_of_eqv
#print axioms ConstructiveReals.Q'.le_trans'
