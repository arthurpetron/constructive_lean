/-
The geometric-tail closed form — the piece `Geometric.lean`'s "Open work"
section deferred for want of `Q'` multiplicative arithmetic.

With the semiring-`eqv` layer of `RationalsMul.lean` in hand, the
inductive bound

    ∀ N, Σ_{k<N} η_max·rᵏ + r^N·H ≤ H        (from η_max + r·H ≤ H)

is provable directly, and its corollary `Σ_{k<N} η_max·rᵏ ≤ H` is the
uniform-in-N geometric tail bound the σ̂-budget and the `expNeg` Cauchy
modulus both need.  This realizes `geometric_tail_closure_strong` /
`geometric_tail_closure` from `Geometric.lean`'s open-work list.

`H` plays the role of the closed-form sum `η_max/(1−r)`: the recurrence
`η_max + r·H ≤ H` is exactly `H ≥ η_max + r·H`, i.e. `H` dominates one
geometric step, which by induction dominates every partial sum.

# Axiom-gate (see README: axiom policy)

Every theorem reports `[propext]`.  No `Classical.*`, no `Quot.sound`,
no `sorryAx`.
-/

import ConstructiveReals.Geometric
import ConstructiveReals.RationalsMul

namespace ConstructiveReals.RationalTail

open ConstructiveReals

/-- **The geometric single step.**  For any `s ≥ 0` (instantiated at
`s = r^N`), one step of the recurrence `η_max + r·H ≤ H` scaled by `s`:

    η_max·s + (r·s)·H ≤ s·H.

Proved by chaining the `eqv` rearrangements (`mul_comm`, `mul_assoc`,
`mul_add`, congruence) through `≤` via `le_of_eqv`/`ge_of_eqv` and the
additive monotonicity lemmas — no additive congruence needed. -/
theorem geo_step (η_max r H s : Q')
    (h_s : (0 : Q') ≤ s) (h_rec : η_max + r * H ≤ H) :
    η_max * s + (r * s) * H ≤ s * H := by
  -- (r·s)·H ≤ s·(r·H)  [commute r,s inside the product, then reassociate]
  have h2 : (r * s) * H ≤ s * (r * H) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right (r * s) (s * r) H (Q'.mul_comm_eqv r s)))
      (Q'.le_of_eqv (Q'.mul_assoc_eqv s r H))
  -- η_max·s ≤ s·η_max
  have h1 : η_max * s ≤ s * η_max := Q'.le_of_eqv (Q'.mul_comm_eqv η_max s)
  -- assemble: replace each summand up to ≤, fold via distributivity, scale recurrence
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (η_max * s) ((r * s) * H) (s * (r * H)) h2)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right (η_max * s) (s * η_max) (s * (r * H)) h1)
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.mul_add_eqv s η_max (r * H)))
        (Q'.mul_le_mul_of_nonneg_left (η_max + r * H) H s h_rec h_s)))

/-- **Strong geometric invariant.**  `Σ_{k<N} η_max·rᵏ + r^N·H ≤ H` for
every `N`, from `η_max + r·H ≤ H` (with `r, H ≥ 0`).  Structural
induction on `N`; the step uses `geo_step` at `s = r^N` plus additive
associativity to regroup. -/
theorem geometric_strong (η_max r H : Q')
    (h_r : (0 : Q') ≤ r) (h_H : (0 : Q') ≤ H) (h_rec : η_max + r * H ≤ H) :
    ∀ N, finSum (fun k => η_max * r ^ k) N + r ^ N * H ≤ H
  | 0 => by
    show (0 : Q') + (1 : Q') * H ≤ H
    rw [Q'.zero_add']
    exact Q'.le_of_eqv (Q'.one_mul_eqv H)
  | N + 1 => by
    have IH := geometric_strong η_max r H h_r h_H h_rec N
    have h_s : (0 : Q') ≤ r ^ N := Q'.pow_nonneg r h_r N
    have STEP : η_max * r ^ N + (r * r ^ N) * H ≤ r ^ N * H :=
      geo_step η_max r H (r ^ N) h_s h_rec
    show (finSum (fun k => η_max * r ^ k) N + η_max * r ^ N) + (r * r ^ N) * H ≤ H
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_assoc_eqv (finSum (fun k => η_max * r ^ k) N)
        (η_max * r ^ N) ((r * r ^ N) * H)))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left (finSum (fun k => η_max * r ^ k) N)
          (η_max * r ^ N + (r * r ^ N) * H) (r ^ N * H) STEP)
        IH)

/-- **Geometric tail closure.**  Every partial sum of the geometric
sequence `η_max·rᵏ` is bounded by `H`, given the one-step recurrence.
This is the uniform-in-N rational tail bound — the closed form the
σ̂-budget tail and `expNeg`'s modulus consume. -/
theorem geometric_tail_closure (η_max r H : Q')
    (h_r : (0 : Q') ≤ r) (h_H : (0 : Q') ≤ H) (h_rec : η_max + r * H ≤ H) :
    ∀ N, finSum (fun k => η_max * r ^ k) N ≤ H := by
  intro N
  have h_tail_nn : (0 : Q') ≤ r ^ N * H :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg r h_r N) h_H
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (finSum (fun k => η_max * r ^ k) N) (r ^ N * H) h_tail_nn)
    (geometric_strong η_max r H h_r h_H h_rec N)

end ConstructiveReals.RationalTail

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.RationalTail.geo_step
#print axioms ConstructiveReals.RationalTail.geometric_strong
#print axioms ConstructiveReals.RationalTail.geometric_tail_closure
