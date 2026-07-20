/-
Algebra of `finSum` — the distributivity / additivity equalities the Cauchy
product needs, beyond the inequalities already in `RationalTail`/`SpectralGap`.

`finSum f n = Σ_{k<n} f k` (Nat-recursive, `RationalTail.lean`).  This module
adds the `Q'.eqv` equalities:

- `finSum_mul_const` / `const_mul_finSum` — pull a constant out of a sum,
- `finSum_add` — a sum of pointwise sums splits,
- `zero_mul_eqv` / `mul_zero_eqv` — the `Q'` zero-product facts they rest on.

These are the building blocks for `(Σ_i a_i)(Σ_j b_j) = Σ_i Σ_j a_i b_j`, the
first step of the Cauchy-product proof of `eˣ·e⁻ˣ = 1`.

# Axiom-gate (see README: axiom policy)

`[propext]` only.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.RationalTail
import ConstructiveReals.RationalsMul
import ConstructiveReals.CRealMul

namespace ConstructiveReals

namespace Q'

/-- `a · 0 ≃ 0`. -/
theorem mul_zero_eqv (a : Q') : (a * (0 : Q')).eqv 0 := by
  have h : (a * (0 : Q')).eqv ((0 : Q') * a) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a 0) (Q'.eqv_refl _)
  -- reduce to showing `(0 * a) ≃ 0`
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv a 0) ?_
  -- `(0 * a).num = 0` so cross-multiplication is `0 = 0`
  show ((0 : Q') * a).num * ((0 : Q').den : Int) = (0 : Q').num * (((0 : Q') * a).den : Int)
  have e : ((0 : Q') * a).num = 0 := by
    show (0 : Q').num * a.num = 0
    show (0 : Int) * a.num = 0
    exact Int.zero_mul _
  rw [e]
  show (0 : Int) = (0 : Q').num * _
  show (0 : Int) = (0 : Int) * _
  rw [Int.zero_mul]

/-- `0 · a ≃ 0`. -/
theorem zero_mul_eqv (a : Q') : ((0 : Q') * a).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv 0 a) (Q'.mul_zero_eqv a)

end Q'

namespace RationalTail

open ConstructiveReals

/-- Termwise `Q'.eqv` lifts to `finSum` (local copy; the `SpectralGap` version
lives downstream of this module). -/
theorem finSum_eqv_congr (f g : QSeq) (h : ∀ i, (f i).eqv (g i)) :
    ∀ n, (finSum f n).eqv (finSum g n)
  | 0 => Q'.eqv_refl 0
  | n + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (finSum f n) (finSum g n) (f n) (finSum_eqv_congr f g h n))
        (Q'.add_eqv_congr_left (finSum g n) (f n) (g n) (h n))

/-- Pull a constant factor out on the right: `(Σ f)·c ≃ Σ (f·c)`. -/
theorem finSum_mul_const (f : QSeq) (c : Q') :
    ∀ n, (finSum f n * c).eqv (finSum (fun i => f i * c) n)
  | 0 => by
      show ((0 : Q') * c).eqv 0
      exact Q'.zero_mul_eqv c
  | n + 1 => by
      show ((finSum f n + f n) * c).eqv (finSum (fun i => f i * c) n + f n * c)
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (finSum f n) (f n) c) ?_
      exact Q'.add_eqv_congr_right (finSum f n * c) (finSum (fun i => f i * c) n) (f n * c)
        (finSum_mul_const f c n)

/-- Pull a constant factor out on the left: `c·(Σ f) ≃ Σ (c·f)`. -/
theorem const_mul_finSum (f : QSeq) (c : Q') (n : Nat) :
    (c * finSum f n).eqv (finSum (fun i => c * f i) n) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv c (finSum f n)) ?_
  refine Q'.eqv_trans _ _ _ (finSum_mul_const f c n) ?_
  exact finSum_eqv_congr (fun i => f i * c) (fun i => c * f i)
    (fun i => Q'.mul_comm_eqv (f i) c) n

/-- A sum of pointwise sums splits: `Σ (f + g) ≃ Σ f + Σ g`. -/
theorem finSum_add (f g : QSeq) :
    ∀ n, (finSum (fun i => f i + g i) n).eqv (finSum f n + finSum g n)
  | 0 => by
      show ((0 : Q')).eqv ((0 : Q') + (0 : Q'))
      decide
  | n + 1 => by
      show ((finSum (fun i => f i + g i) n) + (f n + g n)).eqv
          ((finSum f n + f n) + (finSum g n + g n))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f n + g n) (finSum_add f g n)) ?_
      -- (Σf + Σg) + (f n + g n) ≃ (Σf + f n) + (Σg + g n) : commutative regrouping
      have lhs : ((finSum f n + finSum g n) + (f n + g n)).eqv
          ((finSum f n + f n) + (finSum g n + g n)) := by
        have a1 := Q'.add_assoc_eqv (finSum f n + finSum g n) (f n) (g n)
        -- (A+B)+(f+g) ≃ ((A+B)+f)+g
        have a2 : (((finSum f n + finSum g n) + f n) + g n).eqv
            (((finSum f n + f n) + finSum g n) + g n) := by
          refine Q'.add_eqv_congr_right _ _ (g n) ?_
          -- (A+B)+f ≃ (A+f)+B
          have b1 := Q'.add_assoc_eqv (finSum f n) (finSum g n) (f n)
          have b2 : (finSum f n + (finSum g n + f n)).eqv (finSum f n + (f n + finSum g n)) :=
            Q'.add_eqv_congr_left (finSum f n) _ _ (Q'.add_comm_eqv (finSum g n) (f n))
          have b3 := Q'.eqv_symm (Q'.add_assoc_eqv (finSum f n) (f n) (finSum g n))
          exact Q'.eqv_trans _ _ _ b1 (Q'.eqv_trans _ _ _ b2 b3)
        -- ((A+f)+B)+g ≃ (A+f)+(B+g)
        have a3 := Q'.add_assoc_eqv (finSum f n + f n) (finSum g n) (g n)
        exact Q'.eqv_trans _ _ _ (Q'.eqv_symm a1) (Q'.eqv_trans _ _ _ a2 a3)
      exact lhs

/-- **Double-sum index swap on `finSum`.**
`Σ_{a<m} Σ_{b<n} g a b ≃ Σ_{b<n} Σ_{a<m} g a b`.  Induction on the outer index `m`,
peeling the outer index and folding it into each inner sum via `finSum_add`. -/
theorem finSum_swap (g : Nat → Nat → Q') :
    ∀ m n, (finSum (fun a => finSum (fun b => g a b) n) m).eqv
        (finSum (fun b => finSum (fun a => g a b) m) n)
  | 0, n => by
      show (0 : Q').eqv (finSum (fun b => finSum (fun a => g a b) 0) n)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ (fun _ => 0) (fun _ => Q'.eqv_refl 0) n) ?_
      rw [finSum_zero_seq n]
      exact Q'.eqv_refl 0
  | m + 1, n => by
      show (finSum (fun a => finSum (fun b => g a b) n) m + finSum (fun b => g m b) n).eqv
          (finSum (fun b => finSum (fun a => g a b) (m + 1)) n)
      -- RHS inner (m+1)-sum splits: Σ_{a<m+1} g a b = Σ_{a<m} g a b + g m b.
      refine Q'.eqv_trans _ _ _ ?_
        (Q'.eqv_symm (finSum_add (fun b => finSum (fun a => g a b) m) (fun b => g m b) n))
      exact Q'.add_eqv_congr_right _ _ (finSum (fun b => g m b) n) (finSum_swap g m n)

end RationalTail

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.mul_zero_eqv
#print axioms ConstructiveReals.Q'.zero_mul_eqv
#print axioms ConstructiveReals.RationalTail.finSum_mul_const
#print axioms ConstructiveReals.RationalTail.const_mul_finSum
#print axioms ConstructiveReals.RationalTail.finSum_add
#print axioms ConstructiveReals.RationalTail.finSum_swap
