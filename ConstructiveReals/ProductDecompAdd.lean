/-
Addition-law product decomposition — the rectangle/corner split of
`P⁻ₙ(a)·P⁻ₙ(b)` for the exponential addition law `e^{-a}·e^{-b} = e^{-(a+b)}`.

`P⁻ₙ(a) = partialSum a n = Σ_{i<n} tᵢ(a)`, `P⁻ₙ(b) = partialSum b n = Σ_{j<n} tⱼ(b)`.
Row-splitting the product at the diagonal:

    P⁻ₙ(a)·P⁻ₙ(b)  =  triₙ + cornerₙ ,
    triₙ    := Σ_{i<n} tᵢ(a)·P⁻_{n−i}(b) ,
    cornerₙ := Σ_{i<n} tᵢ(a)·(P⁻ₙ(b) − P⁻_{n−i}(b)).

The triangle satisfies the recurrence `tri_{n+1} = triₙ + cₙ` (peel the last
row, split `P⁻_{(n+1)−i}(b) = P⁻_{n−i}(b) + t_{n−i}(b)`), hence
`triₙ = Σ_{m<n} cₘ`.  Unlike the product-law `e^{-x}·e^{x} = 1`, this triangle
does NOT collapse to a constant: with the addition law (`cₘ = t_m(a+b)`) the
sum is exactly `P⁻ₙ(a+b)`, for ALL `n`.  So

    P⁻ₙ(a)·P⁻ₙ(b)  ≃  P⁻ₙ(a+b) + cornerₙ .

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ExpAddConv
import ConstructiveReals.ProductDecomp

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail
open ConstructiveReals.ExpNeg

/-! ## Triangle, corner -/

/-- `triTermAdd a b n i = tᵢ(a)·P⁻_{n−i}(b)`. -/
def triTermAdd (a b : Q') (n : Nat) : Nat → Q' :=
  fun i => ExpNeg.term a i * ExpNeg.partialSum b (n - i)

/-- `triₙ = Σ_{i<n} tᵢ(a)·P⁻_{n−i}(b)`. -/
def triAdd (a b : Q') (n : Nat) : Q' := finSum (triTermAdd a b n) n

/-- `cornerTermAdd a b n i = tᵢ(a)·(P⁻ₙ(b) − P⁻_{n−i}(b))`. -/
def cornerTermAdd (a b : Q') (n : Nat) : Nat → Q' :=
  fun i => ExpNeg.term a i * (ExpNeg.partialSum b n + -(ExpNeg.partialSum b (n - i)))

/-- `cornerₙ = Σ_{i<n} tᵢ(a)·(P⁻ₙ(b) − P⁻_{n−i}(b))`. -/
def cornerAdd (a b : Q') (n : Nat) : Q' := finSum (cornerTermAdd a b n) n

/-! ## The triangle recurrence `tri_{n+1} ≃ triₙ + cₙ` -/

theorem triAdd_succ (a b : Q') (n : Nat) :
    (triAdd a b (n + 1)).eqv (triAdd a b n + convAdd a b n) := by
  show (finSum (triTermAdd a b (n + 1)) n + triTermAdd a b (n + 1) n).eqv
      (triAdd a b n + convAdd a b n)
  have hlast : (triTermAdd a b (n + 1) n).eqv (ExpNeg.term a n) := by
    show (ExpNeg.term a n * ExpNeg.partialSum b ((n + 1) - n)).eqv (ExpNeg.term a n)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (ExpNeg.term a n * ((0 : Q') + ExpNeg.term b 0)).eqv (ExpNeg.term a n)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term a n) ((0 : Q') + ExpNeg.term b 0) 1 ?_)
      (Q'.mul_one_eqv _)
    show ((0 : Q') + ExpNeg.term b 0).eqv 1
    exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (ExpNeg.term b 0)))
      (Q'.eqv_of_eq (ExpNeg.term_zero b))
  have hrow : ∀ i, i < n →
      (triTermAdd a b (n + 1) i).eqv (triTermAdd a b n i + convAddTerm a b n i) := by
    intro i hi
    have hile : i ≤ n := Nat.le_of_lt hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (ExpNeg.term a i * ExpNeg.partialSum b ((n + 1) - i)).eqv
        (ExpNeg.term a i * ExpNeg.partialSum b (n - i) + ExpNeg.term a i * ExpNeg.term b (n - i))
    rw [hsub]
    show (ExpNeg.term a i * (ExpNeg.partialSum b (n - i) + ExpNeg.term b (n - i))).eqv
        (ExpNeg.term a i * ExpNeg.partialSum b (n - i) + ExpNeg.term a i * ExpNeg.term b (n - i))
    exact Q'.mul_add_eqv (ExpNeg.term a i) (ExpNeg.partialSum b (n - i)) (ExpNeg.term b (n - i))
  have hinner : (finSum (triTermAdd a b (n + 1)) n).eqv
      (triAdd a b n + finSum (convAddTerm a b n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (triTermAdd a b (n + 1))
        (fun i => triTermAdd a b n i + convAddTerm a b n i) n hrow)
      (RationalTail.finSum_add (triTermAdd a b n) (convAddTerm a b n) n)
  have hconv : (convAdd a b n).eqv (finSum (convAddTerm a b n) n + ExpNeg.term a n) := by
    show (finSum (convAddTerm a b n) n + convAddTerm a b n n).eqv
        (finSum (convAddTerm a b n) n + ExpNeg.term a n)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (ExpNeg.term a n * ExpNeg.term b (n - n)).eqv (ExpNeg.term a n)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term a n) (ExpNeg.term b 0) 1
        (Q'.eqv_of_eq (ExpNeg.term_zero b))) ?_
    exact Q'.mul_one_eqv (ExpNeg.term a n)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (triAdd a b n) (finSum (convAddTerm a b n) n) (ExpNeg.term a n)) ?_
  exact Q'.add_eqv_congr_left (triAdd a b n) _ _ (Q'.eqv_symm hconv)

/-! ## `triₙ ≃ Σ_{m<n} cₘ`, and `≃ P⁻ₙ(a+b)` -/

theorem triAdd_eqv_convAddSum (a b : Q') :
    ∀ n, (triAdd a b n).eqv (finSum (convAdd a b) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (triAdd a b (n + 1)).eqv (finSum (convAdd a b) n + convAdd a b n)
      refine Q'.eqv_trans _ _ _ (triAdd_succ a b n) ?_
      exact Q'.add_eqv_congr_right (triAdd a b n) (finSum (convAdd a b) n) (convAdd a b n)
        (triAdd_eqv_convAddSum a b n)

/-- `Σ_{m<n} cₘ ≃ P⁻ₙ(a+b)` (holds for ALL `n`). -/
theorem convAddSum_eqv_partialSum (a b : Q') :
    ∀ n, (finSum (convAdd a b) n).eqv (ExpNeg.partialSum (a + b) n) := by
  intro n
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (convAdd a b) (ExpNeg.term (a + b))
      (fun m => convAdd_eqv_term a b m) n) ?_
  exact Q'.eqv_of_eq (partialSum_eq_finSum (a + b) n).symm

theorem triAdd_eqv_partialSum (a b : Q') (n : Nat) :
    (triAdd a b n).eqv (ExpNeg.partialSum (a + b) n) :=
  Q'.eqv_trans _ _ _ (triAdd_eqv_convAddSum a b n) (convAddSum_eqv_partialSum a b n)

/-! ## The decomposition `P⁻ₙ(a)·P⁻ₙ(b) ≃ triₙ + cornerₙ` -/

theorem prodAdd_eqv_tri_add_corner (a b : Q') (n : Nat) :
    (ExpNeg.partialSum a n * ExpNeg.partialSum b n).eqv (triAdd a b n + cornerAdd a b n) := by
  rw [partialSum_eq_finSum a]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (ExpNeg.term a) (ExpNeg.partialSum b n) n) ?_
  have hterm : ∀ i, (ExpNeg.term a i * ExpNeg.partialSum b n).eqv
      (triTermAdd a b n i + cornerTermAdd a b n i) := by
    intro i
    show (ExpNeg.term a i * ExpNeg.partialSum b n).eqv
        (ExpNeg.term a i * ExpNeg.partialSum b (n - i)
          + ExpNeg.term a i * (ExpNeg.partialSum b n + -(ExpNeg.partialSum b (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term a i) (ExpNeg.partialSum b n)
        (ExpNeg.partialSum b (n - i)
          + (ExpNeg.partialSum b n + -(ExpNeg.partialSum b (n - i))))
        (Q'.add_sub_cancel_eqv (ExpNeg.partialSum b n) (ExpNeg.partialSum b (n - i)))) ?_
    exact Q'.mul_add_eqv (ExpNeg.term a i) (ExpNeg.partialSum b (n - i))
      (ExpNeg.partialSum b n + -(ExpNeg.partialSum b (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => ExpNeg.term a i * ExpNeg.partialSum b n)
      (fun i => triTermAdd a b n i + cornerTermAdd a b n i) hterm n) ?_
  exact RationalTail.finSum_add (triTermAdd a b n) (cornerTermAdd a b n) n

/-- **`P⁻ₙ(a)·P⁻ₙ(b) ≃ P⁻ₙ(a+b) + cornerₙ`.** -/
theorem prodAdd_eqv_partialSum_add_corner (a b : Q') (n : Nat) :
    (ExpNeg.partialSum a n * ExpNeg.partialSum b n).eqv
      (ExpNeg.partialSum (a + b) n + cornerAdd a b n) := by
  refine Q'.eqv_trans _ _ _ (prodAdd_eqv_tri_add_corner a b n) ?_
  exact Q'.add_eqv_congr_right (triAdd a b n) (ExpNeg.partialSum (a + b) n) (cornerAdd a b n)
    (triAdd_eqv_partialSum a b n)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.convAddSum_eqv_partialSum
#print axioms ConstructiveReals.triAdd_eqv_partialSum
#print axioms ConstructiveReals.prodAdd_eqv_partialSum_add_corner
