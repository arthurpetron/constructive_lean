/-
Product law L3a — the rectangle/corner decomposition of `P⁺ₙ·P⁻ₙ`.

`P⁺ₙ = partialSumAbs x n = Σ_{i<n} aᵢ`, `P⁻ₙ = partialSum x n = Σ_{j<n} bⱼ`.
Row-splitting the product at the diagonal:

    P⁺ₙ·P⁻ₙ  =  triₙ + cornerₙ ,
    triₙ    := Σ_{i<n} aᵢ·P⁻_{n−i} ,   cornerₙ := Σ_{i<n} aᵢ·(P⁻ₙ − P⁻_{n−i}).

The triangle satisfies the recurrence `tri_{n+1} = triₙ + cₙ` (peel the last
row, split `P⁻_{(n+1)−i} = P⁻_{n−i} + b_{n−i}`), hence `triₙ = Σ_{m<n} cₘ`.
With L2 (`cₘ = [m=0]`) that sum is `1` for `n ≥ 1`.  So

    P⁺_{n+1}·P⁻_{n+1}  ≃  1 + corner_{n+1}.

L3b bounds `corner_{n+1} → 0`, giving the product law `eˣ·e⁻ˣ = 1`.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ExpNeg
import ConstructiveReals.FinSumAlg
import ConstructiveReals.CauchyConv

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail
open ConstructiveReals.ExpNeg

/-! ## `partialSum*` as `finSum` -/

theorem partialSumAbs_eq_finSum (x : Q') :
    ∀ n, partialSumAbs x n = finSum (termAbs x) n
  | 0 => rfl
  | n + 1 => by rw [partialSumAbs_succ, finSum_succ, partialSumAbs_eq_finSum x n]

theorem partialSum_eq_finSum (x : Q') :
    ∀ n, partialSum x n = finSum (term x) n
  | 0 => rfl
  | n + 1 => by rw [partialSum_succ, finSum_succ, partialSum_eq_finSum x n]

/-! ## Triangle, corner -/

/-- `triTerm x n i = aᵢ·P⁻_{n−i}`. -/
def triTerm (x : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs x i * partialSum x (n - i)

/-- `triₙ = Σ_{i<n} aᵢ·P⁻_{n−i}`. -/
def tri (x : Q') (n : Nat) : Q' := finSum (triTerm x n) n

/-- `cornerTerm x n i = aᵢ·(P⁻ₙ − P⁻_{n−i})`. -/
def cornerTerm (x : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs x i * (partialSum x n + -(partialSum x (n - i)))

/-- `cornerₙ = Σ_{i<n} aᵢ·(P⁻ₙ − P⁻_{n−i})`. -/
def corner (x : Q') (n : Nat) : Q' := finSum (cornerTerm x n) n

/-! ## The triangle recurrence `tri_{n+1} ≃ triₙ + cₙ` -/

theorem tri_succ (x : Q') (n : Nat) :
    (tri x (n + 1)).eqv (tri x n + conv x n) := by
  -- peel the last row (i = n)
  show (finSum (triTerm x (n + 1)) n + triTerm x (n + 1) n).eqv (tri x n + conv x n)
  -- last term: aₙ·P⁻₁ ≃ aₙ ; conv x n = finSum (convTerm x n) n + aₙ·b₀
  have hlast : (triTerm x (n + 1) n).eqv (termAbs x n) := by
    show (termAbs x n * partialSum x ((n + 1) - n)).eqv (termAbs x n)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    -- partialSum x 1 = 0 + term x 0, term x 0 = 1
    show (termAbs x n * ((0 : Q') + term x 0)).eqv (termAbs x n)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (termAbs x n) ((0 : Q') + term x 0) 1 ?_) (Q'.mul_one_eqv _)
    show ((0 : Q') + term x 0).eqv 1
    exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (term x 0)))
      (Q'.eqv_of_eq (ExpNeg.term_zero x))
  -- inner sum over i < n : triTerm x (n+1) i ≃ triTerm x n i + convTerm x n i
  have hrow : ∀ i, i < n →
      (triTerm x (n + 1) i).eqv (triTerm x n i + convTerm x n i) := by
    intro i hi
    have hile : i ≤ n := Nat.le_of_lt hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (termAbs x i * partialSum x ((n + 1) - i)).eqv
        (termAbs x i * partialSum x (n - i) + termAbs x i * term x (n - i))
    rw [hsub]
    -- partialSum x ((n-i)+1) = partialSum x (n-i) + term x (n-i)
    show (termAbs x i * (partialSum x (n - i) + term x (n - i))).eqv
        (termAbs x i * partialSum x (n - i) + termAbs x i * term x (n - i))
    exact Q'.mul_add_eqv (termAbs x i) (partialSum x (n - i)) (term x (n - i))
  have hinner : (finSum (triTerm x (n + 1)) n).eqv
      (tri x n + finSum (convTerm x n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (triTerm x (n + 1))
        (fun i => triTerm x n i + convTerm x n i) n hrow)
      (RationalTail.finSum_add (triTerm x n) (convTerm x n) n)
  -- conv x n = finSum (convTerm x n) n + convTerm x n n, with convTerm x n n ≃ aₙ
  have hconv : (conv x n).eqv (finSum (convTerm x n) n + termAbs x n) := by
    show (finSum (convTerm x n) n + convTerm x n n).eqv (finSum (convTerm x n) n + termAbs x n)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (termAbs x n * term x (n - n)).eqv (termAbs x n)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.mul_one_eqv (termAbs x n)
  -- assemble: (Σ_{i<n} triTerm(n+1)) + last ≃ (tri n + Σ convTerm) + aₙ ≃ tri n + (Σ convTerm + aₙ) ≃ tri n + conv n
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (tri x n) (finSum (convTerm x n) n) (termAbs x n)) ?_
  exact Q'.add_eqv_congr_left (tri x n) _ _ (Q'.eqv_symm hconv)

/-! ## `triₙ ≃ Σ_{m<n} cₘ`, and `= 1` for `n ≥ 1` -/

theorem tri_eqv_convSum (x : Q') :
    ∀ n, (tri x n).eqv (finSum (conv x) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      show (tri x (n + 1)).eqv (finSum (conv x) n + conv x n)
      refine Q'.eqv_trans _ _ _ (tri_succ x n) ?_
      exact Q'.add_eqv_congr_right (tri x n) (finSum (conv x) n) (conv x n)
        (tri_eqv_convSum x n)

/-- `Σ_{m<n+1} cₘ ≃ 1`. -/
theorem convSum_succ_eqv_one (x : Q') (n : Nat) :
    (finSum (conv x) (n + 1)).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (RationalTail.finSum_peel_left (conv x) n) ?_
  -- conv x 0 + Σ_{k<n} conv x (k+1) ≃ 1 + 0 ≃ 1
  have htail : (finSum (fun k => conv x (k + 1)) n).eqv 0 :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr (fun k => conv x (k + 1)) (fun _ => (0 : Q'))
        (fun k => conv_succ_eqv_zero x k) n)
      (Q'.eqv_of_eq (finSum_zero_seq n))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 1 _ (conv_zero x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ 0 htail) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

theorem tri_succ_eqv_one (x : Q') (n : Nat) : (tri x (n + 1)).eqv 1 :=
  Q'.eqv_trans _ _ _ (tri_eqv_convSum x (n + 1)) (convSum_succ_eqv_one x n)

/-! ## The decomposition `P⁺ₙ·P⁻ₙ ≃ triₙ + cornerₙ` -/

theorem prod_eqv_tri_add_corner (x : Q') (n : Nat) :
    (partialSumAbs x n * partialSum x n).eqv (tri x n + corner x n) := by
  rw [partialSumAbs_eq_finSum]
  -- (Σ aᵢ)·P⁻ₙ ≃ Σ (aᵢ·P⁻ₙ)
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (termAbs x) (partialSum x n) n) ?_
  -- termwise: aᵢ·P⁻ₙ ≃ triTerm x n i + cornerTerm x n i
  have hterm : ∀ i, (termAbs x i * partialSum x n).eqv
      (triTerm x n i + cornerTerm x n i) := by
    intro i
    show (termAbs x i * partialSum x n).eqv
        (termAbs x i * partialSum x (n - i)
          + termAbs x i * (partialSum x n + -(partialSum x (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (termAbs x i) (partialSum x n)
        (partialSum x (n - i) + (partialSum x n + -(partialSum x (n - i))))
        (Q'.add_sub_cancel_eqv (partialSum x n) (partialSum x (n - i)))) ?_
    exact Q'.mul_add_eqv (termAbs x i) (partialSum x (n - i))
      (partialSum x n + -(partialSum x (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => termAbs x i * partialSum x n)
      (fun i => triTerm x n i + cornerTerm x n i) hterm n) ?_
  exact RationalTail.finSum_add (triTerm x n) (cornerTerm x n) n

/-- **`P⁺_{n+1}·P⁻_{n+1} ≃ 1 + corner_{n+1}`.** -/
theorem prod_eqv_one_add_corner (x : Q') (n : Nat) :
    (partialSumAbs x (n + 1) * partialSum x (n + 1)).eqv (1 + corner x (n + 1)) := by
  refine Q'.eqv_trans _ _ _ (prod_eqv_tri_add_corner x (n + 1)) ?_
  exact Q'.add_eqv_congr_right (tri x (n + 1)) 1 (corner x (n + 1)) (tri_succ_eqv_one x n)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.tri_succ
#print axioms ConstructiveReals.tri_eqv_convSum
#print axioms ConstructiveReals.convSum_succ_eqv_one
#print axioms ConstructiveReals.prod_eqv_tri_add_corner
#print axioms ConstructiveReals.prod_eqv_one_add_corner
