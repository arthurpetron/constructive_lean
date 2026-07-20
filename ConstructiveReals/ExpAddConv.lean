/-
Exponential addition law — the convolution identity behind
`e^{-a}·e^{-b} = e^{-(a+b)}`.

For the `e^{-x}` series `tₖ(x) = (−x)ᵏ/k!` (`ExpNeg.term`), the `m`-th Cauchy
coefficient of the product `e^{-a}·e^{-b}` is

    convAdd a b m = Σ_{i=0}^{m} tᵢ(a)·t_{m−i}(b),

and the addition law is the binomial collapse

    convAdd a b m ≃ t_m(a+b).

The proof mirrors the product-law L2 (`CauchyConv.lean`, `conv_succ_eqv_zero`):
weight each convolution term by `m = i + (m−i)` and use the weighted
term-recurrences `(k+1)·tₖ₊₁(a) = (−a)·tₖ(a)`, `(k+1)·tₖ₊₁(b) = (−b)·tₖ(b)`.
The two halves collapse (via a 1-D `finSum` reindex) to `(−a)·c_{m−1}` and
`(−b)·c_{m−1}`, whose sum is `(−(a+b))·c_{m−1}`.  Cancelling the positive
factor `ofNat (m+1)` against the weighted recurrence `(m+1)·tₘ₊₁(a+b) =
(−(a+b))·tₘ(a+b)` and inducting on `m` gives the identity — binomial-free,
exactly as L2 avoided `Σ(−1)ʲC(m,j)=0`.

The one new `Q'` primitive is `mul_left_cancel_of_pos` (positive-factor
cancellation for `eqv`, the equality analogue of `mul_eqv_zero_of_pos`).

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat`/`Int` enter.  No
`Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.CauchyConv

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail

/-! ## Q' helper: positive-factor cancellation -/

namespace Q'

/-- `x * y * (z * w) = x * z * (y * w)` — swap the two inner factors. -/
private theorem int_swap_inner (x y z w : Int) :
    (x * y) * (z * w) = (x * z) * (y * w) := by
  rw [Int.mul_assoc x y (z * w), ← Int.mul_assoc y z w, Int.mul_comm y z,
      Int.mul_assoc z y w, ← Int.mul_assoc x z (y * w)]

/-- Cancel a positive factor in an `eqv`: `0 < c` and `c·a ≃ c·b` give `a ≃ b`. -/
theorem mul_left_cancel_of_pos {c a b : Q'} (hc : (0 : Q') < c)
    (h : (c * a).eqv (c * b)) : a.eqv b := by
  have hc' : (0 : Int) * (c.den : Int) < c.num * (((0 : Q').den) : Int) := hc
  have hc_num : (0 : Int) < c.num := by
    have : (0 : Int) * (c.den : Int) < c.num * (1 : Int) := hc'
    rw [Int.zero_mul, Int.mul_one] at this
    exact this
  have hc_num_ne : c.num ≠ 0 := Int.ne_of_gt hc_num
  have hc_den_ne : (c.den : Int) ≠ 0 :=
    Int.ne_of_gt (Int.ofNat_lt.mpr (Q'.den_pos c))
  have hcd_ne : c.num * (c.den : Int) ≠ 0 := Int.mul_ne_zero hc_num_ne hc_den_ne
  have h' : (c * a).num * (((c * b).den) : Int)
      = (c * b).num * (((c * a).den) : Int) := h
  have hna : (c * a).num = c.num * a.num := rfl
  have hnb : (c * b).num = c.num * b.num := rfl
  rw [hna, hnb, Q'.mul_den_cast c b, Q'.mul_den_cast c a] at h'
  rw [Q'.int_swap_inner c.num a.num (c.den : Int) (b.den : Int),
      Q'.int_swap_inner c.num b.num (c.den : Int) (a.den : Int)] at h'
  have hcancel : a.num * (b.den : Int) = b.num * (a.den : Int) :=
    Int.eq_of_mul_eq_mul_left hcd_ne h'
  show a.num * ((b.den) : Int) = b.num * ((a.den) : Int)
  exact hcancel

end Q'

/-! ## The convolution coefficient for the addition law -/

/-- `convAddTerm a b m i = tᵢ(a)·t_{m−i}(b)` (the `i`-th term of the `m`-th
Cauchy coefficient of `e^{-a}·e^{-b}`). -/
def convAddTerm (a b : Q') (m : Nat) : Nat → Q' :=
  fun i => ExpNeg.term a i * ExpNeg.term b (m - i)

/-- `cₘ = Σ_{i=0}^{m} tᵢ(a)·t_{m−i}(b)`. -/
def convAdd (a b : Q') (m : Nat) : Q' := finSum (convAddTerm a b m) (m + 1)

/-! ## Weighted halves -/

/-- The `i`-weighted half: `Σ_i i·convAddTerm a b (m+1) i ≃ (−a)·cₘ`. -/
theorem iWeighted_add (a b : Q') (m : Nat) :
    (finSum (fun i => Q'.ofNat i * convAddTerm a b (m + 1) i) (m + 2)).eqv
      ((-a) * convAdd a b m) := by
  have hpeel := RationalTail.finSum_peel_left
    (fun i => Q'.ofNat i * convAddTerm a b (m + 1) i) (m + 1)
  have hF0 : (Q'.ofNat 0 * convAddTerm a b (m + 1) 0).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (convAddTerm a b (m + 1) 0) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv (convAddTerm a b (m + 1) 0))
  have hFk : ∀ k, (Q'.ofNat (k + 1) * convAddTerm a b (m + 1) (k + 1)).eqv
      ((-a) * convAddTerm a b m k) := by
    intro k
    have hidx : convAddTerm a b (m + 1) (k + 1)
        = ExpNeg.term a (k + 1) * ExpNeg.term b (m - k) := by
      show ExpNeg.term a (k + 1) * ExpNeg.term b ((m + 1) - (k + 1)) = _
      have : (m + 1) - (k + 1) = m - k := by omega
      rw [this]
    rw [hidx]
    show (Q'.ofNat (k + 1) * (ExpNeg.term a (k + 1) * ExpNeg.term b (m - k))).eqv
        ((-a) * convAddTerm a b m k)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k + 1)) (ExpNeg.term a (k + 1))
        (ExpNeg.term b (m - k)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ ((-a) * ExpNeg.term a k) (ExpNeg.term b (m - k))
        (ofNat_succ_mul_term a k)) ?_
    exact Q'.mul_assoc_eqv (-a) (ExpNeg.term a k) (ExpNeg.term b (m - k))
  have hsum : (finSum (fun k => Q'.ofNat (k + 1) * convAddTerm a b (m + 1) (k + 1)) (m + 1)).eqv
      ((-a) * convAdd a b m) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr _ (fun k => (-a) * convAddTerm a b m k) hFk (m + 1))
      (Q'.eqv_symm (RationalTail.const_mul_finSum (convAddTerm a b m) (-a) (m + 1)))
  refine Q'.eqv_trans _ _ _ hpeel ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 _ hF0) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 0 _ _ hsum) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The `(m−i)`-weighted half: `Σ_i (m+1−i)·convAddTerm a b (m+1) i ≃ (−b)·cₘ`. -/
theorem jWeighted_add (a b : Q') (m : Nat) :
    (finSum (fun i => Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) (m + 2)).eqv
      ((-b) * convAdd a b m) := by
  show (finSum (fun i => Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) ((m + 1) + 1)).eqv _
  have hGlast : (Q'.ofNat ((m + 1) - (m + 1)) * convAddTerm a b (m + 1) (m + 1)).eqv 0 := by
    have h0 : (m + 1) - (m + 1) = 0 := by omega
    rw [h0]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (convAddTerm a b (m + 1) (m + 1)) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv (convAddTerm a b (m + 1) (m + 1)))
  have hGi : ∀ i, i < m + 1 →
      (Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i).eqv ((-b) * convAddTerm a b m i) := by
    intro i hi
    have hile : i ≤ m := Nat.lt_succ_iff.mp hi
    have hsub : (m + 1) - i = (m - i) + 1 := by omega
    have hconv : convAddTerm a b (m + 1) i = ExpNeg.term a i * ExpNeg.term b ((m - i) + 1) := by
      show ExpNeg.term a i * ExpNeg.term b ((m + 1) - i) = _
      rw [hsub]
    rw [hsub, hconv]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat ((m - i) + 1))
        (ExpNeg.term a i * ExpNeg.term b ((m - i) + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (ExpNeg.term a i) (ExpNeg.term b ((m - i) + 1))
        (Q'.ofNat ((m - i) + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term a i)
        (ExpNeg.term b ((m - i) + 1) * Q'.ofNat ((m - i) + 1))
        (Q'.ofNat ((m - i) + 1) * ExpNeg.term b ((m - i) + 1))
        (Q'.mul_comm_eqv (ExpNeg.term b ((m - i) + 1)) (Q'.ofNat ((m - i) + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term a i)
        (Q'.ofNat ((m - i) + 1) * ExpNeg.term b ((m - i) + 1))
        ((-b) * ExpNeg.term b (m - i))
        (ofNat_succ_mul_term b (m - i))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (ExpNeg.term a i) (-b) (ExpNeg.term b (m - i)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ ((-b) * ExpNeg.term a i) (ExpNeg.term b (m - i))
        (Q'.mul_comm_eqv (ExpNeg.term a i) (-b))) ?_
    exact Q'.mul_assoc_eqv (-b) (ExpNeg.term a i) (ExpNeg.term b (m - i))
  show (finSum (fun i => Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) (m + 1)
        + Q'.ofNat ((m + 1) - (m + 1)) * convAddTerm a b (m + 1) (m + 1)).eqv
        ((-b) * convAdd a b m)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 hGlast) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt _ (fun i => (-b) * convAddTerm a b m i) (m + 1) hGi) ?_
  exact Q'.eqv_symm (RationalTail.const_mul_finSum (convAddTerm a b m) (-b) (m + 1))

/-- `(m+1)·c_{m+1} ≃ (−(a+b))·cₘ`. -/
theorem ofNat_succ_mul_convAdd (a b : Q') (m : Nat) :
    ((Q'.ofNat (m + 1)) * convAdd a b (m + 1)).eqv ((-(a + b)) * convAdd a b m) := by
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum (convAddTerm a b (m + 1)) (Q'.ofNat (m + 1)) (m + 2)) ?_
  have hsplit : ∀ i, i < m + 2 →
      (Q'.ofNat (m + 1) * convAddTerm a b (m + 1) i).eqv
        (Q'.ofNat i * convAddTerm a b (m + 1) i
          + Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) := by
    intro i hi
    have hile : i ≤ m + 1 := Nat.lt_succ_iff.mp hi
    have hnat : i + ((m + 1) - i) = m + 1 := by omega
    have hofnat : (Q'.ofNat (m + 1)).eqv (Q'.ofNat i + Q'.ofNat ((m + 1) - i)) := by
      have hh := Q'.ofNat_add_eqv i ((m + 1) - i)
      rw [hnat] at hh
      exact hh
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat (m + 1)) (Q'.ofNat i + Q'.ofNat ((m + 1) - i))
        (convAddTerm a b (m + 1) i) hofnat) ?_
    exact Q'.add_mul_eqv (Q'.ofNat i) (Q'.ofNat ((m + 1) - i)) (convAddTerm a b (m + 1) i)
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt _
      (fun i => Q'.ofNat i * convAddTerm a b (m + 1) i
              + Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) (m + 2) hsplit) ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add (fun i => Q'.ofNat i * convAddTerm a b (m + 1) i)
      (fun i => Q'.ofNat ((m + 1) - i) * convAddTerm a b (m + 1) i) (m + 2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ ((-a) * convAdd a b m) _ (iWeighted_add a b m)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((-a) * convAdd a b m) _ ((-b) * convAdd a b m)
      (jWeighted_add a b m)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv (-a) (-b) (convAdd a b m))) ?_
  refine Q'.mul_eqv_congr_right ((-a) + (-b)) (-(a + b)) (convAdd a b m) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a b)

/-! ## The addition law -/

/-- **Exponential addition law (convolution form).**
`Σ_{i=0}^{m} tᵢ(a)·t_{m−i}(b) ≃ t_m(a+b)`. -/
theorem convAdd_eqv_term (a b : Q') (m : Nat) :
    (convAdd a b m).eqv (ExpNeg.term (a + b) m) := by
  induction m with
  | zero =>
      show ((0 : Q') + ExpNeg.term a 0 * ExpNeg.term b 0).eqv (ExpNeg.term (a + b) 0)
      rw [ExpNeg.term_zero, ExpNeg.term_zero, ExpNeg.term_zero, Q'.zero_add']
      exact Q'.mul_one_eqv 1
  | succ m ih =>
      have step :
          ((Q'.ofNat (m + 1)) * convAdd a b (m + 1)).eqv
            ((Q'.ofNat (m + 1)) * ExpNeg.term (a + b) (m + 1)) := by
        refine Q'.eqv_trans _ _ _ (ofNat_succ_mul_convAdd a b m) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (-(a + b)) (convAdd a b m) (ExpNeg.term (a + b) m) ih) ?_
        exact Q'.eqv_symm (ofNat_succ_mul_term (a + b) m)
      exact Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos m) step

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.mul_left_cancel_of_pos
#print axioms ConstructiveReals.convAdd_eqv_term
