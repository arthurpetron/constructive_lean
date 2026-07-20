/-
Product law L2 — the convolution coefficient `cₘ = Σ_{i+j=m} aᵢ·bⱼ` vanishes
for `m ≥ 1` (with `aᵢ = termAbs x i = xⁱ/i!`, `bⱼ = term x j = (−x)ʲ/j!`).

The proof is the binomial-free recurrence `m·cₘ = x·c_{m−1} − x·c_{m−1} = 0`:
weighting each convolution term by `m = i + (m−i)` and using the weighted
term-recurrences `(k+1)·a_{k+1} = x·aₖ`, `(k+1)·b_{k+1} = −x·bₖ` collapses the
two halves (via a 1-D `finSum` reindex) to `±x·c_{m−1}`.  Cancelling the
positive factor `ofNat m` gives `cₘ ≃ 0`.

`cₘ = 0` (m ≥ 1) and `c₀ = 1` make the Cauchy partial sum `Σ_{m<n} cₘ = 1`,
the anchor of the rectangle/corner decomposition (L3) of `P⁺ₙ·P⁻ₙ`.

The self-contained Q'/finSum helpers below (`ofNat_succ_mul_*`,
`mul_eqv_zero_of_pos`, `finSum_peel_left`, `ofNat_add_eqv`) were developed and
verified independently.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ExpNeg
import ConstructiveReals.FinSumAlg

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail

/-! ## Q' helpers -/

namespace Q'

/-- `(k+1) · (1/(k+1)) ≃ 1`. -/
theorem ofNat_succ_mul_invSucc (k : Nat) :
    ((Q'.ofNat (k + 1)) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)).eqv (1 : Q') := by
  show ((Q'.ofNat (k + 1)) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)).num
        * ((1 : Q').den : Int)
      = (1 : Q').num
        * (((Q'.ofNat (k + 1)) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)).den : Int)
  rw [Q'.mul_den_cast]
  show ((Q'.ofNat (k + 1)).num * (Q'.mkPos 1 (k + 1) (Nat.succ_pos _)).num)
        * ((1 : Q').den : Int)
      = (1 : Q').num
        * (((Q'.ofNat (k + 1)).den : Int)
            * ((Q'.mkPos 1 (k + 1) (Nat.succ_pos _)).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show ((Int.ofNat (k + 1)) * (1 : Int)) * (1 : Int)
      = (1 : Int) * ((1 : Int) * ((k + 1 : Nat) : Int))
  rw [Int.mul_one, Int.mul_one, Int.one_mul, Int.one_mul]
  rfl

/-- Cancel a positive factor: `0 < a` and `a·b ≃ 0` give `b ≃ 0`. -/
theorem mul_eqv_zero_of_pos {a b : Q'} (ha : (0 : Q') < a)
    (h : (a * b).eqv (0 : Q')) : b.eqv (0 : Q') := by
  have ha' : (0 : Int) * (a.den : Int) < a.num * (((0 : Q').den) : Int) := ha
  have ha_num : (0 : Int) < a.num := by
    have : (0 : Int) * (a.den : Int) < a.num * (1 : Int) := ha'
    rw [Int.zero_mul, Int.mul_one] at this
    exact this
  have ha_ne : a.num ≠ 0 := Int.ne_of_gt ha_num
  have h' : (a * b).num * (((0 : Q').den) : Int)
      = ((0 : Q').num) * (((a * b).den) : Int) := h
  have hab_num_eq : (a * b).num = 0 := by
    have : (a * b).num * (1 : Int) = (0 : Int) * (((a * b).den) : Int) := h'
    rw [Int.mul_one, Int.zero_mul] at this
    exact this
  have hprod : a.num * b.num = 0 := hab_num_eq
  have hb_num : b.num = 0 := by
    rcases Int.mul_eq_zero.mp hprod with ha0 | hb0
    · exact absurd ha0 ha_ne
    · exact hb0
  show b.num * (((0 : Q').den) : Int) = ((0 : Q').num) * ((b.den) : Int)
  show b.num * (1 : Int) = (0 : Int) * ((b.den) : Int)
  rw [Int.mul_one, Int.zero_mul, hb_num]

/-- `ofNat (i+j) ≃ ofNat i + ofNat j`. -/
theorem ofNat_add_eqv (i j : Nat) :
    (Q'.ofNat (i + j)).eqv (Q'.ofNat i + Q'.ofNat j) := by
  show (Q'.ofNat (i + j)).num * ((Q'.ofNat i + Q'.ofNat j).den : Int)
     = (Q'.ofNat i + Q'.ofNat j).num * ((Q'.ofNat (i + j)).den : Int)
  have hd : ((Q'.ofNat i + Q'.ofNat j).den : Int) = (1 : Int) := by
    show (((1 * 1 - 1) + 1 : Nat) : Int) = (1 : Int)
    decide
  rw [hd]
  show ((↑(i + j) : Int)) * (1 : Int)
     = (((↑i : Int)) * (1 : Int) + ((↑j : Int)) * (1 : Int)) * (1 : Int)
  push_cast
  omega

/-- `0 < ofNat (m+1)`. -/
theorem ofNat_succ_pos (m : Nat) : (0 : Q') < Q'.ofNat (m + 1) := by
  apply CReal.pos_of_num_pos
  show (0 : Int) < Int.ofNat (m + 1)
  exact Int.ofNat_lt.mpr (Nat.succ_pos m)

/-- `ofNat 0 ≃ 0`. -/
theorem ofNat_zero_eqv : (Q'.ofNat 0).eqv (0 : Q') := by decide

/-- An `Eq` lifts to `eqv`. -/
theorem eqv_of_eq {a b : Q'} (h : a = b) : a.eqv b := by subst h; exact Q'.eqv_refl a

end Q'

/-! ## Weighted term recurrences -/

/-- `(k+1)·termAbs_{k+1} ≃ x·termAbs_k`. -/
theorem ofNat_succ_mul_termAbs (x : Q') (k : Nat) :
    ((Q'.ofNat (k + 1)) * ExpNeg.termAbs x (k + 1)).eqv (x * ExpNeg.termAbs x k) := by
  rw [ExpNeg.termAbs_succ]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k+1)) (ExpNeg.termAbs x k)
      (x * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (ExpNeg.termAbs x k * Q'.ofNat (k+1))
      (x * Q'.mkPos 1 (k+1) (Nat.succ_pos _))
      (Q'.mul_comm_eqv (Q'.ofNat (k+1)) (ExpNeg.termAbs x k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (ExpNeg.termAbs x k) (Q'.ofNat (k+1))
      (x * Q'.mkPos 1 (k+1) (Nat.succ_pos _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ExpNeg.termAbs x k)
      (Q'.ofNat (k+1) * (x * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))
      (x * (Q'.ofNat (k+1) * Q'.mkPos 1 (k+1) (Nat.succ_pos _))) ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k+1)) x
        (Q'.mkPos 1 (k+1) (Nat.succ_pos _)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ (x * Q'.ofNat (k+1))
        (Q'.mkPos 1 (k+1) (Nat.succ_pos _))
        (Q'.mul_comm_eqv (Q'.ofNat (k+1)) x)) ?_
    exact Q'.mul_assoc_eqv x (Q'.ofNat (k+1)) (Q'.mkPos 1 (k+1) (Nat.succ_pos _))
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.termAbs x k)
        (x * (Q'.ofNat (k+1) * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))
        (x * 1)
        (Q'.mul_eqv_congr_left x _ 1 (Q'.ofNat_succ_mul_invSucc k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.termAbs x k) (x * 1) x (Q'.mul_one_eqv x)) ?_
    exact Q'.mul_comm_eqv (ExpNeg.termAbs x k) x

/-- `(k+1)·term_{k+1} ≃ (−x)·term_k`. -/
theorem ofNat_succ_mul_term (x : Q') (k : Nat) :
    ((Q'.ofNat (k + 1)) * ExpNeg.term x (k + 1)).eqv ((-x) * ExpNeg.term x k) := by
  rw [ExpNeg.term_succ]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k+1)) (ExpNeg.term x k)
      ((-x) * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (ExpNeg.term x k * Q'.ofNat (k+1))
      ((-x) * Q'.mkPos 1 (k+1) (Nat.succ_pos _))
      (Q'.mul_comm_eqv (Q'.ofNat (k+1)) (ExpNeg.term x k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (ExpNeg.term x k) (Q'.ofNat (k+1))
      ((-x) * Q'.mkPos 1 (k+1) (Nat.succ_pos _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ExpNeg.term x k)
      (Q'.ofNat (k+1) * ((-x) * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))
      ((-x) * (Q'.ofNat (k+1) * Q'.mkPos 1 (k+1) (Nat.succ_pos _))) ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k+1)) (-x)
        (Q'.mkPos 1 (k+1) (Nat.succ_pos _)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ ((-x) * Q'.ofNat (k+1))
        (Q'.mkPos 1 (k+1) (Nat.succ_pos _))
        (Q'.mul_comm_eqv (Q'.ofNat (k+1)) (-x))) ?_
    exact Q'.mul_assoc_eqv (-x) (Q'.ofNat (k+1)) (Q'.mkPos 1 (k+1) (Nat.succ_pos _))
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term x k)
        ((-x) * (Q'.ofNat (k+1) * Q'.mkPos 1 (k+1) (Nat.succ_pos _)))
        ((-x) * 1)
        (Q'.mul_eqv_congr_left (-x) _ 1 (Q'.ofNat_succ_mul_invSucc k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.term x k) ((-x) * 1) (-x) (Q'.mul_one_eqv (-x))) ?_
    exact Q'.mul_comm_eqv (ExpNeg.term x k) (-x)

/-! ## finSum reindex helpers -/

namespace RationalTail

/-- Peel the first term: `Σ_{i<n+1} g i ≃ g 0 + Σ_{i<n} g (i+1)`. -/
theorem finSum_peel_left (g : QSeq) :
    ∀ n, (finSum g (n + 1)).eqv (g 0 + finSum (fun i => g (i + 1)) n)
  | 0 => by
      show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.eqv_refl (g 0)
  | n + 1 => by
      have ih : (finSum g (n + 1)).eqv (g 0 + finSum (fun i => g (i + 1)) n) :=
        finSum_peel_left g n
      have h1 : (finSum g (n + 1) + g (n + 1)).eqv
          ((g 0 + finSum (fun i => g (i + 1)) n) + g (n + 1)) :=
        Q'.add_eqv_congr_right _ _ (g (n + 1)) ih
      have h2 : ((g 0 + finSum (fun i => g (i + 1)) n) + g (n + 1)).eqv
          (g 0 + (finSum (fun i => g (i + 1)) n + g (n + 1))) :=
        Q'.add_assoc_eqv (g 0) (finSum (fun i => g (i + 1)) n) (g (n + 1))
      exact Q'.eqv_trans _ _ _ h1 h2

/-- Range-restricted termwise congruence: agreement on `i < n` suffices. -/
theorem finSum_eqv_congr_lt (f g : QSeq) :
    ∀ n, (∀ i, i < n → (f i).eqv (g i)) → (finSum f n).eqv (finSum g n)
  | 0, _ => Q'.eqv_refl 0
  | n + 1, h =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (finSum f n) (finSum g n) (f n)
          (finSum_eqv_congr_lt f g n (fun i hi => h i (Nat.lt_succ_of_lt hi))))
        (Q'.add_eqv_congr_left (finSum g n) (f n) (g n) (h n (Nat.lt_succ_self n)))

end RationalTail

/-! ## The convolution coefficient -/

/-- `convTerm x m i = aᵢ·b_{m−i}` (the `i`-th term of the `m`-th Cauchy
coefficient), `aᵢ = termAbs x i`, `bⱼ = term x j`. -/
def convTerm (x : Q') (m : Nat) : Nat → Q' :=
  fun i => ExpNeg.termAbs x i * ExpNeg.term x (m - i)

/-- `cₘ = Σ_{i=0}^{m} aᵢ·b_{m−i}`. -/
def conv (x : Q') (m : Nat) : Q' := finSum (convTerm x m) (m + 1)

/-- `c₀ = 1`. -/
theorem conv_zero (x : Q') : (conv x 0).eqv 1 := by
  show ((0 : Q') + (1 : Q') * (1 : Q')).eqv 1
  rw [Q'.zero_add']
  exact Q'.mul_one_eqv 1

/-- The `i`-weighted half: `Σ_i i·convTerm x (m+1) i ≃ x·cₘ`. -/
theorem iWeighted (x : Q') (m : Nat) :
    (finSum (fun i => Q'.ofNat i * convTerm x (m + 1) i) (m + 2)).eqv (x * conv x m) := by
  have hpeel := RationalTail.finSum_peel_left
    (fun i => Q'.ofNat i * convTerm x (m + 1) i) (m + 1)
  have hF0 : (Q'.ofNat 0 * convTerm x (m + 1) 0).eqv 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (convTerm x (m + 1) 0) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv (convTerm x (m + 1) 0))
  have hFk : ∀ k, (Q'.ofNat (k + 1) * convTerm x (m + 1) (k + 1)).eqv (x * convTerm x m k) := by
    intro k
    have hidx : convTerm x (m + 1) (k + 1)
        = ExpNeg.termAbs x (k + 1) * ExpNeg.term x (m - k) := by
      show ExpNeg.termAbs x (k + 1) * ExpNeg.term x ((m + 1) - (k + 1)) = _
      have : (m + 1) - (k + 1) = m - k := by omega
      rw [this]
    rw [hidx]
    show (Q'.ofNat (k + 1) * (ExpNeg.termAbs x (k + 1) * ExpNeg.term x (m - k))).eqv
        (x * convTerm x m k)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k + 1)) (ExpNeg.termAbs x (k + 1))
        (ExpNeg.term x (m - k)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ (x * ExpNeg.termAbs x k) (ExpNeg.term x (m - k))
        (ofNat_succ_mul_termAbs x k)) ?_
    exact Q'.mul_assoc_eqv x (ExpNeg.termAbs x k) (ExpNeg.term x (m - k))
  have hsum : (finSum (fun k => Q'.ofNat (k + 1) * convTerm x (m + 1) (k + 1)) (m + 1)).eqv
      (x * conv x m) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr _ (fun k => x * convTerm x m k) hFk (m + 1))
      (Q'.eqv_symm (RationalTail.const_mul_finSum (convTerm x m) x (m + 1)))
  refine Q'.eqv_trans _ _ _ hpeel ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 _ hF0) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 0 _ _ hsum) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- The `(m−i)`-weighted half: `Σ_i (m+1−i)·convTerm x (m+1) i ≃ (−x)·cₘ`. -/
theorem jWeighted (x : Q') (m : Nat) :
    (finSum (fun i => Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) (m + 2)).eqv
      ((-x) * conv x m) := by
  -- peel the last term (i = m+1), which vanishes
  show (finSum (fun i => Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) ((m + 1) + 1)).eqv _
  have hGlast : (Q'.ofNat ((m + 1) - (m + 1)) * convTerm x (m + 1) (m + 1)).eqv 0 := by
    have h0 : (m + 1) - (m + 1) = 0 := by omega
    rw [h0]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (convTerm x (m + 1) (m + 1)) Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv (convTerm x (m + 1) (m + 1)))
  have hGi : ∀ i, i < m + 1 →
      (Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i).eqv ((-x) * convTerm x m i) := by
    intro i hi
    have hile : i ≤ m := Nat.lt_succ_iff.mp hi
    have hsub : (m + 1) - i = (m - i) + 1 := by omega
    -- rewrite both occurrences of (m+1)-i
    have hconv : convTerm x (m + 1) i = ExpNeg.termAbs x i * ExpNeg.term x ((m - i) + 1) := by
      show ExpNeg.termAbs x i * ExpNeg.term x ((m + 1) - i) = _
      rw [hsub]
    rw [hsub, hconv]
    -- ofNat((m-i)+1) * (termAbs x i * term x ((m-i)+1)) ≃ -x * (termAbs x i * term x (m-i))
    -- move ofNat next to term: ofNat*(A*B) ≃ A*(ofNat*B)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat ((m - i) + 1))
        (ExpNeg.termAbs x i * ExpNeg.term x ((m - i) + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (ExpNeg.termAbs x i) (ExpNeg.term x ((m - i) + 1))
        (Q'.ofNat ((m - i) + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.termAbs x i)
        (ExpNeg.term x ((m - i) + 1) * Q'.ofNat ((m - i) + 1))
        (Q'.ofNat ((m - i) + 1) * ExpNeg.term x ((m - i) + 1))
        (Q'.mul_comm_eqv (ExpNeg.term x ((m - i) + 1)) (Q'.ofNat ((m - i) + 1)))) ?_
    -- now termAbs x i * (ofNat((m-i)+1) * term x ((m-i)+1)) ≃ termAbs x i * (-x * term x (m-i))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (ExpNeg.termAbs x i)
        (Q'.ofNat ((m - i) + 1) * ExpNeg.term x ((m - i) + 1))
        ((-x) * ExpNeg.term x (m - i))
        (ofNat_succ_mul_term x (m - i))) ?_
    -- termAbs x i * (-x * term x (m-i)) ≃ -x * (termAbs x i * term x (m-i)) = -x * convTerm x m i
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (ExpNeg.termAbs x i) (-x) (ExpNeg.term x (m - i)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ ((-x) * ExpNeg.termAbs x i) (ExpNeg.term x (m - i))
        (Q'.mul_comm_eqv (ExpNeg.termAbs x i) (-x))) ?_
    exact Q'.mul_assoc_eqv (-x) (ExpNeg.termAbs x i) (ExpNeg.term x (m - i))
  -- assemble: finSum over (m+2) = finSum over (m+1) + last
  show (finSum (fun i => Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) (m + 1)
        + Q'.ofNat ((m + 1) - (m + 1)) * convTerm x (m + 1) (m + 1)).eqv ((-x) * conv x m)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 hGlast) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
  -- finSum (fun i => ...) (m+1) ≃ -x * conv x m
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt _ (fun i => (-x) * convTerm x m i) (m + 1) hGi) ?_
  exact Q'.eqv_symm (RationalTail.const_mul_finSum (convTerm x m) (-x) (m + 1))

/-- `(m+1)·c_{m+1} ≃ 0`. -/
theorem ofNat_succ_mul_conv (x : Q') (m : Nat) :
    ((Q'.ofNat (m + 1)) * conv x (m + 1)).eqv 0 := by
  -- pull the constant into the sum
  refine Q'.eqv_trans _ _ _
    (RationalTail.const_mul_finSum (convTerm x (m + 1)) (Q'.ofNat (m + 1)) (m + 2)) ?_
  -- split each summand: ofNat(m+1)·t ≃ ofNat i·t + ofNat((m+1)-i)·t
  have hsplit : ∀ i, i < m + 2 →
      (Q'.ofNat (m + 1) * convTerm x (m + 1) i).eqv
        (Q'.ofNat i * convTerm x (m + 1) i + Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) := by
    intro i hi
    have hile : i ≤ m + 1 := Nat.lt_succ_iff.mp hi
    have hnat : i + ((m + 1) - i) = m + 1 := by omega
    have hofnat : (Q'.ofNat (m + 1)).eqv (Q'.ofNat i + Q'.ofNat ((m + 1) - i)) := by
      have hh := Q'.ofNat_add_eqv i ((m + 1) - i)
      rw [hnat] at hh
      exact hh
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat (m + 1)) (Q'.ofNat i + Q'.ofNat ((m + 1) - i))
        (convTerm x (m + 1) i) hofnat) ?_
    exact Q'.add_mul_eqv (Q'.ofNat i) (Q'.ofNat ((m + 1) - i)) (convTerm x (m + 1) i)
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt _
      (fun i => Q'.ofNat i * convTerm x (m + 1) i
              + Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) (m + 2) hsplit) ?_
  -- split the sum
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add (fun i => Q'.ofNat i * convTerm x (m + 1) i)
      (fun i => Q'.ofNat ((m + 1) - i) * convTerm x (m + 1) i) (m + 2)) ?_
  -- ≃ x·conv x m + (-x)·conv x m ≃ 0
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ (x * conv x m) _ (iWeighted x m)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (x * conv x m) _ ((-x) * conv x m)
    (jWeighted x m)) ?_
  -- x·c + (-x)·c ≃ x·c + -(x·c) ≃ 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (x * conv x m) ((-x) * conv x m) (-(x * conv x m))
      (Q'.neg_mul_eqv x (conv x m))) ?_
  exact Q'.add_neg_self_eqv (x * conv x m)

/-- **The convolution coefficient vanishes past degree 0.** `c_{m+1} ≃ 0`. -/
theorem conv_succ_eqv_zero (x : Q') (m : Nat) : (conv x (m + 1)).eqv 0 :=
  Q'.mul_eqv_zero_of_pos (Q'.ofNat_succ_pos m) (ofNat_succ_mul_conv x m)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.conv_zero
#print axioms ConstructiveReals.iWeighted
#print axioms ConstructiveReals.jWeighted
#print axioms ConstructiveReals.ofNat_succ_mul_conv
#print axioms ConstructiveReals.conv_succ_eqv_zero
