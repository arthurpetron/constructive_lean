/-
U.5 soundness (L4b) — `e⁻ˣ ≤ 1/(1+x)`, closing the `recipExpUB` obligation.

The chain, now that `eˣ·e⁻ˣ = 1` (L4a) is available:

  (a) `e⁻ˣ ≥ 0`  — from `eˣ·e⁻ˣ ≥ ½ > 0` and `eˣ ≥ 1 > 0`
       (`nonneg_of_mul_pos`).
  (b) `(1+x)·e⁻ˣ ≤ 1` — `(eˣ − (1+x))·e⁻ˣ ≥ 0` (`mul_nonneg` of two
       nonnegatives) distributes to `(1+x)·e⁻ˣ ≤ eˣ·e⁻ˣ ≤ 1`.
  (c) `e⁻ˣ ≤ 1/(1+x)` — scale (b) by `1/(1+x) ≥ 0` (`leRat_smul_nonneg`)
       and collapse `(1/(1+x))·(1+x) = 1` (`oneOver1p_mul_oneAddX`).

This makes the concrete `ExpUBInstance.recipExpUB` a *sound* upper bound for
`expNeg`, the load-bearing input the U.6 character-tail finite box needs.

Self-contained Q'/CReal helpers (`nonneg_of_mul_pos`, `le_of_sub_nonneg`,
`sub_mul_eqv`, `leRat_congr`, `oneOver1p_mul_oneAddX`) verified in parallel.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat`/`Int` enter.  No
`Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.ProductLaw
import ConstructiveReals.ExpUBInstance
import ConstructiveReals.CRealMulMono
import ConstructiveReals.CRealLe

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.ExpPos
open ConstructiveReals.HalfPow

/-! ## Q' / CReal helpers -/

namespace Q'

/-- `0 < a → 0 ≤ a*b → 0 ≤ b`. -/
theorem nonneg_of_mul_pos {a b : Q'} (ha : (0 : Q') < a) (h : (0 : Q') ≤ a * b) :
    (0 : Q') ≤ b := by
  have ha_num : (0 : Int) < a.num := by
    have hlt : (0 : Int) * (a.den : Int) < a.num * (1 : Int) := ha
    rw [Int.zero_mul, Int.mul_one] at hlt; exact hlt
  have hab_num : (0 : Int) ≤ a.num * b.num := (zero_le_iff_num_nonneg (a * b)).mp h
  rw [zero_le_iff_num_nonneg]
  rcases Int.lt_or_le b.num 0 with hb_neg | hb_nn
  · exfalso
    have hpos : 0 < a.num * (-b.num) := Int.mul_pos ha_num (Int.neg_pos.mpr hb_neg)
    rw [Int.mul_neg] at hpos
    omega
  · exact hb_nn

/-- `0 ≤ d + -c → c ≤ d`. -/
theorem le_of_sub_nonneg {c d : Q'} (h : (0 : Q') ≤ d + -c) : c ≤ d := by
  have hstep : (0 : Q') + c ≤ (d + -c) + c := add_le_add_right 0 (d + -c) c h
  have hR : ((d + -c) + c).eqv d :=
    eqv_trans _ _ _ (add_assoc_eqv d (-c) c)
      (eqv_trans _ _ _ (add_eqv_congr_left d (-c + c) 0 (neg_add_self_eqv c))
        (eqv_of_eq (add_zero' d)))
  rw [zero_add'] at hstep
  exact le_trans' c ((d + -c) + c) d hstep (le_of_eqv hR)

/-- `(a + -b)·c ≃ a·c + -(b·c)`. -/
theorem sub_mul_eqv (a b c : Q') : ((a + -b) * c).eqv (a * c + -(b * c)) :=
  eqv_trans _ _ _ (add_mul_eqv a (-b) c)
    (add_eqv_congr_left (a * c) ((-b) * c) (-(b * c)) (neg_mul_eqv b c))

/-- `0 < a → a ≤ b → 0 < b`. -/
theorem pos_of_lt_of_le {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) : (0 : Q') < b := by
  have hanum : (0 : Int) < a.num := by
    have h : (0 : Int) * (a.den : Int) < a.num * (1 : Int) := ha
    rw [Int.zero_mul, Int.mul_one] at h; exact h
  have hle : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
  have hbd : (0 : Int) < (b.den : Int) := by have := b.den_pos; omega
  have had : (0 : Int) < (a.den : Int) := by have := a.den_pos; omega
  have hlhs : (0 : Int) < a.num * (b.den : Int) := Int.mul_pos hanum hbd
  have hrhs : (0 : Int) < b.num * (a.den : Int) := by omega
  have hbnum : (0 : Int) < b.num := by
    rcases Int.lt_or_le 0 b.num with hpos | hnp
    · exact hpos
    · exfalso
      have hmul : b.num * (a.den : Int) ≤ 0 * (a.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hnp (Int.le_of_lt had)
      rw [Int.zero_mul] at hmul; omega
  show (0 : Int) * (b.den : Int) < b.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]; exact hbnum

end Q'

namespace CReal

/-- `leRat` is congruent under pointwise `eqv` of approximations. -/
theorem leRat_congr {a b : CReal} {c : Q'} (h : ∀ n, (a.approx n).eqv (b.approx n))
    (hb : CReal.leRat b c) : CReal.leRat a c := by
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n)) (hN n hn)⟩

end CReal

namespace ExpUBInstance

/-- `(1/(1+x))·(1+x) ≃ 1` for `x ≥ 0`. -/
theorem oneOver1p_mul_oneAddX (x : Q') (hx : (0 : Q') ≤ x) :
    (ExpUBInstance.oneOver1p x * (1 + x)).eqv 1 := by
  have hx_num : (0 : Int) ≤ x.num := (Q'.zero_le_iff_num_nonneg x).mp hx
  have htoNat : (x.num.toNat : Int) = x.num := Int.toNat_of_nonneg hx_num
  have h1x_num : (1 + x).num = (x.den : Int) + x.num := by
    show (1 : Int) * (x.den : Int) + x.num * (((1 : Q').den) : Int)
        = (x.den : Int) + x.num
    show (1 : Int) * (x.den : Int) + x.num * (1 : Int) = (x.den : Int) + x.num
    rw [Int.one_mul, Int.mul_one]
  have h1x_den : ((1 + x).den : Int) = (x.den : Int) := by
    rw [Q'.add_den_cast 1 x]
    show ((1 : Q').den : Int) * (x.den : Int) = (x.den : Int)
    show (1 : Int) * (x.den : Int) = (x.den : Int)
    rw [Int.one_mul]
  show (ExpUBInstance.oneOver1p x * (1 + x)).num * (((1 : Q').den) : Int)
      = ((1 : Q').num) * ((ExpUBInstance.oneOver1p x * (1 + x)).den : Int)
  show (ExpUBInstance.oneOver1p x * (1 + x)).num * (1 : Int)
      = (1 : Int) * ((ExpUBInstance.oneOver1p x * (1 + x)).den : Int)
  rw [Int.mul_one, Int.one_mul]
  show (ExpUBInstance.oneOver1p x).num * (1 + x).num
      = ((ExpUBInstance.oneOver1p x * (1 + x)).den : Int)
  rw [Q'.mul_den_cast, ExpUBInstance.oneOver1p_num,
      ExpUBInstance.oneOver1p_den, h1x_num, h1x_den]
  show (x.den : Int) * ((x.den : Int) + x.num)
      = ((x.num.toNat + x.den : Nat) : Int) * (x.den : Int)
  rw [Int.natCast_add, htoNat]
  rw [Int.mul_comm (x.den : Int) ((x.den : Int) + x.num),
      Int.add_comm (x.den : Int) x.num]

end ExpUBInstance

/-! ## (a) `e⁻ˣ ≥ 0` -/

/-- `e⁻ˣ ≥ 0`: the limit of `expNeg` is nonnegative (`eˣ·e⁻ˣ ≥ ½` and `eˣ > 0`). -/
theorem expNeg_geRat_zero (x : Q') (hx : (0 : Q') ≤ x) :
    ExpPos.geRat (ExpNeg.expNeg x hx) 0 := by
  intro δ hδ
  obtain ⟨N, hN⟩ := expProd_geRat x hx half (by decide)
  refine ⟨max N 1, fun n hn => ?_⟩
  show (0 : Q') ≤ partialSum x n + δ
  have h1 : (1 : Q') ≤ partialSumAbs x n * partialSum x n + half := hN n (by omega)
  have hQ : (0 : Q') ≤ partialSumAbs x n * partialSum x n := by
    have h2 : (1 : Q') + -half ≤ partialSumAbs x n * partialSum x n := by
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right 1 _ (-half) h1) (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ half (-half))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ (half + -half) 0 (Q'.add_neg_self_eqv half))
          (Q'.eqv_of_eq (Q'.add_zero' _)))
    exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (1 : Q') + -half) h2
  have hP : (0 : Q') < partialSumAbs x n := by
    have hP1 : (0 : Q') < partialSumAbs x 1 := by show (0 : Q') < (0 : Q') + (1 : Q'); decide
    have hmono : partialSumAbs x 1 ≤ partialSumAbs x n := by
      obtain ⟨d, hd⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
      rw [hd]; exact ExpPos.partialSumAbs_mono x hx 1 d
    exact Q'.pos_of_lt_of_le hP1 hmono
  have hge : (0 : Q') ≤ partialSum x n := Q'.nonneg_of_mul_pos hP hQ
  exact Q'.le_trans' _ _ _ hge (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hδ))

/-! ## (b) `(1+x)·e⁻ˣ ≤ 1` -/

theorem oneAddX_mul_expNeg_leRat (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.leRat (CReal.mul (CReal.ofQ' (1 + x)) (ExpNeg.expNeg x hx)) 1 := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Np, hNp⟩ := expProd_leRat x hx (half * ε) hhε
  obtain ⟨Ng, hNg⟩ := CReal.mul_nonneg
    (CReal.geRat_add_neg (ExpPos.oneAddX_le_expPos x hx))
    (expNeg_geRat_zero x hx) (half * ε) hhε
  refine ⟨max Np Ng, fun n hn => ?_⟩
  show (1 + x) * partialSum x n ≤ 1 + ε
  have hp : partialSumAbs x n * partialSum x n ≤ 1 + half * ε := hNp n (by omega)
  have hg : (0 : Q') ≤ (partialSumAbs x n + -(1 + x)) * partialSum x n + half * ε :=
    hNg n (by omega)
  -- distribute the gap product
  have hgr : (0 : Q') ≤ (partialSumAbs x n * partialSum x n
      + -((1 + x) * partialSum x n)) + half * ε :=
    Q'.le_trans' _ _ _ hg (Q'.le_of_eqv
      (Q'.add_eqv_congr_right _ _ (half * ε)
        (Q'.sub_mul_eqv (partialSumAbs x n) (1 + x) (partialSum x n))))
  -- (1+x)·M ≤ P·M + half ε
  have hstep : (1 + x) * partialSum x n ≤ partialSumAbs x n * partialSum x n + half * ε := by
    apply Q'.le_of_sub_nonneg
    refine Q'.le_trans' _ _ _ hgr (Q'.le_of_eqv ?_)
    -- (P·M + -((1+x)·M)) + hε ≃ (P·M + hε) + -((1+x)·M)
    exact Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (partialSumAbs x n * partialSum x n)
        (-((1 + x) * partialSum x n)) (half * ε))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (partialSumAbs x n * partialSum x n)
          (-((1 + x) * partialSum x n) + half * ε)
          (half * ε + -((1 + x) * partialSum x n))
          (Q'.add_comm_eqv _ _))
        (Q'.eqv_symm (Q'.add_assoc_eqv (partialSumAbs x n * partialSum x n)
          (half * ε) (-((1 + x) * partialSum x n)))))
  -- chain to 1 + ε
  refine Q'.le_trans' _ _ _ hstep ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (half * ε) hp) (Q'.le_of_eqv ?_)
  exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (half * ε) (half * ε))
    (Q'.add_eqv_congr_left 1 (half * ε + half * ε) ε (ExpNeg.two_halves ε))

/-! ## (c) `e⁻ˣ ≤ 1/(1+x)` -/

/-- **U.5 soundness.**  `e⁻ˣ ≤ 1/(1+x)` — `ExpUBInstance.recipExpUB` is a sound
upper bound for `expNeg`. -/
theorem expNeg_le_oneOver1p (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.leRat (ExpNeg.expNeg x hx) (ExpUBInstance.oneOver1p x) := by
  have hsc := CReal.leRat_smul_nonneg (ExpUBInstance.oneOver1p_nonneg x)
    (oneAddX_mul_expNeg_leRat x hx)
  have hsc' : CReal.leRat (CReal.mul (CReal.ofQ' (ExpUBInstance.oneOver1p x))
      (CReal.mul (CReal.ofQ' (1 + x)) (ExpNeg.expNeg x hx))) (ExpUBInstance.oneOver1p x) :=
    CReal.leRat_mono hsc (Q'.le_of_eqv (Q'.mul_one_eqv (ExpUBInstance.oneOver1p x)))
  refine CReal.leRat_congr ?_ hsc'
  intro n
  show (partialSum x n).eqv
    (ExpUBInstance.oneOver1p x * ((1 + x) * partialSum x n))
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (ExpUBInstance.oneOver1p x) (1 + x) (partialSum x n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ 1 (partialSum x n)
      (ExpUBInstance.oneOver1p_mul_oneAddX x hx)) ?_
  exact Q'.one_mul_eqv (partialSum x n)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.expNeg_geRat_zero
#print axioms ConstructiveReals.oneAddX_mul_expNeg_leRat
#print axioms ConstructiveReals.expNeg_le_oneOver1p
