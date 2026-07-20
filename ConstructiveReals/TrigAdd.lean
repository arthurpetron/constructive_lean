/-
Constructive trig: the even/odd extension `cosFull`/`sinFull : Q' → CReal`, the
elementary small-angle bounds, and the exp-term bridge that reduces the trig
addition formula to the exponential one — all over the project's `Q'`/`CReal`,
NO Mathlib `ℝ`, NO classical axioms, NO `sorry`.

`Constructive/Trig.lean` ships `cosNN`/`sinNN : (x : Q') → 0 ≤ x → CReal`, the
alternating cos/sin series at a *nonnegative* rational `x = |B|`.  This module
adds, in increasing depth:

  1. **`Q'`/`CReal` congruence plumbing** — `termAbs`, `cosTerm`, `sinTerm`,
     `cosPartial`, `sinPartial` are `eqv`-congruent in their angle argument, so
     `cosNN`/`sinNN` evaluated at `eqv`-equal angles have `CReal.Equiv` limits
     (`equiv_of_approx_eqv`).

  2. **The even/odd extension** (`cosFull`/`sinFull : Q' → CReal`): cos/sin of a
     *signed* rational angle, `cosFull x := cos |x|` (even, `cosFull_even`),
     `sinFull x := ± sin |x|` (odd, `sinFull_odd_of_nonneg`).

  3. **The small-angle bounds** (alternating-decreasing regime `0 ≤ x ≤ 1`),
     truncation form: `|cosPartial x (1+d) − 1| ≤ 2·termAbs x 2 = x²`
     (`cos_small_angle`) and `|sinPartial x (1+d) − sinTerm x 0| ≤ 2·termAbs x 3
     = x³/3` (`sin_small_angle`), the inputs to the `TrigBound` small-angle budget
     family (which is constant-agnostic — it accepts any `Bc`, `Bs`).  Built from
     the `cos`/`sin` block bounds dominated by the exponential magnitude block,
     bounded geometrically at ratio `1/2`.

  4. **The exp-term bridge** (`term_even_eq_abs`, `term_odd_eq_neg_abs`): the trig
     terms are the signed even/odd subsequences of the *signed* exponential series
     `ExpNeg.term x i = (−x)ⁱ/i!`, namely `term x (2k) ≈ termAbs x (2k)` and
     `term x (2k+1) ≈ −termAbs x (2k+1)`.

  5. **The trig convolutions** (`cosConv`/`sinConv`) and the per-degree addition
     identity, base case (`cosConv_addition_zero`).  The general identity is the
     research-novel core; see the footer for its precise statement and the named
     residual that remains (the even/odd reassembly of `ExpAddConv.convAdd`).

# Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (only via reused `Q'` ring / `Nat` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.Trig
import ConstructiveReals.TrigBound
import ConstructiveReals.CRealAbs
import ConstructiveReals.ExpAddConv
import ConstructiveReals.FinSumAlg
import ConstructiveReals.CornerBound
import ConstructiveReals.ProductDecompAdd
import ConstructiveReals.CornerBoundAdd
import ConstructiveReals.ExpAdd

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.Trig

namespace TrigAdd

/-! ## 0. `eqv`-congruence of the magnitude / trig terms in the angle

`termAbs x (k+1) = termAbs x k · (x · invSucc k)`, so an `eqv` on `x` propagates
through the product recurrence.  This lets `cosNN`/`sinNN` at `eqv`-equal angles
be related by `CReal.Equiv`. -/

/-- Antisymmetry of `Q'.le` packaged as `eqv`. -/
theorem eqv_of_le_of_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a.eqv b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm h1 h2

/-- `termAbs 0 (k+1) ≈ 0` — the magnitude series at the zero angle vanishes past
the constant term. -/
theorem termAbs_zero_succ_eqv :
    ∀ k, (termAbs (0 : Q') (k + 1)).eqv 0
  | 0 => by
    show (termAbs (0 : Q') 0 * ((0 : Q') * Q'.invSucc 0)).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (termAbs (0 : Q') 0) ((0 : Q') * Q'.invSucc 0) 0
        (Q'.zero_mul_eqv (Q'.invSucc 0))) ?_
    exact Q'.mul_zero_eqv (termAbs (0 : Q') 0)
  | k + 1 => by
    show (termAbs (0 : Q') (k + 1) * ((0 : Q') * Q'.invSucc (k + 1))).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (termAbs (0 : Q') (k + 1)) 0 ((0 : Q') * Q'.invSucc (k + 1))
        (termAbs_zero_succ_eqv k)) ?_
    exact Q'.zero_mul_eqv ((0 : Q') * Q'.invSucc (k + 1))

/-- `sinTerm 0 k ≈ 0` for every `k` (the odd magnitude term at zero vanishes). -/
theorem sinTerm_zero_angle_eqv (k : Nat) : (sinTerm (0 : Q') k).eqv 0 := by
  show (negPow k * termAbs (0 : Q') (2 * k + 1)).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow k) (termAbs (0 : Q') (2 * k + 1)) 0
      (termAbs_zero_succ_eqv (2 * k))) ?_
  exact Q'.mul_zero_eqv (negPow k)

/-- `sinPartial 0 n ≈ 0`. -/
theorem sinPartial_zero_eqv : ∀ n, (sinPartial (0 : Q') n).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinPartial (0 : Q') n + sinTerm (0 : Q') n).eqv 0
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sinPartial_zero_eqv n) (sinTerm_zero_angle_eqv n)) ?_
    show ((0 : Q') + 0).eqv 0
    exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- `Q'.abs 0 = 0`. -/
theorem abs_zero_eq : Q'.abs (0 : Q') = 0 := by
  unfold Q'.abs; rw [if_pos (Q'.le_refl' 0)]

/-- `termAbs` is `eqv`-congruent in its angle: `x ≈ y → termAbs x k ≈ termAbs y k`. -/
theorem termAbs_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ k, (termAbs x k).eqv (termAbs y k)
  | 0 => Q'.eqv_refl 1
  | k + 1 => by
    show (termAbs x k * (x * Q'.invSucc k)).eqv (termAbs y k * (y * Q'.invSucc k))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (termAbs x k) (termAbs y k) (x * Q'.invSucc k)
        (termAbs_eqv_congr h k)) ?_
    exact Q'.mul_eqv_congr_left (termAbs y k) (x * Q'.invSucc k) (y * Q'.invSucc k)
      (Q'.mul_eqv_congr_right x y (Q'.invSucc k) h)

/-- `cosTerm` is `eqv`-congruent in its angle. -/
theorem cosTerm_eqv_congr {x y : Q'} (h : x.eqv y) (k : Nat) :
    (cosTerm x k).eqv (cosTerm y k) :=
  Q'.mul_eqv_congr_left (negPow k) (termAbs x (2 * k)) (termAbs y (2 * k))
    (termAbs_eqv_congr h (2 * k))

/-- `sinTerm` is `eqv`-congruent in its angle. -/
theorem sinTerm_eqv_congr {x y : Q'} (h : x.eqv y) (k : Nat) :
    (sinTerm x k).eqv (sinTerm y k) :=
  Q'.mul_eqv_congr_left (negPow k) (termAbs x (2 * k + 1)) (termAbs y (2 * k + 1))
    (termAbs_eqv_congr h (2 * k + 1))

/-- `cosPartial` is `eqv`-congruent in its angle. -/
theorem cosPartial_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ n, (cosPartial x n).eqv (cosPartial y n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (cosPartial x n + cosTerm x n).eqv (cosPartial y n + cosTerm y n)
    exact Q'.add_eqv_congr' (cosPartial_eqv_congr h n) (cosTerm_eqv_congr h n)

/-- `sinPartial` is `eqv`-congruent in its angle. -/
theorem sinPartial_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ n, (sinPartial x n).eqv (sinPartial y n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinPartial x n + sinTerm x n).eqv (sinPartial y n + sinTerm y n)
    exact Q'.add_eqv_congr' (sinPartial_eqv_congr h n) (sinTerm_eqv_congr h n)

/-! ## 1. `CReal.Equiv` from termwise `eqv` of approximations

`Equiv_of_lifted_approx_equal` (in `CRealAbs.lean`) reduces `CReal.Equiv A B` to
`∀ N, Equiv (ofQ' (A.approx N)) (ofQ' (B.approx N))`; we supply the per-`N`
`Equiv` of the lifted constants from an `eqv` of the rationals. -/

/-- `Equiv (ofQ' a) (ofQ' b)` from `a ≈ b`. -/
theorem equiv_ofQ'_of_eqv {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show a ≤ b + ε ∧ b ≤ a + ε
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))

/-- If two `CReal`s have termwise-`eqv` approximation sequences, they are
`CReal.Equiv`. -/
theorem equiv_of_approx_eqv {A B : CReal}
    (h : ∀ n, (A.approx n).eqv (B.approx n)) : CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal (fun N => equiv_ofQ'_of_eqv (h N))

/-! ## 2. The even/odd extension `cosFull`/`sinFull : Q' → CReal` -/

/-- **Constructive `cos x`** for a signed rational angle `x`: `cos x := cos |x|`
(cosine is even). -/
def cosFull (x : Q') : CReal := cosNN (Q'.abs x) (Q'.abs_nonneg x)

/-- **Constructive `sin x`** for a signed rational angle `x`: `sin x := sin |x|`
if `0 ≤ x`, else `−sin |x|` (sine is odd). -/
def sinFull (x : Q') : CReal :=
  if (0 : Q') ≤ x then sinNN (Q'.abs x) (Q'.abs_nonneg x)
  else CReal.neg (sinNN (Q'.abs x) (Q'.abs_nonneg x))

@[simp] theorem cosFull_approx (x : Q') (n : Nat) :
    (cosFull x).approx n = cosPartial (Q'.abs x) n := rfl

/-- `cosFull` is even: `cosFull (−x) ≃ cosFull x`. -/
theorem cosFull_even (x : Q') : CReal.Equiv (cosFull (-x)) (cosFull x) := by
  refine equiv_of_approx_eqv (fun n => ?_)
  show (cosPartial (Q'.abs (-x)) n).eqv (cosPartial (Q'.abs x) n)
  exact cosPartial_eqv_congr (Q'.abs_neg' x) n

/-- `sinFull` of a nonnegative angle is `sinNN`. -/
theorem sinFull_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) :
    sinFull x = sinNN (Q'.abs x) (Q'.abs_nonneg x) := by
  unfold sinFull; rw [if_pos hx]

/-- `sinFull (−x) ≃ −sinFull x` (sine is odd).  We prove the case `0 ≤ x`; the
`x < 0` case is symmetric (then `−x > 0`).  Stated as a `CReal.Equiv`. -/
theorem sinFull_odd_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) :
    CReal.Equiv (sinFull (-x)) (CReal.neg (sinFull x)) := by
  -- sinFull x = sinNN |x|.  sinFull (−x): is 0 ≤ −x?  Only if x ≈ 0; in general
  -- −x ≤ 0, so sinFull (−x) = neg (sinNN |−x|) = neg (sinNN |x|) (up to eqv).
  by_cases hnx : (0 : Q') ≤ -x
  · -- both x and −x are ≥ 0, so x ≈ 0: sinNN |x| has approx sinPartial |x|;
    -- |x| ≈ |−x| and sinFull (−x) = sinNN |−x|.  Need sinNN |x| ≃ neg (sinNN |x|),
    -- which holds since x ≈ 0 ⇒ |x| ≈ 0 ⇒ sinPartial |x| n ≃ 0 = −0.
    refine equiv_of_approx_eqv (fun n => ?_)
    rw [sinFull_of_nonneg hnx, sinFull_of_nonneg hx]
    show (sinPartial (Q'.abs (-x)) n).eqv (-(sinPartial (Q'.abs x) n))
    -- x ≥ 0 and −x ≥ 0 ⇒ x ≈ 0.
    have hx0 : x.eqv 0 := by
      have h1 : x ≤ 0 := by
        have := Q'.neg_le_neg hnx
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv x)) ?_
        refine Q'.le_trans' _ _ _ this ?_
        exact Q'.le_of_eqv (by show ((-0 : Q')).eqv 0; decide)
      exact eqv_of_le_of_le h1 hx
    -- |−x| ≈ 0 and |x| ≈ 0
    have hax : (Q'.abs x).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hx0) (Q'.eqv_of_eq abs_zero_eq)
    have hanx : (Q'.abs (-x)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.abs_neg' x) hax
    -- sinPartial _ n ≃ sinPartial 0 n = 0 (since each sinTerm 0 k = 0).
    refine Q'.eqv_trans _ _ _ (sinPartial_eqv_congr hanx n) ?_
    refine Q'.eqv_trans _ _ _ (sinPartial_zero_eqv n) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (sinPartial_eqv_congr hax n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (sinPartial_zero_eqv n)) ?_
    show ((-0 : Q')).eqv 0; decide
  · -- −x < 0, so sinFull (−x) = neg (sinNN |−x|).
    refine equiv_of_approx_eqv (fun n => ?_)
    have hsx : sinFull (-x) = CReal.neg (sinNN (Q'.abs (-x)) (Q'.abs_nonneg (-x))) := by
      unfold sinFull; rw [if_neg hnx]
    rw [hsx, sinFull_of_nonneg hx]
    show (-(sinPartial (Q'.abs (-x)) n)).eqv (-(sinPartial (Q'.abs x) n))
    exact Q'.neg_eqv_congr _ _ (sinPartial_eqv_congr (Q'.abs_neg' x) n)

/-! ## 3. Small-angle bounds (the alternating-decreasing regime `0 ≤ x ≤ 1`)

`cosPartial x (1+d)` differs from `cosPartial x 1 = 1` by the cosine block from
index `1`, two-sidedly dominated by `cosBlockAbs x 1 d`; and that block is
dominated by the exponential magnitude block `blockAbs x 2 (2d)`.  For `0 ≤ x ≤ 1`
the ratio of consecutive magnitude terms from index `2` is `≤ x/3 ≤ 1/2`, so the
whole block is `≤ 2·termAbs x 2 = x²` (`blockAbs_le` at `r = 1/2`,
`H = 2·termAbs x 2`).  Hence `|cos x − 1| ≤ x²` at every truncation — the cosine
small-angle budget.  The sine analogue gives `|sin x − x| ≤ x³/3` (block from
index `1`, dominated by `blockAbs x 3 (2d) ≤ 2·termAbs x 3 = x³/3`). -/

/-- For `0 ≤ x ≤ 1`, the magnitude block from index `2` is `≤ 2·termAbs x 2`. -/
theorem blockAbs_two_le (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    blockAbs x 2 d ≤ termAbs x 2 + termAbs x 2 := by
  have hH : (0 : Q') ≤ termAbs x 2 + termAbs x 2 :=
    Q'.zero_le_add _ _ (termAbs_nonneg x hx 2) (termAbs_nonneg x hx 2)
  -- x·invSucc 2 ≤ half
  have hbound : x * Q'.invSucc 2 ≤ HalfPow.half := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right x 1 (Q'.invSucc 2) hx1 (Q'.invSucc_nonneg 2)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc 2))) ?_
    decide
  -- recurrence: termAbs x 2 + half·(2 termAbs x 2) ≤ 2 termAbs x 2  (equality)
  have hrec : termAbs x 2 + HalfPow.half * (termAbs x 2 + termAbs x 2)
      ≤ termAbs x 2 + termAbs x 2 := by
    refine Q'.le_of_eqv ?_
    refine Q'.add_eqv_congr_left (termAbs x 2) _ _ ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (termAbs x 2) (termAbs x 2))
      (ExpNeg.two_halves (termAbs x 2))
  exact blockAbs_le x HalfPow.half (termAbs x 2 + termAbs x 2) hx 2
    HalfPow.half_nonneg hH hbound hrec d

/-- For `0 ≤ x ≤ 1`, the magnitude block from index `3` is `≤ 2·termAbs x 3`. -/
theorem blockAbs_three_le (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    blockAbs x 3 d ≤ termAbs x 3 + termAbs x 3 := by
  have hH : (0 : Q') ≤ termAbs x 3 + termAbs x 3 :=
    Q'.zero_le_add _ _ (termAbs_nonneg x hx 3) (termAbs_nonneg x hx 3)
  have hbound : x * Q'.invSucc 3 ≤ HalfPow.half := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right x 1 (Q'.invSucc 3) hx1 (Q'.invSucc_nonneg 3)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc 3))) ?_
    decide
  have hrec : termAbs x 3 + HalfPow.half * (termAbs x 3 + termAbs x 3)
      ≤ termAbs x 3 + termAbs x 3 := by
    refine Q'.le_of_eqv ?_
    refine Q'.add_eqv_congr_left (termAbs x 3) _ _ ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (termAbs x 3) (termAbs x 3))
      (ExpNeg.two_halves (termAbs x 3))
  exact blockAbs_le x HalfPow.half (termAbs x 3 + termAbs x 3) hx 3
    HalfPow.half_nonneg hH hbound hrec d

/-- **Cosine small-angle bound (truncation form).**  For `0 ≤ x ≤ 1` and every
truncation `cosPartial x (1+d)`,
`|cosPartial x (1+d) − 1| ≤ 2·termAbs x 2 = x²`. -/
theorem cos_small_angle (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    Q'.abs (cosPartial x (1 + d) + (-1)) ≤ termAbs x 2 + termAbs x 2 := by
  -- block bound on cosBlockAbs x 1 d
  have hblk : cosBlockAbs x 1 d ≤ termAbs x 2 + termAbs x 2 := by
    refine Q'.le_trans' _ _ _ (cosBlockAbs_le_blockAbs x hx 1 d) ?_
    -- blockAbs x (2·1) (2d) = blockAbs x 2 (2d)
    show blockAbs x (2 * 1) (2 * d) ≤ termAbs x 2 + termAbs x 2
    have h21 : 2 * 1 = 2 := by decide
    rw [h21]
    exact blockAbs_two_le x hx hx1 (2 * d)
  -- |cosPartial x (1+d) − 1| ≤ cosBlockAbs x 1 d
  have hup : cosPartial x (1 + d) ≤ 1 + cosBlockAbs x 1 d := by
    have h := cos_block_upper x hx 1 d
    rw [cosPartial_one] at h
    exact h
  have hlo : (1 : Q') ≤ cosPartial x (1 + d) + cosBlockAbs x 1 d := by
    have h := cos_block_lower x hx 1 d
    rw [cosPartial_one] at h
    exact h
  -- assemble the two-sided bound, then abs_le
  refine Q'.abs_le ?_ ?_
  · -- −(block) ≤ cosPartial − 1
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hblk) (Q'.neg_le_sub_of_le_add hlo)
  · -- cosPartial − 1 ≤ block
    exact Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hup) hblk

/-- **Sine small-angle bound (truncation form).**  For `0 ≤ x ≤ 1` and every
truncation `sinPartial x (1+d)`,
`|sinPartial x (1+d) − sinTerm x 0| ≤ 2·termAbs x 3 = x³/3`.  Combined with
`sinTerm x 0 ≈ x`, this is `|sin x − x| ≤ x³/3`. -/
theorem sin_small_angle (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    Q'.abs (sinPartial x (1 + d) + (-(sinTerm x 0))) ≤ termAbs x 3 + termAbs x 3 := by
  have hblk : sinBlockAbs x 1 d ≤ termAbs x 3 + termAbs x 3 := by
    refine Q'.le_trans' _ _ _ (sinBlockAbs_le_blockAbs x hx 1 d) ?_
    show blockAbs x (2 * 1 + 1) (2 * d) ≤ termAbs x 3 + termAbs x 3
    have h31 : 2 * 1 + 1 = 3 := by decide
    rw [h31]
    exact blockAbs_three_le x hx hx1 (2 * d)
  -- sinPartial x 1 = sinTerm x 0
  have hsp1 : sinPartial x 1 = sinTerm x 0 := by
    show sinPartial x 0 + sinTerm x 0 = sinTerm x 0
    rw [sinPartial_zero, Q'.zero_add']
  have hup : sinPartial x (1 + d) ≤ sinTerm x 0 + sinBlockAbs x 1 d := by
    have h := sin_block_upper x hx 1 d
    rw [hsp1] at h
    exact h
  have hlo : sinTerm x 0 ≤ sinPartial x (1 + d) + sinBlockAbs x 1 d := by
    have h := sin_block_lower x hx 1 d
    rw [hsp1] at h
    exact h
  refine Q'.abs_le ?_ ?_
  · exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hblk) (Q'.neg_le_sub_of_le_add hlo)
  · exact Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hup) hblk

/-! ## 4. The exp-term bridge for the addition formula

The trig terms are the signed even/odd subsequences of the *signed* exponential
series `ExpNeg.term x i = (−x)ⁱ/i!`:

  * even index: `(−x)^{2k} = x^{2k}`, so `term x (2k) ≈ termAbs x (2k)`;
  * odd index:  `(−x)^{2k+1} = −x^{2k+1}`, so `term x (2k+1) ≈ −termAbs x (2k+1)`.

These two identities are what reduce the trig convolution to the exponential one
(`ExpAddConv.convAdd_eqv_term`).  Proved by a paired induction on `k`. -/

/-- **The even/odd exp-term bridge.**  `term x (2k) ≈ termAbs x (2k)` and
`term x (2k+1) ≈ −(termAbs x (2k+1))`. -/
theorem term_even_odd_bridge (x : Q') :
    ∀ k, (ExpNeg.term x (2 * k)).eqv (termAbs x (2 * k))
       ∧ (ExpNeg.term x (2 * k + 1)).eqv (-(termAbs x (2 * k + 1)))
  | 0 => by
    refine ⟨Q'.eqv_refl 1, ?_⟩
    -- term x 1 = term x 0 · ((−x)·c0) = 1·((−x)·c0); termAbs x 1 = 1·(x·c0).
    show (ExpNeg.term x 0 * ((-x) * Q'.invSucc 0)).eqv (-(termAbs x 0 * (x * Q'.invSucc 0)))
    rw [ExpNeg.term_zero]
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((-x) * Q'.invSucc 0)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv x (Q'.invSucc 0)) ?_
    refine Q'.neg_eqv_congr _ _ ?_
    exact Q'.eqv_symm (Q'.one_mul_eqv (x * Q'.invSucc 0))
  | k + 1 => by
    obtain ⟨hP, hQ⟩ := term_even_odd_bridge x k
    -- Need P(k+1): term x (2(k+1)) ≈ termAbs x (2(k+1)), and
    --      Q(k+1): term x (2(k+1)+1) ≈ −termAbs x (2(k+1)+1).
    -- Index arithmetic: 2(k+1) = (2k+1)+1, 2(k+1)+1 = ((2k+1)+1)+1.
    have hi1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have hi2 : 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 := by omega
    -- P(k+1): term x ((2k+1)+1) ≈ termAbs x ((2k+1)+1), proved from hQ.
    have hPk1 : (ExpNeg.term x ((2 * k + 1) + 1)).eqv (termAbs x ((2 * k + 1) + 1)) := by
      show (ExpNeg.term x (2 * k + 1) * ((-x) * Q'.invSucc (2 * k + 1))).eqv
          (termAbs x (2 * k + 1) * (x * Q'.invSucc (2 * k + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (ExpNeg.term x (2 * k + 1)) (-(termAbs x (2 * k + 1)))
          ((-x) * Q'.invSucc (2 * k + 1)) hQ) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-(termAbs x (2 * k + 1))) ((-x) * Q'.invSucc (2 * k + 1))
          (-(x * Q'.invSucc (2 * k + 1))) (Q'.neg_mul_eqv x (Q'.invSucc (2 * k + 1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv (termAbs x (2 * k + 1)) (-(x * Q'.invSucc (2 * k + 1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (termAbs x (2 * k + 1)) (x * Q'.invSucc (2 * k + 1)))) ?_
      exact Q'.neg_neg_eqv (termAbs x (2 * k + 1) * (x * Q'.invSucc (2 * k + 1)))
    refine ⟨?_, ?_⟩
    · rw [hi1]; exact hPk1
    · -- term x (((2k+1)+1)+1) = term x ((2k+1)+1) · ((−x)·c) ≈ termAbs((2k+1)+1)·(−(x·c))
      --   = −(termAbs((2k+1)+1)·(x·c)) = −termAbs(((2k+1)+1)+1)
      rw [hi2]
      show (ExpNeg.term x ((2 * k + 1) + 1) * ((-x) * Q'.invSucc ((2 * k + 1) + 1))).eqv
          (-(termAbs x ((2 * k + 1) + 1) * (x * Q'.invSucc ((2 * k + 1) + 1))))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (ExpNeg.term x ((2 * k + 1) + 1)) (termAbs x ((2 * k + 1) + 1))
          ((-x) * Q'.invSucc ((2 * k + 1) + 1)) hPk1) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (termAbs x ((2 * k + 1) + 1)) ((-x) * Q'.invSucc ((2 * k + 1) + 1))
          (-(x * Q'.invSucc ((2 * k + 1) + 1))) (Q'.neg_mul_eqv x (Q'.invSucc ((2 * k + 1) + 1)))) ?_
      exact Q'.mul_neg_eqv (termAbs x ((2 * k + 1) + 1)) (x * Q'.invSucc ((2 * k + 1) + 1))

/-- `term x (2k) ≈ termAbs x (2k)` (even-index bridge). -/
theorem term_even_eq_abs (x : Q') (k : Nat) :
    (ExpNeg.term x (2 * k)).eqv (termAbs x (2 * k)) :=
  (term_even_odd_bridge x k).1

/-- `term x (2k+1) ≈ −(termAbs x (2k+1))` (odd-index bridge). -/
theorem term_odd_eq_neg_abs (x : Q') (k : Nat) :
    (ExpNeg.term x (2 * k + 1)).eqv (-(termAbs x (2 * k + 1))) :=
  (term_even_odd_bridge x k).2

/-! ## 5. The trig convolutions and the per-degree addition identity

`CosConv A B m = Σ_{i=0}^{m} cosTerm A i · cosTerm B (m−i)` and
`SinConv A B m = Σ_{i=0}^{m} sinTerm A i · sinTerm B (m−i)` are the cos·cos and
sin·sin Cauchy products at degree `m`.  The exact per-degree addition identity —
the algebraic heart of `cos(A+B) = cos A cos B − sin A sin B` — is

    CosConv A B m  +  (−(SinConv A B (m−1)))  ≃  cosTerm (A+B) m .          (TC)

Note the **sin convolution is at degree `m−1`**, not `m`: in the even/odd split of
`convAdd A B (2m)` (`ExpAddConv.convAdd_eqv_term`), the even-`i` terms reassemble
`CosConv A B m` (each even·even product `term A (2i)·term B (2j)` with `i+j=m`
equals `cosTerm A i·cosTerm B j` up to the shared sign `(−1)^m`, by
`term_even_eq_abs`), while the odd-`i` terms reassemble `SinConv A B (m−1)`
(each odd·odd product `term A (2i+1)·term B (2j+1)` with `i+j=m−1` equals
`sinTerm A i·sinTerm B j` up to `(−1)^{m−1}`, by `term_odd_eq_neg_abs`).  The two
shared signs `(−1)^m`, `(−1)^{m−1}` differ by one factor of `−1`, which is the
algebraic source of the MINUS sign in the addition formula. -/

/-- `i`-th term of the cos·cos Cauchy product at degree `m`. -/
def cosConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => cosTerm A i * cosTerm B (m - i)

/-- `i`-th term of the sin·sin Cauchy product at degree `m`. -/
def sinConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => sinTerm A i * sinTerm B (m - i)

/-- `CosConv A B m = Σ_{i=0}^{m} cosTerm A i · cosTerm B (m−i)`. -/
def cosConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (cosConvTerm A B m) (m + 1)

/-- `SinConv A B m = Σ_{i=0}^{m} sinTerm A i · sinTerm B (m−i)`. -/
def sinConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (sinConvTerm A B m) (m + 1)

/-- **The per-degree addition identity at `m = 0` (base case of (TC)).**
`cosConv A B 0 ≃ cosTerm (A+B) 0`.  At `m = 0` the sin·sin part is empty, so this
is `cosTerm A 0 · cosTerm B 0 = 1·1 = 1 = cosTerm (A+B) 0`. -/
theorem cosConv_addition_zero (A B : Q') :
    (cosConv A B 0).eqv (cosTerm (A + B) 0) := by
  show ((0 : Q') + cosTerm A 0 * cosTerm B 0).eqv (cosTerm (A + B) 0)
  rw [cosTerm_zero, cosTerm_zero, cosTerm_zero, Q'.zero_add']
  exact Q'.mul_one_eqv 1

/-! ### 5a. `negPow` sign algebra (the source of the addition-formula minus)

The two shared signs in the even/odd reassembly are `negPow m = (−1)^m` (even
sub-sum) and `negPow (m−1) = (−1)^{m−1}` (odd sub-sum).  Their product with the
outer `negPow m` collapses to `1` (even) and `−1` (odd), and that single `−1` is
the minus of `cos(A+B) = cos A cos B − sin A sin B`. -/

/-- `negPow (i + j) ≈ negPow i · negPow j`. -/
theorem negPow_add (i : Nat) : ∀ j, (negPow (i + j)).eqv (negPow i * negPow j)
  | 0 => by
    show (negPow (i + 0)).eqv (negPow i * negPow 0)
    rw [Nat.add_zero]
    exact Q'.eqv_symm (Q'.mul_one_eqv (negPow i))
  | j + 1 => by
    show (negPow (i + (j + 1))).eqv (negPow i * negPow (j + 1))
    have hidx : i + (j + 1) = (i + j) + 1 := by omega
    rw [hidx]
    show (-(negPow (i + j))).eqv (negPow i * (-(negPow j)))
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (negPow_add i j)) ?_
    exact Q'.eqv_symm (Q'.mul_neg_eqv (negPow i) (negPow j))

/-- `negPow (2k) ≈ 1`. -/
theorem negPow_two_mul : ∀ k, (negPow (2 * k)).eqv 1
  | 0 => by show (negPow 0).eqv 1; exact Q'.eqv_refl 1
  | k + 1 => by
    have hidx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hidx]
    show (-(negPow (2 * k + 1))).eqv 1
    show (-(-(negPow (2 * k)))).eqv 1
    refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (negPow (2 * k))) ?_
    exact negPow_two_mul k

/-- `negPow m · negPow m ≈ 1`. -/
theorem negPow_self_mul (m : Nat) : (negPow m * negPow m).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (negPow_add m m)) ?_
  have : m + m = 2 * m := by omega
  rw [this]
  exact negPow_two_mul m

/-- `negPow (m+1) · negPow m ≈ −1`. -/
theorem negPow_succ_mul (m : Nat) : (negPow (m + 1) * negPow m).eqv (-(1 : Q')) := by
  show ((-(negPow m)) * negPow m).eqv (-(1 : Q'))
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (negPow m) (negPow m)) ?_
  exact Q'.neg_eqv_congr _ _ (negPow_self_mul m)

/-! ### 5b. The even/odd `finSum` deinterleave

`finSum f (2m+1) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)` — the even-index sub-sum (`m+1`
terms) plus the odd-index sub-sum (`m` terms).  Proved by induction on `m`, peeling
one even and one odd term per step.  Pure `finSum`/`add`-algebra reindexing. -/

/-- `finSum f (2m+3) = finSum f (2m+1) + f(2m+1) + f(2m+2)` (defeq peel of two). -/
theorem finSum_two_step (f : RationalTail.QSeq) (k : Nat) :
    RationalTail.finSum f (k + 2)
      = RationalTail.finSum f k + f k + f (k + 1) := rfl

/-- Pure `Q'` rearrangement: `(s·t)·(a·b) ≈ (s·a)·(t·b)`. -/
theorem mul_shuffle_4 (s t a b : Q') :
    ((s * t) * (a * b)).eqv ((s * a) * (t * b)) := by
  -- (s·t)·(a·b) ≈ s·(t·(a·b)) ≈ s·((t·a)·b) ≈ s·((a·t)·b) ≈ s·(a·(t·b))
  --   ≈ (s·a)·(t·b)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s t (a * b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv t a b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _
      (Q'.mul_eqv_congr_right (t * a) (a * t) b (Q'.mul_comm_eqv t a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (Q'.mul_assoc_eqv a t b)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv s a (t * b))

/-- Pure `Q'` rearrangement: `(a+b)+((p+q)+r) ≈ (a+p)+((b+r)+q)`.  Both sides
reduce to `((a+p)+(b+r))+q`. -/
theorem add_rearrange_5 (a b p q r : Q') :
    ((a + b) + ((p + q) + r)).eqv ((a + p) + ((b + r) + q)) := by
  -- LHS ≈ ((a+p)+(b+r))+q
  have hL : ((a + b) + ((p + q) + r)).eqv (((a + p) + (b + r)) + q) := by
    -- (p+q)+r ≈ (p+r)+q
    have h1 : ((p + q) + r).eqv ((p + r) + q) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p q r) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left p _ _ (Q'.add_comm_eqv q r)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv p r q)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (a + b) _ _ h1) ?_
    -- (a+b)+((p+r)+q) ≈ ((a+b)+(p+r))+q ≈ ((a+p)+(b+r))+q
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (a + b) (p + r) q)) ?_
    exact Q'.add_eqv_congr_right _ _ q (Q'.add_swap_inner a b p r)
  -- RHS ≈ ((a+p)+(b+r))+q
  have hR : ((a + p) + ((b + r) + q)).eqv (((a + p) + (b + r)) + q) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (a + p) (b + r) q)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- Pure `Q'` rearrangement: `((E+O)+a)+b ≈ (E+b)+(O+a)`. -/
theorem add_rearrange_4 (E O a b : Q') :
    (((E + O) + a) + b).eqv ((E + b) + (O + a)) := by
  -- ((E+O)+a)+b ≈ (E+(O+a))+b ≈ E+((O+a)+b) ≈ E+(b+(O+a)) ≈ (E+b)+(O+a)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ b (Q'.add_assoc_eqv E O a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv E (O + a) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left E _ _ (Q'.add_comm_eqv (O + a) b)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv E b (O + a))

/-- **Even/odd deinterleave.**  `Σ_{i<2m+1} f(i) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)`. -/
theorem finSum_even_odd_split (f : RationalTail.QSeq) :
    ∀ m, (RationalTail.finSum f (2 * m + 1)).eqv
        (RationalTail.finSum (fun p => f (2 * p)) (m + 1)
          + RationalTail.finSum (fun p => f (2 * p + 1)) m)
  | 0 => by
    show (RationalTail.finSum f 1).eqv
        (RationalTail.finSum (fun p => f (2 * p)) 1 + RationalTail.finSum (fun p => f (2 * p + 1)) 0)
    show ((0 : Q') + f 0).eqv (((0 : Q') + f (2 * 0)) + (0 : Q'))
    rw [Nat.mul_zero, Q'.zero_add', Q'.add_zero']
    exact Q'.eqv_refl (f 0)
  | m + 1 => by
    -- LHS index 2*(m+1)+1 = (2m+1)+2 reduces (defeq) to a two-term peel; RHS even
    -- sub-sum at m+2 peels (defeq) to (Σ even m+1)+f(2(m+1)), odd at m+1 to (Σ odd m)+f(2m+1).
    show (RationalTail.finSum f (2 * m + 1) + f (2 * m + 1) + f (2 * (m + 1))).eqv
        ((RationalTail.finSum (fun p => f (2 * p)) (m + 1) + f (2 * (m + 1)))
          + (RationalTail.finSum (fun p => f (2 * p + 1)) m + f (2 * m + 1)))
    -- IH: finSum f (2m+1) ≈ E + O.  Goal: ((E+O) + a) + b ≈ (E+b) + (O+a).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (f (2 * (m + 1)))
        (Q'.add_eqv_congr_right _ _ (f (2 * m + 1)) (finSum_even_odd_split f m))) ?_
    exact add_rearrange_4 _ _ (f (2 * m + 1)) (f (2 * (m + 1)))

/-! ### 5c. The bridge from trig convolution terms to even/odd convAdd terms

`cosConvTerm A B m p = cosTerm A p · cosTerm B (m−p)` reassembles the **even**-index
convAdd term `convAddTerm A B (2m) (2p)` with the shared sign `(−1)^m`; the
**odd**-index convAdd term `convAddTerm A B (2m) (2p+1)` reassembles
`sinConvTerm A B (m−1) p` with shared sign `(−1)^{m−1}`.  Sign via §5a, magnitude
via the §4 bridge `term_even_eq_abs`/`term_odd_eq_neg_abs`. -/

/-- Even-term bridge: for `p ≤ m`,
`cosConvTerm A B m p ≈ negPow m · convAddTerm A B (2m) (2p)`. -/
theorem cosConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (cosConvTerm A B m p).eqv (negPow m * convAddTerm A B (2 * m) (2 * p)) := by
  have hsub : 2 * m - 2 * p = 2 * (m - p) := by omega
  -- LHS = (negPow p · termAbs A (2p)) · (negPow (m−p) · termAbs B (2(m−p)))
  show ((negPow p * termAbs A (2 * p)) * (negPow (m - p) * termAbs B (2 * (m - p)))).eqv
      (negPow m * (ExpNeg.term A (2 * p) * ExpNeg.term B (2 * m - 2 * p)))
  rw [hsub]
  -- RHS: replace term A (2p) ≈ termAbs A (2p), term B (2(m−p)) ≈ termAbs B (2(m−p)).
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p)) (termAbs A (2 * p)) _
        (term_even_eq_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_left (termAbs A (2 * p)) (ExpNeg.term B (2 * (m - p)))
        (termAbs B (2 * (m - p))) (term_even_eq_abs B (m - p)))) ?_
  -- Now: negPow m · (termAbs A (2p) · termAbs B (2(m−p)))  ≈  LHS.
  -- LHS = (negPow p · tA) · (negPow (m−p) · tB).  Rearrange to negPow m · (tA · tB).
  -- First collapse the sign: negPow m ≈ negPow p · negPow (m−p)  (p + (m−p) = m).
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]
    exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p) * termAbs B (2 * (m - p))) hsign) ?_
  -- Goal: (negPow p · negPow (m−p)) · (tA · tB) ≈ (negPow p · tA) · (negPow (m−p) · tB)
  -- Pure mul-comm/assoc shuffle: (s·t)·(a·b) ≈ (s·a)·(t·b).
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p)) (termAbs B (2 * (m - p)))

/-- `(-a)·(-b) ≈ a·b`. -/
theorem neg_mul_neg (a b : Q') : ((-a) * (-b)).eqv (a * b) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) ?_
  exact Q'.neg_neg_eqv (a * b)

/-- Odd-term bridge: for `p ≤ m`,
`sinConvTerm A B m p ≈ negPow m · convAddTerm A B (2(m+1)) (2p+1)`.
The convAdd partner index is `(2m+2)−(2p+1) = 2(m−p)+1` (odd), so both factors
flip sign and the product is positive; the shared sign is `negPow m`. -/
theorem sinConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (sinConvTerm A B m p).eqv (negPow m * convAddTerm A B (2 * (m + 1)) (2 * p + 1)) := by
  have hsub : 2 * (m + 1) - (2 * p + 1) = 2 * (m - p) + 1 := by omega
  show ((negPow p * termAbs A (2 * p + 1)) * (negPow (m - p) * termAbs B (2 * (m - p) + 1))).eqv
      (negPow m * (ExpNeg.term A (2 * p + 1) * ExpNeg.term B (2 * (m + 1) - (2 * p + 1))))
  rw [hsub]
  refine Q'.eqv_symm ?_
  -- Replace term A (2p+1) ≈ −termAbs A (2p+1), term B (2(m−p)+1) ≈ −termAbs B (2(m−p)+1).
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p + 1)) (-(termAbs A (2 * p + 1))) _
        (term_odd_eq_neg_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_left (-(termAbs A (2 * p + 1))) (ExpNeg.term B (2 * (m - p) + 1))
        (-(termAbs B (2 * (m - p) + 1))) (term_odd_eq_neg_abs B (m - p)))) ?_
  -- (−tA)·(−tB) ≈ tA·tB
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (neg_mul_neg (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p) + 1)))) ?_
  -- sign collapse negPow m ≈ negPow p · negPow (m−p)
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]; exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p + 1) * termAbs B (2 * (m - p) + 1)) hsign) ?_
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p) + 1))

/-! ### 5d. Sum-level even/odd bridges and the per-degree addition identity (TC) -/

/-- The even sub-sum of `convAdd A B (2(m+1))` (the `m+2` even-index terms). -/
def evenSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)

/-- The odd sub-sum of `convAdd A B (2(m+1))` (the `m+1` odd-index terms). -/
def oddSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1)

/-- `cosConv A B (m+1) ≈ negPow (m+1) · evenSub A B m`. -/
theorem cosConv_eqv_evenSub (A B : Q') (m : Nat) :
    (cosConv A B (m + 1)).eqv (negPow (m + 1) * evenSub A B m) := by
  -- cosConv (m+1) = finSum (cosConvTerm A B (m+1)) (m+2)
  show (RationalTail.finSum (cosConvTerm A B (m + 1)) (m + 2)).eqv
      (negPow (m + 1) * RationalTail.finSum
        (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (cosConvTerm A B (m + 1))
      (fun p => negPow (m + 1) * convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)
      (fun p hp => cosConvTerm_eqv A B (m + 1) p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (negPow (m + 1)) (m + 2))

/-- `sinConv A B m ≈ negPow m · oddSub A B m`. -/
theorem sinConv_eqv_oddSub (A B : Q') (m : Nat) :
    (sinConv A B m).eqv (negPow m * oddSub A B m) := by
  show (RationalTail.finSum (sinConvTerm A B m) (m + 1)).eqv
      (negPow m * RationalTail.finSum
        (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (sinConvTerm A B m)
      (fun p => negPow m * convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1)
      (fun p hp => sinConvTerm_eqv A B m p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (negPow m) (m + 1))

/-- `convAdd A B (2(m+1)) ≈ evenSub A B m + oddSub A B m` (even/odd deinterleave at
the convAdd degree). -/
theorem convAdd_eqv_even_odd (A B : Q') (m : Nat) :
    (convAdd A B (2 * (m + 1))).eqv (evenSub A B m + oddSub A B m) := by
  -- convAdd A B D = finSum (convAddTerm A B D) (D+1), D = 2(m+1); D+1 = 2(m+1)+1.
  show (RationalTail.finSum (convAddTerm A B (2 * (m + 1))) (2 * (m + 1) + 1)).eqv
      (RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)
        + RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1))
  exact finSum_even_odd_split (convAddTerm A B (2 * (m + 1))) (m + 1)

/-- `cosTerm (A+B) (m+1) ≈ negPow (m+1) · term (A+B) (2(m+1))` (even-index magnitude
bridge applied at the sum angle). -/
theorem cosTerm_eqv_negPow_term (A B : Q') (m : Nat) :
    (cosTerm (A + B) (m + 1)).eqv (negPow (m + 1) * ExpNeg.term (A + B) (2 * (m + 1))) := by
  show (negPow (m + 1) * termAbs (A + B) (2 * (m + 1))).eqv
      (negPow (m + 1) * ExpNeg.term (A + B) (2 * (m + 1)))
  exact Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
    (Q'.eqv_symm (term_even_eq_abs (A + B) (m + 1)))

/-- **The per-degree trig addition identity (TC), inductive degrees `m+1`.**
`cosConv A B (m+1) + (−(sinConv A B m)) ≃ cosTerm (A+B) (m+1)`.

This is the algebraic heart of `cos(A+B) = cos A cos B − sin A sin B`: the even
sub-sum of the exponential Cauchy coefficient `convAdd A B (2(m+1))` reassembles
`cosConv` with sign `(−1)^{m+1}`, the odd sub-sum reassembles `sinConv` with sign
`(−1)^m`, and the single `(−1)^{m+1}·(−1)^m = −1` discrepancy is the MINUS sign. -/
theorem cosConv_addition (A B : Q') (m : Nat) :
    (cosConv A B (m + 1) + (-(sinConv A B m))).eqv (cosTerm (A + B) (m + 1)) := by
  -- Step 1: substitute (C) and (Sn).
  -- cosConv(m+1) ≈ negPow(m+1)·even ; sinConv m ≈ negPow m·odd.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (cosConv_eqv_evenSub A B m)
      (Q'.neg_eqv_congr _ _ (sinConv_eqv_oddSub A B m))) ?_
  -- Goal: negPow(m+1)·even + (−(negPow m·odd)) ≈ cosTerm(A+B)(m+1)
  -- Step 2: −(negPow m·odd) ≈ negPow(m+1)·odd  (since negPow(m+1) = −negPow m).
  have hflip : (-(negPow m * oddSub A B m)).eqv (negPow (m + 1) * oddSub A B m) := by
    show (-(negPow m * oddSub A B m)).eqv ((-(negPow m)) * oddSub A B m)
    exact Q'.eqv_symm (Q'.neg_mul_eqv (negPow m) (oddSub A B m))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (negPow (m + 1) * evenSub A B m) _ _ hflip) ?_
  -- Goal: negPow(m+1)·even + negPow(m+1)·odd ≈ cosTerm(A+B)(m+1)
  -- Step 3: factor: ≈ negPow(m+1)·(even+odd)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_add_eqv (negPow (m + 1)) (evenSub A B m) (oddSub A B m))) ?_
  -- Step 4: even+odd ≈ convAdd A B (2(m+1)) ≈ term(A+B)(2(m+1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.eqv_symm (convAdd_eqv_even_odd A B m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _ (convAdd_eqv_term A B (2 * (m + 1)))) ?_
  -- Goal: negPow(m+1)·term(A+B)(2(m+1)) ≈ cosTerm(A+B)(m+1)
  exact Q'.eqv_symm (cosTerm_eqv_negPow_term A B m)

/-! ### 5e. Trig triangle decompositions (cos·cos and sin·sin diagonal sums)

Exactly as `ProductDecompAdd.triAdd` does for the exponential single product, the
cos·cos and sin·sin partial products row-split at the diagonal into a triangle
(whose recurrence peels one `cosConv`/`sinConv` per row) plus a corner.  Here we
land the triangle recurrences `cosTri (n+1) ≃ cosTri n + cosConv n` and
`cosTri n ≃ Σ_{m<n} cosConv m` (and the `sin` analogues).  These are the clean
adaptations of `triAdd_succ`/`triAdd_eqv_convAddSum`; the difference-of-products
diagonal collapse (which needs the degree-shifted telescope of `cosConv_addition`)
and the corner bounds remain — see the footer residual. -/

/-- `cosPartial x n = finSum (cosTerm x) n` (defeq by induction). -/
theorem cosPartial_eq_finSum (x : Q') :
    ∀ n, cosPartial x n = RationalTail.finSum (cosTerm x) n
  | 0 => rfl
  | n + 1 => by
    show cosPartial x n + cosTerm x n = RationalTail.finSum (cosTerm x) n + cosTerm x n
    rw [cosPartial_eq_finSum x n]

/-- `sinPartial x n = finSum (sinTerm x) n` (defeq by induction). -/
theorem sinPartial_eq_finSum (x : Q') :
    ∀ n, sinPartial x n = RationalTail.finSum (sinTerm x) n
  | 0 => rfl
  | n + 1 => by
    show sinPartial x n + sinTerm x n = RationalTail.finSum (sinTerm x) n + sinTerm x n
    rw [sinPartial_eq_finSum x n]

/-- `cosTriTerm A B n i = cosTerm A i · cosPartial B (n−i)`. -/
def cosTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * cosPartial B (n - i)

/-- `cosTri A B n = Σ_{i<n} cosTerm A i · cosPartial B (n−i)`. -/
def cosTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosTriTerm A B n) n

/-- `sinTriTerm A B n i = sinTerm A i · sinPartial B (n−i)`. -/
def sinTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * sinPartial B (n - i)

/-- `sinTri A B n = Σ_{i<n} sinTerm A i · sinPartial B (n−i)`. -/
def sinTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinTriTerm A B n) n

/-- Cosine triangle recurrence `cosTri (n+1) ≃ cosTri n + cosConv n`. -/
theorem cosTri_succ (A B : Q') (n : Nat) :
    (cosTri A B (n + 1)).eqv (cosTri A B n + cosConv A B n) := by
  show (RationalTail.finSum (cosTriTerm A B (n + 1)) n + cosTriTerm A B (n + 1) n).eqv
      (cosTri A B n + cosConv A B n)
  -- last term: cosTerm A n · cosPartial B 1 = cosTerm A n · cosTerm B 0
  have hlast : (cosTriTerm A B (n + 1) n).eqv (cosTerm A n * cosTerm B 0) := by
    show (cosTerm A n * cosPartial B ((n + 1) - n)).eqv (cosTerm A n * cosTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (cosTerm A n * ((0 : Q') + cosTerm B 0)).eqv (cosTerm A n * cosTerm B 0)
    exact Q'.mul_eqv_congr_left (cosTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosTerm B 0)))
  -- row split: cosTriTerm (n+1) i ≈ cosTriTerm n i + cosConvTerm n i for i < n
  have hrow : ∀ i, i < n →
      (cosTriTerm A B (n + 1) i).eqv (cosTriTerm A B n i + cosConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (cosTerm A i * cosPartial B ((n + 1) - i)).eqv
        (cosTerm A i * cosPartial B (n - i) + cosTerm A i * cosTerm B (n - i))
    rw [hsub]
    show (cosTerm A i * (cosPartial B (n - i) + cosTerm B (n - i))).eqv
        (cosTerm A i * cosPartial B (n - i) + cosTerm A i * cosTerm B (n - i))
    exact Q'.mul_add_eqv (cosTerm A i) (cosPartial B (n - i)) (cosTerm B (n - i))
  have hinner : (RationalTail.finSum (cosTriTerm A B (n + 1)) n).eqv
      (cosTri A B n + RationalTail.finSum (cosConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (cosTriTerm A B (n + 1))
        (fun i => cosTriTerm A B n i + cosConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (cosTriTerm A B n) (cosConvTerm A B n) n)
  -- cosConv n = finSum (cosConvTerm n) (n+1) = finSum (cosConvTerm n) n + cosConvTerm n n,
  -- and cosConvTerm n n = cosTerm A n · cosTerm B 0.
  have hconv : (cosConv A B n).eqv
      (RationalTail.finSum (cosConvTerm A B n) n + cosTerm A n * cosTerm B 0) := by
    show (RationalTail.finSum (cosConvTerm A B n) n + cosConvTerm A B n n).eqv
        (RationalTail.finSum (cosConvTerm A B n) n + cosTerm A n * cosTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (cosTerm A n * cosTerm B (n - n)).eqv (cosTerm A n * cosTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (cosTri A B n) (RationalTail.finSum (cosConvTerm A B n) n)
      (cosTerm A n * cosTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (cosTri A B n) _ _ (Q'.eqv_symm hconv)

/-- Sine triangle recurrence `sinTri (n+1) ≃ sinTri n + sinConv n`. -/
theorem sinTri_succ (A B : Q') (n : Nat) :
    (sinTri A B (n + 1)).eqv (sinTri A B n + sinConv A B n) := by
  show (RationalTail.finSum (sinTriTerm A B (n + 1)) n + sinTriTerm A B (n + 1) n).eqv
      (sinTri A B n + sinConv A B n)
  have hlast : (sinTriTerm A B (n + 1) n).eqv (sinTerm A n * sinTerm B 0) := by
    show (sinTerm A n * sinPartial B ((n + 1) - n)).eqv (sinTerm A n * sinTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (sinTerm A n * ((0 : Q') + sinTerm B 0)).eqv (sinTerm A n * sinTerm B 0)
    exact Q'.mul_eqv_congr_left (sinTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (sinTerm B 0)))
  have hrow : ∀ i, i < n →
      (sinTriTerm A B (n + 1) i).eqv (sinTriTerm A B n i + sinConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (sinTerm A i * sinPartial B ((n + 1) - i)).eqv
        (sinTerm A i * sinPartial B (n - i) + sinTerm A i * sinTerm B (n - i))
    rw [hsub]
    show (sinTerm A i * (sinPartial B (n - i) + sinTerm B (n - i))).eqv
        (sinTerm A i * sinPartial B (n - i) + sinTerm A i * sinTerm B (n - i))
    exact Q'.mul_add_eqv (sinTerm A i) (sinPartial B (n - i)) (sinTerm B (n - i))
  have hinner : (RationalTail.finSum (sinTriTerm A B (n + 1)) n).eqv
      (sinTri A B n + RationalTail.finSum (sinConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (sinTriTerm A B (n + 1))
        (fun i => sinTriTerm A B n i + sinConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (sinTriTerm A B n) (sinConvTerm A B n) n)
  have hconv : (sinConv A B n).eqv
      (RationalTail.finSum (sinConvTerm A B n) n + sinTerm A n * sinTerm B 0) := by
    show (RationalTail.finSum (sinConvTerm A B n) n + sinConvTerm A B n n).eqv
        (RationalTail.finSum (sinConvTerm A B n) n + sinTerm A n * sinTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (sinTerm A n * sinTerm B (n - n)).eqv (sinTerm A n * sinTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (sinTri A B n) (RationalTail.finSum (sinConvTerm A B n) n)
      (sinTerm A n * sinTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (sinTri A B n) _ _ (Q'.eqv_symm hconv)

/-- `cosTri A B n ≃ Σ_{m<n} cosConv A B m`. -/
theorem cosTri_eqv_convSum (A B : Q') :
    ∀ n, (cosTri A B n).eqv (RationalTail.finSum (cosConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (cosTri A B (n + 1)).eqv (RationalTail.finSum (cosConv A B) n + cosConv A B n)
    refine Q'.eqv_trans _ _ _ (cosTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (cosTri A B n) _ (cosConv A B n) (cosTri_eqv_convSum A B n)

/-- `sinTri A B n ≃ Σ_{m<n} sinConv A B m`. -/
theorem sinTri_eqv_convSum (A B : Q') :
    ∀ n, (sinTri A B n).eqv (RationalTail.finSum (sinConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinTri A B (n + 1)).eqv (RationalTail.finSum (sinConv A B) n + sinConv A B n)
    refine Q'.eqv_trans _ _ _ (sinTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (sinTri A B n) _ (sinConv A B n) (sinTri_eqv_convSum A B n)

/-! ### 5f. The diagonal collapse (degree-shifted telescope via (TC))

`Σ_{m<n+1} cosConv m  +  (−ΣQ_{m<n} sinConv m)  ≃  cosPartial (A+B) (n+1)`.  The cos
diagonal sum runs ONE degree past the sin diagonal sum; each paired summand
`cosConv (m+1) − sinConv m` collapses to `cosTerm (A+B) (m+1)` by `cosConv_addition`,
and the unpaired `cosConv 0` collapses by `cosConv_addition_zero`.  This is the
exact `Q'`-level addition law at the *diagonal-sum* level — the trig analogue of
`triAdd_eqv_partialSum`, with the minus and the degree shift made explicit. -/

/-- **Diagonal collapse.**  `(Σ_{m<n+1} cosConv) + (−(Σ_{m<n} sinConv)) ≃
cosPartial (A+B) (n+1)`. -/
theorem cosSum_sub_sinSum_eqv_cosPartial (A B : Q') :
    ∀ n, (RationalTail.finSum (cosConv A B) (n + 1)
        + (-(RationalTail.finSum (sinConv A B) n))).eqv (cosPartial (A + B) (n + 1))
  | 0 => by
    -- (cosConv 0) + (−0) ≃ cosTerm (A+B) 0 = cosPartial (A+B) 1.
    show ((0 : Q') + cosConv A B 0 + (-(0 : Q'))).eqv ((0 : Q') + cosTerm (A + B) 0)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 (by show (-(0:Q')).eqv 0; decide)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' ((0:Q') + cosConv A B 0))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosConv A B 0))) ?_
    refine Q'.eqv_trans _ _ _ (cosConv_addition_zero A B) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (cosTerm (A + B) 0)))
  | n + 1 => by
    -- LHS = (Σcos (n+1) + cosConv(n+1)) + (−(Σsin n + sinConv n))
    --     ≃ [Σcos(n+1) + (−Σsin n)] + [cosConv(n+1) + (−sinConv n)]
    --     ≃ cosPartial(A+B)(n+1) + cosTerm(A+B)(n+1) = cosPartial(A+B)(n+2).
    show ((RationalTail.finSum (cosConv A B) (n + 1) + cosConv A B (n + 1))
        + (-(RationalTail.finSum (sinConv A B) n + sinConv A B n))).eqv
        (cosPartial (A + B) (n + 1) + cosTerm (A + B) (n + 1))
    -- expand the negation of the sin sum
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) n) (sinConv A B n))) ?_
    -- now: (Σcos(n+1) + cosConv(n+1)) + ((−Σsin n) + (−sinConv n))
    -- rearrange to [Σcos(n+1) + (−Σsin n)] + [cosConv(n+1) + (−sinConv n)]
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (RationalTail.finSum (cosConv A B) (n + 1)) (cosConv A B (n + 1))
        (-(RationalTail.finSum (sinConv A B) n)) (-(sinConv A B n))) ?_
    -- apply IH and (TC)
    refine Q'.add_eqv_congr' (cosSum_sub_sinSum_eqv_cosPartial A B n) ?_
    exact cosConv_addition A B n

/-! ### 5g. Trig rectangle/corner product decompositions (clean copies)

`cosPartial A n · cosPartial B n ≃ cosTri A B n + cosCorner A B n` (and sin), the
direct trig analogue of `prodAdd_eqv_tri_add_corner`.  Combined with §5e
(`cosTri ≃ Σ cosConv`) and §5f (diagonal collapse), the *only* remaining gap to the
CReal addition law is the vanishing of the corners and the trailing `sinConv`
mismatch term — the analytic (modulus) ingredient, named in the footer. -/

/-- `cosCornerTerm A B n i = cosTerm A i · (cosPartial B n − cosPartial B (n−i))`. -/
def cosCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * (cosPartial B n + -(cosPartial B (n - i)))

/-- `cosCorner A B n = Σ_{i<n} cosCornerTerm A B n i`. -/
def cosCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosCornerTerm A B n) n

/-- `sinCornerTerm A B n i = sinTerm A i · (sinPartial B n − sinPartial B (n−i))`. -/
def sinCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * (sinPartial B n + -(sinPartial B (n - i)))

/-- `sinCorner A B n = Σ_{i<n} sinCornerTerm A B n i`. -/
def sinCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinCornerTerm A B n) n

/-- **Cosine rectangle/corner decomposition.**  `cosPartial A n · cosPartial B n ≃
cosTri A B n + cosCorner A B n`. -/
theorem cosProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * cosPartial B n).eqv (cosTri A B n + cosCorner A B n) := by
  rw [cosPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (cosTerm A) (cosPartial B n) n) ?_
  have hterm : ∀ i, (cosTerm A i * cosPartial B n).eqv
      (cosTriTerm A B n i + cosCornerTerm A B n i) := by
    intro i
    show (cosTerm A i * cosPartial B n).eqv
        (cosTerm A i * cosPartial B (n - i)
          + cosTerm A i * (cosPartial B n + -(cosPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (cosTerm A i) (cosPartial B n)
        (cosPartial B (n - i) + (cosPartial B n + -(cosPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (cosPartial B n) (cosPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (cosTerm A i) (cosPartial B (n - i))
      (cosPartial B n + -(cosPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => cosTerm A i * cosPartial B n)
      (fun i => cosTriTerm A B n i + cosCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (cosTriTerm A B n) (cosCornerTerm A B n) n

/-- **Sine rectangle/corner decomposition.**  `sinPartial A n · sinPartial B n ≃
sinTri A B n + sinCorner A B n`. -/
theorem sinProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * sinPartial B n).eqv (sinTri A B n + sinCorner A B n) := by
  rw [sinPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (sinTerm A) (sinPartial B n) n) ?_
  have hterm : ∀ i, (sinTerm A i * sinPartial B n).eqv
      (sinTriTerm A B n i + sinCornerTerm A B n i) := by
    intro i
    show (sinTerm A i * sinPartial B n).eqv
        (sinTerm A i * sinPartial B (n - i)
          + sinTerm A i * (sinPartial B n + -(sinPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (sinTerm A i) (sinPartial B n)
        (sinPartial B (n - i) + (sinPartial B n + -(sinPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (sinPartial B n) (sinPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (sinTerm A i) (sinPartial B (n - i))
      (sinPartial B n + -(sinPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => sinTerm A i * sinPartial B n)
      (fun i => sinTriTerm A B n i + sinCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (sinTriTerm A B n) (sinCornerTerm A B n) n

/-- **Cosine rectangle decomposition, diagonal form.**  `cosPartial A n · cosPartial B n
≃ (Σ_{m<n} cosConv A B m) + cosCorner A B n`. -/
theorem cosProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * cosPartial B n).eqv
      (RationalTail.finSum (cosConv A B) n + cosCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (cosProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (cosTri A B n) _ (cosCorner A B n) (cosTri_eqv_convSum A B n)

/-- **Sine rectangle decomposition, diagonal form.**  `sinPartial A n · sinPartial B n
≃ (Σ_{m<n} sinConv A B m) + sinCorner A B n`. -/
theorem sinProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * sinPartial B n).eqv
      (RationalTail.finSum (sinConv A B) n + sinCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (sinProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (sinTri A B n) _ (sinCorner A B n) (sinTri_eqv_convSum A B n)

/-! ### 5h. The trig rectangle/corner addition identity (step 4, `Q'` level)

Assembling §5f (diagonal collapse) with §5g (rectangle decompositions) gives the
exact `Q'.eqv` identity, for `n = k+1`,

  cosPartial A n · cosPartial B n  −  sinPartial A n · sinPartial B n
      ≃  cosPartial (A+B) n  +  remCorner A B k ,

where `remCorner A B k := (cosCorner A B (k+1) − sinCorner A B (k+1)) − sinConv A B k`
collects the two product corners and the single trailing degree-`k` sin convolution
left over from the degree-shifted telescope.  The CReal addition law (step 5) is
exactly `remCorner → 0` past an explicit modulus (the analytic residual). -/

/-- The combined corner remainder of the trig rectangle decomposition at `n = k+1`. -/
def remCorner (A B : Q') (k : Nat) : Q' :=
  (cosCorner A B (k + 1) + (-(sinCorner A B (k + 1)))) + (-(sinConv A B k))

/-- **The trig rectangle/corner addition identity (`Q'` level).**  For `n = k+1`,
`cosPartial A n · cosPartial B n − sinPartial A n · sinPartial B n
≃ cosPartial (A+B) n + remCorner A B k`. -/
theorem cosSinProd_eqv_cosPartial_add_remCorner (A B : Q') (k : Nat) :
    (cosPartial A (k + 1) * cosPartial B (k + 1)
        + (-(sinPartial A (k + 1) * sinPartial B (k + 1)))).eqv
      (cosPartial (A + B) (k + 1) + remCorner A B k) := by
  -- substitute both rectangle decompositions
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (cosProd_eqv_convSum_add_corner A B (k + 1))
      (Q'.neg_eqv_congr _ _ (sinProd_eqv_convSum_add_corner A B (k + 1)))) ?_
  -- LHS now: (CS + CC) + (−(SS + SC)) with CS=Σcos(k+1), CC=cosCorner, SS=Σsin(k+1),
  -- SC=sinCorner.  Σsin(k+1) = Σsin k + sinConv k (defeq), so peel sinConv k:
  -- −SS ≃ (−Σsin k) + (−sinConv k).  Then a pure 5-term rearrangement lands
  -- [CS + (−Σsin k)] + [(CC + (−SC)) + (−sinConv k)] = [collapse] + remCorner.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) (k + 1)) (sinCorner A B (k + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ (-(sinCorner A B (k + 1)))
        (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) k) (sinConv A B k)))) ?_
  -- now: (CS + CC) + (((−Σsin k) + (−sinConv k)) + (−SC))
  refine Q'.eqv_trans _ _ _
    (add_rearrange_5 (RationalTail.finSum (cosConv A B) (k + 1)) (cosCorner A B (k + 1))
      (-(RationalTail.finSum (sinConv A B) k)) (-(sinConv A B k)) (-(sinCorner A B (k + 1)))) ?_
  -- goal: [CS + (−Σsin k)] + [(CC + (−SC)) + (−sinConv k)]
  --        ≃ cosPartial(A+B)(k+1) + remCorner A B k
  refine Q'.add_eqv_congr' (cosSum_sub_sinSum_eqv_cosPartial A B k) ?_
  -- (CC + (−SC)) + (−sinConv k) = remCorner A B k  (defeq).
  exact Q'.eqv_refl _

/-! ## 6. STEP A — `remCorner A B k → 0` past an explicit modulus

`remCorner A B k = (cosCorner A B (k+1) − sinCorner A B (k+1)) − sinConv A B k`.
We bound each piece for `A, B ≥ 0`:

  * the cos/sin product corners are dominated by a trig magnitude corner
    `cos/sinCornerAbs A B n`, which `→ 0` by a Mertens estimate copied from
    `CornerBound.cornerAbs_le` (weights `termAbs A (2i)` / `termAbs A (2i+1)`,
    blocks `cos/sinBlockAbs B (n−i) i`, both dominated by the exponential block
    via `cos/sinBlockAbs_le_blockAbs`);

  * the trailing single convolution `sinConv A B k = Σ_{i≤k} sinTerm A i·sinTerm B (k−i)`
    is dominated by the magnitude convolution `sinConvAbs A B k`, in which every
    term has total magnitude index `(2i+1)+(2(k−i)+1) = 2k+2`, so at least one
    factor has index `≥ k+1`; splitting at the midpoint gives a bound by two
    exponential blocks past the cutoff, hence `→ 0`.

The assembly `remCorner_le` is the genuinely-new analytic (modulus) piece. -/

/-! ### 6a. The trig magnitude corners and the `±corner ≤ cornerAbs` reduction -/

/-- `cosCornerAbsTerm A B n i = termAbs A (2i)·cosBlockAbs B (n−i) i`. -/
def cosCornerAbsTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs A (2 * i) * cosBlockAbs B (n - i) i

/-- `cosCornerAbs A B n = Σ_{i<n} termAbs A (2i)·cosBlockAbs B (n−i) i`. -/
def cosCornerAbs (A B : Q') (n : Nat) : Q' :=
  RationalTail.finSum (cosCornerAbsTerm A B n) n

/-- `sinCornerAbsTerm A B n i = termAbs A (2i+1)·sinBlockAbs B (n−i) i`. -/
def sinCornerAbsTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs A (2 * i + 1) * sinBlockAbs B (n - i) i

/-- `sinCornerAbs A B n = Σ_{i<n} termAbs A (2i+1)·sinBlockAbs B (n−i) i`. -/
def sinCornerAbs (A B : Q') (n : Nat) : Q' :=
  RationalTail.finSum (sinCornerAbsTerm A B n) n

/-- Termwise: `±cosCornerTerm ≤ cosCornerAbsTerm`, for `i < n` (with `A, B ≥ 0`). -/
theorem cosCornerTerm_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n i : Nat) (hi : i < n) :
    cosCornerTerm A B n i ≤ cosCornerAbsTerm A B n i
      ∧ -(cosCornerTerm A B n i) ≤ cosCornerAbsTerm A B n i := by
  have hni : (n - i) + i = n := by omega
  have hBnn : (0 : Q') ≤ termAbs A (2 * i) := termAbs_nonneg A hA (2 * i)
  have hdnn : (0 : Q') ≤ cosBlockAbs B (n - i) i := cosBlockAbs_nonneg B hB (n - i) i
  -- weight bounds: -termAbs A (2i) ≤ cosTerm A i ≤ termAbs A (2i)
  obtain ⟨hu2, hu1⟩ := cosTerm_two_sided A hA i
  -- diff bounds: -cosBlockAbs ≤ (cosPartial B n − cosPartial B (n−i)) ≤ cosBlockAbs
  have hv2 : cosPartial B n + -(cosPartial B (n - i)) ≤ cosBlockAbs B (n - i) i := by
    have h := cos_block_upper B hB (n - i) i
    rw [hni] at h
    exact Q'.sub_le_of_le_add h
  have hv1 : -(cosBlockAbs B (n - i) i) ≤ cosPartial B n + -(cosPartial B (n - i)) := by
    have hbl := cos_block_lower B hB (n - i) i
    rw [hni] at hbl
    have h2 : cosPartial B (n - i) + -(cosPartial B n) ≤ cosBlockAbs B (n - i) i :=
      Q'.sub_le_of_le_add hbl
    have hnv : -(cosPartial B n + -(cosPartial B (n - i))) ≤ cosBlockAbs B (n - i) i := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h2
      exact Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (cosPartial B n) (-(cosPartial B (n - i))))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (-(cosPartial B n)) (-(-(cosPartial B (n - i))))
            (cosPartial B (n - i)) (Q'.neg_neg_eqv (cosPartial B (n - i))))
          (Q'.add_comm_eqv (-(cosPartial B n)) (cosPartial B (n - i))))
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hnv) (Q'.le_of_eqv ?_)
    exact Q'.neg_neg_eqv (cosPartial B n + -(cosPartial B (n - i)))
  refine ⟨?_, ?_⟩
  · exact Q'.mul_le_of_bounds hBnn hdnn hu1 hu2 hv1 hv2
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_mul_eqv _ _))) ?_
    have hnu1 : -(termAbs A (2 * i)) ≤ -(cosTerm A i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2); exact Q'.le_refl' _
    have hnu2 : -(cosTerm A i) ≤ termAbs A (2 * i) := by
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv ?_)
      exact Q'.neg_neg_eqv (termAbs A (2 * i))
    exact Q'.mul_le_of_bounds hBnn hdnn hnu1 hnu2 hv1 hv2

/-- Termwise: `±sinCornerTerm ≤ sinCornerAbsTerm`, for `i < n` (with `A, B ≥ 0`). -/
theorem sinCornerTerm_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n i : Nat) (hi : i < n) :
    sinCornerTerm A B n i ≤ sinCornerAbsTerm A B n i
      ∧ -(sinCornerTerm A B n i) ≤ sinCornerAbsTerm A B n i := by
  have hni : (n - i) + i = n := by omega
  have hBnn : (0 : Q') ≤ termAbs A (2 * i + 1) := termAbs_nonneg A hA (2 * i + 1)
  have hdnn : (0 : Q') ≤ sinBlockAbs B (n - i) i := sinBlockAbs_nonneg B hB (n - i) i
  obtain ⟨hu2, hu1⟩ := sinTerm_two_sided A hA i
  have hv2 : sinPartial B n + -(sinPartial B (n - i)) ≤ sinBlockAbs B (n - i) i := by
    have h := sin_block_upper B hB (n - i) i
    rw [hni] at h
    exact Q'.sub_le_of_le_add h
  have hv1 : -(sinBlockAbs B (n - i) i) ≤ sinPartial B n + -(sinPartial B (n - i)) := by
    have hbl := sin_block_lower B hB (n - i) i
    rw [hni] at hbl
    have h2 : sinPartial B (n - i) + -(sinPartial B n) ≤ sinBlockAbs B (n - i) i :=
      Q'.sub_le_of_le_add hbl
    have hnv : -(sinPartial B n + -(sinPartial B (n - i))) ≤ sinBlockAbs B (n - i) i := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h2
      exact Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (sinPartial B n) (-(sinPartial B (n - i))))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (-(sinPartial B n)) (-(-(sinPartial B (n - i))))
            (sinPartial B (n - i)) (Q'.neg_neg_eqv (sinPartial B (n - i))))
          (Q'.add_comm_eqv (-(sinPartial B n)) (sinPartial B (n - i))))
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hnv) (Q'.le_of_eqv ?_)
    exact Q'.neg_neg_eqv (sinPartial B n + -(sinPartial B (n - i)))
  refine ⟨?_, ?_⟩
  · exact Q'.mul_le_of_bounds hBnn hdnn hu1 hu2 hv1 hv2
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_mul_eqv _ _))) ?_
    have hnu1 : -(termAbs A (2 * i + 1)) ≤ -(sinTerm A i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2); exact Q'.le_refl' _
    have hnu2 : -(sinTerm A i) ≤ termAbs A (2 * i + 1) := by
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv ?_)
      exact Q'.neg_neg_eqv (termAbs A (2 * i + 1))
    exact Q'.mul_le_of_bounds hBnn hdnn hnu1 hnu2 hv1 hv2

/-- `±cosCorner ≤ cosCornerAbs`. -/
theorem cosCorner_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) (n : Nat) :
    cosCorner A B n ≤ cosCornerAbs A B n
      ∧ -(cosCorner A B n) ≤ cosCornerAbs A B n := by
  refine ⟨finSum_le_lt (cosCornerTerm A B n) (cosCornerAbsTerm A B n) n
      (fun i hi => (cosCornerTerm_abs_le A B hA hB n i hi).1), ?_⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (cosCornerTerm A B n) n)) ?_
  exact finSum_le_lt (fun i => -(cosCornerTerm A B n i)) (cosCornerAbsTerm A B n) n
    (fun i hi => (cosCornerTerm_abs_le A B hA hB n i hi).2)

/-- `±sinCorner ≤ sinCornerAbs`. -/
theorem sinCorner_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) (n : Nat) :
    sinCorner A B n ≤ sinCornerAbs A B n
      ∧ -(sinCorner A B n) ≤ sinCornerAbs A B n := by
  refine ⟨finSum_le_lt (sinCornerTerm A B n) (sinCornerAbsTerm A B n) n
      (fun i hi => (sinCornerTerm_abs_le A B hA hB n i hi).1), ?_⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (sinCornerTerm A B n) n)) ?_
  exact finSum_le_lt (fun i => -(sinCornerTerm A B n i)) (sinCornerAbsTerm A B n) n
    (fun i hi => (sinCornerTerm_abs_le A B hA hB n i hi).2)

/-! ### 6b. The Mertens bound on the trig magnitude corners

`cos/sinCornerAbs A B n → 0` past an explicit modulus, copied from
`CornerBound.cornerAbs_le`: split at `K`; for `i < K` the `B`-block starts past
the `B`-cutoff (`cos/sinBlock_bound`), summing the `A`-weights to a global bound
`Ba`; for `K ≤ i` the `A`-weights sum to the `A`-tail `cos/sinBlockAbs A K d ≤ δ`
and the `B`-blocks are `≤ Bb`. -/

/-- The even-index magnitude sub-sum is the `cosBlockAbs … 0` block (eqv). -/
theorem evenTermSum_eqv_cosBlock (A : Q') :
    ∀ m, (RationalTail.finSum (fun i => termAbs A (2 * i)) m).eqv (cosBlockAbs A 0 m)
  | 0 => Q'.eqv_refl 0
  | m + 1 => by
    show (RationalTail.finSum (fun i => termAbs A (2 * i)) m + termAbs A (2 * m)).eqv
        (cosBlockAbs A 0 m + termAbs A (2 * (0 + m)))
    have hidx : 2 * (0 + m) = 2 * m := by omega
    rw [hidx]
    exact Q'.add_eqv_congr_right _ _ (termAbs A (2 * m)) (evenTermSum_eqv_cosBlock A m)

/-- The odd-index magnitude sub-sum is the `sinBlockAbs … 0` block (eqv). -/
theorem oddTermSum_eqv_sinBlock (A : Q') :
    ∀ m, (RationalTail.finSum (fun i => termAbs A (2 * i + 1)) m).eqv (sinBlockAbs A 0 m)
  | 0 => Q'.eqv_refl 0
  | m + 1 => by
    show (RationalTail.finSum (fun i => termAbs A (2 * i + 1)) m + termAbs A (2 * m + 1)).eqv
        (sinBlockAbs A 0 m + termAbs A (2 * (0 + m) + 1))
    have hidx : 2 * (0 + m) + 1 = 2 * m + 1 := by omega
    rw [hidx]
    exact Q'.add_eqv_congr_right _ _ (termAbs A (2 * m + 1)) (oddTermSum_eqv_sinBlock A m)

/-- `cosBlockAbs A K e = Σ_{j<e} termAbs A (2(K+j))` (eqv). -/
theorem cosBlockAbs_eqv_finSum (A : Q') (K : Nat) :
    ∀ e, (cosBlockAbs A K e).eqv (RationalTail.finSum (fun j => termAbs A (2 * (K + j))) e)
  | 0 => Q'.eqv_refl 0
  | e + 1 => by
    show (cosBlockAbs A K e + termAbs A (2 * (K + e))).eqv
        (RationalTail.finSum (fun j => termAbs A (2 * (K + j))) e + termAbs A (2 * (K + e)))
    exact Q'.add_eqv_congr_right _ _ (termAbs A (2 * (K + e))) (cosBlockAbs_eqv_finSum A K e)

/-- `sinBlockAbs A K e = Σ_{j<e} termAbs A (2(K+j)+1)` (eqv). -/
theorem sinBlockAbs_eqv_finSum (A : Q') (K : Nat) :
    ∀ e, (sinBlockAbs A K e).eqv (RationalTail.finSum (fun j => termAbs A (2 * (K + j) + 1)) e)
  | 0 => Q'.eqv_refl 0
  | e + 1 => by
    show (sinBlockAbs A K e + termAbs A (2 * (K + e) + 1)).eqv
        (RationalTail.finSum (fun j => termAbs A (2 * (K + j) + 1)) e + termAbs A (2 * (K + e) + 1))
    exact Q'.add_eqv_congr_right _ _ (termAbs A (2 * (K + e) + 1)) (sinBlockAbs_eqv_finSum A K e)

/-- **`cosCornerAbs A B n → 0`.**  For `A, B ≥ 0` and `ε > 0`, every `n` past an
explicit modulus has `cosCornerAbs A B n ≤ ε`. -/
theorem cosCornerAbs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → cosCornerAbs A B n ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound A hA
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound B hB
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  obtain ⟨K, hKdef⟩ : ∃ K, K = Trig.trigModulus A δ := ⟨_, rfl⟩
  have hKmodA : Trig.trigModulus A δ ≤ K := Nat.le_of_eq hKdef.symm
  refine ⟨K + Trig.trigModulus B δ, fun n hn => ?_⟩
  have hKn : K ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKn
  have hsplit : (cosCornerAbs A B (K + d)).eqv
      (RationalTail.finSum (cosCornerAbsTerm A B (K + d)) K
        + RationalTail.finSum (fun j => cosCornerAbsTerm A B (K + d) (K + j)) d) :=
    finSum_split (cosCornerAbsTerm A B (K + d)) K d
  have hpart1 : RationalTail.finSum (cosCornerAbsTerm A B (K + d)) K ≤ Ba * δ := by
    have hterm1 : ∀ i, i < K → cosCornerAbsTerm A B (K + d) i ≤ termAbs A (2 * i) * δ := by
      intro i hiK
      have hblock : cosBlockAbs B ((K + d) - i) i ≤ δ := by
        have hmodi : Trig.trigModulus B δ ≤ (K + d) - i := by omega
        exact Trig.cosBlock_bound B hB δ hδpos ((K + d) - i) hmodi i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * i)) hblock
        (termAbs_nonneg A hA (2 * i))
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (cosCornerAbsTerm A B (K + d)) (fun i => termAbs A (2 * i) * δ) K hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const (fun i => termAbs A (2 * i)) δ K))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ Ba δ ?_ hδnn
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (evenTermSum_eqv_cosBlock A K)) ?_
    refine Q'.le_trans' _ _ _ (Trig.cosBlockAbs_le_blockAbs A hA 0 K) ?_
    exact blockAbs_le_bound A hA hBa 0 (2 * K)
  have hpart2 : RationalTail.finSum (fun j => cosCornerAbsTerm A B (K + d) (K + j)) d ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => cosCornerAbsTerm A B (K + d) (K + j)) j
        ≤ termAbs A (2 * (K + j)) * Bb := by
      intro j
      show termAbs A (2 * (K + j)) * cosBlockAbs B ((K + d) - (K + j)) (K + j)
          ≤ termAbs A (2 * (K + j)) * Bb
      refine Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * (K + j))) ?_
        (termAbs_nonneg A hA (2 * (K + j)))
      refine Q'.le_trans' _ _ _ (Trig.cosBlockAbs_le_blockAbs B hB ((K + d) - (K + j)) (K + j)) ?_
      exact blockAbs_le_bound B hB hBb _ _
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => cosCornerAbsTerm A B (K + d) (K + j))
        (fun j => termAbs A (2 * (K + j)) * Bb) hterm2 d) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const
        (fun j => termAbs A (2 * (K + j))) Bb d))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ δ Bb ?_ hBb0
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (cosBlockAbs_eqv_finSum A K d)))
      (Trig.cosBlock_bound A hA δ hδpos K hKmodA d)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hδ
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Ba * δ) (δ * Bb) (Bb * δ) (Q'.mul_comm_eqv δ Bb)) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv Ba Bb δ)

/-- **`sinCornerAbs A B n → 0`.**  For `A, B ≥ 0` and `ε > 0`, every `n` past an
explicit modulus has `sinCornerAbs A B n ≤ ε`. -/
theorem sinCornerAbs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → sinCornerAbs A B n ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound A hA
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound B hB
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  obtain ⟨K, hKdef⟩ : ∃ K, K = Trig.trigModulus A δ := ⟨_, rfl⟩
  have hKmodA : Trig.trigModulus A δ ≤ K := Nat.le_of_eq hKdef.symm
  refine ⟨K + Trig.trigModulus B δ, fun n hn => ?_⟩
  have hKn : K ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKn
  have hsplit : (sinCornerAbs A B (K + d)).eqv
      (RationalTail.finSum (sinCornerAbsTerm A B (K + d)) K
        + RationalTail.finSum (fun j => sinCornerAbsTerm A B (K + d) (K + j)) d) :=
    finSum_split (sinCornerAbsTerm A B (K + d)) K d
  have hpart1 : RationalTail.finSum (sinCornerAbsTerm A B (K + d)) K ≤ Ba * δ := by
    have hterm1 : ∀ i, i < K → sinCornerAbsTerm A B (K + d) i ≤ termAbs A (2 * i + 1) * δ := by
      intro i hiK
      have hblock : sinBlockAbs B ((K + d) - i) i ≤ δ := by
        have hmodi : Trig.trigModulus B δ ≤ (K + d) - i := by omega
        exact Trig.sinBlock_bound B hB δ hδpos ((K + d) - i) hmodi i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * i + 1)) hblock
        (termAbs_nonneg A hA (2 * i + 1))
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (sinCornerAbsTerm A B (K + d)) (fun i => termAbs A (2 * i + 1) * δ) K hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const (fun i => termAbs A (2 * i + 1)) δ K))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ Ba δ ?_ hδnn
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (oddTermSum_eqv_sinBlock A K)) ?_
    refine Q'.le_trans' _ _ _ (Trig.sinBlockAbs_le_blockAbs A hA 0 K) ?_
    exact blockAbs_le_bound A hA hBa (2 * 0 + 1) (2 * K)
  have hpart2 : RationalTail.finSum (fun j => sinCornerAbsTerm A B (K + d) (K + j)) d ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => sinCornerAbsTerm A B (K + d) (K + j)) j
        ≤ termAbs A (2 * (K + j) + 1) * Bb := by
      intro j
      show termAbs A (2 * (K + j) + 1) * sinBlockAbs B ((K + d) - (K + j)) (K + j)
          ≤ termAbs A (2 * (K + j) + 1) * Bb
      refine Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * (K + j) + 1)) ?_
        (termAbs_nonneg A hA (2 * (K + j) + 1))
      refine Q'.le_trans' _ _ _ (Trig.sinBlockAbs_le_blockAbs B hB ((K + d) - (K + j)) (K + j)) ?_
      exact blockAbs_le_bound B hB hBb _ _
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => sinCornerAbsTerm A B (K + d) (K + j))
        (fun j => termAbs A (2 * (K + j) + 1) * Bb) hterm2 d) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const
        (fun j => termAbs A (2 * (K + j) + 1)) Bb d))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ δ Bb ?_ hBb0
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sinBlockAbs_eqv_finSum A K d)))
      (Trig.sinBlock_bound A hA δ hδpos K hKmodA d)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hδ
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Ba * δ) (δ * Bb) (Bb * δ) (Q'.mul_comm_eqv δ Bb)) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv Ba Bb δ)

/-! ### 6c. The trailing convolution `sinConv A B k → 0`

`sinConv A B k = Σ_{i≤k} sinTerm A i·sinTerm B (k−i)` is dominated by the
magnitude convolution `sinConvAbs A B k = Σ_{i≤k} termAbs A (2i+1)·termAbs B (2(k−i)+1)`,
in which every term has total magnitude index `(2i+1)+(2(k−i)+1) = 2k+2`.  Splitting
the sum at `h = (k+1)/2`: for `i < h` the `B`-factor's index `2(k−i)+1 ≥ k+1` is past
the `B`-cutoff (single-term `termAbs_le_of_modulus_le`), and the `A`-weights sum to
`≤ Ba`; for `i ≥ h` the `A`-index `2i+1 ≥ k+1` and the `A`-weights form the odd
`A`-tail block `sinBlockAbs A h _ ≤ δ`, the `B`-factors `≤ Bb`. -/

/-- `termAbs A m ≤ partialSumAbs A (m+1)` (a single term ≤ its partial sum). -/
theorem termAbs_le_psAbs_succ (A : Q') (hA : (0 : Q') ≤ A) (m : Nat) :
    termAbs A m ≤ partialSumAbs A (m + 1) := by
  show termAbs A m ≤ partialSumAbs A m + termAbs A m
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (termAbs A m)).symm)) ?_
  exact Q'.add_le_add_right 0 (partialSumAbs A m) (termAbs A m) (psAbs_nonneg A hA m)

/-- Global term bound: `termAbs A m ≤ B` whenever `B` bounds every `partialSumAbs A`. -/
theorem termAbs_le_bound (A : Q') (hA : (0 : Q') ≤ A) {B : Q'}
    (hB : ∀ n, partialSumAbs A n ≤ B) (m : Nat) : termAbs A m ≤ B :=
  Q'.le_trans' _ _ _ (termAbs_le_psAbs_succ A hA m) (hB (m + 1))

/-- `sinConvAbsTerm A B k i = termAbs A (2i+1)·termAbs B (2(k−i)+1)`. -/
def sinConvAbsTerm (A B : Q') (k : Nat) : Nat → Q' :=
  fun i => termAbs A (2 * i + 1) * termAbs B (2 * (k - i) + 1)

/-- `sinConvAbs A B k = Σ_{i≤k} termAbs A (2i+1)·termAbs B (2(k−i)+1)`. -/
def sinConvAbs (A B : Q') (k : Nat) : Q' :=
  RationalTail.finSum (sinConvAbsTerm A B k) (k + 1)

/-- Termwise `±sinConvTerm ≤ sinConvAbsTerm`, for any `i`. -/
theorem sinConvTerm_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (k i : Nat) :
    sinConvTerm A B k i ≤ sinConvAbsTerm A B k i
      ∧ -(sinConvTerm A B k i) ≤ sinConvAbsTerm A B k i := by
  have hAnn : (0 : Q') ≤ termAbs A (2 * i + 1) := termAbs_nonneg A hA (2 * i + 1)
  have hBnn : (0 : Q') ≤ termAbs B (2 * (k - i) + 1) := termAbs_nonneg B hB (2 * (k - i) + 1)
  obtain ⟨hu2, hu1⟩ := sinTerm_two_sided A hA i
  obtain ⟨hv2, hv1⟩ := sinTerm_two_sided B hB (k - i)
  refine ⟨?_, ?_⟩
  · exact Q'.mul_le_of_bounds hAnn hBnn hu1 hu2 hv1 hv2
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_mul_eqv _ _))) ?_
    have hnu1 : -(termAbs A (2 * i + 1)) ≤ -(sinTerm A i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2); exact Q'.le_refl' _
    have hnu2 : -(sinTerm A i) ≤ termAbs A (2 * i + 1) := by
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv ?_)
      exact Q'.neg_neg_eqv (termAbs A (2 * i + 1))
    exact Q'.mul_le_of_bounds hAnn hBnn hnu1 hnu2 hv1 hv2

/-- `±sinConv ≤ sinConvAbs`. -/
theorem sinConv_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) (k : Nat) :
    sinConv A B k ≤ sinConvAbs A B k ∧ -(sinConv A B k) ≤ sinConvAbs A B k := by
  refine ⟨finSum_le_lt (sinConvTerm A B k) (sinConvAbsTerm A B k) (k + 1)
      (fun i _ => (sinConvTerm_abs_le A B hA hB k i).1), ?_⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (sinConvTerm A B k) (k + 1))) ?_
  exact finSum_le_lt (fun i => -(sinConvTerm A B k i)) (sinConvAbsTerm A B k) (k + 1)
    (fun i _ => (sinConvTerm_abs_le A B hA hB k i).2)

/-- **`sinConvAbs A B k → 0`.**  For `A, B ≥ 0` and `ε > 0`, every `k` past an
explicit modulus has `sinConvAbs A B k ≤ ε`. -/
theorem sinConvAbs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ k : Nat, N ≤ k → sinConvAbs A B k ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound A hA
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound B hB
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  refine ⟨2 * Trig.trigModulus A δ + termAbsModulus B δ, fun k hk => ?_⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = (k + 1) / 2 := ⟨_, rfl⟩
  have hhmodA : Trig.trigModulus A δ ≤ h := by omega
  obtain ⟨e, hek⟩ : ∃ e, k + 1 = h + e := ⟨(k + 1) - h, by omega⟩
  have hsplit : (sinConvAbs A B k).eqv
      (RationalTail.finSum (sinConvAbsTerm A B k) h
        + RationalTail.finSum (fun j => sinConvAbsTerm A B k (h + j)) e) := by
    show (RationalTail.finSum (sinConvAbsTerm A B k) (k + 1)).eqv _
    rw [hek]
    exact finSum_split (sinConvAbsTerm A B k) h e
  -- Part 1 ≤ Ba·δ
  have hpart1 : RationalTail.finSum (sinConvAbsTerm A B k) h ≤ Ba * δ := by
    have hterm1 : ∀ i, i < h → sinConvAbsTerm A B k i ≤ termAbs A (2 * i + 1) * δ := by
      intro i hih
      have hBfac : termAbs B (2 * (k - i) + 1) ≤ δ := by
        have hidx : termAbsModulus B δ ≤ 2 * (k - i) + 1 := by omega
        exact termAbs_le_of_modulus_le B δ hB hδpos (2 * (k - i) + 1) hidx
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * i + 1)) hBfac
        (termAbs_nonneg A hA (2 * i + 1))
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (sinConvAbsTerm A B k) (fun i => termAbs A (2 * i + 1) * δ) h hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const (fun i => termAbs A (2 * i + 1)) δ h))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ Ba δ ?_ hδnn
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (oddTermSum_eqv_sinBlock A h)) ?_
    refine Q'.le_trans' _ _ _ (Trig.sinBlockAbs_le_blockAbs A hA 0 h) ?_
    exact blockAbs_le_bound A hA hBa (2 * 0 + 1) (2 * h)
  -- Part 2 ≤ δ·Bb
  have hpart2 : RationalTail.finSum (fun j => sinConvAbsTerm A B k (h + j)) e ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => sinConvAbsTerm A B k (h + j)) j ≤ termAbs A (2 * (h + j) + 1) * Bb := by
      intro j
      show termAbs A (2 * (h + j) + 1) * termAbs B (2 * (k - (h + j)) + 1)
          ≤ termAbs A (2 * (h + j) + 1) * Bb
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * (h + j) + 1))
        (termAbs_le_bound B hB hBb (2 * (k - (h + j)) + 1)) (termAbs_nonneg A hA (2 * (h + j) + 1))
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => sinConvAbsTerm A B k (h + j))
        (fun j => termAbs A (2 * (h + j) + 1) * Bb) hterm2 e) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const
        (fun j => termAbs A (2 * (h + j) + 1)) Bb e))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ δ Bb ?_ hBb0
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (sinBlockAbs_eqv_finSum A h e)))
      (Trig.sinBlock_bound A hA δ hδpos h hhmodA e)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hδ
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Ba * δ) (δ * Bb) (Bb * δ) (Q'.mul_comm_eqv δ Bb)) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv Ba Bb δ)

/-! ### 6d. STEP A — assembling `|remCorner A B k| ≤ ε` past an explicit modulus -/

/-- **STEP A: `remCorner A B k → 0`.**  For `A, B ≥ 0` and `ε > 0`, every `k` past
an explicit (max of three) modulus has both `remCorner A B k ≤ ε` and
`−(remCorner A B k) ≤ ε`.  The trig analogue of `cornerAbsAdd_le`: the two product
corners are dominated by `cos/sinCornerAbs` (→0) and the trailing convolution by
`sinConvAbs` (→0); split `ε` into thirds. -/
theorem remCorner_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ k : Nat, N ≤ k →
      remCorner A B k ≤ ε ∧ -(remCorner A B k) ≤ ε := by
  obtain ⟨t, htpos, ht⟩ := CReal.exists_mul_le (by decide : (0 : Q') ≤ (3 : Q')) hε
  have ht3 : t + t + t ≤ ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) ht
    show (t + t + t).eqv (3 * t)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (3 : Q') ((1 : Q') + 1 + 1) t (by decide)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv ((1 : Q') + 1) 1 t) ?_
    refine Q'.add_eqv_congr' ?_ (Q'.one_mul_eqv t)
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') 1 t) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv t) (Q'.one_mul_eqv t)
  obtain ⟨Nc, hNc⟩ := cosCornerAbs_le A B hA hB t htpos
  obtain ⟨Ns, hNs⟩ := sinCornerAbs_le A B hA hB t htpos
  obtain ⟨Nv, hNv⟩ := sinConvAbs_le A B hA hB t htpos
  refine ⟨max (max Nc Ns) Nv, fun k hk => ?_⟩
  have hkNc : Nc ≤ k + 1 := by
    have : Nc ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
    omega
  have hkNs : Ns ≤ k + 1 := by
    have : Ns ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
    omega
  have hkNv : Nv ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hcc : cosCornerAbs A B (k + 1) ≤ t := hNc (k + 1) hkNc
  have hsc : sinCornerAbs A B (k + 1) ≤ t := hNs (k + 1) hkNs
  have hsv : sinConvAbs A B k ≤ t := hNv k hkNv
  obtain ⟨hcc1, hcc2⟩ := cosCorner_abs_le A B hA hB (k + 1)
  obtain ⟨hsc1, hsc2⟩ := sinCorner_abs_le A B hA hB (k + 1)
  obtain ⟨hsv1, hsv2⟩ := sinConv_abs_le A B hA hB k
  have hup : remCorner A B k ≤ t + t + t := by
    show (cosCorner A B (k + 1) + -(sinCorner A B (k + 1))) + -(sinConv A B k) ≤ t + t + t
    refine Q'.add_le_add (Q'.add_le_add (Q'.le_trans' _ _ _ hcc1 hcc)
      (Q'.le_trans' _ _ _ hsc2 hsc)) (Q'.le_trans' _ _ _ hsv2 hsv)
  have hlo : -(remCorner A B k) ≤ t + t + t := by
    show -((cosCorner A B (k + 1) + -(sinCorner A B (k + 1))) + -(sinConv A B k)) ≤ t + t + t
    have heqv : (-((cosCorner A B (k + 1) + -(sinCorner A B (k + 1))) + -(sinConv A B k))).eqv
        ((-(cosCorner A B (k + 1)) + -(-(sinCorner A B (k + 1)))) + -(-(sinConv A B k))) :=
      Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (cosCorner A B (k + 1) + -(sinCorner A B (k + 1))) (-(sinConv A B k)))
        (Q'.add_eqv_congr_right _ _ (-(-(sinConv A B k)))
          (Q'.neg_add_eqv (cosCorner A B (k + 1)) (-(sinCorner A B (k + 1)))))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
    refine Q'.add_le_add (Q'.add_le_add (Q'.le_trans' _ _ _ hcc2 hcc) ?_) ?_
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_neg_eqv (sinCorner A B (k + 1)))) ?_
      exact Q'.le_trans' _ _ _ hsc1 hsc
    · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_neg_eqv (sinConv A B k))) ?_
      exact Q'.le_trans' _ _ _ hsv1 hsv
  exact ⟨Q'.le_trans' _ _ _ hup ht3, Q'.le_trans' _ _ _ hlo ht3⟩

/-! ## 7. STEP B — the CReal addition law `cos(A+B) ≃ cos A·cos B − sin A·sin B`

We transfer the `Q'`-level rectangle identity `cosSinProd_eqv_cosPartial_add_remCorner`
to a `CReal.Equiv`, using the Step-A modulus `remCorner_le`, mirroring
`ExpAdd.expNeg_add_equiv`.  The right-hand combination is
`cosProdMinus A B := cosFull A · cosFull B − sinFull A · sinFull B` as a `CReal`. -/

/-- The right-hand side of the trig addition law as a `CReal`:
`cosFull A · cosFull B + (−(sinFull A · sinFull B))`. -/
def cosProdMinus (A B : Q') : CReal :=
  CReal.add (CReal.mul (cosFull A) (cosFull B))
    (CReal.neg (CReal.mul (sinFull A) (sinFull B)))

/-- `Q'.abs A = A` for `A ≥ 0`. -/
theorem abs_of_nonneg {A : Q'} (hA : (0 : Q') ≤ A) : Q'.abs A = A := by
  unfold Q'.abs; rw [if_pos hA]

/-- For `A, B ≥ 0`, the RHS approximation is the magnitude product expression. -/
theorem cosProdMinus_approx_nonneg (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n : Nat) :
    (cosProdMinus A B).approx n
      = cosPartial A n * cosPartial B n + -(sinPartial A n * sinPartial B n) := by
  have hsA : sinFull A = sinNN (Q'.abs A) (Q'.abs_nonneg A) := sinFull_of_nonneg hA
  have hsB : sinFull B = sinNN (Q'.abs B) (Q'.abs_nonneg B) := sinFull_of_nonneg hB
  show (cosFull A).approx n * (cosFull B).approx n
      + -((sinFull A).approx n * (sinFull B).approx n) = _
  rw [hsA, hsB]
  show cosPartial (Q'.abs A) n * cosPartial (Q'.abs B) n
      + -(sinPartial (Q'.abs A) n * sinPartial (Q'.abs B) n) = _
  rw [abs_of_nonneg hA, abs_of_nonneg hB]

/-- **STEP B (nonnegative core).**  For `A, B ≥ 0`,
`CReal.Equiv (cosFull (A+B)) (cosProdMinus A B)`. -/
theorem cos_add_equiv_nonneg (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) :
    CReal.Equiv (cosFull (A + B)) (cosProdMinus A B) := by
  intro ε hε
  obtain ⟨N, hN⟩ := remCorner_le A B hA hB ε hε
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hkN : N ≤ k := by omega
  obtain ⟨hrem1, hrem2⟩ := hN k hkN
  have hABabs : Q'.abs (A + B) = A + B := abs_of_nonneg (Q'.zero_le_add A B hA hB)
  have hid := cosSinProd_eqv_cosPartial_add_remCorner A B k
  show (cosFull (A + B)).approx (k + 1) ≤ (cosProdMinus A B).approx (k + 1) + ε
      ∧ (cosProdMinus A B).approx (k + 1) ≤ (cosFull (A + B)).approx (k + 1) + ε
  rw [cosFull_approx, cosProdMinus_approx_nonneg A B hA hB, hABabs]
  -- Abbreviations for the product expression `P` and the sum-partial `C`.
  have hCeqv : (cosPartial (A + B) (k + 1)).eqv
      ((cosPartial A (k + 1) * cosPartial B (k + 1)
          + -(sinPartial A (k + 1) * sinPartial B (k + 1))) + -(remCorner A B k)) := by
    have e1 : ((cosPartial A (k + 1) * cosPartial B (k + 1)
            + -(sinPartial A (k + 1) * sinPartial B (k + 1))) + -(remCorner A B k)).eqv
        ((cosPartial (A + B) (k + 1) + remCorner A B k) + -(remCorner A B k)) :=
      Q'.add_eqv_congr_right _ _ (-(remCorner A B k)) hid
    have e2 : ((cosPartial (A + B) (k + 1) + remCorner A B k) + -(remCorner A B k)).eqv
        (cosPartial (A + B) (k + 1)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (cosPartial (A + B) (k + 1)) (remCorner A B k) (-(remCorner A B k))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (cosPartial (A + B) (k + 1)) _ 0
          (Q'.add_neg_self_eqv (remCorner A B k))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (cosPartial (A + B) (k + 1)))
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2)
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hCeqv) ?_
    exact Q'.add_le_add_left _ (-(remCorner A B k)) ε hrem2
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
    exact Q'.add_le_add_left (cosPartial (A + B) (k + 1)) (remCorner A B k) ε hrem1

end TrigAdd

end ConstructiveReals

/-! ## The precise residual (the addition-formula core, honestly named)

What is CLOSED here and discharges `TrigBound`:

  * The `|cA| ≤ 1`/`|sA| ≤ 1` and small-angle budget hypothesis FAMILIES of
    `TrigBound.cos_second_diff_abs_le` are stated over abstract `Q'` data with the
    budgets `Bc`, `Bs` as parameters; `cos_small_angle`/`sin_small_angle` here
    supply the budgets for the actual `cosPartial`/`sinPartial` truncations (the
    `Q'` values a constructive cos/sin delivers), with `Bc = 2·termAbs x 2 = x²`,
    `Bs = 2·termAbs x 3 = x³/3`.  (The block machinery yields these honest
    constants; the sharp `x²/2` would need an alternating-cancellation refinement
    of the magnitude-sum block bound, not landed here.)

Now CLOSED (the addition-formula core, all `Q'.eqv`, no convergence theory):

  * EVEN/ODD REASSEMBLY (`finSum_even_odd_split`): the deinterleave
    `finSum f (2m+1) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)`, by induction on `m`.

  * THE PER-DEGREE ADDITION IDENTITY `(TC)` (`cosConv_addition`):
        cosConv A B (m+1)  +  (−(sinConv A B m))  ≃  cosTerm (A+B) (m+1) ,
    via the §5a `negPow` sign algebra (`(−1)^{m+1}·(−1)^m = −1` is the MINUS), the
    §4 magnitude bridge, and `ExpAddConv.convAdd_eqv_term`.  The even sub-sum
    reassembles `cosConv` with sign `(−1)^{m+1}`, the odd sub-sum `sinConv` with
    sign `(−1)^m`.  Base case: `cosConv_addition_zero` (`m = 0`).

  * THE DIAGONAL COLLAPSE (`cosSum_sub_sinSum_eqv_cosPartial`):
        (Σ_{m<n+1} cosConv)  +  (−(Σ_{m<n} sinConv))  ≃  cosPartial (A+B) (n+1) ,
    the degree-shifted telescope of `(TC)` (cos diagonal one degree ahead of sin).

  * THE RECTANGLE/CORNER ADDITION IDENTITY at the `Q'` level (step 4,
    `cosSinProd_eqv_cosPartial_add_remCorner`): for `n = k+1`,
        cosPartial A n · cosPartial B n  −  sinPartial A n · sinPartial B n
            ≃  cosPartial (A+B) n  +  remCorner A B k ,
    `remCorner A B k = (cosCorner A B (k+1) − sinCorner A B (k+1)) − sinConv A B k`,
    assembled from the cos/sin rectangle decompositions (`cos/sinProd_eqv_…`) and
    the diagonal collapse.

NOW CLOSED (STEP A — the analytic modulus, §6): `remCorner A B k → 0` past an
EXPLICIT modulus (`remCorner_le`), for `A, B ≥ 0`:
        ∀ ε>0, ∃ N, ∀ k ≥ N, remCorner A B k ≤ ε ∧ −(remCorner A B k) ≤ ε .
  The trig analogue of `CornerBoundAdd.cornerAbsAdd_le`, assembled from three
  independent Mertens-style estimates (NOT a verbatim copy):
    * `cosCornerAbs_le` / `sinCornerAbs_le` — the two product corners
      `cosCorner`/`sinCorner` are two-sidedly dominated by trig magnitude corners
      `cos/sinCornerAbs` (`cos/sinCorner_abs_le`), each → 0 by a split-at-`K`
      Mertens bound copied from `CornerBound.cornerAbs_le` (weights `termAbs A (2i)`
      / `termAbs A (2i+1)`, blocks `cos/sinBlockAbs B (n−i) i` dominated by the
      exponential block via `Trig.cos/sinBlockAbs_le_blockAbs`);
    * `sinConvAbs_le` — the trailing single convolution `sinConv A B k` is dominated
      by the magnitude convolution `sinConvAbs`, in which every term has total
      magnitude index `2k+2`, so splitting at `h = (k+1)/2` bounds it by two
      exponential tails (`termAbs_le_of_modulus_le` + `sinBlock_bound`) → 0.

NOW CLOSED (STEP B nonneg core, §7): `cos_add_equiv_nonneg`, for `A, B ≥ 0`,
        CReal.Equiv (cosFull (A+B)) (cosProdMinus A B) ,
  `cosProdMinus A B = cosFull A · cosFull B + (−(sinFull A · sinFull B))`.  This
  copies `ExpAdd.expNeg_add_equiv`: it transfers the `Q'`-level identity
  `cosSinProd_eqv_cosPartial_add_remCorner` to a `CReal.Equiv` using the Step-A
  modulus `remCorner_le`.  (`abs_of_nonneg` reduces `|A|=A` etc. for the nonneg
  approximations.)

What REMAINS (the residual to the unconditional K_t ≥ 0 / OS2 headline):

  (B-signed) the SIGNED extension `cos_add_equiv`/`sin_add_equiv` for arbitrary
  `A, B : Q'` via the four-case parity algebra (`cosFull_even`/`sinFull_odd_of_nonneg`)
  — needs `CReal.Equiv` transitivity and `mul`/`neg`/`add` Equiv-congruence lemmas
  (not yet in the CReal layer; only `Equiv.symm` and `Equiv_of_lifted_approx_equal`
  exist).  The nonneg core is the analytic content; the signed version is parity
  bookkeeping.

  (C) the CReal-level per-cosine-term second-difference bound
        |cosFull(θ+h) − cosFull(θ) − (−sinFull(θ))·h| ≤ ε·|h|  for 0<|h|≤δ(ε),
  assembled from (B-signed) + `cos_small_angle`/`sin_small_angle` +
  `TrigBound.cos_second_diff_abs_le` at the Equiv/leRat level (the per-index
  `TrigBound.hadd` does NOT hold exactly — only as a limit Equiv — so the bound
  must go through `leRat_of_equiv`, not per-index `cos_second_diff_eq`).

  (D) the θ-parametrised `FDDerivDataC F dSeriesCReal θ` for `F = ϑ₃(θ) =
  1 + 2Σ a^{n²} cosFull(2nθ)` summed (over n) against the tail majorant
  `M = Cmaj a` (`JTPIdentity.dTermMaj_le`), and the θ↔x Chebyshev bridge
  `T_n(cos 2θ) = cos(2nθ)` connecting this θ-ϑ₃ to the x-parametrised
  `dSeriesCReal`/`Rhalf`/`thetaConvCRealGen` — to feed
  `DiffProduct.C1UniqInputsCRealDeriv` →
  `JTPIdentity.Kt_geRat_zero_of_uniq_creal_deriv` for UNCONDITIONAL `K_t ≥ 0`.
  This requires NEW infrastructure not present in the repo: a θ-parametrised ϑ₃
  `CReal` (the entire heat-kernel/theta layer is currently x = cos θ /Chebyshev-`U`
  parametrised, never angle-θ parametrised) and the Chebyshev θ↔x identity.  It is
  the genuine remaining Wall-2 analytic build, named here and NOT faked.

# Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.TrigAdd.termAbs_eqv_congr
#print axioms ConstructiveReals.TrigAdd.cosPartial_eqv_congr
#print axioms ConstructiveReals.TrigAdd.sinPartial_eqv_congr
#print axioms ConstructiveReals.TrigAdd.equiv_of_approx_eqv
#print axioms ConstructiveReals.TrigAdd.cosFull
#print axioms ConstructiveReals.TrigAdd.sinFull
#print axioms ConstructiveReals.TrigAdd.cosFull_even
#print axioms ConstructiveReals.TrigAdd.sinFull_odd_of_nonneg
#print axioms ConstructiveReals.TrigAdd.blockAbs_two_le
#print axioms ConstructiveReals.TrigAdd.cos_small_angle
#print axioms ConstructiveReals.TrigAdd.sin_small_angle
#print axioms ConstructiveReals.TrigAdd.term_even_eq_abs
#print axioms ConstructiveReals.TrigAdd.term_odd_eq_neg_abs
#print axioms ConstructiveReals.TrigAdd.cosConv_addition_zero
#print axioms ConstructiveReals.TrigAdd.negPow_add
#print axioms ConstructiveReals.TrigAdd.negPow_self_mul
#print axioms ConstructiveReals.TrigAdd.negPow_succ_mul
#print axioms ConstructiveReals.TrigAdd.finSum_even_odd_split
#print axioms ConstructiveReals.TrigAdd.cosConvTerm_eqv
#print axioms ConstructiveReals.TrigAdd.sinConvTerm_eqv
#print axioms ConstructiveReals.TrigAdd.cosConv_eqv_evenSub
#print axioms ConstructiveReals.TrigAdd.sinConv_eqv_oddSub
#print axioms ConstructiveReals.TrigAdd.convAdd_eqv_even_odd
#print axioms ConstructiveReals.TrigAdd.cosConv_addition
#print axioms ConstructiveReals.TrigAdd.cosTri_succ
#print axioms ConstructiveReals.TrigAdd.sinTri_succ
#print axioms ConstructiveReals.TrigAdd.cosTri_eqv_convSum
#print axioms ConstructiveReals.TrigAdd.sinTri_eqv_convSum
#print axioms ConstructiveReals.TrigAdd.cosSum_sub_sinSum_eqv_cosPartial
#print axioms ConstructiveReals.TrigAdd.cosProd_eqv_convSum_add_corner
#print axioms ConstructiveReals.TrigAdd.sinProd_eqv_convSum_add_corner
#print axioms ConstructiveReals.TrigAdd.cosSinProd_eqv_cosPartial_add_remCorner
#print axioms ConstructiveReals.TrigAdd.cosCorner_abs_le
#print axioms ConstructiveReals.TrigAdd.sinCorner_abs_le
#print axioms ConstructiveReals.TrigAdd.cosCornerAbs_le
#print axioms ConstructiveReals.TrigAdd.sinCornerAbs_le
#print axioms ConstructiveReals.TrigAdd.sinConvAbs_le
#print axioms ConstructiveReals.TrigAdd.remCorner_le
#print axioms ConstructiveReals.TrigAdd.cos_add_equiv_nonneg
