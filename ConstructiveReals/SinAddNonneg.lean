/-
# The `Q'`-angle SINE addition law (in-range nonnegative core)

This module lands the not-yet-proved `Q'`-core `TrigAdd.sin_add_equiv_nonneg`,

    sinFull (A + B)  ≃  sinFull A · cosFull B  +  cosFull A · sinFull B    (A,B ≥ 0),

the cross-parity twin of `TrigAdd.cos_add_equiv_nonneg`.  It mirrors the cosine
development §5–§7 of `TrigAdd.lean`, but for the ODD convolution degree `2m+1`,
whose even/odd deinterleave reassembles the two MIXED cross-products
`sinTerm·cosTerm` and `cosTerm·sinTerm` — both carrying the SAME sign
`negPow (m+1)`, so the assembly is a single `mul_add` (a pure SUM, no sign-flip,
no `_zero` base case, no trailing convolution).

## What is genuinely proved here (no new axioms — `propext`/`Quot.sound` only)

  * **CRUX** `sinCosConv_addition` — the per-degree cross-parity identity
        sinCosConv A B m + cosSinConv A B m ≃ sinTerm (A+B) m ,
    the algebraic heart (research-novel; the twin of `cosConv_addition`).
  * `sinDiag_eqv_sinPartial` — the (equal-length, pure-sum) diagonal collapse.
  * `sinProd_eqv_sinPartial_add_remCorner` — the `Q'`-level rectangle/corner
    addition identity, with the two-corner remainder `sinRemCorner`.
  * `sinRemCorner_le` — STEP A: `sinRemCorner → 0` past an explicit modulus
    (two Mertens corners, `ε` split in halves).
  * `sin_add_equiv_nonneg` — STEP B: the CReal transfer, unconditional for
    `A, B ≥ 0`.  Inhabits the residual `TrigSineAddCReal.SinAddNonnegCore`.

# Axiom gate (see README: axiom policy): `[propext]` / `[propext, Quot.sound]` only.
-/
import ConstructiveReals.TrigAdd
import ConstructiveReals.TrigSineAddCReal

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.Trig

namespace TrigAdd

/-! ## 1. The even-count even/odd deinterleave

`finSum f (2m+2) ≃ Σ_{p≤m} f(2p) + Σ_{p≤m} f(2p+1)` — both sub-sums have `m+1`
terms (the odd sub-sum picks up one extra term relative to the odd-count split
`finSum_even_odd_split`).  Peels one term onto that split, then `add_assoc`. -/

/-- **Even-count even/odd deinterleave.**  `Σ_{i<2m+2} f(i) ≃
Σ_{p≤m} f(2p) + Σ_{p≤m} f(2p+1)`. -/
theorem finSum_even_odd_split_even (f : RationalTail.QSeq) (m : Nat) :
    (RationalTail.finSum f (2 * m + 2)).eqv
      (RationalTail.finSum (fun p => f (2 * p)) (m + 1)
        + RationalTail.finSum (fun p => f (2 * p + 1)) (m + 1)) := by
  -- finSum f (2m+2) = finSum f (2m+1) + f (2m+1)  (defeq peel of one term);
  -- RHS odd sub-sum at m+1 = (Σ odd m) + f(2m+1) (defeq).
  show (RationalTail.finSum f (2 * m + 1) + f (2 * m + 1)).eqv
      (RationalTail.finSum (fun p => f (2 * p)) (m + 1)
        + (RationalTail.finSum (fun p => f (2 * p + 1)) m + f (2 * m + 1)))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (f (2 * m + 1)) (finSum_even_odd_split f m)) ?_
  exact Q'.add_assoc_eqv _ _ (f (2 * m + 1))

/-! ## 2. The cross-parity convolutions and their even/odd convAdd bridges -/

/-- `i`-th term of the sin·cos cross Cauchy product at degree `m`. -/
def sinCosConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => sinTerm A i * cosTerm B (m - i)

/-- `i`-th term of the cos·sin cross Cauchy product at degree `m`. -/
def cosSinConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => cosTerm A i * sinTerm B (m - i)

/-- `sinCosConv A B m = Σ_{i≤m} sinTerm A i · cosTerm B (m−i)`. -/
def sinCosConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (sinCosConvTerm A B m) (m + 1)

/-- `cosSinConv A B m = Σ_{i≤m} cosTerm A i · sinTerm B (m−i)`. -/
def cosSinConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (cosSinConvTerm A B m) (m + 1)

/-- The even sub-sum of `convAdd A B (2m+1)` (the `m+1` even-index terms). -/
def crossEvenSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * m + 1) (2 * p)) (m + 1)

/-- The odd sub-sum of `convAdd A B (2m+1)` (the `m+1` odd-index terms). -/
def crossOddSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * m + 1) (2 * p + 1)) (m + 1)

/-- Even cross-term bridge: for `p ≤ m`,
`cosSinConvTerm A B m p ≈ negPow (m+1) · convAddTerm A B (2m+1) (2p)`.
`A` even (`cosTerm`, index `2p`), `B` odd (`sinTerm`, partner index `2(m−p)+1`):
one factor flips sign, giving the shared sign `negPow (m+1)`. -/
theorem cosSinConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (cosSinConvTerm A B m p).eqv (negPow (m + 1) * convAddTerm A B (2 * m + 1) (2 * p)) := by
  have hsub : 2 * m + 1 - 2 * p = 2 * (m - p) + 1 := by omega
  show ((negPow p * termAbs A (2 * p)) * (negPow (m - p) * termAbs B (2 * (m - p) + 1))).eqv
      (negPow (m + 1) * (ExpNeg.term A (2 * p) * ExpNeg.term B (2 * m + 1 - 2 * p)))
  rw [hsub]
  refine Q'.eqv_symm ?_
  -- term A (2p) ≈ termAbs A (2p);  term B (2(m−p)+1) ≈ −(termAbs B (2(m−p)+1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p)) (termAbs A (2 * p)) _
        (term_even_eq_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.mul_eqv_congr_left (termAbs A (2 * p)) (ExpNeg.term B (2 * (m - p) + 1))
        (-(termAbs B (2 * (m - p) + 1))) (term_odd_eq_neg_abs B (m - p)))) ?_
  -- termAbs A · (−termAbs B) ≈ −(termAbs A · termAbs B)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.mul_neg_eqv (termAbs A (2 * p)) (termAbs B (2 * (m - p) + 1)))) ?_
  -- negPow(m+1)·(−X) ≈ −(negPow(m+1)·X) ≈ (−negPow(m+1))·X ≈ negPow m · X
  refine Q'.eqv_trans _ _ _
    (Q'.mul_neg_eqv (negPow (m + 1)) (termAbs A (2 * p) * termAbs B (2 * (m - p) + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.neg_mul_eqv (negPow (m + 1))
      (termAbs A (2 * p) * termAbs B (2 * (m - p) + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (-(negPow (m + 1))) (negPow m)
      (termAbs A (2 * p) * termAbs B (2 * (m - p) + 1)) (Q'.neg_neg_eqv (negPow m))) ?_
  -- sign collapse negPow m ≈ negPow p · negPow (m−p), then shuffle
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]; exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p) * termAbs B (2 * (m - p) + 1)) hsign) ?_
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p)) (termAbs B (2 * (m - p) + 1))

/-- Odd cross-term bridge: for `p ≤ m`,
`sinCosConvTerm A B m p ≈ negPow (m+1) · convAddTerm A B (2m+1) (2p+1)`.
`A` odd (`sinTerm`, index `2p+1`), `B` even (`cosTerm`, partner index `2(m−p)`):
one factor flips sign, giving the SAME shared sign `negPow (m+1)`. -/
theorem sinCosConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (sinCosConvTerm A B m p).eqv (negPow (m + 1) * convAddTerm A B (2 * m + 1) (2 * p + 1)) := by
  have hsub : 2 * m + 1 - (2 * p + 1) = 2 * (m - p) := by omega
  show ((negPow p * termAbs A (2 * p + 1)) * (negPow (m - p) * termAbs B (2 * (m - p)))).eqv
      (negPow (m + 1) * (ExpNeg.term A (2 * p + 1) * ExpNeg.term B (2 * m + 1 - (2 * p + 1))))
  rw [hsub]
  refine Q'.eqv_symm ?_
  -- term A (2p+1) ≈ −(termAbs A (2p+1));  term B (2(m−p)) ≈ termAbs B (2(m−p))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p + 1)) (-(termAbs A (2 * p + 1))) _
        (term_odd_eq_neg_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.mul_eqv_congr_left (-(termAbs A (2 * p + 1))) (ExpNeg.term B (2 * (m - p)))
        (termAbs B (2 * (m - p))) (term_even_eq_abs B (m - p)))) ?_
  -- (−termAbs A)·termAbs B ≈ −(termAbs A · termAbs B)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.neg_mul_eqv (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_neg_eqv (negPow (m + 1)) (termAbs A (2 * p + 1) * termAbs B (2 * (m - p)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.neg_mul_eqv (negPow (m + 1))
      (termAbs A (2 * p + 1) * termAbs B (2 * (m - p))))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (-(negPow (m + 1))) (negPow m)
      (termAbs A (2 * p + 1) * termAbs B (2 * (m - p))) (Q'.neg_neg_eqv (negPow m))) ?_
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]; exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p + 1) * termAbs B (2 * (m - p))) hsign) ?_
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p)))

/-- `cosSinConv A B m ≈ negPow (m+1) · crossEvenSub A B m`. -/
theorem cosSinConv_eqv_crossEvenSub (A B : Q') (m : Nat) :
    (cosSinConv A B m).eqv (negPow (m + 1) * crossEvenSub A B m) := by
  show (RationalTail.finSum (cosSinConvTerm A B m) (m + 1)).eqv
      (negPow (m + 1) * RationalTail.finSum
        (fun p => convAddTerm A B (2 * m + 1) (2 * p)) (m + 1))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (cosSinConvTerm A B m)
      (fun p => negPow (m + 1) * convAddTerm A B (2 * m + 1) (2 * p)) (m + 1)
      (fun p hp => cosSinConvTerm_eqv A B m p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * m + 1) (2 * p)) (negPow (m + 1)) (m + 1))

/-- `sinCosConv A B m ≈ negPow (m+1) · crossOddSub A B m`. -/
theorem sinCosConv_eqv_crossOddSub (A B : Q') (m : Nat) :
    (sinCosConv A B m).eqv (negPow (m + 1) * crossOddSub A B m) := by
  show (RationalTail.finSum (sinCosConvTerm A B m) (m + 1)).eqv
      (negPow (m + 1) * RationalTail.finSum
        (fun p => convAddTerm A B (2 * m + 1) (2 * p + 1)) (m + 1))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (sinCosConvTerm A B m)
      (fun p => negPow (m + 1) * convAddTerm A B (2 * m + 1) (2 * p + 1)) (m + 1)
      (fun p hp => sinCosConvTerm_eqv A B m p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * m + 1) (2 * p + 1)) (negPow (m + 1)) (m + 1))

/-- `convAdd A B (2m+1) ≈ crossEvenSub A B m + crossOddSub A B m`. -/
theorem convAdd_eqv_cross (A B : Q') (m : Nat) :
    (convAdd A B (2 * m + 1)).eqv (crossEvenSub A B m + crossOddSub A B m) := by
  show (RationalTail.finSum (convAddTerm A B (2 * m + 1)) (2 * m + 2)).eqv
      (RationalTail.finSum (fun p => convAddTerm A B (2 * m + 1) (2 * p)) (m + 1)
        + RationalTail.finSum (fun p => convAddTerm A B (2 * m + 1) (2 * p + 1)) (m + 1))
  exact finSum_even_odd_split_even (convAddTerm A B (2 * m + 1)) m

/-- `sinTerm (A+B) m ≈ negPow (m+1) · term (A+B) (2m+1)` (odd-index magnitude
bridge at the sum angle: `sinTerm (A+B) m = negPow m · termAbs`, and
`term (A+B) (2m+1) ≈ −termAbs`, so `(−negPow m)·(−termAbs) ≈ negPow m·termAbs`). -/
theorem sinTerm_eqv_negPow_term (A B : Q') (m : Nat) :
    (sinTerm (A + B) m).eqv (negPow (m + 1) * ExpNeg.term (A + B) (2 * m + 1)) := by
  show (negPow m * termAbs (A + B) (2 * m + 1)).eqv
      (negPow (m + 1) * ExpNeg.term (A + B) (2 * m + 1))
  refine Q'.eqv_symm ?_
  -- negPow(m+1)·term(A+B)(2m+1) = (−negPow m)·term ≈ (−negPow m)·(−termAbs) ≈ negPow m·termAbs
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) (ExpNeg.term (A + B) (2 * m + 1))
      (-(termAbs (A + B) (2 * m + 1))) (term_odd_eq_neg_abs (A + B) m)) ?_
  show ((-(negPow m)) * (-(termAbs (A + B) (2 * m + 1)))).eqv
      (negPow m * termAbs (A + B) (2 * m + 1))
  exact neg_mul_neg (negPow m) (termAbs (A + B) (2 * m + 1))

/-- **CRUX — the per-degree cross-parity addition identity.**
`sinCosConv A B m + cosSinConv A B m ≃ sinTerm (A+B) m`.

The algebraic heart of `sin(A+B) = sin A cos B + cos A sin B`: both cross
sub-sums of the ODD convolution `convAdd A B (2m+1)` carry the SAME sign
`negPow (m+1)`, so the assembly is a single `mul_add` — no sign-flip, no base
case (contrast `cosConv_addition`, whose two sub-sums differ by one `−1`). -/
theorem sinCosConv_addition (A B : Q') (m : Nat) :
    (sinCosConv A B m + cosSinConv A B m).eqv (sinTerm (A + B) m) := by
  -- substitute the two sub-sum identities (both sign negPow (m+1))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (sinCosConv_eqv_crossOddSub A B m)
      (cosSinConv_eqv_crossEvenSub A B m)) ?_
  -- negPow(m+1)·crossOdd + negPow(m+1)·crossEven ≈ negPow(m+1)·(crossOdd + crossEven)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_add_eqv (negPow (m + 1)) (crossOddSub A B m) (crossEvenSub A B m))) ?_
  -- crossOdd + crossEven ≈ crossEven + crossOdd ≈ convAdd ≈ term
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.add_comm_eqv (crossOddSub A B m) (crossEvenSub A B m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.eqv_symm (convAdd_eqv_cross A B m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _ (convAdd_eqv_term A B (2 * m + 1))) ?_
  exact Q'.eqv_symm (sinTerm_eqv_negPow_term A B m)

/-! ## 3. Cross triangle recurrences and the diagonal collapse -/

/-- `sinCosTriTerm A B n i = sinTerm A i · cosPartial B (n−i)`. -/
def sinCosTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * cosPartial B (n - i)

/-- `sinCosTri A B n = Σ_{i<n} sinTerm A i · cosPartial B (n−i)`. -/
def sinCosTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinCosTriTerm A B n) n

/-- `cosSinTriTerm A B n i = cosTerm A i · sinPartial B (n−i)`. -/
def cosSinTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * sinPartial B (n - i)

/-- `cosSinTri A B n = Σ_{i<n} cosTerm A i · sinPartial B (n−i)`. -/
def cosSinTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosSinTriTerm A B n) n

/-- sin·cos triangle recurrence `sinCosTri (n+1) ≃ sinCosTri n + sinCosConv n`. -/
theorem sinCosTri_succ (A B : Q') (n : Nat) :
    (sinCosTri A B (n + 1)).eqv (sinCosTri A B n + sinCosConv A B n) := by
  show (RationalTail.finSum (sinCosTriTerm A B (n + 1)) n + sinCosTriTerm A B (n + 1) n).eqv
      (sinCosTri A B n + sinCosConv A B n)
  have hlast : (sinCosTriTerm A B (n + 1) n).eqv (sinTerm A n * cosTerm B 0) := by
    show (sinTerm A n * cosPartial B ((n + 1) - n)).eqv (sinTerm A n * cosTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (sinTerm A n * ((0 : Q') + cosTerm B 0)).eqv (sinTerm A n * cosTerm B 0)
    exact Q'.mul_eqv_congr_left (sinTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosTerm B 0)))
  have hrow : ∀ i, i < n →
      (sinCosTriTerm A B (n + 1) i).eqv (sinCosTriTerm A B n i + sinCosConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (sinTerm A i * cosPartial B ((n + 1) - i)).eqv
        (sinTerm A i * cosPartial B (n - i) + sinTerm A i * cosTerm B (n - i))
    rw [hsub]
    show (sinTerm A i * (cosPartial B (n - i) + cosTerm B (n - i))).eqv
        (sinTerm A i * cosPartial B (n - i) + sinTerm A i * cosTerm B (n - i))
    exact Q'.mul_add_eqv (sinTerm A i) (cosPartial B (n - i)) (cosTerm B (n - i))
  have hinner : (RationalTail.finSum (sinCosTriTerm A B (n + 1)) n).eqv
      (sinCosTri A B n + RationalTail.finSum (sinCosConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (sinCosTriTerm A B (n + 1))
        (fun i => sinCosTriTerm A B n i + sinCosConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (sinCosTriTerm A B n) (sinCosConvTerm A B n) n)
  have hconv : (sinCosConv A B n).eqv
      (RationalTail.finSum (sinCosConvTerm A B n) n + sinTerm A n * cosTerm B 0) := by
    show (RationalTail.finSum (sinCosConvTerm A B n) n + sinCosConvTerm A B n n).eqv
        (RationalTail.finSum (sinCosConvTerm A B n) n + sinTerm A n * cosTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (sinTerm A n * cosTerm B (n - n)).eqv (sinTerm A n * cosTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (sinCosTri A B n) (RationalTail.finSum (sinCosConvTerm A B n) n)
      (sinTerm A n * cosTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (sinCosTri A B n) _ _ (Q'.eqv_symm hconv)

/-- cos·sin triangle recurrence `cosSinTri (n+1) ≃ cosSinTri n + cosSinConv n`. -/
theorem cosSinTri_succ (A B : Q') (n : Nat) :
    (cosSinTri A B (n + 1)).eqv (cosSinTri A B n + cosSinConv A B n) := by
  show (RationalTail.finSum (cosSinTriTerm A B (n + 1)) n + cosSinTriTerm A B (n + 1) n).eqv
      (cosSinTri A B n + cosSinConv A B n)
  have hlast : (cosSinTriTerm A B (n + 1) n).eqv (cosTerm A n * sinTerm B 0) := by
    show (cosTerm A n * sinPartial B ((n + 1) - n)).eqv (cosTerm A n * sinTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (cosTerm A n * ((0 : Q') + sinTerm B 0)).eqv (cosTerm A n * sinTerm B 0)
    exact Q'.mul_eqv_congr_left (cosTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (sinTerm B 0)))
  have hrow : ∀ i, i < n →
      (cosSinTriTerm A B (n + 1) i).eqv (cosSinTriTerm A B n i + cosSinConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (cosTerm A i * sinPartial B ((n + 1) - i)).eqv
        (cosTerm A i * sinPartial B (n - i) + cosTerm A i * sinTerm B (n - i))
    rw [hsub]
    show (cosTerm A i * (sinPartial B (n - i) + sinTerm B (n - i))).eqv
        (cosTerm A i * sinPartial B (n - i) + cosTerm A i * sinTerm B (n - i))
    exact Q'.mul_add_eqv (cosTerm A i) (sinPartial B (n - i)) (sinTerm B (n - i))
  have hinner : (RationalTail.finSum (cosSinTriTerm A B (n + 1)) n).eqv
      (cosSinTri A B n + RationalTail.finSum (cosSinConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (cosSinTriTerm A B (n + 1))
        (fun i => cosSinTriTerm A B n i + cosSinConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (cosSinTriTerm A B n) (cosSinConvTerm A B n) n)
  have hconv : (cosSinConv A B n).eqv
      (RationalTail.finSum (cosSinConvTerm A B n) n + cosTerm A n * sinTerm B 0) := by
    show (RationalTail.finSum (cosSinConvTerm A B n) n + cosSinConvTerm A B n n).eqv
        (RationalTail.finSum (cosSinConvTerm A B n) n + cosTerm A n * sinTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (cosTerm A n * sinTerm B (n - n)).eqv (cosTerm A n * sinTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (cosSinTri A B n) (RationalTail.finSum (cosSinConvTerm A B n) n)
      (cosTerm A n * sinTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (cosSinTri A B n) _ _ (Q'.eqv_symm hconv)

/-- `sinCosTri A B n ≃ Σ_{m<n} sinCosConv A B m`. -/
theorem sinCosTri_eqv_convSum (A B : Q') :
    ∀ n, (sinCosTri A B n).eqv (RationalTail.finSum (sinCosConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinCosTri A B (n + 1)).eqv (RationalTail.finSum (sinCosConv A B) n + sinCosConv A B n)
    refine Q'.eqv_trans _ _ _ (sinCosTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (sinCosTri A B n) _ (sinCosConv A B n) (sinCosTri_eqv_convSum A B n)

/-- `cosSinTri A B n ≃ Σ_{m<n} cosSinConv A B m`. -/
theorem cosSinTri_eqv_convSum (A B : Q') :
    ∀ n, (cosSinTri A B n).eqv (RationalTail.finSum (cosSinConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (cosSinTri A B (n + 1)).eqv (RationalTail.finSum (cosSinConv A B) n + cosSinConv A B n)
    refine Q'.eqv_trans _ _ _ (cosSinTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (cosSinTri A B n) _ (cosSinConv A B n) (cosSinTri_eqv_convSum A B n)

/-- **Diagonal collapse (pure equal-length sum).**  `(Σ_{m<n} sinCosConv) +
(Σ_{m<n} cosSinConv) ≃ sinPartial (A+B) n`.  Induction pairing each `m` via the
crux `sinCosConv_addition` — no degree shift, no unpaired corner. -/
theorem sinDiag_eqv_sinPartial (A B : Q') :
    ∀ n, (RationalTail.finSum (sinCosConv A B) n
        + RationalTail.finSum (cosSinConv A B) n).eqv (sinPartial (A + B) n)
  | 0 => by
    show ((0 : Q') + 0).eqv (sinPartial (A + B) 0)
    show ((0 : Q') + 0).eqv 0
    exact Q'.eqv_of_eq (Q'.zero_add' 0)
  | n + 1 => by
    show ((RationalTail.finSum (sinCosConv A B) n + sinCosConv A B n)
        + (RationalTail.finSum (cosSinConv A B) n + cosSinConv A B n)).eqv
        (sinPartial (A + B) n + sinTerm (A + B) n)
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (RationalTail.finSum (sinCosConv A B) n) (sinCosConv A B n)
        (RationalTail.finSum (cosSinConv A B) n) (cosSinConv A B n)) ?_
    exact Q'.add_eqv_congr' (sinDiag_eqv_sinPartial A B n) (sinCosConv_addition A B n)

/-! ## 4. Cross rectangle/corner decompositions and the addition identity -/

/-- `sinCosCornerTerm A B n i = sinTerm A i · (cosPartial B n − cosPartial B (n−i))`. -/
def sinCosCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * (cosPartial B n + -(cosPartial B (n - i)))

/-- `sinCosCorner A B n = Σ_{i<n} sinCosCornerTerm A B n i`. -/
def sinCosCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinCosCornerTerm A B n) n

/-- `cosSinCornerTerm A B n i = cosTerm A i · (sinPartial B n − sinPartial B (n−i))`. -/
def cosSinCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * (sinPartial B n + -(sinPartial B (n - i)))

/-- `cosSinCorner A B n = Σ_{i<n} cosSinCornerTerm A B n i`. -/
def cosSinCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosSinCornerTerm A B n) n

/-- **sin·cos rectangle/corner decomposition.**  `sinPartial A n · cosPartial B n ≃
sinCosTri A B n + sinCosCorner A B n`. -/
theorem sinCosProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * cosPartial B n).eqv (sinCosTri A B n + sinCosCorner A B n) := by
  rw [sinPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (sinTerm A) (cosPartial B n) n) ?_
  have hterm : ∀ i, (sinTerm A i * cosPartial B n).eqv
      (sinCosTriTerm A B n i + sinCosCornerTerm A B n i) := by
    intro i
    show (sinTerm A i * cosPartial B n).eqv
        (sinTerm A i * cosPartial B (n - i)
          + sinTerm A i * (cosPartial B n + -(cosPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (sinTerm A i) (cosPartial B n)
        (cosPartial B (n - i) + (cosPartial B n + -(cosPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (cosPartial B n) (cosPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (sinTerm A i) (cosPartial B (n - i))
      (cosPartial B n + -(cosPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => sinTerm A i * cosPartial B n)
      (fun i => sinCosTriTerm A B n i + sinCosCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (sinCosTriTerm A B n) (sinCosCornerTerm A B n) n

/-- **cos·sin rectangle/corner decomposition.**  `cosPartial A n · sinPartial B n ≃
cosSinTri A B n + cosSinCorner A B n`. -/
theorem cosSinProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * sinPartial B n).eqv (cosSinTri A B n + cosSinCorner A B n) := by
  rw [cosPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (cosTerm A) (sinPartial B n) n) ?_
  have hterm : ∀ i, (cosTerm A i * sinPartial B n).eqv
      (cosSinTriTerm A B n i + cosSinCornerTerm A B n i) := by
    intro i
    show (cosTerm A i * sinPartial B n).eqv
        (cosTerm A i * sinPartial B (n - i)
          + cosTerm A i * (sinPartial B n + -(sinPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (cosTerm A i) (sinPartial B n)
        (sinPartial B (n - i) + (sinPartial B n + -(sinPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (sinPartial B n) (sinPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (cosTerm A i) (sinPartial B (n - i))
      (sinPartial B n + -(sinPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => cosTerm A i * sinPartial B n)
      (fun i => cosSinTriTerm A B n i + cosSinCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (cosSinTriTerm A B n) (cosSinCornerTerm A B n) n

/-- sin·cos rectangle, diagonal form. -/
theorem sinCosProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * cosPartial B n).eqv
      (RationalTail.finSum (sinCosConv A B) n + sinCosCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (sinCosProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (sinCosTri A B n) _ (sinCosCorner A B n) (sinCosTri_eqv_convSum A B n)

/-- cos·sin rectangle, diagonal form. -/
theorem cosSinProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * sinPartial B n).eqv
      (RationalTail.finSum (cosSinConv A B) n + cosSinCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (cosSinProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (cosSinTri A B n) _ (cosSinCorner A B n) (cosSinTri_eqv_convSum A B n)

/-- The combined corner remainder (TWO corners, no trailing convolution). -/
def sinRemCorner (A B : Q') (n : Nat) : Q' :=
  sinCosCorner A B n + cosSinCorner A B n

/-- **The cross rectangle/corner addition identity (`Q'` level).**  For every `n`,
`sinPartial A n · cosPartial B n + cosPartial A n · sinPartial B n
≃ sinPartial (A+B) n + sinRemCorner A B n`. -/
theorem sinProd_eqv_sinPartial_add_remCorner (A B : Q') (n : Nat) :
    (sinPartial A n * cosPartial B n + cosPartial A n * sinPartial B n).eqv
      (sinPartial (A + B) n + sinRemCorner A B n) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (sinCosProd_eqv_convSum_add_corner A B n)
      (cosSinProd_eqv_convSum_add_corner A B n)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (RationalTail.finSum (sinCosConv A B) n) (sinCosCorner A B n)
      (RationalTail.finSum (cosSinConv A B) n) (cosSinCorner A B n)) ?_
  refine Q'.add_eqv_congr' (sinDiag_eqv_sinPartial A B n) ?_
  exact Q'.eqv_refl _

/-! ## 5. STEP A — the two Mertens corners → 0 -/

/-- `sinCosCornerAbsTerm A B n i = termAbs A (2i+1)·cosBlockAbs B (n−i) i`. -/
def sinCosCornerAbsTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs A (2 * i + 1) * cosBlockAbs B (n - i) i

/-- `sinCosCornerAbs A B n = Σ_{i<n} termAbs A (2i+1)·cosBlockAbs B (n−i) i`. -/
def sinCosCornerAbs (A B : Q') (n : Nat) : Q' :=
  RationalTail.finSum (sinCosCornerAbsTerm A B n) n

/-- `cosSinCornerAbsTerm A B n i = termAbs A (2i)·sinBlockAbs B (n−i) i`. -/
def cosSinCornerAbsTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => termAbs A (2 * i) * sinBlockAbs B (n - i) i

/-- `cosSinCornerAbs A B n = Σ_{i<n} termAbs A (2i)·sinBlockAbs B (n−i) i`. -/
def cosSinCornerAbs (A B : Q') (n : Nat) : Q' :=
  RationalTail.finSum (cosSinCornerAbsTerm A B n) n

/-- Termwise `±sinCosCornerTerm ≤ sinCosCornerAbsTerm`, for `i < n`. -/
theorem sinCosCornerTerm_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n i : Nat) (hi : i < n) :
    sinCosCornerTerm A B n i ≤ sinCosCornerAbsTerm A B n i
      ∧ -(sinCosCornerTerm A B n i) ≤ sinCosCornerAbsTerm A B n i := by
  have hni : (n - i) + i = n := by omega
  have hBnn : (0 : Q') ≤ termAbs A (2 * i + 1) := termAbs_nonneg A hA (2 * i + 1)
  have hdnn : (0 : Q') ≤ cosBlockAbs B (n - i) i := cosBlockAbs_nonneg B hB (n - i) i
  obtain ⟨hu2, hu1⟩ := sinTerm_two_sided A hA i
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
    have hnu1 : -(termAbs A (2 * i + 1)) ≤ -(sinTerm A i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2); exact Q'.le_refl' _
    have hnu2 : -(sinTerm A i) ≤ termAbs A (2 * i + 1) := by
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv ?_)
      exact Q'.neg_neg_eqv (termAbs A (2 * i + 1))
    exact Q'.mul_le_of_bounds hBnn hdnn hnu1 hnu2 hv1 hv2

/-- Termwise `±cosSinCornerTerm ≤ cosSinCornerAbsTerm`, for `i < n`. -/
theorem cosSinCornerTerm_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n i : Nat) (hi : i < n) :
    cosSinCornerTerm A B n i ≤ cosSinCornerAbsTerm A B n i
      ∧ -(cosSinCornerTerm A B n i) ≤ cosSinCornerAbsTerm A B n i := by
  have hni : (n - i) + i = n := by omega
  have hBnn : (0 : Q') ≤ termAbs A (2 * i) := termAbs_nonneg A hA (2 * i)
  have hdnn : (0 : Q') ≤ sinBlockAbs B (n - i) i := sinBlockAbs_nonneg B hB (n - i) i
  obtain ⟨hu2, hu1⟩ := cosTerm_two_sided A hA i
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
    have hnu1 : -(termAbs A (2 * i)) ≤ -(cosTerm A i) := by
      refine Q'.le_trans' _ _ _ ?_ (Q'.neg_le_neg hu2); exact Q'.le_refl' _
    have hnu2 : -(cosTerm A i) ≤ termAbs A (2 * i) := by
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg hu1) (Q'.le_of_eqv ?_)
      exact Q'.neg_neg_eqv (termAbs A (2 * i))
    exact Q'.mul_le_of_bounds hBnn hdnn hnu1 hnu2 hv1 hv2

/-- `±sinCosCorner ≤ sinCosCornerAbs`. -/
theorem sinCosCorner_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) (n : Nat) :
    sinCosCorner A B n ≤ sinCosCornerAbs A B n
      ∧ -(sinCosCorner A B n) ≤ sinCosCornerAbs A B n := by
  refine ⟨finSum_le_lt (sinCosCornerTerm A B n) (sinCosCornerAbsTerm A B n) n
      (fun i hi => (sinCosCornerTerm_abs_le A B hA hB n i hi).1), ?_⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (sinCosCornerTerm A B n) n)) ?_
  exact finSum_le_lt (fun i => -(sinCosCornerTerm A B n i)) (sinCosCornerAbsTerm A B n) n
    (fun i hi => (sinCosCornerTerm_abs_le A B hA hB n i hi).2)

/-- `±cosSinCorner ≤ cosSinCornerAbs`. -/
theorem cosSinCorner_abs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) (n : Nat) :
    cosSinCorner A B n ≤ cosSinCornerAbs A B n
      ∧ -(cosSinCorner A B n) ≤ cosSinCornerAbs A B n := by
  refine ⟨finSum_le_lt (cosSinCornerTerm A B n) (cosSinCornerAbsTerm A B n) n
      (fun i hi => (cosSinCornerTerm_abs_le A B hA hB n i hi).1), ?_⟩
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (cosSinCornerTerm A B n) n)) ?_
  exact finSum_le_lt (fun i => -(cosSinCornerTerm A B n i)) (cosSinCornerAbsTerm A B n) n
    (fun i hi => (cosSinCornerTerm_abs_le A B hA hB n i hi).2)

/-- **`sinCosCornerAbs A B n → 0`.**  Odd `A`-weight × cos `B`-block Mertens bound
(split at `K = trigModulus A δ`). -/
theorem sinCosCornerAbs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → sinCosCornerAbs A B n ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound A hA
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound B hB
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  obtain ⟨K, hKdef⟩ : ∃ K, K = Trig.trigModulus A δ := ⟨_, rfl⟩
  have hKmodA : Trig.trigModulus A δ ≤ K := Nat.le_of_eq hKdef.symm
  refine ⟨K + Trig.trigModulus B δ, fun n hn => ?_⟩
  have hKn : K ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKn
  have hsplit : (sinCosCornerAbs A B (K + d)).eqv
      (RationalTail.finSum (sinCosCornerAbsTerm A B (K + d)) K
        + RationalTail.finSum (fun j => sinCosCornerAbsTerm A B (K + d) (K + j)) d) :=
    finSum_split (sinCosCornerAbsTerm A B (K + d)) K d
  have hpart1 : RationalTail.finSum (sinCosCornerAbsTerm A B (K + d)) K ≤ Ba * δ := by
    have hterm1 : ∀ i, i < K → sinCosCornerAbsTerm A B (K + d) i ≤ termAbs A (2 * i + 1) * δ := by
      intro i hiK
      have hblock : cosBlockAbs B ((K + d) - i) i ≤ δ := by
        have hmodi : Trig.trigModulus B δ ≤ (K + d) - i := by omega
        exact Trig.cosBlock_bound B hB δ hδpos ((K + d) - i) hmodi i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * i + 1)) hblock
        (termAbs_nonneg A hA (2 * i + 1))
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (sinCosCornerAbsTerm A B (K + d)) (fun i => termAbs A (2 * i + 1) * δ) K hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const (fun i => termAbs A (2 * i + 1)) δ K))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ Ba δ ?_ hδnn
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (oddTermSum_eqv_sinBlock A K)) ?_
    refine Q'.le_trans' _ _ _ (Trig.sinBlockAbs_le_blockAbs A hA 0 K) ?_
    exact blockAbs_le_bound A hA hBa (2 * 0 + 1) (2 * K)
  have hpart2 : RationalTail.finSum (fun j => sinCosCornerAbsTerm A B (K + d) (K + j)) d ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => sinCosCornerAbsTerm A B (K + d) (K + j)) j
        ≤ termAbs A (2 * (K + j) + 1) * Bb := by
      intro j
      show termAbs A (2 * (K + j) + 1) * cosBlockAbs B ((K + d) - (K + j)) (K + j)
          ≤ termAbs A (2 * (K + j) + 1) * Bb
      refine Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * (K + j) + 1)) ?_
        (termAbs_nonneg A hA (2 * (K + j) + 1))
      refine Q'.le_trans' _ _ _ (Trig.cosBlockAbs_le_blockAbs B hB ((K + d) - (K + j)) (K + j)) ?_
      exact blockAbs_le_bound B hB hBb _ _
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => sinCosCornerAbsTerm A B (K + d) (K + j))
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

/-- **`cosSinCornerAbs A B n → 0`.**  Even `A`-weight × sin `B`-block Mertens bound. -/
theorem cosSinCornerAbs_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → cosSinCornerAbs A B n ≤ ε := by
  obtain ⟨Ba, hBa0, hBa⟩ := exists_psAbs_bound A hA
  obtain ⟨Bb, hBb0, hBb⟩ := exists_psAbs_bound B hB
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hBa0 hBb0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  obtain ⟨K, hKdef⟩ : ∃ K, K = Trig.trigModulus A δ := ⟨_, rfl⟩
  have hKmodA : Trig.trigModulus A δ ≤ K := Nat.le_of_eq hKdef.symm
  refine ⟨K + Trig.trigModulus B δ, fun n hn => ?_⟩
  have hKn : K ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKn
  have hsplit : (cosSinCornerAbs A B (K + d)).eqv
      (RationalTail.finSum (cosSinCornerAbsTerm A B (K + d)) K
        + RationalTail.finSum (fun j => cosSinCornerAbsTerm A B (K + d) (K + j)) d) :=
    finSum_split (cosSinCornerAbsTerm A B (K + d)) K d
  have hpart1 : RationalTail.finSum (cosSinCornerAbsTerm A B (K + d)) K ≤ Ba * δ := by
    have hterm1 : ∀ i, i < K → cosSinCornerAbsTerm A B (K + d) i ≤ termAbs A (2 * i) * δ := by
      intro i hiK
      have hblock : sinBlockAbs B ((K + d) - i) i ≤ δ := by
        have hmodi : Trig.trigModulus B δ ≤ (K + d) - i := by omega
        exact Trig.sinBlock_bound B hB δ hδpos ((K + d) - i) hmodi i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * i)) hblock
        (termAbs_nonneg A hA (2 * i))
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (cosSinCornerAbsTerm A B (K + d)) (fun i => termAbs A (2 * i) * δ) K hterm1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (RationalTail.finSum_mul_const (fun i => termAbs A (2 * i)) δ K))) ?_
    refine Q'.mul_le_mul_of_nonneg_right _ Ba δ ?_ hδnn
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (evenTermSum_eqv_cosBlock A K)) ?_
    refine Q'.le_trans' _ _ _ (Trig.cosBlockAbs_le_blockAbs A hA 0 K) ?_
    exact blockAbs_le_bound A hA hBa 0 (2 * K)
  have hpart2 : RationalTail.finSum (fun j => cosSinCornerAbsTerm A B (K + d) (K + j)) d ≤ δ * Bb := by
    have hterm2 : ∀ j, (fun j => cosSinCornerAbsTerm A B (K + d) (K + j)) j
        ≤ termAbs A (2 * (K + j)) * Bb := by
      intro j
      show termAbs A (2 * (K + j)) * sinBlockAbs B ((K + d) - (K + j)) (K + j)
          ≤ termAbs A (2 * (K + j)) * Bb
      refine Q'.mul_le_mul_of_nonneg_left _ _ (termAbs A (2 * (K + j))) ?_
        (termAbs_nonneg A hA (2 * (K + j)))
      refine Q'.le_trans' _ _ _ (Trig.sinBlockAbs_le_blockAbs B hB ((K + d) - (K + j)) (K + j)) ?_
      exact blockAbs_le_bound B hB hBb _ _
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => cosSinCornerAbsTerm A B (K + d) (K + j))
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

/-- **STEP A: `sinRemCorner A B n → 0`.**  Two Mertens corners, `ε` split in halves
(no trailing convolution — strictly simpler than the cosine `remCorner_le`). -/
theorem sinRemCorner_le (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      sinRemCorner A B n ≤ ε ∧ -(sinRemCorner A B n) ≤ ε := by
  obtain ⟨t, htpos, ht⟩ := CReal.exists_mul_le (by decide : (0 : Q') ≤ (2 : Q')) hε
  have ht2 : t + t ≤ ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) ht
    show (t + t).eqv (2 * t)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (2 : Q') ((1 : Q') + 1) t (by decide)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') 1 t) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv t) (Q'.one_mul_eqv t)
  obtain ⟨Nc, hNc⟩ := sinCosCornerAbs_le A B hA hB t htpos
  obtain ⟨Ns, hNs⟩ := cosSinCornerAbs_le A B hA hB t htpos
  refine ⟨max Nc Ns, fun n hn => ?_⟩
  have hnNc : Nc ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnNs : Ns ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hc1 : sinCosCornerAbs A B n ≤ t := hNc n hnNc
  have hc2 : cosSinCornerAbs A B n ≤ t := hNs n hnNs
  obtain ⟨h1a, h1b⟩ := sinCosCorner_abs_le A B hA hB n
  obtain ⟨h2a, h2b⟩ := cosSinCorner_abs_le A B hA hB n
  have hup : sinRemCorner A B n ≤ t + t := by
    show sinCosCorner A B n + cosSinCorner A B n ≤ t + t
    exact Q'.add_le_add (Q'.le_trans' _ _ _ h1a hc1) (Q'.le_trans' _ _ _ h2a hc2)
  have hlo : -(sinRemCorner A B n) ≤ t + t := by
    show -(sinCosCorner A B n + cosSinCorner A B n) ≤ t + t
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_add_eqv (sinCosCorner A B n) (cosSinCorner A B n))) ?_
    exact Q'.add_le_add (Q'.le_trans' _ _ _ h1b hc1) (Q'.le_trans' _ _ _ h2b hc2)
  exact ⟨Q'.le_trans' _ _ _ hup ht2, Q'.le_trans' _ _ _ hlo ht2⟩

/-! ## 6. STEP B — the CReal sine addition law (nonnegative core) -/

/-- The `Q'`-level right-hand side as a `CReal` (a defeq copy of
`TrigSineAddCReal.sinProdPlus`): `sinFull A · cosFull B + cosFull A · sinFull B`. -/
def sinProdPlus (A B : Q') : CReal :=
  CReal.add (CReal.mul (sinFull A) (cosFull B))
    (CReal.mul (cosFull A) (sinFull B))

/-- For `A, B ≥ 0`, the RHS approximation is the magnitude cross-product. -/
theorem sinProdPlus_approx_nonneg (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n : Nat) :
    (sinProdPlus A B).approx n
      = sinPartial A n * cosPartial B n + cosPartial A n * sinPartial B n := by
  have hsA : sinFull A = sinNN (Q'.abs A) (Q'.abs_nonneg A) := sinFull_of_nonneg hA
  have hsB : sinFull B = sinNN (Q'.abs B) (Q'.abs_nonneg B) := sinFull_of_nonneg hB
  show (sinFull A).approx n * (cosFull B).approx n
      + (cosFull A).approx n * (sinFull B).approx n = _
  rw [hsA, hsB]
  show sinPartial (Q'.abs A) n * cosPartial (Q'.abs B) n
      + cosPartial (Q'.abs A) n * sinPartial (Q'.abs B) n = _
  rw [abs_of_nonneg hA, abs_of_nonneg hB]

/-- **STEP B (nonnegative core).**  For `A, B ≥ 0`,
`CReal.Equiv (sinFull (A+B)) (sinProdPlus A B)`.  This is the `Q'`-core that
inhabits `TrigSineAddCReal.SinAddNonnegCore`. -/
theorem sin_add_equiv_nonneg (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B) :
    CReal.Equiv (sinFull (A + B)) (sinProdPlus A B) := by
  intro ε hε
  obtain ⟨N, hN⟩ := sinRemCorner_le A B hA hB ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hrem1, hrem2⟩ := hN n hn
  have hABnn : (0 : Q') ≤ A + B := Q'.zero_le_add A B hA hB
  have hABabs : Q'.abs (A + B) = A + B := abs_of_nonneg hABnn
  have hsAB : sinFull (A + B) = sinNN (Q'.abs (A + B)) (Q'.abs_nonneg (A + B)) :=
    sinFull_of_nonneg hABnn
  -- The nonneg approximant identity, as a clean standalone equation (avoids a
  -- dependent-motive rewrite of the proof-carrying `sinNN`).
  have hL : (sinFull (A + B)).approx n = sinPartial (A + B) n := by
    rw [hsAB]
    show sinPartial (Q'.abs (A + B)) n = sinPartial (A + B) n
    rw [hABabs]
  have hid := sinProd_eqv_sinPartial_add_remCorner A B n
  show (sinFull (A + B)).approx n ≤ (sinProdPlus A B).approx n + ε
      ∧ (sinProdPlus A B).approx n ≤ (sinFull (A + B)).approx n + ε
  rw [sinProdPlus_approx_nonneg A B hA hB, hL]
  -- Abbreviate the product sum `P`, the sum-partial `C`, the corner `R`.
  have hCeqv : (sinPartial (A + B) n).eqv
      ((sinPartial A n * cosPartial B n + cosPartial A n * sinPartial B n)
        + -(sinRemCorner A B n)) := by
    have e1 : ((sinPartial A n * cosPartial B n + cosPartial A n * sinPartial B n)
            + -(sinRemCorner A B n)).eqv
        ((sinPartial (A + B) n + sinRemCorner A B n) + -(sinRemCorner A B n)) :=
      Q'.add_eqv_congr_right _ _ (-(sinRemCorner A B n)) hid
    have e2 : ((sinPartial (A + B) n + sinRemCorner A B n) + -(sinRemCorner A B n)).eqv
        (sinPartial (A + B) n) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (sinPartial (A + B) n) (sinRemCorner A B n) (-(sinRemCorner A B n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (sinPartial (A + B) n) _ 0
          (Q'.add_neg_self_eqv (sinRemCorner A B n))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (sinPartial (A + B) n))
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2)
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hCeqv) ?_
    exact Q'.add_le_add_left _ (-(sinRemCorner A B n)) ε hrem2
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
    exact Q'.add_le_add_left (sinPartial (A + B) n) (sinRemCorner A B n) ε hrem1

end TrigAdd

/-- **The residual is discharged.**  `TrigSineAddCReal.SinAddNonnegCore` (whose
single field is exactly the type of `TrigAdd.sin_add_equiv_nonneg`, up to the
defeq of the two `sinProdPlus` copies) is now inhabited unconditionally.  Feeding
this to `TrigSineAddCReal.sinCD_add_of_core` gives the full CReal sine addition
law. -/
def sinAddNonnegCore : TrigSineAddCReal.SinAddNonnegCore :=
  ⟨TrigAdd.sin_add_equiv_nonneg⟩

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.TrigAdd.finSum_even_odd_split_even
#print axioms ConstructiveReals.TrigAdd.cosSinConvTerm_eqv
#print axioms ConstructiveReals.TrigAdd.sinCosConvTerm_eqv
#print axioms ConstructiveReals.TrigAdd.convAdd_eqv_cross
#print axioms ConstructiveReals.TrigAdd.sinTerm_eqv_negPow_term
#print axioms ConstructiveReals.TrigAdd.sinCosConv_addition
#print axioms ConstructiveReals.TrigAdd.sinDiag_eqv_sinPartial
#print axioms ConstructiveReals.TrigAdd.sinProd_eqv_sinPartial_add_remCorner
#print axioms ConstructiveReals.TrigAdd.sinCosCornerAbs_le
#print axioms ConstructiveReals.TrigAdd.cosSinCornerAbs_le
#print axioms ConstructiveReals.TrigAdd.sinRemCorner_le
#print axioms ConstructiveReals.TrigAdd.sin_add_equiv_nonneg
#print axioms ConstructiveReals.sinAddNonnegCore
