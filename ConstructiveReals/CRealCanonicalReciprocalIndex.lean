/-
# Canonical reciprocal-tolerance index for `CReal` rate closure

This leaf instantiates `CReal.ReciprocalIndexData` using the explicit
value-based index

    canonicalReciprocalIndex ε = ε.den / ε.num.toNat = ⌊1 / ε⌋

on positive constructive rationals.  The arithmetic is the constructive core
of `Continuum/ArctanTrigConverges.lean`'s proven `atMw` lemmas, moved behind a
Constructive-only import boundary so every consumer of `CRealRateClosure` can
use it without importing any Continuum theorem.

For positive `ε`, the index has exactly the two properties required by
`ReciprocalIndexData`:

* `invSucc (canonicalReciprocalIndex ε) ≤ ε`;
* `δ ≤ ε` implies
  `canonicalReciprocalIndex ε ≤ canonicalReciprocalIndex δ`.

The definition is total: at a nonpositive tolerance, `Int.toNat` and Nat
division give a harmless value.  The closure API asks for the two laws only at
positive tolerances, which is the mathematically relevant domain.

## Honesty / axiom boundary

There is no choice, quotient extraction, hidden Archimedean witness, `sorry`,
`admit`, `axiom`, `Classical.*`, or `native_decide`.  The index is executable
Type-level data.  The only expected logical dependencies of the public laws and
assembled datum are `[propext, Quot.sound]`, inherited from the existing
constructive `Nat`/`Int` arithmetic and casting infrastructure.
-/

import ConstructiveReals.CRealRateClosure

namespace ConstructiveReals

namespace CReal

/-! ## Local positive-numerator and floor-division arithmetic -/

/-- Positivity of the numerator propagates upward through rational order.

This is local because the rate-closure leaf needs only this one consequence of
the cross-multiplied definition of `Q'.le`. -/
private theorem positiveNumerator_of_le {q r : Q'}
    (hq : (0 : Int) < q.num) (hqr : q ≤ r) :
    (0 : Int) < r.num := by
  have hcross : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := hqr
  have hqd : (0 : Int) < (q.den : Int) := by
    exact_mod_cast q.den_pos
  have hrd : (0 : Int) < (r.den : Int) := by
    exact_mod_cast r.den_pos
  rcases Int.lt_or_le 0 r.num with hr | hr
  · exact hr
  · have hleft : (0 : Int) < q.num * (r.den : Int) :=
      Int.mul_pos hq hrd
    have hright : r.num * (q.den : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hr (Int.le_of_lt hqd)
    omega

/-- Nat floor-division monotonicity in cross-multiplied form.

For positive divisors `b,d`, the inequality `a*d ≤ c*b` implies
`a/b ≤ c/d`. -/
private theorem natDiv_le_natDiv_of_cross
    {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [Nat.le_div_iff_mul_le hd]
  have hdiv : a / b * b ≤ a := Nat.div_mul_le_self a b
  have hstep : (a / b * d) * b ≤ c * b := by
    have hreassoc : (a / b * d) * b = (a / b * b) * d := by
      rw [Nat.mul_right_comm]
    rw [hreassoc]
    exact Nat.le_trans (Nat.mul_le_mul_right d hdiv) hcross
  exact Nat.le_of_mul_le_mul_right hstep hb

/-! ## The executable reciprocal index and its two laws -/

/-- The canonical value-based reciprocal-tolerance index `⌊1/ε⌋`.

For a positive `Q'`, `num.toNat` is its positive numerator, so this is exactly
the Nat floor of `den/num`.  Unlike the raw denominator, it is invariant under
rescaling a rational presentation and antitone in the represented value. -/
def canonicalReciprocalIndex (ε : Q') : Nat :=
  ε.den / ε.num.toNat

/-- The canonical reciprocal sample is below the requested positive tolerance:
`1 / (⌊1/ε⌋ + 1) ≤ ε`. -/
theorem canonicalReciprocalIndex_invSucc_le
    (ε : Q') (hε : (0 : Q') < ε) :
    Q'.invSucc (canonicalReciprocalIndex ε) ≤ ε := by
  have hnum_pos : (0 : Int) < ε.num := num_pos_of_pos hε
  have hnumNat_pos : 0 < ε.num.toNat := by
    have hcast : (0 : Int) < (ε.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hnum_pos)]
      exact hnum_pos
    exact_mod_cast hcast
  have hnat :
      ε.den ≤ ε.num.toNat * (ε.den / ε.num.toNat + 1) := by
    have hdivmod :
        ε.num.toNat * (ε.den / ε.num.toNat)
            + ε.den % ε.num.toNat = ε.den :=
      Nat.div_add_mod ε.den ε.num.toNat
    have hrem : ε.den % ε.num.toNat < ε.num.toNat :=
      Nat.mod_lt ε.den hnumNat_pos
    calc
      ε.den =
          ε.num.toNat * (ε.den / ε.num.toNat)
            + ε.den % ε.num.toNat := hdivmod.symm
      _ ≤ ε.num.toNat * (ε.den / ε.num.toNat)
            + ε.num.toNat :=
        Nat.add_le_add_left (Nat.le_of_lt hrem) _
      _ = ε.num.toNat * (ε.den / ε.num.toNat + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  have hnumeq : ε.num = (ε.num.toNat : Int) :=
    (Int.toNat_of_nonneg (Int.le_of_lt hnum_pos)).symm
  show (Q'.invSucc (canonicalReciprocalIndex ε)).num * (ε.den : Int)
      ≤ ε.num * ((Q'.invSucc (canonicalReciprocalIndex ε)).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den, Int.one_mul, hnumeq]
  show (ε.den : Int) ≤
      (ε.num.toNat : Int)
        * ((ε.den / ε.num.toNat + 1 : Nat) : Int)
  exact_mod_cast hnat

/-- The canonical reciprocal index is antitone on positive tolerances. -/
theorem canonicalReciprocalIndex_antitone
    (ε δ : Q') (hδ : (0 : Q') < δ) (hδε : δ ≤ ε) :
    canonicalReciprocalIndex ε ≤ canonicalReciprocalIndex δ := by
  have hδnum : (0 : Int) < δ.num := num_pos_of_pos hδ
  have hεnum : (0 : Int) < ε.num := positiveNumerator_of_le hδnum hδε
  have hδNat : 0 < δ.num.toNat := by
    have hcast : (0 : Int) < (δ.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hδnum)]
      exact hδnum
    exact_mod_cast hcast
  have hεNat : 0 < ε.num.toNat := by
    have hcast : (0 : Int) < (ε.num.toNat : Int) := by
      rw [Int.toNat_of_nonneg (Int.le_of_lt hεnum)]
      exact hεnum
    exact_mod_cast hcast
  have hcross : δ.num * (ε.den : Int) ≤ ε.num * (δ.den : Int) := hδε
  have hNatCross : δ.num.toNat * ε.den ≤ ε.num.toNat * δ.den := by
    have hδcast : δ.num = (δ.num.toNat : Int) :=
      (Int.toNat_of_nonneg (Int.le_of_lt hδnum)).symm
    have hεcast : ε.num = (ε.num.toNat : Int) :=
      (Int.toNat_of_nonneg (Int.le_of_lt hεnum)).symm
    rw [hδcast, hεcast] at hcross
    exact_mod_cast hcross
  show ε.den / ε.num.toNat ≤ δ.den / δ.num.toNat
  apply natDiv_le_natDiv_of_cross hεNat hδNat
  rw [Nat.mul_comm ε.den δ.num.toNat,
    Nat.mul_comm δ.den ε.num.toNat]
  exact hNatCross

/-! ## The concrete `ReciprocalIndexData` package -/

/-- Canonical executable reciprocal-index data for closing any arbitrary
`CReal.LeRatBound` modulus into an antitone, cofinal rate. -/
def canonicalReciprocalIndexData : ReciprocalIndexData where
  index := canonicalReciprocalIndex
  index_spec := canonicalReciprocalIndex_invSucc_le
  index_antitone := canonicalReciprocalIndex_antitone

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.CReal.canonicalReciprocalIndex_invSucc_le
#print axioms ConstructiveReals.CReal.canonicalReciprocalIndex_antitone
#print axioms ConstructiveReals.CReal.canonicalReciprocalIndexData
