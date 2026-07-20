/-
# `cosC` / `sinC` : constructive `cos` / `sin` of a **CReal** argument

`Constructive/Trig.lean` ships `cosNN`/`sinNN : (x : Q') → 0 ≤ x → CReal` (the
alternating cos/sin series at a *rational* angle) and `Constructive/TrigAdd.lean`
adds the signed even/odd extension, the small-angle bounds, and the addition law.
This module lifts cos/sin to an **irrational (CReal) angle** `w`, exactly as
`CRealExp.expNegC` lifts `e^{−·}` from a rational to a CReal exponent: the limit
`cosC w := lim_k cos(w.approx k)` assembled with the completion backbone
`CReal.completeLimitCauchy` (`ModCauchyEv`).

The keystone new analytic input is the **partial-sum Lipschitz bound**

    |cosPartial a n − cosPartial b n| ≤ |a − b| · 3          (`cosPartialDiff_le`)

(and the sine analogue), the trig contraction modulus the completion needs.  It
is obtained WITHOUT re-deriving a trig termwise-difference estimate: the cosine
term magnitudes are the *even* subsequence of the exponential magnitudes
(`term x (2k) ≈ termAbs x (2k)`, `TrigAdd.term_even_eq_abs`), so the per-term
difference `|cosTerm a k − cosTerm b k|` is dominated by the exponential
`ExpNeg.termDiff_le` bound, and the summed Lipschitz constant is the *even
subsum* of `ExpNeg.sumBound`, itself `≤ 3` (`ExpNeg.sumBound_le_three`).  The
sine analogue uses the *odd* subsequence (`term_odd_eq_neg_abs`).

The argument `w` must have `0 ≤ w.approx k ≤ 1` (the regime in which the
exponential tail engine applies), carried as `Type`-level data together with
`w`'s own Cauchy modulus `Mw` — the same discipline `expNegC` enforces.

# What is delivered (genuine, axiom-clean)

  * `cosC` / `sinC : CReal → CReal` — cos/sin of a CReal angle in `[0,1]`, with
    the completion modulus, and `cosC_converges` / `sinC_converges`
    (`ConvergesTo (fun k => cos (w.approx k)) (cosC w …)`).
  * `cosPartialDiff_le` / `sinPartialDiff_le` — the trig partial-sum Lipschitz
    bound (the reusable contraction modulus).
  * `cosNN_zero_eqv_one` (`cos 0 ≃ 1`) and `sinNN_zero_eqv_zero` (`sin 0 ≃ 0`) —
    the grounding values at the zero angle.

# Honest residuals (named, NOT faked)

  * The `cos`/`sin` of a CReal *multiple-of-π* angle (`sinC (k·π) ≃ 0`) needed to
    discharge `Continuum.HaarClassIntegral.AngleCosineIntegral` requires
    connecting the Machin-series `Pi.pi` to the trig-series `sin` (i.e.
    `sin(π) = 0` for THIS π), a genuine analytic identity NOT available "by
    construction" from the Machin definition; it is left as the sharp residual.
  * The general-CReal range restriction `w.approx ∈ [0,1]` (matching `expNegC`);
    enough for OS2's `cos(π/(M+1))` at `M ≥ 3` (`π/4 < 1`).

# Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (only via reused `Nat`/`Int`/`Q'` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.  Moduli are `Type`-level data.
-/

import ConstructiveReals.TrigAdd
import ConstructiveReals.CRealExp

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.Trig

namespace CRealTrig

/-! ## 1. The trig Lipschitz constants — even / odd subsums of `ExpNeg.sumBound`

`cosSumBound n = Σ_{j<n} (2j)·termAbs 1 (2j)` (even-index subsum) and
`sinSumBound n = Σ_{j<n} (2j+1)·termAbs 1 (2j+1)` (odd-index subsum).  Both are
dominated by `ExpNeg.sumBound (2n) ≤ 3`, giving the uniform Lipschitz constant. -/

/-- Even-index subsum of the weighted magnitude sum. -/
def cosSumBound : Nat → Q'
  | 0 => 0
  | k + 1 => cosSumBound k + Q'.ofNat (2 * k) * ExpNeg.termAbs 1 (2 * k)

/-- Odd-index subsum of the weighted magnitude sum. -/
def sinSumBound : Nat → Q'
  | 0 => 0
  | k + 1 => sinSumBound k + Q'.ofNat (2 * k + 1) * ExpNeg.termAbs 1 (2 * k + 1)

theorem cosSumBound_nonneg : ∀ n, (0 : Q') ≤ cosSumBound n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _ (cosSumBound_nonneg n)
        (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (2 * n))
          (ExpNeg.termAbs_nonneg 1 (by decide) (2 * n)))

theorem sinSumBound_nonneg : ∀ n, (0 : Q') ≤ sinSumBound n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _ (sinSumBound_nonneg n)
        (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (2 * n + 1))
          (ExpNeg.termAbs_nonneg 1 (by decide) (2 * n + 1)))

/-- The even subsum is `≤ ExpNeg.sumBound (2n)`. -/
theorem cosSumBound_le_sumBound : ∀ n, cosSumBound n ≤ ExpNeg.sumBound (2 * n)
  | 0 => by
      show (0 : Q') ≤ ExpNeg.sumBound 0
      exact Q'.le_refl' 0
  | n + 1 => by
      have ih := cosSumBound_le_sumBound n
      have he : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      show cosSumBound n + Q'.ofNat (2 * n) * ExpNeg.termAbs 1 (2 * n)
          ≤ ExpNeg.sumBound (2 * (n + 1))
      rw [he]
      -- sumBound ((2n+1)+1) = sumBound (2n+1) + (2n+1)·termAbs 1 (2n+1);
      -- sumBound (2n+1) = sumBound (2n) + (2n)·termAbs 1 (2n)  (both defeq)
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ih) ?_
      -- sumBound (2n) + (2n)·termAbs 1 (2n) = sumBound (2n+1) ≤ sumBound ((2n+1)+1)
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (2 * n + 1))
          (ExpNeg.termAbs_nonneg 1 (by decide) (2 * n + 1)))

/-- The odd subsum is `≤ ExpNeg.sumBound (2n)`. -/
theorem sinSumBound_le_sumBound : ∀ n, sinSumBound n ≤ ExpNeg.sumBound (2 * n)
  | 0 => by
      show (0 : Q') ≤ ExpNeg.sumBound 0
      exact Q'.le_refl' 0
  | n + 1 => by
      have ih := sinSumBound_le_sumBound n
      have he : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      show sinSumBound n + Q'.ofNat (2 * n + 1) * ExpNeg.termAbs 1 (2 * n + 1)
          ≤ ExpNeg.sumBound (2 * (n + 1))
      rw [he]
      -- reduce to sinSumBound n ≤ sumBound (2n+1), then add the matching odd term
      refine Q'.add_le_add_right _ _ _ ?_
      -- sinSumBound n ≤ sumBound (2n) ≤ sumBound (2n+1)
      refine Q'.le_trans' _ _ _ ih ?_
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' (2 * n))
          (ExpNeg.termAbs_nonneg 1 (by decide) (2 * n)))

theorem cosSumBound_le_three (n : Nat) : cosSumBound n ≤ Q'.ofNat 3 :=
  Q'.le_trans' _ _ _ (cosSumBound_le_sumBound n) (ExpNeg.sumBound_le_three (2 * n))

theorem sinSumBound_le_three (n : Nat) : sinSumBound n ≤ Q'.ofNat 3 :=
  Q'.le_trans' _ _ _ (sinSumBound_le_sumBound n) (ExpNeg.sumBound_le_three (2 * n))

/-! ## 2. The per-term difference bounds

`|cosTerm a k − cosTerm b k| ≤ d·((2k)·termAbs 1 (2k))` for `0 ≤ a,b ≤ 1`,
`|a−b| ≤ d`.  `cosTerm x k = negPow k · termAbs x (2k)`, and the magnitude
difference `|termAbs a (2k) − termAbs b (2k)|` equals `|term a (2k) − term b (2k)|`
via the even-index exp bridge (`term_even_eq_abs`), whence `ExpNeg.termDiff_le`. -/

/-- **Cosine per-term Lipschitz step.** -/
theorem cosTermDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) (j : Nat) :
    Q'.abs (Trig.cosTerm a j + -(Trig.cosTerm b j))
      ≤ d * (Q'.ofNat (2 * j) * ExpNeg.termAbs 1 (2 * j)) := by
  -- cosTerm a j + −(cosTerm b j) ≈ negPow j · (termAbs a (2j) + −(termAbs b (2j)))
  have hfac : (Trig.cosTerm a j + -(Trig.cosTerm b j)).eqv
      (Trig.negPow j * (ExpNeg.termAbs a (2 * j) + -(ExpNeg.termAbs b (2 * j)))) := by
    show (Trig.negPow j * ExpNeg.termAbs a (2 * j)
        + -(Trig.negPow j * ExpNeg.termAbs b (2 * j))).eqv _
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Trig.negPow j) (ExpNeg.termAbs a (2 * j)) (-(ExpNeg.termAbs b (2 * j)))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv (Trig.negPow j) (ExpNeg.termAbs b (2 * j)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hfac)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le (Trig.negPow j)
      (ExpNeg.termAbs a (2 * j) + -(ExpNeg.termAbs b (2 * j)))) ?_
  -- |negPow j|·|z| ≤ 1·|z| = |z|
  have hz : Q'.abs (Trig.negPow j)
        * Q'.abs (ExpNeg.termAbs a (2 * j) + -(ExpNeg.termAbs b (2 * j)))
      ≤ Q'.abs (ExpNeg.termAbs a (2 * j) + -(ExpNeg.termAbs b (2 * j))) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ 1 _ (Trig.abs_negPow_le_one j) (Q'.abs_nonneg _)) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv _)
  refine Q'.le_trans' _ _ _ hz ?_
  -- |termAbs a (2j) − termAbs b (2j)| ≈ |term a (2j) − term b (2j)|
  have hswap : (ExpNeg.termAbs a (2 * j) + -(ExpNeg.termAbs b (2 * j))).eqv
      (ExpNeg.term a (2 * j) + -(ExpNeg.term b (2 * j))) :=
    Q'.add_eqv_congr' (Q'.eqv_symm (TrigAdd.term_even_eq_abs a j))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (TrigAdd.term_even_eq_abs b j)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hswap)) ?_
  exact ExpNeg.termDiff_le ha0 ha1 hb0 hb1 hd hab hba (2 * j)

/-- **Sine per-term Lipschitz step.** -/
theorem sinTermDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) (j : Nat) :
    Q'.abs (Trig.sinTerm a j + -(Trig.sinTerm b j))
      ≤ d * (Q'.ofNat (2 * j + 1) * ExpNeg.termAbs 1 (2 * j + 1)) := by
  have hfac : (Trig.sinTerm a j + -(Trig.sinTerm b j)).eqv
      (Trig.negPow j * (ExpNeg.termAbs a (2 * j + 1) + -(ExpNeg.termAbs b (2 * j + 1)))) := by
    show (Trig.negPow j * ExpNeg.termAbs a (2 * j + 1)
        + -(Trig.negPow j * ExpNeg.termAbs b (2 * j + 1))).eqv _
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Trig.negPow j) (ExpNeg.termAbs a (2 * j + 1))
        (-(ExpNeg.termAbs b (2 * j + 1)))) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv (Trig.negPow j) (ExpNeg.termAbs b (2 * j + 1)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hfac)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le (Trig.negPow j)
      (ExpNeg.termAbs a (2 * j + 1) + -(ExpNeg.termAbs b (2 * j + 1)))) ?_
  have hz : Q'.abs (Trig.negPow j)
        * Q'.abs (ExpNeg.termAbs a (2 * j + 1) + -(ExpNeg.termAbs b (2 * j + 1)))
      ≤ Q'.abs (ExpNeg.termAbs a (2 * j + 1) + -(ExpNeg.termAbs b (2 * j + 1))) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ 1 _ (Trig.abs_negPow_le_one j) (Q'.abs_nonneg _)) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv _)
  refine Q'.le_trans' _ _ _ hz ?_
  -- termAbs a (2j+1) ≈ −(term a (2j+1)), so the magnitude difference ≈ −(term difference)
  have hTa : (ExpNeg.termAbs a (2 * j + 1)).eqv (-(ExpNeg.term a (2 * j + 1))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.neg_neg_eqv (ExpNeg.termAbs a (2 * j + 1)))) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm (TrigAdd.term_odd_eq_neg_abs a j))
  have hTb : (ExpNeg.termAbs b (2 * j + 1)).eqv (-(ExpNeg.term b (2 * j + 1))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.neg_neg_eqv (ExpNeg.termAbs b (2 * j + 1)))) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm (TrigAdd.term_odd_eq_neg_abs b j))
  have hswap : (ExpNeg.termAbs a (2 * j + 1) + -(ExpNeg.termAbs b (2 * j + 1))).eqv
      (-(ExpNeg.term a (2 * j + 1) + -(ExpNeg.term b (2 * j + 1)))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hTa (Q'.neg_eqv_congr _ _ hTb)) ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv (ExpNeg.term a (2 * j + 1)) (-(ExpNeg.term b (2 * j + 1))))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hswap)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_neg' (ExpNeg.term a (2 * j + 1) + -(ExpNeg.term b (2 * j + 1))))) ?_
  exact ExpNeg.termDiff_le ha0 ha1 hb0 hb1 hd hab hba (2 * j + 1)

/-! ## 3. The partial-sum Lipschitz bounds (summed per-term bounds) -/

/-- **Cosine partial-sum Lipschitz.**  `|cosPartial a n − cosPartial b n| ≤ d·cosSumBound n`. -/
theorem cosPartialDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) :
    ∀ n, Q'.abs (Trig.cosPartial a n + -(Trig.cosPartial b n)) ≤ d * cosSumBound n
  | 0 => by
      show Q'.abs ((0 : Q') + -(0 : Q')) ≤ d * cosSumBound 0
      exact Q'.le_trans' _ _ _ (by decide : Q'.abs ((0 : Q') + -(0 : Q')) ≤ (0 : Q'))
        (Q'.mul_nonneg _ _ hd (cosSumBound_nonneg 0))
  | n + 1 => by
      have IH := cosPartialDiff_le ha0 ha1 hb0 hb1 hd hab hba n
      have hre : ((Trig.cosPartial a n + Trig.cosTerm a n)
            + -(Trig.cosPartial b n + Trig.cosTerm b n)).eqv
          ((Trig.cosPartial a n + -(Trig.cosPartial b n))
            + (Trig.cosTerm a n + -(Trig.cosTerm b n))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (Trig.cosPartial b n) (Trig.cosTerm b n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Trig.cosPartial a n) (Trig.cosTerm a n)
          (-(Trig.cosPartial b n) + -(Trig.cosTerm b n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.cosPartial a n) _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (Trig.cosTerm a n) (-(Trig.cosPartial b n))
            (-(Trig.cosTerm b n))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.cosPartial a n) _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (Trig.cosTerm a n)
            (-(Trig.cosPartial b n))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.cosPartial a n) _ _
          (Q'.add_assoc_eqv (-(Trig.cosPartial b n)) (Trig.cosTerm a n) (-(Trig.cosTerm b n)))) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv (Trig.cosPartial a n) (-(Trig.cosPartial b n)) _)
      show Q'.abs (Trig.cosPartial a n + Trig.cosTerm a n
          + -(Trig.cosPartial b n + Trig.cosTerm b n)) ≤ d * cosSumBound (n + 1)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hre)) ?_
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
      refine Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2 IH (cosTermDiff_le ha0 ha1 hb0 hb1 hd hab hba n)) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_add_eqv d (cosSumBound n) (Q'.ofNat (2 * n) * ExpNeg.termAbs 1 (2 * n))))

/-- **Sine partial-sum Lipschitz.**  `|sinPartial a n − sinPartial b n| ≤ d·sinSumBound n`. -/
theorem sinPartialDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) :
    ∀ n, Q'.abs (Trig.sinPartial a n + -(Trig.sinPartial b n)) ≤ d * sinSumBound n
  | 0 => by
      show Q'.abs ((0 : Q') + -(0 : Q')) ≤ d * sinSumBound 0
      exact Q'.le_trans' _ _ _ (by decide : Q'.abs ((0 : Q') + -(0 : Q')) ≤ (0 : Q'))
        (Q'.mul_nonneg _ _ hd (sinSumBound_nonneg 0))
  | n + 1 => by
      have IH := sinPartialDiff_le ha0 ha1 hb0 hb1 hd hab hba n
      have hre : ((Trig.sinPartial a n + Trig.sinTerm a n)
            + -(Trig.sinPartial b n + Trig.sinTerm b n)).eqv
          ((Trig.sinPartial a n + -(Trig.sinPartial b n))
            + (Trig.sinTerm a n + -(Trig.sinTerm b n))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (Trig.sinPartial b n) (Trig.sinTerm b n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Trig.sinPartial a n) (Trig.sinTerm a n)
          (-(Trig.sinPartial b n) + -(Trig.sinTerm b n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.sinPartial a n) _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (Trig.sinTerm a n) (-(Trig.sinPartial b n))
            (-(Trig.sinTerm b n))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.sinPartial a n) _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (Trig.sinTerm a n)
            (-(Trig.sinPartial b n))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Trig.sinPartial a n) _ _
          (Q'.add_assoc_eqv (-(Trig.sinPartial b n)) (Trig.sinTerm a n) (-(Trig.sinTerm b n)))) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv (Trig.sinPartial a n) (-(Trig.sinPartial b n)) _)
      show Q'.abs (Trig.sinPartial a n + Trig.sinTerm a n
          + -(Trig.sinPartial b n + Trig.sinTerm b n)) ≤ d * sinSumBound (n + 1)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hre)) ?_
      refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
      refine Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2 IH (sinTermDiff_le ha0 ha1 hb0 hb1 hd hab hba n)) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm
        (Q'.mul_add_eqv d (sinSumBound n) (Q'.ofNat (2 * n + 1) * ExpNeg.termAbs 1 (2 * n + 1))))

/-! ## 4. The explicit rational-angle Cauchy moduli (the inner regularity)

`cosNN`/`sinNN` are Cauchy with the explicit modulus `Trig.trigModulus`; exposed
as standalone lemmas so the completion can consume them as `Type`-level data. -/

theorem cosNN_cauchy_explicit (x : Q') (hx : (0 : Q') ≤ x) (ε : Q') (hε : (0 : Q') < ε) :
    ∀ m n : Nat, Trig.trigModulus x ε ≤ m → Trig.trigModulus x ε ≤ n →
      Trig.cosPartial x m ≤ Trig.cosPartial x n + ε
        ∧ Trig.cosPartial x n ≤ Trig.cosPartial x m + ε := by
  intro m n hm hn
  have dir : ∀ k l : Nat, Trig.trigModulus x ε ≤ k → k ≤ l →
      Trig.cosPartial x l ≤ Trig.cosPartial x k + ε
        ∧ Trig.cosPartial x k ≤ Trig.cosPartial x l + ε := by
    intro k l hk hkl
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have htail : Trig.cosBlockAbs x k d ≤ ε := Trig.cosBlock_bound x hx ε hε k hk d
    exact ⟨Q'.le_trans' _ _ _ (Trig.cos_block_upper x hx k d)
             (Q'.add_le_add_left (Trig.cosPartial x k) (Trig.cosBlockAbs x k d) ε htail),
           Q'.le_trans' _ _ _ (Trig.cos_block_lower x hx k d)
             (Q'.add_le_add_left (Trig.cosPartial x (k + d)) (Trig.cosBlockAbs x k d) ε htail)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
  · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

theorem sinNN_cauchy_explicit (x : Q') (hx : (0 : Q') ≤ x) (ε : Q') (hε : (0 : Q') < ε) :
    ∀ m n : Nat, Trig.trigModulus x ε ≤ m → Trig.trigModulus x ε ≤ n →
      Trig.sinPartial x m ≤ Trig.sinPartial x n + ε
        ∧ Trig.sinPartial x n ≤ Trig.sinPartial x m + ε := by
  intro m n hm hn
  have dir : ∀ k l : Nat, Trig.trigModulus x ε ≤ k → k ≤ l →
      Trig.sinPartial x l ≤ Trig.sinPartial x k + ε
        ∧ Trig.sinPartial x k ≤ Trig.sinPartial x l + ε := by
    intro k l hk hkl
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have htail : Trig.sinBlockAbs x k d ≤ ε := Trig.sinBlock_bound x hx ε hε k hk d
    exact ⟨Q'.le_trans' _ _ _ (Trig.sin_block_upper x hx k d)
             (Q'.add_le_add_left (Trig.sinPartial x k) (Trig.sinBlockAbs x k d) ε htail),
           Q'.le_trans' _ _ _ (Trig.sin_block_lower x hx k d)
             (Q'.add_le_add_left (Trig.sinPartial x (k + d)) (Trig.sinBlockAbs x k d) ε htail)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
  · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-! ## 5. The completion data and `cosC` / `sinC`

The sequence `k ↦ cosNN (w.approx k)` is `ModCauchyEv`: the OUTER modulus is `w`'s
own modulus composed with the partial-sum Lipschitz (`cosPartialDiff_le` +
`cosSumBound_le_three`, all-`k` so `boundK = 0`); the INNER regularity is
`cosNN_cauchy_explicit` at `trigModulus`. -/

/-- The `ModCauchyEv` datum for `k ↦ cosNN (w.approx k)`. -/
def cosCMC (w : CReal) (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (Mw : Q' → Nat)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    CReal.ModCauchyEv (fun k => Trig.cosNN (w.approx k) (hpos k)) where
  M := fun ε => Mw (ε * Q'.mkPos 1 3 (by decide))
  reg := fun i ε => Trig.trigModulus (w.approx i) ε
  boundK := fun _ _ _ => 0
  bound := by
    intro ε hε m n hm hn k _
    have hd : (0 : Q') ≤ ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (ExpNeg.third_pos hε)
    obtain ⟨hab, hba⟩ := hMw (ε * Q'.mkPos 1 3 (by decide)) (ExpNeg.third_pos hε) m n hm hn
    have habs : Q'.abs (Trig.cosPartial (w.approx m) k + -(Trig.cosPartial (w.approx n) k)) ≤ ε :=
      Q'.le_trans' _ _ _
        (cosPartialDiff_le (hpos m) (hle1 m) (hpos n) (hle1 n) hd hab hba k)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (cosSumBound_le_three k) hd)
          (Q'.le_of_eqv (ExpNeg.third_mul_three ε)))
    exact ⟨ExpNeg.le_add_of_abs_sub_le habs,
      ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm (Trig.cosPartial (w.approx n) k)
          (Trig.cosPartial (w.approx m) k))) habs)⟩
  regular := fun i ε hε p qq hp hqq =>
    cosNN_cauchy_explicit (w.approx i) (hpos i) ε hε p qq hp hqq
  Mmono := fun ε δ hδ hδε =>
    hMwmono _ _ (ExpNeg.third_pos hδ)
      (Q'.mul_le_mul_of_nonneg_right δ ε _ hδε (Q'.le_of_lt (Q'.invSucc_pos 2)))

/-- The `ModCauchyEv` datum for `k ↦ sinNN (w.approx k)`. -/
def sinCMC (w : CReal) (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (Mw : Q' → Nat)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    CReal.ModCauchyEv (fun k => Trig.sinNN (w.approx k) (hpos k)) where
  M := fun ε => Mw (ε * Q'.mkPos 1 3 (by decide))
  reg := fun i ε => Trig.trigModulus (w.approx i) ε
  boundK := fun _ _ _ => 0
  bound := by
    intro ε hε m n hm hn k _
    have hd : (0 : Q') ≤ ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (ExpNeg.third_pos hε)
    obtain ⟨hab, hba⟩ := hMw (ε * Q'.mkPos 1 3 (by decide)) (ExpNeg.third_pos hε) m n hm hn
    have habs : Q'.abs (Trig.sinPartial (w.approx m) k + -(Trig.sinPartial (w.approx n) k)) ≤ ε :=
      Q'.le_trans' _ _ _
        (sinPartialDiff_le (hpos m) (hle1 m) (hpos n) (hle1 n) hd hab hba k)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (sinSumBound_le_three k) hd)
          (Q'.le_of_eqv (ExpNeg.third_mul_three ε)))
    exact ⟨ExpNeg.le_add_of_abs_sub_le habs,
      ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm (Trig.sinPartial (w.approx n) k)
          (Trig.sinPartial (w.approx m) k))) habs)⟩
  regular := fun i ε hε p qq hp hqq =>
    sinNN_cauchy_explicit (w.approx i) (hpos i) ε hε p qq hp hqq
  Mmono := fun ε δ hδ hδε =>
    hMwmono _ _ (ExpNeg.third_pos hδ)
      (Q'.mul_le_mul_of_nonneg_right δ ε _ hδε (Q'.le_of_lt (Q'.invSucc_pos 2)))

/-- **`cos w` for a CReal argument** `w` with `0 ≤ w.approx k ≤ 1` and an explicit
`Type`-level modulus `Mw` for `w`.  The constructive limit of `cos (w.approx k)`. -/
def cosC (w : CReal) (Mw : Q' → Nat) (hpos : ∀ k, (0 : Q') ≤ w.approx k)
    (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) : CReal :=
  CReal.completeLimitCauchy (fun k => Trig.cosNN (w.approx k) (hpos k))
    (cosCMC w hpos hle1 Mw hMw hMwmono)

/-- **`sin w` for a CReal argument** `w`. -/
def sinC (w : CReal) (Mw : Q' → Nat) (hpos : ∀ k, (0 : Q') ≤ w.approx k)
    (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) : CReal :=
  CReal.completeLimitCauchy (fun k => Trig.sinNN (w.approx k) (hpos k))
    (sinCMC w hpos hle1 Mw hMw hMwmono)

/-- `cosC w` is the limit of the sequence `k ↦ cos (w.approx k)`. -/
theorem cosC_converges (w : CReal) (Mw : Q' → Nat) (hpos : ∀ k, (0 : Q') ≤ w.approx k)
    (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    CReal.ConvergesTo (fun k => Trig.cosNN (w.approx k) (hpos k))
      (cosC w Mw hpos hle1 hMw hMwmono) :=
  CReal.convergesTo_completeLimitCauchy _ (cosCMC w hpos hle1 Mw hMw hMwmono)

/-- `sinC w` is the limit of the sequence `k ↦ sin (w.approx k)`. -/
theorem sinC_converges (w : CReal) (Mw : Q' → Nat) (hpos : ∀ k, (0 : Q') ≤ w.approx k)
    (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    CReal.ConvergesTo (fun k => Trig.sinNN (w.approx k) (hpos k))
      (sinC w Mw hpos hle1 hMw hMwmono) :=
  CReal.convergesTo_completeLimitCauchy _ (sinCMC w hpos hle1 Mw hMw hMwmono)

/-! ## 6. Grounding values at the zero angle: `cos 0 ≃ 1`, `sin 0 ≃ 0`

Rational-level values (the CReal-argument evaluation at `czero` reduces to these
plus the constant-sequence limit).  `sinPartial 0 n ≃ 0` for every `n`
(`TrigAdd.sinPartial_zero_eqv`); `cosPartial 0 n ≃ 1` for `n ≥ 1` (the constant
term is `1`, all later magnitude terms vanish at the zero angle). -/

/-- `cosPartial 0 (m+1) ≃ 1`. -/
theorem cosPartial_zero_eqv_one : ∀ m, (Trig.cosPartial (0 : Q') (m + 1)).eqv 1
  | 0 => by rw [Trig.cosPartial_one]; exact Q'.eqv_refl 1
  | m + 1 => by
      -- cosPartial 0 (m+2) = cosPartial 0 (m+1) + cosTerm 0 (m+1) ≃ 1 + 0 ≃ 1
      show (Trig.cosPartial (0 : Q') (m + 1) + Trig.cosTerm (0 : Q') (m + 1)).eqv 1
      have hterm : (Trig.cosTerm (0 : Q') (m + 1)).eqv 0 := by
        show (Trig.negPow (m + 1) * ExpNeg.termAbs (0 : Q') (2 * (m + 1))).eqv 0
        have he : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
        rw [he]
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Trig.negPow (m + 1)) _ 0
            (TrigAdd.termAbs_zero_succ_eqv (2 * m + 1))) ?_
        exact Q'.mul_zero_eqv (Trig.negPow (m + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (cosPartial_zero_eqv_one m) hterm) ?_
      show ((1 : Q') + 0).eqv 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-- **`cos 0 ≃ 1`** (the constant value). -/
theorem cosNN_zero_eqv_one : CReal.Equiv (Trig.cosNN (0 : Q') (by decide)) (CReal.ofQ' (1 : Q')) := by
  intro ε hε
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have he : (Trig.cosPartial (0 : Q') (p + 1)).eqv 1 := cosPartial_zero_eqv_one p
  show Trig.cosPartial (0 : Q') (p + 1) ≤ (1 : Q') + ε
      ∧ (1 : Q') ≤ Trig.cosPartial (0 : Q') (p + 1) + ε
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε))
      (Q'.add_le_add_right 1 (Trig.cosPartial (0 : Q') (p + 1)) ε (Q'.ge_of_eqv he))

/-- **`sin 0 ≃ 0`** (the constant value). -/
theorem sinNN_zero_eqv_zero : CReal.Equiv (Trig.sinNN (0 : Q') (by decide)) CReal.czero :=
  TrigAdd.equiv_of_approx_eqv (fun n => TrigAdd.sinPartial_zero_eqv n)

end CRealTrig

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CRealTrig.cosSumBound_le_three
#print axioms ConstructiveReals.CRealTrig.sinSumBound_le_three
#print axioms ConstructiveReals.CRealTrig.cosTermDiff_le
#print axioms ConstructiveReals.CRealTrig.sinTermDiff_le
#print axioms ConstructiveReals.CRealTrig.cosPartialDiff_le
#print axioms ConstructiveReals.CRealTrig.sinPartialDiff_le
#print axioms ConstructiveReals.CRealTrig.cosNN_cauchy_explicit
#print axioms ConstructiveReals.CRealTrig.sinNN_cauchy_explicit
#print axioms ConstructiveReals.CRealTrig.cosC
#print axioms ConstructiveReals.CRealTrig.sinC
#print axioms ConstructiveReals.CRealTrig.cosC_converges
#print axioms ConstructiveReals.CRealTrig.sinC_converges
#print axioms ConstructiveReals.CRealTrig.cosNN_zero_eqv_one
#print axioms ConstructiveReals.CRealTrig.sinNN_zero_eqv_zero
