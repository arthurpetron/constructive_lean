/-
Constructive uniqueness of limits for asymptotically close
`CReal`-valued sequences.

This deliberately imports the existing limit/equality substrate and copies the
epsilon/4 budget from `CReal.Equiv_of_limit_of_equal`.  It uses no choice: all
three thresholds are eliminated only into the proposition `CReal.Equiv`.
-/

import ConstructiveReals.CRealAbs

namespace ConstructiveReals

open ConstructiveReals

namespace CReal

/-- If two `CReal`-valued sequences converge and become two-sided close, then
their limits are equivalent.

The closeness hypothesis has two independent eventualities: a sequence-stage
threshold and, for every sufficiently late sequence stage, an approximation
threshold.  This is the general `CReal` analogue of
`Equiv_of_ofQ'_limit_close` and is exactly the form needed for quotient
well-definedness of completed pairings. -/
theorem Equiv_of_limit_of_close
    {aSeq bSeq : Nat → CReal} {A B : CReal}
    (hA : ConvergesTo aSeq A)
    (hB : ConvergesTo bSeq B)
    (hclose : ∀ ε : Q', (0 : Q') < ε →
      ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
        ∃ Napx : Nat, ∀ n : Nat, Napx ≤ n →
          (aSeq N).approx n ≤ (bSeq N).approx n + ε ∧
          (bSeq N).approx n ≤ (aSeq N).approx n + ε) :
    CReal.Equiv A B := by
  intro ε hε
  let q : Q' := HalfPow.half * (HalfPow.half * ε)
  have hqpos : (0 : Q') < q :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  obtain ⟨NstA, hstA⟩ := hA q hqpos
  obtain ⟨NstB, hstB⟩ := hB q hqpos
  obtain ⟨NstClose, hstClose⟩ := hclose q hqpos
  let N : Nat := max (max NstA NstB) NstClose
  have hNA : NstA ≤ N :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hNB : NstB ≤ N :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hNClose : NstClose ≤ N := Nat.le_max_right _ _
  obtain ⟨NapxA, hclA⟩ := hstA N hNA
  obtain ⟨NapxB, hclB⟩ := hstB N hNB
  obtain ⟨NapxClose, hclClose⟩ := hstClose N hNClose
  refine ⟨max (max NapxA NapxB) NapxClose, fun n hn => ?_⟩
  have hnA : NapxA ≤ n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnB : NapxB ≤ n :=
    Nat.le_trans
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnClose : NapxClose ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hA1, hA2⟩ := hclA n hnA
  obtain ⟨hB1, hB2⟩ := hclB n hnB
  obtain ⟨hE1, hE2⟩ := hclClose n hnClose
  -- Three q-errors consume 3/4 of epsilon; the fourth quarter is harmless
  -- padding and lets us reuse the project's exact `two_halves` algebra.
  have chain3 : ∀ u v w z : Q',
      u ≤ v + q → v ≤ w + q → w ≤ z + q → u ≤ z + ε := by
    intro u v w z huv hvw hwz
    have s1 : u ≤ (w + q) + q :=
      Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
    have s2 : u ≤ ((z + q) + q) + q :=
      Q'.le_trans' _ _ _ s1
        (Q'.add_le_add_right _ _ q
          (Q'.add_le_add_right _ _ q hwz))
    refine Q'.le_trans' _ _ _ s2 ?_
    have hreassoc :
        (((z + q) + q) + q).eqv (z + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (z + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z q (q + q)) ?_
      exact Q'.add_eqv_congr_left z _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    have hpad :
        z + ((q + q) + q) ≤ z + (((q + q) + q) + q) :=
      Q'.add_le_add_left _ _ _
        (Q'.add_le_self_of_nonneg ((q + q) + q) q
          (Q'.le_of_lt hqpos))
    refine Q'.le_trans' _ _ _ hpad ?_
    refine Q'.le_of_eqv (Q'.add_eqv_congr_left z _ _ ?_)
    have hqq : (q + q).eqv (HalfPow.half * ε) :=
      ExpNeg.two_halves (HalfPow.half * ε)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (q + q) q q) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hqq hqq) ?_
    exact ExpNeg.two_halves ε
  refine ⟨?_, ?_⟩
  · exact chain3
      (A.approx n) ((aSeq N).approx n) ((bSeq N).approx n) (B.approx n)
      hA2 hE1 hB1
  · exact chain3
      (B.approx n) ((bSeq N).approx n) ((aSeq N).approx n) (A.approx n)
      hB2 hE2 hA1

#print axioms Equiv_of_limit_of_close

end CReal

end ConstructiveReals
