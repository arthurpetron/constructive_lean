/-
Constructive Type-level monotone/cofinal closure for an arbitrary rational
modulus.

No order property of the input `M : Q' → Nat` is assumed.  A running hull
samples `M` at canonical reciprocal tolerances and absorbs the diagonal index.
Composing that hull with abstract reciprocal-index data produces the antitone
rate required by `CReal.completeLimitFromRate`.
-/

import ConstructiveReals.CRealCompleteRate

namespace ConstructiveReals

open ConstructiveReals

namespace CReal

/-- Running maximum of the samples `M (invSucc k)`, with the diagonal index
itself absorbed.  Thus it is monotone and cofinal in `Nat`, even when `M` is
completely nonmonotone. -/
def modulusHull (M : Q' → Nat) : Nat → Nat
  | 0 => max (M (Q'.invSucc 0)) 0
  | k + 1 =>
      max (modulusHull M k)
        (max (M (Q'.invSucc (k + 1))) (k + 1))

theorem modulusHull_mono_succ (M : Q' → Nat) (k : Nat) :
    modulusHull M k ≤ modulusHull M (k + 1) :=
  Nat.le_max_left _ _

/-- The modulus hull is monotone in its natural-number index. -/
theorem modulusHull_mono (M : Q' → Nat) {a b : Nat} (hab : a ≤ b) :
    modulusHull M a ≤ modulusHull M b := by
  induction b with
  | zero =>
      exact Nat.le_of_eq (by cases Nat.le_zero.mp hab; rfl)
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · exact Nat.le_trans
          (ih (Nat.lt_succ_iff.mp hlt))
          (modulusHull_mono_succ M b)
      · exact Nat.le_of_eq (by cases Nat.le_antisymm hab hge; rfl)

/-- The hull dominates the arbitrary modulus at the reciprocal tolerance
sampled at its current diagonal index. -/
theorem modulus_le_modulusHull (M : Q' → Nat) (k : Nat) :
    M (Q'.invSucc k) ≤ modulusHull M k := by
  cases k with
  | zero => exact Nat.le_max_left _ _
  | succ k =>
      exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The hull is cofinal: its value at `k` is at least `k`. -/
theorem self_le_modulusHull (M : Q' → Nat) (k : Nat) :
    k ≤ modulusHull M k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- Every earlier reciprocal sample is dominated at every later hull stage. -/
theorem modulus_le_modulusHull_of_le (M : Q' → Nat)
    {a b : Nat} (hab : a ≤ b) :
    M (Q'.invSucc a) ≤ modulusHull M b :=
  Nat.le_trans (modulus_le_modulusHull M a)
    (modulusHull_mono M hab)

/-- Abstract data for a canonical reciprocal-tolerance index.

`index_spec` is the Archimedean fact needed to transfer a Cauchy estimate from
the sampled tolerance to the requested tolerance.  `index_antitone` is the
order fact needed to manufacture `MmonoPred`. -/
structure ReciprocalIndexData where
  index : Q' → Nat
  index_spec : ∀ ε : Q', (0 : Q') < ε →
    Q'.invSucc (index ε) ≤ ε
  index_antitone : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε →
    index ε ≤ index δ

/-- The monotone/cofinal rate obtained from an arbitrary modulus by sampling
its running hull at an antitone reciprocal-tolerance index. -/
def closedRate (A : ReciprocalIndexData) (M : Q' → Nat) (ε : Q') : Nat :=
  modulusHull M (A.index ε)

/-- The closed rate is antitone in tolerance, independently of any order
property of the original modulus. -/
theorem closedRate_mmonoPred (A : ReciprocalIndexData) (M : Q' → Nat) :
    MmonoPred (closedRate A M) := by
  intro ε δ hδ hδε
  exact modulusHull_mono M (A.index_antitone ε δ hδ hδε)

/-- The closed rate reaches the input modulus at the canonical smaller
tolerance `invSucc (A.index ε)`. -/
theorem modulus_le_closedRate (A : ReciprocalIndexData)
    (M : Q' → Nat) (ε : Q') :
    M (Q'.invSucc (A.index ε)) ≤ closedRate A M ε :=
  modulus_le_modulusHull M (A.index ε)

/-- The reciprocal index itself is absorbed by the closed rate. -/
theorem reciprocalIndex_le_closedRate (A : ReciprocalIndexData)
    (M : Q' → Nat) (ε : Q') :
    A.index ε ≤ closedRate A M ε :=
  self_le_modulusHull M (A.index ε)

/-- The tolerance sampled by the closed rate is no larger than the requested
positive tolerance. -/
theorem closedRate_sample_le (A : ReciprocalIndexData)
    (ε : Q') (hε : (0 : Q') < ε) :
    Q'.invSucc (A.index ε) ≤ ε :=
  A.index_spec ε hε

/-- An arbitrary `LeRatBound` transfers to the closed rate.

This does not require `M ε ≤ closedRate A M ε`: apply the old bound at
the smaller canonical tolerance and weaken the resulting rational bound to
`ε`. -/
theorem LeRatBound.closed
    {s : Nat → CReal} {M : Q' → Nat}
    (A : ReciprocalIndexData)
    (hM : LeRatBound s M) :
    LeRatBound s (closedRate A M) := by
  intro ε hε m n hm hn
  let η : Q' := Q'.invSucc (A.index ε)
  have hηpos : (0 : Q') < η := Q'.invSucc_pos (A.index ε)
  have hηε : η ≤ ε := A.index_spec ε hε
  have hMη : M η ≤ closedRate A M ε :=
    modulus_le_closedRate A M ε
  obtain ⟨hmn, hnm⟩ := hM η hηpos m n
    (Nat.le_trans hMη hm) (Nat.le_trans hMη hn)
  exact ⟨CReal.leRat_mono hmn hηε,
    CReal.leRat_mono hnm hηε⟩

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.CReal.modulusHull_mono
#print axioms ConstructiveReals.CReal.modulus_le_modulusHull
#print axioms ConstructiveReals.CReal.self_le_modulusHull
#print axioms ConstructiveReals.CReal.modulus_le_modulusHull_of_le
#print axioms ConstructiveReals.CReal.closedRate_mmonoPred
#print axioms ConstructiveReals.CReal.modulus_le_closedRate
#print axioms ConstructiveReals.CReal.reciprocalIndex_le_closedRate
#print axioms ConstructiveReals.CReal.closedRate_sample_le
#print axioms ConstructiveReals.CReal.LeRatBound.closed
