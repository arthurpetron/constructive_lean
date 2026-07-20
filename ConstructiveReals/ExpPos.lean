/-
Minimal constructive `e^{+x}` for `x ≥ 0`, with monotone-increasing partial
sums — the substrate the U.5 soundness (`e^{-x} ≤ 1/(1+x)`) and the U.6
character-tail need.

`e^x = Σ_{k≥0} x^k/k!` has **all-positive** terms for `x ≥ 0`, so its partial
sums increase monotonically to the limit.  The term `x^k/k!` is *exactly*
`ExpNeg.termAbs x k` (the magnitude term), and the partial sum
`Σ_{k<n} x^k/k!` is `ExpNeg.partialSumAbs x n`; the Cauchy modulus reuses
`ExpNeg`'s geometric tail bounds (`blockAbs_le`, `expNeg_tail_bound`).  So
`expPos` is built entirely from the existing positive-series machinery, and is
*cleaner* than `expNeg` (monotone ⇒ one Cauchy direction is trivial).

Lower bounds use `geRat` (the lower-bound dual of `CRealLe.leRat`): the
one-slack `CReal.le` is too weak here (it fails at small `n`, where the partial
sum is still far from the limit), but every partial sum *is* a genuine lower
bound for the monotone limit — `geRat (expPos x) (partialSumAbs x N)` — and in
particular `1 + x ≤ e^x` (`partialSumAbs x 2 = 1 + x`).

# Axiom-gate (see README: axiom policy)

`[propext]` only.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.ExpNeg

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.HalfPow
open ConstructiveReals.RatNat
open ConstructiveReals.ExpNeg

namespace ExpPos

/-! ## Monotonicity and block split of the positive partial sums -/

/-- The positive partial sums increase: `partialSumAbs x k ≤ partialSumAbs x (k+d)`. -/
theorem partialSumAbs_mono (x : Q') (hx : (0 : Q') ≤ x) (k d : Nat) :
    partialSumAbs x k ≤ partialSumAbs x (k + d) := by
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
      show partialSumAbs x k ≤ partialSumAbs x (k + d) + termAbs x (k + d)
      exact Q'.le_trans' _ _ _ ih
        (Q'.add_le_self_of_nonneg _ _ (termAbs_nonneg x hx (k + d)))

/-- The block split (as a `≤`): `partialSumAbs x (k+d) ≤ partialSumAbs x k + blockAbs x k d`. -/
theorem partialSumAbs_le_add_blockAbs (x : Q') (k d : Nat) :
    partialSumAbs x (k + d) ≤ partialSumAbs x k + blockAbs x k d := by
  induction d with
  | zero =>
      show partialSumAbs x k ≤ partialSumAbs x k + blockAbs x k 0
      rw [blockAbs_zero, Q'.add_zero']
      exact Q'.le_refl' _
  | succ d ih =>
      show partialSumAbs x (k + d) + termAbs x (k + d)
          ≤ partialSumAbs x k + blockAbs x k (d + 1)
      rw [blockAbs_succ]
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _))

/-! ## `expPos : Q' → CReal` -/

/-- Constructive `e^{+x}` for `x ≥ 0`: the monotone positive-series limit. -/
def expPos (x : Q') (hx : (0 : Q') ≤ x) : CReal where
  approx := partialSumAbs x
  cauchy := by
    intro ε hε
    have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    have hhε : (0 : Q') < half * ε := half_mul_pos ε hε
    refine ⟨max (halfRatioCutoff x) (termAbsModulus x (half * ε)), fun m n hm hn => ?_⟩
    have dir : ∀ k l : Nat,
        max (halfRatioCutoff x) (termAbsModulus x (half * ε)) ≤ k → k ≤ l →
        partialSumAbs x l ≤ partialSumAbs x k + ε ∧
        partialSumAbs x k ≤ partialSumAbs x l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have hcut : halfRatioCutoff x ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
      have hterm : termAbs x k ≤ half * ε :=
        termAbs_le_of_modulus_le x (half * ε) hx hhε k
          (Nat.le_trans (Nat.le_max_right _ _) hk)
      have htail : blockAbs x k d ≤ ε := expNeg_tail_bound x hx ε hεnn k hcut hterm d
      refine ⟨?_, ?_⟩
      · exact Q'.le_trans' _ _ _ (partialSumAbs_le_add_blockAbs x k d)
          (Q'.add_le_add_left (partialSumAbs x k) (blockAbs x k d) ε htail)
      · exact Q'.le_trans' _ _ _ (partialSumAbs_mono x hx k d)
          (Q'.add_le_self_of_nonneg (partialSumAbs x (k + d)) ε hεnn)
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

@[simp] theorem expPos_approx (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    (expPos x hx).approx n = partialSumAbs x n := rfl

/-! ## Lower bounds: `geRat` (the dual of `leRat`) -/

/-- `geRat y b`: the limit of `y` is `≥ b`. Dual to `CRealLe.leRat`. -/
def geRat (y : CReal) (b : Q') : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → b ≤ y.approx n + ε

/-- A uniform eventual lower bound (no `ε`) gives `geRat`. -/
theorem geRat_of_eventually {y : CReal} {b : Q'}
    (h : ∃ N : Nat, ∀ n : Nat, N ≤ n → b ≤ y.approx n) : geRat y b := by
  obtain ⟨N, hN⟩ := h
  intro ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.add_le_self_of_nonneg (y.approx n) ε (Q'.le_of_lt hε))⟩

/-- `geRat` is antitone in the bound. -/
theorem geRat_mono {y : CReal} {a b : Q'} (h : geRat y b) (hab : a ≤ b) : geRat y a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ hab (hN n hn)⟩

/-- **Every partial sum is a lower bound**: `partialSumAbs x N ≤ e^x`. -/
theorem expPos_geRat (x : Q') (hx : (0 : Q') ≤ x) (N : Nat) :
    geRat (expPos x hx) (partialSumAbs x N) := by
  apply geRat_of_eventually
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show partialSumAbs x N ≤ partialSumAbs x (N + d)
  exact partialSumAbs_mono x hx N d

/-- `partialSumAbs x 2 = 1 + x` (up to `Q'` equivalence). -/
theorem partialSumAbs_two_eqv (x : Q') : (partialSumAbs x 2).eqv (1 + x) := by
  have ht1 : (termAbs x 1).eqv x := by
    show ((1 : Q') * (x * (1 : Q'))).eqv x
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (x * 1)) (Q'.mul_one_eqv x)
  -- partialSumAbs x 2 defeq (0+1) + termAbs x 1 defeq 1 + termAbs x 1
  show ((1 : Q') + termAbs x 1).eqv (1 + x)
  exact Q'.add_eqv_congr_left 1 (termAbs x 1) x ht1

/-- **`1 + x ≤ e^x`** — the monotone-partial-sum lower bound (`partialSumAbs x 2`). -/
theorem oneAddX_le_expPos (x : Q') (hx : (0 : Q') ≤ x) :
    geRat (expPos x hx) (1 + x) :=
  geRat_mono (expPos_geRat x hx 2) (Q'.ge_of_eqv (partialSumAbs_two_eqv x))

end ExpPos

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.ExpPos.partialSumAbs_mono
#print axioms ConstructiveReals.ExpPos.partialSumAbs_le_add_blockAbs
#print axioms ConstructiveReals.ExpPos.expPos
#print axioms ConstructiveReals.ExpPos.expPos_geRat
#print axioms ConstructiveReals.ExpPos.partialSumAbs_two_eqv
#print axioms ConstructiveReals.ExpPos.oneAddX_le_expPos
