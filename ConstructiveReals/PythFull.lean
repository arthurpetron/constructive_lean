/-
# The series-level Pythagorean identity `cosFull² + sinFull² ≃ 1`, and its
# opposite-sign sine consequence.

This module inhabits the single named analytic residual
`ConstructiveReals.TrigSignedAdd.PythFull` — the constructive Pythagorean
identity `cosFull A · cosFull A + sinFull A · sinFull A ≃ 1` for `A ≥ 0` — as the
**PLUS mirror, at the diagonal `B := A`, of the already-landed MINUS addition
pipeline** (`TrigAdd.cos_add_equiv_nonneg`).  No analytic ingredient is
re-derived: the one genuinely new atom is the per-degree PLUS collapse
`cosConv_addition_plus`, obtained from the existing `Q'`-series identity
`TrigAdd.cosConv_addition` by an angle reflection `B := -A`.

## The chain

  * `termAbs_neg_eq_term` — the magnitude series at `-A` is the `e^{-A}` term
    series at `A` (identical recurrence); `cosTerm`/`sinTerm` at `-A` then relate
    to those at `A` by even/odd parity (`term_even_eq_abs`/`term_odd_eq_neg_abs`).
  * `cosConv_addition_plus` — `cosConv A A (m+1) + sinConv A A m ≃ 0`, the PLUS
    per-degree collapse, from `cosConv_addition A (-A) m`.
  * `plusDiag` — the diagonal telescope `Σ_{m<n+1} cosConv + Σ_{m<n} sinConv ≃ 1`.
  * `cosSinProdPlus_eqv_one_add_remCornerP` — the `Q'`-level rectangle identity
    `cos² + sin² ≃ 1 + remCornerP`.
  * `remCornerP_le` — the analytic modulus `remCornerP A k → 0` for `A ≥ 0`
    (reuses `cos/sinCornerAbs_le`, `sinConvAbs_le` verbatim at `(A, A)`).
  * `pyth_equiv` / `pythFull_of_reflection` — the `CReal` bridge inhabiting
    `PythFull`.

## The sine twin

  * `sinCore_of_pyth_le` / `oppositeSignSinCore_of_pyth` — inhabit
    `TrigSignedAddFull.OppositeSignSinCore` from `PythFull`, the exact sine mirror
    of `TrigSignedAddFull.core_of_pyth_le`.

All declarations depend only on `propext` / `Quot.sound`.
-/
import ConstructiveReals.TrigAdd
import ConstructiveReals.TrigSignedAdd
import ConstructiveReals.TrigSignedAddFull
import ConstructiveReals.CRealAlg

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.Trig
open ConstructiveReals.TrigAdd

namespace PythFullProof

/-! ## Atom 0 — the magnitude/term reflection bridge -/

/-- **Atom 0.**  `termAbs (-A) k ≃ ExpNeg.term A k`.  Both satisfy the identical
recurrence `_ · ((-A) · 1/(k+1))` with base `1`. -/
theorem termAbs_neg_eq_term (A : Q') :
    ∀ k, (termAbs (-A) k).eqv (ExpNeg.term A k)
  | 0 => Q'.eqv_refl 1
  | k + 1 => by
    show (termAbs (-A) k * ((-A) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))).eqv
        (ExpNeg.term A k * ((-A) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)))
    exact Q'.mul_eqv_congr_right (termAbs (-A) k) (ExpNeg.term A k)
      ((-A) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) (termAbs_neg_eq_term A k)

/-- `cosTerm (-A) j ≃ cosTerm A j` (even parity of the magnitude reflection). -/
theorem cosTerm_neg_eqv (A : Q') (j : Nat) :
    (cosTerm (-A) j).eqv (cosTerm A j) := by
  show (negPow j * termAbs (-A) (2 * j)).eqv (negPow j * termAbs A (2 * j))
  refine Q'.mul_eqv_congr_left (negPow j) _ _ ?_
  exact Q'.eqv_trans _ _ _ (termAbs_neg_eq_term A (2 * j)) (term_even_eq_abs A j)

/-- `sinTerm (-A) j ≃ -(sinTerm A j)` (odd parity of the magnitude reflection). -/
theorem sinTerm_neg_eqv (A : Q') (j : Nat) :
    (sinTerm (-A) j).eqv (-(sinTerm A j)) := by
  show (negPow j * termAbs (-A) (2 * j + 1)).eqv (-(negPow j * termAbs A (2 * j + 1)))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow j) (termAbs (-A) (2 * j + 1)) (-(termAbs A (2 * j + 1)))
      (Q'.eqv_trans _ _ _ (termAbs_neg_eq_term A (2 * j + 1)) (term_odd_eq_neg_abs A j))) ?_
  exact Q'.mul_neg_eqv (negPow j) (termAbs A (2 * j + 1))

/-- `cosConv A (-A) m ≃ cosConv A A m` (termwise, even parity). -/
theorem cosConv_neg_eqv (A : Q') (m : Nat) :
    (cosConv A (-A) m).eqv (cosConv A A m) := by
  show (RationalTail.finSum (cosConvTerm A (-A) m) (m + 1)).eqv
      (RationalTail.finSum (cosConvTerm A A m) (m + 1))
  refine RationalTail.finSum_eqv_congr (cosConvTerm A (-A) m) (cosConvTerm A A m) ?_ (m + 1)
  intro i
  show (cosTerm A i * cosTerm (-A) (m - i)).eqv (cosTerm A i * cosTerm A (m - i))
  exact Q'.mul_eqv_congr_left (cosTerm A i) _ _ (cosTerm_neg_eqv A (m - i))

/-- `sinConv A (-A) m ≃ -(sinConv A A m)` (termwise, odd parity). -/
theorem sinConv_neg_eqv (A : Q') (m : Nat) :
    (sinConv A (-A) m).eqv (-(sinConv A A m)) := by
  show (RationalTail.finSum (sinConvTerm A (-A) m) (m + 1)).eqv
      (-(RationalTail.finSum (sinConvTerm A A m) (m + 1)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (sinConvTerm A (-A) m)
      (fun i => -(sinConvTerm A A m i)) ?_ (m + 1)) ?_
  · intro i
    show (sinTerm A i * sinTerm (-A) (m - i)).eqv (-(sinTerm A i * sinTerm A (m - i)))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (sinTerm A i) (sinTerm (-A) (m - i)) (-(sinTerm A (m - i)))
        (sinTerm_neg_eqv A (m - i))) ?_
    exact Q'.mul_neg_eqv (sinTerm A i) (sinTerm A (m - i))
  · exact Q'.eqv_symm (neg_finSum (sinConvTerm A A m) (m + 1))

/-! ## Atom 1 — the per-degree PLUS collapse (reflection) -/

/-- **Atom 1.**  `cosConv A A (m+1) + sinConv A A m ≃ 0`.  The PLUS mirror of the
MINUS per-degree identity `cosConv_addition`, obtained by reflecting `B := -A`:
`cosConv A (-A)(m+1) ≃ cosConv A A (m+1)` (even), `-(sinConv A (-A) m) ≃ sinConv A A m`
(odd), and `cosTerm (A + (-A)) (m+1) ≃ cosTerm 0 (m+1) ≃ 0`. -/
theorem cosConv_addition_plus (A : Q') (m : Nat) :
    (cosConv A A (m + 1) + sinConv A A m).eqv 0 := by
  have hbase := cosConv_addition A (-A) m
  have hcos : (cosConv A (-A) (m + 1)).eqv (cosConv A A (m + 1)) := cosConv_neg_eqv A (m + 1)
  have hsin : (-(sinConv A (-A) m)).eqv (sinConv A A m) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (sinConv_neg_eqv A m)) ?_
    exact Q'.neg_neg_eqv (sinConv A A m)
  have hRHS : (cosTerm (A + (-A)) (m + 1)).eqv 0 := by
    refine Q'.eqv_trans _ _ _ (cosTerm_eqv_congr (Q'.add_neg_self_eqv A) (m + 1)) ?_
    show (negPow (m + 1) * termAbs (0 : Q') (2 * (m + 1))).eqv 0
    have hidx : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hidx]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (negPow (m + 1)) (termAbs (0 : Q') ((2 * m + 1) + 1)) 0
        (termAbs_zero_succ_eqv (2 * m + 1))) ?_
    exact Q'.mul_zero_eqv (negPow (m + 1))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm hcos) (Q'.eqv_symm hsin)) ?_
  exact Q'.eqv_trans _ _ _ hbase hRHS

/-! ## Lemma 2 — the diagonal telescope -/

/-- **Diagonal telescope.**  `(Σ_{m<n+1} cosConv A A) + (Σ_{m<n} sinConv A A) ≃ 1`.
Base: `cosConv A A 0 ≃ cosTerm (A+A) 0 = 1`.  Step: regroup and apply the IH plus
Atom 1. -/
theorem plusDiag (A : Q') :
    ∀ n, (RationalTail.finSum (cosConv A A) (n + 1)
        + RationalTail.finSum (sinConv A A) n).eqv 1
  | 0 => by
    show ((0 + cosConv A A 0) + 0).eqv 1
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' (0 + cosConv A A 0))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosConv A A 0))) ?_
    refine Q'.eqv_trans _ _ _ (cosConv_addition_zero A A) ?_
    rw [cosTerm_zero]
    exact Q'.eqv_refl 1
  | n + 1 => by
    show ((RationalTail.finSum (cosConv A A) (n + 1) + cosConv A A (n + 1))
        + (RationalTail.finSum (sinConv A A) n + sinConv A A n)).eqv 1
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (RationalTail.finSum (cosConv A A) (n + 1)) (cosConv A A (n + 1))
        (RationalTail.finSum (sinConv A A) n) (sinConv A A n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (plusDiag A n) (cosConv_addition_plus A n)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-! ## Lemma 3 — the PLUS rectangle identity -/

/-- The combined corner remainder of the PLUS rectangle decomposition at `n = k+1`. -/
def remCornerP (A : Q') (k : Nat) : Q' :=
  (cosCorner A A (k + 1) + sinCorner A A (k + 1)) + sinConv A A k

/-- **The PLUS rectangle/corner identity (`Q'` level).**  For `n = k+1`,
`cosPartial A n · cosPartial A n + sinPartial A n · sinPartial A n ≃ 1 + remCornerP A k`. -/
theorem cosSinProdPlus_eqv_one_add_remCornerP (A : Q') (k : Nat) :
    (cosPartial A (k + 1) * cosPartial A (k + 1)
        + sinPartial A (k + 1) * sinPartial A (k + 1)).eqv
      (1 + remCornerP A k) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (cosProd_eqv_convSum_add_corner A A (k + 1))
      (sinProd_eqv_convSum_add_corner A A (k + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (add_rearrange_5 (RationalTail.finSum (cosConv A A) (k + 1)) (cosCorner A A (k + 1))
      (RationalTail.finSum (sinConv A A) k) (sinConv A A k) (sinCorner A A (k + 1))) ?_
  exact Q'.add_eqv_congr' (plusDiag A k) (Q'.eqv_refl _)

/-! ## Lemma 4 — the analytic modulus `remCornerP → 0` -/

/-- **`remCornerP A k → 0`** for `A ≥ 0`.  All three pieces are PLUS-joined, so the
bound is strictly simpler than the MINUS `remCorner_le`: split `ε` into thirds and
dominate each corner/convolution by its magnitude analogue. -/
theorem remCornerP_le (A : Q') (hA : (0 : Q') ≤ A)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ k : Nat, N ≤ k →
      remCornerP A k ≤ ε ∧ -(remCornerP A k) ≤ ε := by
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
  obtain ⟨Nc, hNc⟩ := cosCornerAbs_le A A hA hA t htpos
  obtain ⟨Ns, hNs⟩ := sinCornerAbs_le A A hA hA t htpos
  obtain ⟨Nv, hNv⟩ := sinConvAbs_le A A hA hA t htpos
  refine ⟨max (max Nc Ns) Nv, fun k hk => ?_⟩
  have hkNc : Nc ≤ k + 1 := by
    have : Nc ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
    omega
  have hkNs : Ns ≤ k + 1 := by
    have : Ns ≤ k := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
    omega
  have hkNv : Nv ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hcc : cosCornerAbs A A (k + 1) ≤ t := hNc (k + 1) hkNc
  have hsc : sinCornerAbs A A (k + 1) ≤ t := hNs (k + 1) hkNs
  have hsv : sinConvAbs A A k ≤ t := hNv k hkNv
  obtain ⟨hcc1, hcc2⟩ := cosCorner_abs_le A A hA hA (k + 1)
  obtain ⟨hsc1, hsc2⟩ := sinCorner_abs_le A A hA hA (k + 1)
  obtain ⟨hsv1, hsv2⟩ := sinConv_abs_le A A hA hA k
  have hup : remCornerP A k ≤ t + t + t := by
    show (cosCorner A A (k + 1) + sinCorner A A (k + 1)) + sinConv A A k ≤ t + t + t
    exact Q'.add_le_add (Q'.add_le_add (Q'.le_trans' _ _ _ hcc1 hcc)
      (Q'.le_trans' _ _ _ hsc1 hsc)) (Q'.le_trans' _ _ _ hsv1 hsv)
  have hlo : -(remCornerP A k) ≤ t + t + t := by
    show -((cosCorner A A (k + 1) + sinCorner A A (k + 1)) + sinConv A A k) ≤ t + t + t
    have heqv : (-((cosCorner A A (k + 1) + sinCorner A A (k + 1)) + sinConv A A k)).eqv
        ((-(cosCorner A A (k + 1)) + -(sinCorner A A (k + 1))) + -(sinConv A A k)) :=
      Q'.eqv_trans _ _ _
        (Q'.neg_add_eqv (cosCorner A A (k + 1) + sinCorner A A (k + 1)) (sinConv A A k))
        (Q'.add_eqv_congr_right _ _ (-(sinConv A A k))
          (Q'.neg_add_eqv (cosCorner A A (k + 1)) (sinCorner A A (k + 1))))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
    exact Q'.add_le_add (Q'.add_le_add (Q'.le_trans' _ _ _ hcc2 hcc)
      (Q'.le_trans' _ _ _ hsc2 hsc)) (Q'.le_trans' _ _ _ hsv2 hsv)
  exact ⟨Q'.le_trans' _ _ _ hup ht3, Q'.le_trans' _ _ _ hlo ht3⟩

/-! ## Lemma 5 — the `CReal` bridge inhabiting `PythFull` -/

/-- The LHS of the Pythagorean identity as a `CReal`. -/
def prodPlus (A : Q') : CReal :=
  CReal.add (CReal.mul (cosFull A) (cosFull A))
    (CReal.mul (sinFull A) (sinFull A))

/-- For `A ≥ 0`, the LHS approximation is the magnitude product-sum expression. -/
theorem prodPlus_approx_nonneg (A : Q') (hA : (0 : Q') ≤ A) (n : Nat) :
    (prodPlus A).approx n
      = cosPartial A n * cosPartial A n + sinPartial A n * sinPartial A n := by
  have hsA : sinFull A = sinNN (Q'.abs A) (Q'.abs_nonneg A) := sinFull_of_nonneg hA
  show (cosFull A).approx n * (cosFull A).approx n
      + (sinFull A).approx n * (sinFull A).approx n = _
  rw [hsA]
  show cosPartial (Q'.abs A) n * cosPartial (Q'.abs A) n
      + sinPartial (Q'.abs A) n * sinPartial (Q'.abs A) n = _
  rw [TrigAdd.abs_of_nonneg hA]

/-- **The Pythagorean identity as a `CReal.Equiv`.**  For `A ≥ 0`,
`CReal.Equiv (prodPlus A) CReal.cone`, transferring the `Q'`-level rectangle
identity against the `remCornerP_le` modulus. -/
theorem pyth_equiv (A : Q') (hA : (0 : Q') ≤ A) :
    CReal.Equiv (prodPlus A) CReal.cone := by
  intro ε hε
  obtain ⟨N, hN⟩ := remCornerP_le A hA ε hε
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hkN : N ≤ k := by omega
  obtain ⟨hrem1, hrem2⟩ := hN k hkN
  have hid := cosSinProdPlus_eqv_one_add_remCornerP A k
  show (prodPlus A).approx (k + 1) ≤ CReal.cone.approx (k + 1) + ε
      ∧ CReal.cone.approx (k + 1) ≤ (prodPlus A).approx (k + 1) + ε
  rw [prodPlus_approx_nonneg A hA]
  show (cosPartial A (k + 1) * cosPartial A (k + 1)
        + sinPartial A (k + 1) * sinPartial A (k + 1)) ≤ (1 : Q') + ε
    ∧ (1 : Q') ≤ (cosPartial A (k + 1) * cosPartial A (k + 1)
        + sinPartial A (k + 1) * sinPartial A (k + 1)) + ε
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
      (Q'.add_le_add_left 1 (remCornerP A k) ε hrem1)
  · have hCeqv : (1 : Q').eqv
        ((cosPartial A (k + 1) * cosPartial A (k + 1)
            + sinPartial A (k + 1) * sinPartial A (k + 1)) + -(remCornerP A k)) := by
      have e1 : (((cosPartial A (k + 1) * cosPartial A (k + 1)
            + sinPartial A (k + 1) * sinPartial A (k + 1)) + -(remCornerP A k))).eqv
          ((1 + remCornerP A k) + -(remCornerP A k)) :=
        Q'.add_eqv_congr_right _ _ (-(remCornerP A k)) hid
      have e2 : ((1 + remCornerP A k) + -(remCornerP A k)).eqv 1 := by
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (remCornerP A k) (-(remCornerP A k))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 1 _ 0 (Q'.add_neg_self_eqv (remCornerP A k))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' 1)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 e2)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hCeqv)
      (Q'.add_le_add_left _ (-(remCornerP A k)) ε hrem2)

/-- **`TrigSignedAdd.PythFull` is inhabited** by the reflection route. -/
def pythFull_of_reflection : TrigSignedAdd.PythFull :=
  ⟨fun A hA => pyth_equiv A hA⟩

/-! ## Lemma 7 — the opposite-sign sine core from `PythFull`

The exact sine mirror of `TrigSignedAddFull.core_of_pyth_le`: substitute the two
nonneg laws on `(A + -C, C)`, expand, cancel the cross terms, and collapse the
surviving `sinFull(A-C)·(cos²C + sin²C)` via `PythFull`. -/

/-- **The sine opposite-sign core, `C ≤ A` branch, from `PythFull`.** -/
theorem sinCore_of_pyth_le (P : TrigSignedAdd.PythFull) (A C : Q')
    (hA : (0 : Q') ≤ A) (hC : (0 : Q') ≤ C) (hCA : C ≤ A) :
    CReal.Equiv (TrigAdd.sinFull (A + -C))
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C)))) := by
  have hD : (0 : Q') ≤ A + -C := Q'.sub_nonneg_of_le hCA
  have hnegC : (-C + C).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-C) C) (Q'.add_neg_self_eqv C)
  have hDCA : ((A + -C) + C).eqv A :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A (-C) C)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl A) hnegC)
        (Q'.eqv_of_eq (Q'.add_zero' A)))
  have hcosnn : CReal.Equiv (TrigAdd.cosFull ((A + -C) + C))
      (TrigAdd.cosProdMinus (A + -C) C) :=
    TrigAdd.cos_add_equiv_nonneg (A + -C) C hD hC
  have hsinnn : CReal.Equiv (TrigAdd.sinFull ((A + -C) + C))
      (TrigSineAddCReal.sinProdPlus (A + -C) C) :=
    TrigAdd.sin_add_equiv_nonneg (A + -C) C hD hC
  have hI : CReal.Equiv (TrigAdd.cosFull A) (TrigAdd.cosProdMinus (A + -C) C) :=
    ((TrigSignedAddFull.cosFull_argeqv hDCA).symm).trans hcosnn
  have hII : CReal.Equiv (TrigAdd.sinFull A) (TrigSineAddCReal.sinProdPlus (A + -C) C) :=
    ((TrigSignedAdd.sinFull_eqv_congr hDCA).symm).trans hsinnn
  -- Step subst: replace `sinFull A`, `cosFull A` in the target RHS.
  have hsubst : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C))))
      (CReal.add (CReal.mul (TrigSineAddCReal.sinProdPlus (A + -C) C) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosProdMinus (A + -C) C) (TrigAdd.sinFull C)))) :=
    (CReal.add_congr_left (CReal.mul_congr_left hII)).trans
      (CReal.add_congr_right (CReal.neg_congr (CReal.mul_congr_left hI)))
  -- Step B: expand `sinProdPlus (A+−C) C · cosFull C`.
  have hB : CReal.Equiv
      (CReal.mul (TrigSineAddCReal.sinProdPlus (A + -C) C) (TrigAdd.cosFull C))
      (CReal.add (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
        (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C)))) := by
    unfold TrigSineAddCReal.sinProdPlus
    refine (TrigSignedAddFull.cadd_mul (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.cosFull C))
      (CReal.mul (TrigAdd.cosFull (A + -C)) (TrigAdd.sinFull C)) (TrigAdd.cosFull C)).trans ?_
    exact (CReal.add_congr_left
        (CRealAlg.cmul_assoc (TrigAdd.sinFull (A + -C)) (TrigAdd.cosFull C) (TrigAdd.cosFull C))).trans
      (CReal.add_congr_right
        (CRealAlg.cmul_assoc (TrigAdd.cosFull (A + -C)) (TrigAdd.sinFull C) (TrigAdd.cosFull C)))
  -- Step C: expand `cosProdMinus (A+−C) C · sinFull C`.
  have hCexp : CReal.Equiv
      (CReal.mul (TrigAdd.cosProdMinus (A + -C) C) (TrigAdd.sinFull C))
      (CReal.add (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C)))
        (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))) := by
    unfold TrigAdd.cosProdMinus
    refine (TrigSignedAddFull.cadd_mul (CReal.mul (TrigAdd.cosFull (A + -C)) (TrigAdd.cosFull C))
      (CReal.neg (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C))) (TrigAdd.sinFull C)).trans ?_
    refine (CReal.add_congr_left
      (CRealAlg.cmul_assoc (TrigAdd.cosFull (A + -C)) (TrigAdd.cosFull C) (TrigAdd.sinFull C))).trans ?_
    refine CReal.add_congr_right ?_
    exact (TrigSignedAdd.neg_mul (CReal.mul (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C)) (TrigAdd.sinFull C)).trans
      (CReal.neg_congr (CRealAlg.cmul_assoc (TrigAdd.sinFull (A + -C)) (TrigAdd.sinFull C) (TrigAdd.sinFull C)))
  -- term2 = −(cosProdMinus (A+−C) C · sinFull C).
  have hterm2 : CReal.Equiv
      (CReal.neg (CReal.mul (TrigAdd.cosProdMinus (A + -C) C) (TrigAdd.sinFull C)))
      (CReal.add (CReal.neg (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C))))
        (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C)))) := by
    refine (CReal.neg_congr hCexp).trans ?_
    refine (TrigSignedAdd.neg_add_distrib _ _).trans ?_
    exact CReal.add_congr_right (TrigSignedAdd.neg_neg_equiv
      (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))
  -- RHS ≃ (a'+b')+(c'+d') with a'=v(cC·cC), b'=u(sC·cC), c'=−(u(cC·sC)), d'=v(sC·sC).
  have hRHS4 : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C))))
      (CReal.add
        (CReal.add (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
          (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C))))
        (CReal.add (CReal.neg (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C))))
          (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))) :=
    hsubst.trans ((CReal.add_congr_left hB).trans (CReal.add_congr_right hterm2))
  -- b' + c' ≃ 0.
  have hbc : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C)))
        (CReal.neg (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C)))))
      CReal.czero := by
    have hstep : CReal.Equiv
        (CReal.neg (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull C))))
        (CReal.neg (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C)))) :=
      CReal.neg_congr (TrigSignedAdd.mul_congr_right
        (CRealAlg.cmul_comm (TrigAdd.cosFull C) (TrigAdd.sinFull C)))
    refine (CReal.add_congr_right hstep).trans ?_
    refine (TrigSignedAddFull.cadd_comm _ _).trans ?_
    exact TrigSignedAddFull.cadd_neg_left
      (CReal.mul (TrigAdd.cosFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull C)))
  -- a' + d' ≃ sinFull (A+−C).
  have hpyth : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))) CReal.cone :=
    P.pyth C hC
  have had : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C)))
        (CReal.mul (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))))
      (TrigAdd.sinFull (A + -C)) :=
    ((TrigSignedAddFull.cmul_add (TrigAdd.sinFull (A + -C)) (CReal.mul (TrigAdd.cosFull C) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull C) (TrigAdd.sinFull C))).symm).trans
      ((TrigSignedAdd.mul_congr_right hpyth).trans (CRealAlg.cmul_cone (TrigAdd.sinFull (A + -C))))
  -- Combine.
  have hfinal : CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
        (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C))))
      (TrigAdd.sinFull (A + -C)) :=
    hRHS4.trans ((TrigSignedAddFull.cadd_reshuffle _ _ _ _).trans
      (((CReal.add_congr_right hbc).trans (TrigSignedAddFull.cadd_zero _)).trans had))
  exact hfinal.symm

/-- **The sine opposite-sign core is inhabited by `PythFull`.**  Combines the
`C ≤ A` branch with the mirror `A ≤ C` branch (by ODD parity and product
commutativity). -/
def oppositeSignSinCore_of_pyth (P : TrigSignedAdd.PythFull) :
    TrigSignedAddFull.OppositeSignSinCore where
  core := by
    intro A C hA hC
    by_cases hCA : C ≤ A
    · exact sinCore_of_pyth_le P A C hA hC hCA
    · have hAC : A ≤ C := TrigSignedAddFull.le_of_not_le hCA
      have hle := sinCore_of_pyth_le P C A hC hA hAC
      -- transport LHS by odd parity: sinFull (A + -C) ≃ −(sinFull (C + -A)).
      have hneg : (-(C + -A)).eqv (A + -C) :=
        Q'.eqv_trans _ _ _ (Q'.neg_add_eqv C (-A))
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' (Q'.eqv_refl (-C)) (Q'.neg_neg_eqv A))
            (Q'.add_comm_eqv (-C) A))
      have harg : (A + -C).eqv (-(C + -A)) := Q'.eqv_symm hneg
      have hlhs : CReal.Equiv (TrigAdd.sinFull (A + -C)) (CReal.neg (TrigAdd.sinFull (C + -A))) :=
        (TrigSignedAdd.sinFull_eqv_congr harg).trans (TrigSignedAdd.sinFull_neg (C + -A))
      -- middle: distribute the negation over `hle`'s RHS.
      have hmid : CReal.Equiv (CReal.neg (TrigAdd.sinFull (C + -A)))
          (CReal.add (CReal.neg (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull A)))
            (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull A))) := by
        refine (CReal.neg_congr hle).trans ?_
        refine (TrigSignedAdd.neg_add_distrib _ _).trans ?_
        exact CReal.add_congr_right (TrigSignedAdd.neg_neg_equiv
          (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull A)))
      -- transport RHS: order swap + product commutativity.
      have hrhs : CReal.Equiv
          (CReal.add (CReal.neg (CReal.mul (TrigAdd.sinFull C) (TrigAdd.cosFull A)))
            (CReal.mul (TrigAdd.cosFull C) (TrigAdd.sinFull A)))
          (CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull C))
            (CReal.neg (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull C)))) := by
        refine (TrigSignedAddFull.cadd_comm _ _).trans ?_
        refine (CReal.add_congr_left (CRealAlg.cmul_comm (TrigAdd.cosFull C) (TrigAdd.sinFull A))).trans ?_
        exact CReal.add_congr_right (CReal.neg_congr
          (CRealAlg.cmul_comm (TrigAdd.sinFull C) (TrigAdd.cosFull A)))
      exact (hlhs.trans hmid).trans hrhs

end PythFullProof

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.PythFullProof.termAbs_neg_eq_term
#print axioms ConstructiveReals.PythFullProof.cosConv_addition_plus
#print axioms ConstructiveReals.PythFullProof.plusDiag
#print axioms ConstructiveReals.PythFullProof.cosSinProdPlus_eqv_one_add_remCornerP
#print axioms ConstructiveReals.PythFullProof.remCornerP_le
#print axioms ConstructiveReals.PythFullProof.pyth_equiv
#print axioms ConstructiveReals.PythFullProof.pythFull_of_reflection
#print axioms ConstructiveReals.PythFullProof.sinCore_of_pyth_le
#print axioms ConstructiveReals.PythFullProof.oppositeSignSinCore_of_pyth
