/-
# The CReal-angle cosine addition law (in-range nonnegative core)

This module lifts the `Q'`-angle termwise cosine addition identity
`TrigAdd.cos_add_equiv_nonneg`,

    cosFull (A + B)  ≃  cosFull A · cosFull B  +  (−(sinFull A · sinFull B)),

to the level of **CReal angles** `a, b` (with the `cosC`/`sinC` domain data
`0 ≤ a.approx k ≤ 1`, plus a `Type`-level Cauchy modulus).  The deliverable is

    cosC (a + b)  ≃  cosC a · cosC b  +  (−(sinC a · sinC b))

for CReal angles `a`, `b` such that `a`, `b`, **and `a+b`** all carry the
`[0,1]`-range + modulus data (`TrigCData`).  The `a+b ∈ [0,1]` clause is the
honest domain constraint — this is the **nonnegative in-range** cosine law, not a
signed one, and not the sine law (whose `Q'`-core is not landed).

## Engine

Everything collapses to one application of `CReal.Equiv_of_limit_of_equal`, the
same limit-uniqueness engine `CRealExp.expNegCD_add` uses:

  * the termwise identity is `TrigAdd.cos_add_equiv_nonneg` at the approximants;
  * the left sequence `k ↦ cosFull ((a+b).approx k)` converges to `cosC (a+b)`
    (`cosC_converges` + the `cosNN ↔ cosFull` nonneg bridge, `convergesTo_congr_seq`);
  * the right sequence `k ↦ cosFull a_k · cosFull b_k + (−(sinFull a_k · sinFull b_k))`
    converges to `cosC a · cosC b + (−(sinC a · sinC b))`
    (`convergesTo_add ∘ (convergesTo_mul, convergesTo_neg ∘ convergesTo_mul)`),
    bounded by `|cos/sin partial| ≤ 2` on `[0,1]`.

## What is genuinely proved here (no new axioms — `propext`/`Quot.sound` only)

  * `convergesTo_neg`     — pointwise negation of a convergent CReal sequence;
  * `convergesTo_add`     — sum of convergent sequences (re-proved locally);
  * `convergesTo_congr_seq` — termwise-`Equiv` transport of a limit (re-proved locally);
  * `abs_cosPartial_le_two` / `abs_sinPartial_le_two` — the `Q'`-level `≤ 2` bounds
    on the cos/sin truncations for `[0,1]` angles;
  * `cosCD_approx_le_two` / `sinCD_approx_le_two` — the completed-limit `≤ 2` bounds;
  * `cosCD_add`           — the CReal cosine addition law (the headline).
-/
import ConstructiveReals.CRealTrig
import ConstructiveReals.CRealExp
import ConstructiveReals.CRealAdd

namespace ConstructiveReals

open ConstructiveReals.CReal

namespace TrigAddCReal

/-! ## 1. Convergence plumbing for CReal limits

`convergesTo_add` and `convergesTo_congr_seq` already exist in the `Continuum`
layer; we re-prove them here (short `ε/2` splits) so this module needs no
`Continuum` import.  `convergesTo_neg` is genuinely new. -/

/-- **Negation preserves convergence.**  If `s → L` then `k ↦ −(s k) → −L`.
Pointwise (`neg_approx` is `rfl`), no boundedness needed. -/
theorem convergesTo_neg {s : Nat → CReal} {L : CReal}
    (h : CReal.ConvergesTo s L) :
    CReal.ConvergesTo (fun k => CReal.neg (s k)) (CReal.neg L) := by
  intro ε hε
  obtain ⟨Nst, hst⟩ := h ε hε
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨P, hP⟩ := hst N hN
  refine ⟨P, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hP n hn
  -- (neg (s N)).approx n = -(s N).approx n , (neg L).approx n = -(L.approx n)
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- **Sums of convergent sequences converge to the sum.**  (Re-proved locally.) -/
theorem convergesTo_add {sA sB : Nat → CReal} {A B : CReal}
    (hA : CReal.ConvergesTo sA A) (hB : CReal.ConvergesTo sB B) :
    CReal.ConvergesTo (fun N => CReal.add (sA N) (sB N)) (CReal.add A B) := by
  intro ε hε
  have hh : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨NA, hNA⟩ := hA (HalfPow.half * ε) hh
  obtain ⟨NB, hNB⟩ := hB (HalfPow.half * ε) hh
  refine ⟨max NA NB, fun N hN => ?_⟩
  obtain ⟨PA, hPA⟩ := hNA N (Nat.le_trans (Nat.le_max_left _ _) hN)
  obtain ⟨PB, hPB⟩ := hNB N (Nat.le_trans (Nat.le_max_right _ _) hN)
  refine ⟨max PA PB, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := hPA n (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨b1, b2⟩ := hPB n (Nat.le_trans (Nat.le_max_right _ _) hn)
  refine ⟨?_, ?_⟩
  · have hsum := Q'.add_le_add a1 b1
    have ereg := Q'.regroup (A.approx n) (B.approx n) (HalfPow.half * ε)
    have etwo := Q'.add_eqv_congr_left (A.approx n + B.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))
  · have hsum := Q'.add_le_add a2 b2
    have ereg := Q'.regroup ((sA N).approx n) ((sB N).approx n) (HalfPow.half * ε)
    have etwo := Q'.add_eqv_congr_left ((sA N).approx n + (sB N).approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

/-- **Termwise-`Equiv` transport of a limit.**  (Re-proved locally.) -/
theorem convergesTo_congr_seq {s t : Nat → CReal} {L : CReal}
    (hst : ∀ N, CReal.Equiv (s N) (t N)) (hs : CReal.ConvergesTo s L) :
    CReal.ConvergesTo t L := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := hs (HalfPow.half * ε) hhε
  refine ⟨Nstage, fun N hN => ?_⟩
  obtain ⟨Napx1, hap1⟩ := hstage N hN
  obtain ⟨Napx2, hap2⟩ := hst N (HalfPow.half * ε) hhε
  refine ⟨max Napx1 Napx2, fun n hn => ?_⟩
  have hn1 : Napx1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Napx2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hs1, hs2⟩ := hap1 n hn1
  obtain ⟨he1, he2⟩ := hap2 n hn2
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ he2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hs1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L.approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)
  · refine Q'.le_trans' _ _ _ hs2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) he1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((t N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((t N).approx n) (HalfPow.half * ε + HalfPow.half * ε) ε
      (ExpNeg.two_halves ε)

/-! ## 2. The `Q'`-level `≤ 2` truncation bounds -/

/-- `termAbs x 2 + termAbs x 2 ≤ 1` for `0 ≤ x ≤ 1` (base-monotonicity to
`termAbs 1 2 = 1/2`). -/
theorem termAbs2_sum_le_one {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    ExpNeg.termAbs x 2 + ExpNeg.termAbs x 2 ≤ 1 := by
  have hm : ExpNeg.termAbs x 2 ≤ ExpNeg.termAbs 1 2 := ExpNeg.termAbs_base_mono hx0 hx1 2
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hm hm) ?_
  decide

/-- `termAbs x 3 + termAbs x 3 ≤ 1` for `0 ≤ x ≤ 1` (base-monotonicity to
`termAbs 1 3 = 1/6`). -/
theorem termAbs3_sum_le_one {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    ExpNeg.termAbs x 3 + ExpNeg.termAbs x 3 ≤ 1 := by
  have hm : ExpNeg.termAbs x 3 ≤ ExpNeg.termAbs 1 3 := ExpNeg.termAbs_base_mono hx0 hx1 3
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hm hm) ?_
  decide

/-- **Generic `≤ 2` bound from a near-`c` two-sided estimate.**  If `|c| ≤ 1`,
`B ≤ 1` and `|a − c| ≤ B`, then `|a| ≤ 2`.  (`|a| ≤ |a − c| + |c| ≤ B + 1 ≤ 2`.) -/
theorem abs_le_two_of_shift {a c B : Q'} (hc : Q'.abs c ≤ 1) (hB : B ≤ 1)
    (h : Q'.abs (a + (-c)) ≤ B) : Q'.abs a ≤ Q'.ofNat 2 := by
  have e1 : a.eqv ((a + (-c)) + c) := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-c) c) ?_)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-c + c) 0 (Q'.neg_add_self_eqv c)) ?_
    exact QPoly.q_add_zero_eqv a
  have habs : Q'.abs a ≤ Q'.abs (a + (-c)) + Q'.abs c :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr e1)) (ExpNeg.abs_add_le (a + (-c)) c)
  refine Q'.le_trans' _ _ _ habs ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add h hc) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hB (Q'.le_refl' 1)) ?_
  decide

/-- **`|cosPartial x n| ≤ 2`** for `0 ≤ x ≤ 1`, every truncation `n`. -/
theorem abs_cosPartial_le_two {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    ∀ n, Q'.abs (Trig.cosPartial x n) ≤ Q'.ofNat 2
  | 0 => by rw [Trig.cosPartial_zero]; decide
  | n + 1 => by
      rw [show n + 1 = 1 + n from Nat.add_comm n 1]
      exact abs_le_two_of_shift (by decide) (termAbs2_sum_le_one hx0 hx1)
        (TrigAdd.cos_small_angle x hx0 hx1 n)

/-- **`|sinPartial x n| ≤ 2`** for `0 ≤ x ≤ 1`, every truncation `n`. -/
theorem abs_sinPartial_le_two {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    ∀ n, Q'.abs (Trig.sinPartial x n) ≤ Q'.ofNat 2
  | 0 => by rw [Trig.sinPartial_zero]; decide
  | n + 1 => by
      rw [show n + 1 = 1 + n from Nat.add_comm n 1]
      -- `|sinTerm x 0| ≤ 1` since `sinTerm x 0 ≃ x ≤ 1`.
      have hsc : Q'.abs (Trig.sinTerm x 0) ≤ 1 := by
        refine Q'.le_trans' _ _ _
          (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Trig.sinTerm_zero_eqv x))) ?_
        rw [TrigAdd.abs_of_nonneg hx0]; exact hx1
      exact abs_le_two_of_shift hsc (termAbs3_sum_le_one hx0 hx1)
        (TrigAdd.sin_small_angle x hx0 hx1 n)

/-- `|(cosFull x).approx n| ≤ 2` for `0 ≤ x ≤ 1`. -/
theorem abs_cosFull_approx_le_two {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (n : Nat) :
    Q'.abs ((TrigAdd.cosFull x).approx n) ≤ Q'.ofNat 2 := by
  rw [TrigAdd.cosFull_approx]
  exact abs_cosPartial_le_two (Q'.abs_nonneg x)
    (by rw [TrigAdd.abs_of_nonneg hx0]; exact hx1) n

/-- `|(sinFull x).approx n| ≤ 2` for `0 ≤ x ≤ 1`. -/
theorem abs_sinFull_approx_le_two {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (n : Nat) :
    Q'.abs ((TrigAdd.sinFull x).approx n) ≤ Q'.ofNat 2 := by
  rw [TrigAdd.sinFull_of_nonneg hx0, Trig.sinNN_approx]
  exact abs_sinPartial_le_two (Q'.abs_nonneg x)
    (by rw [TrigAdd.abs_of_nonneg hx0]; exact hx1) n

/-! ## 3. The CReal-angle trig data and the `cos`/`sin` inhabitants -/

/-- The modulus-data hypotheses for `cosC w`/`sinC w`, packaged to shorten the
add-law signature (identical shape to `CRealExp.ExpNegCData`). -/
structure TrigCData (w : CReal) : Type where
  Mw : Q' → Nat
  hpos : ∀ k, (0 : Q') ≤ w.approx k
  hle1 : ∀ k, w.approx k ≤ 1
  hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
          w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε
  hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ

/-- `cosC` from packaged data. -/
def cosCD (w : CReal) (d : TrigCData w) : CReal :=
  CRealTrig.cosC w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

/-- `sinC` from packaged data. -/
def sinCD (w : CReal) (d : TrigCData w) : CReal :=
  CRealTrig.sinC w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

theorem cosCD_converges (w : CReal) (d : TrigCData w) :
    CReal.ConvergesTo (fun k => Trig.cosNN (w.approx k) (d.hpos k)) (cosCD w d) :=
  CRealTrig.cosC_converges w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

theorem sinCD_converges (w : CReal) (d : TrigCData w) :
    CReal.ConvergesTo (fun k => Trig.sinNN (w.approx k) (d.hpos k)) (sinCD w d) :=
  CRealTrig.sinC_converges w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

/-- **`|(cosC w).approx n| ≤ 2`** — bounds `cosC`'s own diagonal (template:
`CRealExp.expNegC_approx_le_three`). -/
theorem cosCD_approx_le_two (w : CReal) (d : TrigCData w) (n : Nat) :
    Q'.abs ((cosCD w d).approx n) ≤ Q'.ofNat 2 := by
  show Q'.abs ((CReal.completeLimitCauchy (fun k => Trig.cosNN (w.approx k) (d.hpos k))
      (CRealTrig.cosCMC w d.hpos d.hle1 d.Mw d.hMw d.hMwmono)).approx n) ≤ Q'.ofNat 2
  rw [CReal.completeLimitCauchy_approx, Trig.cosNN_approx]
  exact abs_cosPartial_le_two (d.hpos _) (d.hle1 _) _

/-- **`|(sinC w).approx n| ≤ 2`**. -/
theorem sinCD_approx_le_two (w : CReal) (d : TrigCData w) (n : Nat) :
    Q'.abs ((sinCD w d).approx n) ≤ Q'.ofNat 2 := by
  show Q'.abs ((CReal.completeLimitCauchy (fun k => Trig.sinNN (w.approx k) (d.hpos k))
      (CRealTrig.sinCMC w d.hpos d.hle1 d.Mw d.hMw d.hMwmono)).approx n) ≤ Q'.ofNat 2
  rw [CReal.completeLimitCauchy_approx, Trig.sinNN_approx]
  exact abs_sinPartial_le_two (d.hpos _) (d.hle1 _) _

/-- The right-hand side of the CReal cosine addition law:
`cosC a · cosC b + (−(sinC a · sinC b))`. -/
def cosProdMinusC (a b : CReal) (da : TrigCData a) (db : TrigCData b) : CReal :=
  CReal.add (CReal.mul (cosCD a da) (cosCD b db))
    (CReal.neg (CReal.mul (sinCD a da) (sinCD b db)))

/-! ## 4. The `cosNN ↔ cosFull` / `sinNN ↔ sinFull` nonnegative bridge -/

/-- For `0 ≤ x`, `cosNN x ≃ cosFull x` (cosine is even; `|x| = x`). -/
theorem cosNN_equiv_cosFull {x : Q'} (hx : (0 : Q') ≤ x) :
    CReal.Equiv (Trig.cosNN x hx) (TrigAdd.cosFull x) := by
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  show (Trig.cosPartial x n).eqv (Trig.cosPartial (Q'.abs x) n)
  exact TrigAdd.cosPartial_eqv_congr (Q'.eqv_symm (Q'.eqv_of_eq (TrigAdd.abs_of_nonneg hx))) n

/-- For `0 ≤ x`, `sinNN x ≃ sinFull x`. -/
theorem sinNN_equiv_sinFull {x : Q'} (hx : (0 : Q') ≤ x) :
    CReal.Equiv (Trig.sinNN x hx) (TrigAdd.sinFull x) := by
  rw [TrigAdd.sinFull_of_nonneg hx]
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  show (Trig.sinPartial x n).eqv (Trig.sinPartial (Q'.abs x) n)
  exact TrigAdd.sinPartial_eqv_congr (Q'.eqv_symm (Q'.eqv_of_eq (TrigAdd.abs_of_nonneg hx))) n

/-! ## 5. The headline: the CReal-angle cosine addition law -/

/-- **The CReal cosine addition law (nonnegative in-range core).**  For CReal
angles `a`, `b` (and `a+b`) carrying `[0,1]`-range + modulus data,

    cosC (a+b)  ≃  cosC a · cosC b  +  (−(sinC a · sinC b)).

Proof: `Equiv_of_limit_of_equal` with the termwise `Q'` identity
`TrigAdd.cos_add_equiv_nonneg`, the left sequence `k ↦ cosFull (a_k + b_k)`
converging to `cosC (a+b)` (`cosCD_converges` bridged by `cosNN_equiv_cosFull`),
and the right sequence assembled from `convergesTo_mul` (bounded by `2`),
`convergesTo_neg`, `convergesTo_add`. -/
theorem cosCD_add (a b : CReal) (da : TrigCData a) (db : TrigCData b)
    (dab : TrigCData (CReal.add a b)) :
    CReal.Equiv (cosCD (CReal.add a b) dab) (cosProdMinusC a b da db) := by
  -- The left factor sequences converge to `cosC a`, `cosC b` via the nonneg bridge.
  have hCosA : CReal.ConvergesTo (fun k => TrigAdd.cosFull (a.approx k)) (cosCD a da) :=
    convergesTo_congr_seq (fun k => cosNN_equiv_cosFull (da.hpos k)) (cosCD_converges a da)
  have hCosB : CReal.ConvergesTo (fun k => TrigAdd.cosFull (b.approx k)) (cosCD b db) :=
    convergesTo_congr_seq (fun k => cosNN_equiv_cosFull (db.hpos k)) (cosCD_converges b db)
  have hSinA : CReal.ConvergesTo (fun k => TrigAdd.sinFull (a.approx k)) (sinCD a da) :=
    convergesTo_congr_seq (fun k => sinNN_equiv_sinFull (da.hpos k)) (sinCD_converges a da)
  have hSinB : CReal.ConvergesTo (fun k => TrigAdd.sinFull (b.approx k)) (sinCD b db) :=
    convergesTo_congr_seq (fun k => sinNN_equiv_sinFull (db.hpos k)) (sinCD_converges b db)
  -- The cos-product and sin-product sequences converge (mul-continuity, bound `2`).
  have hProdCos : CReal.ConvergesTo
      (fun k => CReal.mul (TrigAdd.cosFull (a.approx k)) (TrigAdd.cosFull (b.approx k)))
      (CReal.mul (cosCD a da) (cosCD b db)) :=
    CReal.convergesTo_mul (by decide : (0 : Q') ≤ Q'.ofNat 2)
      (fun k n => abs_cosFull_approx_le_two (da.hpos k) (da.hle1 k) n)
      (fun n => cosCD_approx_le_two b db n) hCosA hCosB
  have hProdSin : CReal.ConvergesTo
      (fun k => CReal.mul (TrigAdd.sinFull (a.approx k)) (TrigAdd.sinFull (b.approx k)))
      (CReal.mul (sinCD a da) (sinCD b db)) :=
    CReal.convergesTo_mul (by decide : (0 : Q') ≤ Q'.ofNat 2)
      (fun k n => abs_sinFull_approx_le_two (da.hpos k) (da.hle1 k) n)
      (fun n => sinCD_approx_le_two b db n) hSinA hSinB
  -- The left sequence `k ↦ cosFull ((a+b).approx k)` converges to `cosC (a+b)`.
  have hLeft : CReal.ConvergesTo
      (fun k => TrigAdd.cosFull (a.approx k + b.approx k)) (cosCD (CReal.add a b) dab) :=
    convergesTo_congr_seq (fun k => cosNN_equiv_cosFull (dab.hpos k))
      (cosCD_converges (CReal.add a b) dab)
  -- Assemble the RHS convergence and apply the limit-uniqueness engine.
  exact CReal.Equiv_of_limit_of_equal
    (fun k => TrigAdd.cos_add_equiv_nonneg (a.approx k) (b.approx k) (da.hpos k) (db.hpos k))
    hLeft
    (convergesTo_add hProdCos (convergesTo_neg hProdSin))

end TrigAddCReal

end ConstructiveReals
