/-
# The CReal-angle SINE addition law (in-range nonnegative core) — the LIFT

This module lifts the `Q'`-angle termwise **sine** addition identity to the level
of **CReal angles** `a, b`, exactly mirroring the cosine lift
`TrigAddCReal.cosCD_add`.  The deliverable is

    sinC (a + b)  ≃  sinC a · cosC b  +  cosC a · sinC b

for CReal angles `a`, `b` (and `a+b`) carrying the `[0,1]`-range + `Type`-level
Cauchy modulus data (`TrigCData`).  Unlike the cosine law, the right-hand side is
a **pure sum** (no negation), so the convergence assembly is one
`convergesTo_add` of two `convergesTo_mul` products — strictly simpler than the
cosine case.

## The honest residual (why this is a REDUCTION, not a closure)

The cosine lift `cosCD_add` was fed by the `Q'`-core `TrigAdd.cos_add_equiv_nonneg`
(the termwise identity `cosFull (A+B) ≃ cosFull A · cosFull B − sinFull A · sinFull B`,
proved in `TrigAdd.lean` §5–§7 via the even/odd convolution deinterleave).

The **signed sine analogue** `TrigAdd.sin_add_equiv_nonneg`,

    sinFull (A + B)  ≃  sinFull A · cosFull B  +  cosFull A · sinFull B   (A,B ≥ 0),

is **not yet landed** in the `Q'` layer.  It is genuinely new development (the
cross-parity convolution `sinTerm·cosTerm + cosTerm·sinTerm` deinterleaved from
the ODD convolution degree, where both sub-sums carry the SAME sign — hence a
sum, not a difference).  That core is roughly the same ~600-line §5–§7 effort
spent on cosine and is NOT reproduced here.

So this module names that single missing brick as the Type-level residual
`SinAddNonnegCore` and proves the **entire CReal lift conditional on it**
(`sinCD_add_of_core`).  Every convergence step in the lift is discharged with the
already-verified plumbing from `TrigAddCReal`; the instant `SinAddNonnegCore` is
inhabited (i.e. `TrigAdd.sin_add_equiv_nonneg` is proved), `sinCD_add` follows by
`sinCD_add_of_core core`.

## What is genuinely proved here (no new axioms — `propext`/`Quot.sound` only)

  * `sinProdPlus_approx_nonneg` — the `Q'`-level RHS approximation is the
    magnitude cross-product `sinPartial A · cosPartial B + cosPartial A · sinPartial B`
    for `A, B ≥ 0` (the sine analogue of `TrigAdd.cosProdMinus_approx_nonneg`);
  * `sinCD_add_of_core` — the full CReal sine addition law, conditional on the
    named `Q'`-core `SinAddNonnegCore`.
-/
import ConstructiveReals.TrigAddCReal

namespace ConstructiveReals

open ConstructiveReals.CReal

namespace TrigSineAddCReal

open TrigAddCReal

/-! ## 1. The `Q'`-level right-hand side of the sine addition law -/

/-- The right-hand side of the sine addition law at the `Q'` level, as a `CReal`:
`sinFull A · cosFull B + cosFull A · sinFull B` (a pure sum). -/
def sinProdPlus (A B : Q') : CReal :=
  CReal.add (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B))
    (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B))

/-- **The named Type-level residual: the `Q'`-angle nonnegative sine addition
core.**  The single field `core` is exactly the type of the (not-yet-landed)
`Q'` identity `TrigAdd.sin_add_equiv_nonneg`.  Inhabiting this structure
discharges the CReal lift below.  (Packaged as a `structure` so the residual is
genuine `Type`-level data rather than a bare `Prop`.) -/
structure SinAddNonnegCore : Type where
  core : ∀ (A B : Q'), (0 : Q') ≤ A → (0 : Q') ≤ B →
    CReal.Equiv (TrigAdd.sinFull (A + B)) (sinProdPlus A B)

/-- **For `A, B ≥ 0`, the RHS approximation is the magnitude cross-product.**  The
sine analogue of `TrigAdd.cosProdMinus_approx_nonneg`: since `sinFull` on a
nonnegative argument is `sinNN` of the magnitude and `|A| = A`, the `n`-th
approximant of `sinProdPlus A B` is
`sinPartial A n · cosPartial B n + cosPartial A n · sinPartial B n`. -/
theorem sinProdPlus_approx_nonneg (A B : Q') (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (n : Nat) :
    (sinProdPlus A B).approx n
      = Trig.sinPartial A n * Trig.cosPartial B n
        + Trig.cosPartial A n * Trig.sinPartial B n := by
  have hsA : TrigAdd.sinFull A = Trig.sinNN (Q'.abs A) (Q'.abs_nonneg A) :=
    TrigAdd.sinFull_of_nonneg hA
  have hsB : TrigAdd.sinFull B = Trig.sinNN (Q'.abs B) (Q'.abs_nonneg B) :=
    TrigAdd.sinFull_of_nonneg hB
  show (TrigAdd.sinFull A).approx n * (TrigAdd.cosFull B).approx n
      + (TrigAdd.cosFull A).approx n * (TrigAdd.sinFull B).approx n = _
  rw [hsA, hsB]
  show Trig.sinPartial (Q'.abs A) n * Trig.cosPartial (Q'.abs B) n
      + Trig.cosPartial (Q'.abs A) n * Trig.sinPartial (Q'.abs B) n = _
  rw [TrigAdd.abs_of_nonneg hA, TrigAdd.abs_of_nonneg hB]

/-! ## 2. The CReal-angle right-hand side -/

/-- The right-hand side of the CReal sine addition law:
`sinC a · cosC b + cosC a · sinC b`. -/
def sinProdPlusC (a b : CReal) (da : TrigCData a) (db : TrigCData b) : CReal :=
  CReal.add (CReal.mul (sinCD a da) (cosCD b db))
    (CReal.mul (cosCD a da) (sinCD b db))

/-! ## 3. The headline: the CReal-angle sine addition law (conditional on the core) -/

/-- **The CReal sine addition law (nonnegative in-range core), CONDITIONAL on the
`Q'`-core `SinAddNonnegCore`.**  For CReal angles `a`, `b` (and `a+b`) carrying
`[0,1]`-range + modulus data,

    sinC (a+b)  ≃  sinC a · cosC b  +  cosC a · sinC b .

Proof: `Equiv_of_limit_of_equal` with the termwise `Q'` identity `core`, the left
sequence `k ↦ sinFull (a_k + b_k)` converging to `sinC (a+b)` (`sinCD_converges`
bridged by `sinNN_equiv_sinFull`), and the right sequence assembled from two
`convergesTo_mul` products (each bounded by `2`) via `convergesTo_add`.  The
convergence plumbing is the already-verified `TrigAddCReal` toolkit; the SOLE
open input is `core`. -/
theorem sinCD_add_of_core (core : SinAddNonnegCore)
    (a b : CReal) (da : TrigCData a) (db : TrigCData b)
    (dab : TrigCData (CReal.add a b)) :
    CReal.Equiv (sinCD (CReal.add a b) dab) (sinProdPlusC a b da db) := by
  -- The four factor sequences converge to `cosC a`, `cosC b`, `sinC a`, `sinC b`
  -- via the `cosNN/sinNN ↔ cosFull/sinFull` nonneg bridge.
  have hCosA : CReal.ConvergesTo (fun k => TrigAdd.cosFull (a.approx k)) (cosCD a da) :=
    convergesTo_congr_seq (fun k => cosNN_equiv_cosFull (da.hpos k)) (cosCD_converges a da)
  have hCosB : CReal.ConvergesTo (fun k => TrigAdd.cosFull (b.approx k)) (cosCD b db) :=
    convergesTo_congr_seq (fun k => cosNN_equiv_cosFull (db.hpos k)) (cosCD_converges b db)
  have hSinA : CReal.ConvergesTo (fun k => TrigAdd.sinFull (a.approx k)) (sinCD a da) :=
    convergesTo_congr_seq (fun k => sinNN_equiv_sinFull (da.hpos k)) (sinCD_converges a da)
  have hSinB : CReal.ConvergesTo (fun k => TrigAdd.sinFull (b.approx k)) (sinCD b db) :=
    convergesTo_congr_seq (fun k => sinNN_equiv_sinFull (db.hpos k)) (sinCD_converges b db)
  -- The two cross-product sequences converge (mul-continuity, bound `2`).
  have hProd1 : CReal.ConvergesTo
      (fun k => CReal.mul (TrigAdd.sinFull (a.approx k)) (TrigAdd.cosFull (b.approx k)))
      (CReal.mul (sinCD a da) (cosCD b db)) :=
    CReal.convergesTo_mul (by decide : (0 : Q') ≤ Q'.ofNat 2)
      (fun k n => abs_sinFull_approx_le_two (da.hpos k) (da.hle1 k) n)
      (fun n => cosCD_approx_le_two b db n) hSinA hCosB
  have hProd2 : CReal.ConvergesTo
      (fun k => CReal.mul (TrigAdd.cosFull (a.approx k)) (TrigAdd.sinFull (b.approx k)))
      (CReal.mul (cosCD a da) (sinCD b db)) :=
    CReal.convergesTo_mul (by decide : (0 : Q') ≤ Q'.ofNat 2)
      (fun k n => abs_cosFull_approx_le_two (da.hpos k) (da.hle1 k) n)
      (fun n => sinCD_approx_le_two b db n) hCosA hSinB
  -- The left sequence `k ↦ sinFull ((a+b).approx k)` converges to `sinC (a+b)`.
  have hLeft : CReal.ConvergesTo
      (fun k => TrigAdd.sinFull (a.approx k + b.approx k)) (sinCD (CReal.add a b) dab) :=
    convergesTo_congr_seq (fun k => sinNN_equiv_sinFull (dab.hpos k))
      (sinCD_converges (CReal.add a b) dab)
  -- Assemble the RHS convergence and apply the limit-uniqueness engine.
  exact CReal.Equiv_of_limit_of_equal
    (fun k => core.core (a.approx k) (b.approx k) (da.hpos k) (db.hpos k))
    hLeft
    (convergesTo_add hProd1 hProd2)

end TrigSineAddCReal

end ConstructiveReals
