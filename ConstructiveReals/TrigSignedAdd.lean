/-
# Signed-angle cos/sin `CReal` addition laws: the same-sign quadrants

This module discharges the **stale signed-add footer** left in the constructive
trig layer and lands the two *same-sign* signed addition laws on the completed
even/odd extensions `cosFull`/`sinFull : Q' → CReal`.

Two prior facts are in place upstream:

  * the **nonnegative** cosine law `cosFull (A+B) ≃ cosFull A·cosFull B −
    sinFull A·sinFull B` for `A, B ≥ 0` (unconditional);
  * the **nonnegative** sine law `sinFull (A+B) ≃ sinFull A·cosFull B +
    cosFull A·sinFull B` for `A, B ≥ 0` (unconditional, packaged as the core
    that inhabits the `CReal`-angle sine lift).

## What is genuinely proved here (`propext`/`Quot.sound` only)

  * `sinCD_add` — the full `CReal`-angle sine addition law, assembled by feeding
    the now-inhabited nonneg `Q'`-core to the conditional `CReal` lift (closes the
    last conditional in the sine lift, zero new analytic content);
  * a small `CReal`-algebra toolkit (`neg_add_distrib`, `neg_mul`, `mul_neg`,
    `neg_neg_equiv`, `neg_mul_neg`, `mul_congr_right`) — pure pointwise
    `equiv_of_approx_eqv` bookkeeping;
  * `cosFull_abs_congr` / `sinFull_eqv_congr` / `sinFull_neg` — parity/congruence
    transport for the even/odd extensions;
  * `cos_add_equiv_negneg` — the signed cosine law on the `A ≤ 0, B ≤ 0` quadrant,
    `cosFull (A+B) ≃ cosFull A·cosFull B − sinFull A·sinFull B`;
  * `sin_add_equiv_negneg` — the signed sine law on the `A ≤ 0, B ≤ 0` quadrant,
    `sinFull (A+B) ≃ sinFull A·cosFull B + cosFull A·sinFull B`.

Together with the upstream nonneg laws, both same-sign quadrants are closed.

## The residual (honest, named — NOT bookkeeping)

The **opposite-sign** quadrant `A ≥ 0 > B` forces the *subtraction* formula, whose
derivation from the nonneg law requires the series-level **Pythagorean identity**
`cosFull A² + sinFull A² ≃ 1`, which does not exist for these series and cannot be
bootstrapped from the signed add-law (circular: `cos(A−A)=1` is itself the
opposite-sign case).  It is captured below as the named `Type`-level residuals
`PythFull` and `OppositeSignCosCore`; they are *not* inhabited here.
-/
import ConstructiveReals.TrigSineAddCReal
import ConstructiveReals.SinAddNonneg
import ConstructiveReals.CRealMul
import ConstructiveReals.CRealAlg

namespace ConstructiveReals

open ConstructiveReals.CReal
open TrigAddCReal
open TrigSineAddCReal

namespace TrigSignedAdd

/-! ## 0. The `CReal`-angle sine addition law (assembly, zero new content)

The conditional lift `TrigSineAddCReal.sinCD_add_of_core` takes a `Q'`-level
nonneg sine core; that core is now inhabited unconditionally by
`ConstructiveReals.sinAddNonnegCore`.  Feeding it in gives the headline. -/

/-- **The `CReal`-angle sine addition law.**  For `CReal` angles `a`, `b` (and
`a+b`) carrying `[0,1]`-range + modulus data,
`sinC (a+b) ≃ sinC a·cosC b + cosC a·sinC b`. -/
theorem sinCD_add (a b : CReal) (da : TrigCData a) (db : TrigCData b)
    (dab : TrigCData (CReal.add a b)) :
    CReal.Equiv (sinCD (CReal.add a b) dab) (sinProdPlusC a b da db) :=
  TrigSineAddCReal.sinCD_add_of_core sinAddNonnegCore a b da db dab

/-! ## 1. A small pointwise `CReal`-algebra toolkit -/

/-- `−(X + Y) ≃ (−X) + (−Y)`. -/
theorem neg_add_distrib (X Y : CReal) :
    CReal.Equiv (CReal.neg (CReal.add X Y)) (CReal.add (CReal.neg X) (CReal.neg Y)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.neg_add_eqv (X.approx n) (Y.approx n))

/-- `(−X)·Y ≃ −(X·Y)`. -/
theorem neg_mul (X Y : CReal) :
    CReal.Equiv (CReal.mul (CReal.neg X) Y) (CReal.neg (CReal.mul X Y)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.neg_mul_eqv (X.approx n) (Y.approx n))

/-- `X·(−Y) ≃ −(X·Y)`. -/
theorem mul_neg (X Y : CReal) :
    CReal.Equiv (CReal.mul X (CReal.neg Y)) (CReal.neg (CReal.mul X Y)) :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.mul_neg_eqv (X.approx n) (Y.approx n))

/-- `−(−X) ≃ X`. -/
theorem neg_neg_equiv (X : CReal) :
    CReal.Equiv (CReal.neg (CReal.neg X)) X :=
  TrigAdd.equiv_of_approx_eqv (fun n => Q'.neg_neg_eqv (X.approx n))

/-- `(−X)·(−Y) ≃ X·Y`. -/
theorem neg_mul_neg (X Y : CReal) :
    CReal.Equiv (CReal.mul (CReal.neg X) (CReal.neg Y)) (CReal.mul X Y) :=
  TrigAdd.equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (X.approx n) (-(Y.approx n)))
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (X.approx n) (Y.approx n)))
        (Q'.neg_neg_eqv (X.approx n * Y.approx n))))

/-- `Equiv` congruence for `mul` on the right (derived from `mul_congr_left` and
the `CReal`-level commutativity `CRealAlg.cmul_comm`). -/
theorem mul_congr_right {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  (CRealAlg.cmul_comm A B).trans ((CReal.mul_congr_left h).trans (CRealAlg.cmul_comm B' A))

/-! ## 2. Parity / congruence transport for the even/odd extensions -/

/-- `cosFull` depends only on `|·|`: if `|x| ≃ |y|` then `cosFull x ≃ cosFull y`. -/
theorem cosFull_abs_congr {x y : Q'} (h : (Q'.abs x).eqv (Q'.abs y)) :
    CReal.Equiv (TrigAdd.cosFull x) (TrigAdd.cosFull y) :=
  TrigAdd.equiv_of_approx_eqv (fun n => TrigAdd.cosPartial_eqv_congr h n)

/-- If `u ≃ 0` then every approximant of `sinFull u` is `≃ 0`. -/
theorem sinFull_approx_eqv_zero {u : Q'} (hu : u.eqv 0) (n : Nat) :
    ((TrigAdd.sinFull u).approx n).eqv 0 := by
  have hau : (Q'.abs u).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hu) (Q'.eqv_of_eq TrigAdd.abs_zero_eq)
  have hsp : (Trig.sinPartial (Q'.abs u) n).eqv 0 :=
    Q'.eqv_trans _ _ _ (TrigAdd.sinPartial_eqv_congr hau n) (TrigAdd.sinPartial_zero_eqv n)
  by_cases h0 : (0 : Q') ≤ u
  · rw [TrigAdd.sinFull_of_nonneg h0]; exact hsp
  · have hs2 : TrigAdd.sinFull u = CReal.neg (Trig.sinNN (Q'.abs u) (Q'.abs_nonneg u)) := by
      unfold TrigAdd.sinFull; rw [if_neg h0]
    rw [hs2]
    show (-(Trig.sinPartial (Q'.abs u) n)).eqv 0
    exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hsp) (by decide : ((-0 : Q')).eqv 0)

/-- `sinFull` is a congruence for `Q'`-equivalence of its (signed) argument. -/
theorem sinFull_eqv_congr {u v : Q'} (h : u.eqv v) :
    CReal.Equiv (TrigAdd.sinFull u) (TrigAdd.sinFull v) := by
  by_cases hu : (0 : Q') ≤ u <;> by_cases hv : (0 : Q') ≤ v
  · -- both nonnegative
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    rw [TrigAdd.sinFull_of_nonneg hu, TrigAdd.sinFull_of_nonneg hv]
    show (Trig.sinPartial (Q'.abs u) n).eqv (Trig.sinPartial (Q'.abs v) n)
    exact TrigAdd.sinPartial_eqv_congr (Q'.abs_eqv_congr h) n
  · -- u ≥ 0, v < 0 ⇒ u ≃ v ≃ 0
    have hv0 : v ≤ 0 := Q'.nonpos_of_not_nonneg hv
    have huz : u.eqv 0 :=
      TrigAdd.eqv_of_le_of_le (Q'.le_trans' u v 0 (Q'.le_of_eqv h) hv0) hu
    have hvz : v.eqv 0 :=
      TrigAdd.eqv_of_le_of_le hv0 (Q'.le_trans' 0 u v hu (Q'.le_of_eqv h))
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    exact Q'.eqv_trans _ _ _ (sinFull_approx_eqv_zero huz n)
      (Q'.eqv_symm (sinFull_approx_eqv_zero hvz n))
  · -- u < 0, v ≥ 0 ⇒ u ≃ v ≃ 0
    have hu0 : u ≤ 0 := Q'.nonpos_of_not_nonneg hu
    have huz : u.eqv 0 :=
      TrigAdd.eqv_of_le_of_le hu0 (Q'.le_trans' 0 v u hv (Q'.ge_of_eqv h))
    have hvz : v.eqv 0 :=
      TrigAdd.eqv_of_le_of_le (Q'.le_trans' v u 0 (Q'.ge_of_eqv h) hu0) hv
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    exact Q'.eqv_trans _ _ _ (sinFull_approx_eqv_zero huz n)
      (Q'.eqv_symm (sinFull_approx_eqv_zero hvz n))
  · -- both negative
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    have h2u : TrigAdd.sinFull u = CReal.neg (Trig.sinNN (Q'.abs u) (Q'.abs_nonneg u)) := by
      unfold TrigAdd.sinFull; rw [if_neg hu]
    have h2v : TrigAdd.sinFull v = CReal.neg (Trig.sinNN (Q'.abs v) (Q'.abs_nonneg v)) := by
      unfold TrigAdd.sinFull; rw [if_neg hv]
    rw [h2u, h2v]
    show (-(Trig.sinPartial (Q'.abs u) n)).eqv (-(Trig.sinPartial (Q'.abs v) n))
    exact Q'.neg_eqv_congr _ _ (TrigAdd.sinPartial_eqv_congr (Q'.abs_eqv_congr h) n)

/-- The general odd law: `sinFull (−A) ≃ −(sinFull A)` for **all** `A : Q'`
(the upstream `sinFull_odd_of_nonneg` only covers `A ≥ 0`). -/
theorem sinFull_neg (A : Q') :
    CReal.Equiv (TrigAdd.sinFull (-A)) (CReal.neg (TrigAdd.sinFull A)) := by
  by_cases hA : (0 : Q') ≤ A
  · exact TrigAdd.sinFull_odd_of_nonneg hA
  · have hnA : (0 : Q') ≤ -A := Q'.neg_nonneg_of_not_nonneg hA
    refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
    have hs1 : TrigAdd.sinFull (-A) = Trig.sinNN (Q'.abs (-A)) (Q'.abs_nonneg (-A)) :=
      TrigAdd.sinFull_of_nonneg hnA
    have hs2 : TrigAdd.sinFull A = CReal.neg (Trig.sinNN (Q'.abs A) (Q'.abs_nonneg A)) := by
      unfold TrigAdd.sinFull; rw [if_neg hA]
    rw [hs1, hs2]
    show (Trig.sinPartial (Q'.abs (-A)) n).eqv (-(-(Trig.sinPartial (Q'.abs A) n)))
    exact Q'.eqv_trans _ _ _ (TrigAdd.sinPartial_eqv_congr (Q'.abs_neg' A) n)
      (Q'.eqv_symm (Q'.neg_neg_eqv (Trig.sinPartial (Q'.abs A) n)))

/-! ## 3. The same-sign (both-nonpositive) signed addition laws -/

/-- **Signed cosine addition law, `A ≤ 0, B ≤ 0` quadrant.**
`cosFull (A+B) ≃ cosFull A·cosFull B − sinFull A·sinFull B`. -/
theorem cos_add_equiv_negneg {A B : Q'} (hA : A ≤ 0) (hB : B ≤ 0) :
    CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosProdMinus A B) := by
  have hA' : (0 : Q') ≤ -A := Q'.nonneg_neg_of_nonpos hA
  have hB' : (0 : Q') ≤ -B := Q'.nonneg_neg_of_nonpos hB
  -- e1: reduce the argument via evenness (abs only).
  have habs : (Q'.abs (A + B)).eqv (Q'.abs ((-A) + (-B))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.abs_neg' (A + B)))
      (Q'.abs_eqv_congr (Q'.neg_add_eqv A B))
  have e1 : CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosFull ((-A) + (-B))) :=
    cosFull_abs_congr habs
  -- e2: the unconditional nonneg cosine core on (−A),(−B).
  have e2 : CReal.Equiv (TrigAdd.cosFull ((-A) + (-B))) (TrigAdd.cosProdMinus (-A) (-B)) :=
    TrigAdd.cos_add_equiv_nonneg (-A) (-B) hA' hB'
  -- e3: rewrite the RHS back in terms of A, B (parity of the factors).
  have ecos : CReal.Equiv (CReal.mul (TrigAdd.cosFull (-A)) (TrigAdd.cosFull (-B)))
      (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull B)) :=
    (CReal.mul_congr_left (TrigAdd.cosFull_even A)).trans
      (mul_congr_right (TrigAdd.cosFull_even B))
  have esin : CReal.Equiv (CReal.mul (TrigAdd.sinFull (-A)) (TrigAdd.sinFull (-B)))
      (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull B)) :=
    (CReal.mul_congr_left (sinFull_neg A)).trans
      ((mul_congr_right (sinFull_neg B)).trans
        (neg_mul_neg (TrigAdd.sinFull A) (TrigAdd.sinFull B)))
  have e3 : CReal.Equiv (TrigAdd.cosProdMinus (-A) (-B)) (TrigAdd.cosProdMinus A B) := by
    unfold TrigAdd.cosProdMinus
    exact (CReal.add_congr_left ecos).trans (CReal.add_congr_right (CReal.neg_congr esin))
  exact e1.trans (e2.trans e3)

/-- **Signed sine addition law, `A ≤ 0, B ≤ 0` quadrant.**
`sinFull (A+B) ≃ sinFull A·cosFull B + cosFull A·sinFull B`. -/
theorem sin_add_equiv_negneg {A B : Q'} (hA : A ≤ 0) (hB : B ≤ 0) :
    CReal.Equiv (TrigAdd.sinFull (A + B)) (TrigSineAddCReal.sinProdPlus A B) := by
  have hA' : (0 : Q') ≤ -A := Q'.nonneg_neg_of_nonpos hA
  have hB' : (0 : Q') ≤ -B := Q'.nonneg_neg_of_nonpos hB
  -- nonneg core on (−A),(−B).
  have core : CReal.Equiv (TrigAdd.sinFull ((-A) + (-B)))
      (TrigSineAddCReal.sinProdPlus (-A) (-B)) :=
    TrigAdd.sin_add_equiv_nonneg (-A) (-B) hA' hB'
  -- sinFull (A+B) ≃ −sinFull ((−A)+(−B)) (odd, via the argument equivalence).
  have harg : (A + B).eqv (-((-A) + (-B))) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (-A) (-B))
      (Q'.add_eqv_congr' (Q'.neg_neg_eqv A) (Q'.neg_neg_eqv B)))
  have step1 : CReal.Equiv (TrigAdd.sinFull (A + B))
      (CReal.neg (TrigSineAddCReal.sinProdPlus (-A) (-B))) :=
    ((sinFull_eqv_congr harg).trans (sinFull_neg ((-A) + (-B)))).trans (CReal.neg_congr core)
  -- −sinProdPlus(−A)(−B) ≃ sinProdPlus A B (distribute the negation, parity of factors).
  have negP : CReal.Equiv
      (CReal.neg (CReal.mul (TrigAdd.sinFull (-A)) (TrigAdd.cosFull (-B))))
      (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B)) :=
    (CReal.neg_congr
      (((CReal.mul_congr_left (sinFull_neg A)).trans
        (mul_congr_right (TrigAdd.cosFull_even B))).trans
        (neg_mul (TrigAdd.sinFull A) (TrigAdd.cosFull B)))).trans
      (neg_neg_equiv (CReal.mul (TrigAdd.sinFull A) (TrigAdd.cosFull B)))
  have negQ : CReal.Equiv
      (CReal.neg (CReal.mul (TrigAdd.cosFull (-A)) (TrigAdd.sinFull (-B))))
      (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B)) :=
    (CReal.neg_congr
      (((CReal.mul_congr_left (TrigAdd.cosFull_even A)).trans
        (mul_congr_right (sinFull_neg B))).trans
        (mul_neg (TrigAdd.cosFull A) (TrigAdd.sinFull B)))).trans
      (neg_neg_equiv (CReal.mul (TrigAdd.cosFull A) (TrigAdd.sinFull B)))
  have step2 : CReal.Equiv (CReal.neg (TrigSineAddCReal.sinProdPlus (-A) (-B)))
      (TrigSineAddCReal.sinProdPlus A B) := by
    unfold TrigSineAddCReal.sinProdPlus
    exact (neg_add_distrib _ _).trans
      ((CReal.add_congr_left negP).trans (CReal.add_congr_right negQ))
  exact step1.trans step2

/-! ## 4. The opposite-sign residual (honest, named `Type`-level data) -/

/-- **Named residual `PythFull`.**  The series-level Pythagorean identity
`cosFull A² + sinFull A² ≃ 1` for `A ≥ 0`.  It does not exist for these series and
cannot be bootstrapped from the signed add-law (circular).  It is the sole gate for
the opposite-sign (subtraction) quadrant.  Not inhabited here. -/
structure PythFull : Type where
  pyth : ∀ (A : Q'), (0 : Q') ≤ A →
    CReal.Equiv
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull A))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull A)))
      CReal.cone

/-- **Named residual `OppositeSignCosCore`.**  The opposite-sign (subtraction)
cosine law `cosFull (A − C) ≃ cosFull A·cosFull C + sinFull A·sinFull C` for
`A, C ≥ 0`.  Its derivation from the nonneg add-law is exactly what requires
`PythFull`.  Not inhabited here. -/
structure OppositeSignCosCore : Type where
  core : ∀ (A C : Q'), (0 : Q') ≤ A → (0 : Q') ≤ C →
    CReal.Equiv (TrigAdd.cosFull (A + (-C)))
      (CReal.add (CReal.mul (TrigAdd.cosFull A) (TrigAdd.cosFull C))
        (CReal.mul (TrigAdd.sinFull A) (TrigAdd.sinFull C)))

end TrigSignedAdd

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.TrigSignedAdd.sinCD_add
#print axioms ConstructiveReals.TrigSignedAdd.neg_mul_neg
#print axioms ConstructiveReals.TrigSignedAdd.mul_congr_right
#print axioms ConstructiveReals.TrigSignedAdd.cosFull_abs_congr
#print axioms ConstructiveReals.TrigSignedAdd.sinFull_approx_eqv_zero
#print axioms ConstructiveReals.TrigSignedAdd.sinFull_eqv_congr
#print axioms ConstructiveReals.TrigSignedAdd.sinFull_neg
#print axioms ConstructiveReals.TrigSignedAdd.cos_add_equiv_negneg
#print axioms ConstructiveReals.TrigSignedAdd.sin_add_equiv_negneg
