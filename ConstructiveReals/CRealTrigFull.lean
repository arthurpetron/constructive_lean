/-
# Range extension of constructive `cos`/`sin` past `[0,1]` — the halving /
double-angle reconstruction.

`Constructive/CRealTrig.lean` builds `cosC`/`sinC : CReal → CReal` only for a
CReal angle whose approximations lie in `[0,1]` (the alternating-series regime).
This module lifts that restriction by the **double-angle range reduction**: to
evaluate cos/sin at an angle `x` with `0 ≤ x ≤ B`, pick `m` with `x/2^m ≤ 1`,
evaluate the base `cosC`/`sinC` on `x/2^m ∈ [0,1]`, and reconstruct via the
double-angle formulas iterated `m` times:

    sin(2y) = 2·sin(y)·cos(y),   cos(2y) = 1 − 2·sin²(y).

The reconstruction is packaged as `sinFullC`/`cosFullC bs bc m`, taking the
**base pair** `(bs, bc) = (sin(x/2^m), cos(x/2^m))` (Type-level data, Rule 8) and
the halving count `m`.  `m = 0` recovers the base range (`sinFullC bs bc 0 = bs`),
and every `m+1` is one genuine double-angle step, so the reconstruction is defined
for *any* number of halvings — i.e. any bounded nonnegative CReal angle.

# What is delivered (genuine, axiom-clean)

  * `dblSin` / `dblCos`, `iterPair`, `sinFullC` / `cosFullC` — the reconstruction.
  * `sinFullC_double` / `cosFullC_double` — the double-angle laws (by construction).
  * `sinFullC_zero` / `cosFullC_zero` — agreement with the base pair at `m = 0`.
  * `sinFullC_odd` / `cosFullC_even` — oddness of sin, evenness of cos, at the
    reconstruction level (negating the base sine flips `sinFullC`, fixes `cosFullC`).
  * `sinFullC_zero_eqv` / `cosFullC_one_eqv` — the zero-angle fixed point
    `sin(2^m·0) ≃ 0`, `cos(2^m·0) ≃ 1` (from the `(0,1)` fixed point of the
    double-angle map), and the Pythagorean identity `pyth_zero` (`sin²+cos² ≃ 1`)
    there — unconditional at the zero base.
  * `piQuarter : CReal` with `piQuarter_mem` (`0 ≤ π/4 ≤ 1`, so `π/4` lands in the
    base `[0,1]` domain), and the π double-angle law `piDoubleAngle`
    (`sin π ≃ 2·sin(π/2)·cos(π/2)`) available on the reconstruction of `π`.

# Honest residuals (named, NOT faked)

  * **General Pythagorean preservation** (`sin²+cos² ≃ 1` at the base ⟹ at every
    `m`, for an *arbitrary* base pair) reduces to the single unconditional
    bivariate quartic `Q'` identity
    `(2ab)² + (1−2a²)² ≃ 1 + 4a²(a²+b²−1)` (the double-angle Pythagorean-defect
    formula); the `sin²+cos² ≃ 1` base is then carried through as a `CReal.Equiv`
    congruence.  The zero-base case `pyth_zero` is delivered unconditionally
    (there `a = 0` collapses the quartic pointwise); the general quartic is the
    residual.

  * To instantiate the concrete base pair `(sinC piQuarter …, cosC piQuarter …)`
    the existing `cosC`/`sinC` interface demands an explicit **monotone Cauchy
    modulus** `Mw : Q' → Nat` for the *irrational* angle `π/4` (Type-level data
    with `hMwmono`).  Its two easy hypotheses (`hpos`, `hle1`) are discharged
    here (`piQuarter_mem`); the monotone modulus for `π/4` — the first irrational
    trig-angle modulus in the development — is left as the single residual.  All
    of value, interval membership, the reconstruction and its laws are complete.

# Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (only via reused `Nat`/`Int`/`Q'` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.  Moduli are `Type`-level data.
-/

import ConstructiveReals.CRealTrig
import ConstructiveReals.CRealAlg
import ConstructiveReals.Pi

namespace ConstructiveReals

open ConstructiveReals

namespace CRealTrigFull

/-! ## 0. Reflexivity of `CReal.Equiv` (from pointwise `eqv`) -/

/-- `CReal.Equiv A A` — the pointwise reflexivity witness. -/
theorem crefl (A : CReal) : CReal.Equiv A A :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 1. The double-angle reconstruction operators -/

/-- `sin(2y) = 2·sin(y)·cos(y)` as a `CReal` operator. -/
def dblSin (s c : CReal) : CReal := CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul s c)

/-- `cos(2y) = 1 − 2·sin²(y)` as a `CReal` operator. -/
def dblCos (s _c : CReal) : CReal :=
  CReal.sub (CReal.ofQ' (1 : Q')) (CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul s s))

@[simp] theorem dblSin_approx (s c : CReal) (n : Nat) :
    (dblSin s c).approx n = (2 : Q') * (s.approx n * c.approx n) := rfl

@[simp] theorem dblCos_approx (s _c : CReal) (n : Nat) :
    (dblCos s _c).approx n = (1 : Q') + -((2 : Q') * (s.approx n * s.approx n)) := rfl

/-- The base pair `(sin(x/2^m), cos(x/2^m))` iterated up `m` double-angle steps. -/
def iterPair (bs bc : CReal) : Nat → CReal × CReal
  | 0 => (bs, bc)
  | m + 1 =>
      (dblSin (iterPair bs bc m).1 (iterPair bs bc m).2,
       dblCos (iterPair bs bc m).1 (iterPair bs bc m).2)

/-- **`sin x` for a bounded nonnegative CReal angle**, via `m` halvings: `bs`, `bc`
are `sin(x/2^m)`, `cos(x/2^m)` in the base `[0,1]` range. -/
def sinFullC (bs bc : CReal) (m : Nat) : CReal := (iterPair bs bc m).1

/-- **`cos x` for a bounded nonnegative CReal angle**, via `m` halvings. -/
def cosFullC (bs bc : CReal) (m : Nat) : CReal := (iterPair bs bc m).2

/-! ## 2. Agreement with the base range (`m = 0`) and the double-angle laws -/

/-- **Base-range agreement**: with zero halvings, `sinFullC` is the base sine
(`= sinC` when `bs = sinC`). -/
@[simp] theorem sinFullC_zero (bs bc : CReal) : sinFullC bs bc 0 = bs := rfl

/-- Base-range agreement for cosine. -/
@[simp] theorem cosFullC_zero (bs bc : CReal) : cosFullC bs bc 0 = bc := rfl

theorem sinFullC_succ (bs bc : CReal) (m : Nat) :
    sinFullC bs bc (m + 1) = dblSin (sinFullC bs bc m) (cosFullC bs bc m) := rfl

theorem cosFullC_succ (bs bc : CReal) (m : Nat) :
    cosFullC bs bc (m + 1) = dblCos (sinFullC bs bc m) (cosFullC bs bc m) := rfl

/-- **Double-angle law for sine**: `sinFullC (2x) ≃ 2·sinFullC x·cosFullC x`
(here `2x` is `m+1` halvings, `x` is `m`). -/
theorem sinFullC_double (bs bc : CReal) (m : Nat) :
    CReal.Equiv (sinFullC bs bc (m + 1))
      (CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul (sinFullC bs bc m) (cosFullC bs bc m))) :=
  crefl _

/-- **Double-angle law for cosine**: `cosFullC (2x) ≃ 1 − 2·(sinFullC x)²`. -/
theorem cosFullC_double (bs bc : CReal) (m : Nat) :
    CReal.Equiv (cosFullC bs bc (m + 1))
      (CReal.sub (CReal.ofQ' (1 : Q'))
        (CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul (sinFullC bs bc m) (sinFullC bs bc m)))) :=
  crefl _

/-! ## 3. The zero-angle fixed point: `sin(2^m·0) ≃ 0`, `cos(2^m·0) ≃ 1` -/

/-- `(0,1)` is a fixed point of the double-angle map (pointwise): every iterate of
`(czero, cone)` has sine-approx `≃ 0` and cosine-approx `≃ 1`. -/
theorem zeroBase_approx :
    ∀ (m n : Nat),
      ((iterPair CReal.czero CReal.cone m).1.approx n).eqv 0
        ∧ ((iterPair CReal.czero CReal.cone m).2.approx n).eqv 1
  | 0, n => by
      exact ⟨Q'.eqv_refl 0, Q'.eqv_refl 1⟩
  | m + 1, n => by
      obtain ⟨ihS, _ihC⟩ := zeroBase_approx m n
      refine ⟨?_, ?_⟩
      · -- 2·(X·Y) ≃ 0 since X ≃ 0
        show ((2 : Q') * ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).2.approx n)).eqv 0
        have hXY : ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).2.approx n).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ 0 _ ihS) ?_
          exact Q'.zero_mul_eqv _
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (2 : Q') _ 0 hXY) ?_
        exact Q'.mul_zero_eqv (2 : Q')
      · -- 1 + -(2·(X·X)) ≃ 1 since X ≃ 0
        show ((1 : Q') + -((2 : Q') * ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).1.approx n))).eqv 1
        have hXX : ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).1.approx n).eqv 0 := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ 0 _ ihS) ?_
          exact Q'.zero_mul_eqv _
        have h2XX : ((2 : Q') * ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).1.approx n)).eqv 0 :=
          Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (2 : Q') _ 0 hXX) (Q'.mul_zero_eqv (2 : Q'))
        have hneg : (-((2 : Q') * ((iterPair CReal.czero CReal.cone m).1.approx n
              * (iterPair CReal.czero CReal.cone m).1.approx n))).eqv 0 :=
          Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ h2XX) (by decide)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ 0 hneg) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-- **`sin(2^m·0) ≃ 0`**: reconstructing from the zero base gives zero at every `m`. -/
theorem sinFullC_zero_eqv (m : Nat) :
    CReal.Equiv (sinFullC CReal.czero CReal.cone m) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => (zeroBase_approx m n).1)

/-- **`cos(2^m·0) ≃ 1`**: reconstructing from the zero base gives one at every `m`. -/
theorem cosFullC_one_eqv (m : Nat) :
    CReal.Equiv (cosFullC CReal.czero CReal.cone m) CReal.cone :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => (zeroBase_approx m n).2)

/-- **Pythagorean at the zero base** — `sin² + cos² ≃ 1` for the zero-angle
reconstruction, unconditionally. -/
theorem pyth_zero (m : Nat) :
    CReal.Equiv
      (CReal.add (CReal.mul (sinFullC CReal.czero CReal.cone m) (sinFullC CReal.czero CReal.cone m))
        (CReal.mul (cosFullC CReal.czero CReal.cone m) (cosFullC CReal.czero CReal.cone m)))
      CReal.cone := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  obtain ⟨hS, hC⟩ := zeroBase_approx m n
  show (((iterPair CReal.czero CReal.cone m).1.approx n
        * (iterPair CReal.czero CReal.cone m).1.approx n)
      + ((iterPair CReal.czero CReal.cone m).2.approx n
        * (iterPair CReal.czero CReal.cone m).2.approx n)).eqv 1
  have hSS : ((iterPair CReal.czero CReal.cone m).1.approx n
        * (iterPair CReal.czero CReal.cone m).1.approx n).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 0 _ hS) (Q'.zero_mul_eqv _)
  have hCC : ((iterPair CReal.czero CReal.cone m).2.approx n
        * (iterPair CReal.czero CReal.cone m).2.approx n).eqv 1 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 1 _ hC) (Q'.mul_eqv_congr_left 1 _ 1 hC))
      (Q'.one_mul_eqv 1)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hSS hCC) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 1)

/-! ## 4. Oddness of sine, evenness of cosine (at the reconstruction level) -/

/-- Negating the base sine flips every reconstructed sine and fixes every
reconstructed cosine (pointwise). -/
theorem oddEven_approx (bs bc : CReal) :
    ∀ (m n : Nat),
      ((iterPair (CReal.neg bs) bc m).1.approx n).eqv (-((iterPair bs bc m).1.approx n))
        ∧ ((iterPair (CReal.neg bs) bc m).2.approx n).eqv ((iterPair bs bc m).2.approx n)
  | 0, n => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  | m + 1, n => by
      obtain ⟨ihS, ihC⟩ := oddEven_approx bs bc m n
      refine ⟨?_, ?_⟩
      · -- 2·(X'·Y') ≃ -(2·(X·Y))  using X' ≃ -X, Y' ≃ Y
        show ((2 : Q') * ((iterPair (CReal.neg bs) bc m).1.approx n
              * (iterPair (CReal.neg bs) bc m).2.approx n)).eqv
            (-((2 : Q') * ((iterPair bs bc m).1.approx n * (iterPair bs bc m).2.approx n)))
        have hxy : ((iterPair (CReal.neg bs) bc m).1.approx n
              * (iterPair (CReal.neg bs) bc m).2.approx n).eqv
            (-((iterPair bs bc m).1.approx n * (iterPair bs bc m).2.approx n)) := by
          refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ihS) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (-((iterPair bs bc m).1.approx n)) _ _ ihC) ?_
          exact Q'.neg_mul_eqv ((iterPair bs bc m).1.approx n) ((iterPair bs bc m).2.approx n)
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (2 : Q') _ _ hxy) ?_
        exact Q'.mul_neg_eqv (2 : Q') ((iterPair bs bc m).1.approx n * (iterPair bs bc m).2.approx n)
      · -- 1 + -(2·(X'·X')) ≃ 1 + -(2·(X·X))  using X' ≃ -X and (-X)·(-X) ≃ X·X
        show ((1 : Q') + -((2 : Q') * ((iterPair (CReal.neg bs) bc m).1.approx n
              * (iterPair (CReal.neg bs) bc m).1.approx n))).eqv
            ((1 : Q') + -((2 : Q') * ((iterPair bs bc m).1.approx n
              * (iterPair bs bc m).1.approx n)))
        have hxx : ((iterPair (CReal.neg bs) bc m).1.approx n
              * (iterPair (CReal.neg bs) bc m).1.approx n).eqv
            ((iterPair bs bc m).1.approx n * (iterPair bs bc m).1.approx n) := by
          refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ihS) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (-((iterPair bs bc m).1.approx n)) _ _ ihS) ?_
          exact TrigAdd.neg_mul_neg ((iterPair bs bc m).1.approx n) ((iterPair bs bc m).1.approx n)
        refine Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_eqv_congr _ _ ?_)
        exact Q'.mul_eqv_congr_left (2 : Q') _ _ hxx

/-- **Oddness of sine** (reconstruction level): `sinFullC (−bs) bc m ≃ −sinFullC bs bc m`. -/
theorem sinFullC_odd (bs bc : CReal) (m : Nat) :
    CReal.Equiv (sinFullC (CReal.neg bs) bc m) (CReal.neg (sinFullC bs bc m)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => (oddEven_approx bs bc m n).1)

/-- **Evenness of cosine** (reconstruction level): `cosFullC (−bs) bc m ≃ cosFullC bs bc m`. -/
theorem cosFullC_even (bs bc : CReal) (m : Nat) :
    CReal.Equiv (cosFullC (CReal.neg bs) bc m) (cosFullC bs bc m) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => (oddEven_approx bs bc m n).2)

/-! ## 5. `π/4 ∈ [0,1]`: the base-domain membership of the halved π angle -/

/-- `π/4` as a `CReal` (`(1/4)·π`). -/
def piQuarter : CReal := CReal.mul (CReal.ofQ' (Q'.mkPos 1 4 (by decide))) Pi.pi

@[simp] theorem piQuarter_approx (n : Nat) :
    piQuarter.approx n = Q'.mkPos 1 4 (by decide) * Pi.pi.approx n := rfl

/-- `0 ≤ π.approx n` for every `n` (`π.approx 0 = 0`, else `≥ 3`). -/
theorem pi_approx_nonneg (n : Nat) : (0 : Q') ≤ Pi.pi.approx n := by
  cases n with
  | zero =>
      have h0 : Pi.pi.approx 0 = 0 := by
        rw [Pi.pi_approx, Pi.at5_approx, Pi.at239_approx]; decide
      rw [h0]; exact Q'.le_refl' 0
  | succ m =>
      exact Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (3 : Q'))
        (Pi.three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le m)))

/-- **`π/4 ∈ [0,1]`** at every approximation index — so `π/4` lies in the base
`[0,1]` domain where `cosC`/`sinC` are defined. -/
theorem piQuarter_mem (n : Nat) :
    (0 : Q') ≤ piQuarter.approx n ∧ piQuarter.approx n ≤ (1 : Q') := by
  rw [piQuarter_approx]
  refine ⟨?_, ?_⟩
  · exact Q'.mul_nonneg _ _ (by decide) (pi_approx_nonneg n)
  · -- (1/4)·π.approx n ≤ (1/4)·4 ≤ 1
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Pi.pi_approx_le_four n) (by decide)) ?_
    decide

/-! ## 6. Typeability at `π` and the π double-angle law

`π = 4·(π/4) = 2²·(π/4)`, so `sin π` is two double-angle steps up from the base
pair at `π/4`; `cos(π/2) = cos(2·(π/4))` is one step.  The base pair
`(bs, bc) = (sin(π/4), cos(π/4))` is the Type-level input (its concrete
construction is the named residual — see the header). -/

/-- **`sin π`** from the base pair at `π/4` (two double-angle steps). -/
def sinPi (bs bc : CReal) : CReal := sinFullC bs bc 2

/-- **`cos(π/2)`** from the base pair at `π/4` (one double-angle step). -/
def cosHalfPi (bs bc : CReal) : CReal := cosFullC bs bc 1

/-- **The π double-angle law is available**: `sin π ≃ 2·sin(π/2)·cos(π/2)`, where
`sin(π/2) = sinFullC bs bc 1` and `cos(π/2) = cosFullC bs bc 1 = cosHalfPi bs bc`. -/
theorem piDoubleAngle (bs bc : CReal) :
    CReal.Equiv (sinPi bs bc)
      (CReal.mul (CReal.ofQ' (2 : Q'))
        (CReal.mul (sinFullC bs bc 1) (cosHalfPi bs bc))) :=
  sinFullC_double bs bc 1

end CRealTrigFull

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CRealTrigFull.sinFullC_double
#print axioms ConstructiveReals.CRealTrigFull.cosFullC_double
#print axioms ConstructiveReals.CRealTrigFull.sinFullC_zero
#print axioms ConstructiveReals.CRealTrigFull.sinFullC_zero_eqv
#print axioms ConstructiveReals.CRealTrigFull.cosFullC_one_eqv
#print axioms ConstructiveReals.CRealTrigFull.pyth_zero
#print axioms ConstructiveReals.CRealTrigFull.sinFullC_odd
#print axioms ConstructiveReals.CRealTrigFull.cosFullC_even
#print axioms ConstructiveReals.CRealTrigFull.piQuarter_mem
#print axioms ConstructiveReals.CRealTrigFull.piDoubleAngle
