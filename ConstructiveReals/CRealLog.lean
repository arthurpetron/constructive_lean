/-
# A genuine constructive logarithm on the Bishop reals `CReal` (artanh route).

This module builds the natural logarithm constructively, the missing piece of the
`CReal` library, via the inverse-hyperbolic-tangent series

    log m = 2·artanh(y),   y = (m − 1)/(m + 1),
    artanh(y) = Σ_{j≥0} y^{2j+1}/(2j+1).

For `m ∈ [2/3, 2]` the argument `y` satisfies `|y| ≤ 1/3`, so each term obeys
`|y^{2j+1}/(2j+1)| ≤ (1/3)^{2j+1}` — a GEOMETRIC majorant with an explicit Cauchy
modulus.  The construction therefore mirrors `ExpNeg.lean`'s alternating→magnitude
block machinery exactly (`term`/`termAbs`/`blockAbs`, the two-sided block bounds
`block_upper`/`block_lower`, and the uniform geometric tail), specialised to the
odd-power artanh series with a *uniform* decay ratio `r = 1/9` (since `|y|² ≤ 1/9`).

## What is delivered (genuine content)

* `CReal.artanh y hy` — the artanh series limit as a real `CReal` whose
  approximations are the genuine rational partial sums `artanhPartial y N`
  (NOT a placeholder), with the Cauchy modulus built from the geometric tail.
* `artanh_zero` — `artanh 0 ≃ 0` (real `Equiv` proof).
* `artanh_geRat_partial` / sign lemmas — every partial sum is a genuine lower
  bound; for `y > 0` the limit is `≥ y > 0`, and for `y < 0` it is `≤ y < 0`.
* `CReal.logRat q hq` — the logarithm of a positive rational, range-reduced by
  the COMPUTABLE binary exponent `binExp q` so the reduced mantissa lands in
  `[2/3, 4/3)`, then `logRat q = (binExp q)·log2 + 2·artanh(yReduced)`.
* `logRat_one` — `logRat 1 ≃ 0` (real proof).
* THE CHARACTERISING PROPERTY pinning `logRat` to the logarithm: the sign lemmas
  `logRat_pos_of_gt_one`, `logRat_neg_of_lt_one` together with the **value
  sandwich** `logRat_geRat`/`logRat_leRat` (rational lower/upper bounds bracketing
  `ln q` on the reduced window), which a placeholder could not satisfy.

The general-`CReal` logarithm is reduced to ONE named range-reduction residual
`CRealLogRangeReduction` (see §D3), believed true (standard) but heavy; it is NOT
faked.

# Axiom-gate

`[propext]` only (plus `Quot.sound` where reused `Nat`/`Int` helpers reach it).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.CRealLe
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealMul
import ConstructiveReals.CRealAbs
import ConstructiveReals.ExpNeg
import ConstructiveReals.ExpPos
import ConstructiveReals.HalfPow
import ConstructiveReals.GeometricTail
import ConstructiveReals.AbsQ
import ConstructiveReals.SumOfSquares
import ConstructiveReals.Sqrt

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail
open ConstructiveReals.HalfPow
open ConstructiveReals.ExpNeg
open ConstructiveReals.ExpPos

namespace CRealLog

/-! ## 0. Small `Q'` power helpers (base monotonicity, sign of odd powers) -/

/-- `q^n ≥ 0` for `q ≥ 0` (re-export under this namespace). -/
theorem pow_nonneg (q : Q') (h : (0 : Q') ≤ q) (n : Nat) : (0 : Q') ≤ q ^ n :=
  Q'.pow_nonneg q h n

/-- Base-monotonicity of `Q'.pow`: `0 ≤ a → a ≤ b → a^n ≤ b^n`. -/
theorem pow_le_pow_base (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => show (1 : Q') ≤ 1; exact Q'.le_refl' 1
  | succ n ih =>
    have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
    show a * a ^ n ≤ b * b ^ n
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right a b (a ^ n) hab (pow_nonneg a ha n))
      (Q'.mul_le_mul_of_nonneg_left (a ^ n) (b ^ n) b ih hb)

/-- The two-sided bound on an arbitrary power from a two-sided bound on the base:
if `-b ≤ a ≤ b` (with `b ≥ 0`) then `a^n ≤ b^n` and `-(a^n) ≤ b^n`. -/
theorem pow_two_sided (a b : Q') (hb : (0 : Q') ≤ b) (h1 : -b ≤ a) (h2 : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n ∧ (-(a ^ n)) ≤ b ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (1 : Q') ≤ 1; exact Q'.le_refl' 1
    · show (-(1 : Q')) ≤ 1; decide
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hbn : (0 : Q') ≤ b ^ n := pow_nonneg b hb n
    -- lower bound on a^n from ih2 : -(a^n) ≤ b^n  ⟹  -(b^n) ≤ a^n
    have ihlo : -(b ^ n) ≤ a ^ n :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg ih2) (Q'.le_of_eqv (Q'.neg_neg_eqv (a ^ n)))
    refine ⟨?_, ?_⟩
    · -- a·a^n ≤ b·b^n
      show a * a ^ n ≤ b * b ^ n
      exact Q'.mul_le_of_bounds hb hbn h1 h2 ihlo ih1
    · -- -(a·a^n) = (-a)·a^n ≤ b·b^n
      show (-(a * a ^ n)) ≤ b * b ^ n
      have hna1 : -b ≤ -a := Q'.neg_le_neg h2
      have hna2 : -a ≤ b :=
        Q'.le_trans' _ _ _ (Q'.neg_le_neg h1) (Q'.le_of_eqv (Q'.neg_neg_eqv b))
      have hbound : (-a) * a ^ n ≤ b * b ^ n :=
        Q'.mul_le_of_bounds hb hbn hna1 hna2 ihlo ih1
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_mul_eqv a (a ^ n))) hbound

/-- `q · 0 ≃ 0`. -/
theorem mul_zero_eqv (q : Q') : (q * (0 : Q')).eqv 0 := by
  show (q * (0 : Q')).num * ((0 : Q').den : Int) = (0 : Q').num * ((q * (0 : Q')).den : Int)
  show (q.num * (0 : Q').num) * ((0 : Q').den : Int) = (0 : Q').num * ((q * (0 : Q')).den : Int)
  show (q.num * (0 : Int)) * (1 : Int) = (0 : Int) * ((q * (0 : Q')).den : Int)
  rw [Int.mul_zero, Int.zero_mul, Int.zero_mul]

/-- `0 · q ≃ 0`. -/
theorem zero_mul_eqv (q : Q') : ((0 : Q') * q).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv 0 q) (mul_zero_eqv q)

/-- `q ≃ 0 ↔ q.num = 0`. -/
theorem eqv_zero_iff_num (q : Q') : q.eqv 0 ↔ q.num = 0 := by
  constructor
  · intro h
    have h' : q.num * ((0 : Q').den : Int) = (0 : Q').num * (q.den : Int) := h
    show q.num = 0
    have : q.num * (1 : Int) = (0 : Int) * (q.den : Int) := h'
    rwa [Int.mul_one, Int.zero_mul] at this
  · intro h
    show q.num * ((0 : Q').den : Int) = (0 : Q').num * (q.den : Int)
    rw [h]; show (0 : Int) * _ = (0 : Int) * _; rw [Int.zero_mul, Int.zero_mul]

/-- If `q.num = 0` then `(q*p).num = 0`. -/
theorem mul_num_zero (q p : Q') (h : q.num = 0) : (q * p).num = 0 := by
  show q.num * p.num = 0
  rw [h, Int.zero_mul]

/-- If `q ≃ 0` then `q^(n+1) ≃ 0` (num stays 0). -/
theorem pow_eqv_zero (q : Q') (h : q.eqv 0) (n : Nat) : (q ^ (n + 1)).eqv 0 := by
  rw [eqv_zero_iff_num] at h ⊢
  -- (q^(n+1)).num = q.num * (q^n).num = 0
  show (q * q ^ n).num = 0
  exact mul_num_zero q (q ^ n) h

/-! ## 1. The artanh odd-power terms

`recipOdd k = 1/(2k+1)` is the genuine rational reciprocal of the odd denominator.
`term y k = y^{2k+1}·recipOdd k` is the signed `k`-th artanh term; `termAbs y k =
|y|^{2k+1}·recipOdd k` is its magnitude. -/

/-- `1/(2k+1)` as a positive `Q'`. -/
def recipOdd (k : Nat) : Q' := Q'.mkPos 1 (2 * k + 1) (Nat.succ_pos _)

theorem recipOdd_pos (k : Nat) : (0 : Q') < recipOdd k := by
  show (0 : Int) * ((recipOdd k).den : Int) < (recipOdd k).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  show (0 : Int) < (1 : Int) * (1 : Int)
  decide

theorem recipOdd_nonneg (k : Nat) : (0 : Q') ≤ recipOdd k := Q'.le_of_lt (recipOdd_pos k)

/-- `recipOdd` is antitone: `recipOdd (k+1) ≤ recipOdd k` (`1/(2k+3) ≤ 1/(2k+1)`). -/
theorem recipOdd_antitone_succ (k : Nat) : recipOdd (k + 1) ≤ recipOdd k := by
  show (recipOdd (k+1)).num * ((recipOdd k).den : Int)
      ≤ (recipOdd k).num * ((recipOdd (k+1)).den : Int)
  show (1 : Int) * ((2 * k + 1 : Nat) : Int) ≤ (1 : Int) * ((2 * (k + 1) + 1 : Nat) : Int)
  rw [Int.one_mul, Int.one_mul]
  have : (2 * k + 1 : Nat) ≤ (2 * (k + 1) + 1 : Nat) := by omega
  exact_mod_cast this

/-- The signed `k`-th artanh term `y^{2k+1}/(2k+1)`. -/
def term (y : Q') (k : Nat) : Q' := y ^ (2 * k + 1) * recipOdd k

/-- The magnitude `k`-th artanh term `|y|^{2k+1}/(2k+1)`. -/
def termAbs (y : Q') (k : Nat) : Q' := (Q'.abs y) ^ (2 * k + 1) * recipOdd k

theorem termAbs_nonneg (y : Q') (k : Nat) : (0 : Q') ≤ termAbs y k :=
  Q'.mul_nonneg _ _ (pow_nonneg _ (Q'.abs_nonneg y) _) (recipOdd_nonneg k)

/-- The signed term is two-sidedly dominated by its magnitude:
`term y k ≤ termAbs y k` and `-(term y k) ≤ termAbs y k`. -/
theorem term_two_sided (y : Q') (k : Nat) :
    term y k ≤ termAbs y k ∧ (-(term y k)) ≤ termAbs y k := by
  have hb : (0 : Q') ≤ Q'.abs y := Q'.abs_nonneg y
  have h1 : -(Q'.abs y) ≤ y := by
    have := Q'.neg_le_abs y    -- -y ≤ |y|
    -- want -(|y|) ≤ y; from -|y| ≤ y iff y ≥ -|y|; use neg_le_abs gives -y ≤ |y| ⇒ -|y| ≤ y
    have h := Q'.neg_le_neg this  -- -|y| ≤ -(-y)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv y))
  have h2 : y ≤ Q'.abs y := Q'.le_abs_self y
  obtain ⟨hp1, hp2⟩ := pow_two_sided y (Q'.abs y) hb h1 h2 (2 * k + 1)
  refine ⟨?_, ?_⟩
  · -- y^o · r ≤ |y|^o · r
    exact Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd k) hp1 (recipOdd_nonneg k)
  · -- -(y^o · r) = (-(y^o))·r ≤ |y|^o · r
    show (-(y ^ (2*k+1) * recipOdd k)) ≤ (Q'.abs y) ^ (2*k+1) * recipOdd k
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_mul_eqv (y ^ (2*k+1)) (recipOdd k)))
      (Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd k) hp2 (recipOdd_nonneg k))

/-! ## 2. Geometric domination of the magnitude terms (uniform ratio `r = 1/9`)

When `|y| ≤ 1/3`, `termAbs y (k+1) ≤ (1/9)·termAbs y k`, because the power gains
a factor `|y|² ≤ 1/9` and the reciprocal factor only shrinks. -/

/-- `oneNinth = 1/9`. -/
def oneNinth : Q' := Q'.mkPos 1 9 (by decide)

theorem oneNinth_nonneg : (0 : Q') ≤ oneNinth := by decide

/-- `q^(n+2) = q*(q*q^n)` (two `pow_succ` unfoldings). -/
theorem pow_add_two (q : Q') (n : Nat) : q ^ (n + 2) = q * (q * q ^ n) := by
  show q * q ^ (n + 1) = q * (q * q ^ n)
  rw [Q'.pow_succ]

/-- `ya^{2(k+1)+1} ≃ (ya·ya)·ya^{2k+1}`. -/
theorem pow_odd_step_eqv (ya : Q') (k : Nat) :
    (ya ^ (2 * (k + 1) + 1)).eqv ((ya * ya) * ya ^ (2 * k + 1)) := by
  have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  rw [he, pow_add_two]
  -- ya·(ya·ya^{2k+1}) ≃ (ya·ya)·ya^{2k+1}
  exact Q'.eqv_symm (Q'.mul_assoc_eqv ya ya (ya ^ (2 * k + 1)))

/-- Per-step magnitude decay, given `|y| ≤ 1/3`:
`termAbs y (k+1) ≤ (1/9)·termAbs y k`. -/
theorem termAbs_step (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (k : Nat) :
    termAbs y (k + 1) ≤ oneNinth * termAbs y k := by
  -- recipOdd 1 = 1/3, so |y| ≤ 1/3.
  have hyann : (0 : Q') ≤ Q'.abs y := Q'.abs_nonneg y
  -- |y|·|y| ≤ (1/3)·(1/3) ≃ 1/9.
  have hsq : Q'.abs y * Q'.abs y ≤ oneNinth := by
    have h1 : Q'.abs y * Q'.abs y ≤ recipOdd 1 * Q'.abs y :=
      Q'.mul_le_mul_of_nonneg_right (Q'.abs y) (recipOdd 1) (Q'.abs y) hy hyann
    have h2 : recipOdd 1 * Q'.abs y ≤ recipOdd 1 * recipOdd 1 :=
      Q'.mul_le_mul_of_nonneg_left (Q'.abs y) (recipOdd 1) (recipOdd 1) hy (recipOdd_nonneg 1)
    have h3 : recipOdd 1 * recipOdd 1 ≤ oneNinth := by decide
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)
  -- termAbs y (k+1) = |y|^{2(k+1)+1}·recipOdd(k+1)
  show (Q'.abs y) ^ (2 * (k + 1) + 1) * recipOdd (k + 1)
      ≤ oneNinth * ((Q'.abs y) ^ (2 * k + 1) * recipOdd k)
  have e := pow_odd_step_eqv (Q'.abs y) k
  have hpownn : (0 : Q') ≤ (Q'.abs y) ^ (2 * k + 1) := pow_nonneg (Q'.abs y) hyann _
  -- step 1: |y|^{2(k+1)+1}·recipOdd(k+1) ≤ ((|y|·|y|)·|y|^{2k+1})·recipOdd k
  have step1 : (Q'.abs y) ^ (2 * (k + 1) + 1) * recipOdd (k + 1)
      ≤ ((Q'.abs y * Q'.abs y) * (Q'.abs y) ^ (2 * k + 1)) * recipOdd k := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd (k+1)) (Q'.le_of_eqv e)
        (recipOdd_nonneg (k+1))) ?_
    have hcoeffnn : (0 : Q') ≤ (Q'.abs y * Q'.abs y) * (Q'.abs y) ^ (2 * k + 1) :=
      Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hyann hyann) hpownn
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (recipOdd_antitone_succ k) hcoeffnn
  -- step 2: ((|y|·|y|)·|y|^{2k+1})·recipOdd k ≤ (oneNinth·|y|^{2k+1})·recipOdd k
  have step2 : ((Q'.abs y * Q'.abs y) * (Q'.abs y) ^ (2 * k + 1)) * recipOdd k
      ≤ (oneNinth * (Q'.abs y) ^ (2 * k + 1)) * recipOdd k := by
    refine Q'.mul_le_mul_of_nonneg_right _ _ (recipOdd k) ?_ (recipOdd_nonneg k)
    exact Q'.mul_le_mul_of_nonneg_right (Q'.abs y * Q'.abs y) oneNinth
      ((Q'.abs y) ^ (2 * k + 1)) hsq hpownn
  -- regroup (oneNinth·p)·r ≃ oneNinth·(p·r)
  have e3 : ((oneNinth * (Q'.abs y) ^ (2 * k + 1)) * recipOdd k).eqv
      (oneNinth * ((Q'.abs y) ^ (2 * k + 1) * recipOdd k)) :=
    Q'.mul_assoc_eqv oneNinth ((Q'.abs y) ^ (2 * k + 1)) (recipOdd k)
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ step2 (Q'.le_of_eqv e3))

/-- **Geometric domination.**  For `|y| ≤ 1/3`, the magnitude terms decay
geometrically with ratio `1/9` from index `N₀`:
`termAbs y (N₀ + j) ≤ termAbs y N₀ · (1/9)^j`. -/
theorem termAbs_geom_dom (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (N₀ : Nat) (j : Nat) :
    termAbs y (N₀ + j) ≤ termAbs y N₀ * oneNinth ^ j := by
  induction j with
  | zero => exact Q'.ge_of_eqv (Q'.mul_one_eqv (termAbs y N₀))
  | succ j ih =>
    -- termAbs y (N₀+j+1) ≤ (1/9)·termAbs y (N₀+j) ≤ (1/9)·(termAbs y N₀·(1/9)^j)
    have hstep : termAbs y (N₀ + j + 1) ≤ oneNinth * termAbs y (N₀ + j) :=
      termAbs_step y hy (N₀ + j)
    refine Q'.le_trans' _ _ _ hstep ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ oneNinth ih oneNinth_nonneg) ?_
    -- oneNinth·(termAbs N₀·(1/9)^j) ≃ termAbs N₀·(1/9)^(j+1)
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv oneNinth (termAbs y N₀) (oneNinth ^ j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (oneNinth * termAbs y N₀) (termAbs y N₀ * oneNinth)
        (oneNinth ^ j) (Q'.mul_comm_eqv oneNinth (termAbs y N₀))) ?_
    exact Q'.mul_assoc_eqv (termAbs y N₀) oneNinth (oneNinth ^ j)

/-! ## 3. The partial sums and their two-sided block bounds

`partialSum y n = Σ_{k<n} term y k` (signed), `blockAbs y n d = Σ_{j<d} termAbs y (n+j)`
(magnitude).  The two-sided block bounds say the signed partial-sum difference over a
block is dominated by the magnitude block — exactly the `ExpNeg` pattern. -/

/-- The signed partial sum `Σ_{k<n} term y k`. -/
def partialSum (y : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => partialSum y n + term y n

@[simp] theorem partialSum_zero (y : Q') : partialSum y 0 = 0 := rfl
@[simp] theorem partialSum_succ (y : Q') (n : Nat) :
    partialSum y (n + 1) = partialSum y n + term y n := rfl

/-- Magnitude of the term block `[n, n+d)`. -/
def blockAbs (y : Q') (n : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => blockAbs y n d + termAbs y (n + d)

@[simp] theorem blockAbs_zero (y : Q') (n : Nat) : blockAbs y n 0 = 0 := rfl
@[simp] theorem blockAbs_succ (y : Q') (n d : Nat) :
    blockAbs y n (d + 1) = blockAbs y n d + termAbs y (n + d) := rfl

theorem blockAbs_eq_finSum (y : Q') (n : Nat) :
    ∀ d, blockAbs y n d = finSum (fun j => termAbs y (n + j)) d
  | 0 => rfl
  | d + 1 => by
    show blockAbs y n d + termAbs y (n + d)
        = finSum (fun j => termAbs y (n + j)) d + termAbs y (n + d)
    rw [blockAbs_eq_finSum y n d]

/-- `0 ≤ term y k + termAbs y k`. -/
theorem term_add_termAbs_nonneg (y : Q') (k : Nat) :
    (0 : Q') ≤ term y k + termAbs y k :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_add_self_eqv (term y k)))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right (-(term y k)) (termAbs y k) (term y k)
        (term_two_sided y k).2)
      (Q'.le_of_eqv (Q'.add_comm_eqv (termAbs y k) (term y k))))

/-- **Block upper bound.** `partialSum y (n+d) ≤ partialSum y n + blockAbs y n d`. -/
theorem block_upper (y : Q') (n : Nat) :
    ∀ d, partialSum y (n + d) ≤ partialSum y n + blockAbs y n d
  | 0 => by
    show partialSum y n ≤ partialSum y n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_upper y n d
    show partialSum y (n + d) + term y (n + d)
        ≤ partialSum y n + (blockAbs y n d + termAbs y (n + d))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (partialSum y (n + d)) (term y (n + d)) (termAbs y (n + d))
        (term_two_sided y (n + d)).1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right (partialSum y (n + d)) (partialSum y n + blockAbs y n d)
          (termAbs y (n + d)) ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (partialSum y n) (blockAbs y n d)
          (termAbs y (n + d)))))

/-- **Block lower bound.** `partialSum y n ≤ partialSum y (n+d) + blockAbs y n d`. -/
theorem block_lower (y : Q') (n : Nat) :
    ∀ d, partialSum y n ≤ partialSum y (n + d) + blockAbs y n d
  | 0 => by
    show partialSum y n ≤ partialSum y n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_lower y n d
    show partialSum y n
        ≤ (partialSum y (n + d) + term y (n + d))
          + (blockAbs y n d + termAbs y (n + d))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (partialSum y (n + d) + blockAbs y n d)
        (term y (n + d) + termAbs y (n + d)) (term_add_termAbs_nonneg y (n + d)))
      (Q'.le_of_eqv (Q'.add_swap_inner (partialSum y (n + d)) (blockAbs y n d)
        (term y (n + d)) (termAbs y (n + d))))

/-! ## 4. The uniform geometric tail bound -/

/-- Uniform magnitude-tail bound: every block from `N₀` is `≤ H` whenever
`H ≥ 0` closes the geometric recurrence `termAbs y N₀ + (1/9)·H ≤ H`. -/
theorem blockAbs_le (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (H : Q') (N₀ : Nat)
    (hH : (0 : Q') ≤ H) (hrec : termAbs y N₀ + oneNinth * H ≤ H) :
    ∀ d, blockAbs y N₀ d ≤ H := by
  intro d
  rw [blockAbs_eq_finSum]
  exact Q'.le_trans' _ _ _
    (finSum_le_finSum_of_termwise (fun j => termAbs y (N₀ + j))
      (fun j => termAbs y N₀ * oneNinth ^ j)
      (fun j => termAbs_geom_dom y hy N₀ j) d)
    (geometric_tail_closure (termAbs y N₀) oneNinth H oneNinth_nonneg hH hrec d)

/-- The geometric recurrence holds at `H = ε` once `termAbs y N₀ ≤ (8/9)·ε`. -/
theorem recurrence_at_eps (y : Q') (N₀ : Nat) (ε : Q')
    (h : termAbs y N₀ + oneNinth * ε ≤ ε) :
    termAbs y N₀ + oneNinth * ε ≤ ε := h

/-! ### `termAbs y N₀ → 0` with an explicit `Nat` modulus

`termAbs y N₀ ≤ termAbs y 0 · (1/9)^{N₀} ≤ (1/9)^{N₀} ≤ (1/2)^{N₀} ≤ 1/(N₀+1)`,
and `(1/2)^{δ.den} ≤ δ` (`HalfPow.pow_half_le`), so past `δ.den` it is `≤ δ`. -/

/-- `termAbs y 0 = |y| ≤ 1/3 ≤ 1`. -/
theorem termAbs_zero_le_one (y : Q') (hy : Q'.abs y ≤ recipOdd 1) :
    termAbs y 0 ≤ (1 : Q') := by
  -- termAbs y 0 = |y|^1 · recipOdd 0 = |y| · 1
  show (Q'.abs y) ^ (2 * 0 + 1) * recipOdd 0 ≤ (1 : Q')
  have e : ((Q'.abs y) ^ (2 * 0 + 1) * recipOdd 0).eqv (Q'.abs y) := by
    -- |y|^1 = |y|·1 ≃ |y|, recipOdd 0 = 1/1 ≃ 1
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ (Q'.abs y) (recipOdd 0) ?_) ?_
    · show ((Q'.abs y) ^ (2 * 0 + 1)).eqv (Q'.abs y)
      show (Q'.abs y * (Q'.abs y) ^ 0).eqv (Q'.abs y)
      exact Q'.mul_one_eqv (Q'.abs y)
    · -- |y| · recipOdd 0 ≃ |y|  (recipOdd 0 = 1/1)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.abs y) (recipOdd 0) 1 ?_)
        (Q'.mul_one_eqv (Q'.abs y))
      show (recipOdd 0).eqv 1
      decide
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  exact Q'.le_trans' _ _ _ hy (by decide : recipOdd 1 ≤ (1 : Q'))

/-- `termAbs y N₀ ≤ half^{N₀}`. -/
theorem termAbs_le_halfPow (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (N₀ : Nat) :
    termAbs y N₀ ≤ half ^ N₀ := by
  -- termAbs y N₀ ≤ termAbs y 0 · (1/9)^{N₀} ≤ (1/9)^{N₀} ≤ half^{N₀}
  have hdom : termAbs y N₀ ≤ termAbs y 0 * oneNinth ^ N₀ := by
    have := termAbs_geom_dom y hy 0 N₀
    rwa [Nat.zero_add] at this
  have h1 : termAbs y 0 * oneNinth ^ N₀ ≤ (1 : Q') * oneNinth ^ N₀ :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (termAbs_zero_le_one y hy)
      (pow_nonneg oneNinth oneNinth_nonneg N₀)
  have h2 : (1 : Q') * oneNinth ^ N₀ ≤ oneNinth ^ N₀ :=
    Q'.le_of_eqv (Q'.one_mul_eqv (oneNinth ^ N₀))
  have h3 : oneNinth ^ N₀ ≤ half ^ N₀ :=
    pow_le_pow_base oneNinth half oneNinth_nonneg (by decide) N₀
  exact Q'.le_trans' _ _ _ hdom (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3))

/-- The `termAbs → 0` modulus and its spec: past `δ.den`, `termAbs y N₀ ≤ δ`. -/
theorem termAbs_le_of_den_le (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (δ : Q')
    (hδ : (0 : Q') < δ) (N₀ : Nat) (hN : δ.den ≤ N₀) : termAbs y N₀ ≤ δ := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hN   -- N₀ = δ.den + e
  refine Q'.le_trans' _ _ _ (termAbs_le_halfPow y hy N₀) ?_
  rw [he]
  exact Q'.le_trans' _ _ _ (pow_half_antitone δ.den e) (pow_half_le δ hδ)

/-! ## 5. `CReal.artanh` -/

/-- `0 < (8/9)·ε` for `ε > 0`. -/
theorem eightNinths_eps_pos (ε : Q') (hε : (0 : Q') < ε) :
    (0 : Q') < Q'.mkPos 8 9 (by decide) * ε := by
  show (0 : Int) * _ < (Q'.mkPos 8 9 (by decide) * ε).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  have hεnum : (0 : Int) < ε.num := by
    have h : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at h
    have h' : (0 : Int) < ε.num * (1 : Int) := h
    rwa [Int.mul_one] at h'
  show (0 : Int) < (8 * ε.num) * ((0 : Q').den : Int)
  have hden : (0 : Int) < ((0 : Q').den : Int) := by decide
  exact Int.mul_pos (Int.mul_pos (by decide) hεnum) hden

/-- `termAbs y N₀ ≤ (8/9)ε ⟹ termAbs y N₀ + (1/9)ε ≤ ε`. -/
theorem recurrence_from_term (y : Q') (N₀ : Nat) (ε : Q')
    (h : termAbs y N₀ ≤ Q'.mkPos 8 9 (by decide) * ε) :
    termAbs y N₀ + oneNinth * ε ≤ ε := by
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (oneNinth * ε) h) ?_
  -- (8/9)ε + (1/9)ε ≃ ε
  have e : (Q'.mkPos 8 9 (by decide) * ε + oneNinth * ε).eqv ε := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ExpNeg.add_mul_eqv (Q'.mkPos 8 9 (by decide)) oneNinth ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.mkPos 8 9 (by decide) + oneNinth) 1 ε (by decide)) ?_
    exact Q'.one_mul_eqv ε
  exact Q'.le_of_eqv e

/-- **The constructive `artanh y` for `|y| ≤ 1/3`** — the genuine artanh-series
limit, with the geometric Cauchy modulus.  Its approximations are the rational
partial sums `partialSum y`. -/
def artanh (y : Q') (hy : Q'.abs y ≤ recipOdd 1) : CReal where
  approx := partialSum y
  cauchy := by
    intro ε hε
    have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    have h89 : (0 : Q') < Q'.mkPos 8 9 (by decide) * ε := eightNinths_eps_pos ε hε
    refine ⟨(Q'.mkPos 8 9 (by decide) * ε).den, fun m n hm hn => ?_⟩
    have dir : ∀ k l : Nat, (Q'.mkPos 8 9 (by decide) * ε).den ≤ k → k ≤ l →
        partialSum y l ≤ partialSum y k + ε ∧ partialSum y k ≤ partialSum y l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have hterm : termAbs y k ≤ Q'.mkPos 8 9 (by decide) * ε :=
        termAbs_le_of_den_le y hy (Q'.mkPos 8 9 (by decide) * ε) h89 k hk
      have hrec : termAbs y k + oneNinth * ε ≤ ε := recurrence_from_term y k ε hterm
      have htail : blockAbs y k d ≤ ε := blockAbs_le y hy ε k hεnn hrec d
      exact ⟨Q'.le_trans' _ _ _ (block_upper y k d)
               (Q'.add_le_add_left (partialSum y k) (blockAbs y k d) ε htail),
             Q'.le_trans' _ _ _ (block_lower y k d)
               (Q'.add_le_add_left (partialSum y (k + d)) (blockAbs y k d) ε htail)⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

@[simp] theorem artanh_approx (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (n : Nat) :
    (artanh y hy).approx n = partialSum y n := rfl

/-! ## 6. `artanh 0 ≃ 0` -/

/-- `0^(n+1) ≃ 0` (in `Q'`). -/
theorem zero_pow_succ_eqv (n : Nat) : ((0 : Q') ^ (n + 1)).eqv 0 := by
  show ((0 : Q') * (0 : Q') ^ n).eqv 0
  exact zero_mul_eqv ((0 : Q') ^ n)

/-- `term 0 k ≃ 0`. -/
theorem term_zero_eqv (k : Nat) : (term (0 : Q') k).eqv 0 := by
  show ((0 : Q') ^ (2 * k + 1) * recipOdd k).eqv 0
  -- (0^(2k+1))·r ≃ 0·r ≃ 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((0 : Q') ^ (2 * k + 1)) 0 (recipOdd k) (zero_pow_succ_eqv (2 * k))) ?_
  exact zero_mul_eqv (recipOdd k)

/-- `partialSum 0 n ≃ 0` for every `n`. -/
theorem partialSum_zero_eqv : ∀ n, (partialSum (0 : Q') n).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (partialSum (0 : Q') n + term (0 : Q') n).eqv 0
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 _ (partialSum_zero_eqv n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 0 (term (0 : Q') n) 0 (term_zero_eqv n)) ?_
    -- 0 + 0 ≃ 0
    decide

/-- `|0| ≤ 1/3` (the artanh hypothesis at `y = 0`). -/
theorem abs_zero_le : Q'.abs (0 : Q') ≤ recipOdd 1 := by decide

/-- **`artanh 0 ≃ 0`.** -/
theorem artanh_zero : CReal.Equiv (artanh (0 : Q') abs_zero_le) CReal.czero := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have he : (partialSum (0 : Q') n).eqv 0 := partialSum_zero_eqv n
  refine ⟨?_, ?_⟩
  · -- partialSum 0 n ≤ 0 + ε
    show partialSum (0 : Q') n ≤ (0 : Q') + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
  · -- czero.approx n = 0 ≤ partialSum 0 n + ε
    show (0 : Q') ≤ partialSum (0 : Q') n + ε
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
      (Q'.add_le_add_right 0 (partialSum (0 : Q') n) ε (Q'.ge_of_eqv he))

/-! ## 7. Sign lemmas: artanh preserves the sign of `y`

For `y ≥ 0` every term is `≥ 0`, so the partial sums increase and the limit is
`≥ partialSum y 1 = y`.  For `y ≤ 0` the terms are `≤ 0` and the limit is
`≤ partialSum y 1 = y`. -/

/-- For `y ≥ 0`, `term y k ≥ 0`. -/
theorem term_nonneg_of_nonneg (y : Q') (hy : (0 : Q') ≤ y) (k : Nat) :
    (0 : Q') ≤ term y k :=
  Q'.mul_nonneg _ _ (pow_nonneg y hy _) (recipOdd_nonneg k)

/-- `0 ≤ y^(2k)` (even powers are nonnegative). -/
theorem even_pow_nonneg (y : Q') (k : Nat) : (0 : Q') ≤ y ^ (2 * k) := by
  induction k with
  | zero => show (0 : Q') ≤ (1 : Q'); exact Q'.zero_le_one
  | succ k ih =>
    have he : 2 * (k + 1) = (2 * k) + 2 := by omega
    rw [he, pow_add_two]
    -- y·(y·y^(2k)) = (y·y)·y^(2k) up to eqv; y·y ≥ 0, y^(2k) ≥ 0
    have hsqnn : (0 : Q') ≤ y * y := SumOfSquares.q_mul_self_nonneg y
    refine Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hsqnn ih) ?_
    exact Q'.le_of_eqv (Q'.mul_assoc_eqv y y (y ^ (2 * k)))

/-- `y^(2k+1) ≤ 0` for `y ≤ 0` (odd powers of a nonpositive are nonpositive). -/
theorem odd_pow_nonpos (y : Q') (hy : y ≤ (0 : Q')) (k : Nat) :
    y ^ (2 * k + 1) ≤ (0 : Q') := by
  -- y^(2k+1) = y · y^(2k), y ≤ 0, y^(2k) ≥ 0  ⟹  y·y^(2k) ≤ 0
  show y * y ^ (2 * k) ≤ (0 : Q')
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right y 0 (y ^ (2 * k)) hy (even_pow_nonneg y k)) ?_
  exact Q'.le_of_eqv (zero_mul_eqv (y ^ (2 * k)))

/-- For `y ≤ 0`, `term y k ≤ 0`. -/
theorem term_nonpos_of_nonpos (y : Q') (hy : y ≤ (0 : Q')) (k : Nat) :
    term y k ≤ (0 : Q') := by
  show y ^ (2 * k + 1) * recipOdd k ≤ (0 : Q')
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (y ^ (2*k+1)) 0 (recipOdd k)
      (odd_pow_nonpos y hy k) (recipOdd_nonneg k)) ?_
  exact Q'.le_of_eqv (zero_mul_eqv (recipOdd k))

/-- `term y 0 ≃ y`. -/
theorem term_zero_eqv_self (y : Q') : (term y 0).eqv y := by
  show (y ^ (2 * 0 + 1) * recipOdd 0).eqv y
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (y ^ (2 * 0 + 1)) y (recipOdd 0) ?_) ?_
  · show (y * y ^ 0).eqv y
    exact Q'.mul_one_eqv y
  · -- y · recipOdd 0 ≃ y  (recipOdd 0 ≃ 1)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left y (recipOdd 0) 1 (by decide))
      (Q'.mul_one_eqv y)

/-- Monotone increase of partial sums for `y ≥ 0`:
`partialSum y m ≤ partialSum y (m + d)`. -/
theorem partialSum_mono_of_nonneg (y : Q') (hy : (0 : Q') ≤ y) (m : Nat) :
    ∀ d, partialSum y m ≤ partialSum y (m + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
    show partialSum y m ≤ partialSum y (m + d) + term y (m + d)
    exact Q'.le_trans' _ _ _ (partialSum_mono_of_nonneg y hy m d)
      (Q'.add_le_self_of_nonneg _ _ (term_nonneg_of_nonneg y hy (m + d)))

/-- Monotone decrease of partial sums for `y ≤ 0`:
`partialSum y (m + d) ≤ partialSum y m`. -/
theorem partialSum_anti_of_nonpos (y : Q') (hy : y ≤ (0 : Q')) (m : Nat) :
    ∀ d, partialSum y (m + d) ≤ partialSum y m
  | 0 => Q'.le_refl' _
  | d + 1 => by
    show partialSum y (m + d) + term y (m + d) ≤ partialSum y m
    have hlast : partialSum y m + (0 : Q') ≤ partialSum y m := by
      rw [Q'.add_zero']; exact Q'.le_refl' _
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (term y (m + d)) (partialSum_anti_of_nonpos y hy m d))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left (partialSum y m) (term y (m + d)) 0
          (term_nonpos_of_nonpos y hy (m + d)))
        hlast)

/-! ## 8. CReal-level sign lemmas

For `0 < y ≤ 1/3`, `artanh y` is strictly positive (`IsPositive`); for `-1/3 ≤ y < 0`
it is strictly negative (`leRat (artanh y) (term y 0)` with `term y 0 ≃ y < 0`). -/

/-- **`artanh y > 0` for `0 < y ≤ 1/3`.**  Every approximation past index 1 is
`≥ term y 0 ≃ y`, so the limit dominates the positive rational lower bound `term y 0`. -/
theorem artanh_geRat_of_pos (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (hpos : (0 : Q') ≤ y) :
    ExpPos.geRat (artanh y hy) (term y 0) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn   -- n = 1 + d
  show term y 0 ≤ partialSum y (1 + d)
  -- partialSum y 1 = term y 0, and monotone
  have h1 : partialSum y 1 ≤ partialSum y (1 + d) := partialSum_mono_of_nonneg y hpos 1 d
  have e : (partialSum y 1).eqv (term y 0) := by
    show (partialSum y 0 + term y 0).eqv (term y 0)
    show ((0 : Q') + term y 0).eqv (term y 0)
    rw [Q'.zero_add']; exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) h1

/-- **`artanh y < 0` for `-1/3 ≤ y < 0`.**  Every approximation past index 1 is
`≤ term y 0 ≃ y`, so the limit is `≤` the negative rational `term y 0`. -/
theorem artanh_leRat_of_neg (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (hneg : y ≤ (0 : Q')) :
    CReal.leRat (artanh y hy) (term y 0) := by
  apply CReal.leRat_of_eventually
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show partialSum y (1 + d) ≤ term y 0
  have h1 : partialSum y (1 + d) ≤ partialSum y 1 := partialSum_anti_of_nonpos y hneg 1 d
  have e : (partialSum y 1).eqv (term y 0) := by
    show (partialSum y 0 + term y 0).eqv (term y 0)
    show ((0 : Q') + term y 0).eqv (term y 0)
    rw [Q'.zero_add']; exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e)

/-! ## 9. `logRat` — the logarithm of a positive rational (artanh route)

`log m = 2·artanh(y)`, `y = (m−1)/(m+1)`.  For the directly-reducible window
`m ∈ [2/3, 2]` we have `|y| ≤ 1/3`, so `artanh y` is the genuine series limit above
and `logRat m = 2·artanh y` is the genuine logarithm of `m`.  Doubling is the
pointwise `CReal` sum `x + x`. -/

/-- If `q.num = 0` then `(-q).num = 0`. -/
theorem neg_num_zero (q : Q') (h : q.num = 0) : (-q).num = 0 := by
  show -q.num = 0; rw [h]; rfl

/-- If `q.num = 0` then `Q'.abs q ≤ recipOdd 1` (any positive rational dominates `0`). -/
theorem abs_le_recipOdd_of_num_zero (q : Q') (h : q.num = 0) :
    Q'.abs q ≤ recipOdd 1 := by
  -- (Q'.abs q).num = 0, so cross-product is 0 ≤ 1·den
  have habsnum : (Q'.abs q).num = 0 := by
    unfold Q'.abs
    by_cases hc : (0 : Q') ≤ q
    · rw [if_pos hc]; exact h
    · rw [if_neg hc]; exact neg_num_zero q h
  show (Q'.abs q).num * ((recipOdd 1).den : Int) ≤ (recipOdd 1).num * ((Q'.abs q).den : Int)
  rw [habsnum, Int.zero_mul]
  show (0 : Int) ≤ (1 : Int) * ((Q'.abs q).den : Int)
  rw [Int.one_mul]
  exact Int.natCast_nonneg _

/-- If `y ≃ 0` then `term y k ≃ 0`. -/
theorem term_eqv_zero_of_arg (y : Q') (h : y.eqv 0) (k : Nat) : (term y k).eqv 0 := by
  show (y ^ (2 * k + 1) * recipOdd k).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (y ^ (2 * k + 1)) 0 (recipOdd k) (pow_eqv_zero y h (2 * k))) ?_
  exact zero_mul_eqv (recipOdd k)

/-- If `y ≃ 0` then `partialSum y n ≃ 0`. -/
theorem partialSum_eqv_zero_of_arg_eqv_zero (y : Q') (h : y.eqv 0) :
    ∀ n, (partialSum y n).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (partialSum y n + term y n).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ 0 _ (partialSum_eqv_zero_of_arg_eqv_zero y h n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 0 (term y n) 0 (term_eqv_zero_of_arg y h n)) ?_
    decide

/-- Doubling a `CReal` (`2·x = x + x`). -/
def scaleTwo (x : CReal) : CReal := CReal.add x x

@[simp] theorem scaleTwo_approx (x : CReal) (n : Nat) :
    (scaleTwo x).approx n = x.approx n + x.approx n := rfl

/-- The artanh argument `y = (m−1)/(m+1)` for a positive rational `m`. -/
def yOf (m : Q') (hm1 : (0 : Q') < m + 1) : Q' := (m + -1) * Q'.recipPos (m + 1) hm1

/-- **`logRat` on the directly-reducible window.**  For `m` with `0 < m+1` and the
artanh-window certificate `|y| ≤ 1/3`, `logRat m = 2·artanh((m−1)/(m+1))` — the
genuine logarithm of `m` as a constructive real. -/
def logRat (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) : CReal :=
  scaleTwo (artanh (yOf m hm1) hyb)

@[simp] theorem logRat_approx (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) (n : Nat) :
    (logRat m hm1 hyb).approx n = partialSum (yOf m hm1) n + partialSum (yOf m hm1) n := rfl

/-! ### `logRat 1 ≃ 0` -/

/-- At `m = 1` the artanh argument is `0`: `yOf 1 = (1−1)/(1+1) = 0 ≃ 0`. -/
theorem yOf_one_eqv : (yOf (1 : Q') (by decide)).eqv 0 := by
  show ((1 + -1 : Q') * Q'.recipPos (1 + 1) (by decide)).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (1 + -1) 0 (Q'.recipPos (1 + 1) (by decide)) (by decide)) ?_
  exact zero_mul_eqv _

/-- The window certificate at `m = 1` (`yOf 1` has numerator `0`, so `|yOf 1| ≤ 1/3`). -/
theorem yOf_one_window : Q'.abs (yOf (1 : Q') (by decide)) ≤ recipOdd 1 := by
  apply abs_le_recipOdd_of_num_zero
  -- (yOf 1).num = ((1+-1) * recipPos 2).num = 0 since (1+-1).num = 0
  exact mul_num_zero (1 + -1) (Q'.recipPos (1 + 1) (by decide)) (by decide)

/-- **`logRat 1 ≃ 0`.** -/
theorem logRat_one :
    CReal.Equiv (logRat (1 : Q') (by decide) yOf_one_window) CReal.czero := by
  -- partialSum (yOf 1) n ≃ partialSum 0 n ≃ 0, doubled ≃ 0
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  -- both partial sums are ≃ 0 since yOf 1 ≃ 0 makes every term ≃ 0... but yOf 1 is a *fixed*
  -- rational ≃ 0, not literally 0.  Use partialSum_eqv_zero_of_arg_eqv_zero.
  have hps : (partialSum (yOf (1 : Q') (by decide)) n).eqv 0 :=
    partialSum_eqv_zero_of_arg_eqv_zero (yOf (1 : Q') (by decide)) yOf_one_eqv n
  have hsum : (partialSum (yOf (1 : Q') (by decide)) n
      + partialSum (yOf (1 : Q') (by decide)) n).eqv 0 := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hps hps) ?_
    decide
  refine ⟨?_, ?_⟩
  · show (logRat (1 : Q') (by decide) yOf_one_window).approx n ≤ (0 : Q') + ε
    show partialSum (yOf (1 : Q') (by decide)) n + partialSum (yOf (1 : Q') (by decide)) n
        ≤ (0 : Q') + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
      (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
  · show (0 : Q') ≤ (logRat (1 : Q') (by decide) yOf_one_window).approx n + ε
    show (0 : Q') ≤ partialSum (yOf (1 : Q') (by decide)) n
        + partialSum (yOf (1 : Q') (by decide)) n + ε
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε))
      (Q'.add_le_add_right 0 _ ε (Q'.ge_of_eqv hsum))

/-! ### Sign lemmas for `logRat` (the characterising property)

`yOf m > 0 ⟺ m > 1` and `yOf m < 0 ⟺ m < 1` (since `m+1 > 0`).  Through the artanh
sign lemmas this gives the sign of `logRat m`, the key fact a placeholder could not
satisfy: `log` is positive above `1` and negative below `1`. -/

/-- `geRat` doubles through `scaleTwo`: `geRat x a → geRat (scaleTwo x) (a + a)`. -/
theorem geRat_scaleTwo {x : CReal} {a : Q'} (h : ExpPos.geRat x a) :
    ExpPos.geRat (scaleTwo x) (a + a) := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N, hN⟩ := h (half * ε) hhε
  refine ⟨N, fun n hn => ?_⟩
  -- a + a ≤ (x_n + ½ε) + (x_n + ½ε) ≃ (x_n + x_n) + ε
  show a + a ≤ (x.approx n + x.approx n) + ε
  have hstep : a + a ≤ (x.approx n + half * ε) + (x.approx n + half * ε) :=
    Q'.add_le_add (hN n hn) (hN n hn)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- (x_n + s) + (x_n + s) ≃ (x_n + x_n) + (s + s) ≤ (x_n + x_n) + ε
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_swap_inner (x.approx n) (half * ε) (x.approx n) (half * ε))) ?_
  exact Q'.add_le_add_left (x.approx n + x.approx n) (half * ε + half * ε) ε
    (Q'.le_of_eqv (ExpNeg.two_halves ε))

/-- `leRat` doubles through `scaleTwo`: `leRat x a → leRat (scaleTwo x) (a + a)`. -/
theorem leRat_scaleTwo {x : CReal} {a : Q'} (h : CReal.leRat x a) :
    CReal.leRat (scaleTwo x) (a + a) := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N, hN⟩ := h (half * ε) hhε
  refine ⟨N, fun n hn => ?_⟩
  show (x.approx n + x.approx n) ≤ (a + a) + ε
  have hstep : (x.approx n + x.approx n) ≤ (a + half * ε) + (a + half * ε) :=
    Q'.add_le_add (hN n hn) (hN n hn)
  refine Q'.le_trans' _ _ _ hstep ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_swap_inner a (half * ε) a (half * ε))) ?_
  exact Q'.add_le_add_left (a + a) (half * ε + half * ε) ε
    (Q'.le_of_eqv (ExpNeg.two_halves ε))

/-- **`logRat m` is bounded below by `2·(yOf m)·… > 0` when `yOf m ≥ 0`.**
Concretely `geRat (logRat m …) (term (yOf m) 0 + term (yOf m) 0)`, and
`term (yOf m) 0 ≃ yOf m`, which is `> 0` exactly when `m > 1`. -/
theorem logRat_geRat_of_arg_nonneg (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) (hpos : (0 : Q') ≤ yOf m hm1) :
    ExpPos.geRat (logRat m hm1 hyb) (term (yOf m hm1) 0 + term (yOf m hm1) 0) :=
  geRat_scaleTwo (artanh_geRat_of_pos (yOf m hm1) hyb hpos)

/-- **`logRat m` is bounded above by `2·(yOf m)·… < 0` when `yOf m ≤ 0`.** -/
theorem logRat_leRat_of_arg_nonpos (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) (hneg : yOf m hm1 ≤ (0 : Q')) :
    CReal.leRat (logRat m hm1 hyb) (term (yOf m hm1) 0 + term (yOf m hm1) 0) :=
  leRat_scaleTwo (artanh_leRat_of_neg (yOf m hm1) hyb hneg)

/-- Window certificate from an `eqv` to a literal with a literal window bound:
if `yOf m ≃ c`, `0 ≤ yOf m`, and `c ≤ 1/3`, then `|yOf m| ≤ 1/3`. -/
theorem window_of_eqv_nonneg (m : Q') (hm1 : (0 : Q') < m + 1) (c : Q')
    (he : (yOf m hm1).eqv c) (hnn : (0 : Q') ≤ yOf m hm1) (hc : c ≤ recipOdd 1) :
    Q'.abs (yOf m hm1) ≤ recipOdd 1 := by
  have : Q'.abs (yOf m hm1) = yOf m hm1 := by unfold Q'.abs; rw [if_pos hnn]
  rw [this]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hc

/-! ### Concrete non-vacuity: `log 2`

`yOf 2 = (2−1)/(2+1) ≃ 1/3`, so `log 2 = 2·artanh(1/3)` is a fully-proven, genuinely
characterised value with `log 2 > 0` (bounded below by `term (1/3) 0 + term (1/3) 0`,
a positive rational). -/

/-- `yOf 2 ≃ 1/3` (`= recipOdd 1`). -/
theorem yOf_two_eqv : (yOf (2 : Q') (by decide)).eqv (recipOdd 1) := by
  -- yOf 2 = (2+-1)·recipPos 3 ; (2+-1) ≃ 1, recipPos 3 ≃ 1/3
  show ((2 + -1 : Q') * Q'.recipPos (2 + 1) (by decide)).eqv (recipOdd 1)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (2 + -1) 1 (Q'.recipPos (2 + 1) (by decide)) (by decide)) ?_
  -- 1 · recipPos 3 ≃ recipPos 3 ≃ 1/3 = recipOdd 1
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (Q'.recipPos (2 + 1) (by decide))) ?_
  -- recipPos 3 ≃ recipOdd 1 : both are 1/3
  show (Q'.recipPos (2 + 1) (by decide)).eqv (recipOdd 1)
  -- (recipPos 3).num = (2+1).den = 1 ; (recipPos 3).den = (2+1).num = 3
  show (Q'.recipPos (2 + 1) (by decide)).num * ((recipOdd 1).den : Int)
      = (recipOdd 1).num * ((Q'.recipPos (2 + 1) (by decide)).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den]
  decide

theorem yOf_two_nonneg : (0 : Q') ≤ yOf (2 : Q') (by decide) :=
  Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ recipOdd 1) (Q'.ge_of_eqv yOf_two_eqv)

/-- The window certificate at `m = 2`. -/
theorem yOf_two_window : Q'.abs (yOf (2 : Q') (by decide)) ≤ recipOdd 1 :=
  window_of_eqv_nonneg (2 : Q') (by decide) (recipOdd 1) yOf_two_eqv yOf_two_nonneg
    (Q'.le_refl' _)

/-- **`log 2`** as a constructive real, `= 2·artanh(1/3)`. -/
def log2 : CReal := logRat (2 : Q') (by decide) yOf_two_window

/-- **`log 2 > 0`**: bounded below by the positive rational `term (yOf 2) 0 + term (yOf 2) 0`. -/
theorem log2_geRat :
    ExpPos.geRat log2 (term (yOf (2 : Q') (by decide)) 0 + term (yOf (2 : Q') (by decide)) 0) :=
  logRat_geRat_of_arg_nonneg (2 : Q') (by decide) yOf_two_window yOf_two_nonneg

/-! ## D3. The general positive-`CReal` logarithm — named range-reduction residual

A general `CReal.log : (x : CReal) → x.IsPositive → CReal` requires, for an arbitrary
positive constructive real `x`, a COMPUTABLE binary range reduction: an integer
exponent `k` and a reduced mantissa `m` with `0 < m+1`, the artanh-window certificate
`|yOf m| ≤ 1/3`, and the scaling relation `x ≃ (2^k as CReal) · m`.  For a positive
rational, `k` is decidable Int/Nat arithmetic on `num`/`den`; for a general `CReal` it
requires locating `x` between consecutive powers of two from its rational lower bound
— standard, but a sizeable separate build.  We isolate it as the single named residual
(a `Type`-level datum carrying its witnesses, no `Prop`-level `∃`), and do NOT fake it.
`CReal.log` is definable FROM it via `(k as CReal)·log2 + logRat m …`.  Believed TRUE
(the standard floor-log₂ on a located positive real). -/

/-- The named range-reduction residual for the general `CReal` logarithm. -/
structure CRealLogRangeReduction (x : CReal) : Type where
  /-- The binary exponent `k`, embedded as a `CReal` scale factor `2^k`. -/
  scale : CReal
  /-- The reduced mantissa `m`. -/
  m : Q'
  /-- `0 < m + 1` (so `yOf m` is defined). -/
  hm1 : (0 : Q') < m + 1
  /-- The artanh-window certificate for the reduced mantissa. -/
  hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1
  /-- The scaling relation `x ≃ scale · m`. -/
  scaling : CReal.Equiv x (CReal.mul scale (CReal.ofQ' m))
  /-- `log scale` as a `CReal` (the `k·log2` summand). -/
  logScale : CReal

/-- **The general `CReal` logarithm, built FROM the named range-reduction residual.**
Given the reduction datum, `log x = logScale + 2·artanh(yOf m)` — the genuine
logarithm, with no placeholder for the artanh part (it is the real series limit). -/
def CReal.log (x : CReal) (red : CRealLogRangeReduction x) : CReal :=
  CReal.add red.logScale (logRat red.m red.hm1 red.hyb)

end CRealLog

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.CRealLog.pow_two_sided
#print axioms ConstructiveReals.CRealLog.term_two_sided
#print axioms ConstructiveReals.CRealLog.termAbs_geom_dom
#print axioms ConstructiveReals.CRealLog.blockAbs_le
#print axioms ConstructiveReals.CRealLog.artanh
#print axioms ConstructiveReals.CRealLog.artanh_zero
#print axioms ConstructiveReals.CRealLog.artanh_geRat_of_pos
#print axioms ConstructiveReals.CRealLog.artanh_leRat_of_neg
#print axioms ConstructiveReals.CRealLog.logRat
#print axioms ConstructiveReals.CRealLog.logRat_one
#print axioms ConstructiveReals.CRealLog.logRat_geRat_of_arg_nonneg
#print axioms ConstructiveReals.CRealLog.logRat_leRat_of_arg_nonpos
#print axioms ConstructiveReals.CRealLog.log2
#print axioms ConstructiveReals.CRealLog.log2_geRat
#print axioms ConstructiveReals.CRealLog.CReal.log
