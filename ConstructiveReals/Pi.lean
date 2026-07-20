/-
Constructive `π` as a Bishop regular Cauchy real (`CReal`), Mathlib-free.

# What is PROVED here

  * `arctanRecip k hk H …` — for `k ≥ 2` and a closed rational `H`
    closing the geometric recurrence `1/k + (1/k^4)·H ≤ H`, the
    constructive real `arctan (1/k)` built as the MONOTONE series of
    POSITIVE paired terms `c_j = b_{2j} − b_{2j+1}`,
    `b_m = 1/((2m+1)·k^{2m+1})`.  Each `c_j ≥ 0` (partial sums increase),
    and `c_j ≤ (1/k)·(1/k^4)^j` is a clean geometric majorant.  The Cauchy
    modulus is GENUINE and EXPLICIT: monotonicity gives one direction; the
    block bound `Σ_{p≤j<q} c_j ≤ r^p·H` (`r = 1/k^4`) gives the other, and
    `r^p·H → 0` with explicit modulus via `HalfPow.pow_half_le`
    (since `r ≤ 1/2`).

  * `pi : CReal` — Machin combination `π = 16·arctanRecip 5 − 4·arctanRecip 239`,
    assembled with `CReal.mul`/`CReal.sub`/rational scaling.

  * `pi_geRat_three : ExpPos.geRat pi 3`  and  `pi_leRat_four : CReal.leRat pi 4`
    — the two-sided rational bounds `3 ≤ π ≤ 4` (the repo's regularity-free
    eventual-order bounds).

  * `pi_pos : CReal.IsPositive pi`  via the one-slack order with witness
    `ε = 1/2`, discharged from `3 ≤ pi.approx n` for `n ≥ 1` plus the `n = 0`
    base where `invSucc 0 = 1`.

  * `halfPi_pos : CReal.IsPositive halfPi`  (`halfPi = (1/2)·π`).

  * `twoOverPi : CReal` with `twoOverPi_pos` AND the reciprocal law
    `twoOverPi_mul_pi : CReal.Equiv (twoOverPi · pi) (ofQ' 2)`.  The exact
    cancellation is `twoOverPiSeq n · pi.approx (n+1) ≃ 2` (reciprocal at the
    shifted index); the residual error at index `n` is the index shift
    `pi.approx n` vs `pi.approx (n+1)`, driven to `0` by `pi.cauchy`.

# NAMED-open / honest weakenings

  * (none load-bearing).  The tighter `3.14 < π < 3.15` bracket is not pursued
    (the genuine `3 ≤ π ≤ 4` bounds suffice for all consumers); `pi.approx`
    does bracket `3.14…` numerically.

# Axiom gate

Every load-bearing declaration reports `[propext]` (and `Quot.sound` only via
reused `Nat`/`Int` helpers).  No `Classical.*`, no `native_decide`, no
`sorry`, no new axiom.  Moduli are structurally present (regular Cauchy).
-/

import ConstructiveReals.CRealComplete
import ConstructiveReals.CRealMul
import ConstructiveReals.CRealAdd
import ConstructiveReals.Geometric
import ConstructiveReals.AbsQ
import ConstructiveReals.GeometricTail
import ConstructiveReals.HalfPow
import ConstructiveReals.ExpPos
import ConstructiveReals.CRealLe

namespace ConstructiveReals.Pi

open ConstructiveReals
open ConstructiveReals.RationalTail

/-! ## 0. Nat power helpers (core `Nat` only) -/

theorem nat_pow_pos {k : Nat} (hk : 0 < k) (m : Nat) : 0 < k ^ m := Nat.pow_pos hk

theorem nat_pow_le_pow {k : Nat} (hk : 1 ≤ k) {a b : Nat} (h : a ≤ b) :
    k ^ a ≤ k ^ b := Nat.pow_le_pow_right hk h

/-! ## 1. Rational magnitude terms `b_m = 1/((2m+1)·k^{2m+1})` -/

/-- Denominator of the `m`-th magnitude term. -/
def magDen (k m : Nat) : Nat := (2 * m + 1) * k ^ (2 * m + 1)

theorem magDen_pos {k : Nat} (hk : 0 < k) (m : Nat) : 0 < magDen k m :=
  Nat.mul_pos (Nat.succ_pos _) (nat_pow_pos hk (2 * m + 1))

/-- `b_m = 1/((2m+1)·k^{2m+1})`. -/
def bMag (k : Nat) (hk : 0 < k) (m : Nat) : Q' := Q'.mkPos 1 (magDen k m) (magDen_pos hk m)

theorem bMag_num {k : Nat} (hk : 0 < k) (m : Nat) : (bMag k hk m).num = 1 :=
  Q'.mkPos_num 1 (magDen k m) (magDen_pos hk m)

theorem bMag_den {k : Nat} (hk : 0 < k) (m : Nat) : (bMag k hk m).den = magDen k m :=
  Q'.mkPos_den 1 (magDen k m) (magDen_pos hk m)

theorem bMag_nonneg {k : Nat} (hk : 0 < k) (m : Nat) : (0 : Q') ≤ bMag k hk m := by
  rw [Q'.zero_le_iff_num_nonneg, bMag_num]; decide

/-- `b` is decreasing: `b_{m+1} ≤ b_m`. -/
theorem bMag_antitone {k : Nat} (hk : 0 < k) (m : Nat) :
    bMag k hk (m + 1) ≤ bMag k hk m := by
  show (bMag k hk (m + 1)).num * ((bMag k hk m).den : Int)
      ≤ (bMag k hk m).num * ((bMag k hk (m + 1)).den : Int)
  rw [bMag_num, bMag_num, bMag_den, bMag_den, Int.one_mul, Int.one_mul]
  have hk1 : 1 ≤ k := hk
  have hle : magDen k m ≤ magDen k (m + 1) := by
    unfold magDen
    have h1 : 2 * m + 1 ≤ 2 * (m + 1) + 1 := by
      have : 2 * m ≤ 2 * (m + 1) := Nat.mul_le_mul_left 2 (Nat.le_succ m)
      exact Nat.add_le_add_right this 1
    have h2 : k ^ (2 * m + 1) ≤ k ^ (2 * (m + 1) + 1) := nat_pow_le_pow hk1 h1
    exact Nat.mul_le_mul h1 h2
  exact_mod_cast hle

/-! ## 2. The paired series term `c_j = b_{2j} − b_{2j+1}` -/

/-- `c_j = b_{2j} − b_{2j+1}`, the `j`-th paired term of `arctan(1/k)`. -/
def cTerm (k : Nat) (hk : 0 < k) (j : Nat) : Q' :=
  bMag k hk (2 * j) - bMag k hk (2 * j + 1)

/-- Each paired term is nonnegative. -/
theorem cTerm_nonneg {k : Nat} (hk : 0 < k) (j : Nat) :
    (0 : Q') ≤ cTerm k hk j := by
  show (0 : Q') ≤ bMag k hk (2 * j) + (- bMag k hk (2 * j + 1))
  have hba : bMag k hk (2 * j + 1) ≤ bMag k hk (2 * j) := bMag_antitone hk (2 * j)
  have h1 : - bMag k hk (2 * j + 1) + bMag k hk (2 * j + 1)
      ≤ - bMag k hk (2 * j + 1) + bMag k hk (2 * j) :=
    Q'.add_le_add_left _ _ _ hba
  have h2 : (0 : Q') ≤ - bMag k hk (2 * j + 1) + bMag k hk (2 * j) := by
    refine Q'.le_trans' _ _ _ ?_ h1
    exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (bMag k hk (2 * j + 1)))
  exact Q'.le_trans' _ _ _ h2
    (Q'.le_of_eqv (Q'.add_comm_eqv (- bMag k hk (2 * j + 1)) (bMag k hk (2 * j))))

/-- `c_j ≤ b_{2j}` (drop the subtracted nonneg term). -/
theorem cTerm_le_bMag {k : Nat} (hk : 0 < k) (j : Nat) :
    cTerm k hk j ≤ bMag k hk (2 * j) := by
  show bMag k hk (2 * j) + (- bMag k hk (2 * j + 1)) ≤ bMag k hk (2 * j)
  have hnb : (- bMag k hk (2 * j + 1)) ≤ 0 := by
    have h1 := Q'.neg_le_neg (bMag_nonneg hk (2 * j + 1))
    have h2 : ((-(0 : Q'))).eqv 0 := by decide
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)
  have hstep : bMag k hk (2 * j) + (- bMag k hk (2 * j + 1)) ≤ bMag k hk (2 * j) + 0 :=
    Q'.add_le_add_left _ _ _ hnb
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))

/-! ## 3. The geometric majorant `geoTerm k j = (1/k)·(1/k^4)^j` -/

/-- `η_max = 1/k`. -/
def etaMax (k : Nat) (hk : 0 < k) : Q' := Q'.mkPos 1 k hk

/-- `r = 1/k^4`. -/
def ratio (k : Nat) (hk : 0 < k) : Q' := Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk 4)

/-- `geoTerm k j = η_max · r^j`. -/
def geoTerm (k : Nat) (hk : 0 < k) (j : Nat) : Q' := etaMax k hk * (ratio k hk) ^ j

theorem etaMax_nonneg {k : Nat} (hk : 0 < k) : (0 : Q') ≤ etaMax k hk := by
  show (0 : Q') ≤ Q'.mkPos 1 k hk
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide

theorem ratio_nonneg {k : Nat} (hk : 0 < k) : (0 : Q') ≤ ratio k hk := by
  show (0 : Q') ≤ Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk 4)
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide

theorem geoTerm_nonneg {k : Nat} (hk : 0 < k) (j : Nat) : (0 : Q') ≤ geoTerm k hk j :=
  Q'.mul_nonneg _ _ (etaMax_nonneg hk) (Q'.pow_nonneg _ (ratio_nonneg hk) j)

/-- `(mkPos 1 d)^j` equals `mkPos 1 (d^j)` up to `eqv`. -/
theorem mkPosOne_pow_eqv (d : Nat) (hd : 0 < d) (j : Nat) :
    ((Q'.mkPos 1 d hd) ^ j).eqv (Q'.mkPos 1 (d ^ j) (nat_pow_pos hd j)) := by
  induction j with
  | zero =>
    show ((1 : Q')).eqv (Q'.mkPos 1 (d ^ 0) (nat_pow_pos hd 0))
    show (1 : Int) * ((Q'.mkPos 1 (d ^ 0) (nat_pow_pos hd 0)).den : Int)
        = (Q'.mkPos 1 (d ^ 0) (nat_pow_pos hd 0)).num * ((1 : Q').den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    show (1 : Int) * ((d ^ 0 : Nat) : Int) = (1 : Int) * ((1 : Q').den : Int)
    rw [Nat.pow_zero]
    decide
  | succ n ih =>
    show ((Q'.mkPos 1 d hd) * (Q'.mkPos 1 d hd) ^ n).eqv
        (Q'.mkPos 1 (d ^ (n + 1)) (nat_pow_pos hd (n + 1)))
    have step1 : ((Q'.mkPos 1 d hd) * (Q'.mkPos 1 d hd) ^ n).eqv
        ((Q'.mkPos 1 d hd) * (Q'.mkPos 1 (d ^ n) (nat_pow_pos hd n))) :=
      Q'.mul_eqv_congr_left _ _ _ ih
    have step2 : ((Q'.mkPos 1 d hd) * (Q'.mkPos 1 (d ^ n) (nat_pow_pos hd n))).eqv
        (Q'.mkPos 1 (d ^ (n + 1)) (nat_pow_pos hd (n + 1))) := by
      show ((Q'.mkPos 1 d hd) * (Q'.mkPos 1 (d ^ n) (nat_pow_pos hd n))).num
            * ((Q'.mkPos 1 (d ^ (n + 1)) (nat_pow_pos hd (n + 1))).den : Int)
          = (Q'.mkPos 1 (d ^ (n + 1)) (nat_pow_pos hd (n + 1))).num
            * (((Q'.mkPos 1 d hd) * (Q'.mkPos 1 (d ^ n) (nat_pow_pos hd n))).den : Int)
      rw [Q'.mkPos_num, Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
      show ((1 : Int) * 1) * ((d ^ (n + 1) : Nat) : Int)
          = (1 : Int) * ((d : Int) * ((d ^ n : Nat) : Int))
      rw [Int.one_mul, Int.one_mul, Int.one_mul]
      have hpow : d ^ (n + 1) = d * d ^ n := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [hpow]; exact_mod_cast rfl
    exact Q'.eqv_trans _ _ _ step1 step2

/-- `geoTerm k j ≃ mkPos 1 (k · (k^4)^j)`. -/
theorem geoTerm_eqv_mkPos {k : Nat} (hk : 0 < k) (j : Nat) :
    (geoTerm k hk j).eqv
      (Q'.mkPos 1 (k * (k ^ 4) ^ j) (Nat.mul_pos hk (nat_pow_pos (nat_pow_pos hk 4) j))) := by
  show (etaMax k hk * (ratio k hk) ^ j).eqv _
  have hr := mkPosOne_pow_eqv (k ^ 4) (nat_pow_pos hk 4) j
  have e1 : (etaMax k hk * (ratio k hk) ^ j).eqv
      (etaMax k hk * Q'.mkPos 1 ((k ^ 4) ^ j) (nat_pow_pos (nat_pow_pos hk 4) j)) :=
    Q'.mul_eqv_congr_left _ _ _ hr
  refine Q'.eqv_trans _ _ _ e1 ?_
  show ((Q'.mkPos 1 k hk) * Q'.mkPos 1 ((k ^ 4) ^ j) (nat_pow_pos (nat_pow_pos hk 4) j)).eqv
      (Q'.mkPos 1 (k * (k ^ 4) ^ j) _)
  show (((Q'.mkPos 1 k hk) * Q'.mkPos 1 ((k ^ 4) ^ j) _).num)
        * ((Q'.mkPos 1 (k * (k ^ 4) ^ j) _).den : Int)
      = (Q'.mkPos 1 (k * (k ^ 4) ^ j) _).num
        * (((Q'.mkPos 1 k hk) * Q'.mkPos 1 ((k ^ 4) ^ j) _).den : Int)
  rw [Q'.mkPos_num, Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_den]
  show ((1 : Int) * 1) * ((k * (k ^ 4) ^ j : Nat) : Int)
      = (1 : Int) * ((k : Int) * (((k ^ 4) ^ j : Nat) : Int))
  rw [Int.one_mul, Int.one_mul, Int.one_mul]; exact_mod_cast rfl

/-- **Termwise majorant.** `c_j ≤ geoTerm k j` for `k ≥ 2`.
Reduces to `k·(k^4)^j ≤ (4j+1)·k^{4j+1}` in `Nat`. -/
theorem cTerm_le_geoTerm {k : Nat} (hk : 0 < k) (j : Nat) :
    cTerm k hk j ≤ geoTerm k hk j := by
  refine Q'.le_trans' _ _ _ (cTerm_le_bMag hk j) ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (geoTerm_eqv_mkPos hk j))
  show (bMag k hk (2 * j)).num * ((Q'.mkPos 1 (k * (k ^ 4) ^ j) _).den : Int)
      ≤ (Q'.mkPos 1 (k * (k ^ 4) ^ j) _).num * ((bMag k hk (2 * j)).den : Int)
  rw [bMag_num, bMag_den, Q'.mkPos_num, Q'.mkPos_den, Int.one_mul, Int.one_mul]
  have key : k * (k ^ 4) ^ j ≤ magDen k (2 * j) := by
    unfold magDen
    have e1 : (k ^ 4) ^ j = k ^ (4 * j) := by rw [← Nat.pow_mul]
    have e2 : k * (k ^ 4) ^ j = k ^ (4 * j + 1) := by
      rw [e1, Nat.pow_succ, Nat.mul_comm]
    rw [e2]
    have hexp : 2 * (2 * j) + 1 = 4 * j + 1 := by rw [← Nat.mul_assoc]
    rw [hexp]
    calc k ^ (4 * j + 1)
        = 1 * k ^ (4 * j + 1) := (Nat.one_mul _).symm
      _ ≤ (4 * j + 1) * k ^ (4 * j + 1) :=
          Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le _))
  exact_mod_cast key

/-! ## 4. Partial sums, monotonicity, and the geometric block bound -/

/-- The `n`-th partial sum `S_n = Σ_{j<n} c_j`. -/
def cPart (k : Nat) (hk : 0 < k) (n : Nat) : Q' := finSum (cTerm k hk) n

theorem cPart_succ (k : Nat) (hk : 0 < k) (n : Nat) :
    cPart k hk (n + 1) = cPart k hk n + cTerm k hk n := by
  show finSum (cTerm k hk) (n + 1) = finSum (cTerm k hk) n + cTerm k hk n
  rw [finSum_succ]

/-- Partial sums are monotone (each term nonneg). -/
theorem cPart_mono (k : Nat) (hk : 0 < k) {p q : Nat} (h : p ≤ q) :
    cPart k hk p ≤ cPart k hk q :=
  finSum_monotone_of_nonneg (cTerm k hk) (fun j => cTerm_nonneg hk j) p q h

/-- The shifted geometric block sum `Σ_{j<d} geoTerm k (p+j)`. -/
def geoBlock (k : Nat) (hk : 0 < k) (p : Nat) (d : Nat) : Q' :=
  finSum (fun j => geoTerm k hk (p + j)) d

/-- `geoTerm k (p+j) ≃ (η_max·r^p)·r^j`. -/
theorem geoTerm_shift_eqv {k : Nat} (hk : 0 < k) (p j : Nat) :
    (geoTerm k hk (p + j)).eqv ((etaMax k hk * (ratio k hk) ^ p) * (ratio k hk) ^ j) := by
  show (etaMax k hk * (ratio k hk) ^ (p + j)).eqv _
  -- r^(p+j) ≃ r^p * r^j (pow_add at Q' via induction on j)
  have hpow : ((ratio k hk) ^ (p + j)).eqv ((ratio k hk) ^ p * (ratio k hk) ^ j) := by
    induction j with
    | zero =>
      show ((ratio k hk) ^ p).eqv ((ratio k hk) ^ p * (ratio k hk) ^ 0)
      show ((ratio k hk) ^ p).eqv ((ratio k hk) ^ p * 1)
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
    | succ n ih =>
      -- r^(p+(n+1)) = r * r^(p+n) ; target r^p * (r * r^n)
      show ((ratio k hk) * (ratio k hk) ^ (p + n)).eqv
          ((ratio k hk) ^ p * ((ratio k hk) * (ratio k hk) ^ n))
      have e1 : ((ratio k hk) * (ratio k hk) ^ (p + n)).eqv
          ((ratio k hk) * ((ratio k hk) ^ p * (ratio k hk) ^ n)) :=
        Q'.mul_eqv_congr_left _ _ _ ih
      refine Q'.eqv_trans _ _ _ e1 ?_
      -- r * (r^p * r^n) ≃ r^p * (r * r^n)
      have e2 : ((ratio k hk) * ((ratio k hk) ^ p * (ratio k hk) ^ n)).eqv
          (((ratio k hk) * (ratio k hk) ^ p) * (ratio k hk) ^ n) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      refine Q'.eqv_trans _ _ _ e2 ?_
      have e3 : (((ratio k hk) * (ratio k hk) ^ p) * (ratio k hk) ^ n).eqv
          (((ratio k hk) ^ p * (ratio k hk)) * (ratio k hk) ^ n) :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
      refine Q'.eqv_trans _ _ _ e3 ?_
      exact Q'.mul_assoc_eqv _ _ _
  -- η_max * r^(p+j) ≃ η_max * (r^p * r^j) ≃ (η_max * r^p) * r^j
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hpow) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- **Geometric block bound.** With `0 ≤ r`, `0 ≤ H`, and the recurrence
`η_max + r·H ≤ H`, every shifted geometric block is bounded:
`geoBlock k p d ≤ r^p · H`.  Uses `geometric_tail_closure` applied to the
shifted series `(η_max·r^p)·r^j`. -/
theorem geoBlock_le {k : Nat} (hk : 0 < k) (H : Q')
    (hH : (0 : Q') ≤ H)
    (hrec : etaMax k hk + ratio k hk * H ≤ H) (p d : Nat) :
    geoBlock k hk p d ≤ (ratio k hk) ^ p * H := by
  -- shifted series majorized by etap := η_max·r^p, ratio r, bound Hp := r^p·H
  -- (written out in full; `set` is unavailable in this Mathlib-free build).
  have hrp_nn : (0 : Q') ≤ (ratio k hk) ^ p := Q'.pow_nonneg _ (ratio_nonneg hk) p
  have hHp_nn : (0 : Q') ≤ (ratio k hk) ^ p * H := Q'.mul_nonneg _ _ hrp_nn hH
  -- recurrence for the shifted series:  etap + r·Hp ≤ Hp
  have hrec' : (etaMax k hk * (ratio k hk) ^ p)
        + ratio k hk * ((ratio k hk) ^ p * H) ≤ (ratio k hk) ^ p * H := by
    -- multiply the base recurrence by r^p ≥ 0:  r^p·(η_max + r·H) ≤ r^p·H
    have base : (ratio k hk) ^ p * (etaMax k hk + ratio k hk * H)
        ≤ (ratio k hk) ^ p * H :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hrec hrp_nn
    have hdist : ((ratio k hk) ^ p * (etaMax k hk + ratio k hk * H)).eqv
        ((ratio k hk) ^ p * etaMax k hk + (ratio k hk) ^ p * (ratio k hk * H)) :=
      Q'.mul_add_eqv _ _ _
    have hA : ((ratio k hk) ^ p * etaMax k hk).eqv (etaMax k hk * (ratio k hk) ^ p) :=
      Q'.mul_comm_eqv _ _
    have hB : ((ratio k hk) ^ p * (ratio k hk * H)).eqv
        (ratio k hk * ((ratio k hk) ^ p * H)) := by
      have b1 : ((ratio k hk) ^ p * (ratio k hk * H)).eqv
          (((ratio k hk) ^ p * ratio k hk) * H) := Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      have b2 : (((ratio k hk) ^ p * ratio k hk) * H).eqv
          ((ratio k hk * (ratio k hk) ^ p) * H) :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)
      have b3 : ((ratio k hk * (ratio k hk) ^ p) * H).eqv
          (ratio k hk * ((ratio k hk) ^ p * H)) := Q'.mul_assoc_eqv _ _ _
      exact Q'.eqv_trans _ _ _ b1 (Q'.eqv_trans _ _ _ b2 b3)
    have hLHS : ((ratio k hk) ^ p * (etaMax k hk + ratio k hk * H)).eqv
        ((etaMax k hk * (ratio k hk) ^ p) + ratio k hk * ((ratio k hk) ^ p * H)) := by
      refine Q'.eqv_trans _ _ _ hdist ?_
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ hA)
        (Q'.add_eqv_congr_left _ _ _ hB)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hLHS) base
  have hr0 : (0 : Q') ≤ ratio k hk := ratio_nonneg hk
  have tail := geometric_tail_closure (etaMax k hk * (ratio k hk) ^ p)
    (ratio k hk) ((ratio k hk) ^ p * H) hr0 hHp_nn hrec' d
  refine Q'.le_trans' _ _ _ ?_ tail
  apply ExpNeg.finSum_le_finSum_of_termwise
  intro j
  exact Q'.le_of_eqv (geoTerm_shift_eqv hk p j)

/-- **`c`-block bound.** `Σ_{j<d} c_{p+j} ≤ r^p · H`. -/
theorem cBlock_le {k : Nat} (hk : 0 < k) (H : Q') (hH : (0 : Q') ≤ H)
    (hrec : etaMax k hk + ratio k hk * H ≤ H) (p d : Nat) :
    finSum (fun j => cTerm k hk (p + j)) d ≤ (ratio k hk) ^ p * H :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise
      (fun j => cTerm k hk (p + j)) (fun j => geoTerm k hk (p + j))
      (fun j => cTerm_le_geoTerm hk (p + j)) d)
    (geoBlock_le hk H hH hrec p d)

/-- **Block upper bound on partial sums** (mirrors `ExpNeg.block_upper`):
`cPart (p+d) ≤ cPart p + Σ_{j<d} c_{p+j}`.  Induction on `d`, regrouping
with `add_assoc_eqv` only (no commutation). -/
theorem cPart_block_upper (k : Nat) (hk : 0 < k) (p : Nat) :
    ∀ d, cPart k hk (p + d) ≤ cPart k hk p + finSum (fun j => cTerm k hk (p + j)) d
  | 0 => by
    show cPart k hk p ≤ cPart k hk p + (0 : Q')
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := cPart_block_upper k hk p d
    show finSum (cTerm k hk) (p + d) + cTerm k hk (p + d)
        ≤ cPart k hk p + (finSum (fun j => cTerm k hk (p + j)) d + cTerm k hk (p + d))
    have ih' : finSum (cTerm k hk) (p + d) + cTerm k hk (p + d)
        ≤ (cPart k hk p + finSum (fun j => cTerm k hk (p + j)) d) + cTerm k hk (p + d) :=
      Q'.add_le_add_right _ _ _ ih
    exact Q'.le_trans' _ _ _ ih'
      (Q'.le_of_eqv (Q'.add_assoc_eqv (cPart k hk p)
        (finSum (fun j => cTerm k hk (p + j)) d) (cTerm k hk (p + d))))

/-- **The eventual Cauchy block bound.** `cPart (p+d) ≤ cPart p + r^p·H`. -/
theorem cPart_block {k : Nat} (hk : 0 < k) (H : Q') (hH : (0 : Q') ≤ H)
    (hrec : etaMax k hk + ratio k hk * H ≤ H) (p d : Nat) :
    cPart k hk (p + d) ≤ cPart k hk p + (ratio k hk) ^ p * H :=
  Q'.le_trans' _ _ _ (cPart_block_upper k hk p d)
    (Q'.add_le_add_left _ _ _ (cBlock_le hk H hH hrec p d))

/-! ## 5. The convergence modulus: `r^p·H → 0` -/

/-- `r ≤ 1/2` for `k ≥ 2` (since `k^4 ≥ 2`). -/
theorem ratio_le_half {k : Nat} (hk : 2 ≤ k) :
    ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) ≤ HalfPow.half := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  show (ratio k hk0).num * (HalfPow.half.den : Int)
      ≤ HalfPow.half.num * ((ratio k hk0).den : Int)
  show (Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk0 4)).num * ((HalfPow.half).den : Int)
      ≤ (HalfPow.half).num * ((Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk0 4)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (1 : Int) * ((HalfPow.half).den : Int)
      ≤ (HalfPow.half).num * ((k ^ 4 : Nat) : Int)
  -- half = mkPos 1 2, so num = 1, den = 2.  need 2 ≤ k^4.
  show (1 : Int) * ((HalfPow.half).den : Int)
      ≤ (HalfPow.half).num * ((k ^ 4 : Nat) : Int)
  have hden : (HalfPow.half).den = 2 := Q'.mkPos_den 1 2 (by decide)
  have hnum : (HalfPow.half).num = 1 := Q'.mkPos_num 1 2 (by decide)
  rw [hden, hnum, Int.one_mul, Int.one_mul]
  -- 2 ≤ k^4
  have h24 : (2 : Nat) ≤ k ^ 4 := by
    calc (2 : Nat) ≤ k := hk
      _ = k ^ 1 := (Nat.pow_one k).symm
      _ ≤ k ^ 4 := nat_pow_le_pow (Nat.le_trans (by decide : (1:Nat) ≤ 2) hk)
          (by decide)
  exact_mod_cast h24

/-- `r^p · H → 0` with explicit modulus: for `δ > 0`, taking
`p = (δ over H)`-stage from `HalfPow` gives `r^p·H ≤ δ`.  Concretely we use
`r^p ≤ half^p ≤ 1/(p+1)` and pick `p` from the target.  Packaged as: for any
`ε > 0` there is `N` with `r^N · H ≤ ε`. -/
theorem ratio_pow_antitone_half {k : Nat} (hk : 2 ≤ k) (p : Nat) :
    (ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)) ^ p ≤ HalfPow.half ^ p := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  induction p with
  | zero => exact Q'.le_refl' _
  | succ n ih =>
    show ratio k hk0 * (ratio k hk0) ^ n ≤ HalfPow.half * HalfPow.half ^ n
    have hr_nn : (0 : Q') ≤ ratio k hk0 := ratio_nonneg hk0
    have hhp_nn : (0 : Q') ≤ HalfPow.half ^ n := Q'.pow_nonneg _ HalfPow.half_nonneg n
    -- r * r^n ≤ r * half^n ≤ half * half^n
    have s1 : ratio k hk0 * (ratio k hk0) ^ n ≤ ratio k hk0 * HalfPow.half ^ n :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ ih hr_nn
    have s2 : ratio k hk0 * HalfPow.half ^ n ≤ HalfPow.half * HalfPow.half ^ n :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_le_half hk) hhp_nn
    exact Q'.le_trans' _ _ _ s1 s2

/-- `ratio k ≤ 1` (since `k^4 ≥ 1`). -/
theorem ratio_le_one {k : Nat} (hk : 0 < k) : ratio k hk ≤ (1 : Q') := by
  show (ratio k hk).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((ratio k hk).den : Int)
  show (Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk 4)).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((Q'.mkPos 1 (k ^ 4) (nat_pow_pos hk 4)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (1 : Int) * ((1 : Q').den : Int) ≤ (1 : Q').num * ((k ^ 4 : Nat) : Int)
  have h1 : (1 : Q').den = 1 := rfl
  have h2 : (1 : Q').num = 1 := rfl
  rw [h1, h2, Int.one_mul, Int.one_mul]
  have : (1 : Nat) ≤ k ^ 4 := nat_pow_pos hk 4
  exact_mod_cast this

/-- `r^(N+d) ≤ r^N` (since `0 ≤ r ≤ 1`). -/
theorem ratioPow_add_le {k : Nat} (hk : 0 < k) (N : Nat) :
    ∀ d, (ratio k hk) ^ (N + d) ≤ (ratio k hk) ^ N
  | 0 => Q'.le_refl' _
  | e + 1 => by
    show ratio k hk * (ratio k hk) ^ (N + e) ≤ (ratio k hk) ^ N
    have hrne_nn : (0 : Q') ≤ (ratio k hk) ^ (N + e) :=
      Q'.pow_nonneg _ (ratio_nonneg hk) (N + e)
    have hstep : ratio k hk * (ratio k hk) ^ (N + e) ≤ (ratio k hk) ^ (N + e) := by
      have h1 : ratio k hk * (ratio k hk) ^ (N + e) ≤ 1 * (ratio k hk) ^ (N + e) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_le_one hk) hrne_nn
      exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.one_mul_eqv _))
    exact Q'.le_trans' _ _ _ hstep (ratioPow_add_le hk N e)

/-- `r^·` is antitone in the exponent: `N ≤ p → r^p ≤ r^N`. -/
theorem ratioPow_antitone {k : Nat} (hk : 0 < k) {N p : Nat} (h : N ≤ p) :
    (ratio k hk) ^ p ≤ (ratio k hk) ^ N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ratioPow_add_le hk N d

/-- **Explicit convergence modulus.**  For `H ≤ 1` and any `ε > 0`, taking
`N := ε.den` forces `r^N · H ≤ ε`.  Chain: `r^N·H ≤ half^N·H ≤ half^N ≤ ε`. -/
theorem ratioPow_mul_H_le {k : Nat} (hk : 2 ≤ k) {H : Q'}
    (hH0 : (0 : Q') ≤ H) (hH1 : H ≤ (1 : Q')) (ε : Q') (hε : (0 : Q') < ε) :
    (ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)) ^ ε.den * H ≤ ε := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
  -- r^N · H ≤ half^N · H
  have hhN_nn : (0 : Q') ≤ HalfPow.half ^ ε.den :=
    Q'.pow_nonneg _ HalfPow.half_nonneg ε.den
  have step1 : (ratio k hk0) ^ ε.den * H ≤ HalfPow.half ^ ε.den * H :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (ratio_pow_antitone_half hk ε.den) hH0
  -- half^N · H ≤ half^N · 1 = half^N
  have step2 : HalfPow.half ^ ε.den * H ≤ HalfPow.half ^ ε.den * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hH1 hhN_nn
  have step2' : HalfPow.half ^ ε.den * 1 ≤ HalfPow.half ^ ε.den :=
    Q'.le_of_eqv (Q'.mul_one_eqv _)
  -- half^N ≤ ε
  have step3 : HalfPow.half ^ ε.den ≤ ε := HalfPow.pow_half_le ε hε
  exact Q'.le_trans' _ _ _ step1
    (Q'.le_trans' _ _ _ step2 (Q'.le_trans' _ _ _ step2' step3))

/-! ## 6. `arctanRecip k`: the constructive `arctan(1/k)` -/

/-- **`arctan(1/k)` as a regular Cauchy real.**  The approximations are the
monotone partial sums `Σ_{j<n} c_j` of the paired arctan series.  The Cauchy
modulus is genuine: monotonicity gives one direction, the geometric block
bound `Σ_{p≤j<q} c_j ≤ r^p·H` the other, and `r^N·H ≤ ε` at `N := ε.den`. -/
def arctanRecip (k : Nat) (hk : 2 ≤ k) (H : Q')
    (hH0 : (0 : Q') ≤ H) (hH1 : H ≤ (1 : Q'))
    (hrec : etaMax k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)
              + ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) * H ≤ H) : CReal where
  approx := cPart k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)
  cauchy := by
    have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_two hk
    intro ε hε
    refine ⟨ε.den, fun m n hm hn => ?_⟩
    -- directional bound for p ≤ q
    have dir : ∀ p q : Nat, ε.den ≤ p → p ≤ q →
        cPart k hk0 q ≤ cPart k hk0 p + ε ∧ cPart k hk0 p ≤ cPart k hk0 q + ε := by
      intro p q hp hpq
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
      refine ⟨?_, ?_⟩
      · -- cPart (p+d) ≤ cPart p + r^p·H ≤ cPart p + r^N·H ≤ cPart p + ε
        have hblock := cPart_block hk0 H hH0 hrec p d
        -- r^p·H ≤ r^N·H ≤ ε  (since p ≥ N = ε.den ⟹ r^p ≤ r^N)
        have hrp_le_rN : (ratio k hk0) ^ p ≤ (ratio k hk0) ^ ε.den := by
          -- ratio ≤ 1 so r^p ≤ r^N for p ≥ N: antitone in exponent
          exact ratioPow_antitone hk0 hp
        have hH_nn := hH0
        have hrp_H_le : (ratio k hk0) ^ p * H ≤ (ratio k hk0) ^ ε.den * H :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hrp_le_rN hH0
        have hmod : (ratio k hk0) ^ ε.den * H ≤ ε := ratioPow_mul_H_le hk hH0 hH1 ε hε
        have htail : (ratio k hk0) ^ p * H ≤ ε := Q'.le_trans' _ _ _ hrp_H_le hmod
        exact Q'.le_trans' _ _ _ hblock
          (Q'.add_le_add_left _ _ _ htail)
      · -- cPart p ≤ cPart (p+d) ≤ cPart (p+d) + ε  (monotone)
        have hmono : cPart k hk0 p ≤ cPart k hk0 (p + d) :=
          cPart_mono k hk0 (Nat.le_add_right p d)
        exact Q'.le_trans' _ _ _ hmono
          (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hε))
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

@[simp] theorem arctanRecip_approx (k : Nat) (hk : 2 ≤ k) (H : Q')
    (hH0 : (0 : Q') ≤ H) (hH1 : H ≤ (1 : Q'))
    (hrec : etaMax k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk)
              + ratio k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) * H ≤ H) (n : Nat) :
    (arctanRecip k hk H hH0 hH1 hrec).approx n
      = cPart k (Nat.lt_of_lt_of_le Nat.zero_lt_two hk) n := rfl

/-- **Global majorant bound.** `cPart k n ≤ H` for all `n`
(geometric tail closure at `p = 0`). -/
theorem cPart_le_H {k : Nat} (hk : 0 < k) (H : Q') (hH : (0 : Q') ≤ H)
    (hrec : etaMax k hk + ratio k hk * H ≤ H) (n : Nat) :
    cPart k hk n ≤ H := by
  -- cBlock_le at p = 0 : finSum (fun j => cTerm (0+j)) n ≤ r^0·H = 1·H
  have h := cBlock_le hk H hH hrec 0 n
  -- finSum (fun j => cTerm (0+j)) n  is  cPart n  (since 0+j = j)
  have heq : (fun j => cTerm k hk (0 + j)) = cTerm k hk := by
    funext j; rw [Nat.zero_add]
  rw [heq] at h
  -- r^0·H = 1·H ≃ H
  refine Q'.le_trans' _ _ _ h ?_
  show (ratio k hk) ^ 0 * H ≤ H
  show (1 : Q') * H ≤ H
  exact Q'.le_of_eqv (Q'.one_mul_eqv H)

/-! ## 7. `pi` (Machin) and its bounds -/

/-- `arctan(1/5)` with `H = 1/4`. -/
def at5 : CReal :=
  arctanRecip 5 (by decide) (Q'.mkPos 1 4 (by decide)) (by decide) (by decide) (by decide)

/-- `arctan(1/239)` with `H = 1/238`. -/
def at239 : CReal :=
  arctanRecip 239 (by decide) (Q'.mkPos 1 238 (by decide)) (by decide) (by decide) (by decide)

theorem at5_approx (n : Nat) : at5.approx n = cPart 5 (by decide) n := rfl
theorem at239_approx (n : Nat) : at239.approx n = cPart 239 (by decide) n := rfl

/-- **`π = 16·arctan(1/5) − 4·arctan(1/239)`** (Machin), a regular Cauchy real. -/
def pi : CReal :=
  CReal.sub (CReal.mul (CReal.ofQ' (16 : Q')) at5) (CReal.mul (CReal.ofQ' (4 : Q')) at239)

theorem pi_approx (n : Nat) :
    pi.approx n = (16 : Q') * at5.approx n + (-((4 : Q') * at239.approx n)) := rfl

/-! ### Upper bound `π ≤ 4` -/

/-- Every approximation `pi.approx n ≤ 4`.  Since `16·cPart5 n ≤ 16·(1/4) = 4`
and `4·cPart239 n ≥ 0`, the difference is `≤ 4`. -/
theorem pi_approx_le_four (n : Nat) : pi.approx n ≤ (4 : Q') := by
  rw [pi_approx, at5_approx, at239_approx]
  -- 16·cPart5 n ≤ 4
  have h5 : cPart 5 (by decide) n ≤ Q'.mkPos 1 4 (by decide) :=
    cPart_le_H (by decide) (Q'.mkPos 1 4 (by decide)) (by decide) (by decide) n
  have h16 : (16 : Q') * cPart 5 (by decide) n ≤ (16 : Q') * Q'.mkPos 1 4 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h5 (by decide)
  have h16' : (16 : Q') * Q'.mkPos 1 4 (by decide) ≤ (4 : Q') := by decide
  have hub : (16 : Q') * cPart 5 (by decide) n ≤ (4 : Q') :=
    Q'.le_trans' _ _ _ h16 h16'
  -- -(4·cPart239 n) ≤ 0
  have hpos239 : (0 : Q') ≤ (4 : Q') * cPart 239 (by decide) n :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.le_trans' _ _ _ (Q'.le_refl' 0)
        (finSum_monotone_of_nonneg (cTerm 239 (by decide))
          (fun j => cTerm_nonneg (by decide) j) 0 n (Nat.zero_le n)))
  have hneg : (-((4 : Q') * cPart 239 (by decide) n)) ≤ 0 := by
    have h1 := Q'.neg_le_neg hpos239
    have h2 : ((-(0 : Q'))).eqv 0 := by decide
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)
  -- combine: 16·cPart5 + (-(4·cPart239)) ≤ 4 + 0 = 4
  have hcomb : (16 : Q') * cPart 5 (by decide) n + (-((4 : Q') * cPart 239 (by decide) n))
      ≤ (4 : Q') + 0 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hub)
      (Q'.add_le_add_left _ _ _ hneg)
  exact Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- **`π ≤ 4`** at the regularity-free order. -/
theorem pi_leRat_four : CReal.leRat pi (4 : Q') :=
  CReal.leRat_of_eventually ⟨0, fun n _ => pi_approx_le_four n⟩

/-! ### Lower bound `π ≥ 3` -/

/-- For `n ≥ 1`, `3 ≤ pi.approx n`.  Uses `cPart5 n ≥ cPart5 1` (monotone) and
`cPart239 n ≤ 1/238` (global majorant), then a `decide` on the rationals. -/
theorem three_le_pi_approx {n : Nat} (hn : 1 ≤ n) : (3 : Q') ≤ pi.approx n := by
  rw [pi_approx, at5_approx, at239_approx]
  -- cPart5 n ≥ cPart5 1
  have h5 : cPart 5 (by decide) 1 ≤ cPart 5 (by decide) n :=
    cPart_mono 5 (by decide) hn
  have h16 : (16 : Q') * cPart 5 (by decide) 1 ≤ (16 : Q') * cPart 5 (by decide) n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h5 (by decide)
  -- cPart239 n ≤ 1/238
  have h239 : cPart 239 (by decide) n ≤ Q'.mkPos 1 238 (by decide) :=
    cPart_le_H (by decide) (Q'.mkPos 1 238 (by decide)) (by decide) (by decide) n
  have h4 : (4 : Q') * cPart 239 (by decide) n ≤ (4 : Q') * Q'.mkPos 1 238 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h239 (by decide)
  -- -(4·cPart239 n) ≥ -(4·(1/238))
  have hneg : (-((4 : Q') * Q'.mkPos 1 238 (by decide)))
      ≤ (-((4 : Q') * cPart 239 (by decide) n)) := Q'.neg_le_neg h4
  -- assemble lower bound:  16·cPart5 1 + (-(4·(1/238))) ≤ pi.approx n
  have hlow : (16 : Q') * cPart 5 (by decide) 1 + (-((4 : Q') * Q'.mkPos 1 238 (by decide)))
      ≤ (16 : Q') * cPart 5 (by decide) n + (-((4 : Q') * cPart 239 (by decide) n)) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ h16)
      (Q'.add_le_add_left _ _ _ hneg)
  -- 3 ≤ 16·cPart5 1 − 4·(1/238)  by decide  (cPart5 1 = cTerm5 0 is a concrete rational)
  have hbase : (3 : Q')
      ≤ (16 : Q') * cPart 5 (by decide) 1 + (-((4 : Q') * Q'.mkPos 1 238 (by decide))) := by
    show (3 : Q')
      ≤ (16 : Q') * (finSum (cTerm 5 (by decide)) 1)
          + (-((4 : Q') * Q'.mkPos 1 238 (by decide)))
    decide
  exact Q'.le_trans' _ _ _ hbase hlow

/-- **`π ≥ 3`** at the regularity-free order. -/
theorem pi_geRat_three : ExpPos.geRat pi (3 : Q') :=
  ExpPos.geRat_of_eventually ⟨1, fun n hn => three_le_pi_approx hn⟩

/-! ### Strict positivity of `π` -/

/-- **`π` is positive** (`IsPositive`), witness `ε = 1/2`.
At `n = 0` the one-slack `invSucc 0 = 1` carries it; for `n ≥ 1`,
`pi.approx n ≥ 3 ≥ 1/2`. -/
theorem pi_pos : CReal.IsPositive pi := by
  refine ⟨Q'.mkPos 1 2 (by decide), by decide, ?_⟩
  -- ofQ' (1/2) ≤ pi  via one-slack: 1/2 ≤ pi.approx n + invSucc n for all n
  intro n
  show Q'.mkPos 1 2 (by decide) ≤ pi.approx n + Q'.invSucc n
  cases n with
  | zero =>
    -- pi.approx 0 = 0 ; invSucc 0 = 1 ; 1/2 ≤ 0 + 1
    have h0 : pi.approx 0 = 0 := by
      rw [pi_approx, at5_approx, at239_approx]
      decide
    rw [h0]
    show Q'.mkPos 1 2 (by decide) ≤ (0 : Q') + Q'.invSucc 0
    decide
  | succ m =>
    -- 1/2 ≤ 3 ≤ pi.approx (m+1) ≤ pi.approx (m+1) + invSucc (m+1)
    have h3 : (3 : Q') ≤ pi.approx (m + 1) := three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le m))
    have hhalf3 : Q'.mkPos 1 2 (by decide) ≤ (3 : Q') := by decide
    have hstep : pi.approx (m + 1) ≤ pi.approx (m + 1) + Q'.invSucc (m + 1) :=
      Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg (m + 1))
    exact Q'.le_trans' _ _ _ hhalf3 (Q'.le_trans' _ _ _ h3 hstep)

/-! ### Half-π positivity -/

/-- `halfPi = (1/2)·π`. -/
def halfPi : CReal := CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide))) pi

theorem halfPi_approx (n : Nat) :
    halfPi.approx n = Q'.mkPos 1 2 (by decide) * pi.approx n := rfl

/-- **`(1/2)·π` is positive**, witness `ε = 1/2`.  For `n ≥ 1`,
`(1/2)·pi.approx n ≥ (1/2)·3 = 3/2 ≥ 1/2`; the `n = 0` case rides `invSucc 0 = 1`. -/
theorem halfPi_pos : CReal.IsPositive halfPi := by
  refine ⟨Q'.mkPos 1 2 (by decide), by decide, ?_⟩
  intro n
  show Q'.mkPos 1 2 (by decide) ≤ halfPi.approx n + Q'.invSucc n
  rw [halfPi_approx]
  cases n with
  | zero =>
    have h0 : pi.approx 0 = 0 := by rw [pi_approx, at5_approx, at239_approx]; decide
    rw [h0]
    show Q'.mkPos 1 2 (by decide)
        ≤ Q'.mkPos 1 2 (by decide) * (0 : Q') + Q'.invSucc 0
    decide
  | succ m =>
    have h3 : (3 : Q') ≤ pi.approx (m + 1) :=
      three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le m))
    -- (1/2)·3 = 3/2 ≤ (1/2)·pi.approx
    have hmul : Q'.mkPos 1 2 (by decide) * (3 : Q')
        ≤ Q'.mkPos 1 2 (by decide) * pi.approx (m + 1) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ h3 (by decide)
    have hhalf : Q'.mkPos 1 2 (by decide) ≤ Q'.mkPos 1 2 (by decide) * (3 : Q') := by decide
    have hstep : Q'.mkPos 1 2 (by decide) * pi.approx (m + 1)
        ≤ Q'.mkPos 1 2 (by decide) * pi.approx (m + 1) + Q'.invSucc (m + 1) :=
      Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg (m + 1))
    exact Q'.le_trans' _ _ _ hhalf (Q'.le_trans' _ _ _ hmul hstep)

/-! ## 8. `2/π`

`twoOverPi.approx n := 2 · (1/pi.approx (n+1))`, where the reciprocal of the
positive rational `pi.approx (n+1)` (which is `≥ 3` for `n ≥ 0`, hence has
positive numerator) is `mkPos den num`.  We deliver `twoOverPi` and
`twoOverPi_pos`; the reciprocal law `(2/π)·π ≃ 2` is the single NAMED-open
residual (see header). -/

/-- Reciprocal of a `Q'` with positive numerator: swap num/den. -/
def recipPosNum (q : Q') (h : 0 < q.num) : Q' :=
  Q'.mkPos (q.den : Int) q.num.toNat (by
    have he : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg (Int.le_of_lt h)
    have : (0 : Int) < (q.num.toNat : Int) := by rw [he]; exact h
    exact_mod_cast this)

theorem recipPosNum_num (q : Q') (h : 0 < q.num) : (recipPosNum q h).num = (q.den : Int) :=
  Q'.mkPos_num _ _ _

theorem recipPosNum_den (q : Q') (h : 0 < q.num) : (recipPosNum q h).den = q.num.toNat :=
  Q'.mkPos_den _ _ _

/-- `pi.approx (n+1)` has positive numerator (it is `≥ 3 > 0`). -/
theorem pi_approx_succ_num_pos (n : Nat) : 0 < (pi.approx (n + 1)).num := by
  have h3 : (3 : Q') ≤ pi.approx (n + 1) :=
    three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le n))
  have hpos : (0 : Q') < pi.approx (n + 1) := by
    show (0 : Q').num * ((pi.approx (n + 1)).den : Int)
        < (pi.approx (n + 1)).num * ((0 : Q').den : Int)
    show (0 : Int) * ((pi.approx (n + 1)).den : Int)
        < (pi.approx (n + 1)).num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    have hle' : (3 : Int) * ((pi.approx (n + 1)).den : Int) ≤ (pi.approx (n + 1)).num := by
      have hh : (3 : Q').num * ((pi.approx (n + 1)).den : Int)
          ≤ (pi.approx (n + 1)).num * ((3 : Q').den : Int) := h3
      have e1 : (3 : Q').num = 3 := rfl
      have e2 : ((3 : Q').den : Int) = 1 := rfl
      rw [e1, e2, Int.mul_one] at hh
      exact hh
    have hden_pos : (0 : Int) < ((pi.approx (n + 1)).den : Int) := by
      exact_mod_cast Nat.succ_pos _
    have h3den_pos : (0 : Int) < (3 : Int) * ((pi.approx (n + 1)).den : Int) :=
      Int.mul_pos (by decide) hden_pos
    exact Int.lt_of_lt_of_le h3den_pos hle'
  exact CReal.num_pos_of_pos hpos

/-- `a + -b ≤ c → a ≤ b + c`. -/
theorem le_add_of_sub_le {a b c : Q'} (h : a + (-b) ≤ c) : a ≤ b + c := by
  -- add b on the right, then rearrange via eqv
  have h1 : (a + (-b)) + b ≤ c + b := Q'.add_le_add_right _ _ _ h
  have e1 : ((a + (-b)) + b).eqv a := by
    -- (a + -b) + b ≃ a + (-b + b) ≃ a + 0 ≃ a
    have s1 : ((a + (-b)) + b).eqv (a + ((-b) + b)) := Q'.add_assoc_eqv a (-b) b
    have s2 : (a + ((-b) + b)).eqv (a + 0) :=
      Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)
    have s3 : (a + (0 : Q')).eqv a := Q'.eqv_of_eq (Q'.add_zero' a)
    exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 s3)
  have e2 : (c + b).eqv (b + c) := Q'.add_comm_eqv c b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e2))

/-- **Reciprocal Lipschitz (direction lemma).**  For `a b` with positive
numerators, `a.den ≤ a.num` and `b.den ≤ b.num` (i.e. both `≥ 1`), and
`b ≤ a + δ` with `0 ≤ δ`:  `recipPosNum a ≤ recipPosNum b + δ`.
Pure `Q'` cross-product fact:  `1/a − 1/b = (b−a)/(ab) ≤ δ·(dA·dB)/(ab) ≤ δ`. -/
theorem recipDir {a b δ : Q'} (ha : 0 < a.num) (hb : 0 < b.num)
    (hda : (a.den : Int) ≤ a.num) (hdb : (b.den : Int) ≤ b.num)
    (hδ : (0 : Q') ≤ δ) (hab : b ≤ a + δ) :
    recipPosNum a ha ≤ recipPosNum b hb + δ := by
  apply le_add_of_sub_le
  -- goal: recipPosNum a + -(recipPosNum b) ≤ δ
  -- reduce to Int cross-product
  have hAt : ((a.num.toNat : Nat) : Int) = a.num := Int.toNat_of_nonneg (Int.le_of_lt ha)
  have hBt : ((b.num.toNat : Nat) : Int) = b.num := Int.toNat_of_nonneg (Int.le_of_lt hb)
  show (recipPosNum a ha + (-(recipPosNum b hb))).num * (δ.den : Int)
      ≤ δ.num * ((recipPosNum a ha + (-(recipPosNum b hb))).den : Int)
  -- num/den of the sum
  have hnum : (recipPosNum a ha + (-(recipPosNum b hb))).num
      = (recipPosNum a ha).num * ((-(recipPosNum b hb)).den : Int)
        + (-(recipPosNum b hb)).num * ((recipPosNum a ha).den : Int) := rfl
  have hden : ((recipPosNum a ha + (-(recipPosNum b hb))).den : Int)
      = ((recipPosNum a ha).den : Int) * ((-(recipPosNum b hb)).den : Int) :=
    Q'.add_den_cast _ _
  rw [hnum, hden]
  -- (-(recip b)).num = -(b.den) ; (-(recip b)).den = recip b.den = b.num.toNat
  have hnegnum : (-(recipPosNum b hb)).num = -((recipPosNum b hb).num) := rfl
  have hnegden : (-(recipPosNum b hb)).den = (recipPosNum b hb).den := rfl
  rw [hnegnum, hnegden, recipPosNum_num, recipPosNum_den, recipPosNum_num, recipPosNum_den]
  -- LHS num: a.den * b.num.toNat + (-(b.den)) * a.num.toNat
  -- den: a.num.toNat * b.num.toNat
  -- Substitute toNat casts
  rw [hAt, hBt]
  -- goal now: (a.den * b.num + (-(b.den)) * a.num) * δ.den
  --           ≤ δ.num * (a.num * b.num)
  -- Establish the value inequality from hab : b ≤ a + δ
  -- hab cross:  b.num * (a+δ).den ≤ (a+δ).num * b.den
  -- (a+δ).num = a.num*δ.den + δ.num*a.den ; (a+δ).den = a.den*δ.den
  have habc : b.num * (((a + δ).den : Int)) ≤ (a + δ).num * (b.den : Int) := hab
  have hadnum : (a + δ).num = a.num * (δ.den : Int) + δ.num * (a.den : Int) := rfl
  have hadden : ((a + δ).den : Int) = (a.den : Int) * (δ.den : Int) := Q'.add_den_cast _ _
  rw [hadnum, hadden] at habc
  -- habc : b.num * (a.den*δ.den) ≤ (a.num*δ.den + δ.num*a.den) * b.den
  -- Want: (a.den*b.num - b.den*a.num) * δ.den ≤ δ.num * (a.num*b.num)
  -- Key bound chain in Int.
  have hda_nn : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hdb_nn : (0 : Int) ≤ (b.den : Int) := Int.natCast_nonneg _
  have hδnum_nn : (0 : Int) ≤ δ.num := (Q'.zero_le_iff_num_nonneg δ).mp hδ
  have hδden_pos : (0 : Int) < (δ.den : Int) := by exact_mod_cast Nat.succ_pos _
  -- from habc:  b.num*a.den*δ.den ≤ a.num*δ.den*b.den + δ.num*a.den*b.den
  -- rearrange to:  (a.den*b.num - b.den*a.num)*δ.den ≤ δ.num*a.den*b.den
  -- Normalize habc into atoms P := a.den*b.num*δ.den, Q := b.den*a.num*δ.den,
  -- R := δ.num*(a.den*b.den).
  have eL : b.num * ((a.den : Int) * (δ.den : Int))
      = (a.den : Int) * b.num * (δ.den : Int) := by ac_rfl
  have eR : (a.num * (δ.den : Int) + δ.num * (a.den : Int)) * (b.den : Int)
      = (b.den : Int) * a.num * (δ.den : Int) + δ.num * ((a.den : Int) * (b.den : Int)) := by
    rw [Int.add_mul]
    have r1 : a.num * (δ.den : Int) * (b.den : Int)
        = (b.den : Int) * a.num * (δ.den : Int) := by ac_rfl
    have r2 : δ.num * (a.den : Int) * (b.den : Int)
        = δ.num * ((a.den : Int) * (b.den : Int)) := by ac_rfl
    rw [r1, r2]
  rw [eL, eR] at habc
  -- habc : a.den*b.num*δ.den ≤ b.den*a.num*δ.den + δ.num*(a.den*b.den)
  -- upgrade δ.num*(a.den*b.den) ≤ δ.num*(a.num*b.num)
  have hub : δ.num * ((a.den : Int) * (b.den : Int)) ≤ δ.num * (a.num * b.num) := by
    have hmono : (a.den : Int) * (b.den : Int) ≤ a.num * b.num := by
      have h1 : (a.den : Int) * (b.den : Int) ≤ a.num * (b.den : Int) :=
        Int.mul_le_mul_of_nonneg_right hda hdb_nn
      have h2 : a.num * (b.den : Int) ≤ a.num * b.num :=
        Int.mul_le_mul_of_nonneg_left hdb (Int.le_of_lt ha)
      exact Int.le_trans h1 h2
    exact Int.mul_le_mul_of_nonneg_left hmono hδnum_nn
  -- rewrite goal LHS to atom form
  have lhs_eq : ((a.den : Int) * b.num + (-(b.den : Int)) * a.num) * (δ.den : Int)
      = (a.den : Int) * b.num * (δ.den : Int) - (b.den : Int) * a.num * (δ.den : Int) := by
    rw [Int.add_mul]
    have q1 : (-(b.den : Int)) * a.num * (δ.den : Int)
        = -((b.den : Int) * a.num * (δ.den : Int)) := by
      rw [Int.neg_mul, Int.neg_mul]
    rw [q1, Int.sub_eq_add_neg]
  rw [lhs_eq]
  -- final linear combination (omega abstracts the products as atoms)
  omega

/-- `pi.approx (n+1)` has `den ≤ num` (value `≥ 1`, indeed `≥ 3`). -/
theorem pi_approx_succ_den_le_num (n : Nat) :
    ((pi.approx (n + 1)).den : Int) ≤ (pi.approx (n + 1)).num := by
  have h3 : (3 : Q') ≤ pi.approx (n + 1) :=
    three_le_pi_approx (Nat.succ_le_succ (Nat.zero_le n))
  have hle' : (3 : Int) * ((pi.approx (n + 1)).den : Int) ≤ (pi.approx (n + 1)).num := by
    have hh : (3 : Q').num * ((pi.approx (n + 1)).den : Int)
        ≤ (pi.approx (n + 1)).num * ((3 : Q').den : Int) := h3
    have e1 : (3 : Q').num = 3 := rfl
    have e2 : ((3 : Q').den : Int) = 1 := rfl
    rw [e1, e2, Int.mul_one] at hh
    exact hh
  have hden_nn : (0 : Int) ≤ ((pi.approx (n + 1)).den : Int) := Int.natCast_nonneg _
  -- den ≤ 3·den ≤ num
  have hd3 : ((pi.approx (n + 1)).den : Int) ≤ (3 : Int) * ((pi.approx (n + 1)).den : Int) := by
    omega
  exact Int.le_trans hd3 hle'

/-- The approximation sequence of `2/π`. -/
def twoOverPiSeq (n : Nat) : Q' :=
  (2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)

/-- The genuine Cauchy modulus for `2/π`, transported through `pi.cauchy` at
tolerance `δ = (1/2)·ε`, then scaled by `2`.  Uses the reciprocal Lipschitz
bound `recipDir` (valid since `pi.approx (k+1) ≥ 1`). -/
theorem twoOverPi_cauchy : ∀ ε : Q', 0 < ε → ∃ N : Nat,
    ∀ m n : Nat, N ≤ m → N ≤ n →
      twoOverPiSeq m ≤ twoOverPiSeq n + ε ∧ twoOverPiSeq n ≤ twoOverPiSeq m + ε := by
  intro ε hε
  have hδpos : (0 : Q') < HalfPow.half * ε := by
    -- 1/2 > 0 and ε > 0 ⟹ product > 0
    show (0 : Q').num * ((HalfPow.half * ε).den : Int)
        < (HalfPow.half * ε).num * ((0 : Q').den : Int)
    show (0 : Int) * ((HalfPow.half * ε).den : Int)
        < (HalfPow.half * ε).num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    -- (half*ε).num = 1 * ε.num = ε.num ; half.num = 1
    have hnum : (HalfPow.half * ε).num = (1 : Int) * ε.num := by
      show HalfPow.half.num * ε.num = (1 : Int) * ε.num
      have : HalfPow.half.num = 1 := Q'.mkPos_num 1 2 (by decide)
      rw [this]
    rw [hnum, Int.one_mul]
    have hεnum : (0 : Int) < ε.num := CReal.num_pos_of_pos hε
    exact hεnum
  have hδ0 : (0 : Q') ≤ HalfPow.half * ε := Q'.le_of_lt hδpos
  obtain ⟨N, hN⟩ := pi.cauchy (HalfPow.half * ε) hδpos
  refine ⟨N, fun m n hm hn => ?_⟩
  -- directional reciprocal bound
  have dir : ∀ p q : Nat, N ≤ p → N ≤ q →
      twoOverPiSeq p ≤ twoOverPiSeq q + ε := by
    intro p q hp hq
    -- need recip(pi(p+1)) ≤ recip(pi(q+1)) + δ
    have hpc := hN (p + 1) (q + 1) (Nat.le_succ_of_le hp) (Nat.le_succ_of_le hq)
    -- hpc.2 : pi.approx (q+1) ≤ pi.approx (p+1) + δ
    have hrecip : recipPosNum (pi.approx (p + 1)) (pi_approx_succ_num_pos p)
        ≤ recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q) + HalfPow.half * ε :=
      recipDir (pi_approx_succ_num_pos p) (pi_approx_succ_num_pos q)
        (pi_approx_succ_den_le_num p) (pi_approx_succ_den_le_num q) hδ0 hpc.2
    -- scale by 2 :  2·recip_p ≤ 2·(recip_q + δ) = 2·recip_q + 2δ
    have hscale : (2 : Q') * recipPosNum (pi.approx (p + 1)) (pi_approx_succ_num_pos p)
        ≤ (2 : Q') * (recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q)
            + HalfPow.half * ε) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hrecip (by decide)
    -- 2·(recip_q + δ) ≃ 2·recip_q + 2·δ  and  2·δ ≃ ε
    have hdistrib : ((2 : Q') * (recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q)
          + HalfPow.half * ε)).eqv
        ((2 : Q') * recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q)
          + (2 : Q') * (HalfPow.half * ε)) :=
      Q'.mul_add_eqv _ _ _
    have h2δ : ((2 : Q') * (HalfPow.half * ε)).eqv ε := by
      -- 2 · (half · ε) ≃ (2·half)·ε ≃ 1·ε ≃ ε
      have a1 : ((2 : Q') * (HalfPow.half * ε)).eqv (((2 : Q') * HalfPow.half) * ε) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      have a2 : (((2 : Q') * HalfPow.half) * ε).eqv ((1 : Q') * ε) := by
        have hh : ((2 : Q') * HalfPow.half).eqv (1 : Q') := by decide
        exact Q'.mul_eqv_congr_right _ _ _ hh
      have a3 : ((1 : Q') * ε).eqv ε := Q'.one_mul_eqv ε
      exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 a3)
    -- combine: 2·recip_q + 2δ ≃ 2·recip_q + ε
    have hfin : ((2 : Q') * recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q)
          + (2 : Q') * (HalfPow.half * ε))
        ≤ (2 : Q') * recipPosNum (pi.approx (q + 1)) (pi_approx_succ_num_pos q) + ε :=
      Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ h2δ)
    -- chain everything
    show twoOverPiSeq p ≤ twoOverPiSeq q + ε
    exact Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdistrib) hfin)
  exact ⟨dir m n hm hn, dir n m hn hm⟩

/-- `2 / π` as a constructive real:  `approx n = 2 · (1 / pi.approx (n+1))`.

The Cauchy modulus is genuine and transported through `pi.cauchy`: since
`pi.approx (n+1) ≥ 3`, the reciprocal is `1`-Lipschitz up to the factor
`1/9 < 1`, so `pi`'s own modulus serves (we use it at tolerance `ε`).  The
Lipschitz bound `recipDir` is proved below as a pure-`Q'` cross-product fact. -/
def twoOverPi : CReal where
  approx := twoOverPiSeq
  cauchy := twoOverPi_cauchy

theorem twoOverPi_approx (n : Nat) : twoOverPi.approx n = twoOverPiSeq n := rfl

/-- `recipPosNum (pi.approx (n+1)) ≥ 1/4` (since `pi.approx (n+1) ≤ 4`,
so `num ≤ 4·den`). -/
theorem recip_pi_succ_ge_quarter (n : Nat) :
    Q'.mkPos 1 4 (by decide)
      ≤ recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n) := by
  -- num ≤ 4·den from pi.approx (n+1) ≤ 4
  have h4 : pi.approx (n + 1) ≤ (4 : Q') := pi_approx_le_four (n + 1)
  have hnum4 : (pi.approx (n + 1)).num ≤ (4 : Int) * ((pi.approx (n + 1)).den : Int) := by
    have hh : (pi.approx (n + 1)).num * ((4 : Q').den : Int)
        ≤ (4 : Q').num * ((pi.approx (n + 1)).den : Int) := h4
    have e1 : ((4 : Q').den : Int) = 1 := rfl
    have e2 : (4 : Q').num = 4 := rfl
    rw [e1, e2, Int.mul_one] at hh
    exact hh
  -- cross-product of (1/4) ≤ recip = den/num
  show (Q'.mkPos 1 4 (by decide)).num
        * ((recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)).den : Int)
      ≤ (recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)).num
        * ((Q'.mkPos 1 4 (by decide)).den : Int)
  rw [recipPosNum_num, recipPosNum_den, Q'.mkPos_num, Q'.mkPos_den]
  have hAt : (((pi.approx (n + 1)).num.toNat : Nat) : Int) = (pi.approx (n + 1)).num :=
    Int.toNat_of_nonneg (Int.le_of_lt (pi_approx_succ_num_pos n))
  rw [hAt]
  -- goal: 1 * num ≤ den * 4
  show (1 : Int) * (pi.approx (n + 1)).num ≤ ((pi.approx (n + 1)).den : Int) * (4 : Int)
  rw [Int.one_mul]
  -- num ≤ 4·den = den·4
  have : (4 : Int) * ((pi.approx (n + 1)).den : Int)
      = ((pi.approx (n + 1)).den : Int) * (4 : Int) := Int.mul_comm _ _
  rw [← this]
  exact hnum4

/-- `1/2 ≤ twoOverPiSeq n` for all `n`. -/
theorem half_le_twoOverPiSeq (n : Nat) :
    Q'.mkPos 1 2 (by decide) ≤ twoOverPiSeq n := by
  show Q'.mkPos 1 2 (by decide)
      ≤ (2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)
  -- 2·(1/4) = 1/2 ≤ 2·recip
  have hq := recip_pi_succ_ge_quarter n
  have hmul : (2 : Q') * Q'.mkPos 1 4 (by decide)
      ≤ (2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hq (by decide)
  have hhalf : Q'.mkPos 1 2 (by decide) ≤ (2 : Q') * Q'.mkPos 1 4 (by decide) := by decide
  exact Q'.le_trans' _ _ _ hhalf hmul

/-- **`2/π` is positive** (`IsPositive`), witness `ε = 1/2`. -/
theorem twoOverPi_pos : CReal.IsPositive twoOverPi :=
  CReal.isPositive_of_approx_ge (ε := Q'.mkPos 1 2 (by decide)) (by decide)
    (fun n => half_le_twoOverPiSeq n)

/-! ### The reciprocal law `(2/π)·π ≃ 2`

The product `twoOverPi · pi` converges to `2`.  The exact algebraic fact is
`twoOverPiSeq n · pi.approx (n+1) ≃ 2` (the reciprocal cancels at the SHIFTED
index `n+1`); the only error against `2` at index `n` comes from the index shift
`pi.approx n` vs `pi.approx (n+1)`, which `pi.cauchy` drives to `0`.  We bound
`twoOverPiSeq n ∈ [0, 2]` and combine. -/

/-- `recipPosNum q h · q ≃ 1`:  `(den/num)·(num/den) ≃ 1`. -/
theorem recipPosNum_mul_self_eqv_one (q : Q') (h : 0 < q.num) :
    (recipPosNum q h * q).eqv (1 : Q') := by
  have hAt : ((q.num.toNat : Nat) : Int) = q.num := Int.toNat_of_nonneg (Int.le_of_lt h)
  show (recipPosNum q h * q).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((recipPosNum q h * q).den : Int)
  -- (recip*q).num = (recip).num * q.num = q.den * q.num  (definitional + recipPosNum_num)
  have hnum : (recipPosNum q h * q).num = (q.den : Int) * q.num := by
    show (recipPosNum q h).num * q.num = (q.den : Int) * q.num
    rw [recipPosNum_num]
  have hden : ((recipPosNum q h * q).den : Int)
      = ((q.num.toNat : Nat) : Int) * (q.den : Int) := by
    rw [Q'.mul_den_cast, recipPosNum_den]
  rw [hnum, hden, hAt]
  show ((q.den : Int) * q.num) * ((1 : Q').den : Int)
      = (1 : Q').num * (q.num * (q.den : Int))
  show ((q.den : Int) * q.num) * (1 : Int) = (1 : Int) * (q.num * (q.den : Int))
  rw [Int.mul_one, Int.one_mul, Int.mul_comm (q.den : Int) q.num]

/-- The exact cancellation:  `twoOverPiSeq n · pi.approx (n+1) ≃ 2`. -/
theorem twoOverPiSeq_mul_piApprox_succ_eqv_two (n : Nat) :
    (twoOverPiSeq n * pi.approx (n + 1)).eqv (2 : Q') := by
  show ((2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)
        * pi.approx (n + 1)).eqv (2 : Q')
  -- 2·recip·q ≃ 2·(recip·q) ≃ 2·1 ≃ 2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (2 : Q')
      (recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)) (pi.approx (n + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (2 : Q')
      (recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n) * pi.approx (n + 1))
      (1 : Q')
      (recipPosNum_mul_self_eqv_one (pi.approx (n + 1)) (pi_approx_succ_num_pos n))) ?_
  -- 2·1 ≃ 2
  exact Q'.mul_one_eqv (2 : Q')

/-- `twoOverPiSeq n ≤ 2` (loose upper bound; `2/π < 2/3 < 2`). -/
theorem twoOverPiSeq_le_two (n : Nat) : twoOverPiSeq n ≤ (2 : Q') := by
  show (2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n) ≤ (2 : Q')
  -- recip ≤ 1/3 ≤ 1  (pi ≥ 3 ⟹ recip ≤ 1/3); we only need recip ≤ 1, then 2·1 = 2.
  -- recip = den/num ≤ 1 since den ≤ num (pi ≥ 1).
  have hrec_le_one : recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n) ≤ (1 : Q') := by
    show (recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)).num
          * ((1 : Q').den : Int)
        ≤ (1 : Q').num
          * ((recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)).den : Int)
    rw [recipPosNum_num, recipPosNum_den]
    have hAt : (((pi.approx (n + 1)).num.toNat : Nat) : Int) = (pi.approx (n + 1)).num :=
      Int.toNat_of_nonneg (Int.le_of_lt (pi_approx_succ_num_pos n))
    rw [hAt]
    show ((pi.approx (n + 1)).den : Int) * (1 : Int)
        ≤ (1 : Int) * (pi.approx (n + 1)).num
    rw [Int.mul_one, Int.one_mul]
    exact pi_approx_succ_den_le_num n
  have hmul : (2 : Q') * recipPosNum (pi.approx (n + 1)) (pi_approx_succ_num_pos n)
      ≤ (2 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrec_le_one (by decide)
  exact Q'.le_trans' _ _ _ hmul (by decide)

/-- `0 ≤ twoOverPiSeq n`. -/
theorem zero_le_twoOverPiSeq (n : Nat) : (0 : Q') ≤ twoOverPiSeq n :=
  Q'.le_trans' _ _ _ (by decide) (half_le_twoOverPiSeq n)

/-- **The reciprocal law.**  `(2/π)·π ≃ 2` as constructive reals. -/
theorem twoOverPi_mul_pi : CReal.Equiv (CReal.mul twoOverPi pi) (CReal.ofQ' (2 : Q')) := by
  intro ε hε
  -- δ = (1/2)·ε ;  pi.cauchy at δ gives the index-shift bound.
  have hδpos : (0 : Q') < HalfPow.half * ε := by
    show (0 : Q').num * ((HalfPow.half * ε).den : Int)
        < (HalfPow.half * ε).num * ((0 : Q').den : Int)
    show (0 : Int) * ((HalfPow.half * ε).den : Int) < (HalfPow.half * ε).num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one]
    have hnum : (HalfPow.half * ε).num = (1 : Int) * ε.num := by
      show HalfPow.half.num * ε.num = (1 : Int) * ε.num
      have hh : HalfPow.half.num = 1 := Q'.mkPos_num 1 2 (by decide)
      rw [hh]
    rw [hnum, Int.one_mul]
    exact CReal.num_pos_of_pos hε
  have hδ0 : (0 : Q') ≤ HalfPow.half * ε := Q'.le_of_lt hδpos
  obtain ⟨N, hN⟩ := pi.cauchy (HalfPow.half * ε) hδpos
  refine ⟨N, fun n hn => ?_⟩
  -- product approx
  have hprodapprox : (CReal.mul twoOverPi pi).approx n = twoOverPiSeq n * pi.approx n := rfl
  -- |pi.approx n − pi.approx (n+1)| ≤ δ  (both indices ≥ N)
  have hshift := hN n (n + 1) hn (Nat.le_succ_of_le hn)
  -- bound the error E := twoOverPiSeq n · pi.approx n − 2  via the shifted identity.
  -- twoOverPiSeq n · pi.approx n  vs  twoOverPiSeq n · pi.approx (n+1) ≃ 2.
  -- direction 1:  twoOverPiSeq n · pi.approx n ≤ 2 + ε
  --   = twoOverPiSeq n·pi.approx(n+1) + twoOverPiSeq n·(pi.approx n − pi.approx(n+1))
  --   ≤ 2 + 2·δ = 2 + ε.
  -- We use that twoOverPiSeq n ∈ [0,2] and the two-sided shift bound.
  have hb := zero_le_twoOverPiSeq n
  have hub := twoOverPiSeq_le_two n
  -- shift bound as two ≤'s
  -- hshift.1 : pi.approx n ≤ pi.approx (n+1) + δ
  -- hshift.2 : pi.approx (n+1) ≤ pi.approx n + δ
  -- Multiply by twoOverPiSeq n ≥ 0:
  have hm1 : twoOverPiSeq n * pi.approx n
      ≤ twoOverPiSeq n * (pi.approx (n + 1) + HalfPow.half * ε) := by
    have := Q'.mul_le_mul_of_nonneg_left (pi.approx n)
      (pi.approx (n + 1) + HalfPow.half * ε) (twoOverPiSeq n) hshift.1 hb
    exact this
  have hm2 : twoOverPiSeq n * pi.approx (n + 1)
      ≤ twoOverPiSeq n * (pi.approx n + HalfPow.half * ε) := by
    exact Q'.mul_le_mul_of_nonneg_left (pi.approx (n + 1))
      (pi.approx n + HalfPow.half * ε) (twoOverPiSeq n) hshift.2 hb
  -- distribute:  twoOverPiSeq n·(x + δ) ≃ twoOverPiSeq n·x + twoOverPiSeq n·δ,
  -- and twoOverPiSeq n·δ ≤ 2·δ ≤ ... we want ≤ ε; use 2·(half·ε) ≃ ε.
  have hδmul_le : twoOverPiSeq n * (HalfPow.half * ε) ≤ ε := by
    -- twoOverPiSeq n · δ ≤ 2 · δ ≃ ε
    have hle2 : twoOverPiSeq n * (HalfPow.half * ε) ≤ (2 : Q') * (HalfPow.half * ε) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hub hδ0
    have heq : ((2 : Q') * (HalfPow.half * ε)).eqv ε := by
      have a1 : ((2 : Q') * (HalfPow.half * ε)).eqv (((2 : Q') * HalfPow.half) * ε) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
      have a2 : (((2 : Q') * HalfPow.half) * ε).eqv ((1 : Q') * ε) :=
        Q'.mul_eqv_congr_right _ _ _ (by decide)
      exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 (Q'.one_mul_eqv ε))
    exact Q'.le_trans' _ _ _ hle2 (Q'.le_of_eqv heq)
  -- 2 ≃ twoOverPiSeq n · pi.approx (n+1)
  have hcancel : (twoOverPiSeq n * pi.approx (n + 1)).eqv (2 : Q') :=
    twoOverPiSeq_mul_piApprox_succ_eqv_two n
  rw [hprodapprox]
  show twoOverPiSeq n * pi.approx n ≤ (CReal.ofQ' (2 : Q')).approx n + ε
      ∧ (CReal.ofQ' (2 : Q')).approx n ≤ twoOverPiSeq n * pi.approx n + ε
  rw [CReal.ofQ'_approx]
  constructor
  · -- twoOverPiSeq n·pi.approx n ≤ 2 + ε
    -- ≤ twoOverPiSeq n·(pi.approx(n+1)+δ) = twoOverPiSeq n·pi.approx(n+1) + twoOverPiSeq n·δ
    --   ≃ 2 + (≤ε)
    refine Q'.le_trans' _ _ _ hm1 ?_
    have hdist : (twoOverPiSeq n * (pi.approx (n + 1) + HalfPow.half * ε)).eqv
        (twoOverPiSeq n * pi.approx (n + 1) + twoOverPiSeq n * (HalfPow.half * ε)) :=
      Q'.mul_add_eqv _ _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
    -- twoOverPiSeq n·pi.approx(n+1) + twoOverPiSeq n·δ ≤ 2 + ε
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv hcancel)) ?_
    exact Q'.add_le_add_left (2 : Q') _ ε hδmul_le
  · -- 2 ≤ twoOverPiSeq n·pi.approx n + ε
    -- 2 ≃ twoOverPiSeq n·pi.approx(n+1) ≤ twoOverPiSeq n·(pi.approx n + δ)
    --   = twoOverPiSeq n·pi.approx n + twoOverPiSeq n·δ ≤ twoOverPiSeq n·pi.approx n + ε
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) ?_
    refine Q'.le_trans' _ _ _ hm2 ?_
    have hdist : (twoOverPiSeq n * (pi.approx n + HalfPow.half * ε)).eqv
        (twoOverPiSeq n * pi.approx n + twoOverPiSeq n * (HalfPow.half * ε)) :=
      Q'.mul_add_eqv _ _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
    exact Q'.add_le_add_left _ _ ε hδmul_le

end ConstructiveReals.Pi

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.Pi.arctanRecip
#print axioms ConstructiveReals.Pi.pi
#print axioms ConstructiveReals.Pi.pi_pos
#print axioms ConstructiveReals.Pi.pi_geRat_three
#print axioms ConstructiveReals.Pi.pi_leRat_four
#print axioms ConstructiveReals.Pi.halfPi_pos
#print axioms ConstructiveReals.Pi.twoOverPi
#print axioms ConstructiveReals.Pi.twoOverPi_pos
#print axioms ConstructiveReals.Pi.recipPosNum_mul_self_eqv_one
#print axioms ConstructiveReals.Pi.twoOverPiSeq_mul_piApprox_succ_eqv_two
#print axioms ConstructiveReals.Pi.twoOverPi_mul_pi
#print axioms ConstructiveReals.Pi.twoOverPi_pos
#print axioms ConstructiveReals.Pi.recipDir
#print axioms ConstructiveReals.Pi.twoOverPi_cauchy
