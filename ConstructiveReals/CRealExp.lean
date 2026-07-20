/-
# `CReal.expNegC` — the constructive exponential on a **CReal** argument

`ExpNeg.expNeg : (x : Q') → 0 ≤ x → CReal` gives `e^{−x}` for a RATIONAL exponent.
Iterated-root flows of the form `sep_k = exp(log R /(b+1)^k)` need `e^{−w}` for
a **CReal** exponent `w` (irrational).  This module builds that: `expNegC w` is the
constructive limit `lim_k expNeg (w.approx k)`, assembled with the completion
backbone `CReal.completeLimit` (`CRealComplete`).

A general `CReal`'s Cauchy modulus is a `Prop` `∃` (no `Type`-level data, so no
`Classical`-free extraction), so `expNegC` takes the argument's modulus `Mw` as
explicit `Type`-level data — exactly the discipline `ModCauchy` already enforces.

The keystone analytic input is the **limit-level Lipschitz bound**
`e^{−a} − e^{−b} ≤ b − a` (`expNeg` is a contraction on `[0,∞)`), which factors
through the convexity bound `1 − e^{−t} ≤ t` (`oneSub_le_expNeg`) and
`e^{−a} ≤ 1`.  This file first lands the missing `CReal` left-distributivity that
the contraction proof needs (the pointwise ring law `mul` lacked), then the bounds.

# Axiom-gate (see README: axiom policy)

`[propext]` (and `Quot.sound` where `Nat`/`Int` helpers enter).  No `Classical.*`,
no `native_decide`, no `sorry`.  Moduli are `Type`-level data.
-/

import ConstructiveReals.CRealComplete
import ConstructiveReals.CRealCompleteCauchy
import ConstructiveReals.Sqrt
import ConstructiveReals.QPoly
import ConstructiveReals.CRealAlg
import ConstructiveReals.CRealMulLe
import ConstructiveReals.ExpAdd
import ConstructiveReals.ExpNegCongr
import ConstructiveReals.Soundness
import ConstructiveReals.CauchyConv

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.CReal

namespace CReal

/-! ## 1. `CReal` left-distributivity (the missing pointwise ring law)

`CReal.mul`, `CReal.add`, `CReal.neg` all act approx-wise, so left-distributivity
of `mul` over `add`/`sub` reduces to the `Q'` identity at each approximation index
via `SumOfSquares.Equiv_of_approx_eqv` — the same technique `CRealAlg` uses for
associativity/commutativity. -/

/-- **Left-distributivity over `add`** (pointwise): `x·(y + z) ≃ x·y + x·z`. -/
theorem mul_add (x y z : CReal) :
    CReal.Equiv (CReal.mul x (CReal.add y z))
      (CReal.add (CReal.mul x y) (CReal.mul x z)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.mul_add_eqv (x.approx n) (y.approx n) (z.approx n))

/-- **Left-distributivity over `sub`** (pointwise): `x·(y − z) ≃ x·y − x·z`. -/
theorem mul_sub (x y z : CReal) :
    CReal.Equiv (CReal.mul x (CReal.sub y z))
      (CReal.sub (CReal.mul x y) (CReal.mul x z)) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  -- (sub y z).approx n = y.approx n + -(z.approx n);  goal at Q' level:
  --   x·(y + -z) ≃ x·y + -(x·z)
  show (x.approx n * (y.approx n + -(z.approx n))).eqv
    (x.approx n * y.approx n + -(x.approx n * z.approx n))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (x.approx n) (y.approx n) (-(z.approx n))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv (x.approx n) (z.approx n))

end CReal

/-! ## 2. Sign structure of the `e^{−x}` series terms

For `x ≥ 0` the series `e^{−x} = ∑ (−x)^k/k!` is alternating: even-index terms are
`≥ 0`, odd-index terms are `≤ 0`.  Proved by a single joint induction on the pair
`(term (2m) ≥ 0, term (2m+1) ≤ 0)` from the sign of the recurrence factor
`(−x)·1/(k+1) ≤ 0`.  Feeds the alternating-series lower bound `e^{−x} ≥ 1−x`. -/

namespace Q'

/-- `a ≤ 0 → 0 ≤ -a`. -/
theorem nonneg_neg_of_nonpos {a : Q'} (h : a ≤ (0 : Q')) : (0 : Q') ≤ -a :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q').eqv (-(0 : Q')))) (Q'.neg_le_neg h)

/-- `0 ≤ -a → a ≤ 0`. -/
theorem nonpos_of_neg_nonneg {a : Q'} (h : (0 : Q') ≤ -a) : a ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_neg_eqv a)))
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0)))

/-- `0 ≤ a → -a ≤ 0`. -/
theorem nonpos_neg_of_nonneg {a : Q'} (h : (0 : Q') ≤ a) : -a ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (Q'.le_of_eqv (by decide : (-(0 : Q')).eqv 0))

/-- Product of two nonpositives is nonnegative: `a,b ≤ 0 → 0 ≤ a·b`. -/
theorem mul_nonneg_of_nonpos_nonpos {a b : Q'} (ha : a ≤ (0 : Q')) (hb : b ≤ (0 : Q')) :
    (0 : Q') ≤ a * b := by
  have h := Q'.mul_nonneg (-a) (-b) (nonneg_neg_of_nonpos ha) (nonneg_neg_of_nonpos hb)
  -- (−a)·(−b) ≃ −(a·(−b)) ≃ −(−(a·b)) ≃ a·b
  refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) ?_
  exact Q'.neg_neg_eqv (a * b)

/-- Product of a nonnegative and a nonpositive is nonpositive: `0 ≤ a, b ≤ 0 → a·b ≤ 0`. -/
theorem mul_nonpos_of_nonneg_nonpos {a b : Q'} (ha : (0 : Q') ≤ a) (hb : b ≤ (0 : Q')) :
    a * b ≤ (0 : Q') := by
  have h : (0 : Q') ≤ a * (-b) := Q'.mul_nonneg a (-b) ha (nonneg_neg_of_nonpos hb)
  -- a·(−b) ≃ −(a·b), so 0 ≤ −(a·b), hence a·b ≤ 0
  exact nonpos_of_neg_nonneg (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_neg_eqv a b)))

end Q'

namespace ExpNeg

/-- The recurrence factor `(−x)·1/(k+1)` is nonpositive for `x ≥ 0`. -/
theorem recFactor_nonpos {x : Q'} (hx : (0 : Q') ≤ x) (k : Nat) :
    (-x) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _) ≤ (0 : Q') := by
  have hm : (0 : Q') ≤ Q'.mkPos 1 (k + 1) (Nat.succ_pos _) := Q'.invSucc_nonneg k
  have hxm : (0 : Q') ≤ x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _) := Q'.mul_nonneg x _ hx hm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_mul_eqv x _)) (Q'.nonpos_neg_of_nonneg hxm)

/-- **Alternating sign of the `e^{−x}` series terms.**  For `x ≥ 0`, even-index
terms are `≥ 0` and odd-index terms are `≤ 0`.  Joint induction on `m`. -/
theorem term_sign {x : Q'} (hx : (0 : Q') ≤ x) :
    ∀ m, (0 : Q') ≤ term x (2 * m) ∧ term x (2 * m + 1) ≤ (0 : Q')
  | 0 => by
      refine ⟨?_, ?_⟩
      · show (0 : Q') ≤ term x 0; rw [term_zero]; decide
      · show term x 1 ≤ (0 : Q')
        rw [term_succ, term_zero]
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (recFactor_nonpos hx 0)
  | m + 1 => by
      obtain ⟨_, hodd⟩ := term_sign hx m
      have e1 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      have e2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by omega
      have hev2 : (0 : Q') ≤ term x (2 * m + 1 + 1) := by
        rw [term_succ]
        exact Q'.mul_nonneg_of_nonpos_nonpos hodd (recFactor_nonpos hx _)
      refine ⟨?_, ?_⟩
      · rw [e1]; exact hev2
      · rw [e2, term_succ]
        exact Q'.mul_nonpos_of_nonneg_nonpos hev2 (recFactor_nonpos hx _)

/-- **`expNeg`'s explicit Cauchy modulus** (exposed as a standalone lemma, so the
modulus is `Type`-level data the completion can consume — a general `CReal`'s
`.cauchy` is a `Prop` `∃`).  `Mexp x ε := max (RatNat.halfRatioCutoff x) (termAbsModulus x
(½ε))`; for `m, n ≥ Mexp x ε` the partial sums agree to within `ε`.  This is
exactly the body of `expNeg`'s own `cauchy` field. -/
def Mexp (x ε : Q') : Nat := max (RatNat.halfRatioCutoff x) (termAbsModulus x (HalfPow.half * ε))

theorem expNeg_cauchy_explicit (x : Q') (hx : (0 : Q') ≤ x) (ε : Q') (hε : (0 : Q') < ε) :
    ∀ m n, Mexp x ε ≤ m → Mexp x ε ≤ n →
      partialSum x m ≤ partialSum x n + ε ∧ partialSum x n ≤ partialSum x m + ε := by
  intro m n hm hn
  have hhε : (0 : Q') < HalfPow.half * ε := half_mul_pos ε hε
  have dir : ∀ k l : Nat, Mexp x ε ≤ k → k ≤ l →
      partialSum x l ≤ partialSum x k + ε ∧ partialSum x k ≤ partialSum x l + ε := by
    intro k l hk hkl
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have hcut : RatNat.halfRatioCutoff x ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
    have hterm : termAbs x k ≤ HalfPow.half * ε :=
      termAbs_le_of_modulus_le x (HalfPow.half * ε) hx hhε k
        (Nat.le_trans (Nat.le_max_right _ _) hk)
    have htail : blockAbs x k d ≤ ε :=
      expNeg_tail_bound x hx ε (Q'.le_of_lt hε) k hcut hterm d
    exact ⟨Q'.le_trans' _ _ _ (block_upper x hx k d)
             (Q'.add_le_add_left (partialSum x k) (blockAbs x k d) ε htail),
           Q'.le_trans' _ _ _ (block_lower x hx k d)
             (Q'.add_le_add_left (partialSum x (k + d)) (blockAbs x k d) ε htail)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
  · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-! ### 2b. Telescoping identity and `termAbs` base-monotonicity (for the
partial-sum Lipschitz, §5b)

`invSucc (k+1)·(invSucc k + 1) ≃ invSucc k` is the exact cancellation that makes
the per-term Lipschitz bound `δ_{k+1} ≤ d·termAbs 1 k` telescope without blow-up.
It follows from the reciprocal identity `ofNat (k+1)·invSucc k ≃ 1`
(`CauchyConv.ofNat_succ_mul_invSucc`). -/

/-- `1 + ofNat (n+1) ≃ ofNat (n+2)`. -/
theorem one_add_ofNat_succ (n : Nat) :
    ((1 : Q') + Q'.ofNat (n + 1)).eqv (Q'.ofNat (n + 2)) := by
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (n + 1) 1) ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat (n + 1)) (Q'.ofNat 1) 1 (by decide)) ?_
  exact Q'.add_comm_eqv (Q'.ofNat (n + 1)) 1

/-- **The telescoping cancellation.** -/
theorem invSucc_cancel (k : Nat) :
    (Q'.invSucc (k + 1) * (Q'.invSucc k + 1)).eqv (Q'.invSucc k) := by
  have h1 : ((Q'.ofNat (k + 1)) * Q'.invSucc k).eqv 1 :=
    Q'.ofNat_succ_mul_invSucc k
  have h2 : ((Q'.ofNat (k + 2)) * Q'.invSucc (k + 1)).eqv 1 :=
    Q'.ofNat_succ_mul_invSucc (k + 1)
  -- hA : invSucc k + 1 ≃ ofNat (k+2) · invSucc k
  have hA : (Q'.invSucc k + 1).eqv ((Q'.ofNat (k + 2)) * Q'.invSucc k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.invSucc k) 1 ((Q'.ofNat (k + 1)) * Q'.invSucc k)
        (Q'.eqv_symm h1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (Q'.invSucc k) (1 * Q'.invSucc k)
        ((Q'.ofNat (k + 1)) * Q'.invSucc k) (Q'.eqv_symm (Q'.one_mul_eqv _))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv 1 (Q'.ofNat (k + 1)) (Q'.invSucc k))) ?_
    exact Q'.mul_eqv_congr_right _ _ (Q'.invSucc k) (one_add_ofNat_succ k)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hA) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.invSucc (k + 1)) (Q'.ofNat (k + 2)) (Q'.invSucc k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.invSucc k)
      (Q'.mul_comm_eqv (Q'.invSucc (k + 1)) (Q'.ofNat (k + 2)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (Q'.invSucc k) h2) ?_
  exact Q'.one_mul_eqv (Q'.invSucc k)

/-- Two-sided `add` congruence (composed from the one-sided `Q'` versions). -/
theorem add_eqv_congr2 {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha) (Q'.add_eqv_congr_left a' b b' hb)

/-- Two-sided `≤` addition. -/
theorem add_le_add2 {a b c e : Q'} (h1 : a ≤ b) (h2 : c ≤ e) : a + c ≤ b + e :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c e h2)

/-- `0 ≤ ofNat k`. -/
theorem ofNat_nonneg' : ∀ k : Nat, (0 : Q') ≤ Q'.ofNat k
  | 0 => Q'.le_of_eqv (Q'.eqv_symm (by decide : (Q'.ofNat 0).eqv 0))
  | k + 1 =>
      Q'.le_trans' _ _ _
        (Q'.zero_le_add _ _ (ofNat_nonneg' k) (by decide : (0 : Q') ≤ Q'.ofNat 1))
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.ofNat_add_eqv k 1)))

/-- `-(abs q) ≤ q`. -/
theorem neg_abs_le (q : Q') : -(Q'.abs q) ≤ q :=
  Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs q))
    (Q'.le_of_eqv (Q'.neg_neg_eqv q))

/-- `abs c = c` for `c ≥ 0`. -/
theorem abs_of_nonneg {c : Q'} (hc : (0 : Q') ≤ c) : Q'.abs c = c := if_pos hc

/-- `.eqv` from `≤` both ways (antisymmetry, at the `Int` cross-product level). -/
theorem eqv_of_le_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a.eqv b :=
  Int.le_antisymm h1 h2

/-- `abs` respects `.eqv`. -/
theorem abs_eqv_congr {p q : Q'} (h : p.eqv q) : (Q'.abs p).eqv (Q'.abs q) := by
  refine eqv_of_le_le ?_ ?_
  · refine Q'.abs_le (Q'.le_trans' _ _ _ (neg_abs_le q) (Q'.ge_of_eqv h)) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.le_abs_self q)
  · refine Q'.abs_le (Q'.le_trans' _ _ _ (neg_abs_le p) (Q'.le_of_eqv h)) ?_
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.le_abs_self p)

/-- `abs (u·v) ≤ abs u · abs v`. -/
theorem abs_mul_le (u v : Q') : Q'.abs (u * v) ≤ Q'.abs u * Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · -- −(|u|·|v|) ≤ u·v :  −(u·v) = (−u)·v ≤ |u|·|v|
    have h : (-u) * v ≤ Q'.abs u * Q'.abs v :=
      Q'.mul_le_of_bounds (Q'.abs_nonneg u) (Q'.abs_nonneg v)
        (Q'.neg_le_neg (Q'.le_abs_self u)) (Q'.neg_le_abs u)
        (neg_abs_le v) (Q'.le_abs_self v)
    have h' : -(u * v) ≤ Q'.abs u * Q'.abs v :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_mul_eqv u v)) h
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg h')
      (Q'.le_of_eqv (Q'.neg_neg_eqv (u * v)))
  · exact Q'.mul_le_of_bounds (Q'.abs_nonneg u) (Q'.abs_nonneg v)
      (neg_abs_le u) (Q'.le_abs_self u) (neg_abs_le v) (Q'.le_abs_self v)

/-- `abs (u+v) ≤ abs u + abs v`. -/
theorem abs_add_le (u v : Q') : Q'.abs (u + v) ≤ Q'.abs u + Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · have h : (-(Q'.abs u)) + (-(Q'.abs v)) ≤ u + v :=
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right (-(Q'.abs u)) u (-(Q'.abs v)) (neg_abs_le u))
        (Q'.add_le_add_left u (-(Q'.abs v)) v (neg_abs_le v))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_add_eqv (Q'.abs u) (Q'.abs v))) h
  · exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (Q'.le_abs_self u))
      (Q'.add_le_add_left _ _ _ (Q'.le_abs_self v))

/-- **`termAbs` is monotone in the base** for sub-unit bases: `termAbs b k ≤
termAbs 1 k` when `0 ≤ b ≤ 1`. -/
theorem termAbs_base_mono {b : Q'} (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ (1 : Q')) :
    ∀ k, termAbs b k ≤ termAbs 1 k
  | 0 => by
      show termAbs b 0 ≤ termAbs 1 0
      rw [termAbs_zero, termAbs_zero]; exact Q'.le_refl' 1
  | k + 1 => by
      show termAbs b k * (b * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
        ≤ termAbs 1 k * (1 * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
      have hm : (0 : Q') ≤ Q'.mkPos 1 (k + 1) (Nat.succ_pos _) := Q'.invSucc_nonneg k
      have hbm : (0 : Q') ≤ b * Q'.mkPos 1 (k + 1) (Nat.succ_pos _) := Q'.mul_nonneg b _ hb0 hm
      have hstep1 : termAbs b k * (b * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
          ≤ termAbs 1 k * (b * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (termAbs_base_mono hb0 hb1 k) hbm
      have hbm1 : b * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)
          ≤ 1 * Q'.mkPos 1 (k + 1) (Nat.succ_pos _) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hb1 hm
      have ht1 : (0 : Q') ≤ termAbs 1 k := termAbs_nonneg 1 (by decide) k
      exact Q'.le_trans' _ _ _ hstep1 (Q'.mul_le_mul_of_nonneg_left _ _ _ hbm1 ht1)

/-- `1 + ofNat k ≃ ofNat (k+1)`. -/
theorem one_add_ofNat (k : Nat) : ((1 : Q') + Q'.ofNat k).eqv (Q'.ofNat (k + 1)) := by
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv k 1) ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (by decide)) ?_
  exact Q'.add_comm_eqv (Q'.ofNat k) 1

/-- `abs (term x k) ≤ termAbs x k`. -/
theorem abs_term_le (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    Q'.abs (term x k) ≤ termAbs x k := by
  obtain ⟨h1, h2⟩ := term_two_sided x hx k
  exact Q'.abs_le
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg h2) (Q'.le_of_eqv (Q'.neg_neg_eqv _))) h1

/-- **The per-term Lipschitz step** (with the term/`termAbs` data abstracted as
parameters `ta, tb, c, T, Tnext`, so no `set` tactic is needed).  Given the bound
at scale `k`, it produces the bound at `k+1` by factoring
`ta·((−a)·c) + −(tb·((−b)·c)) = c·((b−a)·tb + a·(tb−ta))` and telescoping with
`(1 + ofNat k) ≃ ofNat (k+1)` and `Tnext ≃ c·T`. -/
theorem termDiff_step {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1)
    (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) (k : Nat)
    {ta tb c T Tnext : Q'} (hc : (0 : Q') ≤ c) (hTnext : Tnext.eqv (c * T))
    (htb : Q'.abs tb ≤ T) (IH : Q'.abs (ta + -tb) ≤ d * (Q'.ofNat k * T)) :
    Q'.abs (ta * ((-a) * c) + -(tb * ((-b) * c))) ≤ d * (Q'.ofNat (k + 1) * Tnext) := by
      -- (1) factoring:  ta·((−a)·c) + −(tb·((−b)·c)) ≃ c·(b·tb + −(a·ta))
      have hfac : (ta * ((-a) * c) + -(tb * ((-b) * c))).eqv (c * (b * tb + -(a * ta))) := by
        have e1 : (ta * ((-a) * c)).eqv (-(c * (a * ta))) := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left ta ((-a) * c) (-(a * c)) (Q'.neg_mul_eqv a c)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv ta (a * c)) ?_
          refine Q'.neg_eqv_congr _ _ ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv ta (a * c)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (a * c) (c * a) ta (Q'.mul_comm_eqv a c)) ?_
          exact Q'.mul_assoc_eqv c a ta
        have e2 : (tb * ((-b) * c)).eqv (-(c * (b * tb))) := by
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left tb ((-b) * c) (-(b * c)) (Q'.neg_mul_eqv b c)) ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv tb (b * c)) ?_
          refine Q'.neg_eqv_congr _ _ ?_
          refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv tb (b * c)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (b * c) (c * b) tb (Q'.mul_comm_eqv b c)) ?_
          exact Q'.mul_assoc_eqv c b tb
        -- assemble:  e1 + (−e2) ;  then commute and factor c
        refine Q'.eqv_trans _ _ _
          (add_eqv_congr2 e1 (Q'.neg_eqv_congr _ _ e2)) ?_
        -- −(c·(a·ta)) + −(−(c·(b·tb)))  ≃  c·(b·tb) + −(c·(a·ta))  ≃  c·(b·tb + −(a·ta))
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (c * (b * tb)))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-(c * (a * ta))) (c * (b * tb))) ?_
        -- c·(b·tb) + −(c·(a·ta)) ≃ c·(b·tb) − c·(a·ta) ≃ c·(b·tb − a·ta)
        exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c (b * tb) (-(a * ta))) (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv c (a * ta))))
      have hT : (0 : Q') ≤ T := Q'.le_trans' _ _ _ (Q'.abs_nonneg tb) htb
      -- (2) bound the inner factor:  |b·tb + −(a·ta)| ≤ d·T + d·(ofNat k · T)
      have hZbound : Q'.abs (b * tb + -(a * ta))
          ≤ d * T + d * (Q'.ofNat k * T) := by
        -- decompose b·tb − a·ta ≃ (b−a)·tb + a·(tb − ta)
        have hdec : (b * tb + -(a * ta)).eqv ((b + -a) * tb + a * (tb + -ta)) := by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _ _ _
            (add_eqv_congr2 (Q'.add_mul_eqv b (-a) tb)
              (Q'.mul_add_eqv a tb (-ta))) ?_
          -- (b·tb + (−a)·tb) + (a·tb + a·(−ta))  ≃  b·tb + −(a·ta)
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left _ _ _
              (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv a ta))) ?_
          -- regroup:  (b·tb + (−a)·tb) + (a·tb + −(a·ta))
          --   the two ±(a·tb) cancel
          refine Q'.eqv_trans _ _ _
            (Q'.add_assoc_eqv (b * tb) ((-a) * tb) (a * tb + -(a * ta))) ?_
          refine Q'.add_eqv_congr_left (b * tb) _ _ ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv ((-a) * tb) (a * tb) (-(a * ta)))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv (-a) a tb))
                (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ tb (Q'.neg_add_self_eqv a))
                  (Q'.zero_mul_eqv tb)))) ?_
          exact QPoly.q_zero_add_eqv (-(a * ta))
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr hdec)) ?_
        refine Q'.le_trans' _ _ _ (abs_add_le ((b + -a) * tb) (a * (tb + -ta))) ?_
        refine add_le_add2 ?_ ?_
        · -- |(b−a)·tb| ≤ d·T
          refine Q'.le_trans' _ _ _ (abs_mul_le (b + -a) tb) ?_
          have hba_d : Q'.abs (b + -a) ≤ d :=
            Q'.abs_le
              (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.sub_le_of_le_add hab))
                (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv a (-b))
                  (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-a) (-(-b)) b (Q'.neg_neg_eqv b)) (Q'.add_comm_eqv (-a) b)))))
              (Q'.sub_le_of_le_add hba)
          exact Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ hba_d (Q'.abs_nonneg tb))
            (Q'.mul_le_mul_of_nonneg_left _ _ _ htb hd)
        · -- |a·(tb−ta)| ≤ d·(ofNat k · T)
          refine Q'.le_trans' _ _ _ (abs_mul_le a (tb + -ta)) ?_
          rw [abs_of_nonneg ha0]
          have hnn : (0 : Q') ≤ d * (Q'.ofNat k * T) :=
            Q'.mul_nonneg _ _ hd (Q'.mul_nonneg _ _ (ofNat_nonneg' k) hT)
          have hswap : (tb + -ta).eqv (-(ta + -tb)) := by
            refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv ta (-tb)) ?_)
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left (-ta) (-(-tb)) tb (Q'.neg_neg_eqv tb)) ?_
            exact Q'.add_comm_eqv (-ta) tb
          have hdiff : Q'.abs (tb + -ta) ≤ d * (Q'.ofNat k * T) :=
            Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
              (abs_eqv_congr hswap) (Q'.abs_neg' (ta + -tb)))) IH
          refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hdiff ha0) ?_
          exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha1 hnn)
            (Q'.le_of_eqv (Q'.one_mul_eqv _))
      -- (3) combine: |P| ≤ c·Zbound ≃ d·(ofNat(k+1)·Tnext)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr hfac)) ?_
      refine Q'.le_trans' _ _ _ (abs_mul_le c (b * tb + -(a * ta))) ?_
      rw [abs_of_nonneg hc]
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hZbound hc) ?_
      refine Q'.le_of_eqv ?_
      -- c·(d·T + d·(ofNat k·T)) ≃ d·(ofNat(k+1)·Tnext)
      -- step A: d·T + d·(ofNat k·T) ≃ d·(ofNat(k+1)·T)
      have hA : (d * T + d * (Q'.ofNat k * T)).eqv (d * (Q'.ofNat (k + 1) * T)) := by
        refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv d T (Q'.ofNat k * T))) ?_
        refine Q'.mul_eqv_congr_left d _ _ ?_
        refine Q'.eqv_trans _ _ _ ?_ (Q'.mul_eqv_congr_right _ _ T (one_add_ofNat k))
        refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.add_mul_eqv 1 (Q'.ofNat k) T))
        exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv T))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ hA) ?_
      -- step B: c·(d·(N·T)) ≃ d·(N·(c·T)) ≃ d·(N·Tnext)   (N = ofNat(k+1))
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv c d (Q'.ofNat (k + 1) * T))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (c * d) (d * c) (Q'.ofNat (k + 1) * T) (Q'.mul_comm_eqv c d)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv d c (Q'.ofNat (k + 1) * T)) ?_
      refine Q'.mul_eqv_congr_left d _ _ ?_
      -- c·(N·T) ≃ N·(c·T) ≃ N·Tnext
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c (Q'.ofNat (k + 1)) T)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (c * Q'.ofNat (k + 1)) (Q'.ofNat (k + 1) * c) T
          (Q'.mul_comm_eqv c (Q'.ofNat (k + 1)))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat (k + 1)) c T) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat (k + 1)) _ _ (Q'.eqv_symm hTnext)

/-- **The per-term Lipschitz bound** for sub-unit bases `0 ≤ a,b ≤ 1` with
`|a−b| ≤ d`: `|term a k − term b k| ≤ d·(k · termAbs 1 k)`.  Induction via
`termDiff_step`. -/
theorem termDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) :
    ∀ k, Q'.abs (term a k + -(term b k)) ≤ d * (Q'.ofNat k * termAbs 1 k)
  | 0 => by
      rw [term_zero, term_zero]
      have hrhs : (0 : Q') ≤ d * (Q'.ofNat 0 * termAbs 1 0) :=
        Q'.mul_nonneg _ _ hd (Q'.mul_nonneg _ _ (by decide) (termAbs_nonneg 1 (by decide) 0))
      exact Q'.le_trans' _ _ _ (by decide : Q'.abs ((1 : Q') + -(1 : Q')) ≤ (0 : Q')) hrhs
  | k + 1 => by
      have IH := termDiff_le ha0 ha1 hb0 hb1 hd hab hba k
      have htb : Q'.abs (term b k) ≤ termAbs 1 k :=
        Q'.le_trans' _ _ _ (abs_term_le b hb0 k) (termAbs_base_mono hb0 hb1 k)
      have hTnext : (termAbs 1 (k + 1)).eqv
          (Q'.mkPos 1 (k + 1) (Nat.succ_pos _) * termAbs 1 k) := by
        rw [termAbs_succ]
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)) ?_
        exact Q'.mul_comm_eqv (termAbs 1 k) (Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
      exact termDiff_step ha0 ha1 hd hab hba k (Q'.invSucc_nonneg k) hTnext htb IH

/-- The running Lipschitz-constant sum `∑_{j<k} ofNat j · termAbs 1 j`. -/
def sumBound : Nat → Q'
  | 0 => 0
  | k + 1 => sumBound k + Q'.ofNat k * termAbs 1 k

theorem sumBound_nonneg : ∀ k, (0 : Q') ≤ sumBound k
  | 0 => by decide
  | k + 1 => Q'.zero_le_add _ _ (sumBound_nonneg k)
      (Q'.mul_nonneg _ _ (ofNat_nonneg' k) (termAbs_nonneg 1 (by decide) k))

/-- **The partial-sum Lipschitz bound** (summed `termDiff_le`):
`|partialSum a k − partialSum b k| ≤ d·sumBound k`. -/
theorem partialSumDiff_le {a b d : Q'} (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (hb0 : (0 : Q') ≤ b)
    (hb1 : b ≤ 1) (hd : (0 : Q') ≤ d) (hab : a ≤ b + d) (hba : b ≤ a + d) :
    ∀ k, Q'.abs (partialSum a k + -(partialSum b k)) ≤ d * sumBound k
  | 0 => by
      show Q'.abs ((0 : Q') + -(0 : Q')) ≤ d * sumBound 0
      exact Q'.le_trans' _ _ _ (by decide : Q'.abs ((0 : Q') + -(0 : Q')) ≤ (0 : Q'))
        (Q'.mul_nonneg _ _ hd (sumBound_nonneg 0))
  | k + 1 => by
      have IH := partialSumDiff_le ha0 ha1 hb0 hb1 hd hab hba k
      have hre : ((partialSum a k + term a k) + -(partialSum b k + term b k)).eqv
          ((partialSum a k + -(partialSum b k)) + (term a k + -(term b k))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv (partialSum b k) (term b k))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (partialSum a k) (term a k)
          (-(partialSum b k) + -(term b k))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (partialSum a k) _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (term a k) (-(partialSum b k)) (-(term b k))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (partialSum a k) _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (term a k) (-(partialSum b k))))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (partialSum a k) _ _
          (Q'.add_assoc_eqv (-(partialSum b k)) (term a k) (-(term b k)))) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv (partialSum a k) (-(partialSum b k)) _)
      show Q'.abs (partialSum a k + term a k + -(partialSum b k + term b k))
          ≤ d * (sumBound k + Q'.ofNat k * termAbs 1 k)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr hre)) ?_
      refine Q'.le_trans' _ _ _ (abs_add_le _ _) ?_
      refine Q'.le_trans' _ _ _ (add_le_add2 IH
        (termDiff_le ha0 ha1 hb0 hb1 hd hab hba k)) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv d (sumBound k) (Q'.ofNat k * termAbs 1 k)))

/-! ### 2c. `sumBound k ≤ 3` (the uniform Lipschitz constant)

`sumBound (k+1) ≃ partialSumAbs 1 k` (each `ofNat (j+1)·termAbs 1 (j+1) ≃ termAbs 1 j`
via `ofNat_succ_mul_invSucc`), and `partialSumAbs 1 k ≤ 3` by a geometric invariant
(`+ 2·termAbs 1 k ≤ 3`, ratio `2·termAbs 1 (k+1) ≤ termAbs 1 k` for `k ≥ 1`). -/

/-- `ofNat 2 · (1/(k+2)) ≤ 1`. -/
theorem two_mkPos_le_one (k : Nat) :
    Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (Nat.succ_pos _) ≤ (1 : Q') := by
  have hle : Q'.ofNat 2 ≤ Q'.ofNat (k + 2) := by
    have hkk : k + 2 = 2 + k := by omega
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (Q'.ofNat 2) (Q'.ofNat k) (ofNat_nonneg' k)) ?_
    rw [hkk]
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.ofNat_add_eqv 2 k))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (Q'.ofNat 2) (Q'.ofNat (k + 2))
      (Q'.mkPos 1 (k + 2) (Nat.succ_pos _)) hle (Q'.invSucc_nonneg (k + 1)))
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc (k + 1)))

/-- `ofNat 2 · x ≃ x + x`. -/
theorem two_mul_eqv (x : Q') : (Q'.ofNat 2 * x).eqv (x + x) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 2) (1 + 1) x (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 x) ?_
  exact add_eqv_congr2 (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

/-- The geometric ratio: `2·termAbs 1 (k+2) ≤ termAbs 1 (k+1)`. -/
theorem two_termAbs_le (k : Nat) :
    Q'.ofNat 2 * termAbs 1 (k + 2) ≤ termAbs 1 (k + 1) := by
  rw [termAbs_succ]
  have hrearr : (Q'.ofNat 2 * (termAbs 1 (k + 1)
        * (1 * Q'.mkPos 1 (k + 1 + 1) (Nat.succ_pos _)))).eqv
      (termAbs 1 (k + 1) * (Q'.ofNat 2 * (1 * Q'.mkPos 1 (k + 1 + 1) (Nat.succ_pos _)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (termAbs 1 (k + 1))
        (1 * Q'.mkPos 1 (k + 1 + 1) (Nat.succ_pos _)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 2) (termAbs 1 (k + 1)))) ?_
    exact Q'.mul_assoc_eqv (termAbs 1 (k + 1)) (Q'.ofNat 2)
      (1 * Q'.mkPos 1 (k + 1 + 1) (Nat.succ_pos _))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
  have hfac : Q'.ofNat 2 * (1 * Q'.mkPos 1 (k + 1 + 1) (Nat.succ_pos _)) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.one_mul_eqv _)))
      (two_mkPos_le_one k)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ 1 (termAbs 1 (k + 1)) hfac
      (termAbs_nonneg 1 (by decide) (k + 1)))
    (Q'.le_of_eqv (Q'.mul_one_eqv (termAbs 1 (k + 1))))

/-- **Geometric invariant.** `partialSumAbs 1 k + 2·termAbs 1 k ≤ 3`. -/
theorem partialSumAbs_geom_inv : ∀ k,
    partialSumAbs 1 k + Q'.ofNat 2 * termAbs 1 k ≤ Q'.ofNat 3
  | 0 => by decide
  | 1 => by decide
  | k + 2 => by
      have IH := partialSumAbs_geom_inv (k + 1)
      show (partialSumAbs 1 (k + 1) + termAbs 1 (k + 1)) + Q'.ofNat 2 * termAbs 1 (k + 2)
          ≤ Q'.ofNat 3
      refine Q'.le_trans' _ _ _ ?_ IH
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _ (two_termAbs_le k)) (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (partialSumAbs 1 (k + 1)) (termAbs 1 (k + 1)) (termAbs 1 (k + 1))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (two_mul_eqv (termAbs 1 (k + 1))))

/-- `partialSumAbs 1 k ≤ 3`. -/
theorem partialSumAbs_le_three (k : Nat) : partialSumAbs 1 k ≤ Q'.ofNat 3 :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (partialSumAbs 1 k) _
      (Q'.mul_nonneg _ _ (by decide) (termAbs_nonneg 1 (by decide) k)))
    (partialSumAbs_geom_inv k)

/-- `ofNat (k+1)·termAbs 1 (k+1) ≃ termAbs 1 k`. -/
theorem g_succ_eqv (k : Nat) :
    (Q'.ofNat (k + 1) * termAbs 1 (k + 1)).eqv (termAbs 1 k) := by
  rw [termAbs_succ]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k + 1)) (termAbs 1 k)
      (1 * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat (k + 1) * termAbs 1 k)
      (termAbs 1 k * Q'.ofNat (k + 1)) _
      (Q'.mul_comm_eqv (Q'.ofNat (k + 1)) (termAbs 1 k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (termAbs 1 k) (Q'.ofNat (k + 1))
      (1 * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (termAbs 1 k) _ 1 ?_) (Q'.mul_one_eqv (termAbs 1 k))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (k + 1)) _ _ (Q'.one_mul_eqv _)) ?_
  exact Q'.ofNat_succ_mul_invSucc k

/-- `sumBound (k+1) ≃ partialSumAbs 1 k`. -/
theorem sumBound_eqv : ∀ k, (sumBound (k + 1)).eqv (partialSumAbs 1 k)
  | 0 => by decide
  | k + 1 => by
      show (sumBound (k + 1) + Q'.ofNat (k + 1) * termAbs 1 (k + 1)).eqv
          (partialSumAbs 1 (k + 1))
      exact add_eqv_congr2 (sumBound_eqv k) (g_succ_eqv k)

/-- **`sumBound k ≤ 3`** — the uniform Lipschitz constant. -/
theorem sumBound_le_three : ∀ k, sumBound k ≤ Q'.ofNat 3
  | 0 => by decide
  | k + 1 => Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumBound_eqv k)) (partialSumAbs_le_three k)

/-! ### 2d. `expNegC` — `e^{−w}` for a CReal argument `w` with `0 ≤ w.approx ≤ 1`

Assembled as the completion `lim_k expNeg (w.approx k)` (`completeLimitCauchy`):
the **outer** modulus comes from `w`'s own (data) modulus `Mw` composed with the
partial-sum Lipschitz `partialSumDiff_le` + `sumBound_le_three` (all-`k`,
`boundK = 0`); the **inner** per-term regularity is `expNeg`'s explicit modulus
`Mexp` (`expNeg_cauchy_explicit`).  `Mexp` is NOT monotone in its argument, so the
per-term `ModCauchyEv` (not the uniform `ModCauchy`) is required. -/

/-- `0 < ε/3`. -/
theorem third_pos {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < ε * Q'.mkPos 1 3 (by decide) :=
  Q'.mul_pos hε (Q'.invSucc_pos 2)

/-- `(ε/3)·3 ≃ ε`. -/
theorem third_mul_three (ε : Q') :
    ((ε * Q'.mkPos 1 3 (by decide)) * Q'.ofNat 3).eqv ε := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ε (Q'.mkPos 1 3 (by decide)) (Q'.ofNat 3)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left ε _ 1 ?_) (Q'.mul_one_eqv ε)
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.mkPos 1 3 (by decide)) (Q'.ofNat 3)) ?_
  exact Q'.ofNat_succ_mul_invSucc 2

/-- `|a − b| ≤ ε → a ≤ b + ε`. -/
theorem le_add_of_abs_sub_le {a b ε : Q'} (h : Q'.abs (a + -b) ≤ ε) : a ≤ b + ε := by
  have h1 : a + -b ≤ ε := Q'.le_trans' _ _ _ (Q'.le_abs_self (a + -b)) h
  have h2 : (a + -b) + b ≤ ε + b := Q'.add_le_add_right (a + -b) ε b h1
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.add_comm_eqv ε b)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

/-- `|a − b| ≃ |b − a|`. -/
theorem abs_sub_comm (a b : Q') : (Q'.abs (a + -b)).eqv (Q'.abs (b + -a)) := by
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (abs_eqv_congr ?_) (Q'.abs_neg' (a + -b)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv a (-b)) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-a) (-(-b)) b (Q'.neg_neg_eqv b)) ?_
  exact Q'.add_comm_eqv (-a) b

/-- The `ModCauchyEv` data backing `expNegC` (named so the convergence is
exposed for §6). -/
def expNegMC (w : CReal) (Mw : Q' → Nat)
    (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    CReal.ModCauchyEv (fun k => expNeg (w.approx k) (hpos k)) :=
    { M := fun ε => Mw (ε * Q'.mkPos 1 3 (by decide))
      reg := fun i ε => Mexp (w.approx i) ε
      boundK := fun _ _ _ => 0
      bound := by
        intro ε hε m n hm hn k _
        have hd : (0 : Q') ≤ ε * Q'.mkPos 1 3 (by decide) := Q'.le_of_lt (third_pos hε)
        obtain ⟨hab, hba⟩ := hMw (ε * Q'.mkPos 1 3 (by decide)) (third_pos hε) m n hm hn
        have habs : Q'.abs (partialSum (w.approx m) k + -(partialSum (w.approx n) k)) ≤ ε :=
          Q'.le_trans' _ _ _
            (partialSumDiff_le (hpos m) (hle1 m) (hpos n) (hle1 n) hd hab hba k)
            (Q'.le_trans' _ _ _
              (Q'.mul_le_mul_of_nonneg_left _ _ _ (sumBound_le_three k) hd)
              (Q'.le_of_eqv (third_mul_three ε)))
        exact ⟨le_add_of_abs_sub_le habs,
          le_add_of_abs_sub_le (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (abs_sub_comm (partialSum (w.approx n) k) (partialSum (w.approx m) k)))
            habs)⟩
      regular := fun i ε hε p q hp hq =>
        expNeg_cauchy_explicit (w.approx i) (hpos i) ε hε p q hp hq
      Mmono := fun ε δ hδ hδε =>
        hMwmono _ _ (third_pos hδ)
          (Q'.mul_le_mul_of_nonneg_right δ ε _ hδε (Q'.le_of_lt (Q'.invSucc_pos 2))) }

/-- **`e^{−w}` for a CReal argument** `w` with `0 ≤ w.approx k ≤ 1` and an explicit
`Type`-level modulus `Mw` for `w`.  The constructive limit of `e^{−w.approx k}`. -/
def expNegC (w : CReal) (Mw : Q' → Nat)
    (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) : CReal :=
  CReal.completeLimitCauchy (fun k => expNeg (w.approx k) (hpos k))
    (expNegMC w Mw hpos hle1 hMw hMwmono)

/-- `expNegC w` is the limit of the sequence `k ↦ e^{−w.approx k}`. -/
theorem expNegC_converges (w : CReal) (Mw : Q' → Nat)
    (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) :
    ConvergesTo (fun k => expNeg (w.approx k) (hpos k))
      (expNegC w Mw hpos hle1 hMw hMwmono) :=
  CReal.convergesTo_completeLimitCauchy _ (expNegMC w Mw hpos hle1 hMw hMwmono)

/-! ### 2e. Boundedness `|partialSum x n| ≤ 3` (for the mul-continuity in §6) -/

/-- `|partialSum x n| ≤ partialSumAbs x n` (triangle). -/
theorem abs_partialSum_le (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ n, Q'.abs (partialSum x n) ≤ partialSumAbs x n
  | 0 => by rw [partialSum_zero, partialSumAbs_zero]; decide
  | n + 1 => by
      show Q'.abs (partialSum x n + term x n) ≤ partialSumAbs x n + termAbs x n
      exact Q'.le_trans' _ _ _ (abs_add_le (partialSum x n) (term x n))
        (add_le_add2 (abs_partialSum_le x hx n) (abs_term_le x hx n))

/-- `partialSumAbs x n ≤ partialSumAbs 1 n` for `0 ≤ x ≤ 1`. -/
theorem partialSumAbs_base_mono {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) :
    ∀ n, partialSumAbs x n ≤ partialSumAbs 1 n
  | 0 => by rw [partialSumAbs_zero, partialSumAbs_zero]; exact Q'.le_refl' 0
  | n + 1 => add_le_add2 (partialSumAbs_base_mono hx0 hx1 n) (termAbs_base_mono hx0 hx1 n)

/-- **`|partialSum x n| ≤ 3`** for `0 ≤ x ≤ 1`. -/
theorem abs_partialSum_le_three {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (n : Nat) :
    Q'.abs (partialSum x n) ≤ Q'.ofNat 3 :=
  Q'.le_trans' _ _ _ (abs_partialSum_le x hx0 n)
    (Q'.le_trans' _ _ _ (partialSumAbs_base_mono hx0 hx1 n) (partialSumAbs_le_three n))

/-- `|（expNeg (w.approx i) _).approx n| ≤ 3` (the bounded factor, with the diagonal
index `i` kept opaque). -/
theorem abs_expNeg_approx_le_three {w : CReal} (hpos : ∀ k, (0 : Q') ≤ w.approx k)
    (hle1 : ∀ k, w.approx k ≤ 1) (i n : Nat) :
    Q'.abs ((expNeg (w.approx i) (hpos i)).approx n) ≤ Q'.ofNat 3 :=
  abs_partialSum_le_three (hpos i) (hle1 i) n

/-- `|（expNegC w …).approx n| ≤ 3` — bounds `expNegC`'s own diagonal. -/
theorem expNegC_approx_le_three (w : CReal) (Mw : Q' → Nat)
    (hpos : ∀ k, (0 : Q') ≤ w.approx k) (hle1 : ∀ k, w.approx k ≤ 1)
    (hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
            w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε)
    (hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ) (n : Nat) :
    Q'.abs ((expNegC w Mw hpos hle1 hMw hMwmono).approx n) ≤ Q'.ofNat 3 := by
  show Q'.abs ((CReal.completeLimitCauchy (fun k => expNeg (w.approx k) (hpos k))
      (expNegMC w Mw hpos hle1 hMw hMwmono)).approx n) ≤ Q'.ofNat 3
  rw [CReal.completeLimitCauchy_approx]
  generalize CReal.RhatE (fun k => expNeg (w.approx k) (hpos k))
    (expNegMC w Mw hpos hle1 hMw hMwmono) n = jdx
  generalize CReal.MhatE (fun k => expNeg (w.approx k) (hpos k))
    (expNegMC w Mw hpos hle1 hMw hMwmono) n = idx
  exact abs_expNeg_approx_le_three hpos hle1 idx jdx

/-! ## 3. The alternating-series lower bound `e^{−x} ≥ 1 − x`

For `0 ≤ x ≤ 1` the magnitude terms `xᵏ/k!` decrease, so the alternating partial
sums bracket the limit: even-indexed partial sums increase from
`partialSum x 2 = 1 − x`, and odd-indexed ones sit just above.  Hence
`1 − x ≤ partialSum x n` for every `n ≥ 2`, giving `1 − x ≤ e^{−x}` in the
limit — equivalently `1 − e^{−x} ≤ x` (`CReal.oneSub_le_expNeg`), the convexity
input the contraction modulus needs. -/

/-- Linear rearrangement: `1 − t ≤ p  ↔  1 − p ≤ t` (used to flip the partial-sum
lower bound into the `leRat` upper bound on `1 − e^{−t}`). -/
theorem oneSub_swap {t p : Q'} (h : (1 : Q') + -t ≤ p) : (1 : Q') + -p ≤ t := by
  have h1 : (1 : Q') ≤ p + t := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.add_le_add_right (1 + -t) p t h)
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-t) t) ?_)
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 (-t + t) 0 (Q'.neg_add_self_eqv t))
      (QPoly.q_add_zero_eqv 1)
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right 1 (p + t) (-p) h1) (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (p + t) (t + p) (-p) (Q'.add_comm_eqv p t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv t p (-p)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left t (p + -p) 0 (Q'.add_neg_self_eqv p))
    (QPoly.q_add_zero_eqv t)

/-- The first-order term `term x 1 ≃ −x`. -/
theorem term_one_eqv (x : Q') : (term x 1).eqv (-x) := by
  rw [term_succ, term_zero]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (-x) (Q'.mkPos 1 (0 + 1) (Nat.succ_pos _)) 1 (by decide)) ?_
  exact Q'.mul_one_eqv (-x)

/-- `partialSum x 2 ≃ 1 − x`. -/
theorem partialSum_two_eqv (x : Q') : (partialSum x 2).eqv ((1 : Q') + -x) := by
  rw [partialSum_two]
  exact Q'.add_eqv_congr_left 1 (term x 1) (-x) (term_one_eqv x)

/-- **Consecutive-pair nonnegativity.**  For `0 ≤ x ≤ 1`,
`0 ≤ term x (2m+2) + term x (2m+3)`: the even (positive) term dominates the next
(negative) one because the magnitudes `xᵏ/k!` decrease.  Proved by factoring
`term (2m+3) = term (2m+2)·((−x)·1/(2m+3))` and `0 ≤ 1 + (−x)·1/(2m+3)`. -/
theorem pair_nonneg {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (m : Nat) :
    (0 : Q') ≤ term x (2 * m + 2) + term x (2 * m + 3) := by
  have ht2 : (0 : Q') ≤ term x (2 * m + 2) := by
    have e : 2 * m + 2 = 2 * (m + 1) := by omega
    rw [e]; exact (term_sign hx0 (m + 1)).1
  have e3 : 2 * m + 3 = (2 * m + 2) + 1 := by omega
  rw [e3, term_succ]
  have hmnn : (0 : Q') ≤ Q'.mkPos 1 ((2 * m + 2) + 1) (Nat.succ_pos _) := Q'.invSucc_nonneg _
  have hmle1 : Q'.mkPos 1 ((2 * m + 2) + 1) (Nat.succ_pos _) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le (2 * m + 2))) (by decide)
  have hxm : x * Q'.mkPos 1 ((2 * m + 2) + 1) (Nat.succ_pos _) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right x 1 _ hx1 hmnn)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) hmle1)
  have hrfge : (0 : Q') ≤ (1 : Q') + (-x) * Q'.mkPos 1 ((2 * m + 2) + 1) (Nat.succ_pos _) :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hxm)
      (Q'.le_of_eqv (Q'.add_eqv_congr_left 1 _ _ (Q'.eqv_symm (Q'.neg_mul_eqv x _))))
  have hprod : (0 : Q') ≤ term x (2 * m + 2)
      * ((1 : Q') + (-x) * Q'.mkPos 1 ((2 * m + 2) + 1) (Nat.succ_pos _)) :=
    Q'.mul_nonneg _ _ ht2 hrfge
  refine Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (term x (2 * m + 2)) 1 _) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (term x (2 * m + 2)))

/-- **Even-indexed partial sums are ≥ `1 − x`** (for `0 ≤ x ≤ 1`).  Induction:
base `partialSum x 2 ≃ 1 − x`; step adds a nonneg consecutive pair. -/
theorem even_lb {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ∀ m, (1 : Q') - x ≤ partialSum x (2 * m + 2)
  | 0 => by
      show (1 : Q') + -x ≤ partialSum x 2
      exact Q'.le_of_eqv (Q'.eqv_symm (partialSum_two_eqv x))
  | m + 1 => by
      have IH := even_lb hx0 hx1 m
      have hpair : (0 : Q') ≤ term x (2 * m + 2) + term x ((2 * m + 2) + 1) := by
        have e : 2 * m + 3 = (2 * m + 2) + 1 := by omega
        rw [e] at *; exact pair_nonneg hx0 hx1 m
      have eidx : 2 * (m + 1) + 2 = ((2 * m + 2) + 1) + 1 := by omega
      rw [eidx, partialSum_succ, partialSum_succ]
      refine Q'.le_trans' _ _ _ IH ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _))) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ 0 _ hpair) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

/-- **Odd-indexed partial sums are ≥ `1 − x`**: the preceding even sum plus a
nonneg even term. -/
theorem odd_lb {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (m : Nat) :
    (1 : Q') - x ≤ partialSum x (2 * m + 3) := by
  have he := even_lb hx0 hx1 m
  have ht2 : (0 : Q') ≤ term x (2 * m + 2) := by
    have e2 : 2 * m + 2 = 2 * (m + 1) := by omega
    rw [e2]; exact (term_sign hx0 (m + 1)).1
  have e : 2 * m + 3 = (2 * m + 2) + 1 := by omega
  rw [e, partialSum_succ]
  refine Q'.le_trans' _ _ _ he ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _))) ?_
  exact Q'.add_le_add_left _ 0 _ ht2

/-- **The alternating-series lower bound (`Q'` level).**  For `0 ≤ x ≤ 1` and every
`n ≥ 2`, `1 − x ≤ partialSum x n`.  Splits on the parity of `n`. -/
theorem oneSub_le_partialSum {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (n : Nat) (hn : 2 ≤ n) : (1 : Q') - x ≤ partialSum x n := by
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hpar with h | h
  · have e : n = 2 * (n / 2 - 1) + 2 := by omega
    rw [e]; exact even_lb hx0 hx1 (n / 2 - 1)
  · have e : n = 2 * (n / 2 - 1) + 3 := by omega
    rw [e]; exact odd_lb hx0 hx1 (n / 2 - 1)

end ExpNeg

namespace CReal

/-- **`1 − e^{−t} ≤ t`** for `0 ≤ t ≤ 1` — the convexity bound, as a sound
rational upper bound on the `CReal` `1 − e^{−t}`.  From the alternating-series
lower bound `1 − t ≤ partialSum t n` (`n ≥ 2`) via the linear flip `oneSub_swap`. -/
theorem oneSub_le_expNeg {t : Q'} (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) :
    CReal.leRat (CReal.sub CReal.cone (ExpNeg.expNeg t ht0)) t := by
  apply CReal.leRat_of_eventually
  refine ⟨2, fun n hn => ?_⟩
  show (1 : Q') + -(ExpNeg.partialSum t n) ≤ t
  exact ExpNeg.oneSub_swap (ExpNeg.oneSub_le_partialSum ht0 ht1 n hn)

/-! ## 4. `Equiv` congruences and the contraction `e^{−a} − e^{−b} ≤ b − a`

`add`/`neg`/`sub` are pointwise, so `Equiv` is a congruence for them (one-liners
from the definition).  The contraction then factors:
`e^{−a} − e^{−b} = e^{−a}·(1 − e^{−(b−a)})` (via `mul_sub` + the addition law
`expNeg_add_equiv`), and is bounded by `1·(b−a) = b−a` using `e^{−a} ≤ 1`,
`1 − e^{−(b−a)} ≤ b−a` (§3) and `leRat_mul`.  Needs `b − a ≤ 1`. -/

/-- `Equiv` congruence for `add` on the right. -/
theorem add_congr_right {x y y' : CReal} (h : CReal.Equiv y y') :
    CReal.Equiv (CReal.add x y) (CReal.add x y') := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  show (x.approx n + y.approx n ≤ (x.approx n + y'.approx n) + ε)
    ∧ (x.approx n + y'.approx n ≤ (x.approx n + y.approx n) + ε)
  exact ⟨Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ h1)
           (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))),
         Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ h2)
           (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))⟩

/-- `Equiv` congruence for `add` on the left. -/
theorem add_congr_left {x x' y : CReal} (h : CReal.Equiv x x') :
    CReal.Equiv (CReal.add x y) (CReal.add x' y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  show (x.approx n + y.approx n ≤ (x'.approx n + y.approx n) + ε)
    ∧ (x'.approx n + y.approx n ≤ (x.approx n + y.approx n) + ε)
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h1) (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x'.approx n) ε (y.approx n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ε (y.approx n))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (x'.approx n) (y.approx n) ε)
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h2) (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x.approx n) ε (y.approx n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ε (y.approx n))) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (x.approx n) (y.approx n) ε)

/-- `Equiv` congruence for `neg`. -/
theorem neg_congr {y y' : CReal} (h : CReal.Equiv y y') :
    CReal.Equiv (CReal.neg y) (CReal.neg y') := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  show (-(y.approx n) ≤ -(y'.approx n) + ε) ∧ (-(y'.approx n) ≤ -(y.approx n) + ε)
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- `Equiv` congruence for `sub` on the right. -/
theorem sub_congr_right {x y y' : CReal} (h : CReal.Equiv y y') :
    CReal.Equiv (CReal.sub x y) (CReal.sub x y') :=
  add_congr_right (neg_congr h)

/-- `Equiv` congruence for `sub` on the left. -/
theorem sub_congr_left {x x' y : CReal} (h : CReal.Equiv x x') :
    CReal.Equiv (CReal.sub x y) (CReal.sub x' y) :=
  add_congr_left h

/-- **`e^{−x} ≤ 1`** (copied from `SU3CharFactor` to avoid the heavy `RepTheory`
import): `e^{−x} ≤ 1/(1+x) ≤ 1`. -/
theorem expNeg_le_one (x : Q') (hx : (0 : Q') ≤ x) :
    CReal.leRat (ExpNeg.expNeg x hx) 1 := by
  have h2 : ExpUBInstance.oneOver1p x ≤ 1 := by
    have hanti := ExpUBInstance.oneOver1p_antitone 0 x hx
    rwa [ExpUBInstance.oneOver1p_zero] at hanti
  exact CReal.leRat_mono (expNeg_le_oneOver1p x hx) h2

/-- **`0 ≤ 1 − e^{−c}`** (as `geRat … 0`): the margin is nonnegative, from
`e^{−c} ≤ 1`. -/
theorem geRat_sub_cone_expNeg {c : Q'} (hc0 : (0 : Q') ≤ c) :
    ExpPos.geRat (CReal.sub CReal.cone (ExpNeg.expNeg c hc0)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := expNeg_le_one c hc0 ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (0 : Q') ≤ ((1 : Q') + -(ExpNeg.partialSum c n)) + ε
  have h0 : (0 : Q') ≤ ((1 : Q') + ε) + -(ExpNeg.partialSum c n) :=
    Q'.sub_nonneg_of_le (hN n hn)
  refine Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv ?_)
  -- (1+ε) + -ps ≃ (1 + -ps) + ε
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 ε (-(ExpNeg.partialSum c n))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.add_comm_eqv ε (-(ExpNeg.partialSum c n)))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv 1 (-(ExpNeg.partialSum c n)) ε)

/-- **The contraction (limit-level Lipschitz).**  For `0 ≤ a ≤ b` with `b − a ≤ 1`,
`e^{−a} − e^{−b} ≤ b − a`.  This is the modulus of continuity the completion needs:
`expNeg` is a contraction on `[0,∞)`. -/
theorem expNeg_contraction {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b)
    (hba : b - a ≤ (1 : Q')) :
    CReal.leRat (CReal.sub (ExpNeg.expNeg a ha)
      (ExpNeg.expNeg b (Q'.le_trans' _ _ _ ha hab))) (b - a) := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
  have hc0 : (0 : Q') ≤ b - a := Q'.sub_nonneg_of_le hab
  -- the addition law: e^{−b} ≈ e^{−a}·e^{−(b−a)}
  have hac : (a + (b - a)).eqv b := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (b + -a) (-a + b) (Q'.add_comm_eqv b (-a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) b)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ b (Q'.add_neg_self_eqv a)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 b) ?_
    exact QPoly.q_add_zero_eqv b
  have hb_eq : CReal.Equiv (ExpNeg.expNeg b hb)
      (CReal.mul (ExpNeg.expNeg a ha) (ExpNeg.expNeg (b - a) hc0)) :=
    (Equiv.trans (expNeg_add_equiv a (b - a) ha hc0)
      (expNeg_eqv_congr (Q'.zero_le_add a (b - a) ha hc0) hb hac)).symm
  -- factor the difference: sub a (e^{−b}) ≈ a·(1 − e^{−(b−a)})
  have step1 : CReal.Equiv (CReal.sub (ExpNeg.expNeg a ha) (ExpNeg.expNeg b hb))
      (CReal.sub (ExpNeg.expNeg a ha)
        (CReal.mul (ExpNeg.expNeg a ha) (ExpNeg.expNeg (b - a) hc0))) :=
    sub_congr_right hb_eq
  have step2 : CReal.Equiv
      (CReal.sub (ExpNeg.expNeg a ha)
        (CReal.mul (ExpNeg.expNeg a ha) (ExpNeg.expNeg (b - a) hc0)))
      (CReal.mul (ExpNeg.expNeg a ha)
        (CReal.sub CReal.cone (ExpNeg.expNeg (b - a) hc0))) :=
    (Equiv.trans (CReal.mul_sub (ExpNeg.expNeg a ha) CReal.cone (ExpNeg.expNeg (b - a) hc0))
      (sub_congr_left (CRealAlg.cmul_cone (ExpNeg.expNeg a ha)))).symm
  have E := Equiv.trans step1 step2
  -- bound the factored form by 1·(b−a) = b−a
  have hmul : CReal.leRat (CReal.mul (ExpNeg.expNeg a ha)
      (CReal.sub CReal.cone (ExpNeg.expNeg (b - a) hc0))) (b - a) := by
    have hlm := CReal.leRat_mul (expNeg_le_one a ha) (oneSub_le_expNeg hc0 hba)
      (expNeg_geRat_zero a ha) (geRat_sub_cone_expNeg hc0)
      (by decide : (0 : Q') ≤ (1 : Q')) hc0
    exact CReal.leRat_mono hlm (Q'.le_of_eqv (Q'.one_mul_eqv (b - a)))
  exact leRat_of_equiv E hmul

/-! ## 6. `cpow`, mul-continuity, and the add-law lift -/

/-- CReal `Nat`-power (fold of `mul`). -/
def cpow (x : CReal) : Nat → CReal
  | 0 => CReal.cone
  | n + 1 => CReal.mul (cpow x n) x

/-- Product-difference decomposition: `a·b − c·d ≃ a·(b−d) + d·(a−c)`. -/
theorem mul_sub_decomp (a b c d : Q') :
    (a * b + -(c * d)).eqv (a * (b + -d) + d * (a + -c)) := by
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (ExpNeg.add_eqv_congr2
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a b (-d))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv a d)))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv d a (-c))
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv d c)))) ?_)
  -- (a·b + −(a·d)) + (d·a + −(d·c)) ≃ a·b + −(c·d)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (a * b) (-(a * d)) (d * a + -(d * c))) ?_
  refine Q'.add_eqv_congr_left (a * b) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-(a * d)) (d * a) (-(d * c)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv d a))
        (Q'.neg_add_self_eqv (a * d)))) ?_
  exact Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv (-(d * c)))
    (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv d c))

/-- `a ≤ b+δ`, `b ≤ a+δ` ⟹ `|a − b| ≤ δ`. -/
theorem abs_sub_le_of_bounds {a b δ : Q'} (h1 : a ≤ b + δ) (h2 : b ≤ a + δ) :
    Q'.abs (a + -b) ≤ δ :=
  Q'.abs_le
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.sub_le_of_le_add h2))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv b (-a))
        (Q'.eqv_trans _ _ _
          (ExpNeg.add_eqv_congr2 (Q'.eqv_refl (-b)) (Q'.neg_neg_eqv a))
          (Q'.add_comm_eqv (-b) a)))))
    (Q'.sub_le_of_le_add h1)

/-- **mul-continuity** of the completion limit: if `u → U`, `v → V` and the
sequences/limit factor approximations are bounded by `B`, then
`mul (u k) (v k) → mul U V`. -/
theorem convergesTo_mul {u v : Nat → CReal} {U V : CReal} {B : Q'} (hB : (0 : Q') ≤ B)
    (hub : ∀ k n, Q'.abs ((u k).approx n) ≤ B) (hVb : ∀ n, Q'.abs (V.approx n) ≤ B)
    (hu : ConvergesTo u U) (hv : ConvergesTo v V) :
    ConvergesTo (fun k => CReal.mul (u k) (v k)) (CReal.mul U V) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_mul_le (Q'.zero_le_add B B hB hB) hε
  obtain ⟨NstU, hstU⟩ := hu δ hδpos
  obtain ⟨NstV, hstV⟩ := hv δ hδpos
  refine ⟨max NstU NstV, fun N hN => ?_⟩
  obtain ⟨NapxU, hclU⟩ := hstU N (Nat.le_trans (Nat.le_max_left _ _) hN)
  obtain ⟨NapxV, hclV⟩ := hstV N (Nat.le_trans (Nat.le_max_right _ _) hN)
  refine ⟨max NapxU NapxV, fun n hn => ?_⟩
  obtain ⟨hU1, hU2⟩ := hclU n (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨hV1, hV2⟩ := hclV n (Nat.le_trans (Nat.le_max_right _ _) hn)
  -- the product difference is ≤ ε
  have hbound : Q'.abs ((u N).approx n * (v N).approx n
      + -(U.approx n * V.approx n)) ≤ ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr
      (mul_sub_decomp ((u N).approx n) ((v N).approx n) (U.approx n) (V.approx n)))) ?_
    refine Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _) ?_
    have hp1 : Q'.abs ((u N).approx n * ((v N).approx n + -(V.approx n))) ≤ B * δ :=
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (hub N n) (Q'.abs_nonneg _))
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (abs_sub_le_of_bounds hV1 hV2) hB))
    have hp2 : Q'.abs (V.approx n * ((u N).approx n + -(U.approx n))) ≤ B * δ :=
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (hVb n) (Q'.abs_nonneg _))
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (abs_sub_le_of_bounds hU1 hU2) hB))
    refine Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hp1 hp2) ?_
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_mul_eqv B B δ))) hδ
  exact ⟨ExpNeg.le_add_of_abs_sub_le hbound,
    ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm (U.approx n * V.approx n)
        ((u N).approx n * (v N).approx n))) hbound)⟩

/-- The modulus-data hypotheses for `expNegC w` (Cauchy modulus + antitonicity),
packaged to shorten the add-law signature. -/
structure ExpNegCData (w : CReal) : Type where
  Mw : Q' → Nat
  hpos : ∀ k, (0 : Q') ≤ w.approx k
  hle1 : ∀ k, w.approx k ≤ 1
  hMw : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Mw ε ≤ m → Mw ε ≤ n →
          w.approx m ≤ w.approx n + ε ∧ w.approx n ≤ w.approx m + ε
  hMwmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Mw ε ≤ Mw δ

/-- `expNegC` from packaged data. -/
def expNegCD (w : CReal) (d : ExpNegCData w) : CReal :=
  ExpNeg.expNegC w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

theorem expNegCD_converges (w : CReal) (d : ExpNegCData w) :
    ConvergesTo (fun k => ExpNeg.expNeg (w.approx k) (d.hpos k)) (expNegCD w d) :=
  ExpNeg.expNegC_converges w d.Mw d.hpos d.hle1 d.hMw d.hMwmono

/-- **The add-law lift.**  `e^{−a}·e^{−b} ≈ e^{−(a+b)}` for CReal arguments.
Both factors converge (`expNegCD_converges`), their product converges to the
product of limits (`convergesTo_mul`, bounded by `|partialSum| ≤ 3`), the product
sequence is termwise `e^{−a_k}·e^{−b_k} ≈ e^{−(a_k+b_k)}` (`expNeg_add_equiv`), so
the limits agree (`Equiv_of_limit_of_equal`). -/
theorem expNegCD_add (a b : CReal) (da : ExpNegCData a) (db : ExpNegCData b)
    (dab : ExpNegCData (CReal.add a b)) :
    CReal.Equiv (CReal.mul (expNegCD a da) (expNegCD b db)) (expNegCD (CReal.add a b) dab) := by
  have hub : ∀ k n, Q'.abs ((ExpNeg.expNeg (a.approx k) (da.hpos k)).approx n) ≤ Q'.ofNat 3 :=
    fun k n => ExpNeg.abs_partialSum_le_three (da.hpos k) (da.hle1 k) n
  have hVb : ∀ n, Q'.abs ((expNegCD b db).approx n) ≤ Q'.ofNat 3 :=
    fun n => ExpNeg.expNegC_approx_le_three b db.Mw db.hpos db.hle1 db.hMw db.hMwmono n
  refine Equiv_of_limit_of_equal
    (fun k => expNeg_add_equiv (a.approx k) (b.approx k) (da.hpos k) (db.hpos k))
    (convergesTo_mul (by decide : (0 : Q') ≤ Q'.ofNat 3) hub hVb
      (expNegCD_converges a da) (expNegCD_converges b db))
    (expNegCD_converges (CReal.add a b) dab)

/-! ## 7. The power law and the self-similar flow inhabitant -/

/-- `X + -Y ≤ ε → X ≤ Y + ε`. -/
theorem le_add_of_sub_le {X Y ε : Q'} (h : X + -Y ≤ ε) : X ≤ Y + ε := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right (X + -Y) ε Y h)
      (Q'.le_of_eqv (Q'.add_comm_eqv ε Y)))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv X (-Y) Y) ?_)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left X (-Y + Y) 0 (Q'.neg_add_self_eqv Y)) ?_
  exact QPoly.q_add_zero_eqv X

/-- **Left mul-congruence**: `Equiv A A' → Equiv (A·B) (A'·B)` (the non-pointwise
product congruence, via `localBound B`). -/
theorem mul_congr_left {A A' B : CReal} (h : CReal.Equiv A A') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A' B) := by
  intro ε hε
  obtain ⟨Nb, Bb, hBb, hbb⟩ := CReal.localBound B
  obtain ⟨δ, hδpos, hδle⟩ := CReal.exists_mul_le hBb hε
  obtain ⟨Na, hNa⟩ := h δ hδpos
  refine ⟨max Nb Na, fun n hn => ?_⟩
  obtain ⟨hb1, hb2⟩ := hbb n (Nat.le_trans (Nat.le_max_left _ _) hn)
  obtain ⟨ha1, ha2⟩ := hNa n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hd : Q'.abs (A.approx n + -(A'.approx n)) ≤ δ := abs_sub_le_of_bounds ha1 ha2
  have hBn : Q'.abs (B.approx n) ≤ Bb := Q'.abs_le hb1 hb2
  have hprod : Q'.abs ((A.approx n + -(A'.approx n)) * B.approx n) ≤ ε :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (Q'.abs_nonneg _))
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hBn (Q'.le_of_lt hδpos)))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv δ Bb)) hδle))
  have heqv : ((A.approx n + -(A'.approx n)) * B.approx n).eqv
      (A.approx n * B.approx n + -(A'.approx n * B.approx n)) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (A.approx n) (-(A'.approx n)) (B.approx n))
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv (A'.approx n) (B.approx n)))
  have habs : Q'.abs (A.approx n * B.approx n + -(A'.approx n * B.approx n)) ≤ ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr (Q'.eqv_symm heqv))) hprod
  exact ⟨le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs),
    le_add_of_sub_le (Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_sub_comm
        (A'.approx n * B.approx n) (A.approx n * B.approx n))) habs))⟩

/-- `(a+e)+(a+e) ≃ (a+a)+(e+e)`. -/
theorem add_pair_rearrange (a e : Q') : ((a + e) + (a + e)).eqv ((a + a) + (e + e)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a e (a + e)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (e + (a + e)) ((a + e) + e)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv e a e))
      (Q'.add_eqv_congr_right _ _ e (Q'.add_comm_eqv e a)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((a + e) + e) (a + (e + e))
    (Q'.add_assoc_eqv a e e)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a a (e + e))

/-- `ε/2 + ε/2 ≃ ε`. -/
theorem half_add_half (ε : Q') :
    (ε * Q'.mkPos 1 2 (by decide) + ε * Q'.mkPos 1 2 (by decide)).eqv ε := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv ε _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left ε _ 1 (by decide)) ?_
  exact Q'.mul_one_eqv ε

/-- **`ExpNegCData` for `s + s`** (the 2-fold sum), given `s`'s data and `s.approx ≤ 1/2`. -/
def addSelfData (s : CReal) (d : ExpNegCData s)
    (hhalf : ∀ k, s.approx k + s.approx k ≤ 1) : ExpNegCData (CReal.add s s) where
  Mw := fun ε => d.Mw (ε * Q'.mkPos 1 2 (by decide))
  hpos := fun k => Q'.zero_le_add _ _ (d.hpos k) (d.hpos k)
  hle1 := hhalf
  hMw := fun ε hε m n hm hn => by
    have hε2 : (0 : Q') < ε * Q'.mkPos 1 2 (by decide) := Q'.mul_pos hε (Q'.invSucc_pos 1)
    obtain ⟨h1, h2⟩ := d.hMw (ε * Q'.mkPos 1 2 (by decide)) hε2 m n hm hn
    refine ⟨?_, ?_⟩
    · refine Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 h1 h1) (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _ (add_pair_rearrange (s.approx n) _)
        (Q'.add_eqv_congr_left _ _ _ (half_add_half ε))
    · refine Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 h2 h2) (Q'.le_of_eqv ?_)
      exact Q'.eqv_trans _ _ _ (add_pair_rearrange (s.approx m) _)
        (Q'.add_eqv_congr_left _ _ _ (half_add_half ε))
  hMwmono := fun ε δ hδ hδε =>
    d.hMwmono _ _ (Q'.mul_pos hδ (Q'.invSucc_pos 1))
      (Q'.mul_le_mul_of_nonneg_right δ ε _ hδε (Q'.le_of_lt (Q'.invSucc_pos 1)))

/-- **Self-similarity (one step, `b = 1`).**  `(e^{−s})² ≈ e^{−(s+s)}` — i.e. with
`sep₀ = e^{−(s+s)}`, `sep₁ = e^{−s}`, we have `sep₀ ≈ sep₁²`, genuinely inhabiting
the CReal self-similar flow law via `expNegC` where the rational `polyFlow` failed.
Combines `cone_mul`, `mul_congr_left`, and the add law `expNegCD_add` (at `a=b=s`). -/
theorem self_similar_two (s : CReal) (d : ExpNegCData s)
    (hhalf : ∀ k, s.approx k + s.approx k ≤ 1) :
    CReal.Equiv (cpow (expNegCD s d) 2) (expNegCD (CReal.add s s) (addSelfData s d hhalf)) :=
  Equiv.trans (mul_congr_left (CRealAlg.cone_mul (expNegCD s d)))
    (expNegCD_add s s d d (addSelfData s d hhalf))

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CReal.mul_add
#print axioms ConstructiveReals.CReal.mul_sub
#print axioms ConstructiveReals.Q'.mul_nonneg_of_nonpos_nonpos
#print axioms ConstructiveReals.Q'.mul_nonpos_of_nonneg_nonpos
#print axioms ConstructiveReals.ExpNeg.term_sign
#print axioms ConstructiveReals.ExpNeg.oneSub_le_partialSum
#print axioms ConstructiveReals.ExpNeg.expNeg_cauchy_explicit
#print axioms ConstructiveReals.CReal.oneSub_le_expNeg
#print axioms ConstructiveReals.CReal.expNeg_contraction
#print axioms ConstructiveReals.ExpNeg.termDiff_le
#print axioms ConstructiveReals.ExpNeg.partialSumDiff_le
#print axioms ConstructiveReals.ExpNeg.sumBound_le_three
#print axioms ConstructiveReals.ExpNeg.expNegC

#print axioms ConstructiveReals.CReal.cpow
#print axioms ConstructiveReals.CReal.convergesTo_mul
#print axioms ConstructiveReals.CReal.expNegCD_add

#print axioms ConstructiveReals.CReal.mul_congr_left
#print axioms ConstructiveReals.CReal.self_similar_two
