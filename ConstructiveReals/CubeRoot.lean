/-
Constructive cube root `CReal.cbrtFrom` for positive rationals.

# Why this module exists

A positive real has a unique positive cube root.  This module builds it as a
genuine constructive `CReal` — with witnessed positivity, a proved defining
identity `(∛R)³ ≃ R`, and the order corollaries `0 < R < 1 ⟹ 0 < ∛R < 1` — so
that cube roots of rational data are honest constructive reals rather than
paper-only symbols.

This is **ordinary constructive real analysis** (a monotone located bisection on
the strictly increasing map `t ↦ t³` on `[0,∞)`), modeled on the existing
square-root construction.

# Construction (monotone located bisection)

For a positive rational `R`, maintain a rational bracket `[lo_n, hi_n]` with the
located invariant

    lo_n³ ≤ R ≤ hi_n³ ,   0 ≤ lo_n ≤ hi_n ,   hi_n − lo_n = (R+1)·2^{-n} .

Start `[0, R+1]` (`0³ = 0 ≤ R ≤ (R+1)³`).  Each step bisects at the midpoint
`m = (lo+hi)/2` and keeps the half-bracket still containing the crossing of
`t³ = R`, decided by the **decidable** test `m³ ≤ R`.  The lower endpoints
`lo_n` form the approximation sequence of the `CReal`; the geometric width
`(R+1)·2^{-n} → 0` gives the Cauchy modulus (carried as `Type`-level data via
`CReal.mulModulus`), and the cube identity follows from the squeeze
`lo_n³ ≤ R ≤ hi_n³` together with
`hi³ − lo³ = (hi−lo)(hi²+hi·lo+lo²) ≤ 3(R+1)²·(hi−lo) → 0`.

# Intended use

From `0 < R < 1` one gets a constructive `ρ = ∛R` with `0 < ρ < 1` and
`ρ·ρ·ρ ≃ R`.

# Axiom-gate (see README: axiom policy)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(the `Quot.sound` from `omega`/`Nat`).  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Sqrt
import ConstructiveReals.ExpAdd

namespace ConstructiveReals

namespace Q'

/-- `¬ (p ≤ q) → q ≤ p` on `Q'` (decidable `Int` trichotomy on numerators). -/
theorem le_of_not_le {p q : Q'} (h : ¬ (p ≤ q)) : q ≤ p := by
  show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
  have h' : ¬ (p.num * (q.den : Int) ≤ q.num * (p.den : Int)) := h
  exact Int.le_of_lt (Int.not_le.mp h')

/-- `min' p q ≤ p`. -/
theorem min_le_left {p q : Q'} : Q'.min' p q ≤ p := by
  unfold Q'.min'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact Q'.le_refl' p
  · rw [if_neg h]; exact le_of_not_le h

/-- `min' p q ≤ q`. -/
theorem min_le_right {p q : Q'} : Q'.min' p q ≤ q := by
  unfold Q'.min'
  by_cases h : p ≤ q
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Q'.le_refl' q

/-- Strict left multiplication by a positive factor: `0 < c → a < b → c*a < c*b`. -/
theorem mul_lt_mul_of_pos_left {a b c : Q'} (hc : (0 : Q') < c) (hab : a < b) :
    c * a < c * b := by
  show (c * a).num * ((c * b).den : Int) < (c * b).num * ((c * a).den : Int)
  rw [show (c * a).num = c.num * a.num from rfl, show (c * b).num = c.num * b.num from rfl,
      mul_den_cast c b, mul_den_cast c a]
  have hcn : 0 < c.num := num_pos_of_pos hc
  have habn : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  -- (c.num*a.num)*(c.den*b.den) < (c.num*b.num)*(c.den*a.den)
  have e1 : (c.num * a.num) * ((c.den : Int) * (b.den : Int))
          = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
  have e2 : (c.num * b.num) * ((c.den : Int) * (a.den : Int))
          = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
  rw [e1, e2]
  exact Int.mul_lt_mul_of_pos_left habn
    (Int.mul_pos hcn (by exact_mod_cast c.den_pos))

end Q'

namespace CReal

open Q' HalfPow

/-! ## The bisection bracket -/

/-- One bisection step for `∛R`: bisect `[lo,hi]` at the midpoint and keep the
half still bracketing the crossing of `t³ = R`. -/
def cbrtStep (R : Q') (s : Q' × Q') : Q' × Q' :=
  let lo := s.1
  let hi := s.2
  let m := half * (lo + hi)
  if m * m * m ≤ R then (m, hi) else (lo, m)

/-- The bisection bracket starting from `[L₀, U₀]`, then repeatedly bisected.
The initial bracket is supplied as data (a positive lower witness `L₀` with
`L₀³ ≤ R` keeps the lower endpoints uniformly positive, mirroring the
square-root construction's `L` witness). -/
def cbrtSeq (R L₀ U₀ : Q') : Nat → Q' × Q'
  | 0 => (L₀, U₀)
  | n + 1 => cbrtStep R (cbrtSeq R L₀ U₀ n)

/-- Lower endpoints — the approximation sequence of `∛R`. -/
def cbrtLo (R L₀ U₀ : Q') (n : Nat) : Q' := (cbrtSeq R L₀ U₀ n).1
/-- Upper endpoints. -/
def cbrtHi (R L₀ U₀ : Q') (n : Nat) : Q' := (cbrtSeq R L₀ U₀ n).2

@[simp] theorem cbrtLo_zero (R L₀ U₀ : Q') : cbrtLo R L₀ U₀ 0 = L₀ := rfl
@[simp] theorem cbrtHi_zero (R L₀ U₀ : Q') : cbrtHi R L₀ U₀ 0 = U₀ := rfl

theorem cbrtSeq_succ (R L₀ U₀ : Q') (n : Nat) :
    cbrtSeq R L₀ U₀ (n + 1) = cbrtStep R (cbrtSeq R L₀ U₀ n) := rfl

/-! ## Midpoint facts -/

/-- `lo ≤ ½(lo+hi)` when `lo ≤ hi`. -/
theorem le_mid {lo hi : Q'} (h : lo ≤ hi) : lo ≤ half * (lo + hi) := by
  -- lo ≃ half*(lo+lo) ≤ half*(lo+hi)
  have hdouble : (half * (lo + lo)).eqv lo := by
    -- half*(lo+lo) ≃ lo  (proved as in Sqrt.half_double)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half (lo + lo) ((Q'.ofNat 2) * lo)
        (Q'.eqv_symm ?_)) ?_
    · show ((Q'.ofNat 2) * lo).eqv (lo + lo)
      show ((Q'.ofNat 2) * lo).num * ((lo + lo).den : Int)
         = (lo + lo).num * (((Q'.ofNat 2) * lo).den : Int)
      have hn : ((Q'.ofNat 2) * lo).num = 2 * lo.num := rfl
      have hd : (((Q'.ofNat 2) * lo).den : Int) = (lo.den : Int) := by
        rw [mul_den_cast]
        show ((Q'.ofNat 2).den : Int) * (lo.den : Int) = (lo.den : Int)
        rw [show ((Q'.ofNat 2).den : Int) = 1 from rfl, Int.one_mul]
      have hxn : (lo + lo).num = lo.num * (lo.den : Int) + lo.num * (lo.den : Int) := rfl
      have hxd : ((lo + lo).den : Int) = (lo.den : Int) * (lo.den : Int) := add_den_cast lo lo
      rw [hn, hd, hxn, hxd]
      generalize lo.num = m; generalize (lo.den : Int) = E
      show (2 * m) * (E * E) = (m * E + m * E) * E
      rw [show m * E + m * E = 2 * (m * E) by omega, Int.mul_assoc 2 m (E * E),
          Int.mul_assoc 2 (m * E) E, Int.mul_assoc m E E]
    · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) lo)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (half * Q'.ofNat 2) 1 lo (by decide)) ?_
      exact Q'.one_mul_eqv lo
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hdouble) ?_
  exact Q'.mul_le_mul_of_nonneg_left (lo + lo) (lo + hi) half
    (Q'.add_le_add_left lo lo hi h) (by decide)

/-- `½(lo+hi) ≤ hi` when `lo ≤ hi`. -/
theorem mid_le {lo hi : Q'} (h : lo ≤ hi) : half * (lo + hi) ≤ hi := by
  have hdouble : (half * (hi + hi)).eqv hi := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left half (hi + hi) ((Q'.ofNat 2) * hi)
        (Q'.eqv_symm ?_)) ?_
    · show ((Q'.ofNat 2) * hi).eqv (hi + hi)
      show ((Q'.ofNat 2) * hi).num * ((hi + hi).den : Int)
         = (hi + hi).num * (((Q'.ofNat 2) * hi).den : Int)
      have hn : ((Q'.ofNat 2) * hi).num = 2 * hi.num := rfl
      have hd : (((Q'.ofNat 2) * hi).den : Int) = (hi.den : Int) := by
        rw [mul_den_cast]
        show ((Q'.ofNat 2).den : Int) * (hi.den : Int) = (hi.den : Int)
        rw [show ((Q'.ofNat 2).den : Int) = 1 from rfl, Int.one_mul]
      have hxn : (hi + hi).num = hi.num * (hi.den : Int) + hi.num * (hi.den : Int) := rfl
      have hxd : ((hi + hi).den : Int) = (hi.den : Int) * (hi.den : Int) := add_den_cast hi hi
      rw [hn, hd, hxn, hxd]
      generalize hi.num = m; generalize (hi.den : Int) = E
      show (2 * m) * (E * E) = (m * E + m * E) * E
      rw [show m * E + m * E = 2 * (m * E) by omega, Int.mul_assoc 2 m (E * E),
          Int.mul_assoc 2 (m * E) E, Int.mul_assoc m E E]
    · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) hi)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (half * Q'.ofNat 2) 1 hi (by decide)) ?_
      exact Q'.one_mul_eqv hi
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv hdouble)
  exact Q'.mul_le_mul_of_nonneg_left (lo + hi) (hi + hi) half
    (Q'.add_le_add_right lo hi hi h) (by decide)

/-! ## Width of the bracket -/

/-- The bracket width `hi_n − lo_n`. -/
def cbrtWidth (R L₀ U₀ : Q') (n : Nat) : Q' := cbrtHi R L₀ U₀ n + -(cbrtLo R L₀ U₀ n)

/-- `hi + -(½(lo+hi)) ≃ ½(hi + -lo)`. -/
theorem hi_sub_mid (lo hi : Q') :
    (hi + -(half * (lo + hi))).eqv (half * (hi + -lo)) := by
  have hm : (half * (lo + hi)).eqv (half * lo + half * hi) := mul_add_eqv half lo hi
  have hnegm : (-(half * (lo + hi))).eqv (-(half * lo) + -(half * hi)) :=
    Q'.eqv_trans _ _ _ (neg_eqv_congr _ _ hm) (neg_add_eqv (half * lo) (half * hi))
  have hhi : hi.eqv (half * hi + half * hi) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv half half hi)) ?_
    refine Q'.eqv_trans _ _ _ (mul_eqv_congr_right (half + half) 1 hi (by decide)) ?_
    exact one_mul_eqv hi
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right hi (half * hi + half * hi) (-(half * (lo + hi))) hhi) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left (half * hi + half * hi) (-(half * (lo + hi)))
      (-(half * lo) + -(half * hi)) hnegm) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (mul_add_eqv half hi (-lo))
      (add_eqv_congr_left (half * hi) (half * -lo) (-(half * lo)) (mul_neg_eqv half lo))))
  have hAABA : ∀ A B : Q', ((A + A) + (B + -A)).eqv (A + B) := by
    intro A B
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_left (A + A) (B + -A) (-A + B) (add_comm_eqv B (-A))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_assoc_eqv (A + A) (-A) B)) ?_
    refine add_eqv_congr_right ((A + A) + -A) A B ?_
    refine Q'.eqv_trans _ _ _ (add_assoc_eqv A A (-A)) ?_
    refine Q'.eqv_trans _ _ _ (add_eqv_congr_left A (A + -A) 0 (add_neg_self_eqv A)) ?_
    exact Q'.eqv_of_eq (add_zero' A)
  exact hAABA (half * hi) (-(half * lo))

/-- `(½(lo+hi)) + -lo ≃ ½(hi + -lo)`. -/
theorem mid_sub_lo (lo hi : Q') :
    ((half * (lo + hi)) + -lo).eqv (half * (hi + -lo)) := by
  have hm : (half * (lo + hi)).eqv (half * lo + half * hi) := mul_add_eqv half lo hi
  have hlo : lo.eqv (half * lo + half * lo) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv half half lo)) ?_
    refine Q'.eqv_trans _ _ _ (mul_eqv_congr_right (half + half) 1 lo (by decide)) ?_
    exact one_mul_eqv lo
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right (half * (lo + hi)) (half * lo + half * hi) (-lo) hm) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left (half * lo + half * hi) (-lo) (-(half * lo) + -(half * lo))
      (Q'.eqv_trans _ _ _ (neg_eqv_congr _ _ hlo) (neg_add_eqv (half * lo) (half * lo)))) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ (mul_add_eqv half hi (-lo))
      (add_eqv_congr_left (half * hi) (half * -lo) (-(half * lo)) (mul_neg_eqv half lo))))
  have hPQ : ∀ P Q : Q', ((P + Q) + (-P + -P)).eqv (Q + -P) := by
    intro P Q
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_right (P + Q) (Q + P) (-P + -P) (add_comm_eqv P Q)) ?_
    refine Q'.eqv_trans _ _ _ (add_assoc_eqv Q P (-P + -P)) ?_
    refine add_eqv_congr_left Q (P + (-P + -P)) (-P) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_assoc_eqv P (-P) (-P))) ?_
    refine Q'.eqv_trans _ _ _ (add_eqv_congr_right (P + -P) 0 (-P) (add_neg_self_eqv P)) ?_
    exact QPoly.q_zero_add_eqv (-P)
  exact hPQ (half * lo) (half * hi)

/-- The width halves at each step: `width(n+1) ≃ ½·width(n)`. -/
theorem cbrtWidth_succ (R L₀ U₀ : Q') (n : Nat) :
    (cbrtWidth R L₀ U₀ (n + 1)).eqv (half * cbrtWidth R L₀ U₀ n) := by
  show (cbrtHi R L₀ U₀ (n + 1) + -(cbrtLo R L₀ U₀ (n + 1))).eqv
       (half * (cbrtHi R L₀ U₀ n + -(cbrtLo R L₀ U₀ n)))
  rw [show cbrtHi R L₀ U₀ (n + 1) = (cbrtStep R (cbrtSeq R L₀ U₀ n)).2 from rfl,
      show cbrtLo R L₀ U₀ (n + 1) = (cbrtStep R (cbrtSeq R L₀ U₀ n)).1 from rfl]
  show ((if half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2))
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)) ≤ R
          then (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2), (cbrtSeq R L₀ U₀ n).2)
          else ((cbrtSeq R L₀ U₀ n).1, half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2))).2
        + -(if half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2))
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)) ≤ R
          then (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2), (cbrtSeq R L₀ U₀ n).2)
          else ((cbrtSeq R L₀ U₀ n).1, half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2))).1).eqv
       (half * ((cbrtSeq R L₀ U₀ n).2 + -(cbrtSeq R L₀ U₀ n).1))
  by_cases hcase : half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2))
            * (half * ((cbrtSeq R L₀ U₀ n).1 + (cbrtSeq R L₀ U₀ n).2)) ≤ R
  · rw [if_pos hcase]
    exact hi_sub_mid (cbrtSeq R L₀ U₀ n).1 (cbrtSeq R L₀ U₀ n).2
  · rw [if_neg hcase]
    exact mid_sub_lo (cbrtSeq R L₀ U₀ n).1 (cbrtSeq R L₀ U₀ n).2

/-- `width n ≃ (U₀ − L₀)·½ⁿ`. -/
theorem cbrtWidth_eq_geom (R L₀ U₀ : Q') :
    ∀ n, (cbrtWidth R L₀ U₀ n).eqv ((U₀ + -L₀) * half ^ n)
  | 0 => by
      show (cbrtHi R L₀ U₀ 0 + -(cbrtLo R L₀ U₀ 0)).eqv ((U₀ + -L₀) * half ^ 0)
      rw [cbrtHi_zero, cbrtLo_zero, Q'.pow_zero]
      exact Q'.eqv_symm (mul_one_eqv (U₀ + -L₀))
  | n + 1 => by
      refine Q'.eqv_trans _ _ _ (cbrtWidth_succ R L₀ U₀ n) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_congr_left half (cbrtWidth R L₀ U₀ n) ((U₀ + -L₀) * half ^ n)
          (cbrtWidth_eq_geom R L₀ U₀ n)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_assoc_eqv half (U₀ + -L₀) (half ^ n))) ?_
      refine Q'.eqv_trans _ _ _
        (mul_eqv_congr_right (half * (U₀ + -L₀)) ((U₀ + -L₀) * half) (half ^ n)
          (mul_comm_eqv half (U₀ + -L₀))) ?_
      refine Q'.eqv_trans _ _ _ (mul_assoc_eqv (U₀ + -L₀) half (half ^ n)) ?_
      rw [Q'.pow_succ]
      exact Q'.eqv_refl _

/-! ## The initial-bracket data and the located invariant -/

/-- A valid initial bracket `[L₀, U₀]` for `∛R`: positive lower witness with
`L₀³ ≤ R ≤ U₀³` and `L₀ ≤ U₀`. -/
structure CbrtInit (R L₀ U₀ : Q') : Prop where
  loPos : (0 : Q') < L₀
  loCube : L₀ * L₀ * L₀ ≤ R
  RleHiCube : R ≤ U₀ * U₀ * U₀
  loLeHi : L₀ ≤ U₀

/-- The located bracket invariant at stage `n` (lower endpoints stay `≥ L₀`). -/
def CbrtInv (R L₀ U₀ : Q') (n : Nat) : Prop :=
  L₀ ≤ cbrtLo R L₀ U₀ n ∧ cbrtLo R L₀ U₀ n ≤ cbrtHi R L₀ U₀ n ∧
    cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n ≤ R ∧
    R ≤ cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n

/-- The invariant holds at every stage (induction). -/
theorem cbrtInv (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) :
    ∀ n, CbrtInv R L₀ U₀ n
  | 0 => ⟨Q'.le_refl' _, hinit.loLeHi, hinit.loCube, hinit.RleHiCube⟩
  | n + 1 => by
      obtain ⟨hlo, hle, hlo3, hhi3⟩ := cbrtInv R L₀ U₀ hinit n
      have hlm : cbrtLo R L₀ U₀ n ≤ half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n) := le_mid hle
      have hmh : half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n) ≤ cbrtHi R L₀ U₀ n := mid_le hle
      have hmlo : L₀ ≤ half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n) := Q'.le_trans' _ _ _ hlo hlm
      show CbrtInv R L₀ U₀ (n + 1)
      have hloeq : cbrtLo R L₀ U₀ (n + 1) =
          (if half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
              * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
              * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
            then (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n), cbrtHi R L₀ U₀ n)
            else (cbrtLo R L₀ U₀ n, half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))).1 := rfl
      have hhieq : cbrtHi R L₀ U₀ (n + 1) =
          (if half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
              * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
              * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
            then (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n), cbrtHi R L₀ U₀ n)
            else (cbrtLo R L₀ U₀ n, half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))).2 := rfl
      by_cases hc : half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
      · have hlo' : cbrtLo R L₀ U₀ (n + 1) = half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n) := by
          rw [hloeq, if_pos hc]
        have hhi' : cbrtHi R L₀ U₀ (n + 1) = cbrtHi R L₀ U₀ n := by rw [hhieq, if_pos hc]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlo']; exact hmlo
        · rw [hlo', hhi']; exact hmh
        · rw [hlo']; exact hc
        · rw [hhi']; exact hhi3
      · have hRle : R ≤ half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
            * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
            * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) := Q'.le_of_not_le hc
        have hlo' : cbrtLo R L₀ U₀ (n + 1) = cbrtLo R L₀ U₀ n := by rw [hloeq, if_neg hc]
        have hhi' : cbrtHi R L₀ U₀ (n + 1) = half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n) := by
          rw [hhieq, if_neg hc]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlo']; exact hlo
        · rw [hlo', hhi']; exact hlm
        · rw [hlo']; exact hlo3
        · rw [hhi']; exact hRle

/-! ### Invariant corollaries -/

theorem cbrtLo_ge_L₀ (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    L₀ ≤ cbrtLo R L₀ U₀ n := (cbrtInv R L₀ U₀ hinit n).1

theorem cbrtLo_le_cbrtHi (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    cbrtLo R L₀ U₀ n ≤ cbrtHi R L₀ U₀ n := (cbrtInv R L₀ U₀ hinit n).2.1

theorem cbrtLo_cube_le (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n ≤ R :=
  (cbrtInv R L₀ U₀ hinit n).2.2.1

theorem R_le_cbrtHi_cube (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    R ≤ cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n :=
  (cbrtInv R L₀ U₀ hinit n).2.2.2

theorem cbrtLo_nonneg (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    (0 : Q') ≤ cbrtLo R L₀ U₀ n :=
  Q'.le_trans' _ _ _ (Q'.le_of_lt hinit.loPos) (cbrtLo_ge_L₀ R L₀ U₀ hinit n)

/-! ### Monotonicity of the endpoints -/

/-- `lo` is nondecreasing in one step. -/
theorem cbrtLo_le_succ (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    cbrtLo R L₀ U₀ n ≤ cbrtLo R L₀ U₀ (n + 1) := by
  have hle := cbrtLo_le_cbrtHi R L₀ U₀ hinit n
  have hloeq : cbrtLo R L₀ U₀ (n + 1) =
      (if half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
        then (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n), cbrtHi R L₀ U₀ n)
        else (cbrtLo R L₀ U₀ n, half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))).1 := rfl
  by_cases hc : half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
      * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
      * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
  · rw [hloeq, if_pos hc]; exact le_mid hle
  · rw [hloeq, if_neg hc]; exact Q'.le_refl' _

/-- `hi` is nonincreasing in one step. -/
theorem cbrtHi_succ_le (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    cbrtHi R L₀ U₀ (n + 1) ≤ cbrtHi R L₀ U₀ n := by
  have hle := cbrtLo_le_cbrtHi R L₀ U₀ hinit n
  have hhieq : cbrtHi R L₀ U₀ (n + 1) =
      (if half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
          * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
        then (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n), cbrtHi R L₀ U₀ n)
        else (cbrtLo R L₀ U₀ n, half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))).2 := rfl
  by_cases hc : half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)
      * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n))
      * (half * (cbrtLo R L₀ U₀ n + cbrtHi R L₀ U₀ n)) ≤ R
  · rw [hhieq, if_pos hc]; exact Q'.le_refl' _
  · rw [hhieq, if_neg hc]; exact mid_le hle

/-- `lo` monotone: `lo n ≤ lo (n+d)`. -/
theorem cbrtLo_mono_add (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    ∀ d, cbrtLo R L₀ U₀ n ≤ cbrtLo R L₀ U₀ (n + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ (cbrtLo_mono_add R L₀ U₀ hinit n d) ?_
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      exact cbrtLo_le_succ R L₀ U₀ hinit (n + d)

theorem cbrtLo_mono (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) {n m : Nat} (h : n ≤ m) :
    cbrtLo R L₀ U₀ n ≤ cbrtLo R L₀ U₀ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact cbrtLo_mono_add R L₀ U₀ hinit n d

/-- `hi` antitone: `hi (n+d) ≤ hi n`. -/
theorem cbrtHi_anti_add (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    ∀ d, cbrtHi R L₀ U₀ (n + d) ≤ cbrtHi R L₀ U₀ n
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ ?_ (cbrtHi_anti_add R L₀ U₀ hinit n d)
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      exact cbrtHi_succ_le R L₀ U₀ hinit (n + d)

theorem cbrtHi_anti (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) {n m : Nat} (h : n ≤ m) :
    cbrtHi R L₀ U₀ m ≤ cbrtHi R L₀ U₀ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact cbrtHi_anti_add R L₀ U₀ hinit n d

/-! ## The Cauchy modulus -/

/-- The width bound `U₀ − L₀ ≥ 0`. -/
theorem width0_nonneg {R L₀ U₀ : Q'} (hinit : CbrtInit R L₀ U₀) : (0 : Q') ≤ U₀ + -L₀ := by
  have := Q'.add_le_add_right L₀ U₀ (-L₀) hinit.loLeHi
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv L₀)) this

/-- The Cauchy modulus (Type-level data): a stage `N` past which the width is
`≤ ε`.  `N = δ.den` for the `δ` solving `(U₀ − L₀)·δ ≤ ε`. -/
def cbrtModulus (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (ε : Q') (hε : (0 : Q') < ε) : Nat :=
  (mulModulus (U₀ + -L₀) ε (width0_nonneg hinit) hε).1.den

/-- `width (cbrtModulus …) ≤ ε`. -/
theorem cbrtWidth_modulus_le (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀)
    (ε : Q') (hε : (0 : Q') < ε) :
    cbrtWidth R L₀ U₀ (cbrtModulus R L₀ U₀ hinit ε hε) ≤ ε := by
  have hWnn : (0 : Q') ≤ U₀ + -L₀ := width0_nonneg hinit
  let md := mulModulus (U₀ + -L₀) ε hWnn hε
  have hδpos : (0 : Q') < md.1 := md.2.1
  have hδle : (U₀ + -L₀) * md.1 ≤ ε := md.2.2
  show cbrtWidth R L₀ U₀ md.1.den ≤ ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (cbrtWidth_eq_geom R L₀ U₀ md.1.den)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (half ^ md.1.den) md.1 (U₀ + -L₀)
      (HalfPow.pow_half_le md.1 hδpos) hWnn) ?_
  exact hδle

/-- The bracket-width controls how far apart two lower endpoints past `N` can be:
for `N ≤ p` and `N ≤ q`, `lo p ≤ lo q + width N`. -/
theorem cbrtLo_close (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) {N p q : Nat}
    (hNp : N ≤ p) (hNq : N ≤ q) :
    cbrtLo R L₀ U₀ p ≤ cbrtLo R L₀ U₀ q + cbrtWidth R L₀ U₀ N := by
  have h1 : cbrtLo R L₀ U₀ p ≤ cbrtHi R L₀ U₀ N :=
    Q'.le_trans' _ _ _ (cbrtLo_le_cbrtHi R L₀ U₀ hinit p) (cbrtHi_anti R L₀ U₀ hinit hNp)
  have h2 : cbrtLo R L₀ U₀ N ≤ cbrtLo R L₀ U₀ q := cbrtLo_mono R L₀ U₀ hinit hNq
  have h3 : cbrtHi R L₀ U₀ N ≤ cbrtLo R L₀ U₀ q + cbrtWidth R L₀ U₀ N := by
    show cbrtHi R L₀ U₀ N ≤ cbrtLo R L₀ U₀ q + (cbrtHi R L₀ U₀ N + -(cbrtLo R L₀ U₀ N))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_sub_cancel_eqv (cbrtHi R L₀ U₀ N) (cbrtLo R L₀ U₀ N))) ?_
    exact Q'.add_le_add_right (cbrtLo R L₀ U₀ N) (cbrtLo R L₀ U₀ q)
      (cbrtHi R L₀ U₀ N + -(cbrtLo R L₀ U₀ N)) h2
  exact Q'.le_trans' _ _ _ h1 h3

/-! ## The constructive cube root as a `CReal` -/

/-- **The constructive cube root** `∛R` as a `CReal`, for a positive rational
`R` with a valid initial bracket `[L₀, U₀]`.  Approximations are the lower
endpoints `cbrtLo`; the Cauchy modulus is `cbrtModulus`. -/
def cbrtFromInit (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) : CReal where
  approx n := cbrtLo R L₀ U₀ n
  cauchy := by
    intro ε hε
    refine ⟨cbrtModulus R L₀ U₀ hinit ε hε, fun p q hp hq => ?_⟩
    have hwle : cbrtWidth R L₀ U₀ (cbrtModulus R L₀ U₀ hinit ε hε) ≤ ε :=
      cbrtWidth_modulus_le R L₀ U₀ hinit ε hε
    refine ⟨?_, ?_⟩
    · exact Q'.le_trans' _ _ _ (cbrtLo_close R L₀ U₀ hinit hp hq)
        (Q'.add_le_add_left (cbrtLo R L₀ U₀ q)
          (cbrtWidth R L₀ U₀ (cbrtModulus R L₀ U₀ hinit ε hε)) ε hwle)
    · exact Q'.le_trans' _ _ _ (cbrtLo_close R L₀ U₀ hinit hq hp)
        (Q'.add_le_add_left (cbrtLo R L₀ U₀ p)
          (cbrtWidth R L₀ U₀ (cbrtModulus R L₀ U₀ hinit ε hε)) ε hwle)

@[simp] theorem cbrtFromInit_approx (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    (cbrtFromInit R L₀ U₀ hinit).approx n = cbrtLo R L₀ U₀ n := rfl

/-! ### Positivity -/

/-- `∛R` is strictly positive (witnessed by the rational lower bound `L₀`). -/
theorem cbrtFromInit_isPositive (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) :
    CReal.IsPositive (cbrtFromInit R L₀ U₀ hinit) :=
  CReal.isPositive_of_approx_ge hinit.loPos (fun n => cbrtLo_ge_L₀ R L₀ U₀ hinit n)

/-! ### The cube identity `(∛R)³ ≃ R`

The cube CReal is `mul (mul x x) x`, with approximations `(lo·lo)·lo`.  Squeeze
`lo³ ≤ R ≤ hi³` with `hi³ − lo³ = (hi−lo)(hi²+hi·lo+lo²) ≤ 3U₀²·(hi−lo) → 0`. -/

/-- The cube difference factorization `(b − a)(b²+ba+a²) ≃ b³ − a³`. -/
theorem cube_diff (a b : Q') :
    ((b + -a) * (b * b + b * a + a * a)).eqv (b * b * b + -(a * a * a)) := by
  -- expand (b + -a)*S = b*S + (-a)*S = b*S + -(a*S)
  refine Q'.eqv_trans _ _ _ (add_mul_eqv b (-a) (b * b + b * a + a * a)) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left (b * (b * b + b * a + a * a)) ((-a) * (b * b + b * a + a * a))
      (-(a * (b * b + b * a + a * a))) (neg_mul_eqv a (b * b + b * a + a * a))) ?_
  -- b*S ≃ b*b*b + b*b*a + b*a*a   ; a*S ≃ a*b*b + a*b*a + a*a*a
  have hbS : (b * (b * b + b * a + a * a)).eqv
      ((b * (b * b) + b * (b * a)) + b * (a * a)) := by
    refine Q'.eqv_trans _ _ _ (mul_add_eqv b (b * b + b * a) (a * a)) ?_
    exact add_eqv_congr_right (b * (b * b + b * a)) (b * (b * b) + b * (b * a)) (b * (a * a))
      (mul_add_eqv b (b * b) (b * a))
  have haS : (a * (b * b + b * a + a * a)).eqv
      ((a * (b * b) + a * (b * a)) + a * (a * a)) := by
    refine Q'.eqv_trans _ _ _ (mul_add_eqv a (b * b + b * a) (a * a)) ?_
    exact add_eqv_congr_right (a * (b * b + b * a)) (a * (b * b) + a * (b * a)) (a * (a * a))
      (mul_add_eqv a (b * b) (b * a))
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right (b * (b * b + b * a + a * a))
      ((b * (b * b) + b * (b * a)) + b * (a * a)) (-(a * (b * b + b * a + a * a))) hbS) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left ((b * (b * b) + b * (b * a)) + b * (a * a))
      (-(a * (b * b + b * a + a * a)))
      (-((a * (b * b) + a * (b * a)) + a * (a * a))) (neg_eqv_congr _ _ haS)) ?_
  -- now a pure additive-cancellation identity in the 6 monomials.
  -- target: b*b*b + -(a*a*a).  cross terms b*(b*a) and b*(a*a)=a*(b*a) ... cancel
  -- We normalize using num-level equality through `q_eqv_of_sub_zero` is messy;
  -- instead identify the surviving/cancelling pairs explicitly.
  -- b*(b*b) ≃ b*b*b ; a*(a*a) ≃ a*a*a ; b*(b*a) cancels a*(b*b); b*(a*a) cancels a*(b*a).
  have e_bbb : (b * (b * b)).eqv (b * b * b) := Q'.eqv_symm (mul_assoc_eqv b b b)
  have e_aaa : (a * (a * a)).eqv (a * a * a) := Q'.eqv_symm (mul_assoc_eqv a a a)
  have e_cross1 : (b * (b * a)).eqv (a * (b * b)) := by
    -- b*(b*a) ≃ (b*b)*a ≃ a*(b*b)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_assoc_eqv b b a)) (mul_comm_eqv (b * b) a)
  have e_cross2 : (b * (a * a)).eqv (a * (b * a)) := by
    -- b*(a*a) ≃ (b*a)*a ≃ a*(b*a)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (mul_assoc_eqv b a a)) ?_
    exact mul_comm_eqv (b * a) a
  -- Notation: P = b*(b*b), Qm = b*(b*a), Rr = b*(a*a), X = a*(b*b), Y = a*(b*a), Z = a*(a*a)
  -- LHS = ((P + Qm) + Rr) + -((X + Y) + Z) ; Qm ≃ X, Rr ≃ Y, P ≃ b³, Z ≃ a³.
  -- Step 1: rewrite the first summand ((P+Qm)+Rr) ≃ (b³ + X) + Y.
  have hfirst :
      (((b * (b * b)) + (b * (b * a))) + (b * (a * a))).eqv
        (((b * b * b) + (a * (b * b))) + (a * (b * a))) := by
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_right ((b * (b * b)) + (b * (b * a))) ((b * b * b) + (a * (b * b)))
        (b * (a * a)) ?_) ?_
    · exact Q'.eqv_trans _ _ _
        (add_eqv_congr_right (b * (b * b)) (b * b * b) (b * (b * a)) e_bbb)
        (add_eqv_congr_left (b * b * b) (b * (b * a)) (a * (b * b)) e_cross1)
    · exact add_eqv_congr_left ((b * b * b) + (a * (b * b))) (b * (a * a)) (a * (b * a)) e_cross2
  -- Step 2: rewrite the negated summand -((X+Y)+Z) ≃ -((X+Y)+a³).
  have hsecond :
      (-(((a * (b * b)) + (a * (b * a))) + (a * (a * a)))).eqv
        (-(((a * (b * b)) + (a * (b * a))) + (a * a * a))) :=
    neg_eqv_congr _ _
      (add_eqv_congr_left ((a * (b * b)) + (a * (b * a))) (a * (a * a)) (a * a * a) e_aaa)
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right (((b * (b * b)) + (b * (b * a))) + (b * (a * a)))
      (((b * b * b) + (a * (b * b))) + (a * (b * a)))
      (-(((a * (b * b)) + (a * (b * a))) + (a * (a * a)))) hfirst) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left (((b * b * b) + (a * (b * b))) + (a * (b * a)))
      (-(((a * (b * b)) + (a * (b * a))) + (a * (a * a))))
      (-(((a * (b * b)) + (a * (b * a))) + (a * a * a))) hsecond) ?_
  -- Now ((b³+X)+Y) + -((X+Y)+a³) ≃ b³ + -a³, with S = X+Y.
  -- ((b³+X)+Y) ≃ b³ + (X+Y) = b³ + S
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right (((b * b * b) + (a * (b * b))) + (a * (b * a)))
      ((b * b * b) + ((a * (b * b)) + (a * (b * a))))
      (-(((a * (b * b)) + (a * (b * a))) + (a * a * a)))
      (add_assoc_eqv (b * b * b) (a * (b * b)) (a * (b * a)))) ?_
  -- (b³ + S) + -(S + a³) ≃ b³ + (S + -(S + a³)) ≃ b³ + -a³
  refine Q'.eqv_trans _ _ _
    (add_assoc_eqv (b * b * b) ((a * (b * b)) + (a * (b * a)))
      (-(((a * (b * b)) + (a * (b * a))) + (a * a * a)))) ?_
  refine add_eqv_congr_left (b * b * b)
    (((a * (b * b)) + (a * (b * a))) + -(((a * (b * b)) + (a * (b * a))) + (a * a * a)))
    (-(a * a * a)) ?_
  -- S + -(S + a³) ≃ -a³
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_left ((a * (b * b)) + (a * (b * a)))
      (-(((a * (b * b)) + (a * (b * a))) + (a * a * a)))
      (-((a * (b * b)) + (a * (b * a))) + -(a * a * a))
      (neg_add_eqv ((a * (b * b)) + (a * (b * a))) (a * a * a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (add_assoc_eqv ((a * (b * b)) + (a * (b * a)))
      (-((a * (b * b)) + (a * (b * a)))) (-(a * a * a)))) ?_
  refine Q'.eqv_trans _ _ _
    (add_eqv_congr_right (((a * (b * b)) + (a * (b * a))) + -((a * (b * b)) + (a * (b * a))))
      0 (-(a * a * a)) (add_neg_self_eqv ((a * (b * b)) + (a * (b * a))))) ?_
  exact QPoly.q_zero_add_eqv (-(a * a * a))

/-- `0 ≤ a ≤ b ≤ U ⟹ b³ − a³ ≤ ((U²+U²)+U²)·(b − a)`. -/
theorem cube_diff_le {a b U : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) (hbU : b ≤ U) :
    b * b * b + -(a * a * a) ≤ ((U * U + U * U) + U * U) * (b + -a) := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
  have haU : a ≤ U := Q'.le_trans' _ _ _ hab hbU
  have hUnn : (0 : Q') ≤ U := Q'.le_trans' _ _ _ hb hbU
  have hdnn : (0 : Q') ≤ b + -a := by
    have := Q'.add_le_add_right a b (-a) hab
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) this
  -- b³ − a³ ≃ (b−a)·(b²+ba+a²) ≤ (b−a)·3U² = 3U²·(b−a)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cube_diff a b)) ?_
  -- (b−a)·S ≤ (b−a)·3U²  then commute
  have hSle : (b * b + b * a + a * a) ≤ (U * U + U * U) + U * U := by
    refine Q'.add_le_add ?_ (Q'.mul_le_mul_of_nonneg haU haU hUnn ha)
    exact Q'.add_le_add (Q'.mul_le_mul_of_nonneg hbU hbU hUnn hb)
      (Q'.mul_le_mul_of_nonneg hbU haU hUnn ha)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (b * b + b * a + a * a) ((U * U + U * U) + U * U)
      (b + -a) hSle hdnn) ?_
  exact Q'.le_of_eqv (mul_comm_eqv (b + -a) ((U * U + U * U) + U * U))

/-- `R − lo³ ≤ ((U₀²+U₀²)+U₀²)·width n`. -/
theorem R_sub_loCube_le (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) (n : Nat) :
    R + -(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n)
      ≤ ((U₀ * U₀ + U₀ * U₀) + U₀ * U₀) * cbrtWidth R L₀ U₀ n := by
  -- R − lo³ ≤ hi³ − lo³ ≤ 3U₀²·(hi − lo) = 3U₀²·width
  have hRle : R ≤ cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n :=
    R_le_cbrtHi_cube R L₀ U₀ hinit n
  have h1 : R + -(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n)
      ≤ cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n * cbrtHi R L₀ U₀ n
        + -(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n) :=
    Q'.add_le_add_right R _ _ hRle
  refine Q'.le_trans' _ _ _ h1 ?_
  have hHiU : cbrtHi R L₀ U₀ n ≤ U₀ := by
    have := cbrtHi_anti R L₀ U₀ hinit (Nat.zero_le n)
    rwa [cbrtHi_zero] at this
  exact cube_diff_le (cbrtLo_nonneg R L₀ U₀ hinit n) (cbrtLo_le_cbrtHi R L₀ U₀ hinit n) hHiU

/-- The width is decreasing: `N ≤ n → width n ≤ width N`. -/
theorem cbrtWidth_antitone (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) {N n : Nat}
    (h : N ≤ n) : cbrtWidth R L₀ U₀ n ≤ cbrtWidth R L₀ U₀ N := by
  show cbrtHi R L₀ U₀ n + -(cbrtLo R L₀ U₀ n) ≤ cbrtHi R L₀ U₀ N + -(cbrtLo R L₀ U₀ N)
  refine Q'.add_le_add (cbrtHi_anti R L₀ U₀ hinit h) ?_
  exact Q'.neg_le_neg (cbrtLo_mono R L₀ U₀ hinit h)

/-! ### The defining identity `(∛R)³ ≃ R` -/

/-- **`(∛R)³ ≃ R`.**  The triple product `ρ·ρ·ρ` is `Equiv` to the constant
`ofQ' R`. -/
theorem cbrtFromInit_cube_equiv (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀) :
    CReal.Equiv
      (CReal.mul (CReal.mul (cbrtFromInit R L₀ U₀ hinit) (cbrtFromInit R L₀ U₀ hinit))
        (cbrtFromInit R L₀ U₀ hinit))
      (CReal.ofQ' R) := by
  intro ε hε
  -- coefficient C = 3U₀² ≥ 0
  have hsq : (0 : Q') ≤ U₀ * U₀ := SumOfSquares.q_mul_self_nonneg U₀
  have hCnn : (0 : Q') ≤ (U₀ * U₀ + U₀ * U₀) + U₀ * U₀ := by
    have h2 : (0 : Q') ≤ U₀ * U₀ + U₀ * U₀ :=
      Q'.le_trans' _ _ _ hsq (Q'.add_le_self_of_nonneg (U₀ * U₀) (U₀ * U₀) hsq)
    exact Q'.le_trans' _ _ _ h2 (Q'.add_le_self_of_nonneg (U₀ * U₀ + U₀ * U₀) (U₀ * U₀) hsq)
  -- δ with C·δ ≤ ε
  obtain ⟨δ, hδpos, hδle⟩ := CReal.exists_mul_le hCnn hε
  -- N with width N ≤ δ
  refine ⟨cbrtModulus R L₀ U₀ hinit δ hδpos, fun n hn => ?_⟩
  have hwN : cbrtWidth R L₀ U₀ (cbrtModulus R L₀ U₀ hinit δ hδpos) ≤ δ :=
    cbrtWidth_modulus_le R L₀ U₀ hinit δ hδpos
  have hwn : cbrtWidth R L₀ U₀ n ≤ δ :=
    Q'.le_trans' _ _ _ (cbrtWidth_antitone R L₀ U₀ hinit hn) hwN
  -- A_n := (lo*lo)*lo = lo³ ; want A_n ≤ R + ε and R ≤ A_n + ε
  show ((cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n) * cbrtLo R L₀ U₀ n ≤ R + ε)
     ∧ (R ≤ (cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n) * cbrtLo R L₀ U₀ n + ε)
  refine ⟨?_, ?_⟩
  · -- lo³ ≤ R ≤ R + ε
    exact Q'.le_trans' _ _ _ (cbrtLo_cube_le R L₀ U₀ hinit n)
      (Q'.add_le_self_of_nonneg R ε (Q'.le_of_lt hε))
  · -- R ≤ lo³ + ε  :  R − lo³ ≤ C·width n ≤ C·δ ≤ ε
    have hbound : R + -(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n)
        ≤ ((U₀ * U₀ + U₀ * U₀) + U₀ * U₀) * cbrtWidth R L₀ U₀ n :=
      R_sub_loCube_le R L₀ U₀ hinit n
    have hCw : ((U₀ * U₀ + U₀ * U₀) + U₀ * U₀) * cbrtWidth R L₀ U₀ n ≤ ε :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left (cbrtWidth R L₀ U₀ n) δ
          ((U₀ * U₀ + U₀ * U₀) + U₀ * U₀) hwn hCnn) hδle
    -- R − lo³ ≤ ε  ⟹  R ≤ lo³ + ε
    have hsub : R + -(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n) ≤ ε :=
      Q'.le_trans' _ _ _ hbound hCw
    -- (R − lo³) + lo³ ≤ ε + lo³ ; LHS ≃ R, RHS ≃ lo³ + ε
    have h2 := Q'.add_le_add_right _ ε
      (cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n) hsub
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv ?_))
    · -- (R + -lo³) + lo³ ≃ R
      refine Q'.eqv_trans _ _ _ (add_assoc_eqv R
        (-(cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n))
        (cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n)) ?_
      refine Q'.eqv_trans _ _ _ (add_eqv_congr_left R _ 0
        (Q'.neg_add_self_eqv (cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n))) ?_
      exact Q'.eqv_of_eq (add_zero' R)
    · -- ε + lo³ ≃ lo³ + ε
      exact add_comm_eqv ε (cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n * cbrtLo R L₀ U₀ n)

/-! ### Cube monotonicity and order corollaries -/

/-- Strict cube monotonicity: `0 ≤ y → y < x → y³ < x³`. -/
theorem cube_lt_cube_of_lt {x y : Q'} (hy : (0 : Q') ≤ y) (hyx : y < x) :
    y * y * y < x * x * x := by
  have hx : (0 : Q') < x := Q'.lt_of_le_of_lt hy hyx
  have hxnn : (0 : Q') ≤ x := Q'.le_of_lt hx
  have hyle : y ≤ x := Q'.le_of_lt hyx
  -- y*y ≤ x*x
  have hyy : y * y ≤ x * x := Q'.mul_le_mul_of_nonneg hyle hyle hxnn hy
  -- y*y*y ≤ x*x*y
  have h1 : y * y * y ≤ x * x * y :=
    Q'.mul_le_mul_of_nonneg_right (y * y) (x * x) y hyy hy
  -- x*x*y < x*x*x  (strict, x*x > 0)
  have hxx : (0 : Q') < x * x := Q'.mul_pos hx hx
  have h2 : (x * x) * y < (x * x) * x := Q'.mul_lt_mul_of_pos_left hxx hyx
  exact Q'.lt_of_le_of_lt h1 h2

/-- Cube reflects `≤`: `0 ≤ x → 0 ≤ y → x³ ≤ y³ → x ≤ y`. -/
theorem le_of_cube_le_cube {x y : Q'} (_hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y)
    (h : x * x * x ≤ y * y * y) : x ≤ y := by
  show x.num * (y.den : Int) ≤ y.num * (x.den : Int)
  refine Int.not_lt.mp (fun hlt0 => ?_)
  -- hlt0 : y.num*x.den < x.num*y.den  is exactly  y < x
  have hyx : y < x := hlt0
  have hcube : y * y * y < x * x * x := cube_lt_cube_of_lt hy hyx
  -- x³ ≤ y³ and y³ < x³ : contradiction
  exact absurd h (Int.not_le.mpr hcube)

/-- **`∛R ≤ c` when `R ≤ c³`** (cube order-reflection), as `CReal.leRat (∛R) c`. -/
theorem cbrtFromInit_leRat_of_cube (R L₀ U₀ : Q') (hinit : CbrtInit R L₀ U₀)
    (c : Q') (hc : (0 : Q') ≤ c) (hRc : R ≤ c * c * c) :
    CReal.leRat (cbrtFromInit R L₀ U₀ hinit) c := by
  refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
  show cbrtLo R L₀ U₀ n ≤ c
  -- lo n ≥ 0, c ≥ 0, lo³ ≤ R ≤ c³ ⟹ lo ≤ c
  refine le_of_cube_le_cube (cbrtLo_nonneg R L₀ U₀ hinit n) hc ?_
  exact Q'.le_trans' _ _ _ (cbrtLo_cube_le R L₀ U₀ hinit n) hRc

/-! ## A canonical bracket and the user-facing cube root -/

/-- `R ≤ (R+1)³` for `0 ≤ R`. -/
theorem le_succ_cube {R : Q'} (hR : (0 : Q') ≤ R) :
    R ≤ (R + 1) * (R + 1) * (R + 1) := by
  have h1 : (1 : Q') ≤ R + 1 := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.add_le_add_right 0 R 1 hR)
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 1))
  have hR1nn : (0 : Q') ≤ R + 1 := Q'.le_trans' _ _ _ (by decide) h1
  have hsq : (1 : Q') ≤ (R + 1) * (R + 1) := by
    refine Q'.le_trans' _ _ _ (show (1 : Q') ≤ (1 : Q') * 1 by decide) ?_
    exact Q'.mul_le_mul_of_nonneg h1 h1 hR1nn (by decide)
  have hRle : R ≤ R + 1 := Q'.add_le_self_of_nonneg R 1 (by decide)
  refine Q'.le_trans' _ _ _ hRle ?_
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (R + 1))) ?_
  exact Q'.mul_le_mul_of_nonneg_right 1 ((R + 1) * (R + 1)) (R + 1) hsq hR1nn

/-- `0 ≤ t ≤ 1 → t³ ≤ t` (a positive sub-unit shrinks under cubing). -/
theorem cube_le_self_of_le_one {t : Q'} (ht : (0 : Q') ≤ t) (ht1 : t ≤ 1) :
    t * t * t ≤ t := by
  -- t³ = (t*t)*t ≤ 1*1*t = t  (t*t ≤ 1*1 = 1, then *t)
  have htt : t * t ≤ (1 : Q') * 1 := Q'.mul_le_mul_of_nonneg ht1 ht1 (by decide) ht
  have htt1 : t * t ≤ (1 : Q') := Q'.le_trans' _ _ _ htt (Q'.le_of_eqv (by decide))
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (t * t) 1 t htt1 ht) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv t)

/-- `0 < a → 0 < b → 0 < min' a b`. -/
theorem min_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < Q'.min' a b := by
  unfold Q'.min'
  by_cases h : a ≤ b
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

/-- The canonical initial bracket for `0 < R < 1`: `L₀ = min'(R,1)`, `U₀ = R+1`. -/
theorem cbrtInit_canonical {R : Q'} (hR : (0 : Q') < R) :
    CbrtInit R (Q'.min' R 1) (R + 1) where
  loPos := min_pos hR (by decide)
  loCube := by
    -- min³ ≤ min ≤ R  (min ≤ 1 so min³ ≤ min; min ≤ R)
    have hmnn : (0 : Q') ≤ Q'.min' R 1 := Q'.le_of_lt (min_pos hR (by decide))
    have hm1 : Q'.min' R 1 ≤ 1 := (@Q'.min_le_right R 1)
    have hmR : Q'.min' R 1 ≤ R := (@Q'.min_le_left R 1)
    exact Q'.le_trans' _ _ _ (cube_le_self_of_le_one hmnn hm1) hmR
  RleHiCube := le_succ_cube (Q'.le_of_lt hR)
  loLeHi := by
    -- min' R 1 ≤ R ≤ R+1
    exact Q'.le_trans' _ _ _ ((@Q'.min_le_left R 1)) (Q'.add_le_self_of_nonneg R 1 (by decide))

/-- **The constructive cube root** `∛R` of a positive rational `R`, via the
canonical bracket. -/
def cbrtFrom (R : Q') (hR : (0 : Q') < R) : CReal :=
  cbrtFromInit R (Q'.min' R 1) (R + 1) (cbrtInit_canonical hR)

/-- `(∛R)³ ≃ R`. -/
theorem cbrtFrom_cube_equiv (R : Q') (hR : (0 : Q') < R) :
    CReal.Equiv
      (CReal.mul (CReal.mul (cbrtFrom R hR) (cbrtFrom R hR)) (cbrtFrom R hR))
      (CReal.ofQ' R) :=
  cbrtFromInit_cube_equiv R (Q'.min' R 1) (R + 1) (cbrtInit_canonical hR)

/-- `∛R` is strictly positive. -/
theorem cbrtFrom_isPositive (R : Q') (hR : (0 : Q') < R) :
    CReal.IsPositive (cbrtFrom R hR) :=
  cbrtFromInit_isPositive R (Q'.min' R 1) (R + 1) (cbrtInit_canonical hR)

/-- `∛R ≤ c` when `R ≤ c³` (`0 ≤ c`), as `CReal.leRat (∛R) c`. -/
theorem cbrtFrom_leRat_of_cube (R : Q') (hR : (0 : Q') < R)
    (c : Q') (hc : (0 : Q') ≤ c) (hRc : R ≤ c * c * c) :
    CReal.leRat (cbrtFrom R hR) c :=
  cbrtFromInit_leRat_of_cube R (Q'.min' R 1) (R + 1) (cbrtInit_canonical hR) c hc hRc

/-- `∛R < 1` (in `leRat`-form) when `R < 1`. -/
theorem cbrtFrom_lt_one (R : Q') (hR : (0 : Q') < R) (hR1 : R < 1) :
    CReal.leRat (cbrtFrom R hR) 1 := by
  refine cbrtFrom_leRat_of_cube R hR 1 (by decide) ?_
  -- R ≤ 1 = 1³
  refine Q'.le_trans' _ _ _ (Q'.le_of_lt hR1) (Q'.le_of_eqv (by decide))

/-! ## The existence deliverable -/

/-- **Existence of the positive cube root (`Σ'`-witness, the moduli-as-data policy (README)).**
For `0 < R < 1`, there is a constructive real `ρ = ∛R` with `0 < ρ`, `ρ < 1`
(`leRat`-form), and `ρ·ρ·ρ ≃ R`. -/
def cubeRoot_exists (R : Q') (hR : (0 : Q') < R) (hR1 : R < 1) :
    Σ' ρ : CReal, CReal.IsPositive ρ ∧ CReal.leRat ρ 1 ∧
      CReal.Equiv (CReal.mul (CReal.mul ρ ρ) ρ) (CReal.ofQ' R) :=
  ⟨cbrtFrom R hR, cbrtFrom_isPositive R hR, cbrtFrom_lt_one R hR hR1,
    cbrtFrom_cube_equiv R hR⟩

/-! ## Uniqueness

The cube on the nonnegative cone is strictly increasing (`cube_lt_cube_of_lt`),
so it is injective there: two nonnegative rationals with equal cubes are equal.
This `Q'`-antisymmetry is the algebraic heart of cube-root uniqueness (the
strict monotonicity that rules out a second positive root). -/

/-- **Uniqueness of the positive cube root (rational core).**  Two nonnegative
rationals with `Equiv` cubes are `Equiv` (equal as rationals).  (`a³ ≤ b³` and
`b³ ≤ a³` each give an inequality via `le_of_cube_le_cube`; `≤`-antisymmetry on
the cross-multiplied numerators concludes.) -/
theorem cubeRoot_unique_rat {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (h : (a * a * a).eqv (b * b * b)) : a.eqv b := by
  have hab : a ≤ b := le_of_cube_le_cube ha hb (Q'.le_of_eqv h)
  have hba : b ≤ a := le_of_cube_le_cube hb ha (Q'.ge_of_eqv h)
  -- a ≤ b and b ≤ a at the num level give a.eqv b
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

/-! ### CReal-level uniqueness

The cube map is strictly increasing on the positive cone, hence injective: any
two strictly-positive constructive reals with the same cube are `Equiv`.  The
argument is purely pointwise (no CReal-product algebra): from positivity each
sequence is eventually `≥ ε'`, and from the cube-`Equiv` the cubes are eventually
within `ε`; the factorisation `a³ − b³ = (a − b)(a² + ab + b²)` with
`a² + ab + b² ≥ ε'²` then bounds `|aₙ − bₙ| ≤ ε / ε'²`. -/

/-- A positive `CReal` is eventually bounded below by a positive rational:
`IsPositive ρ → ∃ε'>0, ∃N, ∀n≥N, ε' ≤ ρ.approx n`. -/
theorem eventually_ge_of_isPositive {ρ : CReal} (h : CReal.IsPositive ρ) :
    ∃ ε' : Q', (0 : Q') < ε' ∧ ∃ N : Nat, ∀ n : Nat, N ≤ n → ε' ≤ ρ.approx n := by
  obtain ⟨ε, hε, hle⟩ := h
  -- hle : ofQ' ε ≤ ρ  i.e. ∀n, ε ≤ ρ.approx n + invSucc n
  refine ⟨half * ε, ExpNeg.half_mul_pos ε hε, (half * ε).den, fun n hn => ?_⟩
  have hn' : ε ≤ ρ.approx n + Q'.invSucc n := hle n
  -- invSucc n ≤ invSucc (half*ε).den ≤ half*ε
  have hinv : Q'.invSucc n ≤ half * ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le (half * ε)
      (ExpNeg.half_mul_pos ε hε))
  -- ε ≤ ρ_n + half*ε ⟹ half*ε ≤ ρ_n  (since ε = half*ε + half*ε)
  have hstep : ε ≤ ρ.approx n + half * ε :=
    Q'.le_trans' _ _ _ hn' (Q'.add_le_add_left (ρ.approx n) (Q'.invSucc n) (half * ε) hinv)
  -- (half*ε + half*ε) ≤ ρ_n + half*ε ⟹ half*ε ≤ ρ_n
  have hε2 : (half * ε + half * ε) ≤ ρ.approx n + half * ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves ε)) hstep
  -- cancel half*ε on the right
  have := Q'.add_le_add_right (half * ε + half * ε) (ρ.approx n + half * ε) (-(half * ε)) hε2
  -- (half*ε + half*ε) + -(half*ε) ≃ half*ε ; (ρ_n + half*ε) + -(half*ε) ≃ ρ_n
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_))
  · -- (half*ε + half*ε) + -(half*ε) ≃ half*ε
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (half * ε) (half * ε) (-(half * ε))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (half * ε) (half * ε + -(half * ε)) 0
        (Q'.add_neg_self_eqv (half * ε))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (half * ε))
  · -- (ρ_n + half*ε) + -(half*ε) ≃ ρ_n
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (ρ.approx n) (half * ε) (-(half * ε))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (ρ.approx n) (half * ε + -(half * ε)) 0
        (Q'.add_neg_self_eqv (half * ε))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (ρ.approx n))

/-- Pointwise cube-difference lower bound: `0 ≤ e → e ≤ b → b ≤ a →
`(a − b)·(e·e) ≤ a³ − b³`.  (Since `a²+ab+b² ≥ e² > 0` and `a − b ≥ 0`.) -/
theorem mul_sq_le_cube_diff {a b e : Q'} (he : (0 : Q') ≤ e) (heb : e ≤ b) (hba : b ≤ a) :
    (a + -b) * (e * e) ≤ a * a * a + -(b * b * b) := by
  have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ he heb
  have ha : (0 : Q') ≤ a := Q'.le_trans' _ _ _ hb hba
  have hdnn : (0 : Q') ≤ a + -b := by
    have := Q'.add_le_add_right b a (-b) hba
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) this
  -- e² ≤ b² ≤ a²+ab+b²  (= the quadratic factor)
  have he2 : e * e ≤ (a * a + a * b) + b * b := by
    have hbb : e * e ≤ b * b := Q'.mul_le_mul_of_nonneg heb heb hb he
    refine Q'.le_trans' _ _ _ hbb ?_
    -- b² ≤ (a²+ab)+b²
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv (b * b))) ?_
    refine Q'.add_le_add_right 0 (a * a + a * b) (b * b) ?_
    -- 0 ≤ a²+ab
    have h1 : (0 : Q') ≤ a * a := SumOfSquares.q_mul_self_nonneg a
    have h2 : (0 : Q') ≤ a * b := Q'.mul_nonneg a b ha hb
    exact Q'.le_trans' _ _ _ h1 (Q'.add_le_self_of_nonneg (a * a) (a * b) h2)
  -- (a-b)·e² ≤ (a-b)·(a²+ab+b²) ≃ a³-b³
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (e * e) ((a * a + a * b) + b * b) (a + -b) he2 hdnn) ?_
  -- (a-b)·((a²+ab)+b²) ≃ a³ - b³   (cube_diff is for (b*b + b*a + a*a); match shape)
  refine Q'.le_of_eqv ?_
  -- ((a*a + a*b) + b*b) ≃ (a*a + a*b) + b*b ; cube_diff gives (a-b)*(a²+ab+b²) form with b,a swapped.
  -- Use cube_diff with (a:=b, b:=a): (a + -b)*(a*a + a*b + b*b) ≃ a³ + -(b³).
  exact cube_diff b a

/-- From `(p + -q)·(e·e) ≤ (e·e)·ε` with `0 < e`, conclude `p ≤ q + ε`. -/
private theorem le_add_of_mul_sq_le {p q e ε : Q'} (he : (0 : Q') < e)
    (h : (p + -q) * (e * e) ≤ (e * e) * ε) : p ≤ q + ε := by
  have hee : (0 : Q') < e * e := Q'.mul_pos he he
  -- cancel e*e : p + -q ≤ ε
  have hsub : p + -q ≤ ε := by
    refine Q'.le_of_mul_le_mul_left (c := e * e) ?_ hee
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mul_comm_eqv (e * e) (p + -q))) h
  -- p + -q ≤ ε ⟹ p ≤ q + ε
  have := Q'.add_le_add_right (p + -q) ε q hsub
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_))
  · -- (p + -q) + q ≃ p
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p (-q) q) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left p (-q + q) 0 (Q'.neg_add_self_eqv q)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' p)
  · exact Q'.add_comm_eqv ε q

/-- **CReal-level uniqueness of the positive cube root.**  Two strictly-positive
constructive reals with the same cube (both `Equiv` to `ofQ' R`) are `Equiv`. -/
theorem cubeRoot_unique {ρ₁ ρ₂ : CReal} {R : Q'}
    (h1 : CReal.Equiv (CReal.mul (CReal.mul ρ₁ ρ₁) ρ₁) (CReal.ofQ' R))
    (h2 : CReal.Equiv (CReal.mul (CReal.mul ρ₂ ρ₂) ρ₂) (CReal.ofQ' R))
    (hp1 : CReal.IsPositive ρ₁) (hp2 : CReal.IsPositive ρ₂) :
    CReal.Equiv ρ₁ ρ₂ := by
  -- cubes are Equiv to each other
  have hcubes : CReal.Equiv (CReal.mul (CReal.mul ρ₁ ρ₁) ρ₁)
      (CReal.mul (CReal.mul ρ₂ ρ₂) ρ₂) := CReal.Equiv.trans h1 (CReal.Equiv.symm h2)
  -- common positive lower bound e, past N₀
  obtain ⟨e1, he1, N1, hN1⟩ := eventually_ge_of_isPositive hp1
  obtain ⟨e2, he2, N2, hN2⟩ := eventually_ge_of_isPositive hp2
  -- e = min' e1 e2 > 0, and both seqs ≥ e past max N1 N2
  intro ε hε
  have hepos : (0 : Q') < Q'.min' e1 e2 := min_pos he1 he2
  have hee_pos : (0 : Q') < Q'.min' e1 e2 * Q'.min' e1 e2 := Q'.mul_pos hepos hepos
  -- cube tolerance δ = (e*e)*ε
  have hδpos : (0 : Q') < (Q'.min' e1 e2 * Q'.min' e1 e2) * ε := Q'.mul_pos hee_pos hε
  obtain ⟨Nc, hNc⟩ := hcubes _ hδpos
  refine ⟨max (max N1 N2) Nc, fun n hn => ?_⟩
  have hnN1 : N1 ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnN2 : N2 ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnNc : Nc ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- pointwise lower bounds
  have hge1 : Q'.min' e1 e2 ≤ ρ₁.approx n :=
    Q'.le_trans' _ _ _ (@Q'.min_le_left e1 e2) (hN1 n hnN1)
  have hge2 : Q'.min' e1 e2 ≤ ρ₂.approx n :=
    Q'.le_trans' _ _ _ (@Q'.min_le_right e1 e2) (hN2 n hnN2)
  have henn : (0 : Q') ≤ Q'.min' e1 e2 := Q'.le_of_lt hepos
  -- cube-closeness
  obtain ⟨hc1, hc2⟩ := hNc n hnNc
  -- hc1 : aρ³ ≤ bρ³ + δ ; hc2 : bρ³ ≤ aρ³ + δ   (δ = (e*e)*ε), at ofQ' R both sides? no:
  -- approxs: A_n = (ρ₁_n*ρ₁_n)*ρ₁_n, B_n = (ρ₂_n*ρ₂_n)*ρ₂_n
  have hc1' : (ρ₁.approx n * ρ₁.approx n) * ρ₁.approx n
      ≤ (ρ₂.approx n * ρ₂.approx n) * ρ₂.approx n + (Q'.min' e1 e2 * Q'.min' e1 e2) * ε := hc1
  have hc2' : (ρ₂.approx n * ρ₂.approx n) * ρ₂.approx n
      ≤ (ρ₁.approx n * ρ₁.approx n) * ρ₁.approx n + (Q'.min' e1 e2 * Q'.min' e1 e2) * ε := hc2
  refine ⟨?_, ?_⟩
  · -- ρ₁_n ≤ ρ₂_n + ε
    by_cases hcase : ρ₂.approx n ≤ ρ₁.approx n
    · -- a = ρ₁_n ≥ b = ρ₂_n : (a-b)e² ≤ a³-b³ ≤ δ
      have hfac := mul_sq_le_cube_diff henn hge2 hcase
      -- a³ - b³ ≤ δ  from hc1'
      have hdiff : ρ₁.approx n * ρ₁.approx n * ρ₁.approx n
          + -(ρ₂.approx n * ρ₂.approx n * ρ₂.approx n)
          ≤ (Q'.min' e1 e2 * Q'.min' e1 e2) * ε := by
        have := Q'.add_le_add_right _ _
          (-(ρ₂.approx n * ρ₂.approx n * ρ₂.approx n)) hc1'
        refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
        -- (b³ + δ) + -b³ ≃ δ
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(ρ₂.approx n * ρ₂.approx n * ρ₂.approx n))
            (Q'.add_comm_eqv (ρ₂.approx n * ρ₂.approx n * ρ₂.approx n)
              ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε)
            (ρ₂.approx n * ρ₂.approx n * ρ₂.approx n)
            (-(ρ₂.approx n * ρ₂.approx n * ρ₂.approx n))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε) _ 0
            (Q'.add_neg_self_eqv (ρ₂.approx n * ρ₂.approx n * ρ₂.approx n))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have hmul : (ρ₁.approx n + -ρ₂.approx n)
          * (Q'.min' e1 e2 * Q'.min' e1 e2)
          ≤ (Q'.min' e1 e2 * Q'.min' e1 e2) * ε :=
        Q'.le_trans' _ _ _ hfac hdiff
      exact le_add_of_mul_sq_le hepos hmul
    · -- a = ρ₁_n ≤ b = ρ₂_n : trivially ρ₁_n ≤ ρ₂_n ≤ ρ₂_n + ε
      have hle : ρ₁.approx n ≤ ρ₂.approx n := Q'.le_of_not_le hcase
      exact Q'.le_trans' _ _ _ hle
        (Q'.add_le_self_of_nonneg (ρ₂.approx n) ε (Q'.le_of_lt hε))
  · -- ρ₂_n ≤ ρ₁_n + ε  (symmetric)
    by_cases hcase : ρ₁.approx n ≤ ρ₂.approx n
    · have hfac := mul_sq_le_cube_diff henn hge1 hcase
      have hdiff : ρ₂.approx n * ρ₂.approx n * ρ₂.approx n
          + -(ρ₁.approx n * ρ₁.approx n * ρ₁.approx n)
          ≤ (Q'.min' e1 e2 * Q'.min' e1 e2) * ε := by
        have := Q'.add_le_add_right _ _
          (-(ρ₁.approx n * ρ₁.approx n * ρ₁.approx n)) hc2'
        refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ (-(ρ₁.approx n * ρ₁.approx n * ρ₁.approx n))
            (Q'.add_comm_eqv (ρ₁.approx n * ρ₁.approx n * ρ₁.approx n)
              ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε)
            (ρ₁.approx n * ρ₁.approx n * ρ₁.approx n)
            (-(ρ₁.approx n * ρ₁.approx n * ρ₁.approx n))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left ((Q'.min' e1 e2 * Q'.min' e1 e2) * ε) _ 0
            (Q'.add_neg_self_eqv (ρ₁.approx n * ρ₁.approx n * ρ₁.approx n))) ?_
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      have hmul : (ρ₂.approx n + -ρ₁.approx n)
          * (Q'.min' e1 e2 * Q'.min' e1 e2)
          ≤ (Q'.min' e1 e2 * Q'.min' e1 e2) * ε :=
        Q'.le_trans' _ _ _ hfac hdiff
      exact le_add_of_mul_sq_le hepos hmul
    · have hle : ρ₂.approx n ≤ ρ₁.approx n := Q'.le_of_not_le hcase
      exact Q'.le_trans' _ _ _ hle
        (Q'.add_le_self_of_nonneg (ρ₁.approx n) ε (Q'.le_of_lt hε))

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`, no
`native_decide`, no `sorryAx`.

This module is ordinary constructive real analysis (a monotone located bisection
on `t ↦ t³`), NOT a 4D-analytic oracle: it carries no spectral / continuum /
Yang–Mills content.  Intended use: inhabit a matched-retune carrier
`ρ³ = g₁/(2 g₀)` with a genuine positive real cube root. -/

#print axioms ConstructiveReals.CReal.cbrtFromInit
#print axioms ConstructiveReals.CReal.cbrtFrom
#print axioms ConstructiveReals.CReal.cbrtWidth_eq_geom
#print axioms ConstructiveReals.CReal.cbrtInv
#print axioms ConstructiveReals.CReal.cube_diff
#print axioms ConstructiveReals.CReal.cbrtFromInit_cube_equiv
#print axioms ConstructiveReals.CReal.cbrtFrom_cube_equiv
#print axioms ConstructiveReals.CReal.cbrtFromInit_isPositive
#print axioms ConstructiveReals.CReal.cbrtFrom_isPositive
#print axioms ConstructiveReals.CReal.le_of_cube_le_cube
#print axioms ConstructiveReals.CReal.cbrtFrom_leRat_of_cube
#print axioms ConstructiveReals.CReal.cbrtFrom_lt_one
#print axioms ConstructiveReals.CReal.cubeRoot_exists
#print axioms ConstructiveReals.CReal.cubeRoot_unique_rat
#print axioms ConstructiveReals.CReal.cubeRoot_unique
