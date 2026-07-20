/-
`(1/2)^k → 0` in the constructive rationals `Q'`, with an EXPLICIT modulus.

This module proves the convergence-to-zero of the halving sequence
`half^k = (1/2)^k` and packages it as a constructive modulus: for any
`δ : Q'` with `0 < δ`, taking `k = δ.den` already forces
`half^k ≤ δ`.  The witness `δ.den` is a closed-form function of the
target `δ`, so this is a Rule-8-compliant explicit modulus (no
classical existence, no `Classical.choice`).

The argument has three rational ingredients, each reduced to an `Int`
inequality via the `Q'` cross-product representation:

  * `half * invSucc k ≤ invSucc (k+1)` — one halving beats the
    harmonic step `1/(k+1) → 1/(k+2)` because `k+2 ≤ 2(k+1)`;
  * `half^k ≤ invSucc k` — induction, chaining the above through
    left-monotonicity of `*`;
  * `invSucc δ.den ≤ δ` — for `0 < δ` we have `1 ≤ δ.num`, hence
    `1/(δ.den+1) ≤ δ`.

# Axiom-gate (see README: axiom policy)

Every theorem below reports `[propext]` only.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`, no `sorry`.  The single Nat→Int side-goal
`k + 2 ≤ 2 * (k + 1)` is discharged by a hand proof through
`Nat.le.intro` / `exact_mod_cast`, NOT `omega`, so `Quot.sound` is
avoided entirely.
-/

import ConstructiveReals.Reals
import ConstructiveReals.RationalsMul
import ConstructiveReals.GeometricTail

namespace ConstructiveReals.HalfPow

open ConstructiveReals

/-! ## `half = 1/2` -/

/-- The rational `1/2`. -/
def half : Q' := Q'.mkPos 1 2 (by decide)

/-- `0 ≤ 1/2`. -/
theorem half_nonneg : (0 : Q') ≤ half := by decide

/-! ## One halving beats one harmonic step -/

/-- `(k + 2 : Nat) ≤ 2 * (k + 1)` — the pure-`Nat` core of the halving
estimate.  Proved by exhibiting the explicit witness `k` for the
`Nat.le.intro` form `k + 2 + k = 2 * (k + 1)`, avoiding `omega`. -/
theorem nat_step (k : Nat) : k + 2 ≤ 2 * (k + 1) := by
  apply Nat.le.intro (k := k)
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.two_mul]
  rw [Nat.add_comm (k + 2) k, ← Nat.add_assoc, Nat.add_comm k k]

/-- `half * invSucc k ≤ invSucc (k+1)`: one halving dominates the
harmonic decrement `1/(k+1) → 1/(k+2)`. -/
theorem half_mul_invSucc_le (k : Nat) :
    half * Q'.invSucc k ≤ Q'.invSucc (k + 1) := by
  show (half * Q'.invSucc k).num * ((Q'.invSucc (k + 1)).den : Int)
      ≤ (Q'.invSucc (k + 1)).num * ((half * Q'.invSucc k).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den, Q'.mul_den_cast half (Q'.invSucc k),
      Q'.invSucc_den]
  show ((1 : Int) * 1) * (((k + 1) + 1 : Nat) : Int)
      ≤ (1 : Int) * (((2 : Nat) : Int) * ((k + 1 : Nat) : Int))
  rw [Int.one_mul, Int.one_mul, Int.one_mul]
  have hnat : k + 2 ≤ 2 * (k + 1) := nat_step k
  have : (((k + 1) + 1 : Nat) : Int) ≤ ((2 * (k + 1) : Nat) : Int) := by
    exact_mod_cast hnat
  rw [Int.natCast_mul] at this
  show (((k + 1) + 1 : Nat) : Int) ≤ ((2 : Nat) : Int) * ((k + 1 : Nat) : Int)
  exact this

/-- `half^k ≤ invSucc k = 1/(k+1)`.  Induction on `k`. -/
theorem pow_half_le_invSucc (k : Nat) : half ^ k ≤ Q'.invSucc k := by
  induction k with
  | zero =>
    show (1 : Q') ≤ Q'.invSucc 0
    decide
  | succ n ih =>
    show half * half ^ n ≤ Q'.invSucc (n + 1)
    have h1 : half * half ^ n ≤ half * Q'.invSucc n :=
      Q'.mul_le_mul_of_nonneg_left (half ^ n) (Q'.invSucc n) half ih half_nonneg
    have h2 : half * Q'.invSucc n ≤ Q'.invSucc (n + 1) :=
      half_mul_invSucc_le n
    exact Q'.le_trans' (half * half ^ n) (half * Q'.invSucc n)
      (Q'.invSucc (n + 1)) h1 h2

/-- For positive `δ`, the unit fraction `invSucc δ.den = 1/(δ.den+1)`
is `≤ δ`.  Uses `1 ≤ δ.num` (from `0 < δ`) and `δ.den ≥ 0`. -/
theorem invSucc_den_le (δ : Q') (hδ : (0 : Q') < δ) :
    Q'.invSucc δ.den ≤ δ := by
  have hnum_pos : (0 : Int) < δ.num := by
    have h : (0 : Int) * (δ.den : Int) < δ.num * ((0 : Q').den : Int) := hδ
    rw [Int.zero_mul] at h
    show (0 : Int) < δ.num
    have h' : (0 : Int) < δ.num * (1 : Int) := h
    rw [Int.mul_one] at h'
    exact h'
  have hone_le : (1 : Int) ≤ δ.num := hnum_pos
  show (Q'.invSucc δ.den).num * (δ.den : Int)
      ≤ δ.num * ((Q'.invSucc δ.den).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den]
  rw [Int.one_mul]
  have hden1_nn : (0 : Int) ≤ ((δ.den + 1 : Nat) : Int) := Int.natCast_nonneg _
  have hstep : (1 : Int) * ((δ.den + 1 : Nat) : Int)
      ≤ δ.num * ((δ.den + 1 : Nat) : Int) :=
    Int.mul_le_mul_of_nonneg_right hone_le hden1_nn
  rw [Int.one_mul] at hstep
  have hden_lt : (δ.den : Int) ≤ ((δ.den + 1 : Nat) : Int) := by
    have hcast : ((δ.den + 1 : Nat) : Int) = (δ.den : Int) + 1 :=
      Int.natCast_add δ.den 1
    rw [hcast]
    exact Int.le_add_of_nonneg_right (by decide)
  exact Int.le_trans hden_lt hstep

/-! ## The deliverable: explicit-modulus convergence to zero -/

/-- **Explicit modulus.**  For any positive rational `δ`, the halving
power at exponent `δ.den` is already `≤ δ`: `(1/2)^(δ.den) ≤ δ`.  Since
`δ.den` is a closed-form function of `δ`, this exhibits the modulus of
convergence of `(1/2)^k → 0`. -/
theorem pow_half_le (δ : Q') (hδ : (0 : Q') < δ) : half ^ δ.den ≤ δ :=
  Q'.le_trans' (half ^ δ.den) (Q'.invSucc δ.den) δ
    (pow_half_le_invSucc δ.den) (invSucc_den_le δ hδ)

end ConstructiveReals.HalfPow

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.HalfPow.half_nonneg
#print axioms ConstructiveReals.HalfPow.nat_step
#print axioms ConstructiveReals.HalfPow.half_mul_invSucc_le
#print axioms ConstructiveReals.HalfPow.pow_half_le_invSucc
#print axioms ConstructiveReals.HalfPow.invSucc_den_le
#print axioms ConstructiveReals.HalfPow.pow_half_le
