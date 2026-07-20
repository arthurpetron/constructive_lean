/-
A minimal reflective univariate polynomial ring over `Q'` — a "`ring` for
`Q'`" sufficient to discharge the polynomial identities that route (a)
needs at every order (the SOS-factorization of each Gram
pivot), without a metaprogramming `ring` tactic.

A polynomial is its coefficient list `[c₀, c₁, …, cₙ]` (low-to-high
degree), evaluated by Horner.  The ring operations `padd`, `pmul`, `pneg`
on lists are proved to be `eval`-homomorphisms; then a polynomial identity
`f ≃ g` is discharged by computing `psub f g` and `decide`-checking that
every coefficient is `≃ 0` (`poly_eqv`).  Combined with
`SumOfSquares.Equiv_of_approx_eqv`, this lifts to `CReal` polynomial
identities (each reduces pointwise to a `Q'` identity).

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Rationals
import ConstructiveReals.RationalsMul

namespace ConstructiveReals.QPoly

open ConstructiveReals

/-! ## Small `Q'` ring facts (not already named) -/

theorem q_mul_zero (a : Q') : (a * 0).eqv 0 := by
  show a.num * 0 * ((0 : Q').den : Int) = 0 * ((a * 0).den : Int)
  omega

theorem q_zero_mul (a : Q') : ((0 : Q') * a).eqv 0 := by
  show 0 * a.num * ((0 : Q').den : Int) = 0 * (((0 : Q') * a).den : Int)
  omega

theorem q_zero_add_eqv (a : Q') : ((0 : Q') + a).eqv a := by
  show ((0 : Q') + a).num * (a.den : Int) = a.num * (((0 : Q') + a).den : Int)
  rw [Q'.zero_add']

theorem q_add_zero_eqv (a : Q') : (a + (0 : Q')).eqv a := by
  show (a + (0 : Q')).num * (a.den : Int) = a.num * ((a + (0 : Q')).den : Int)
  rw [Q'.add_zero']

/-- Congruence for `+` on both arguments. -/
theorem q_add_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- `(a+b)·c ≃ a·c + b·c` (the missing right-distributivity; `add_mul_eqv`
itself lives in a heavier module, so we derive it locally). -/
theorem q_add_mul (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a + b) c)
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c a b)
      (q_add_congr (Q'.mul_comm_eqv c a) (Q'.mul_comm_eqv c b)))

/-- Interchange: `(a+b)+(c+d) ≃ (a+c)+(b+d)`. -/
theorem q_interchange (a b c d : Q') : ((a + b) + (c + d)).eqv ((a + c) + (b + d)) := by
  -- (a+b)+(c+d) ≃ a+(b+(c+d)) ≃ a+((b+c)+d) ≃ a+((c+b)+d) ≃ a+(c+(b+d)) ≃ (a+c)+(b+d)
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (b + (c + d)) ((b + c) + d)
    (Q'.eqv_symm (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((b + c) + d) ((c + b) + d)
    (Q'.add_eqv_congr_right (b + c) (c + b) d (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a ((c + b) + d) (c + (b + d))
    (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a c (b + d))

/-- From `a + -b ≃ 0` conclude `a ≃ b`. -/
theorem q_eqv_of_sub_zero {a b : Q'} (h : (a + -b).eqv 0) : a.eqv b := by
  have h1 : ((a + -b) + b).eqv a :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b))
        (q_add_zero_eqv a))
  have h2 : ((a + -b) + b).eqv b :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (a + -b) 0 b h) (q_zero_add_eqv b)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h1) h2

/-! ## Polynomials and Horner evaluation -/

/-- A univariate polynomial as its coefficient list (low-to-high degree). -/
abbrev Poly := List Q'

/-- Horner evaluation `[c₀,c₁,…] ↦ c₀ + x·(c₁ + x·(…))`. -/
def eval : Poly → Q' → Q'
  | [], _ => 0
  | (c :: cs), x => c + x * eval cs x

/-! ## Ring operations on coefficient lists -/

def padd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | (a :: p), (b :: q) => (a + b) :: padd p q

def pscale (k : Q') : Poly → Poly
  | [] => []
  | (c :: cs) => (k * c) :: pscale k cs

def pneg (p : Poly) : Poly := pscale (-1) p

def psub (p q : Poly) : Poly := padd p (pneg q)

def pmul : Poly → Poly → Poly
  | [], _ => []
  | (a :: p), q => padd (pscale a q) (0 :: pmul p q)

/-! ## Homomorphism correctness -/

theorem eval_pscale (k : Q') : ∀ (p : Poly) (x : Q'),
    (eval (pscale k p) x).eqv (k * eval p x)
  | [], _ => Q'.eqv_symm (q_mul_zero k)
  | (c :: cs), x => by
      show (k * c + x * eval (pscale k cs) x).eqv (k * (c + x * eval cs x))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (k * c) (x * eval (pscale k cs) x) (x * (k * eval cs x))
          (Q'.mul_eqv_congr_left x _ _ (eval_pscale k cs x))) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv k c (x * eval cs x)) ?_
      refine Q'.add_eqv_congr_left (k * c) (k * (x * eval cs x)) (x * (k * eval cs x)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv k x (eval cs x))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (k * x) (x * k) (eval cs x) (Q'.mul_comm_eqv k x)) ?_
      exact Q'.mul_assoc_eqv x k (eval cs x)

theorem eval_padd : ∀ (p q : Poly) (x : Q'),
    (eval (padd p q) x).eqv (eval p x + eval q x)
  | [], q, x => Q'.eqv_symm (q_zero_add_eqv (eval q x))
  | (a :: p), [], x => Q'.eqv_symm (q_add_zero_eqv (eval (a :: p) x))
  | (a :: p), (b :: q), x => by
      show ((a + b) + x * eval (padd p q) x).eqv
        ((a + x * eval p x) + (b + x * eval q x))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (a + b) (x * eval (padd p q) x)
          (x * (eval p x + eval q x))
          (Q'.mul_eqv_congr_left x _ _ (eval_padd p q x))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (a + b) (x * (eval p x + eval q x))
          (x * eval p x + x * eval q x) (Q'.mul_add_eqv x (eval p x) (eval q x))) ?_
      exact q_interchange a b (x * eval p x) (x * eval q x)

theorem eval_pneg (p : Poly) (x : Q') : (eval (pneg p) x).eqv (-(eval p x)) :=
  Q'.eqv_trans _ _ _ (eval_pscale (-1) p x)
    (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (eval p x))
      (Q'.neg_eqv_congr (1 * eval p x) (eval p x) (Q'.one_mul_eqv (eval p x))))

theorem eval_psub (p q : Poly) (x : Q') :
    (eval (psub p q) x).eqv (eval p x + -(eval q x)) :=
  Q'.eqv_trans _ _ _ (eval_padd p (pneg q) x)
    (Q'.add_eqv_congr_left (eval p x) (eval (pneg q) x) (-(eval q x)) (eval_pneg q x))

theorem eval_pmul : ∀ (p q : Poly) (x : Q'),
    (eval (pmul p q) x).eqv (eval p x * eval q x)
  | [], q, x => Q'.eqv_symm (q_zero_mul (eval q x))
  | (a :: p), q, x => by
      show (eval (padd (pscale a q) (0 :: pmul p q)) x).eqv ((a + x * eval p x) * eval q x)
      refine Q'.eqv_trans _ _ _ (eval_padd (pscale a q) (0 :: pmul p q) x) ?_
      have hL : (eval (pscale a q) x).eqv (a * eval q x) := eval_pscale a q x
      have hR : (eval (0 :: pmul p q) x).eqv (x * (eval p x * eval q x)) :=
        Q'.eqv_trans _ _ _ (q_zero_add_eqv (x * eval (pmul p q) x))
          (Q'.mul_eqv_congr_left x _ _ (eval_pmul p q x))
      refine Q'.eqv_trans _ _ _ (q_add_congr hL hR) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (q_add_mul a (x * eval p x) (eval q x)) ?_
      exact Q'.add_eqv_congr_left (a * eval q x) ((x * eval p x) * eval q x)
        (x * (eval p x * eval q x)) (Q'.mul_assoc_eqv x (eval p x) (eval q x))

/-! ## The identity prover -/

/-- Every coefficient is `≃ 0` — as a `Bool` test (so `Decidable` is free). -/
def allZeroB : Poly → Bool
  | [] => true
  | (c :: cs) => decide (c.eqv 0) && allZeroB cs

def allZero (p : Poly) : Prop := allZeroB p = true

instance (p : Poly) : Decidable (allZero p) := inferInstanceAs (Decidable (_ = true))

theorem eval_zero_of_allZero : ∀ (p : Poly) (x : Q'), allZero p → (eval p x).eqv 0
  | [], _, _ => Q'.eqv_refl 0
  | (c :: cs), x, h => by
      have hb : decide (c.eqv 0) = true ∧ allZeroB cs = true := by
        have h' := h; rw [allZero, allZeroB, Bool.and_eq_true] at h'; exact h'
      have hc : c.eqv 0 := of_decide_eq_true hb.1
      have hcs : (eval cs x).eqv 0 := eval_zero_of_allZero cs x hb.2
      show (c + x * eval cs x).eqv 0
      exact Q'.eqv_trans _ _ _
        (q_add_congr hc
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ hcs) (q_mul_zero x)))
        (q_add_zero_eqv 0)

/-- **The identity prover:** if `psub p q` has all coefficients `≃ 0`
(checkable by `decide`), then `eval p x ≃ eval q x` for all `x`. -/
theorem poly_eqv (p q : Poly) (x : Q') (h : allZero (psub p q)) :
    (eval p x).eqv (eval q x) :=
  q_eqv_of_sub_zero
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (eval_psub p q x))
      (eval_zero_of_allZero (psub p q) x h))

/-! ## Validation: the 2×2 heat-kernel pivot factorization

The pivot of the SU(2) heat-kernel Gram 2×2 minor, in `r = e^{−t/2}`, is
`1 + 3r⁴ − 4r³`, with the manifest-SOS factorization `(1−r)²(3r²+2r+1)`.
The ring discharges this identity by `decide` on the coefficient lists —
end-to-end proof that the helper closes the per-order certificates. -/
theorem pivot2_factor (r : Q') :
    (eval [1, 0, 0, -(Q'.ofNat 4), Q'.ofNat 3] r).eqv
      (eval (pmul (pmul [1, -(1 : Q')] [1, -(1 : Q')])
        [1, Q'.ofNat 2, Q'.ofNat 3]) r) :=
  poly_eqv _ _ r (by decide)

end ConstructiveReals.QPoly

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.QPoly.eval_pmul
#print axioms ConstructiveReals.QPoly.poly_eqv
#print axioms ConstructiveReals.QPoly.pivot2_factor
