/-
Finite sums of constructive reals — the bridge from per-term `leRat` bounds to
a bound on a finite partial sum.

The character-tail factor `Sᵢ = Σ_x (x+1)^{2n}·e^{−t·h(x)}` is, at finite
truncation, a sum of `CReal` terms.  `csum A n = Σ_{i<n} A i` (built from
`CReal.add`), and `leRat_csum` says: if each term `A i` has limit `≤ b i`, then
the finite sum has limit `≤ Σ_{i<n} b i` — a rational.  Combined with
`charTerm_leRat` (box) and the geometric majorant (tail), this bounds every
truncation of `Sᵢ` by a rational, uniformly.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.CRealAdd

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail

namespace CReal

/-- Finite sum of constructive reals: `csum A n = Σ_{i<n} A i`. -/
def csum (A : Nat → CReal) : Nat → CReal
  | 0 => czero
  | n + 1 => add (csum A n) (A n)

@[simp] theorem csum_zero (A : Nat → CReal) : csum A 0 = czero := rfl

@[simp] theorem csum_succ (A : Nat → CReal) (n : Nat) :
    csum A (n + 1) = add (csum A n) (A n) := rfl

/-- The approximations of `csum` are the finite sums of the approximations. -/
theorem csum_approx (A : Nat → CReal) :
    ∀ n k, (csum A n).approx k = finSum (fun i => (A i).approx k) n
  | 0, _ => rfl
  | n + 1, k => by
      show (csum A n).approx k + (A n).approx k
          = finSum (fun i => (A i).approx k) n + (A n).approx k
      rw [csum_approx A n k]

/-- **Per-term `leRat` bounds sum.**  If each `A i` has limit `≤ b i`, then
`csum A n` has limit `≤ Σ_{i<n} b i`. -/
theorem leRat_csum (A : Nat → CReal) (b : QSeq) (h : ∀ i, CReal.leRat (A i) (b i)) :
    ∀ n, CReal.leRat (csum A n) (finSum b n)
  | 0 => CReal.leRat_ofQ' (Q'.le_refl' 0)
  | n + 1 => CReal.leRat_add (leRat_csum A b h n) (h n)

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CReal.csum_approx
#print axioms ConstructiveReals.CReal.leRat_csum
