/-
A SOUND rational upper bound for constructive reals: `CReal.leRat x b`.

`Reals.lean`'s one-slack `≤` is sound only for *regular* sequences (the
`n`-th term within `1/(n+1)` of the limit).  The `expNeg` partial sums
are NOT regular — the alternating partials overshoot for large `x` — so
that order cannot certify a tight upper bound on `e^{−x}`.

`leRat x b` is the regularity-free "limit `≤ b`" predicate:
`x.approx n` is eventually `≤ b + ε`, for every `ε > 0`.  It is sound for
ANY Cauchy sequence (no regularity needed) and is exactly what discharges
the `ExpUB` per-term seeds `e^{−t·C₂} ≤ (rational)`.

# Axiom-gate (see README: axiom policy)

Every theorem reports `[propext]` only.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import ConstructiveReals.Reals

namespace ConstructiveReals

namespace CReal

open ConstructiveReals

/-- **Sound rational upper bound.**  `leRat x b` says the limit of `x` is
`≤ b`: for every tolerance `ε > 0`, the approximations are eventually
`≤ b + ε`.  Unlike the one-slack `≤`, this needs no regularity, so it
correctly bounds non-regular sequences such as the `expNeg` partials. -/
def leRat (x : CReal) (b : Q') : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → x.approx n ≤ b + ε

/-- A uniform eventual bound `approx n ≤ b` (no `ε`) gives `leRat x b`. -/
theorem leRat_of_eventually {x : CReal} {b : Q'}
    (h : ∃ N : Nat, ∀ n : Nat, N ≤ n → x.approx n ≤ b) : leRat x b := by
  intro ε hε
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε))⟩

/-- Monotone in the bound: `leRat x a` and `a ≤ b` give `leRat x b`. -/
theorem leRat_mono {x : CReal} {a b : Q'} (h : leRat x a) (hab : a ≤ b) :
    leRat x b := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _ (hN n hn)
    (Q'.add_le_add_right a b ε hab)⟩

/-- The embedding respects the bound: `a ≤ b → leRat (ofQ' a) b`. -/
theorem leRat_ofQ' {a b : Q'} (hab : a ≤ b) : leRat (ofQ' a) b :=
  leRat_of_eventually ⟨0, fun _ _ => hab⟩

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CReal.leRat_of_eventually
#print axioms ConstructiveReals.CReal.leRat_mono
#print axioms ConstructiveReals.CReal.leRat_ofQ'
