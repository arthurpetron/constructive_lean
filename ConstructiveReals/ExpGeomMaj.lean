/-
U.6 tail — the inductive geometric majorant for `e^{-H(k)}`.

The character-tail factor `Sᵢ = Σ_x (x+1)^{2n}·e^{−t·h(x)}` converges because the
exponential decays geometrically.  To feed `CharacterTail.geom_series_le` (a
`Q'` series) we need a *rational* majorant of `e^{−t·h(x)}` with a geometric
ratio.  Writing `H(k) = t·h(k)` and `d(k) = H(k+1) − H(k) = t·(h(k+1)−h(k))`
(the increment), a rational sequence `B` with `B(k+1) = B(k)·E(d(k))`
(`E = recipExpUB.E = 1/(1+·)`) bounds it:

    e^{−H(k)}  ≤  B(k) ,   provided  B(0) ≥ E(H(0)).

The inductive step is the payoff of the addition law and the product bound:
`e^{−H(k+1)} = e^{−H(k)}·e^{−d(k)} ≤ B(k)·E(d(k))` — `expNeg_add_equiv` +
`leRat_of_equiv` + `leRat_mul` (with `recipExpUB` soundness on the new factor,
and `expNeg_geRat_zero` for the nonnegativity the product bound needs).

This is fully abstract in `H`, `d`, `B`; the SU(3)/SU(2) character instances
supply the concrete `h` and the geometric `B`.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ExpAdd
import ConstructiveReals.CRealMulLe
import ConstructiveReals.Soundness
import ConstructiveReals.ExpUBInstance

namespace ConstructiveReals

open ConstructiveReals

/-- `expNeg` depends on its argument's nonnegativity proof only through a `Prop`
field, so equal arguments give the same `CReal`. -/
theorem expNeg_eq_of_eq {x y : Q'} (h : x = y) (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y) :
    ExpNeg.expNeg x hx = ExpNeg.expNeg y hy := by
  subst h; rfl

/-- **The inductive geometric majorant.**  If `H` accumulates nonnegative
increments `d` (`H(k+1) = H(k) + d(k)`) and the rational `B` follows
`B(k+1) = B(k)·E(d(k))` from a valid start `B(0) ≥ E(H(0))`, then
`e^{−H(k)} ≤ B(k)` for all `k`.  (`E = recipExpUB.E = 1/(1+·)`.) -/
theorem expNeg_le_geomMaj (H d B : Nat → Q')
    (hH : ∀ k, (0 : Q') ≤ H k) (hd : ∀ k, (0 : Q') ≤ d k)
    (hstep : ∀ k, H (k + 1) = H k + d k)
    (hBnn : ∀ k, (0 : Q') ≤ B k)
    (hB0 : CReal.leRat (ExpNeg.expNeg (H 0) (hH 0)) (B 0))
    (hBstep : ∀ k, B (k + 1) = B k * ExpUBInstance.oneOver1p (d k)) :
    ∀ k, CReal.leRat (ExpNeg.expNeg (H k) (hH k)) (B k) := by
  intro k
  induction k with
  | zero => exact hB0
  | succ k ih =>
      -- goal: leRat (expNeg (H (k+1))) (B (k+1))
      rw [hBstep k]
      -- goal: leRat (expNeg (H (k+1))) (B k * oneOver1p (d k))
      -- product bound on mul (expNeg (H k)) (expNeg (d k))
      have hmul : CReal.leRat
          (CReal.mul (ExpNeg.expNeg (H k) (hH k)) (ExpNeg.expNeg (d k) (hd k)))
          (B k * ExpUBInstance.oneOver1p (d k)) :=
        CReal.leRat_mul ih (expNeg_le_oneOver1p (d k) (hd k))
          (expNeg_geRat_zero (H k) (hH k)) (expNeg_geRat_zero (d k) (hd k))
          (hBnn k) (ExpUBInstance.oneOver1p_nonneg (d k))
      -- addition law: mul (expNeg (H k)) (expNeg (d k)) ≃ expNeg (H k + d k)
      have hequiv := expNeg_add_equiv (H k) (d k) (hH k) (hd k)
      have hres : CReal.leRat
          (ExpNeg.expNeg (H k + d k) (Q'.zero_le_add (H k) (d k) (hH k) (hd k)))
          (B k * ExpUBInstance.oneOver1p (d k)) :=
        CReal.leRat_of_equiv (CReal.Equiv.symm hequiv) hmul
      -- transport across H (k+1) = H k + d k
      rw [expNeg_eq_of_eq (hstep k) (hH (k + 1))
        (Q'.zero_le_add (H k) (d k) (hH k) (hd k))]
      exact hres

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.expNeg_eq_of_eq
#print axioms ConstructiveReals.expNeg_le_geomMaj
