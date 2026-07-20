/-
**The decaying-exponential SUM closes geometrically.**

Lifts the per-term geometric domination `ExpGeomBound.expNeg_mul_le_pow`
(`e^{−a·m} ≤ ρ^m`) to the SUM, via the existing `CReal.leRat_csum` (termwise
`CReal ≤ Q'` ⟹ `csum ≤ finSum`) and `geometric_tail_closure`
(`Σ_{k<N} ρ^k ≤ H` given `1 + ρ·H ≤ H`):

    Σ_{m<N} e^{−a·m} ≤ H.

This closes the geometric envelope of the per-axis character tail (atom (B1) of
`docs/sun-uniform-cap-factorization.md`): the heat-kernel exponential sum is
bounded by the rational geometric-series limit, uniformly in `N`.  The
polynomial-weighted refinement `Σ (m+1)^{2q} e^{−a·m}` further composes this
term bound with `PolylogTail.weightedGeomSum_le` (scaling each term by the
nonnegative `(m+1)^{2q}` via `CReal.leRat_smul_nonneg`).

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.ExpGeomBound
import ConstructiveReals.CRealSum
import ConstructiveReals.GeometricTail

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail

/-- **Geometric closure of the heat-kernel exponential sum.**
`Σ_{m<N} e^{−a·m} ≤ H` for every `N`, given `e^{−a} ≤ ρ` (`0 ≤ ρ`) and the
one-step geometric recurrence `1 + ρ·H ≤ H` (`0 ≤ H`).

Per-term `e^{−a·m} ≤ ρ^m` (`expNeg_mul_le_pow`) lifts through `leRat_csum` to
`Σ e^{−a·m} ≤ Σ ρ^m`, and `geometric_tail_closure` caps `Σ ρ^m ≤ H`. -/
theorem expNeg_geom_csum_le (a ρ H : Q') (ha : (0 : Q') ≤ a)
    (hρ0 : (0 : Q') ≤ ρ) (hH : (0 : Q') ≤ H)
    (hρ : CReal.leRat (ExpNeg.expNeg a ha) ρ) (hrec : (1 : Q') + ρ * H ≤ H) :
    ∀ N, CReal.leRat
      (CReal.csum (fun m => ExpNeg.expNeg (a * Q'.ofNat m)
        (Q'.mul_nonneg a (Q'.ofNat m) ha (ofNat_nonneg m))) N) H := by
  intro N
  refine CReal.leRat_mono
    (CReal.leRat_csum _ (fun k => 1 * ρ ^ k)
      (fun m => CReal.leRat_mono (expNeg_mul_le_pow a ρ ha hρ0 hρ m)
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv (ρ ^ m))))) N)
    (geometric_tail_closure 1 ρ H hρ0 hH hrec N)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.expNeg_geom_csum_le
