/-
The rational exponential seed interface: an abstract rational upper
bound for `x ↦ e^{−x}` on `x ≥ 0`, entirely in `Q'`.

`ExpUB` packages a rational function `E : Q' → Q'` together with the
structural facts (`E ≥ 0`, `E 0 ≤ 1`, antitonicity) that downstream
majorant arguments need.  A concrete instance — the Padé/Bernoulli
bound `E(x) = 1/(1+x)` — is built in `ExpUBInstance.lean`, and its
soundness against the constructive series exponential (`e^{−x} ≤ E x`)
is proved in `Soundness.lean`.

The point of keeping the seed abstract is that any consumer needing
"a nonnegative, antitone rational majorant of the decaying
exponential" can take an `ExpUB` as a parameter and remain independent
of which concrete bound is used.

# Axiom-gate

Every load-bearing theorem reports `[propext]` (the `Q'` order) or
empty (`decide`).  No `Classical.*`, no `Quot.sound`, no `sorryAx`.
-/

import ConstructiveReals.Geometric

namespace ConstructiveReals.ExpBound

open ConstructiveReals

/-! ## The seed interface: a rational upper bound for `e^{−x}`

`ExpUB` abstracts a rational function `E : Q' → Q'` that upper-bounds
`x ↦ e^{−x}` on `x ≥ 0`, with the structural properties downstream
majorant arguments use.  `ExpUBInstance.lean` instantiates `E`
concretely and proves these fields; here it is abstract, so every
consumer is *conditional on `ExpUB`* rather than tied to one bound. -/

/-- A rational upper-bound operator for `e^{−x}` on `x ≥ 0`. -/
structure ExpUB where
  /-- The rational bound: morally `E x ≥ e^{−x}`. -/
  E : Q' → Q'
  /-- `e^{−x} > 0`, so the bound is nonnegative. -/
  E_pos : ∀ x, (0 : Q') ≤ E x
  /-- `e^{0} = 1`. -/
  E_zero_le_one : E 0 ≤ 1
  /-- `e^{−·}` is decreasing: larger argument ⇒ smaller value. -/
  E_antitone : ∀ x y, x ≤ y → E y ≤ E x

/-- The weighted majorant `d² · E(t·c)` — a typical term shape for
series majorized through the seed `E`. -/
def termMaj (U : ExpUB) (d t c : Q') : Q' := d * d * U.E (t * c)

/-- The weighted majorant is nonnegative (`d² ≥ 0`, `E ≥ 0`). -/
theorem termMaj_nonneg (U : ExpUB) (d t c : Q') (hd : (0 : Q') ≤ d) :
    (0 : Q') ≤ termMaj U d t c := by
  show (0 : Q') ≤ d * d * U.E (t * c)
  exact Q'.mul_nonneg (d * d) (U.E (t * c)) (Q'.mul_nonneg d d hd hd) (U.E_pos _)

end ConstructiveReals.ExpBound

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.ExpBound.termMaj_nonneg
