/-
U.6 box-term soundness — `termMaj` is a *proven* per-irrep bound.

`ExpBound.termMaj U dim t c = dim²·U.E(t·c)` is the majorant the character-tail
box sum adds up over a finite box of irreps.  Its soundness — that it really
upper-bounds the actual term `dim²·e^{−t·c}` of `Z_t` — was the "deferred to
Level 2" obligation in `ExpBound`'s header.  With the U.5 soundness
`expNeg_le_oneOver1p` (`e⁻ˣ ≤ 1/(1+x) = recipExpUB.E`) now proven, that
obligation closes: scaling the sound rational bound by the nonnegative
dimension factor (`leRat_smul_nonneg`) gives

    dim²·e^{−t·c}  ≤  dim²·recipExpUB.E(t·c)  =  termMaj recipExpUB dim t c,

as a sound `CReal.leRat`.  This is the box half of each character-tail factor
`Sᵢ`; the infinite tail past the box is the (irreducibly exponential) geometric
remainder handled by `CharacterTail.geom_series_le`.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat`/`Int` enter.  No
`Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Soundness
import ConstructiveReals.ExpBound

namespace ConstructiveReals

open ConstructiveReals

/-- **The character box term is soundly bounded by `termMaj`.**  For a
nonnegative dimension `dim`, heat-kernel time `t ≥ 0`, and Casimir `c ≥ 0`,
the actual term `dim²·e^{−t·c}` of `Z_t` has limit `≤ termMaj recipExpUB dim t c`
(`= dim²·1/(1+t·c)`).  The exponential `e^{−t·c}` is `expNeg (t·c)`. -/
theorem charTerm_leRat (dim t c : Q') (hd : (0 : Q') ≤ dim)
    (ht : (0 : Q') ≤ t) (hc : (0 : Q') ≤ c) :
    CReal.leRat
      (CReal.mul (CReal.ofQ' (dim * dim)) (ExpNeg.expNeg (t * c) (Q'.mul_nonneg t c ht hc)))
      (ExpBound.termMaj ExpUBInstance.recipExpUB dim t c) :=
  CReal.leRat_smul_nonneg (Q'.mul_nonneg dim dim hd hd)
    (expNeg_le_oneOver1p (t * c) (Q'.mul_nonneg t c ht hc))

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.charTerm_leRat
