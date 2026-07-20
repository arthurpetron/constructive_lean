/-
`expNeg` respects `.eqv` of its argument:
`x.eqv y → CReal.Equiv (expNeg x) (expNeg y)`.

`expNeg x`'s approximations are `partialSum x`, built purely from `Q'`
arithmetic on `x`:

    term x (k+1)       = term x k · ((−x) · 1/(k+1))
    partialSum x (n+1) = partialSum x n + term x n

Every operation (`neg`, `mul`, `add`) respects `.eqv`, so `term` and
`partialSum` are `.eqv`-congruent in `x` (`term_eqv`, `partialSum_eqv`),
and two `.eqv`-equal arguments give pointwise-`.eqv` — hence `Equiv` —
limit sequences.

This is the substrate lemma the U.6 character-tail factorization needs:
the heat-kernel exponent `t·C₂(p,q)` equals `t·f(p)+t·f(q)+t·(pq/3)` only
up to `.eqv` (`Q'` addition is not definitional), so the exponential
addition law `expNeg_add_equiv` can be applied to the split form only
after transporting `expNeg` across that `.eqv` with `expNeg_eqv_congr`.

# Axiom-gate (see README: axiom policy)

`[propext]`, plus `Quot.sound` where `Nat`/`Int` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ExpAdd

namespace ConstructiveReals

open ConstructiveReals

/-- `term x k` is `.eqv`-congruent in `x`: each series term is a product
of `Q'` operations on `x`, all `.eqv`-respecting. -/
theorem term_eqv {x y : Q'} (hxy : x.eqv y) (k : Nat) :
    (ExpNeg.term x k).eqv (ExpNeg.term y k) := by
  induction k with
  | zero => exact Q'.eqv_refl 1
  | succ k ih =>
    rw [ExpNeg.term_succ, ExpNeg.term_succ]
    -- term x k · ((−x)·c)  ~  term y k · ((−x)·c)  ~  term y k · ((−y)·c)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ih) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_eqv_congr x y hxy))

/-- `partialSum x n` is `.eqv`-congruent in `x`. -/
theorem partialSum_eqv {x y : Q'} (hxy : x.eqv y) (n : Nat) :
    (ExpNeg.partialSum x n).eqv (ExpNeg.partialSum y n) := by
  induction n with
  | zero => exact Q'.eqv_refl 0
  | succ n ih =>
    rw [ExpNeg.partialSum_succ, ExpNeg.partialSum_succ]
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ih) ?_
    exact Q'.add_eqv_congr_left _ _ _ (term_eqv hxy n)

/-- **`expNeg` respects `.eqv`.**  Two `.eqv`-equal exponents give the same
limit (`Equiv`), since their `partialSum` sequences are pointwise `.eqv`. -/
theorem expNeg_eqv_congr {x y : Q'} (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y)
    (hxy : x.eqv y) :
    CReal.Equiv (ExpNeg.expNeg x hx) (ExpNeg.expNeg y hy) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have he : (ExpNeg.partialSum x n).eqv (ExpNeg.partialSum y n) :=
    partialSum_eqv hxy n
  have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
  refine ⟨?_, ?_⟩
  · show ExpNeg.partialSum x n ≤ ExpNeg.partialSum y n + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg _ ε hεnn)
  · show ExpNeg.partialSum y n ≤ ExpNeg.partialSum x n + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm he))
      (Q'.add_le_self_of_nonneg _ ε hεnn)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.term_eqv
#print axioms ConstructiveReals.partialSum_eqv
#print axioms ConstructiveReals.expNeg_eqv_congr
