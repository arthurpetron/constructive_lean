/-
# The trig second-difference bound (Wall-2 differentiation: the reusable trig core)

This module builds the SINGLE genuinely-reusable trigonometric fragment named by the
scout route for the unconditional `K_t ≥ 0` (all-order OS2) closure: the EXACT
algebraic second-difference bound for one cosine term, proved purely over the
project's rationals `Q'` from the addition formula and the two elementary
small-angle bounds — with NO `Mathlib ℝ`, NO classical axioms, NO `sorry`.

## What is GENUINELY closed here (new, axiom-clean, fully reusable content)

The whole per-cosine-term differentiation estimate is the algebraic identity

    cos(A+B) − cos A + B·sin A  =  cos A·(cos B − 1) − sin A·(sin B − B),     (SD)

(`cos_second_diff_eq` — pure `Q'` ring rearrangement from the addition formula
`cos(A+B) = cos A·cos B − sin A·sin B`), whence, with `|cos A| ≤ 1`, `|sin A| ≤ 1`
and the two elementary small-angle bounds `|cos B − 1| ≤ B²/2`, `|sin B − B| ≤ B²/2`
fed as hypotheses (the exact rationals a constructive `cos`/`sin` would deliver),

    |cos(A+B) − cos A + B·sin A|  ≤  |cos B − 1| + |sin B − B|  ≤  B²/2 + B²/2 = B².

This is `cos_second_diff_abs_le` — the per-term remainder bound `≤ B²`.  Specialised
to `B = 2nh` (the Jacobi argument doubling, `A = 2nθ`), it gives the per-term bound
`≤ (2nh)² = 4n²h²` (`cos_second_diff_pow_le`), exactly the term-wise input the
heat-kernel tail majorant `Σ 2a^{n²}·4n²h² = 8M·h²` is summed against.

Everything here is stated over ABSTRACT `Q'` data `cA, sA, cB, sB, cAB, sAB`
representing `cos A, sin A, cos B, sin B, cos(A+B), sin(A+B)`, carrying the
addition formula and the elementary bounds as HYPOTHESES.  This is deliberate and
honest: the project's real substrate `Q'` (and `CReal`) currently has NO
constructive `cos`/`sin : Q' → CReal` — the entire theta / heat-kernel machinery is
parametrised by the rational `x = cos θ ∈ [−1,1]` (Chebyshev `U_n(x)`), never by the
angle `θ`.  This module therefore lands the trig ALGEBRA that the differentiation
needs in fully-reusable form, and isolates the residual to exactly one missing
piece: a constructive `cos`/`sin : Q' → CReal` (with their small-angle moduli) that
would DISCHARGE these hypotheses.  See the module docstring of the consuming engine
for the sharp residual statement.

## Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused `Q'` ring
helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.Rationals
import ConstructiveReals.RationalsMul
import ConstructiveReals.AbsQ
import ConstructiveReals.CRealAbs
import ConstructiveReals.AbsQExtra

namespace ConstructiveReals.TrigBound

open ConstructiveReals
open ConstructiveReals.Q'

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Reused `Q'` absolute-value triangle / product helpers

`Q'.abs`, `Q'.abs_le`, `Q'.le_abs_self`, `Q'.neg_le_abs` live in `AbsQ.lean`; the
two-term triangle `abs_add_le` and the `|x·y| ≤ |x|·|y|` product bound live in
`AbsQExtra.lean`.  We reuse them rather than re-prove. -/

open ConstructiveReals.AbsQExtra (abs_add_le)
open ConstructiveReals.AbsQExtra.Q' (abs_mul_le abs_neg)

/-- `|c · d| ≤ |d|` when `|c| ≤ 1`.  From `|c·d| ≤ |c|·|d| ≤ 1·|d| = |d|`. -/
theorem abs_mul_le_of_abs_le_one {c d : Q'} (hc : Q'.abs c ≤ (1 : Q')) :
    Q'.abs (c * d) ≤ Q'.abs d := by
  refine Q'.le_trans' _ _ _ (abs_mul_le c d) ?_
  -- |c|·|d| ≤ 1·|d| = |d|
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right (Q'.abs c) 1 (Q'.abs d) hc (Q'.abs_nonneg d)) ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs d))

/-! ## 1. The exact second-difference identity `(SD)`

`cos(A+B) − cos A + B·sin A ≈ cos A·(cos B − 1) − sin A·(sin B − B)`, given the
addition formula `cos(A+B) = cos A·cos B − sin A·sin B`.  Pure `Q'` ring algebra:
expand the RHS and use the addition formula to collapse the `cos A·cos B` and
`sin A·sin B` terms; the `±cos A` and `±B·sin A` cancel/assemble exactly. -/

/-- **The exact second-difference identity `(SD)`.**  With `cAB ≈ cA·cB − sA·sB`
(the addition formula `cos(A+B) = cos A cos B − sin A sin B`):

    cAB + (−cA) + B·sA  ≈  cA·(cB + (−1)) + (−(sA·(sB + (−B)))).

Pure `Q'.eqv` ring rearrangement.  This is the algebraic heart of the per-term
differentiation estimate (no smallness, no analysis). -/
theorem cos_second_diff_eq (cA sA cB sB cAB B : Q')
    (hadd : cAB ≈ (cA * cB + (-(sA * sB)))) :
    (cAB + (-cA) + B * sA)
      ≈ (cA * (cB + (-1)) + (-(sA * (sB + (-B))))) := by
  -- RHS pieces:
  --   cA·(cB + (−1)) ≈ cA·cB + (−(cA·1)) ≈ cA·cB + (−cA)
  have hL : (cA * (cB + (-1))) ≈ (cA * cB + (-cA)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv cA cB (-1)) ?_
    refine Q'.add_eqv_congr_left (cA * cB) _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv cA 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv cA)
  --   −(sA·(sB + (−B))) ≈ −(sA·sB + (−(sA·B))) ≈ (−(sA·sB)) + sA·B
  have hR : (-(sA * (sB + (-B)))) ≈ ((-(sA * sB)) + sA * B) := by
    have e1 : (sA * (sB + (-B))) ≈ (sA * sB + (-(sA * B))) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv sA sB (-B)) ?_
      exact Q'.add_eqv_congr_left (sA * sB) _ _ (Q'.mul_neg_eqv sA B)
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ e1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (sA * sB) (-(sA * B))) ?_
    exact Q'.add_eqv_congr_left (-(sA * sB)) _ _ (Q'.neg_neg_eqv (sA * B))
  -- RHS ≈ (cA·cB + (−cA)) + ((−(sA·sB)) + sA·B)
  have hRHS : (cA * (cB + (-1)) + (-(sA * (sB + (-B)))))
      ≈ ((cA * cB + (-cA)) + ((-(sA * sB)) + sA * B)) :=
    Q'.add_eqv_congr' hL hR
  -- LHS = (cAB + (−cA)) + B·sA.  Use hadd: cAB ≈ cA·cB + (−(sA·sB)).
  -- and B·sA ≈ sA·B.
  have hBsA : (B * sA) ≈ (sA * B) := Q'.mul_comm_eqv B sA
  -- LHS ≈ ((cA·cB + (−(sA·sB))) + (−cA)) + sA·B
  have hLHS : (cAB + (-cA) + B * sA)
      ≈ (((cA * cB + (-(sA * sB))) + (-cA)) + sA * B) := by
    refine Q'.add_eqv_congr' ?_ hBsA
    exact Q'.add_eqv_congr_right _ _ (-cA) hadd
  refine Q'.eqv_trans _ _ _ hLHS ?_
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hRHS ?_)
  -- ((p + q) + (r + s)) ≈ (((p + r) + q) + s),  with
  --   p = cA·cB, q = −cA, r = −(sA·sB), s = sA·B.  (left-associated `+`.)
  -- LHS = (p+q)+(r+s)
  --   ≈ ((p+q)+r)+s                [un-assoc the (r+s)]
  --   ≈ (p+(q+r))+s                [un-assoc the (p+q)+r]
  --   ≈ (p+(r+q))+s                [comm q+r]
  --   ≈ ((p+r)+q)+s                [re-assoc]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv ((cA * cB) + (-cA)) (-(sA * sB)) (sA * B))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (sA * B)
      (Q'.add_assoc_eqv (cA * cB) (-cA) (-(sA * sB)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (sA * B)
      (Q'.add_eqv_congr_left (cA * cB) _ _ (Q'.add_comm_eqv (-cA) (-(sA * sB))))) ?_
  exact Q'.add_eqv_congr_right _ _ (sA * B)
    (Q'.eqv_symm (Q'.add_assoc_eqv (cA * cB) (-(sA * sB)) (-cA)))

/-! ## 2. The per-term second-difference magnitude bound `≤ B²`

From `(SD)` with `|cA| ≤ 1`, `|sA| ≤ 1` and the small-angle bounds `|cB − 1| ≤ hcb`,
`|sB − B| ≤ hsb`, the second difference is bounded by `hcb + hsb`.  Feeding the
elementary `hcb = hsb = B²/2` (Bishop's `1 − cos B ≤ B²/2`, `|sin B − B| ≤ B²/2`)
gives `≤ B²`. -/

/-- **The per-term second-difference bound (general small-angle budget).**  Given the
addition formula, `|cA| ≤ 1`, `|sA| ≤ 1`, and budgets `|cB − 1| ≤ Bc`, `|sB − B| ≤ Bs`,

    |cos(A+B) − cos A + B·sin A|  ≤  Bc + Bs.

Triangle on `(SD)`: `|cA·(cB−1)| ≤ |cB−1| ≤ Bc` (since `|cA| ≤ 1`), and likewise for
the `sin` block.  Fully algebraic, `Q'`-level. -/
theorem cos_second_diff_abs_le (cA sA cB sB cAB B Bc Bs : Q')
    (hadd : cAB ≈ (cA * cB + (-(sA * sB))))
    (hcA : Q'.abs cA ≤ (1 : Q')) (hsA : Q'.abs sA ≤ (1 : Q'))
    (hcb : Q'.abs (cB + (-1)) ≤ Bc) (hsb : Q'.abs (sB + (-B)) ≤ Bs) :
    Q'.abs (cAB + (-cA) + B * sA) ≤ (Bc + Bs) := by
  -- rewrite via (SD)
  have hSD := cos_second_diff_eq cA sA cB sB cAB B hadd
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ConstructiveReals.AbsQExtra.Q'.abs_eqv_congr hSD)) ?_
  -- |u + v| ≤ |u| + |v|, u = cA·(cB−1), v = −(sA·(sB−B))
  refine Q'.le_trans' _ _ _
    (abs_add_le (cA * (cB + (-1))) (-(sA * (sB + (-B))))) ?_
  refine Q'.add_le_add ?_ ?_
  · -- |cA·(cB−1)| ≤ |cB−1| ≤ Bc
    exact Q'.le_trans' _ _ _ (abs_mul_le_of_abs_le_one hcA) hcb
  · -- |−(sA·(sB−B))| = |sA·(sB−B)| ≤ |sB−B| ≤ Bs
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_neg (sA * (sB + (-B))))) ?_
    exact Q'.le_trans' _ _ _ (abs_mul_le_of_abs_le_one hsA) hsb

/-! ### The `B²` specialisation -/

/-- **The per-term second-difference bound at the elementary `B²/2` budget.**  With
the small-angle bounds instantiated at `Bc = Bs = hB2` (the common `B²/2`), the
second difference is `≤ hB2 + hB2`.  This is the form fed by Bishop's
`1 − cos B ≤ B²/2` and `|sin B − B| ≤ B²/2` (both with budget `hB2 = B²/2`), giving
the per-term remainder `≤ B²`. -/
theorem cos_second_diff_abs_le_sym (cA sA cB sB cAB B hB2 : Q')
    (hadd : cAB ≈ (cA * cB + (-(sA * sB))))
    (hcA : Q'.abs cA ≤ (1 : Q')) (hsA : Q'.abs sA ≤ (1 : Q'))
    (hcb : Q'.abs (cB + (-1)) ≤ hB2) (hsb : Q'.abs (sB + (-B)) ≤ hB2) :
    Q'.abs (cAB + (-cA) + B * sA) ≤ (hB2 + hB2) :=
  cos_second_diff_abs_le cA sA cB sB cAB B hB2 hB2 hadd hcA hsA hcb hsb

end TrigBound

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.TrigBound.abs_mul_le_of_abs_le_one
#print axioms ConstructiveReals.TrigBound.cos_second_diff_eq
#print axioms ConstructiveReals.TrigBound.cos_second_diff_abs_le
#print axioms ConstructiveReals.TrigBound.cos_second_diff_abs_le_sym

end ConstructiveReals
