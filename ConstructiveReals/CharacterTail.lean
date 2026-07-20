/-
U.6 tail-summation core: a constructive geometric bound for any
ratio-dominated nonnegative `Q'`-series.

The large-field character sum factorizes (U.2, `general_character_sum.py`) as
`Z_t(G) ≤ ∏_i S_i − 1` with each
`S_i(t) = Σ_{x≥0} (x+1)^{2n_i} · e^{−t·h_i(x)}`.  Each `S_i` is bounded by an
exact box plus a **geometric tail**: past a cutoff the successive-term ratio
`f(x+1)/f(x)` drops below 1 (the exponential `e^{−t·(linear)}` beats the
polynomial `((x+2)/(x+1))^{2n_i}`), so the tail is a geometric series.

This module proves the reusable engine of that step, *parametrized by the
ratio bound* (so the exponential analysis is a separate input): if a
nonnegative series `f` satisfies `f(k+1) ≤ r·f(k)` with `r < 1` (packaged via
the geometric recurrence `f₀ + r·H ≤ H`), then every partial sum is `≤ H`.
It reuses `RationalTail.geometric_tail_closure`; the new content is the
term-ratio ⇒ geometric-domination step.

# Axiom-gate (see README: axiom policy)

`[propext]` only.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.GeometricTail

namespace ConstructiveReals

open ConstructiveReals.RationalTail

namespace CharacterTail

/-- Termwise `≤` lifts to `finSum` (local copy). -/
theorem finSum_le_termwise (f g : QSeq) (h : ∀ k, f k ≤ g k) :
    ∀ n, finSum f n ≤ finSum g n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show finSum f n + f n ≤ finSum g n + g n
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_left (finSum f n) (f n) (g n) (h n))
        (Q'.add_le_add_right (finSum f n) (finSum g n) (g n)
          (finSum_le_termwise f g h n))

/-- **Geometric domination from a term-ratio bound**: if `f 0 ≤ f₀` and
`f(k+1) ≤ r·f(k)` (`r ≥ 0`), then `f(k) ≤ f₀·rᵏ`. -/
theorem geom_dom (f : QSeq) (f0 r : Q') (hr : (0 : Q') ≤ r)
    (hf0 : f 0 ≤ f0) (hdom : ∀ k, f (k + 1) ≤ r * f k) :
    ∀ k, f k ≤ f0 * r ^ k := by
  intro k
  induction k with
  | zero =>
      show f 0 ≤ f0 * r ^ 0
      exact Q'.le_trans' (f 0) f0 (f0 * r ^ 0) hf0 (Q'.ge_of_eqv (Q'.mul_one_eqv f0))
  | succ k ih =>
      show f (k + 1) ≤ f0 * r ^ (k + 1)
      have hstep : r * f k ≤ r * (f0 * r ^ k) :=
        Q'.mul_le_mul_of_nonneg_left (f k) (f0 * r ^ k) r ih hr
      have he : (r * (f0 * r ^ k)).eqv (f0 * r ^ (k + 1)) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r f0 (r ^ k)))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right (r * f0) (f0 * r) (r ^ k) (Q'.mul_comm_eqv r f0))
            (Q'.mul_assoc_eqv f0 r (r ^ k)))
      exact Q'.le_trans' (f (k + 1)) (r * (f0 * r ^ k)) (f0 * r ^ (k + 1))
        (Q'.le_trans' (f (k + 1)) (r * f k) (r * (f0 * r ^ k)) (hdom k) hstep)
        (Q'.le_of_eqv he)

/-- **Geometric tail bound.**  A ratio-dominated nonnegative series sums under
`H`: if `f 0 ≤ f₀`, `f(k+1) ≤ r·f(k)` (`0 ≤ r`), and the geometric recurrence
`f₀ + r·H ≤ H` holds (`0 ≤ H`), then `∀ N, Σ_{k<N} f(k) ≤ H`.

This bounds each character-tail factor `S_i` once the term ratio is known
`< 1`; the exponential ratio analysis (`e^{−t·(linear)} < 1`) is the separate
analytic input that supplies `hdom`. -/
theorem geom_series_le (f : QSeq) (f0 r H : Q')
    (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hf0 : f 0 ≤ f0) (hdom : ∀ k, f (k + 1) ≤ r * f k)
    (hrec : f0 + r * H ≤ H) :
    ∀ N, finSum f N ≤ H := by
  intro N
  exact Q'.le_trans' (finSum f N) (finSum (fun k => f0 * r ^ k) N) H
    (finSum_le_termwise f (fun k => f0 * r ^ k) (geom_dom f f0 r hr hf0 hdom) N)
    (geometric_tail_closure f0 r H hr hH hrec N)

end CharacterTail

end ConstructiveReals

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.CharacterTail.geom_dom
#print axioms ConstructiveReals.CharacterTail.geom_series_le
