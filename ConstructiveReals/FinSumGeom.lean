/-
Uniform box + geometric-tail bound on `finSum`.

The character-tail factor's rational majorant `g` is summed over `[0, N)` for
every truncation `N`.  Splitting at a box cutoff `M`: the box `Σ_{x<M} g` is a
fixed rational, and the tail `Σ_{M≤x<N} g` is a geometric series (ratio `r < 1`
past `M`) bounded by a fixed `H` (`CharacterTail.geom_series_le`).  Hence

    finSum g N  ≤  finSum g M + H   for every N,

uniformly.  This is the `Q'`-level uniform bound that, fed `leRat_csum`, bounds
every truncation of `Sᵢ` by a rational.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.CornerBound
import ConstructiveReals.CharacterTail

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail

/-- **Uniform box + geometric-tail bound.**  For a nonnegative `g` whose shifted
tail `j ↦ g(M+j)` is ratio-dominated (`g M ≤ f₀`, `g(M+(k+1)) ≤ r·g(M+k)`, and
the geometric recurrence `f₀ + r·H ≤ H`), every partial sum is bounded:
`finSum g N ≤ finSum g M + H`. -/
theorem finSum_geom_uniform (g : QSeq) (M : Nat) (f0 r H : Q')
    (hg : ∀ k, (0 : Q') ≤ g k) (hr : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hf0 : g M ≤ f0) (hdom : ∀ k, g (M + (k + 1)) ≤ r * g (M + k))
    (hrec : f0 + r * H ≤ H) :
    ∀ N, finSum g N ≤ finSum g M + H := by
  have htail : ∀ N', finSum (fun j => g (M + j)) N' ≤ H :=
    CharacterTail.geom_series_le (fun j => g (M + j)) f0 r H hr hH hf0 hdom hrec
  intro N
  rcases Nat.le_total N M with hNM | hMN
  · -- N ≤ M : finSum g N ≤ finSum g M ≤ finSum g M + H
    exact Q'.le_trans' _ _ _ (finSum_monotone_of_nonneg g hg N M hNM)
      (Q'.add_le_self_of_nonneg (finSum g M) H hH)
  · -- M ≤ N : finSum g N = finSum g M + tail ≤ finSum g M + H
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (finSum_split g M d))
      (Q'.add_le_add_left (finSum g M) _ H (htail d))

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.finSum_geom_uniform
