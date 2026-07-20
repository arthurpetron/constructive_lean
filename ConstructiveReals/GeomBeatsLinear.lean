/-
**Atom (B3) kernel: a geometric series with small ratio beats a linear factor.**

`∀ k, (k : Q')·s^k ≤ 1`  for  `0 ≤ s`,  `2s ≤ 1`  (i.e. `s ≤ 1/2`).

This is the elementary closure of the SU(N) worst-case scalar inequality
(`docs/sun-uniform-cap-factorization.md` (B3)): with `e^{−tδ_N} ≤ ρ^{N−1}` (from
the geometric-domination machinery `ExpGeomBound.expNeg_mul_le_pow`, using
`δ_N ≥ c(N−1)`), the cap `(N−1)·4^{N−1} ≤ e^{tδ_N}` follows once
`(N−1)·(4ρ)^{N−1} ≤ 1`, i.e. `k·s^k ≤ 1` with `s = 4ρ ≤ 1/2` — the geometric
decay `s^k` (rational base `< 1`) crushes the linear `k`.  THIS lemma is that
fact, in pure `Q'`/`Int` (the exponential half is `expNeg_mul_le_pow`).

Proof: `(k+1)·s^{k+1} ≤ s` by induction (the sequence `(k+1)s^{k+1}` is
non-increasing once `(k+2)s ≤ k+1`, which holds since `2s ≤ 1`), then
`k·s^k ≤ s ≤ 1`.

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Geometric
import ConstructiveReals.RationalsMul

namespace ConstructiveReals

open ConstructiveReals

/-- `0 ≤ s` ⟹ `0 ≤ s.num`. -/
private theorem num_nonneg_of_nonneg {s : Q'} (hs0 : (0 : Q') ≤ s) : (0 : Int) ≤ s.num := by
  rw [Q'.zero_le_iff_num_nonneg] at hs0; exact hs0

/-- From `2s ≤ 1`: `2·s.num ≤ s.den`. -/
private theorem two_num_le_den {s : Q'} (h2s : 2 * s ≤ 1) : 2 * s.num ≤ (s.den : Int) := by
  have hc : (2 * s).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((2 * s).den : Int) := h2s
  have hn : (2 * s).num = 2 * s.num := rfl
  have hd : ((2 * s).den : Int) = (s.den : Int) := by
    rw [Q'.mul_den_cast]
    have h2d : ((2 : Q').den : Int) = 1 := rfl
    rw [h2d, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [hn, hd, h1n, h1d] at hc
  omega

/-- **`(k+2)·s ≤ k+1`** for `0 ≤ s`, `2s ≤ 1`.  The non-increase condition. -/
theorem ofNat_succ_succ_mul_le {s : Q'} (hs0 : (0 : Q') ≤ s) (h2s : 2 * s ≤ 1) (k : Nat) :
    Q'.ofNat (k + 2) * s ≤ Q'.ofNat (k + 1) := by
  show (Q'.ofNat (k + 2) * s).num * ((Q'.ofNat (k + 1)).den : Int)
     ≤ (Q'.ofNat (k + 1)).num * ((Q'.ofNat (k + 2) * s).den : Int)
  have hn : (Q'.ofNat (k + 2) * s).num = ((k : Int) + 2) * s.num := by
    show (Q'.ofNat (k + 2)).num * s.num = ((k : Int) + 2) * s.num
    have he : (Q'.ofNat (k + 2)).num = ((k : Int) + 2) := by
      show ((k + 2 : Nat) : Int) = (k : Int) + 2; omega
    rw [he]
  have hd : ((Q'.ofNat (k + 2) * s).den : Int) = (s.den : Int) := by
    rw [Q'.mul_den_cast]
    have h2d : ((Q'.ofNat (k + 2)).den : Int) = 1 := rfl
    rw [h2d, Int.one_mul]
  have hbn : (Q'.ofNat (k + 1)).num = ((k : Int) + 1) := by
    show ((k + 1 : Nat) : Int) = (k : Int) + 1; omega
  have hbd : ((Q'.ofNat (k + 1)).den : Int) = 1 := rfl
  rw [hn, hd, hbn, hbd]
  -- goal: ((k+2)·s.num)·1 ≤ (k+1)·s.den
  have hsn : (0 : Int) ≤ s.num := num_nonneg_of_nonneg hs0
  have h2 : 2 * s.num ≤ (s.den : Int) := two_num_le_den h2s
  have c1 : ((k : Int) + 2) * s.num ≤ ((k : Int) + 1) * 2 * s.num :=
    Int.mul_le_mul_of_nonneg_right (by omega) hsn
  have c2 : ((k : Int) + 1) * 2 * s.num ≤ ((k : Int) + 1) * (s.den : Int) := by
    have hrw : ((k : Int) + 1) * 2 * s.num = ((k : Int) + 1) * (2 * s.num) := by
      rw [Int.mul_assoc]
    rw [hrw]
    exact Int.mul_le_mul_of_nonneg_left h2 (by omega)
  have hchain : ((k : Int) + 2) * s.num ≤ ((k : Int) + 1) * (s.den : Int) :=
    Int.le_trans c1 c2
  omega

/-- `(k+1)·s^{k+1} ≤ s` for `0 ≤ s`, `2s ≤ 1` — the non-increasing sequence
starting at `s`. -/
theorem ofNat_succ_mul_pow_le {s : Q'} (hs0 : (0 : Q') ≤ s) (h2s : 2 * s ≤ 1) :
    ∀ k, Q'.ofNat (k + 1) * s ^ (k + 1) ≤ s := by
  intro k
  induction k with
  | zero =>
      show Q'.ofNat 1 * s ^ (0 + 1) ≤ s
      rw [Q'.pow_succ, Q'.pow_zero]
      -- goal: ofNat 1 * (s * 1) ≤ s
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 1) _ _ (Q'.mul_one_eqv s)) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 s (by decide)) (Q'.one_mul_eqv s)
  | succ k ih =>
      show Q'.ofNat (k + 2) * s ^ (k + 2) ≤ s
      have hpownn : (0 : Q') ≤ s ^ (k + 1) := Q'.pow_nonneg s hs0 (k + 1)
      have hassoc : (Q'.ofNat (k + 2) * s ^ (k + 2)).eqv
          ((Q'.ofNat (k + 2) * s) * s ^ (k + 1)) := by
        rw [Q'.pow_succ]
        exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (k + 2)) s (s ^ (k + 1)))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNat_succ_succ_mul_le hs0 h2s k) hpownn) ?_
      exact ih

/-- **Geometric-beats-linear.**  `(k : Q')·s^k ≤ 1` for every `k`, given
`0 ≤ s` and `2s ≤ 1` (`s ≤ 1/2`).  The exponential half of atom (B3) is
`ExpGeomBound.expNeg_mul_le_pow`; this is the elementary scalar tail. -/
theorem geom_beats_linear {s : Q'} (hs0 : (0 : Q') ≤ s) (h2s : 2 * s ≤ 1) :
    ∀ k, Q'.ofNat k * s ^ k ≤ 1 := by
  intro k
  have hs1 : s ≤ 1 := by
    show s.num * ((1 : Q').den : Int) ≤ (1 : Q').num * (s.den : Int)
    have hsn : (0 : Int) ≤ s.num := num_nonneg_of_nonneg hs0
    have h2 : 2 * s.num ≤ (s.den : Int) := two_num_le_den h2s
    show s.num * 1 ≤ 1 * (s.den : Int)
    omega
  cases k with
  | zero =>
      show Q'.ofNat 0 * s ^ 0 ≤ 1
      rw [Q'.pow_zero]; decide
  | succ m =>
      exact Q'.le_trans' _ _ _ (ofNat_succ_mul_pow_le hs0 h2s m) hs1

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.ofNat_succ_succ_mul_le
#print axioms ConstructiveReals.ofNat_succ_mul_pow_le
#print axioms ConstructiveReals.geom_beats_linear
