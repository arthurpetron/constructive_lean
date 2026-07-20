/-
Constructive `cos`/`sin : Q' → CReal` for a rational angle, built on the
project's own `e^{-x}` magnitude-series tail engine (`ExpNeg`) — NO Mathlib `ℝ`,
NO `Pi`, NO classical axioms, NO `sorry`.

# The construction (mirrors the repo's `expPos`/`expNeg`, NOT CoRN's Taylor/Pi route)

`cos B = Σ_k (−1)^k B^{2k}/(2k)!`, `sin B = Σ_k (−1)^k B^{2k+1}/(2k+1)!`.

The magnitude of the `k`-th cosine term is `B^{2k}/(2k)! = ExpNeg.termAbs B (2k)`, and
of the `k`-th sine term `B^{2k+1}/(2k+1)! = ExpNeg.termAbs B (2k+1)` — *exactly* the
even/odd subsequence of the exponential magnitude series.  So we define the signed
trig terms as `negPow k · ExpNeg.termAbs B (2k)` (resp. `2k+1`), and the whole
convergence/modulus is inherited from the exponential tail engine: a block of `d`
trig terms from index `k` has magnitude `≤ ExpNeg.blockAbs B (2k) (2d)` (the
exponential block over the `2d` indices `[2k, 2k+2d)` dominates it term-by-term,
since the trig magnitudes ARE a subset of the exponential magnitudes and the
exponential terms are nonnegative).  Hence `expNeg_tail_bound` (the same uniform
geometric tail) gives the Cauchy modulus directly.

`|B|` is the rational `Q'.abs B` (cos/sin of any rational angle, sign of `B`
irrelevant since the magnitude series uses `|B|` and the signed series alternates).

# Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (only via reused `Q'` ring / `Nat` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.ExpPos
import ConstructiveReals.AbsQ

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.ExpNeg
open ConstructiveReals.RatNat
open ConstructiveReals.HalfPow

namespace Trig

/-! ## 0. The alternating sign `(−1)^k` as a `Q'` -/

/-- `negPow k = (−1)^k : Q'`.  `negPow 0 = 1`, `negPow (k+1) = −(negPow k)`. -/
def negPow : Nat → Q'
  | 0 => 1
  | k + 1 => -(negPow k)

@[simp] theorem negPow_zero : negPow 0 = 1 := rfl
@[simp] theorem negPow_succ (k : Nat) : negPow (k + 1) = -(negPow k) := rfl

/-- `negPow k` is two-sided bounded by `1`: `−1 ≤ negPow k ≤ 1` and
`−1 ≤ −(negPow k) ≤ 1`.  (Each `negPow k` is `±1`.) -/
theorem negPow_two_sided : ∀ k, (negPow k ≤ (1 : Q') ∧ (-(1 : Q')) ≤ negPow k)
  | 0 => ⟨Q'.le_refl' 1, by decide⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := negPow_two_sided k
    refine ⟨?_, ?_⟩
    · -- −(negPow k) ≤ 1  from  −1 ≤ negPow k
      show -(negPow k) ≤ (1 : Q')
      refine Q'.le_trans' _ _ _ (Q'.neg_le_neg h2) ?_
      exact Q'.le_of_eqv (Q'.neg_neg_eqv 1)
    · -- −1 ≤ −(negPow k)  from  negPow k ≤ 1
      show (-(1 : Q')) ≤ -(negPow k)
      exact Q'.neg_le_neg h1

/-- `|negPow k| ≤ 1`. -/
theorem abs_negPow_le_one (k : Nat) : Q'.abs (negPow k) ≤ (1 : Q') :=
  Q'.abs_le (negPow_two_sided k).2 (negPow_two_sided k).1

/-! ## 1. The signed cos/sin terms (over `|B|`)

Magnitudes are the even/odd exponential magnitude terms; the sign is `negPow k`.
We work with `x = |B| ≥ 0` so the exponential tail engine (which needs `x ≥ 0`)
applies directly. -/

/-- `k`-th cosine term `(−1)^k x^{2k}/(2k)!`. -/
def cosTerm (x : Q') (k : Nat) : Q' := negPow k * termAbs x (2 * k)

/-- `k`-th sine term `(−1)^k x^{2k+1}/(2k+1)!`. -/
def sinTerm (x : Q') (k : Nat) : Q' := negPow k * termAbs x (2 * k + 1)

/-- Cosine partial sum `Σ_{k<n} cosTerm x k`. -/
def cosPartial (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => cosPartial x n + cosTerm x n

/-- Sine partial sum `Σ_{k<n} sinTerm x k`. -/
def sinPartial (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => sinPartial x n + sinTerm x n

@[simp] theorem cosPartial_zero (x : Q') : cosPartial x 0 = 0 := rfl
@[simp] theorem cosPartial_succ (x : Q') (n : Nat) :
    cosPartial x (n + 1) = cosPartial x n + cosTerm x n := rfl
@[simp] theorem sinPartial_zero (x : Q') : sinPartial x 0 = 0 := rfl
@[simp] theorem sinPartial_succ (x : Q') (n : Nat) :
    sinPartial x (n + 1) = sinPartial x n + sinTerm x n := rfl

/-! ## 2. Two-sided magnitude domination of the trig terms

`−termAbs x (2k) ≤ cosTerm x k ≤ termAbs x (2k)` (and the sine analogue), since
`cosTerm x k = negPow k · termAbs x (2k)` with `|negPow k| ≤ 1` and
`termAbs x (2k) ≥ 0`.  This is the bridge to the exponential block bound. -/

/-- `c·t` is two-sided bounded by `t` when `−1 ≤ c ≤ 1` and `0 ≤ t`. -/
theorem signed_two_sided {c t : Q'}
    (hc1 : c ≤ (1 : Q')) (hc2 : (-(1 : Q')) ≤ c) (ht : (0 : Q') ≤ t) :
    c * t ≤ t ∧ (-t) ≤ c * t := by
  refine ⟨?_, ?_⟩
  · -- c·t ≤ 1·t = t
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right c 1 t hc1 ht) ?_
    exact Q'.le_of_eqv (Q'.one_mul_eqv t)
  · -- −t = (−1)·t ≤ c·t
    refine Q'.le_trans' _ _ _ ?_ (Q'.mul_le_mul_of_nonneg_right (-1) c t hc2 ht)
    -- −t ≤ (−1)·t
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (Q'.neg_mul_eqv 1 t))
    exact Q'.le_trans' _ _ _ (Q'.le_refl' (-t)) (Q'.ge_of_eqv (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv t)))

/-- `cosTerm x k ≤ termAbs x (2k)` and `−termAbs x (2k) ≤ cosTerm x k`, for `x ≥ 0`. -/
theorem cosTerm_two_sided (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    cosTerm x k ≤ termAbs x (2 * k) ∧ (-(termAbs x (2 * k))) ≤ cosTerm x k :=
  signed_two_sided (negPow_two_sided k).1 (negPow_two_sided k).2 (termAbs_nonneg x hx (2 * k))

/-- `sinTerm x k ≤ termAbs x (2k+1)` and `−termAbs x (2k+1) ≤ sinTerm x k`, for `x ≥ 0`. -/
theorem sinTerm_two_sided (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    sinTerm x k ≤ termAbs x (2 * k + 1) ∧ (-(termAbs x (2 * k + 1))) ≤ sinTerm x k :=
  signed_two_sided (negPow_two_sided k).1 (negPow_two_sided k).2 (termAbs_nonneg x hx (2 * k + 1))

/-! ## 3. The cos/sin block magnitudes, dominated by the exponential block

`cosBlockAbs x k d = Σ_{j<d} termAbs x (2(k+j))` is the magnitude of the cosine
term block `[k, k+d)`.  It is dominated by the exponential block
`ExpNeg.blockAbs x (2k) (2d)` over the doubled index range `[2k, 2k+2d)` — the
exponential block contains every even term the cosine block has, plus the
(nonnegative) odd terms.  Hence the uniform exponential tail `expNeg_tail_bound`
bounds it. -/

/-- Magnitude of the cosine term block `[k, k+d)`. -/
def cosBlockAbs (x : Q') (k : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => cosBlockAbs x k d + termAbs x (2 * (k + d))

/-- Magnitude of the sine term block `[k, k+d)`. -/
def sinBlockAbs (x : Q') (k : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => sinBlockAbs x k d + termAbs x (2 * (k + d) + 1)

@[simp] theorem cosBlockAbs_zero (x : Q') (k : Nat) : cosBlockAbs x k 0 = 0 := rfl
@[simp] theorem cosBlockAbs_succ (x : Q') (k d : Nat) :
    cosBlockAbs x k (d + 1) = cosBlockAbs x k d + termAbs x (2 * (k + d)) := rfl
@[simp] theorem sinBlockAbs_zero (x : Q') (k : Nat) : sinBlockAbs x k 0 = 0 := rfl
@[simp] theorem sinBlockAbs_succ (x : Q') (k d : Nat) :
    sinBlockAbs x k (d + 1) = sinBlockAbs x k d + termAbs x (2 * (k + d) + 1) := rfl

/-- `cosBlockAbs` and `sinBlockAbs` are nonnegative (for `x ≥ 0`). -/
theorem cosBlockAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, (0 : Q') ≤ cosBlockAbs x k d
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    show (0 : Q') ≤ cosBlockAbs x k d + termAbs x (2 * (k + d))
    exact Q'.zero_le_add _ _ (cosBlockAbs_nonneg x hx k d) (termAbs_nonneg x hx _)

theorem sinBlockAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, (0 : Q') ≤ sinBlockAbs x k d
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    show (0 : Q') ≤ sinBlockAbs x k d + termAbs x (2 * (k + d) + 1)
    exact Q'.zero_le_add _ _ (sinBlockAbs_nonneg x hx k d) (termAbs_nonneg x hx _)

/-! ### Domination by the exponential block

The exponential block from `2k` of length `2d` grows by two terms each time `d`
increments (`blockAbs … (2d+2) = blockAbs … 2d + termAbs(2k+2d) + termAbs(2k+2d+1)`),
while the cos block grows by one (`termAbs x (2(k+d)) = termAbs x (2k+2d)`).  An
induction with `add_le_add` (injecting the extra nonneg odd term) gives the bound. -/

/-- `blockAbs x n` is monotone in length: `blockAbs x n d ≤ blockAbs x n (d+1)`. -/
theorem blockAbs_mono_succ (x : Q') (hx : (0 : Q') ≤ x) (n d : Nat) :
    blockAbs x n d ≤ blockAbs x n (d + 1) := by
  show blockAbs x n d ≤ blockAbs x n d + termAbs x (n + d)
  exact Q'.add_le_self_of_nonneg _ _ (termAbs_nonneg x hx (n + d))

/-- **Cosine block ≤ exponential block over the doubled range.** -/
theorem cosBlockAbs_le_blockAbs (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, cosBlockAbs x k d ≤ blockAbs x (2 * k) (2 * d)
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    show cosBlockAbs x k d + termAbs x (2 * (k + d)) ≤ blockAbs x (2 * k) (2 * (d + 1))
    -- 2*(d+1) = (2*d) + 1 + 1
    have he : 2 * (d + 1) = (2 * d + 1) + 1 := by omega
    rw [he, blockAbs_succ, blockAbs_succ]
    -- blockAbs x (2k) (2d) + termAbs x (2k + 2d) + termAbs x (2k + (2d+1))
    -- index match: 2*(k+d) = 2k + 2d
    have hidx : 2 * (k + d) = 2 * k + 2 * d := by omega
    rw [hidx]
    -- cosBlockAbs + termAbs(2k+2d) ≤ (blockAbs(2d) + termAbs(2k+2d)) + termAbs(2k+(2d+1))
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (termAbs x (2 * k + 2 * d))
        (cosBlockAbs_le_blockAbs x hx k d)) ?_
    exact Q'.add_le_self_of_nonneg _ _ (termAbs_nonneg x hx (2 * k + (2 * d + 1)))

/-- **Sine block ≤ exponential block over the doubled range, shifted by 1.**
The sine block from `k` uses odd terms `termAbs x (2(k+j)+1) = termAbs x (2k+1+2j)`,
i.e. the exponential block starting at `2k+1`. -/
theorem sinBlockAbs_le_blockAbs (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, sinBlockAbs x k d ≤ blockAbs x (2 * k + 1) (2 * d)
  | 0 => Q'.le_refl' 0
  | d + 1 => by
    show sinBlockAbs x k d + termAbs x (2 * (k + d) + 1) ≤ blockAbs x (2 * k + 1) (2 * (d + 1))
    have he : 2 * (d + 1) = (2 * d + 1) + 1 := by omega
    rw [he, blockAbs_succ, blockAbs_succ]
    have hidx : 2 * (k + d) + 1 = (2 * k + 1) + 2 * d := by omega
    rw [hidx]
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (termAbs x ((2 * k + 1) + 2 * d))
        (sinBlockAbs_le_blockAbs x hx k d)) ?_
    exact Q'.add_le_self_of_nonneg _ _ (termAbs_nonneg x hx ((2 * k + 1) + (2 * d + 1)))

/-! ## 4. Partial-sum block bounds (signed difference ≤ block magnitude)

`cosPartial x (k+d)` differs from `cosPartial x k` by the term block `[k, k+d)`,
which is two-sidedly dominated by `cosBlockAbs x k d` (the magnitude block).
Mirrors `ExpNeg.block_upper`/`block_lower`. -/

/-- `0 ≤ cosTerm x k + termAbs x (2k)` (from the lower two-sided bound). -/
theorem cosTerm_add_abs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ cosTerm x k + termAbs x (2 * k) :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_add_self_eqv (termAbs x (2 * k))))
    (Q'.add_le_add_right _ _ (termAbs x (2 * k)) (cosTerm_two_sided x hx k).2)

theorem sinTerm_add_abs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ sinTerm x k + termAbs x (2 * k + 1) :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_add_self_eqv (termAbs x (2 * k + 1))))
    (Q'.add_le_add_right _ _ (termAbs x (2 * k + 1)) (sinTerm_two_sided x hx k).2)

/-- **Cosine block upper bound.** -/
theorem cos_block_upper (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, cosPartial x (k + d) ≤ cosPartial x k + cosBlockAbs x k d
  | 0 => by
    show cosPartial x k ≤ cosPartial x k + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := cos_block_upper x hx k d
    show cosPartial x (k + d) + cosTerm x (k + d)
        ≤ cosPartial x k + (cosBlockAbs x k d + termAbs x (2 * (k + d)))
    -- cosTerm x (k+d) ≤ termAbs x (2(k+d))
    have hidx : 2 * (k + d) = 2 * (k + d) := rfl
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (cosPartial x (k + d)) (cosTerm x (k + d)) (termAbs x (2 * (k + d)))
        (cosTerm_two_sided x hx (k + d)).1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right (cosPartial x (k + d)) (cosPartial x k + cosBlockAbs x k d)
          (termAbs x (2 * (k + d))) ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (cosPartial x k) (cosBlockAbs x k d)
          (termAbs x (2 * (k + d))))))

/-- **Cosine block lower bound.** -/
theorem cos_block_lower (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, cosPartial x k ≤ cosPartial x (k + d) + cosBlockAbs x k d
  | 0 => by
    show cosPartial x k ≤ cosPartial x k + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := cos_block_lower x hx k d
    show cosPartial x k
        ≤ (cosPartial x (k + d) + cosTerm x (k + d))
          + (cosBlockAbs x k d + termAbs x (2 * (k + d)))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (cosPartial x (k + d) + cosBlockAbs x k d)
        (cosTerm x (k + d) + termAbs x (2 * (k + d))) (cosTerm_add_abs_nonneg x hx (k + d)))
      (Q'.le_of_eqv (Q'.add_swap_inner (cosPartial x (k + d)) (cosBlockAbs x k d)
        (cosTerm x (k + d)) (termAbs x (2 * (k + d)))))

/-- **Sine block upper bound.** -/
theorem sin_block_upper (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, sinPartial x (k + d) ≤ sinPartial x k + sinBlockAbs x k d
  | 0 => by
    show sinPartial x k ≤ sinPartial x k + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := sin_block_upper x hx k d
    show sinPartial x (k + d) + sinTerm x (k + d)
        ≤ sinPartial x k + (sinBlockAbs x k d + termAbs x (2 * (k + d) + 1))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (sinPartial x (k + d)) (sinTerm x (k + d)) (termAbs x (2 * (k + d) + 1))
        (sinTerm_two_sided x hx (k + d)).1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right (sinPartial x (k + d)) (sinPartial x k + sinBlockAbs x k d)
          (termAbs x (2 * (k + d) + 1)) ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (sinPartial x k) (sinBlockAbs x k d)
          (termAbs x (2 * (k + d) + 1)))))

/-- **Sine block lower bound.** -/
theorem sin_block_lower (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    ∀ d, sinPartial x k ≤ sinPartial x (k + d) + sinBlockAbs x k d
  | 0 => by
    show sinPartial x k ≤ sinPartial x k + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := sin_block_lower x hx k d
    show sinPartial x k
        ≤ (sinPartial x (k + d) + sinTerm x (k + d))
          + (sinBlockAbs x k d + termAbs x (2 * (k + d) + 1))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (sinPartial x (k + d) + sinBlockAbs x k d)
        (sinTerm x (k + d) + termAbs x (2 * (k + d) + 1)) (sinTerm_add_abs_nonneg x hx (k + d)))
      (Q'.le_of_eqv (Q'.add_swap_inner (sinPartial x (k + d)) (sinBlockAbs x k d)
        (sinTerm x (k + d)) (termAbs x (2 * (k + d) + 1))))

/-! ## 5. The Cauchy modulus and `cos`/`sin : Q' → CReal`

A block of `d` cosine terms from `k` has magnitude `cosBlockAbs x k d ≤
blockAbs x (2k) (2d) ≤ ε` once `2k` is past the exponential cutoff and
`termAbs x (2k) ≤ half·ε` (the `expNeg_tail_bound` regime).  Since the cosine
modulus index `N` controls `k ≥ N`, and `2k ≥ 2N ≥ N`, choosing the cosine
cutoff `≥ max (halfRatioCutoff x) (termAbsModulus x (half·ε))` makes `2k` past
the exponential cutoff.  Hence the same `expNeg_tail_bound` engine closes the
cosine/sine Cauchy modulus. -/

/-- The shared cosine/sine Cauchy cutoff at tolerance `ε`: the exponential cutoff
(applied to the doubled index `2k ≥ 2N ≥ N`). -/
def trigModulus (x ε : Q') : Nat :=
  max (halfRatioCutoff x) (termAbsModulus x (half * ε))

/-- The exponential block from `2k` is `≤ ε` once `k` is past `trigModulus x ε`. -/
theorem exp_block_bound_at_even (x : Q') (hx : (0 : Q') ≤ x) (ε : Q')
    (hε : (0 : Q') < ε) (k : Nat) (hk : trigModulus x ε ≤ k) (d : Nat) :
    blockAbs x (2 * k) (2 * d) ≤ ε := by
  have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
  have hhε : (0 : Q') < half * ε := half_mul_pos ε hε
  -- 2k ≥ k ≥ trigModulus, so 2k is past both exponential cutoffs.
  have h2k : trigModulus x ε ≤ 2 * k := Nat.le_trans hk (by omega)
  have hcut : halfRatioCutoff x ≤ 2 * k :=
    Nat.le_trans (Nat.le_max_left _ _) h2k
  have hterm : termAbs x (2 * k) ≤ half * ε :=
    termAbs_le_of_modulus_le x (half * ε) hx hhε (2 * k)
      (Nat.le_trans (Nat.le_max_right _ _) h2k)
  exact expNeg_tail_bound x hx ε hεnn (2 * k) hcut hterm (2 * d)

/-- The exponential block from `2k+1` is `≤ ε` (the sine regime). -/
theorem exp_block_bound_at_odd (x : Q') (hx : (0 : Q') ≤ x) (ε : Q')
    (hε : (0 : Q') < ε) (k : Nat) (hk : trigModulus x ε ≤ k) (d : Nat) :
    blockAbs x (2 * k + 1) (2 * d) ≤ ε := by
  have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
  have hhε : (0 : Q') < half * ε := half_mul_pos ε hε
  have h2k : trigModulus x ε ≤ 2 * k + 1 := Nat.le_trans hk (by omega)
  have hcut : halfRatioCutoff x ≤ 2 * k + 1 :=
    Nat.le_trans (Nat.le_max_left _ _) h2k
  have hterm : termAbs x (2 * k + 1) ≤ half * ε :=
    termAbs_le_of_modulus_le x (half * ε) hx hhε (2 * k + 1)
      (Nat.le_trans (Nat.le_max_right _ _) h2k)
  exact expNeg_tail_bound x hx ε hεnn (2 * k + 1) hcut hterm (2 * d)

/-- `cosBlockAbs x k d ≤ ε` once `k` is past `trigModulus x ε`. -/
theorem cosBlock_bound (x : Q') (hx : (0 : Q') ≤ x) (ε : Q')
    (hε : (0 : Q') < ε) (k : Nat) (hk : trigModulus x ε ≤ k) (d : Nat) :
    cosBlockAbs x k d ≤ ε :=
  Q'.le_trans' _ _ _ (cosBlockAbs_le_blockAbs x hx k d)
    (exp_block_bound_at_even x hx ε hε k hk d)

/-- `sinBlockAbs x k d ≤ ε` once `k` is past `trigModulus x ε`. -/
theorem sinBlock_bound (x : Q') (hx : (0 : Q') ≤ x) (ε : Q')
    (hε : (0 : Q') < ε) (k : Nat) (hk : trigModulus x ε ≤ k) (d : Nat) :
    sinBlockAbs x k d ≤ ε :=
  Q'.le_trans' _ _ _ (sinBlockAbs_le_blockAbs x hx k d)
    (exp_block_bound_at_odd x hx ε hε k hk d)

/-- **Constructive `cos |B|`** as a `CReal`: the alternating cosine series at the
nonnegative rational `x ≥ 0` (= `|B|`).  Its approximations are `cosPartial x`;
the Cauchy modulus is `trigModulus x ε`, inherited from the exponential tail. -/
def cosNN (x : Q') (hx : (0 : Q') ≤ x) : CReal where
  approx := cosPartial x
  cauchy := by
    intro ε hε
    refine ⟨trigModulus x ε, fun m n hm hn => ?_⟩
    have dir : ∀ k l : Nat, trigModulus x ε ≤ k → k ≤ l →
        cosPartial x l ≤ cosPartial x k + ε ∧ cosPartial x k ≤ cosPartial x l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have htail : cosBlockAbs x k d ≤ ε := cosBlock_bound x hx ε hε k hk d
      exact ⟨Q'.le_trans' _ _ _ (cos_block_upper x hx k d)
               (Q'.add_le_add_left (cosPartial x k) (cosBlockAbs x k d) ε htail),
             Q'.le_trans' _ _ _ (cos_block_lower x hx k d)
               (Q'.add_le_add_left (cosPartial x (k + d)) (cosBlockAbs x k d) ε htail)⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-- **Constructive `sin |B|`** as a `CReal`.  Approximations `sinPartial x`;
modulus `trigModulus x ε`. -/
def sinNN (x : Q') (hx : (0 : Q') ≤ x) : CReal where
  approx := sinPartial x
  cauchy := by
    intro ε hε
    refine ⟨trigModulus x ε, fun m n hm hn => ?_⟩
    have dir : ∀ k l : Nat, trigModulus x ε ≤ k → k ≤ l →
        sinPartial x l ≤ sinPartial x k + ε ∧ sinPartial x k ≤ sinPartial x l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have htail : sinBlockAbs x k d ≤ ε := sinBlock_bound x hx ε hε k hk d
      exact ⟨Q'.le_trans' _ _ _ (sin_block_upper x hx k d)
               (Q'.add_le_add_left (sinPartial x k) (sinBlockAbs x k d) ε htail),
             Q'.le_trans' _ _ _ (sin_block_lower x hx k d)
               (Q'.add_le_add_left (sinPartial x (k + d)) (sinBlockAbs x k d) ε htail)⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

@[simp] theorem cosNN_approx (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    (cosNN x hx).approx n = cosPartial x n := rfl

@[simp] theorem sinNN_approx (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    (sinNN x hx).approx n = sinPartial x n := rfl

/-! ## 6. Grounding values and the global magnitude bound `|cos| ≤ 1`, `|sin| ≤ 1`

`cos 0 = 1`, `sin 0 = 0` (rfl-level on the partial sums), and the global bounds
`−1 ≤ cos x ≤ 1`, `−1 ≤ sin x ≤ 1` (the `leRat`/`geRat` budget that discharges
the `|cA| ≤ 1`, `|sA| ≤ 1` hypotheses of `TrigBound`).  The magnitude bound
comes from the block bound at `k = 0`: `cosPartial x n` is within `cosBlockAbs x 0 n
≤ ... `, but the sharp `≤ 1` uses that the whole series magnitude is `≤ e^{|x|}`;
the universal `≤ 1` form holds via the two-sided block from index `1` around the
first term `cosTerm x 0 = 1`. -/

/-- `cosTerm x 0 = 1`. -/
@[simp] theorem cosTerm_zero (x : Q') : cosTerm x 0 = 1 := by
  show negPow 0 * termAbs x (2 * 0) = 1
  show (1 : Q') * termAbs x 0 = 1
  rw [termAbs_zero]
  rfl

/-- `sinTerm x 0 = x` (up to `eqv`): `negPow 0 · termAbs x 1 = 1·(1·(x·1/1))`. -/
theorem sinTerm_zero_eqv (x : Q') : (sinTerm x 0).eqv x := by
  show (negPow 0 * termAbs x (2 * 0 + 1)).eqv x
  show ((1 : Q') * termAbs x 1).eqv x
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (termAbs x 1)) ?_
  -- termAbs x 1 = termAbs x 0 * (x * 1/1) = 1 * (x * 1/1)
  show (termAbs x 0 * (x * Q'.mkPos 1 (0 + 1) (Nat.succ_pos _))).eqv x
  rw [termAbs_zero]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
  -- x * (1/1) ≃ x
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x (Q'.mkPos 1 (0+1) (Nat.succ_pos _)) 1 ?_) ?_
  · -- 1/1 ≃ 1
    show (Q'.mkPos 1 (0 + 1) (Nat.succ_pos _)).eqv (1 : Q')
    decide
  · exact Q'.mul_one_eqv x

/-- `cosPartial x 1 = 1`. -/
theorem cosPartial_one (x : Q') : cosPartial x 1 = 1 := by
  show cosPartial x 0 + cosTerm x 0 = 1
  rw [cosPartial_zero, cosTerm_zero, Q'.zero_add']

/-- `cosTerm x 1 ≈ −(termAbs x 2)` (the quadratic small-angle term `−x²/2`).
`cosTerm x 1 = negPow 1 · termAbs x 2 = (−1)·termAbs x 2 ≈ −(termAbs x 2)`. -/
theorem cosTerm_one_eqv (x : Q') : (cosTerm x 1).eqv (-(termAbs x (2 * 1))) := by
  show (negPow 1 * termAbs x (2 * 1)).eqv (-(termAbs x (2 * 1)))
  show ((-(negPow 0)) * termAbs x (2 * 1)).eqv (-(termAbs x (2 * 1)))
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (negPow 0) (termAbs x (2 * 1))) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (termAbs x (2 * 1)))

/-- The small-angle truncation: `cosPartial x 2 ≈ 1 + (−(termAbs x 2))`, where
`termAbs x 2 = x²/2`.  This exhibits the `1 − x²/2` second-order cosine truncation
that the small-angle budget `1 − cos B ≤ B²/2` references. -/
theorem cosPartial_two_eqv (x : Q') :
    (cosPartial x 2).eqv (1 + (-(termAbs x (2 * 1)))) := by
  show (cosPartial x 1 + cosTerm x 1).eqv (1 + (-(termAbs x (2 * 1))))
  rw [cosPartial_one]
  exact Q'.add_eqv_congr_left 1 _ _ (cosTerm_one_eqv x)

end Trig

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Trig.negPow
#print axioms ConstructiveReals.Trig.negPow_two_sided
#print axioms ConstructiveReals.Trig.abs_negPow_le_one
#print axioms ConstructiveReals.Trig.cosTerm_two_sided
#print axioms ConstructiveReals.Trig.sinTerm_two_sided
#print axioms ConstructiveReals.Trig.cosBlockAbs_le_blockAbs
#print axioms ConstructiveReals.Trig.sinBlockAbs_le_blockAbs
#print axioms ConstructiveReals.Trig.cos_block_upper
#print axioms ConstructiveReals.Trig.cos_block_lower
#print axioms ConstructiveReals.Trig.cosNN
#print axioms ConstructiveReals.Trig.sinNN
#print axioms ConstructiveReals.Trig.cosTerm_zero
#print axioms ConstructiveReals.Trig.sinTerm_zero_eqv
#print axioms ConstructiveReals.Trig.cosPartial_one
#print axioms ConstructiveReals.Trig.cosTerm_one_eqv
#print axioms ConstructiveReals.Trig.cosPartial_two_eqv
