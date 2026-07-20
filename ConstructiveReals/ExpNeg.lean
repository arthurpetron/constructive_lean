/-
Level-2 sketch: the constructive `e^{−x}` for rational `x`, discharging
the `ExpUB` seed that `Constructive/ExpBound.lean` leaves abstract.

This is the **MVP/sketch** form (cf. `Reals.lean`, `Geometric.lean`,
which ship a compiling core plus a documented "Open work" section).  It
delivers the `Q'`-expressible series machinery and the structural facts
that are provable now; the convergence-modulus proof that upgrades
`partialSum` into a genuine `CReal` — and the bracket lemmas that
discharge the `ExpUB` fields — are derived in prose below and scoped as a
ledgered follow-on.  No theorem here is a `sorry`.

# The key observation: `e^{−x}` of a *rational* has *rational* partials

`e^{−x} = Σ_{k≥0} (−x)^k / k!`.  For `x : Q'` every term is rational, and
the term-to-term ratio is `(−x)/(k+1)` — a `Q'` multiplication by
`1/(k+1) = Q'.mkPos 1 (k+1)`.  So the partial sums are computable in `Q'`
with **no real arithmetic at all**.  This is why the constructive real
`expNeg x` can be built directly as the `CReal` whose `approx n` is the
`n`-term partial sum: the approximations live in `Q'`, only the *limit*
is a `CReal`.  Concretely (below): `term`, `partialSum`, and the rfl
recurrences are all here and compile.

# The modulus (sketch of the deferred `cauchy` proof)

To make `partialSum x` a `CReal` we owe the regular-Cauchy modulus:
`∀ ε > 0, ∃ N, ∀ m,n ≥ N, |Sₘ − Sₙ| ≤ ε`.  The clean route, valid for the
closure's use (`x = t·C₂ ≥ 0`):

  * **Restrict to a remainder regime `N₀ > x`.**  For `k ≥ N₀` the ratio
    `x/(k+1) ≤ x/(N₀+1) =: r < 1` (a `Q'` inequality), so the term
    magnitudes `|t_k| = x^k/k!` are dominated by a *geometric* sequence
    `|t_{N₀}|·r^{k−N₀}`.
  * **Geometric tail.**  `Σ_{k≥N} |t_k| ≤ |t_{N₀}|·r^{N−N₀}/(1−r)`, a
    `Q'` value — this is exactly the closed form deferred in
    `Geometric.lean` (`geometric_tail_closure_strong`).  Picking `N` with
    `r^{N−N₀} ≤ ε·(1−r)/|t_{N₀}|` (possible since `r^k → 0`, an
    `∃`-witness by induction on the rational `ε`) gives the modulus.
  * `|Sₘ − Sₙ| ≤ Σ_{k≥min(m,n)} |t_k|` since the partials differ by a
    block of terms; the geometric tail bounds it.

So `expNeg`'s modulus reduces to the **same geometric closed form** the
budget tail already needs — one piece of `Q'` arithmetic unlocks both.

# Discharging `ExpUB` (sketch)

With `expNeg x : CReal` in hand, the `ExpBound.ExpUB` fields become:

  * `E_pos`     — `e^{−x} ≥ 0`: every partial sum from an even cut is ≥ 0
                  for `x ∈ [0,1]`; in general use the dominated bracket.
  * `E_zero_le_one` — `e^{0} = 1`: `partialSum 0 n = 1` for `n ≥ 1`
                  (the `x = 0` series is `1 + 0 + …`), a rfl-level fact.
  * `E_antitone` — `x ≤ y ⇒ e^{−y} ≤ e^{−x}`: termwise on the dominated
                  series, lifted through `CReal.ofQ'_le_of_approx_ge`.
  * a usable *rational* `E`: the truncated lower bound `eₘ(x) = Σ_{k≤2m}
                  (−x)^k/k! ≤ e^{x}` (for `x ≥ 0`, even cut over-estimates)
                  gives `e^{−x} ≤ 1/eₘ(x)`; or, division-free, expose the
                  bound as `e^{−x}·eₘ(x) ≤ 1` — the form `ExpBound` can use
                  without `Q'.div`.

The bracket facts (`even cut ≥ limit ≥ odd cut` for `x ∈ [0,1]`) need the
alternating-decreasing argument, hence `Q'` term-magnitude monotonicity —
the same `mul_le_mul_of_nonneg_left` gap noted in `Geometric.lean`.

# Open work (ledgered, not `sorry`)

The shared dependencies are now **discharged**: the `Q'` semiring-`eqv`
layer (`RationalsMul.lean`: `mul_comm/assoc/add_eqv`,
`mul_le_mul_of_nonneg_left`, congruence) and the geometric tail closed
form (`GeometricTail.lean`: `geometric_tail_closure`) both exist and are
axiom-clean.  What remains for `expNeg`:

  * `expNeg (x : Q') : CReal` — the `cauchy` field.  Its analytic core
    (geometric tail past `N₀ > x`) is now `geometric_tail_closure`; the
    residual is the *term-magnitude* control: `|t_{k+1}| ≤ r·|t_k|` for
    `k ≥ N₀` (ratio `x/(k+1) ≤ r < 1`), the alternating two-sided block
    bound `|Sₘ − Sₙ| ≤` tail, and the `∃N` witness from `ε` (factorial
    growth).  No new shared lemmas — only series-specific `Q'` work.
  * `expNeg_le_one_of_nonneg`, `expNeg_antitone`, the `ExpUB` instance
    (and its `E_bounds` tie `expNeg x ≤ ofQ' (E x)`), then the SU(3)
    `Z_t` CReal upper bound feeding `ExpBound.Z_upper_su3`.

# Axiom-gate (see README: axiom policy)

Every theorem below reports `[propext]` or empty.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.RationalsMul
import ConstructiveReals.GeometricTail
import ConstructiveReals.HalfPow
import ConstructiveReals.RatNat
import ConstructiveReals.CRealLe

namespace ConstructiveReals.ExpNeg

open ConstructiveReals
open ConstructiveReals.RationalTail
open ConstructiveReals.HalfPow
open ConstructiveReals.RatNat

/-! ## The series, in `Q'`

`term x k` is the `k`-th series term `(−x)^k / k!`, via the ratio
recurrence `t_{k+1} = t_k · (−x)/(k+1)`.  `partialSum x n = Σ_{k<n} t_k`.
Both are pure `Q'`; the division by `(k+1)` is `Q'.mkPos 1 (k+1)`. -/

/-- `k`-th term of the `e^{−x}` series.  `t_0 = 1`,
`t_{k+1} = t_k · ((−x) · 1/(k+1))`. -/
def term (x : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => term x k * ((-x) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))

/-- `n`-term partial sum `Σ_{k<n} term x k`. -/
def partialSum (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => partialSum x n + term x n

@[simp] theorem term_zero (x : Q') : term x 0 = 1 := rfl

@[simp] theorem term_succ (x : Q') (k : Nat) :
    term x (k + 1) = term x k * ((-x) * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) := rfl

@[simp] theorem partialSum_zero (x : Q') : partialSum x 0 = 0 := rfl

@[simp] theorem partialSum_succ (x : Q') (n : Nat) :
    partialSum x (n + 1) = partialSum x n + term x n := rfl

/-- Sanity check that the recurrence is wired correctly: the 1-term
partial sum is `1` (the `k = 0` term), for every `x`. -/
theorem partialSum_one (x : Q') : partialSum x 1 = 1 := by
  simp only [partialSum_succ, partialSum_zero, term_zero, Q'.zero_add']

/-- The 2-term partial sum is `1 + t₁` (with `t₁ ≃ −x` the first-order
term).  Stated against the structural `1 + term x 1` rather than the
reduced `1 − x`, since `Q'` equality is structural, not semantic — the
`≃ 1 − x` form holds only up to `Q'.eqv` (cf. `Rationals.lean`). -/
theorem partialSum_two (x : Q') : partialSum x 2 = 1 + term x 1 := by
  show partialSum x 1 + term x 1 = 1 + term x 1
  rw [partialSum_one]

/-! ## The magnitude series `Σ xᵏ/k!` (all nonnegative)

`termAbs x k = xᵏ/k! = |term x k|` (for `x ≥ 0`), via the same recurrence
with `+x` in place of `−x`.  It dominates `term x k` two-sidedly
(`−termAbs ≤ term ≤ termAbs`), which is what turns the alternating series'
block differences into a (sign-free) magnitude tail — the first half of
the Cauchy modulus.  `Q'.mkPos 1 (k+1) (Nat.succ_pos _)` is `Q'.invSucc k`
definitionally, so `Q'.invSucc_nonneg` discharges the factor's sign. -/

/-- `k`-th magnitude term `xᵏ/k!`. -/
def termAbs (x : Q') : Nat → Q'
  | 0 => 1
  | k + 1 => termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))

@[simp] theorem termAbs_zero (x : Q') : termAbs x 0 = 1 := rfl

@[simp] theorem termAbs_succ (x : Q') (k : Nat) :
    termAbs x (k + 1) = termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _)) := rfl

/-- The magnitude partial sum `Σ_{k<n} termAbs x k`. -/
def partialSumAbs (x : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => partialSumAbs x n + termAbs x n

@[simp] theorem partialSumAbs_zero (x : Q') : partialSumAbs x 0 = 0 := rfl

@[simp] theorem partialSumAbs_succ (x : Q') (n : Nat) :
    partialSumAbs x (n + 1) = partialSumAbs x n + termAbs x n := rfl

/-- For `x ≥ 0`, every magnitude term is nonnegative. -/
theorem termAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ k, (0 : Q') ≤ termAbs x k
  | 0 => by show (0 : Q') ≤ 1; decide
  | k + 1 => by
    show (0 : Q') ≤ termAbs x k * (x * Q'.mkPos 1 (k + 1) (Nat.succ_pos _))
    exact Q'.mul_nonneg _ _ (termAbs_nonneg x hx k)
      (Q'.mul_nonneg _ _ hx (Q'.invSucc_nonneg k))

/-! ## The alternating → magnitude two-sided bound

`−(termAbs x k) ≤ term x k ≤ termAbs x k` for `x ≥ 0`.  This is the
conceptual core that turns the *signed* alternating series into the
*nonnegative* magnitude series: it lets the block differences
`partialSum x m − partialSum x n` be bounded by the magnitude tail
`partialSumAbs x m − partialSumAbs x n`, which is the route to the Cauchy
modulus without any absolute-value construction on `Q'`.

Proved by induction: the step uses `term x (k+1) = term x k · (−x)·c`,
`termAbs x (k+1) = termAbs x k · (x·c)`, and the negation/congruence
`eqv` laws from `RationalsMul.lean`, chained through `≤` via
`le_of_eqv`/`ge_of_eqv` (the symmetric `±term ≤ termAbs` form keeps each
side using one induction hypothesis, with no double-negation). -/
theorem term_two_sided (x : Q') (hx : (0 : Q') ≤ x) :
    ∀ k, term x k ≤ termAbs x k ∧ (-(term x k)) ≤ termAbs x k
  | 0 => by
    refine ⟨?_, ?_⟩
    · show (1 : Q') ≤ 1; exact Q'.le_refl' 1
    · show (-(1 : Q')) ≤ 1; decide
  | k + 1 => by
    obtain ⟨h1, h2⟩ := term_two_sided x hx k
    -- `Q'.invSucc k` is `Q'.mkPos 1 (k+1) (Nat.succ_pos _)` definitionally.
    have he : (0 : Q') ≤ x * Q'.invSucc k :=
      Q'.mul_nonneg _ _ hx (Q'.invSucc_nonneg k)
    refine ⟨?_, ?_⟩
    · -- term x (k+1) = term x k · ((−x)·c) ≤ termAbs x k · (x·c)
      show term x k * ((-x) * Q'.invSucc k) ≤ termAbs x k * (x * Q'.invSucc k)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left (term x k) ((-x) * Q'.invSucc k)
          (-(x * Q'.invSucc k)) (Q'.neg_mul_eqv x (Q'.invSucc k))))
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_neg_eqv (term x k) (x * Q'.invSucc k)))
          (Q'.le_trans' _ _ _
            (Q'.ge_of_eqv (Q'.neg_mul_eqv (term x k) (x * Q'.invSucc k)))
            (Q'.mul_le_mul_of_nonneg_right (-(term x k)) (termAbs x k)
              (x * Q'.invSucc k) h2 he)))
    · -- −(term x (k+1)) ≤ termAbs x k · (x·c)
      show (-(term x k * ((-x) * Q'.invSucc k))) ≤ termAbs x k * (x * Q'.invSucc k)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (term x k) ((-x) * Q'.invSucc k) (-(x * Q'.invSucc k))
            (Q'.neg_mul_eqv x (Q'.invSucc k)))))
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (term x k) (x * Q'.invSucc k))))
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.neg_neg_eqv (term x k * (x * Q'.invSucc k))))
            (Q'.mul_le_mul_of_nonneg_right (term x k) (termAbs x k)
              (x * Q'.invSucc k) h1 he)))

/-! ## Block bound: alternating partial-sum differences ≤ magnitude block

`blockAbs x n d = Σ_{j<d} termAbs x (n+j)` is the (nonnegative) magnitude
of the term block `[n, n+d)`.  The two-sided bound says the *signed*
partial-sum difference over that block is dominated by it — the bridge
from `term_two_sided` to the Cauchy modulus (a `Q'`, sign-free tail
two-sidedly bounding the alternating partials, no abs construction).

`block_upper` is the clean half (`add_assoc` only).  `block_lower` is the
standing follow-on: its step must commute a term past `blockAbs`, which
needs *additive* `eqv`-congruence (`a ≃ b → a+c ≃ b+c`), built like
`mul_eqv_congr_left` via a bespoke `Int` rearrangement — the AC-`simp`
route that sufficed for 3-term `add_assoc_eqv` times out on the 4-term
rearrangement. -/

/-- Magnitude of the term block `[n, n+d)`: `Σ_{j<d} termAbs x (n+j)`. -/
def blockAbs (x : Q') (n : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 => blockAbs x n d + termAbs x (n + d)

@[simp] theorem blockAbs_zero (x : Q') (n : Nat) : blockAbs x n 0 = 0 := rfl

@[simp] theorem blockAbs_succ (x : Q') (n d : Nat) :
    blockAbs x n (d + 1) = blockAbs x n d + termAbs x (n + d) := rfl

/-- `0 ≤ term x k + termAbs x k` for `x ≥ 0` (from `term_two_sided.2`,
via `−(term) + term ≃ 0` and `add_comm`). -/
theorem term_add_termAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ term x k + termAbs x k :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_add_self_eqv (term x k)))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right (-(term x k)) (termAbs x k) (term x k)
        (term_two_sided x hx k).2)
      (Q'.le_of_eqv (Q'.add_comm_eqv (termAbs x k) (term x k))))

/-- **Block upper bound.**  `partialSum x (n+d) ≤ partialSum x n + blockAbs x n d`.
By induction on `d`: the step replaces `term` by `termAbs` in place
(`term ≤ termAbs`) and regroups with `add_assoc` — no commutation, so no
additive congruence is needed. -/
theorem block_upper (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    ∀ d, partialSum x (n + d) ≤ partialSum x n + blockAbs x n d
  | 0 => by
    show partialSum x n ≤ partialSum x n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_upper x hx n d
    show partialSum x (n + d) + term x (n + d)
          ≤ partialSum x n + (blockAbs x n d + termAbs x (n + d))
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (partialSum x (n + d)) (term x (n + d)) (termAbs x (n + d))
        (term_two_sided x hx (n + d)).1)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right (partialSum x (n + d)) (partialSum x n + blockAbs x n d)
          (termAbs x (n + d)) ih)
        (Q'.le_of_eqv (Q'.add_assoc_eqv (partialSum x n) (blockAbs x n d)
          (termAbs x (n + d)))))

/-- **Block lower bound.**  `partialSum x n ≤ partialSum x (n+d) + blockAbs x n d`.
By induction on `d`: the step injects the nonnegative `term + termAbs`
(`term_add_termAbs_nonneg`) and re-sorts the four summands with
`add_swap_inner` — this is the half that needs additive `eqv`-congruence. -/
theorem block_lower (x : Q') (hx : (0 : Q') ≤ x) (n : Nat) :
    ∀ d, partialSum x n ≤ partialSum x (n + d) + blockAbs x n d
  | 0 => by
    show partialSum x n ≤ partialSum x n + 0
    exact Q'.add_le_self_of_nonneg _ _ (Q'.le_refl' 0)
  | d + 1 => by
    have ih := block_lower x hx n d
    show partialSum x n
          ≤ (partialSum x (n + d) + term x (n + d))
            + (blockAbs x n d + termAbs x (n + d))
    refine Q'.le_trans' _ _ _ ih ?_
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (partialSum x (n + d) + blockAbs x n d)
        (term x (n + d) + termAbs x (n + d)) (term_add_termAbs_nonneg x hx (n + d)))
      (Q'.le_of_eqv (Q'.add_swap_inner (partialSum x (n + d)) (blockAbs x n d)
        (term x (n + d)) (termAbs x (n + d))))

/-! ## Geometric domination of the magnitude terms

Past a cutoff `N₀ > x` the ratio `termAbs(k+1)/termAbs(k) = x/(k+1)` is
`≤ x/(N₀+1) =: r < 1`, so `termAbs x (N₀+j) ≤ termAbs x N₀ · rʲ`.  This is
what feeds the magnitude block into the geometric tail bound
(`GeometricTail.geometric_tail_closure`). -/

/-- `invSucc` is antitone: `k ≤ m → invSucc m ≤ invSucc k` (`1/(m+1) ≤ 1/(k+1)`).
Lives here (not `RationalsMul`) because `invSucc` is defined in `Reals`. -/
theorem invSucc_le_of_le {k m : Nat} (h : k ≤ m) : Q'.invSucc m ≤ Q'.invSucc k := by
  show (Q'.invSucc m).num * ((Q'.invSucc k).den : Int)
      ≤ (Q'.invSucc k).num * ((Q'.invSucc m).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_num, Q'.invSucc_den, Q'.invSucc_den,
      Int.one_mul, Int.one_mul]
  exact_mod_cast Nat.succ_le_succ h

/-- **Geometric domination.**  For `x ≥ 0` and a rational ratio `r` with
`x · invSucc N₀ ≤ r` (and `0 ≤ r`), the magnitude terms past `N₀` decay
geometrically: `termAbs x (N₀ + j) ≤ termAbs x N₀ · rʲ`. -/
theorem termAbs_geom_dom (x r : Q') (hx : (0 : Q') ≤ x) (N₀ : Nat)
    (hr0 : (0 : Q') ≤ r) (hbound : x * Q'.invSucc N₀ ≤ r) :
    ∀ j, termAbs x (N₀ + j) ≤ termAbs x N₀ * r ^ j
  | 0 => by
    show termAbs x N₀ ≤ termAbs x N₀ * r ^ 0
    exact Q'.ge_of_eqv (Q'.mul_one_eqv (termAbs x N₀))
  | j + 1 => by
    have ih := termAbs_geom_dom x r hx N₀ hr0 hbound j
    have hxr : x * Q'.invSucc (N₀ + j) ≤ r :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left (Q'.invSucc (N₀ + j)) (Q'.invSucc N₀) x
          (invSucc_le_of_le (Nat.le_add_right N₀ j)) hx)
        hbound
    have htAk : (0 : Q') ≤ termAbs x (N₀ + j) := termAbs_nonneg x hx (N₀ + j)
    show termAbs x (N₀ + j) * (x * Q'.invSucc (N₀ + j)) ≤ termAbs x N₀ * r ^ (j + 1)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (x * Q'.invSucc (N₀ + j)) r (termAbs x (N₀ + j))
        hxr htAk) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (termAbs x (N₀ + j)) (termAbs x N₀ * r ^ j) r
        ih hr0) ?_
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_assoc_eqv (termAbs x N₀) (r ^ j) r))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (termAbs x N₀) (r ^ j * r) (r * r ^ j)
        (Q'.mul_comm_eqv (r ^ j) r)))

/-! ## The magnitude tail is uniformly bounded: `blockAbs x N₀ d ≤ H`

Feeding the geometric domination into `geometric_tail_closure`: with a
ratio `r < 1` and a `Q'` bound `H` satisfying the one-step recurrence
`termAbs x N₀ + r·H ≤ H` (i.e. `H ≥ termAbs x N₀ / (1−r)`), every
magnitude block from `N₀` is bounded by `H`, uniformly in its length `d`.
This is the sign-free tail bound the Cauchy modulus rests on. -/

/-- Termwise comparison lifts to finite sums. -/
theorem finSum_le_finSum_of_termwise (f g : QSeq) (h : ∀ k, f k ≤ g k) :
    ∀ n, finSum f n ≤ finSum g n
  | 0 => by show (0 : Q') ≤ 0; exact Q'.le_refl' 0
  | n + 1 => by
    show finSum f n + f n ≤ finSum g n + g n
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (finSum f n) (f n) (g n) (h n))
      (Q'.add_le_add_right (finSum f n) (finSum g n) (g n)
        (finSum_le_finSum_of_termwise f g h n))

/-- `blockAbs x n d` is the finite sum of the shifted magnitude terms. -/
theorem blockAbs_eq_finSum (x : Q') (n : Nat) :
    ∀ d, blockAbs x n d = finSum (fun j => termAbs x (n + j)) d
  | 0 => rfl
  | d + 1 => by
    show blockAbs x n d + termAbs x (n + d)
        = finSum (fun j => termAbs x (n + j)) d + termAbs x (n + d)
    rw [blockAbs_eq_finSum x n d]

/-- **Uniform magnitude-tail bound.**  For `x ≥ 0`, ratio `r` with
`x · invSucc N₀ ≤ r` and `0 ≤ r`, and a bound `H ≥ 0` closing the
geometric recurrence `termAbs x N₀ + r·H ≤ H`, every block from `N₀` is
`≤ H`. -/
theorem blockAbs_le (x r H : Q') (hx : (0 : Q') ≤ x) (N₀ : Nat)
    (hr0 : (0 : Q') ≤ r) (hH : (0 : Q') ≤ H)
    (hbound : x * Q'.invSucc N₀ ≤ r)
    (hrec : termAbs x N₀ + r * H ≤ H) :
    ∀ d, blockAbs x N₀ d ≤ H := by
  intro d
  rw [blockAbs_eq_finSum]
  exact Q'.le_trans' _ _ _
    (finSum_le_finSum_of_termwise (fun j => termAbs x (N₀ + j))
      (fun j => termAbs x N₀ * r ^ j)
      (fun j => termAbs_geom_dom x r hx N₀ hr0 hbound j) d)
    (geometric_tail_closure (termAbs x N₀) r H hr0 hH hrec d)

/-! ## `termAbs x n → 0` with an explicit `Nat` modulus

Past `M := halfRatioCutoff x` the ratio is `≤ 1/2`, so
`termAbs x (M+j) ≤ termAbs x M · (1/2)ʲ` (`termAbs_geom_dom` at `r = half`),
and `(1/2)ʲ → 0` (`HalfPow.pow_half_le`).  The modulus is the closed-form
`Nat` `termAbsModulus x ε`. -/

/-- Half-powers are antitone: `half^(i+d) ≤ half^i`. -/
theorem pow_half_antitone (i : Nat) : ∀ d, half ^ (i + d) ≤ half ^ i
  | 0 => Q'.le_refl' _
  | d + 1 => by
    show half * half ^ (i + d) ≤ half ^ i
    have hy : (0 : Q') ≤ half ^ (i + d) := Q'.pow_nonneg half half_nonneg (i + d)
    have hstep : half * half ^ (i + d) ≤ half ^ (i + d) :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right half 1 (half ^ (i + d)) (by decide) hy)
        (Q'.le_of_eqv (Q'.one_mul_eqv _))
    exact Q'.le_trans' _ _ _ hstep (pow_half_antitone i d)

/-- `c · invSucc c.num.toNat ≤ 1` for `c ≥ 0` (since `c ≤ c.num.toNat`). -/
theorem mul_invSucc_toNat_le_one (c : Q') (hc : (0 : Q') ≤ c) :
    c * Q'.invSucc c.num.toNat ≤ 1 := by
  show (c * Q'.invSucc c.num.toNat).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((c * Q'.invSucc c.num.toNat).den : Int)
  have h_prod_num : (c * Q'.invSucc c.num.toNat).num = c.num * (1 : Int) := rfl
  rw [h_prod_num, Int.mul_one]
  rw [Q'.mul_den_cast c (Q'.invSucc c.num.toNat), Q'.invSucc_den]
  show c.num * (1 : Int) ≤ (1 : Int) * ((c.den : Int) * ((c.num.toNat + 1 : Nat) : Int))
  rw [Int.mul_one, Int.one_mul]
  have h_num_nn : (0 : Int) ≤ c.num := (Q'.zero_le_iff_num_nonneg c).mp hc
  have h_toNat : (Int.ofNat c.num.toNat) = c.num := Int.toNat_of_nonneg h_num_nn
  have h_cnt1 : ((c.num.toNat + 1 : Nat) : Int) = c.num + 1 := by
    rw [Int.natCast_add]
    show (Int.ofNat c.num.toNat) + (1 : Int) = c.num + 1
    rw [h_toNat]
  rw [h_cnt1]
  have h_one_le_den : (1 : Int) ≤ (c.den : Int) := by
    have : (1 : Nat) ≤ c.den := c.den_pos
    exact_mod_cast this
  have h_rhs_nn : (0 : Int) ≤ c.num + 1 := Int.add_nonneg h_num_nn (by decide)
  have h1 : c.num ≤ c.num + 1 := Int.le_add_of_nonneg_right (by decide)
  have h2 : (1 : Int) * (c.num + 1) ≤ (c.den : Int) * (c.num + 1) :=
    Int.mul_le_mul_of_nonneg_right h_one_le_den h_rhs_nn
  rw [Int.one_mul] at h2
  exact Int.le_trans h1 h2

/-- `c · (ε · invSucc c.num.toNat) ≤ ε` for `c, ε ≥ 0`: the `c·δ ≤ ε`
fact behind the `termAbs → 0` modulus, with `δ = ε · invSucc c.num.toNat`. -/
theorem mul_le_of_mul_invSucc_toNat (c ε : Q') (hc : (0 : Q') ≤ c)
    (hε : (0 : Q') ≤ ε) : c * (ε * Q'.invSucc c.num.toNat) ≤ ε := by
  have hcy : c * Q'.invSucc c.num.toNat ≤ 1 := mul_invSucc_toNat_le_one c hc
  have hrearr : (c * (ε * Q'.invSucc c.num.toNat)).eqv
      (ε * (c * Q'.invSucc c.num.toNat)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c ε (Q'.invSucc c.num.toNat)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (c * ε) (ε * c) (Q'.invSucc c.num.toNat)
          (Q'.mul_comm_eqv c ε))
        (Q'.mul_assoc_eqv ε c (Q'.invSucc c.num.toNat)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hrearr)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (c * Q'.invSucc c.num.toNat) 1 ε hcy hε)
      (Q'.le_of_eqv (Q'.mul_one_eqv ε)))

/-- The `termAbs → 0` modulus: `Nat` cutoff past which `termAbs x n ≤ ε`. -/
def termAbsModulus (x ε : Q') : Nat :=
  halfRatioCutoff x
    + (ε * Q'.invSucc (termAbs x (halfRatioCutoff x)).num.toNat).den

/-- **`termAbs x n → 0`.**  For `x ≥ 0` and `ε > 0`, every `n` at or past
`termAbsModulus x ε` has `termAbs x n ≤ ε`. -/
theorem termAbs_le_of_modulus_le (x ε : Q') (hx : (0 : Q') ≤ x)
    (hε : (0 : Q') < ε) (n : Nat) (hn : termAbsModulus x ε ≤ n) :
    termAbs x n ≤ ε := by
  -- Abbreviations.
  have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
  -- M ≤ n, so n = M + j.
  have hMn : halfRatioCutoff x ≤ n :=
    Nat.le_trans (Nat.le_add_right _ _) hn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hMn   -- n = halfRatioCutoff x + j
  subst hj
  -- c := termAbs x M, δ := ε * invSucc c.num.toNat ; j ≥ δ.den.
  have hjδ : (ε * Q'.invSucc (termAbs x (halfRatioCutoff x)).num.toNat).den ≤ j := by
    have := hn
    -- termAbsModulus = M + δ.den ≤ M + j  ⇒  δ.den ≤ j
    exact Nat.le_of_add_le_add_left this
  -- δ > 0.
  have hcnn : (0 : Q') ≤ termAbs x (halfRatioCutoff x) := termAbs_nonneg x hx _
  have hδpos : (0 : Q') < ε * Q'.invSucc (termAbs x (halfRatioCutoff x)).num.toNat := by
    show (0 : Int) * _ < (ε * Q'.invSucc _).num * ((0 : Q').den : Int)
    rw [Int.zero_mul]
    have hεnum : (0 : Int) < ε.num := by
      have h : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
      rw [Int.zero_mul] at h
      have h' : (0 : Int) < ε.num * (1 : Int) := h
      rwa [Int.mul_one] at h'
    show (0 : Int) < (ε.num * 1) * ((0 : Q').den : Int)
    rw [Int.mul_one]
    show (0 : Int) < ε.num * (1 : Int)
    rw [Int.mul_one]
    exact hεnum
  -- termAbs x (M+j) ≤ termAbs x M · half^j.
  have hgeom : termAbs x (halfRatioCutoff x + j)
      ≤ termAbs x (halfRatioCutoff x) * half ^ j :=
    termAbs_geom_dom x half hx (halfRatioCutoff x) half_nonneg
      (halfRatioCutoff_spec x hx) j
  -- half^j ≤ δ.
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hjδ   -- j = δ.den + e
  have hhalf : half ^ j
      ≤ ε * Q'.invSucc (termAbs x (halfRatioCutoff x)).num.toNat := by
    rw [he]
    exact Q'.le_trans' _ _ _
      (pow_half_antitone _ e)
      (pow_half_le _ hδpos)
  -- termAbs x M · half^j ≤ termAbs x M · δ ≤ ε.
  exact Q'.le_trans' _ _ _ hgeom
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (half ^ j)
        (ε * Q'.invSucc (termAbs x (halfRatioCutoff x)).num.toNat)
        (termAbs x (halfRatioCutoff x)) hhalf hcnn)
      (mul_le_of_mul_invSucc_toNat (termAbs x (halfRatioCutoff x)) ε hcnn hεnn))

/-! ## Assembling `expNeg : Q' → CReal`

`partialSum x` is the approximating sequence; its Cauchy modulus comes
from the block bounds (`block_upper`/`block_lower`) plus the uniform tail
bound `blockAbs ≤ ε` (`blockAbs_le` at `r = 1/2`, `H = ε`), once the
smaller index is past `termAbsModulus x (ε/2)`. -/

/-- Right-distributivity at `eqv`: `(a + b) * c ≃ a*c + b*c`. -/
theorem add_mul_eqv (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (a + b) c)
    (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c a b)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (c * a) (a * c) (c * b) (Q'.mul_comm_eqv c a))
        (Q'.add_eqv_congr_left (a * c) (c * b) (b * c) (Q'.mul_comm_eqv c b))))

/-- `half + half ≃ 1`. -/
theorem half_add_half_eqv : (half + half).eqv 1 := by decide

/-- `half·a + half·a ≃ a`. -/
theorem two_halves (a : Q') : (half * a + half * a).eqv a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv half half a))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (half + half) 1 a half_add_half_eqv)
      (Q'.one_mul_eqv a))

/-- Past the cutoff the ratio is `≤ 1/2`: `x · invSucc k ≤ half` for
`k ≥ halfRatioCutoff x`. -/
theorem x_invSucc_le_half (x : Q') (hx : (0 : Q') ≤ x) (k : Nat)
    (hk : halfRatioCutoff x ≤ k) : x * Q'.invSucc k ≤ half :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (Q'.invSucc k) (Q'.invSucc (halfRatioCutoff x)) x
      (invSucc_le_of_le hk) hx)
    (halfRatioCutoff_spec x hx)

/-- The geometric recurrence `termAbs x k + half·ε ≤ ε`, given
`termAbs x k ≤ half·ε`. -/
theorem expNeg_recurrence (x : Q') (k : Nat) (ε : Q')
    (h : termAbs x k ≤ half * ε) : termAbs x k + half * ε ≤ ε :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right (termAbs x k) (half * ε) (half * ε) h)
    (Q'.le_of_eqv (two_halves ε))

/-- Uniform tail bound: every block from a `k` past the cutoff with
`termAbs x k ≤ half·ε` is `≤ ε`. -/
theorem expNeg_tail_bound (x : Q') (hx : (0 : Q') ≤ x) (ε : Q')
    (hε : (0 : Q') ≤ ε) (k : Nat) (hcut : halfRatioCutoff x ≤ k)
    (hterm : termAbs x k ≤ half * ε) (d : Nat) :
    blockAbs x k d ≤ ε :=
  blockAbs_le x half ε hx k half_nonneg hε
    (x_invSucc_le_half x hx k hcut) (expNeg_recurrence x k ε hterm) d

/-- `0 < half · ε` for `ε > 0`. -/
theorem half_mul_pos (ε : Q') (hε : (0 : Q') < ε) : (0 : Q') < half * ε := by
  show (0 : Int) * ((half * ε).den : Int) < (half * ε).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  have hεnum : (0 : Int) < ε.num := by
    have h : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at h
    have h' : (0 : Int) < ε.num * (1 : Int) := h
    rwa [Int.mul_one] at h'
  show (0 : Int) < (1 * ε.num) * ((0 : Q').den : Int)
  rw [Int.one_mul]
  show (0 : Int) < ε.num * (1 : Int)
  rw [Int.mul_one]
  exact hεnum

/-- **The constructive exponential `e^{−x}` for `x ≥ 0`.**  Its
approximations are the rational partial sums `partialSum x`; the Cauchy
modulus is `max (halfRatioCutoff x) (termAbsModulus x (half·ε))`. -/
def expNeg (x : Q') (hx : (0 : Q') ≤ x) : CReal where
  approx := partialSum x
  cauchy := by
    intro ε hε
    have hεnn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    have hhε : (0 : Q') < half * ε := half_mul_pos ε hε
    refine ⟨max (halfRatioCutoff x) (termAbsModulus x (half * ε)),
      fun m n hm hn => ?_⟩
    -- One direction for the smaller index `k ≤ l`.
    have dir : ∀ k l : Nat,
        max (halfRatioCutoff x) (termAbsModulus x (half * ε)) ≤ k → k ≤ l →
        partialSum x l ≤ partialSum x k + ε ∧ partialSum x k ≤ partialSum x l + ε := by
      intro k l hk hkl
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
      have hcut : halfRatioCutoff x ≤ k :=
        Nat.le_trans (Nat.le_max_left _ _) hk
      have hterm : termAbs x k ≤ half * ε :=
        termAbs_le_of_modulus_le x (half * ε) hx hhε k
          (Nat.le_trans (Nat.le_max_right _ _) hk)
      have htail : blockAbs x k d ≤ ε := expNeg_tail_bound x hx ε hεnn k hcut hterm d
      exact ⟨Q'.le_trans' _ _ _ (block_upper x hx k d)
               (Q'.add_le_add_left (partialSum x k) (blockAbs x k d) ε htail),
             Q'.le_trans' _ _ _ (block_lower x hx k d)
               (Q'.add_le_add_left (partialSum x (k + d)) (blockAbs x k d) ε htail)⟩
    rcases Nat.le_total m n with hmn | hnm
    · exact ⟨(dir m n hm hmn).2, (dir m n hm hmn).1⟩
    · exact ⟨(dir n m hn hnm).1, (dir n m hn hnm).2⟩

/-! ## Sound rational upper bounds on `expNeg`

`expNeg x ≤ᵣ b` (the regularity-free `CReal.leRat`) holds whenever a
single rational certificate `partialSum x K + (termAbs x K + termAbs x K)
≤ b` holds at some `K` past the cutoff: past `K` the partials stay within
the block bound `2·termAbs x K` of `partialSum x K`, hence `≤ b`.  This is
the sound bound the one-slack `≤` could not provide. -/

/-- **Sound upper bound on `e^{−x}`.**  `expNeg x ≤ᵣ b`, certified by a
single `Q'` inequality at a cutoff index `K`. -/
theorem expNeg_leRat (x : Q') (hx : (0 : Q') ≤ x) (b : Q') (K : Nat)
    (hcut : halfRatioCutoff x ≤ K)
    (hcert : partialSum x K + (termAbs x K + termAbs x K) ≤ b) :
    CReal.leRat (expNeg x hx) b := by
  apply CReal.leRat_of_eventually
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show partialSum x (K + d) ≤ b
  have hc : (0 : Q') ≤ termAbs x K := termAbs_nonneg x hx K
  have hH : (0 : Q') ≤ termAbs x K + termAbs x K := Q'.zero_le_add _ _ hc hc
  have hhalfcc : (half * (termAbs x K + termAbs x K)).eqv (termAbs x K) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv half (termAbs x K) (termAbs x K))
      (two_halves (termAbs x K))
  have hrec : termAbs x K + half * (termAbs x K + termAbs x K)
      ≤ termAbs x K + termAbs x K :=
    expNeg_recurrence x K (termAbs x K + termAbs x K) (Q'.ge_of_eqv hhalfcc)
  have htail : blockAbs x K d ≤ termAbs x K + termAbs x K :=
    blockAbs_le x half (termAbs x K + termAbs x K) hx K half_nonneg hH
      (x_invSucc_le_half x hx K hcut) hrec d
  exact Q'.le_trans' _ _ _ (block_upper x hx K d)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left (partialSum x K) (blockAbs x K d)
        (termAbs x K + termAbs x K) htail)
      hcert)

/-- Demonstration on a tractable argument: `e^{−1} ≤ 5/12`, certified at
cutoff `K = 4` (`partialSum 1 4 + 2·termAbs 1 4 = 1/3 + 1/12 = 5/12`).
At the SU(3) operating point (`x ≈ 14.8`) the analogous certificate needs
`K ≳ 30` and partial sums with astronomically large numerators/denominators,
beyond `decide`; that bound stays a documented `Q'` fiducial in
`ExpBound`, now backed by this sound mechanism. -/
theorem expNeg_one_leRat :
    CReal.leRat (expNeg 1 (by decide)) (Q'.mkPos 5 12 (by decide)) :=
  expNeg_leRat 1 (by decide) (Q'.mkPos 5 12 (by decide)) 4 (by decide) (by decide)

end ConstructiveReals.ExpNeg

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.ExpNeg.term
#print axioms ConstructiveReals.ExpNeg.partialSum
#print axioms ConstructiveReals.ExpNeg.partialSum_one
#print axioms ConstructiveReals.ExpNeg.partialSum_two
#print axioms ConstructiveReals.ExpNeg.termAbs
#print axioms ConstructiveReals.ExpNeg.partialSumAbs
#print axioms ConstructiveReals.ExpNeg.termAbs_nonneg
#print axioms ConstructiveReals.ExpNeg.term_two_sided
#print axioms ConstructiveReals.ExpNeg.blockAbs
#print axioms ConstructiveReals.ExpNeg.term_add_termAbs_nonneg
#print axioms ConstructiveReals.ExpNeg.block_upper
#print axioms ConstructiveReals.ExpNeg.block_lower
#print axioms ConstructiveReals.ExpNeg.invSucc_le_of_le
#print axioms ConstructiveReals.ExpNeg.termAbs_geom_dom
#print axioms ConstructiveReals.ExpNeg.finSum_le_finSum_of_termwise
#print axioms ConstructiveReals.ExpNeg.blockAbs_eq_finSum
#print axioms ConstructiveReals.ExpNeg.blockAbs_le
#print axioms ConstructiveReals.ExpNeg.pow_half_antitone
#print axioms ConstructiveReals.ExpNeg.mul_invSucc_toNat_le_one
#print axioms ConstructiveReals.ExpNeg.mul_le_of_mul_invSucc_toNat
#print axioms ConstructiveReals.ExpNeg.termAbs_le_of_modulus_le
#print axioms ConstructiveReals.ExpNeg.add_mul_eqv
#print axioms ConstructiveReals.ExpNeg.two_halves
#print axioms ConstructiveReals.ExpNeg.x_invSucc_le_half
#print axioms ConstructiveReals.ExpNeg.expNeg_recurrence
#print axioms ConstructiveReals.ExpNeg.expNeg_tail_bound
#print axioms ConstructiveReals.ExpNeg.expNeg
#print axioms ConstructiveReals.ExpNeg.expNeg_leRat
#print axioms ConstructiveReals.ExpNeg.expNeg_one_leRat
