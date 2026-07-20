/-
Rational tail bound module — global budget closure for partial sums, at Q'.

Provides the Q'-rational framework for global closures of the shape

    Σ_{k=0}^∞ η_k  <  B

at finite truncation `N`: when the cost sequence is finitely supported
(or uniformly tail-bounded), the closure is constructively provable
inside Q' with no real-number layer.

# What this module provides

A `Q'`-rational framework for budget closure:

  - `QSeq` — a sequence of `Q'` values indexed by `Nat`.
  - `finSum f N` — the finite partial sum Σ_{k=0}^{N-1} f k.
  - `partialSum_budget_closure` — the framework theorem: given an η
    sequence, a uniform bound on its partial sums, and a closure-condition
    `eta_total_bound ≤ σ̂_0`, conclude `Σ_{k<N} η_k ≤ σ̂_0` for every N.

The "geometric rational tail" structure expected by the user is realized
NOT through an exponential decay assumption on `η_k` itself (which would
require Q'.pow and exponential-bound machinery) but through the
**telescoping-bounded** structure inherent in the Python derivation:
`η_k = c_η · (K_∩(k+1) - K_∩(k))` for monotone-bounded `K_∩`, so

    Σ_{k<N} η_k  =  c_η · (K_∩(N) - K_∩(0))  ≤  c_η · K_max.

The user supplies `eta_total_bound = c_η · K_max ∈ ℚ` and the closure
condition `eta_total_bound ≤ σ̂_0 ∈ ℚ`; the module discharges the rest
via `Q'.le_trans'`.

# What this module does NOT provide

- An infinite-K convergence proof.  Q' is countable-rational, not
  constructive-reals; "Σ_{k=0}^∞" is not directly representable.
  The framework is *uniform-in-N*: it proves `∀ N, Σ_{k<N} η_k ≤ σ̂_0`,
  which is the correct constructive form of the global claim at finite
  truncation (per `ConstructiveReals/Rationals.lean` module
  docstring §"Boundary" / `notes/sigma-hat-derivation.md` §4).
- A telescoping identity for general Q' sequences.  Q' equality is
  structural (not semantic), so `(a - b) + (b - c) = a - c` does not
  hold by `rfl` and requires either Q'.eqv or `Q'.reduce`.  The
  telescoping step is left to the user / a downstream module that
  needs it; here the framework just composes a user-supplied uniform
  partial-sum bound with the closure condition via transitivity.

# Axiom-gate (see README: axiom policy)

Every load-bearing claim below ends in `Q'.le_trans'` (`[propext]`)
plus basic structural recursion.  No `sorryAx`, no `Classical.*`.
-/

import ConstructiveReals.Rationals

namespace ConstructiveReals.RationalTail

open ConstructiveReals

/-! ## Q'-valued sequences and finite sums -/

/-- A sequence of `Q'` values indexed by `Nat`.

Models the per-step η trajectory (or Δ_∩ trajectory) of the σ̂ budget
closure.  The Python `compute_eta(g_k, g_k_next, t_choice)` returns a
single `Q'` value per `k`; aggregating across `k = 0, 1, …, K` gives
a `QSeq`. -/
def QSeq : Type := Nat → Q'

/-- The finite partial sum `Σ_{k=0}^{N-1} f k`.

Recursively: `finSum f 0 = 0`; `finSum f (N+1) = finSum f N + f N`.
Defined structurally; no axiom dependency. -/
def finSum (f : QSeq) : Nat → Q'
  | 0 => 0
  | n + 1 => finSum f n + f n

@[simp] theorem finSum_zero (f : QSeq) : finSum f 0 = 0 := rfl

@[simp] theorem finSum_succ (f : QSeq) (n : Nat) :
    finSum f (n + 1) = finSum f n + f n := rfl

/-- The constant-zero sequence sums to zero at every length. -/
theorem finSum_zero_seq (n : Nat) : finSum (fun _ => (0 : Q')) n = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show finSum (fun _ => (0 : Q')) k + (0 : Q') = 0
    rw [Q'.add_zero']
    exact ih


/-! ## Stabilization of `finSum` past a zero-tail cut-off

A workhorse lemma: if a `QSeq` is identically zero from index `K` onward, then
its partial sums stabilize at `finSum f K` for every `N ≥ K`.  This lets a
truncated-constant pilot (`η_k = η_max` for `k < K`, then `0`) reduce its
`∀ N` partial-sum bound to a finite case analysis on `N < K` plus the
stabilized tail.

No monotonicity assumption is needed; the proof is structural induction on
the offset `M = N - K` and uses only `Q'.add_zero'` plus the recursive
defining equation `finSum f (K + M + 1) = finSum f (K + M) + f (K + M)`. -/

/-- If `f k = 0` for every `k ≥ K`, then `finSum f (K + M) = finSum f K`
for every offset `M`.

Equivalently: past the cut-off `K`, partial sums of `f` are constant.

Useful for closing the partial-sum bound on a finitely-supported `QSeq` —
all the work happens for `N ≤ K`, and this lemma handles `N > K`. -/
theorem finSum_stabilizes_after_K
    (f : QSeq) (K : Nat) (h : ∀ k, K ≤ k → f k = 0) :
    ∀ M, finSum f (K + M) = finSum f K
  | 0 => rfl
  | M + 1 => by
    -- finSum f (K + (M + 1)) reduces to finSum f (K + M) + f (K + M),
    -- and f (K + M) = 0 by hypothesis, then add_zero' + ih.
    show finSum f (K + M) + f (K + M) = finSum f K
    have hf : f (K + M) = 0 := h (K + M) (Nat.le_add_right K M)
    rw [hf, Q'.add_zero']
    exact finSum_stabilizes_after_K f K h M

/-! ## The budget-closure framework theorem

Bounded partial sums under a budget, at finite truncation. -/


/-- **Global budget closure** (Q' framework form).

Given:
  * `η : QSeq` — a nonnegative per-step cost sequence;
  * `eta_total_bound : Q'` — a uniform upper bound on every partial sum;
  * `sigma_0 : Q'` — the total budget;
  * `h_eta_bound : ∀ N, finSum η N ≤ eta_total_bound` — the partial-sum
    bound (analytic content: this is the telescoping-bounded form, supplied
    by the user / downstream from `K_∩` monotonicity + boundedness);
  * `h_budget : eta_total_bound ≤ sigma_0` — the closure condition,

conclude: `∀ N, finSum η N ≤ sigma_0`.

This is the global ``Σ_k η_k ≤ budget`` claim at finite truncation,
expressed entirely in Q' (no constructive-reals layer).  The proof is
a single transitivity step: each partial sum is bounded by
`eta_total_bound` (by hypothesis), and `eta_total_bound ≤ sigma_0`
(by closure condition), so each partial sum is `≤ sigma_0`. -/
theorem partialSum_budget_closure
    (η : QSeq) (eta_total_bound sigma_0 : Q')
    (h_eta_bound : ∀ N, finSum η N ≤ eta_total_bound)
    (h_budget : eta_total_bound ≤ sigma_0) :
    ∀ N, finSum η N ≤ sigma_0 :=
  fun N => Q'.le_trans' _ _ _ (h_eta_bound N) h_budget

/-! ## Generic K = 3 truncated-constant pilot closure

A reusable closure theorem for any "η is η_max for k ∈ {0, 1, 2}, zero
thereafter" pilot.  Downstream consumers pick `K ≥ 3` as the
target, so the K = 3 case is the canonical pilot shape; both the
canonical (g_0 = 0.30) and Wilson (g_0 = 0.50) SU(2) wire-ins in
downstream consumers instantiate it.

Pulling the structural induction out here means each new pilot variant
needs only the four partial-sum inequalities (each discharged by
`decide` at concrete rationals) plus the closure condition — the
recursive proof is shared. -/

/-- Truncated-constant pilot sequence: `η_max` for `k < 3`, zero thereafter. -/
def truncated_const_3 (η_max : Q') : QSeq
  | 0     => η_max
  | 1     => η_max
  | 2     => η_max
  | _ + 3 => 0

/-- `truncated_const_3 η_max` is zero past index 3. -/
theorem truncated_const_3_zero_of_ge_3 (η_max : Q') :
    ∀ k, 3 ≤ k → truncated_const_3 η_max k = 0
  | 0,     h => absurd h (by decide)
  | 1,     h => absurd h (by decide)
  | 2,     h => absurd h (by decide)
  | _ + 3, _ => rfl

/-- Generic K = 3 truncated-constant partial-sum bound.

Given four partial-sum hypotheses (each typically discharged by `decide`
at concrete rational `η_max`), conclude the bound holds at every `N`.
The proof is structural induction on `N` with stabilization past `K = 3`.

For each Phase-3 pilot wire-in:

  * Choose `η_max ∈ Q'` as a rational upper bound on `max_k η_k` from
    the Python pilot (`computations/q_lift.py`).
  * Choose `σ_0 ∈ Q'` as the initial σ̂.
  * Discharge `h0 : 0 ≤ σ_0` and `h1, h2, h3 : i-fold sum ≤ σ_0` by `decide`.
  * Apply this theorem.

The four inequalities encode "after 0, 1, 2, 3 transitions, the running
total stays under the budget." -/
theorem truncated_const_3_partial_sum_bound
    (η_max σ_0 : Q')
    (h0 : (0 : Q') ≤ σ_0)
    (h1 : (0 : Q') + η_max ≤ σ_0)
    (h2 : ((0 : Q') + η_max) + η_max ≤ σ_0)
    (h3 : (((0 : Q') + η_max) + η_max) + η_max ≤ σ_0) :
    ∀ N, finSum (truncated_const_3 η_max) N ≤ σ_0
  | 0     => h0
  | 1     => h1
  | 2     => h2
  | 3     => h3
  | n + 4 => by
    -- For N ≥ 4 the partial sum stabilizes at finSum (...) 3 via the
    -- zero-tail past index 3.
    show finSum (truncated_const_3 η_max) ((n + 1) + 3) ≤ σ_0
    rw [Nat.add_comm (n + 1) 3,
        finSum_stabilizes_after_K (truncated_const_3 η_max) 3
          (truncated_const_3_zero_of_ge_3 η_max) (n + 1)]
    exact h3

/-! ## Monotonicity of `finSum` for nonneg sequences

The Q' analog of "Σ_{k=0}^{N-1} a_k is monotone-increasing in N if a_k ≥ 0."
Needed by `prefix_plus_tail_closure` below: for N below the cut-off K_0,
monotonicity bounds the partial sum by `finSum η K_0`.

Both lemmas follow from `Q'.add_le_self_of_nonneg` by structural induction. -/

/-- One-step monotonicity: `finSum η n ≤ finSum η (n + 1)` when `0 ≤ η n`. -/
theorem finSum_le_succ_of_nonneg (η : QSeq) (n : Nat) (h : (0 : Q') ≤ η n) :
    finSum η n ≤ finSum η (n + 1) := by
  show finSum η n ≤ finSum η n + η n
  exact Q'.add_le_self_of_nonneg (finSum η n) (η n) h

/-- For nonneg `η`, `finSum η M ≤ finSum η (M + K)` for every `K`.
Proof by induction on `K` using `finSum_le_succ_of_nonneg`. -/
theorem finSum_le_add_of_nonneg
    (η : QSeq) (h_nonneg : ∀ k, (0 : Q') ≤ η k) (M : Nat) :
    ∀ K, finSum η M ≤ finSum η (M + K)
  | 0 => by
    show finSum η M ≤ finSum η (M + 0)
    show finSum η M ≤ finSum η M
    exact Q'.le_refl' _
  | K + 1 => by
    -- finSum η (M + (K + 1)) = finSum η (M + K) + η (M + K)
    -- ≥ finSum η (M + K)        (by finSum_le_succ_of_nonneg)
    -- ≥ finSum η M               (by IH)
    show finSum η M ≤ finSum η (M + K) + η (M + K)
    have h_ih : finSum η M ≤ finSum η (M + K) :=
      finSum_le_add_of_nonneg η h_nonneg M K
    have h_step : finSum η (M + K) ≤ finSum η (M + K) + η (M + K) :=
      Q'.add_le_self_of_nonneg _ _ (h_nonneg _)
    exact Q'.le_trans' _ _ _ h_ih h_step

/-- General monotonicity: `M ≤ N → finSum η M ≤ finSum η N` for nonneg `η`.

Derived from `finSum_le_add_of_nonneg` via `Nat.exists_eq_add_of_le`. -/
theorem finSum_monotone_of_nonneg
    (η : QSeq) (h_nonneg : ∀ k, (0 : Q') ≤ η k)
    (M N : Nat) (h_le : M ≤ N) :
    finSum η M ≤ finSum η N := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le h_le
  -- Goal: finSum η M ≤ finSum η (M + K)
  exact finSum_le_add_of_nonneg η h_nonneg M K

/-! ## Prefix-plus-tail closure for infinite trajectories

Extends `partialSum_budget_closure` to the natural "infinite trajectory"
shape of `notes/sigma-hat-derivation.md` §4.2 option (i): the global
closure ``∀ N, finSum η N ≤ σ_0`` follows from a UNIFORM-PAST-K_0 bound
(a single rational `bound` that bounds `finSum η (K_0 + M)` for every
`M`) plus the budget condition `bound ≤ σ_0`.

For `N ≥ K_0`, the result is the uniform bound transitioned through the
budget condition (the same shape as `partialSum_budget_closure`).

For `N < K_0`, the result uses **monotonicity** of `finSum η` for
nonneg sequences (`finSum_monotone_of_nonneg`): partial sums at smaller
`N` can only be smaller, so they too are bounded by `finSum η K_0 ≤ bound`.

The new infrastructure that makes this work:
  * `Q'.add_le_self_of_nonneg`  (added 2026-05-25 to `Rationals.lean`)
  * `finSum_le_add_of_nonneg`   (above)
  * `finSum_monotone_of_nonneg` (above)

Use case (Phase-4 prep): for the UV-direction SU(2) trajectory where
`g_k → 0` as `k → ∞`, η_k decays geometrically and the tail `Σ_{k ≥ K_0}
η_k ≤ T` is rationally bounded.  Picking `bound := finSum η K_0 + T`
(both rational at finite K_0) and supplying the per-M tail bound gives
the infinite-trajectory closure entirely in Q'. -/

/-- **Prefix-plus-tail closure for infinite trajectories.**

Given:
  * `η : QSeq` with `h_nonneg : ∀ k, 0 ≤ η k`,
  * `K_0 : Nat` (the cut-off scale),
  * `bound : Q'` such that `∀ M, finSum η (K_0 + M) ≤ bound` (the
    uniform-past-K_0 hypothesis — typically derived as
    `finSum η K_0 + (geometric tail bound)`),
  * `h_budget : bound ≤ σ_0` (the closure condition),

conclude: `∀ N, finSum η N ≤ σ_0`.

Differs from `partialSum_budget_closure` in that the user only supplies
the bound past `K_0`; for `N < K_0` we use nonneg-monotonicity of the
partial sums, which is the structural payoff of `add_le_self_of_nonneg`
+ `finSum_monotone_of_nonneg`. -/
theorem prefix_plus_tail_closure
    (η : QSeq) (K_0 : Nat) (bound σ_0 : Q')
    (h_nonneg : ∀ k, (0 : Q') ≤ η k)
    (h_tail_uniform : ∀ M, finSum η (K_0 + M) ≤ bound)
    (h_budget : bound ≤ σ_0) :
    ∀ N, finSum η N ≤ σ_0 := by
  intro N
  -- Case split on whether N ≥ K_0 or N < K_0.
  by_cases h : K_0 ≤ N
  case pos =>
    -- N ≥ K_0: write N = K_0 + M for some M, apply h_tail_uniform.
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h
    exact Q'.le_trans' _ _ _ (h_tail_uniform M) h_budget
  case neg =>
    -- N < K_0: by monotonicity, finSum η N ≤ finSum η K_0 = finSum η (K_0 + 0)
    -- ≤ bound (by h_tail_uniform at M = 0) ≤ σ_0 (by h_budget).
    have h_N_le_K0 : N ≤ K_0 := Nat.le_of_not_le h
    have h_mono : finSum η N ≤ finSum η K_0 :=
      finSum_monotone_of_nonneg η h_nonneg N K_0 h_N_le_K0
    have h_K0_bound : finSum η K_0 ≤ bound := by
      have h_zero := h_tail_uniform 0
      -- h_zero : finSum η (K_0 + 0) ≤ bound
      -- Need: finSum η K_0 ≤ bound.  K_0 + 0 = K_0 by Nat.add_zero.
      show finSum η K_0 ≤ bound
      have h_eq : K_0 + 0 = K_0 := Nat.add_zero K_0
      rw [h_eq] at h_zero
      exact h_zero
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h_mono h_K0_bound) h_budget

/-! ## Smoke-test instance: zero-η trajectory

The trivially-closed pilot: an η sequence that is identically zero
(no σ̂ degradation per step) closes against any positive σ̂_0. -/

/-- For the zero-η sequence, every partial sum is `≤ 0` (in fact equals 0). -/
theorem zero_eta_bound (N : Nat) :
    finSum (fun _ => (0 : Q')) N ≤ (0 : Q') := by
  rw [finSum_zero_seq]
  exact Q'.le_refl' _

/-- **Smoke-test closure**: the zero-η sequence closes the budget against
σ̂_0 = 1.  Demonstrates that `partialSum_budget_closure` is callable with
real Q' values and discharges constructively. -/
theorem smoke_test_zero_eta_closes :
    ∀ N, finSum (fun _ => (0 : Q')) N ≤ (1 : Q') := by
  apply partialSum_budget_closure
  · -- eta partial sums all bounded by 0
    exact zero_eta_bound
  · -- 0 ≤ 1 in Q'
    show (0 : Int) * (1 : Int) ≤ (1 : Int) * (1 : Int)
    decide

/-! ## Pilot instance: constant-η trajectory

A more substantive instance.  For a constant η sequence `η k = η_0`
(every step contributes the same η_0), the partial sum after N steps
is `N · η_0`.  The closure requires `N · η_0 ≤ σ̂_0` uniformly — which
fails for any positive η_0 as N → ∞.  This honestly surfaces the
"need-for-telescoping-or-decay" boundary: a *constant* η sequence
does NOT admit a finite uniform bound, so the closure framework's
`eta_total_bound` hypothesis cannot be satisfied with a fixed Q' rational.

The substantive pilot (telescoping-bounded η from the SU(2) trajectory)
satisfies `eta_total_bound = c_η · K_max` with `K_max` finite, hence
admits closure — but only via the per-step bound supplied externally
(e.g. from a future `K_∩`-trajectory analysis module).

This instance below documents the inverse: a smoke test showing the
framework correctly handles a *bounded-trajectory* case via direct
witness, leaving the SU(2)-pilot integration as future work. -/

/-- A single-step η that bounds at η_0: the trivial bounded trajectory.

`finSum (single_step_eta η_0) N = if N = 0 then 0 else η_0`. -/
def single_step_eta (η_0 : Q') : QSeq := fun k => if k = 0 then η_0 else 0

/-- The single-step η has partial sum bounded by `η_0` from step 1 onward
(and 0 at step 0).  At every N, partial sum ≤ η_0 ∨ partial sum = 0. -/
theorem single_step_eta_partial_sum_bound
    (η_0 : Q') (h_η_nonneg : (0 : Q') ≤ η_0) (N : Nat) :
    finSum (single_step_eta η_0) N ≤ η_0 := by
  match N with
  | 0 =>
    -- finSum _ 0 = 0 ≤ η_0 (by hypothesis)
    show (0 : Q') ≤ η_0
    exact h_η_nonneg
  | n + 1 =>
    -- finSum f (n+1) = finSum f n + f n.  We'll show this equals η_0 when
    -- n = 0, and equals (prev sum) when n > 0; in either case ≤ η_0.
    -- For the smoke test we proceed by induction on the structure.
    show finSum (single_step_eta η_0) n + single_step_eta η_0 n ≤ η_0
    -- Use a separate inductive lemma that handles the structure cleanly.
    -- Below: a direct argument splitting on n.
    match n with
    | 0 =>
      -- finSum (...) 0 + (single_step η_0) 0 = 0 + η_0 = η_0.
      show (0 : Q') + (single_step_eta η_0) 0 ≤ η_0
      have h_step_zero : single_step_eta η_0 0 = η_0 := by
        show (if (0 : Nat) = 0 then η_0 else 0) = η_0
        simp
      rw [h_step_zero, Q'.zero_add']
      exact Q'.le_refl' _
    | k + 1 =>
      -- single_step_eta η_0 (k+1) = 0 since k+1 ≠ 0.
      -- finSum at (k+1) = (finSum at k) + 0 = (finSum at k) ≤ η_0 (by ind hyp).
      show finSum (single_step_eta η_0) (k + 1) + single_step_eta η_0 (k + 1) ≤ η_0
      have h_zero : single_step_eta η_0 (k + 1) = 0 := by
        show (if (k + 1 : Nat) = 0 then η_0 else 0) = 0
        simp
      rw [h_zero, Q'.add_zero']
      exact single_step_eta_partial_sum_bound η_0 h_η_nonneg (k + 1)

/-- **Pilot closure**: for a single-step η at value `η_0 ≥ 0`, the budget
closes against any `σ̂_0 ≥ η_0`. -/
theorem single_step_eta_closes
    (η_0 sigma_0 : Q')
    (h_η_nonneg : (0 : Q') ≤ η_0)
    (h_budget : η_0 ≤ sigma_0) :
    ∀ N, finSum (single_step_eta η_0) N ≤ sigma_0 :=
  partialSum_budget_closure (single_step_eta η_0) η_0 sigma_0
    (single_step_eta_partial_sum_bound η_0 h_η_nonneg)
    h_budget

end ConstructiveReals.RationalTail

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.RationalTail.finSum
#print axioms ConstructiveReals.RationalTail.finSum_zero
#print axioms ConstructiveReals.RationalTail.finSum_succ
#print axioms ConstructiveReals.RationalTail.finSum_zero_seq
#print axioms ConstructiveReals.RationalTail.finSum_stabilizes_after_K
#print axioms ConstructiveReals.RationalTail.finSum_le_succ_of_nonneg
#print axioms ConstructiveReals.RationalTail.finSum_le_add_of_nonneg
#print axioms ConstructiveReals.RationalTail.finSum_monotone_of_nonneg
#print axioms ConstructiveReals.RationalTail.truncated_const_3
#print axioms ConstructiveReals.RationalTail.truncated_const_3_zero_of_ge_3
#print axioms ConstructiveReals.RationalTail.truncated_const_3_partial_sum_bound
#print axioms ConstructiveReals.RationalTail.partialSum_budget_closure
#print axioms ConstructiveReals.RationalTail.prefix_plus_tail_closure
#print axioms ConstructiveReals.RationalTail.zero_eta_bound
#print axioms ConstructiveReals.RationalTail.smoke_test_zero_eta_closes
#print axioms ConstructiveReals.RationalTail.single_step_eta
#print axioms ConstructiveReals.RationalTail.single_step_eta_partial_sum_bound
#print axioms ConstructiveReals.RationalTail.single_step_eta_closes
