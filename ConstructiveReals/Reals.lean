/-
Constructive reals — Bishop-style regular Cauchy sequences in `Q'`.

# Why this module exists

This is the base layer of the constructive-reals development: a
Bishop-style constructive real over the from-scratch rationals `Q'`.
It provides:

  * `CReal` — a regular Cauchy sequence in `Q'` with explicit
    Cauchy modulus (the ε-N form, two-sided to avoid an
    absolute-value construction on `Q'`).
  * `CReal.ofQ'` — the canonical embedding `Q' ↪ CReal`.
  * `CReal.le` — a one-slack Bishop-style order:
    `x ≤ y` iff `∀ n, x.approx n ≤ y.approx n + 1/(n+1)`.
  * `CReal.IsPositive` — strictly-positive-with-Q'-rational-witness.
  * `CReal.ofQ'_le_of_approx_ge` — the load-bearing bridge: if every
    `Q'` approximation of `x` is ≥ ε, then `ofQ' ε ≤ x` at the
    CReal level.

# Scope and what this module deliberately does not include

  * **Transitivity of `≤`.**  Bishop's one-slack `≤` is not
    structurally transitive (the slack accumulates).  Transitivity
    via an ε-splitting argument needs a larger `Q'` algebra build-out
    than this base module carries; `RegularCReal.lean` builds the
    canonical-modulus real whose order IS transitive, and downstream
    modules develop the ε-splitting machinery.
  * **Arithmetic** (`add`, `neg`, `sub`, `mul`) lives in
    `CRealAdd.lean` / `CRealMul.lean` and their successors.
  * **Square root** (`CReal.sqrt`) lives in `Sqrt.lean`.

# Constructive content and axiom gate

  * **Modulus caveat (see README: moduli-as-data policy).**  The `cauchy` field is a
    `Prop`-level `∃ N`.  No `Classical.choice` is used (a proof of it
    BHK-constructs a specific `N`), but the earlier claim that the
    witness is "extractable via structural recursion on `Nat`" was
    over-stated: the body is a `∀ m n ≥ N` (not decidable), so `Nat.find`
    does not apply and Lean's proof-irrelevant `Prop` blocks recovering
    `N` as data.  In MLTT the same datum written with `Σ` keeps the
    modulus as a function with a working projection; that is the
    Rule-8.3-mandated direction.  New modulus work (see
    `Constructive/ExpNeg.lean`) therefore builds the modulus as a
    `Type`-level function and applies it to fill this legacy field; a
    `Type`-level-modulus refactor of `CReal` is the standing follow-on.
  * Equality on `CReal` is *not* decidable (this is genuine and
    reflects the constructive nature of reals); the module does
    NOT pretend otherwise.  We expose only `≤`, not `=`.
  * All load-bearing theorems pass `#print axioms` with `[propext]`
    only.  No `Classical.choice`, no `Classical.em`, no `Quot.sound`,
    and no `sorryAx` in any theorem listed in the audit at the
    bottom of this file.

-/

import ConstructiveReals.Rationals

namespace ConstructiveReals

/-! ## Q' helpers for the constructive-reals layer

Two small extensions to the `Q'` API.  Each is provable from the
lemmas already in `Rationals.lean` and pulls in no new axioms beyond
`[propext]`. -/

namespace Q'

/-! ### `Q'.invSucc n = 1/(n+1)`

The canonical "n-th tolerance" rational, used as the slack term in
the one-slack Bishop order below.  Defined positive by structure
since `n+1 ≥ 1` for every `n : Nat`. -/

/-- `1/(n+1)` as a `Q'`.  Always positive. -/
@[inline] def invSucc (n : Nat) : Q' := mkPos 1 (n+1) (Nat.succ_pos _)

theorem invSucc_num (n : Nat) : (invSucc n).num = 1 := rfl

theorem invSucc_den (n : Nat) : (invSucc n).den = n + 1 := by
  unfold invSucc
  exact mkPos_den 1 (n+1) (Nat.succ_pos _)

theorem invSucc_pos (n : Nat) : (0 : Q') < invSucc n := by
  show (0 : Int) * ((invSucc n).den : Int) < (invSucc n).num * ((0 : Q').den : Int)
  rw [invSucc_num, invSucc_den]
  show (0 : Int) * (((n+1) : Nat) : Int) < (1 : Int) * (1 : Int)
  simp

/-! ### `Q'.le_of_lt`

The standard ≤-from-<.  Lean core's `Int.le_of_lt` discharges this
on the cross-product representation. -/

/-- If `a < b` then `a ≤ b`. -/
theorem le_of_lt {a b : Q'} (h : a < b) : a ≤ b := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  exact Int.le_of_lt h

/-- `0 ≤ invSucc n`.  Corollary of `le_of_lt` and `invSucc_pos`. -/
theorem invSucc_nonneg (n : Nat) : (0 : Q') ≤ invSucc n :=
  le_of_lt (invSucc_pos n)

end Q'

/-! ## The `CReal` structure

A constructive real is a sequence `approx : Nat → Q'` together with
an explicit modulus of convergence: for every rational tolerance
`ε > 0`, we can supply a stage `N` past which all pairs of
approximations agree to within `ε` (two-sided, to avoid
absolute-value construction). -/

/-- A constructive real number: a regular Cauchy sequence in `Q'`. -/
structure CReal where
  /-- The `n`-th rational approximation. -/
  approx : Nat → Q'
  /-- The Cauchy modulus: for every tolerance `ε > 0` there is a
  stage `N` past which all approximations are within `ε` of each
  other (two-sided). -/
  cauchy : ∀ ε : Q', (0 : Q') < ε →
    ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
      approx m ≤ approx n + ε ∧ approx n ≤ approx m + ε

namespace CReal

/-! ### The embedding `Q' ↪ CReal` -/

/-- The constant CReal `q : Q'` viewed as a regular sequence. -/
def ofQ' (q : Q') : CReal where
  approx _ := q
  cauchy := by
    intro ε hε
    have h_ε_nn : (0 : Q') ≤ ε := Q'.le_of_lt hε
    refine ⟨0, fun _ _ _ _ => ⟨?_, ?_⟩⟩
    · exact Q'.add_le_self_of_nonneg q ε h_ε_nn
    · exact Q'.add_le_self_of_nonneg q ε h_ε_nn

@[simp] theorem ofQ'_approx (q : Q') (n : Nat) : (ofQ' q).approx n = q := rfl

/-- Zero in CReal: the embedding of `0 : Q'`. -/
def czero : CReal := ofQ' 0
/-- One in CReal: the embedding of `1 : Q'`. -/
def cone : CReal := ofQ' 1

instance : Zero CReal := ⟨czero⟩
instance : One CReal := ⟨cone⟩

/-! ### Order: Bishop's one-slack form

We use the one-slack Bishop order:
  `x ≤ y` iff `∀ n, x.approx n ≤ y.approx n + 1/(n+1)`.

This is **not** transitive in general (the slack accumulates), but
it has the structural properties positivity arguments need:

  * Reflexivity: `x ≤ x` (the slack is nonneg).
  * Q' lift: `q ≤ q'` at `Q'` implies `ofQ' q ≤ ofQ' q'`.
  * Approximation lift: `∀ n, lb ≤ x.approx n` implies `ofQ' lb ≤ x`.

The accumulating-slack defect of transitivity is repaired by the
canonical-modulus real `RegularCReal.lean`, whose order IS
transitive, and by the ε-splitting machinery of later modules.

We avoid the name `LE` for our binary relation because it collides
with Lean's built-in `LE` typeclass; we use `CReal.le` and expose
the `≤` notation via `instance : LE CReal`. -/

/-- Bishop's one-slack "≤" on CReals. -/
def le (x y : CReal) : Prop :=
  ∀ n : Nat, x.approx n ≤ y.approx n + Q'.invSucc n

instance : LE CReal := ⟨CReal.le⟩

/-! #### Reflexivity -/

theorem le_refl (x : CReal) : x ≤ x := by
  intro n
  show x.approx n ≤ x.approx n + Q'.invSucc n
  exact Q'.add_le_self_of_nonneg (x.approx n) (Q'.invSucc n) (Q'.invSucc_nonneg n)

/-! #### Q' → CReal monotonicity bridge -/

/-- The lift `Q' ≤ ⟶ CReal ≤` (backward direction): `q ≤ q'` at `Q'`
implies `ofQ' q ≤ ofQ' q'` at CReal.

This is the direction we actually need (lifting Q'-rational
inequalities to CReal-rational inequalities of constant CReals).
The forward direction fails for the one-slack order (the n=0 slack
is `invSucc 0 = 1`, which is larger than typical Q' inequalities). -/
theorem ofQ'_le_ofQ' {q q' : Q'} (h : q ≤ q') : ofQ' q ≤ ofQ' q' := by
  intro n
  show q ≤ q' + Q'.invSucc n
  have h_step : q' ≤ q' + Q'.invSucc n :=
    Q'.add_le_self_of_nonneg q' (Q'.invSucc n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' q q' (q' + Q'.invSucc n) h h_step

/-! #### The load-bearing lift: approximation lower bound ⟹ CReal lower bound -/

/-- **The headline framework theorem of this module.**

If every approximation `x.approx n` is ≥ some `Q'`-rational `lb`,
then `ofQ' lb ≤ x` at the CReal level.  This is the constructive
analog of "if a sequence is bounded below by a constant, its limit
is too." -/
theorem ofQ'_le_of_approx_ge
    {x : CReal} {lb : Q'}
    (h : ∀ n : Nat, lb ≤ x.approx n) :
    ofQ' lb ≤ x := by
  intro n
  show lb ≤ x.approx n + Q'.invSucc n
  have h_step : x.approx n ≤ x.approx n + Q'.invSucc n :=
    Q'.add_le_self_of_nonneg (x.approx n) (Q'.invSucc n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' lb (x.approx n) (x.approx n + Q'.invSucc n) (h n) h_step

/-- **Dual of `ofQ'_le_of_approx_ge`.**

If every approximation `x.approx n` is ≤ some `Q'`-rational `ub`, then
`x ≤ ofQ' ub` at the CReal level.  The constructive analog of "if a
sequence is bounded above by a constant, its limit is too" — the lift
needed to state a CReal-level *upper* bound (e.g. `expNeg x ≤ ofQ' (E x)`
for a rational exponential bound `E`). -/
theorem le_ofQ'_of_approx_le
    {x : CReal} {ub : Q'}
    (h : ∀ n : Nat, x.approx n ≤ ub) :
    x ≤ ofQ' ub := by
  intro n
  show x.approx n ≤ ub + Q'.invSucc n
  exact Q'.le_trans' (x.approx n) ub (ub + Q'.invSucc n)
    (h n) (Q'.add_le_self_of_nonneg ub (Q'.invSucc n) (Q'.invSucc_nonneg n))

/-! ### Strict positivity at the CReal level -/

/-- A CReal-level "strictly positive": there is a positive `Q'`
witness `ε` with `ofQ' ε ≤ x`.  This is the constructive analog of
`x > 0`: equality to zero is undecidable, but
bounded-below-by-a-positive-Q'-rational is the right witness. -/
def IsPositive (x : CReal) : Prop :=
  ∃ ε : Q', (0 : Q') < ε ∧ ofQ' ε ≤ x

/-- A CReal is positive whenever every approximation is ≥ some
positive `Q'`-rational `ε`. -/
theorem isPositive_of_approx_ge
    {x : CReal} {ε : Q'} (hε : (0 : Q') < ε)
    (h : ∀ n : Nat, ε ≤ x.approx n) :
    IsPositive x :=
  ⟨ε, hε, ofQ'_le_of_approx_ge h⟩

/-! ### A convenience constructor for the trivial-case limit

For a constant `Q'` sequence the CReal is just `ofQ' q`; this
re-exposes that under the limit-constructor name so that
constant-limit applications read cleanly. -/

/-- A constant `Q'`-sequence's limit is the embedded `ofQ' q`. -/
def limit_of_constant (q : Q') : CReal := ofQ' q

@[simp] theorem limit_of_constant_eq (q : Q') :
    limit_of_constant q = ofQ' q := rfl

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every theorem below must report `propext` or empty.  No
`Classical.*`, no `Quot.sound`, no `sorryAx`. -/

#print axioms ConstructiveReals.Q'.invSucc_num
#print axioms ConstructiveReals.Q'.invSucc_den
#print axioms ConstructiveReals.Q'.invSucc_pos
#print axioms ConstructiveReals.Q'.invSucc_nonneg
#print axioms ConstructiveReals.Q'.le_of_lt
#print axioms ConstructiveReals.CReal.ofQ'_approx
#print axioms ConstructiveReals.CReal.le_refl
#print axioms ConstructiveReals.CReal.ofQ'_le_ofQ'
#print axioms ConstructiveReals.CReal.ofQ'_le_of_approx_ge
#print axioms ConstructiveReals.CReal.le_ofQ'_of_approx_le
#print axioms ConstructiveReals.CReal.isPositive_of_approx_ge
#print axioms ConstructiveReals.CReal.limit_of_constant_eq
