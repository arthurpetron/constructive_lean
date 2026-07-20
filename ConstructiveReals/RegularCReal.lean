/-
Regular constructive reals — a CANONICAL-modulus Bishop real in `Q'`.

# Why this module exists

The existing constructive real (`Constructive/Reals.lean`) carries its
Cauchy modulus as a `Prop`-level `∃ N` field (`cauchy`).  Two consequences
follow.  First, the modulus is not recoverable as data (Lean's
proof-irrelevant `Prop` blocks large elimination), which is the standing
Rule-8.3 caveat already flagged in that module's docstring.  Second — and
this is the load-bearing defect — its one-slack order
`x ≤ y := ∀ n, x.approx n ≤ y.approx n + 1/(n+1)` is genuinely
NON-transitive: the slack `1/(n+1)` does not shrink under chaining, so
`x ≤ y` and `y ≤ z` only give `x.approx n ≤ z.approx n + 2/(n+1)`, which
is a strictly weaker statement.

This module builds, ALONGSIDE the existing `CReal` (which is left
untouched), a fresh `RegularCReal` whose regularity modulus is CANONICAL
and carried as STRUCTURE DATA: a `∀ m n` bound

  `|x.approx m − x.approx n| ≤ 1/(m+1) + 1/(n+1)`

written two-sided to avoid an absolute value.  Because the modulus is
fixed (the canonical `1/(k+1)`), it is never extracted from an
existential ⇒ the whole development is choice-free, and — the headline —
the Bishop order

  `x ≤ y := ∀ n, x.approx n ≤ y.approx n + 2/(n+1)`

is now TRANSITIVE.  The proof is the standard regular-real argument:
evaluate at a large auxiliary index `K`, pull the two endpoints back to
index `n` via regularity, chain the two hypotheses at `K`, and absorb the
residual `K`-slack by the Archimedean principle on `Q'`.

There is deliberately NO `CReal → RegularCReal` conversion: that
direction would have to extract a modulus from the `Prop`-`∃` `cauchy`
field, which needs countable choice.  `RegularCReal` is defined fresh,
with the modulus as data, so the choice-free property is preserved.

# Constructive content and axiom gate (see README: axiom policy)

The regularity field is a `∀`-statement (the canonical modulus), not a
`Prop`-`∃`, so no witness is ever discarded (Rule 8.3).  Every
declaration is gated with `#print axioms` at the bottom; the permitted
output is `propext` / `Quot.sound` only (the latter only via reused
`Nat`/`Int` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.Rationals
import ConstructiveReals.RationalsMul
import ConstructiveReals.AbsQ
import ConstructiveReals.Reals

namespace ConstructiveReals

/-! ## Q' helpers: the Archimedean principle in `1/(N+1)` form

The single new `Q'` fact this module needs beyond `Reals.lean`: if a
rational `a` is below `b` plus an arbitrarily small `c·(1/(N+1))`, then
`a ≤ b`.  This is the constructive Archimedean cancellation that lets the
auxiliary-index slack in the transitivity proof be driven to zero. -/

namespace Q'

/-! ### Small `Int` arithmetic helpers (linear, discharged by `omega`) -/

/-- `u ≤ v → u − v ≤ 0` on `Int`. -/
theorem sub_nonpos_of_le (u v : Int) (h : u ≤ v) : u - v ≤ 0 := by omega
/-- `u − v ≤ 0 → u ≤ v` on `Int`. -/
theorem le_of_sub_nonpos (u v : Int) (h : u - v ≤ 0) : u ≤ v := by omega
/-- `a ≤ b + c → a − b ≤ c` on `Int`. -/
theorem sub_le_of_le_add' (a b c : Int) (h : a ≤ b + c) : a - b ≤ c := by omega

/-- The `add` numerator in its definitional cross form. -/
theorem add_num_cast (a b : Q') :
    (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl

/-- `(ofNat n).num = n`. -/
theorem ofNat_num_cast (n : Nat) : (Q'.ofNat n).num = (n : Int) := rfl

/-- `((ofNat n).den : Int) = 1`. -/
theorem ofNat_den_cast (n : Nat) : ((Q'.ofNat n).den : Int) = (1 : Int) := by
  show (((0 : Nat) + 1 : Nat) : Int) = (1 : Int); decide

/-- `(a * b).num = a.num * b.num`. -/
theorem mul_num_cast (a b : Q') : (a * b).num = a.num * b.num := rfl

/-- `(ofNat c * invSucc N).num = c`.  The numerator of `c·(1/(N+1))`. -/
theorem ofNat_mul_invSucc_num (c N : Nat) :
    (Q'.ofNat c * Q'.invSucc N).num = (c : Int) := by
  show (Q'.ofNat c).num * (Q'.invSucc N).num = (c : Int)
  rw [Q'.invSucc_num]
  show (Int.ofNat c) * (1 : Int) = (c : Int)
  rw [Int.mul_one]; rfl

/-- `((ofNat c * invSucc N).den : Int) = N + 1`.  The denominator of
`c·(1/(N+1))`. -/
theorem ofNat_mul_invSucc_den (c N : Nat) :
    ((Q'.ofNat c * Q'.invSucc N).den : Int) = ((N : Int) + 1) := by
  rw [Q'.mul_den_cast]
  show ((Q'.ofNat c).den : Int) * ((Q'.invSucc N).den : Int) = (N : Int) + 1
  have hden1 : ((Q'.ofNat c).den : Int) = (1 : Int) := by
    show (((0 : Nat) + 1 : Nat) : Int) = (1 : Int); decide
  rw [hden1, Int.one_mul, Q'.invSucc_den]
  omega

/-- The cross-product rearrangement used at each `N`:
`Da·(db·N₁) ≤ (Db·N₁ + c·db)·da  ⟹  (Da·db − Db·da)·N₁ ≤ c·db·da`. -/
theorem archimedean_cross_int (Da db Db da c N1 : Int)
    (h : Da * (db * N1) ≤ (Db * N1 + c * db) * da) :
    (Da * db - Db * da) * N1 ≤ c * db * da := by
  have key : (Da * db - Db * da) * N1
      = Da * (db * N1) - (Db * N1) * da := by
    rw [Int.sub_mul, Int.mul_assoc, Int.mul_comm db N1,
        show Db * da * N1 = (Db * N1) * da by
          rw [Int.mul_assoc, Int.mul_comm da N1, ← Int.mul_assoc]]
  have rhs : (Db * N1 + c * db) * da = (Db * N1) * da + c * db * da := by
    rw [Int.add_mul, Int.mul_assoc]
  rw [key]
  have h2 : Da * (db * N1) ≤ (Db * N1) * da + c * db * da := by rw [← rhs]; exact h
  exact Q'.sub_le_of_le_add' _ _ _ h2

/-- The integer Archimedean core: if `D·(N+1) ≤ M` for every `N : Nat` and
`0 ≤ M`, then `D ≤ 0`.  Instantiate at `N = M.toNat`; if `0 < D` (so
`1 ≤ D`) then `M+1 ≤ D·(M+1) ≤ M`, impossible. -/
theorem archimedean_int (D M : Int)
    (hcross : ∀ N : Nat, D * ((N : Int) + 1) ≤ M) (hM_nn : (0 : Int) ≤ M) :
    D ≤ 0 := by
  rcases Int.lt_or_le 0 D with hpos | hle
  · exfalso
    have hone_le : (1 : Int) ≤ D := hpos
    have hMtoNat : ((M.toNat : Int)) = M := Int.toNat_of_nonneg hM_nn
    have hinst : D * (((M.toNat : Nat) : Int) + 1) ≤ M := hcross M.toNat
    have hcast : (((M.toNat : Nat) : Int) + 1) = M + 1 := by rw [hMtoNat]
    rw [hcast] at hinst
    have hMp1_nn : (0 : Int) ≤ M + 1 := by omega
    have hge : (M + 1) ≤ D * (M + 1) := by
      have := Int.mul_le_mul_of_nonneg_right hone_le hMp1_nn
      rw [Int.one_mul] at this
      exact this
    omega
  · exact hle

/-- **The Archimedean principle (the only new `Q'` lemma here).**

If `a ≤ b + c·(1/(N+1))` for EVERY `N : Nat`, then `a ≤ b`.

Constructive proof: the cross-product of the hypothesis at `N` reads
`D·(N+1) ≤ c·b.den·a.den`, where `D := a.num·b.den − b.num·a.den` is the
integer whose sign decides `a ≤ b` (`D ≤ 0`).  `archimedean_int`
instantiates at `N = M.toNat` and splits on the decidable `Int` order to
force `D ≤ 0`. -/
theorem le_of_le_add_mul_invSucc (a b : Q') (c : Nat)
    (h : ∀ N : Nat, a ≤ b + Q'.ofNat c * Q'.invSucc N) : a ≤ b := by
  have hda_nn : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  have hdb_nn : (0 : Int) ≤ (b.den : Int) := Int.natCast_nonneg _
  -- The cross-product of the hypothesis, in the `D·(N+1) ≤ M` form, where
  -- D = a.num·b.den − b.num·a.den and M = c·b.den·a.den.
  have hcross : ∀ N : Nat,
      (a.num * (b.den : Int) - b.num * (a.den : Int)) * ((N : Int) + 1)
        ≤ (c : Int) * (b.den : Int) * (a.den : Int) := by
    intro N
    have hN' : a.num * ((b + Q'.ofNat c * Q'.invSucc N).den : Int)
        ≤ (b + Q'.ofNat c * Q'.invSucc N).num * (a.den : Int) := h N
    have hden : ((b + Q'.ofNat c * Q'.invSucc N).den : Int)
        = (b.den : Int) * ((N : Int) + 1) := by
      rw [Q'.add_den_cast, ofNat_mul_invSucc_den c N]
    have hnum : (b + Q'.ofNat c * Q'.invSucc N).num
        = b.num * ((N : Int) + 1) + (c : Int) * (b.den : Int) := by
      show b.num * ((Q'.ofNat c * Q'.invSucc N).den : Int)
          + (Q'.ofNat c * Q'.invSucc N).num * (b.den : Int)
        = b.num * ((N : Int) + 1) + (c : Int) * (b.den : Int)
      rw [ofNat_mul_invSucc_den c N, ofNat_mul_invSucc_num c N]
    rw [hden, hnum] at hN'
    exact archimedean_cross_int a.num (b.den : Int) b.num (a.den : Int)
      (c : Int) ((N : Int) + 1) hN'
  -- The goal `a ≤ b` is `a.num·b.den ≤ b.num·a.den`, i.e. `D ≤ 0`.
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  refine Q'.le_of_sub_nonpos (a.num * (b.den : Int)) (b.num * (a.den : Int)) ?_
  exact archimedean_int _ _ hcross
    (Int.mul_nonneg (Int.mul_nonneg (Int.natCast_nonneg c) hdb_nn) hda_nn)

set_option maxHeartbeats 4000000 in
/-- The abstract `Int` polynomial identity underlying `slack6_eqv`, in the
exact monomial shape produced by expanding the cross-product with the
`*_cast` lemmas.  Proved by distributing (`6 = 1+1+1+1+1+1` so the literal
coefficient splits into the six matching monomials) then `ac_rfl`. -/
theorem slack6_int (wn wd pn pd qn qd : Int) :
    ((((wn * (pd * qd) + (pn * qd + qn * pd) * wd) * (qd * qd) +
                (qn * qd + qn * qd) * (wd * (pd * qd))) *
              (qd * qd) +
            (qn * qd + qn * qd) * (wd * (pd * qd) * (qd * qd))) *
          (pd * qd) +
        (pn * qd + qn * pd) * (wd * (pd * qd) * (qd * qd) * (qd * qd))) *
      (wd * (pd * pd) * qd) =
    ((wn * (pd * pd) + (pn * pd + pn * pd) * wd) * qd +
        6 * qn * (wd * (pd * pd))) *
      (wd * (pd * qd) * (qd * qd) * (qd * qd) * (pd * qd)) := by
  have h6 : (6 : Int) = 1 + 1 + 1 + 1 + 1 + 1 := by decide
  rw [h6]
  simp only [Int.add_mul, Int.one_mul]
  ac_rfl

/-- The pure-`Q'` slack-collection identity used by transitivity.
Both sides equal `w + 2p + 6q` as exact rationals; this `eqv` is the
rearrangement of the four chained slack blocks into `2p + 6q`.  It is
proved by reducing the `eqv` cross-product to `slack6_int`. -/
theorem slack6_eqv (w p q : Q') :
    ((((w + (p + q)) + (q + q)) + (q + q)) + (p + q)).eqv
      (w + (p + p) + Q'.ofNat 6 * q) := by
  -- Reduce to the Int cross-product identity.
  show (((((w + (p + q)) + (q + q)) + (q + q)) + (p + q)).num)
        * ((w + (p + p) + Q'.ofNat 6 * q).den : Int)
      = ((w + (p + p) + Q'.ofNat 6 * q).num)
        * (((((w + (p + q)) + (q + q)) + (q + q)) + (p + q)).den : Int)
  -- Expand every `add` / `mul` numerator and denominator via the canonical
  -- cast formulas, reducing to the polynomial identity `slack6_int`.
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
             Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.one_mul]
  exact slack6_int w.num (w.den : Int) p.num (p.den : Int) q.num (q.den : Int)

/-- **Generalized Archimedean principle.**  If `a ≤ b + r N` for every `N`,
where each residual `r N` is itself bounded by `c·(1/(N+1))`, then `a ≤ b`.
This is the form the transitivity proof consumes: the auxiliary-index
slack `r N` is a sum of unit fractions, which is `≤ 6·(1/(N+1))` by a
termwise `≤` (no exact `eqv` identity on the messy sum is needed). -/
theorem le_of_le_add_residual (a b : Q') (c : Nat) (r : Nat → Q')
    (hr : ∀ N : Nat, r N ≤ Q'.ofNat c * Q'.invSucc N)
    (h : ∀ N : Nat, a ≤ b + r N) : a ≤ b := by
  refine le_of_le_add_mul_invSucc a b c ?_
  intro N
  exact Q'.le_trans' _ _ _ (h N) (Q'.add_le_add_left b _ _ (hr N))

end Q'

/-! ## The `RegularCReal` structure

A regular constructive real is a sequence `approx : Nat → Q'` together
with a CANONICAL regularity bound: every pair of approximations agrees to
within `1/(m+1) + 1/(n+1)`, stated two-sided to avoid an absolute value
on `Q'`.  The modulus is fixed (not existentially quantified), so it is
never extracted and the development stays choice-free. -/

/-- A **regular constructive real**: a sequence in `Q'` with the canonical
two-sided regularity modulus `|approx m − approx n| ≤ 1/(m+1) + 1/(n+1)`,
carried as `∀`-data rather than a `Prop`-`∃`. -/
structure RegularCReal where
  /-- The `n`-th rational approximation. -/
  approx : Nat → Q'
  /-- Canonical regularity: any two approximations are within
  `1/(m+1) + 1/(n+1)` of each other, two-sided. -/
  regular : ∀ m n : Nat,
    approx m ≤ approx n + (Q'.invSucc m + Q'.invSucc n) ∧
    approx n ≤ approx m + (Q'.invSucc m + Q'.invSucc n)

namespace RegularCReal

/-! ### The embedding `Q' ↪ RegularCReal` -/

/-- The constant `RegularCReal` at `q : Q'`.  Regular because every two
approximations are equal, so their gap `0` is below any nonneg slack. -/
def ofQ' (q : Q') : RegularCReal where
  approx _ := q
  regular := by
    intro m n
    have hslack : (0 : Q') ≤ Q'.invSucc m + Q'.invSucc n :=
      Q'.zero_le_add _ _ (Q'.invSucc_nonneg m) (Q'.invSucc_nonneg n)
    exact ⟨Q'.add_le_self_of_nonneg q _ hslack, Q'.add_le_self_of_nonneg q _ hslack⟩

@[simp] theorem ofQ'_approx (q : Q') (n : Nat) : (ofQ' q).approx n = q := rfl

/-- Zero in `RegularCReal`: the embedding of `0 : Q'`. -/
def czero : RegularCReal := ofQ' 0
/-- One in `RegularCReal`: the embedding of `1 : Q'`. -/
def cone : RegularCReal := ofQ' 1

instance : Zero RegularCReal := ⟨czero⟩
instance : One RegularCReal := ⟨cone⟩

/-! ### Equality of regular reals

The standard Bishop equality: `x ≈ y` iff `|x_n − y_n| ≤ 2/(n+1)` for
every `n`, two-sided.  Unlike the existing `CReal`, this is provably an
EQUIVALENCE RELATION — transitivity holds because regularity lets the
auxiliary-index slack be driven to zero by the Archimedean principle. -/

/-- Bishop equality on regular reals: `x ≈ y` iff every pair of
approximations is within `2/(n+1)`, two-sided. -/
def Equiv (x y : RegularCReal) : Prop :=
  ∀ n : Nat,
    x.approx n ≤ y.approx n + (Q'.invSucc n + Q'.invSucc n) ∧
    y.approx n ≤ x.approx n + (Q'.invSucc n + Q'.invSucc n)

/-- `Equiv` is reflexive. -/
theorem Equiv.refl (x : RegularCReal) : Equiv x x := by
  intro n
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  exact ⟨Q'.add_le_self_of_nonneg _ _ hslack, Q'.add_le_self_of_nonneg _ _ hslack⟩

/-- `Equiv` is symmetric. -/
theorem Equiv.symm {x y : RegularCReal} (h : Equiv x y) : Equiv y x := by
  intro n
  exact ⟨(h n).2, (h n).1⟩

/-! ### Order: Bishop's regular-real order

`x ≤ y` iff `x_n ≤ y_n + 2/(n+1)` for every `n`.  For regular reals this
is TRANSITIVE — the headline deliverable of this module. -/

/-- Bishop's order on regular reals. -/
def le (x y : RegularCReal) : Prop :=
  ∀ n : Nat, x.approx n ≤ y.approx n + (Q'.invSucc n + Q'.invSucc n)

instance : LE RegularCReal := ⟨RegularCReal.le⟩

/-! #### Reflexivity -/

theorem le_refl (x : RegularCReal) : x ≤ x := by
  intro n
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  exact Q'.add_le_self_of_nonneg _ _ hslack

/-! #### A `Q'`-slack regularity corollary used in transitivity

`x_n ≤ x_K + (invSucc n + invSucc K)` and the reverse pullback, in the
exact additive shapes the chaining calc needs. -/

/-- Pull `x_n` up to `x_K`: `x_n ≤ x_K + (invSucc n + invSucc K)`. -/
theorem approx_le_approx_add (x : RegularCReal) (n K : Nat) :
    x.approx n ≤ x.approx K + (Q'.invSucc n + Q'.invSucc K) := by
  -- regular K n gives x_n ≤ x_K + (invSucc K + invSucc n); commute the slack.
  have h := (x.regular K n).2
  refine Q'.le_trans' _ _ _ h ?_
  refine Q'.add_le_add_left (x.approx K) _ _ ?_
  exact Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc K) (Q'.invSucc n))

/-! #### The headline: transitivity of `≤` -/

/-- **THE HEADLINE THEOREM.**  Bishop's order on regular reals is
transitive: `x ≤ y → y ≤ z → x ≤ z`.

Proof.  Fix the target index `n`.  By the Archimedean principle
(`Q'.le_of_le_add_mul_invSucc` with coefficient `6`), it suffices to show
`x_n ≤ z_n + (invSucc n + invSucc n) + 6·(1/(K+1))` for EVERY `K`.  At
each `K`, chain four bounds:

  * `x_n ≤ x_K + (invSucc n + invSucc K)`         (regularity)
  * `x_K ≤ y_K + (invSucc K + invSucc K)`         (`x ≤ y` at `K`)
  * `y_K ≤ z_K + (invSucc K + invSucc K)`         (`y ≤ z` at `K`)
  * `z_K ≤ z_n + (invSucc n + invSucc K)`         (regularity)

Summing collapses the `x_K, y_K, z_K` terms and leaves
`z_n + 2·invSucc n + 6·invSucc K`, which is exactly the per-`K` bound the
Archimedean lemma consumes. -/
theorem le_trans {x y z : RegularCReal} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  intro n
  -- Reduce to the per-K bound via the Archimedean principle (coefficient 6).
  refine Q'.le_of_le_add_mul_invSucc (x.approx n)
    (z.approx n + (Q'.invSucc n + Q'.invSucc n)) 6 ?_
  intro K
  -- The four chaining bounds at index K.
  have hxK : x.approx n ≤ x.approx K + (Q'.invSucc n + Q'.invSucc K) :=
    approx_le_approx_add x n K
  have hxyK : x.approx K ≤ y.approx K + (Q'.invSucc K + Q'.invSucc K) := hxy K
  have hyzK : y.approx K ≤ z.approx K + (Q'.invSucc K + Q'.invSucc K) := hyz K
  have hzK : z.approx K ≤ z.approx n + (Q'.invSucc n + Q'.invSucc K) := by
    -- z_K ≤ z_n + (invSucc n + invSucc K): regular K n side 1, commuted.
    have h := (z.regular K n).1
    refine Q'.le_trans' _ _ _ h ?_
    refine Q'.add_le_add_left (z.approx n) _ _ ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc K) (Q'.invSucc n))
  -- Chain: x_n ≤ z_n + (invSucc n + invSucc n) + 6·invSucc K.
  -- Work on the cross-product / additive level via Q' lemmas.
  -- Build the running upper bound step by step.
  -- Step A: x_n ≤ x_K + (invSucc n + invSucc K)
  -- Step B: add the (x_K → y_K) and (y_K → z_K) and (z_K → z_n) bounds.
  -- We assemble the final RHS and prove the single chained inequality by
  -- transitivity through the partial sums, then identify the slack with
  -- 2·invSucc n + 6·invSucc K via `eqv`.
  -- First chain the four ≤ into one big additive bound.
  have step1 : x.approx n
      ≤ x.approx K + (Q'.invSucc n + Q'.invSucc K) := hxK
  have step2 : x.approx K + (Q'.invSucc n + Q'.invSucc K)
      ≤ (y.approx K + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K) :=
    Q'.add_le_add_right _ _ _ hxyK
  have step3 : (y.approx K + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K)
      ≤ ((z.approx K + (Q'.invSucc K + Q'.invSucc K))
            + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K) :=
    Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hyzK)
  have step4 : ((z.approx K + (Q'.invSucc K + Q'.invSucc K))
            + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K)
      ≤ (((z.approx n + (Q'.invSucc n + Q'.invSucc K))
              + (Q'.invSucc K + Q'.invSucc K))
            + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K) :=
    Q'.add_le_add_right _ _ _
      (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hzK))
  -- Chain all four.
  have hchain : x.approx n
      ≤ (((z.approx n + (Q'.invSucc n + Q'.invSucc K))
              + (Q'.invSucc K + Q'.invSucc K))
            + (Q'.invSucc K + Q'.invSucc K))
          + (Q'.invSucc n + Q'.invSucc K) :=
    Q'.le_trans' _ _ _ step1
      (Q'.le_trans' _ _ _ step2 (Q'.le_trans' _ _ _ step3 step4))
  -- Identify the RHS with z_n + ((invSucc n + invSucc n) + 6·invSucc K).
  refine Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv ?_)
  -- The accumulated slack collects to 2·invSucc n + 6·invSucc K; the
  -- rearrangement is the pure-Q' generic identity `slack6_eqv`.
  exact Q'.slack6_eqv (z.approx n) (Q'.invSucc n) (Q'.invSucc K)

instance : Trans RegularCReal.le RegularCReal.le RegularCReal.le where
  trans hxy hyz := le_trans hxy hyz

/-! #### `Equiv` is an equivalence relation; `le`/`Equiv` compatibility

`Equiv x y` is, definitionally, `le x y ∧ le y x`, so transitivity of
`Equiv` is immediate from `le_trans` on each side.  This is the second
payoff of regularity (the existing `CReal` cannot prove it). -/

/-- `Equiv x y ↔ x ≤ y ∧ y ≤ x` (definitional unfolding). -/
theorem Equiv_iff_le_le (x y : RegularCReal) :
    Equiv x y ↔ (x ≤ y ∧ y ≤ x) := by
  constructor
  · intro h; exact ⟨fun n => (h n).1, fun n => (h n).2⟩
  · intro ⟨h1, h2⟩ n; exact ⟨h1 n, h2 n⟩

/-- The forward half of `Equiv`: `Equiv x y → x ≤ y`. -/
theorem le_of_Equiv {x y : RegularCReal} (h : Equiv x y) : x ≤ y :=
  fun n => (h n).1

/-- The reverse half of `Equiv`: `Equiv x y → y ≤ x`. -/
theorem ge_of_Equiv {x y : RegularCReal} (h : Equiv x y) : y ≤ x :=
  fun n => (h n).2

/-- **`Equiv` is transitive** — provable here BECAUSE `le` is transitive.
From `Equiv x y` and `Equiv y z`, chain the two `le`-halves with
`le_trans` on each side. -/
theorem Equiv.trans {x y z : RegularCReal}
    (hxy : Equiv x y) (hyz : Equiv y z) : Equiv x z :=
  (Equiv_iff_le_le x z).mpr
    ⟨le_trans (le_of_Equiv hxy) (le_of_Equiv hyz),
     le_trans (ge_of_Equiv hyz) (ge_of_Equiv hxy)⟩

/-- **Antisymmetry into `Equiv`.**  `x ≤ y` and `y ≤ x` give `Equiv x y`. -/
theorem le_antisymm {x y : RegularCReal} (hxy : x ≤ y) (hyx : y ≤ x) :
    Equiv x y :=
  (Equiv_iff_le_le x y).mpr ⟨hxy, hyx⟩

/-- `le` respects `Equiv` on the left: `Equiv x x' → x ≤ y → x' ≤ y`. -/
theorem le_congr_left {x x' y : RegularCReal}
    (hx : Equiv x x') (h : x ≤ y) : x' ≤ y :=
  le_trans (ge_of_Equiv hx) h

/-- `le` respects `Equiv` on the right: `Equiv y y' → x ≤ y → x ≤ y'`. -/
theorem le_congr_right {x y y' : RegularCReal}
    (hy : Equiv y y') (h : x ≤ y) : x ≤ y' :=
  le_trans h (le_of_Equiv hy)

/-! ### Order/embedding lemmas mirroring `CReal` -/

/-- `q ≤ q'` at `Q'` lifts to `ofQ' q ≤ ofQ' q'`. -/
theorem ofQ'_le_ofQ' {q q' : Q'} (h : q ≤ q') : ofQ' q ≤ ofQ' q' := by
  intro n
  show q ≤ q' + (Q'.invSucc n + Q'.invSucc n)
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' q q' (q' + (Q'.invSucc n + Q'.invSucc n)) h
    (Q'.add_le_self_of_nonneg q' _ hslack)

/-- If every approximation of `x` is ≥ a rational `lb`, then `ofQ' lb ≤ x`. -/
theorem ofQ'_le_of_approx_ge {x : RegularCReal} {lb : Q'}
    (h : ∀ n : Nat, lb ≤ x.approx n) : ofQ' lb ≤ x := by
  intro n
  show lb ≤ x.approx n + (Q'.invSucc n + Q'.invSucc n)
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' lb (x.approx n) (x.approx n + _) (h n)
    (Q'.add_le_self_of_nonneg (x.approx n) _ hslack)

/-- If every approximation of `x` is ≤ a rational `ub`, then `x ≤ ofQ' ub`. -/
theorem le_ofQ'_of_approx_le {x : RegularCReal} {ub : Q'}
    (h : ∀ n : Nat, x.approx n ≤ ub) : x ≤ ofQ' ub := by
  intro n
  show x.approx n ≤ ub + (Q'.invSucc n + Q'.invSucc n)
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  exact Q'.le_trans' (x.approx n) ub (ub + _) (h n)
    (Q'.add_le_self_of_nonneg ub _ hslack)

/-! ### Strict positivity -/

/-- A `RegularCReal` is **positive** when bounded below by a positive
rational: `∃ ε > 0, ofQ' ε ≤ x`.  (Equality to zero is undecidable;
bounded-below-by-a-positive-rational is the constructive witness.) -/
def IsPositive (x : RegularCReal) : Prop :=
  ∃ ε : Q', (0 : Q') < ε ∧ ofQ' ε ≤ x

/-- Positivity witness: if every approximation is ≥ a positive `ε`. -/
theorem isPositive_of_approx_ge {x : RegularCReal} {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ n : Nat, ε ≤ x.approx n) : IsPositive x :=
  ⟨ε, hε, ofQ'_le_of_approx_ge h⟩

/-! ### Absolute value (deferred)

Index-wise `Q'.abs` would inherit regularity via the reverse-triangle
inequality `|abs u − abs v| ≤ |u − v|`.  The reverse-triangle building
blocks (`abs_eqv_congr`, `abs_add_le'`) live in a heavier downstream
module not on this foundation's import surface; `abs` on `RegularCReal`
is therefore left for the phase that ports those `Q'.abs` lemmas onto
this base.  It is not needed by any lemma in this module. -/

end RegularCReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every declaration below must report `propext` / `Quot.sound` only (the
latter only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.Q'.sub_nonpos_of_le
#print axioms ConstructiveReals.Q'.le_of_sub_nonpos
#print axioms ConstructiveReals.Q'.sub_le_of_le_add'
#print axioms ConstructiveReals.Q'.add_num_cast
#print axioms ConstructiveReals.Q'.ofNat_num_cast
#print axioms ConstructiveReals.Q'.ofNat_den_cast
#print axioms ConstructiveReals.Q'.mul_num_cast
#print axioms ConstructiveReals.Q'.ofNat_mul_invSucc_num
#print axioms ConstructiveReals.Q'.ofNat_mul_invSucc_den
#print axioms ConstructiveReals.Q'.archimedean_cross_int
#print axioms ConstructiveReals.Q'.archimedean_int
#print axioms ConstructiveReals.Q'.le_of_le_add_mul_invSucc
#print axioms ConstructiveReals.Q'.le_of_le_add_residual
#print axioms ConstructiveReals.Q'.slack6_int
#print axioms ConstructiveReals.Q'.slack6_eqv
#print axioms ConstructiveReals.RegularCReal.ofQ'_approx
#print axioms ConstructiveReals.RegularCReal.Equiv.refl
#print axioms ConstructiveReals.RegularCReal.Equiv.symm
#print axioms ConstructiveReals.RegularCReal.Equiv.trans
#print axioms ConstructiveReals.RegularCReal.le_refl
#print axioms ConstructiveReals.RegularCReal.approx_le_approx_add
#print axioms ConstructiveReals.RegularCReal.le_trans
#print axioms ConstructiveReals.RegularCReal.le_antisymm
#print axioms ConstructiveReals.RegularCReal.le_of_Equiv
#print axioms ConstructiveReals.RegularCReal.le_congr_left
#print axioms ConstructiveReals.RegularCReal.le_congr_right
#print axioms ConstructiveReals.RegularCReal.ofQ'_le_ofQ'
#print axioms ConstructiveReals.RegularCReal.ofQ'_le_of_approx_ge
#print axioms ConstructiveReals.RegularCReal.le_ofQ'_of_approx_le
#print axioms ConstructiveReals.RegularCReal.isPositive_of_approx_ge
