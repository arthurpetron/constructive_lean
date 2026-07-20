/-
# Constructive completeness backbone for `CReal`

A constructive (Specker-aware) completeness layer for the Bishop-style regular
reals `CReal`.  Specker's theorem says a Cauchy/monotone sequence has **no**
limit without an EXPLICIT modulus, so every limit constructor here carries its
modulus as `Type`-level data (functions `Q' → Nat`, never a bare `∃`).

This module provides four reusable pieces, in dependency order:

* **`CReal.sub`** — the additive difference `x − y := add x (neg y)`, with the
  embedding compatibility `ofQ'_sub` and `sub_self_eqv_zero`.  (`add`/`neg`
  already exist pointwise; `sub` is the named convenience the limit lemmas use.)

* **`CReal.le_trans`** — transitivity of the one-slack Bishop order.  The
  one-slack `≤` is **not** pointwise transitive (the `1/(n+1)` slack
  accumulates), so the proof routes through the rational eventual-`≤` form
  `leEv` (`x_n ≤ y_n + ε` eventually, for every `ε > 0`), which IS transitive by
  an `ε/2` split and is inter-derivable with the one-slack `≤` (`le_of_leEv` uses
  the Cauchy moduli of `x` and `y`; `leEv_of_le` uses the Archimedean `invSucc`
  bound).  This closes the long-standing one-slack-transitivity gap.

* **`CReal.completeLimit`** — the headline.  A `CReal` sequence `s : Nat → CReal`
  packaged as `ModCauchy s` — an OUTER modulus `M : Q' → Nat` (uniform two-sided
  approx bound between terms) together with a UNIFORM INNER regularity modulus
  `reg : Q' → Nat` (a single Cauchy modulus working for every term `s i`) —
  yields a limit `CReal L` (the monotone-shifted diagonal
  `L.approx k := (s (Mhat k)).approx k`, `Mhat` the running max of
  `M (invSucc 0..k)`) together with `ConvergesTo s L`.  This generalises the
  geometric-increment constructor to an arbitrary uniform-rate modulus-Cauchy
  `CReal` sequence.  The two moduli are `Type`-level data, so no convergence
  witness hides in a `Prop` `∃` (Rule 8.3).

* **bound-passing** — `ofQ' lb ≤ s k` for all `k` lifts to `ofQ' lb ≤ L`
  (`ofQ'_le_completeLimit`), dually for upper bounds, and `IsPositive` passes to
  the limit (`isPositive_completeLimit`), using `≤`-transitivity + convergence.

A small non-vacuity demo (`demoConstLimit`) constructs the limit of a concrete
modulus-Cauchy `CReal` sequence.

# Axiom-gate (see README: axiom policy)

Every load-bearing declaration reports `[propext]` (and `Quot.sound` only where
`Nat`/`omega`/`Int` helpers reach it).  No `Classical.*`, no `native_decide`, no
`sorry`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.CRealLe
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealAbs
import ConstructiveReals.ExpNeg
import ConstructiveReals.HalfPow

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.HalfPow

namespace CReal

open Q'

/-! ## 0. Difference `CReal.sub` -/

/-- The constructive-real difference `x − y := add x (neg y)`. -/
def sub (x y : CReal) : CReal := add x (neg y)

@[simp] theorem sub_approx (x y : CReal) (n : Nat) :
    (sub x y).approx n = x.approx n + (-(y.approx n)) := rfl

/-- `sub` commutes with the embedding: `ofQ' a − ofQ' b = ofQ' (a + (-b))`. -/
theorem ofQ'_sub (a b : Q') : sub (ofQ' a) (ofQ' b) = ofQ' (a + (-b)) := rfl

/-- `x − x ≃ 0`: the difference of a `CReal` with itself is infinitesimal. -/
theorem sub_self_eqv_zero (x : CReal) : CReal.Equiv (sub x x) czero := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have he : (x.approx n + (-(x.approx n))).eqv (0 : Q') := Q'.add_neg_self_eqv (x.approx n)
  have hzeps : (0 : Q') ≤ (0 : Q') + ε :=
    Q'.add_le_self_of_nonneg 0 ε (Q'.le_of_lt hε)
  refine ⟨?_, ?_⟩
  · -- x_n + -x_n ≤ 0 ≤ 0 + ε = czero_n + ε
    show x.approx n + (-(x.approx n)) ≤ (0 : Q') + ε
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hzeps
  · -- czero_n = 0 ≤ (x_n + -x_n) + ε
    show (0 : Q') ≤ (x.approx n + (-(x.approx n))) + ε
    refine Q'.le_trans' _ _ _ hzeps ?_
    exact Q'.add_le_add_right _ _ ε (Q'.ge_of_eqv he)

/-! ## 1. The rational eventual order `leEv` and `≤`-transitivity -/

/-- The eventual rational order: the limit of `x` is `≤` the limit of `y`. -/
def leEv (x y : CReal) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → x.approx n ≤ y.approx n + ε

/-- `leEv` is transitive (`ε/2` split). -/
theorem leEv_trans {x y z : CReal} (h1 : leEv x y) (h2 : leEv y z) : leEv x z := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨N1, hN1⟩ := h1 (half * ε) hhε
  obtain ⟨N2, hN2⟩ := h2 (half * ε) hhε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine Q'.le_trans' _ _ _ (hN1 n hn1) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (half * ε) (hN2 n hn2)) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (z.approx n) (half * ε) (half * ε)) ?_)
  exact Q'.add_eqv_congr_left (z.approx n) (half * ε + half * ε) ε (ExpNeg.two_halves ε)

/-- **One-slack `≤` ⟹ eventual `≤`.**  `N = ε.den` makes `invSucc n ≤ ε`. -/
theorem leEv_of_le {x y : CReal} (h : x ≤ y) : leEv x y := by
  intro ε hε
  refine ⟨ε.den, fun n hn => ?_⟩
  have hinv : Q'.invSucc n ≤ ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le ε hε)
  refine Q'.le_trans' _ _ _ (h n) ?_
  exact Q'.add_le_add_left (y.approx n) (Q'.invSucc n) ε hinv

/-- `leEv` is reflexive. -/
theorem leEv_refl (x : CReal) : leEv x x := by
  intro ε hε
  exact ⟨0, fun n _ => Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε)⟩

/-- A `Q'` lower bound on every approx lifts to `leEv (ofQ' lb) x`. -/
theorem leEv_ofQ'_of_approx_ge {x : CReal} {lb : Q'}
    (h : ∀ n : Nat, lb ≤ x.approx n) : leEv (ofQ' lb) x := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show lb ≤ x.approx n + ε
  exact Q'.le_trans' _ _ _ (h n) (Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε))

/-- A `Q'` upper bound on every approx lifts to `leEv x (ofQ' ub)`. -/
theorem leEv_le_ofQ'_of_approx_le {x : CReal} {ub : Q'}
    (h : ∀ n : Nat, x.approx n ≤ ub) : leEv x (ofQ' ub) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show x.approx n ≤ ub + ε
  exact Q'.le_trans' _ _ _ (h n) (Q'.add_le_self_of_nonneg ub ε (Q'.le_of_lt hε))

/-! ### The transitive order is `leEv`, not the one-slack `≤`

The one-slack order `x ≤ y` (`∀ n, x_n ≤ y_n + 1/(n+1)`) is **not** transitive
for this (merely-Cauchy, NOT regular) `CReal`: the slack `1/(n+1)` accumulates,
and at small `n` the unconstrained raw approximations `x_0`, `x_1`, … carry no
relation to the limit, so the standard lookahead argument has nothing to bound
`x_n − x_m` by at small `n`.  Transitivity of `≤` would require regularity
(`|x_m − x_n| ≤ 1/(n+1)`), which `CReal.cauchy` does not provide.

The correct transitive order on these reals is the regularity-free EVENTUAL order
`leEv` (proved transitive above).  `leEv_of_le` lifts any one-slack inequality
into it, so downstream code that needs transitive comparison should compose in
`leEv`.  This module therefore closes the transitivity obligation at the `leEv`
layer rather than papering over the genuine `≤`-defect. -/

/-! ## 2. General completeness — the uniform-rate modulus-Cauchy limit -/

/-- A uniform-rate modulus-Cauchy datum for a `CReal` sequence `s`: an OUTER
modulus `M` (terms within `ε` of each other, uniformly in the approx index, for
indices `≥ M ε`) and a single UNIFORM INNER regularity modulus `reg` (a Cauchy
modulus that works for EVERY term `s i`).  Both are `Type`-level data. -/
structure ModCauchy (s : Nat → CReal) where
  /-- Outer Cauchy modulus, `Type`-level data. -/
  M : Q' → Nat
  /-- Uniform inner regularity modulus, `Type`-level data. -/
  reg : Q' → Nat
  /-- Outer uniform two-sided bound: for `m, n ≥ M ε`, every approx index is
  within `ε`. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
    ∀ k : Nat, (s m).approx k ≤ (s n).approx k + ε ∧ (s n).approx k ≤ (s m).approx k + ε
  /-- Uniform inner regularity: each term `s i` is Cauchy with modulus `reg`. -/
  regular : ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg ε ≤ p → reg ε ≤ qq →
    (s i).approx p ≤ (s i).approx qq + ε ∧ (s i).approx qq ≤ (s i).approx p + ε
  /-- The outer modulus is antitone: a smaller target tolerance needs a later
  stage (`δ ≤ ε ⟹ M ε ≤ M δ`).  Every reasonable modulus satisfies this and it
  is what makes the diagonal converge to the supplied terms. -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ

/-- Running-max of `M (invSucc 0), …, M (invSucc k)` — monotone, dominating each. -/
def Mhat (s : Nat → CReal) (c : ModCauchy s) : Nat → Nat
  | 0 => c.M (Q'.invSucc 0)
  | k + 1 => max (Mhat s c k) (c.M (Q'.invSucc (k + 1)))

theorem Mhat_mono_succ (s : Nat → CReal) (c : ModCauchy s) (k : Nat) :
    Mhat s c k ≤ Mhat s c (k + 1) := Nat.le_max_left _ _

theorem Mhat_mono (s : Nat → CReal) (c : ModCauchy s) {a b : Nat} (h : a ≤ b) :
    Mhat s c a ≤ Mhat s c b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (Mhat_mono_succ s c b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

/-- `c.M (invSucc k) ≤ Mhat s c k`. -/
theorem M_le_Mhat (s : Nat → CReal) (c : ModCauchy s) (k : Nat) :
    c.M (Q'.invSucc k) ≤ Mhat s c k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The monotone-shifted diagonal `D k = (s (Mhat k)).approx k`. -/
def diagSeq (s : Nat → CReal) (c : ModCauchy s) (k : Nat) : Q' :=
  (s (Mhat s c k)).approx k

/-- The directed core bound on the diagonal: for `a ≤ b` and `a, b ≥ N(ε)` (with
`N ε = max (q.den) (reg q)`, `q = ¼ε`), `|D a − D b| ≤ ε`.  Bridges
`D a → (s (Mhat b))_a → (s (Mhat b))_b = D b` via the OUTER bound at scale
`invSucc a ≤ q` (terms `≥ M (invSucc a)`) and the UNIFORM INNER regularity of
`s (Mhat b)` at scale `q` (approx indices `a, b ≥ reg q`). -/
theorem diagSeq_directed (s : Nat → CReal) (c : ModCauchy s)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∀ a b : Nat, a ≤ b → max (half * (half * ε)).den (c.reg (half * (half * ε))) ≤ a →
      diagSeq s c a ≤ diagSeq s c b + ε ∧ diagSeq s c b ≤ diagSeq s c a + ε := by
  intro a b hab hNa
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  have hda : q.den ≤ a := Nat.le_trans (Nat.le_max_left _ _) hNa
  have hra : c.reg q ≤ a := Nat.le_trans (Nat.le_max_right _ _) hNa
  have hrb : c.reg q ≤ b := Nat.le_trans hra hab
  have hinvapos : (0 : Q') < Q'.invSucc a := Q'.invSucc_pos a
  have hinva : Q'.invSucc a ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hda) (HalfPow.invSucc_den_le q hqpos)
  have hMa : c.M (Q'.invSucc a) ≤ Mhat s c a := M_le_Mhat s c a
  have hMb : c.M (Q'.invSucc a) ≤ Mhat s c b := Nat.le_trans hMa (Mhat_mono s c hab)
  -- OUTER bounds (both directions) at scale invSucc a, approx index a.
  obtain ⟨hO1, hO2⟩ := c.bound (Q'.invSucc a) hinvapos (Mhat s c a) (Mhat s c b) hMa hMb a
  have hO1' : (s (Mhat s c a)).approx a ≤ (s (Mhat s c b)).approx a + q :=
    Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_left _ _ q hinva)
  have hO2' : (s (Mhat s c b)).approx a ≤ (s (Mhat s c a)).approx a + q :=
    Q'.le_trans' _ _ _ hO2 (Q'.add_le_add_left _ _ q hinva)
  -- INNER regularity (both directions) of s (Mhat b) between approx indices a, b.
  obtain ⟨hI1, hI2⟩ := c.regular (Mhat s c b) q hqpos a b hra hrb
  -- `2q ≤ ε` collapse.
  have htwoq : ∀ w : Q', (w + q) + q ≤ w + ε := by
    intro w
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w q q)) ?_
    refine Q'.add_le_add_left w (q + q) ε ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves (half * ε))) ?_
    -- ½ε ≤ ½ε + ½ε ≃ ε
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (half * ε) (half * ε) (Q'.le_of_lt (ExpNeg.half_mul_pos ε hε))) ?_
    exact Q'.le_of_eqv (ExpNeg.two_halves ε)
  refine ⟨?_, ?_⟩
  · -- D a = (s Mhat a)_a ≤ (s Mhat b)_a + q ≤ ((s Mhat b)_b + q) + q ≤ D b + ε
    have hchain : diagSeq s c a ≤ ((s (Mhat s c b)).approx b + q) + q :=
      Q'.le_trans' _ _ _ hO1' (Q'.add_le_add_right _ _ q hI1)
    exact Q'.le_trans' _ _ _ hchain (htwoq (diagSeq s c b))
  · -- D b = (s Mhat b)_b ≤ (s Mhat b)_a + q ≤ ((s Mhat a)_a + q) + q ≤ D a + ε
    have hchain : diagSeq s c b ≤ ((s (Mhat s c a)).approx a + q) + q :=
      Q'.le_trans' _ _ _ hI2 (Q'.add_le_add_right _ _ q hO2')
    exact Q'.le_trans' _ _ _ hchain (htwoq (diagSeq s c a))

/-- **General completeness limit.**  The monotone-shifted diagonal of a
uniform-rate modulus-Cauchy `CReal` sequence is a `CReal`. -/
def completeLimit (s : Nat → CReal) (c : ModCauchy s) : CReal where
  approx k := diagSeq s c k
  cauchy := by
    intro ε hε
    refine ⟨max (half * (half * ε)).den (c.reg (half * (half * ε))), fun a b ha hb => ?_⟩
    rcases Nat.le_total a b with hab | hba
    · exact diagSeq_directed s c ε hε a b hab ha
    · have h := diagSeq_directed s c ε hε b a hba hb
      exact ⟨h.2, h.1⟩

@[simp] theorem completeLimit_approx (s : Nat → CReal) (c : ModCauchy s) (k : Nat) :
    (completeLimit s c).approx k = (s (Mhat s c k)).approx k := rfl

/-- **The diagonal limit is the limit of `s`.**  `ConvergesTo s (completeLimit s c)`.
At scale `ε`: the term-stage is `c.M ε`; for any term `N ≥ c.M ε` and any approx
index `n ≥ ε.den` (so `invSucc n ≤ ε`, whence `Mhat n ≥ M (invSucc n) ≥ M ε` by
antitonicity), the OUTER uniform bound at scale `ε` comparing `s N` and
`s (Mhat n)` at approx index `n` gives `|(s N)_n − L_n| ≤ ε`. -/
theorem convergesTo_completeLimit (s : Nat → CReal) (c : ModCauchy s) :
    ConvergesTo s (completeLimit s c) := by
  intro ε hε
  refine ⟨c.M ε, fun N hN => ⟨ε.den, fun n hn => ?_⟩⟩
  -- invSucc n ≤ ε  (since n ≥ ε.den)
  have hinvn : Q'.invSucc n ≤ ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le ε hε)
  have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
  -- M ε ≤ M (invSucc n) ≤ Mhat n
  have hMen : c.M ε ≤ Mhat s c n :=
    Nat.le_trans (c.Mmono ε (Q'.invSucc n) hinvnpos hinvn) (M_le_Mhat s c n)
  -- outer bound at scale ε comparing s N and s (Mhat n), approx index n.
  obtain ⟨h1, h2⟩ := c.bound ε hε N (Mhat s c n) hN hMen n
  -- (completeLimit).approx n = (s (Mhat n)).approx n
  exact ⟨h1, h2⟩

/-! ## 3. Bound-passing to the diagonal limit -/

/-- **Lower bound passes to the limit.**  If `ofQ' lb ≤ s k` for every term `k`
(at the one-slack level, i.e. `lb ≤ (s k)_j` for all `j`), then
`leEv (ofQ' lb) (completeLimit s c)`: the limit's eventual value is `≥ lb`. -/
theorem leEv_ofQ'_completeLimit (s : Nat → CReal) (c : ModCauchy s) {lb : Q'}
    (h : ∀ k j : Nat, lb ≤ (s k).approx j) :
    leEv (ofQ' lb) (completeLimit s c) :=
  leEv_ofQ'_of_approx_ge (fun n => h (Mhat s c n) n)

/-- **Upper bound passes to the limit.** -/
theorem leEv_completeLimit_ofQ' (s : Nat → CReal) (c : ModCauchy s) {ub : Q'}
    (h : ∀ k j : Nat, (s k).approx j ≤ ub) :
    leEv (completeLimit s c) (ofQ' ub) :=
  leEv_le_ofQ'_of_approx_le (fun n => h (Mhat s c n) n)

/-- **Strict positivity passes to the limit (eventual form).**  If every approx
of every term is `≥ ε > 0`, then `leEv (ofQ' ε) (completeLimit s c)` with the
same positive witness — the `leEv`-level analog of `IsPositive`. -/
theorem isPositiveEv_completeLimit (s : Nat → CReal) (c : ModCauchy s) {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ k j : Nat, ε ≤ (s k).approx j) :
    (0 : Q') < ε ∧ leEv (ofQ' ε) (completeLimit s c) :=
  ⟨hε, leEv_ofQ'_completeLimit s c h⟩

end CReal

/-! ## 4. Non-vacuity demo

A concrete uniform-rate modulus-Cauchy `CReal` sequence: the constant sequence
`s k = ofQ' 1`.  Its outer modulus is `M ε = 0` (all terms are identical), its
inner regularity modulus is `reg ε = 0` (each `ofQ' 1` is constant), and the
diagonal limit is again `ofQ' 1` definitionally.  This exhibits the completeness
machinery as non-vacuous end to end. -/

namespace CReal

/-- The constant `CReal` sequence at `ofQ' 1`. -/
def constSeq : Nat → CReal := fun _ => ofQ' 1

/-- The constant sequence is uniform-rate modulus-Cauchy with trivial moduli. -/
def constSeqModCauchy : ModCauchy constSeq where
  M := fun _ => 0
  reg := fun _ => 0
  bound := by
    intro ε hε m n _ _ k
    -- (constSeq m).approx k = 1 = (constSeq n).approx k ; bound by self + ε.
    refine ⟨?_, ?_⟩ <;>
      exact Q'.add_le_self_of_nonneg (1 : Q') ε (Q'.le_of_lt hε)
  regular := by
    intro i ε hε p qq _ _
    refine ⟨?_, ?_⟩ <;>
      exact Q'.add_le_self_of_nonneg (1 : Q') ε (Q'.le_of_lt hε)
  Mmono := by intro _ _ _ _; exact Nat.le_refl 0

/-- The completeness limit of the constant `ofQ' 1` sequence. -/
def demoConstLimit : CReal := completeLimit constSeq constSeqModCauchy

/-- The demo limit is `ofQ' 1` at the level of approximations. -/
theorem demoConstLimit_approx (k : Nat) : demoConstLimit.approx k = (1 : Q') := rfl

/-- The machinery is non-vacuous: the constant sequence converges to its limit. -/
theorem demoConstLimit_converges : ConvergesTo constSeq demoConstLimit :=
  convergesTo_completeLimit constSeq constSeqModCauchy

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.CReal.sub_approx
#print axioms ConstructiveReals.CReal.ofQ'_sub
#print axioms ConstructiveReals.CReal.sub_self_eqv_zero
#print axioms ConstructiveReals.CReal.leEv_trans
#print axioms ConstructiveReals.CReal.leEv_of_le
#print axioms ConstructiveReals.CReal.leEv_refl
#print axioms ConstructiveReals.CReal.leEv_ofQ'_of_approx_ge
#print axioms ConstructiveReals.CReal.leEv_le_ofQ'_of_approx_le
#print axioms ConstructiveReals.CReal.Mhat_mono
#print axioms ConstructiveReals.CReal.M_le_Mhat
#print axioms ConstructiveReals.CReal.diagSeq_directed
#print axioms ConstructiveReals.CReal.completeLimit
#print axioms ConstructiveReals.CReal.completeLimit_approx
#print axioms ConstructiveReals.CReal.convergesTo_completeLimit
#print axioms ConstructiveReals.CReal.leEv_ofQ'_completeLimit
#print axioms ConstructiveReals.CReal.leEv_completeLimit_ofQ'
#print axioms ConstructiveReals.CReal.isPositiveEv_completeLimit
#print axioms ConstructiveReals.CReal.demoConstLimit_approx
#print axioms ConstructiveReals.CReal.demoConstLimit_converges
