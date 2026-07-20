/-
√ of a *CReal* radicand — `csqrt`, with the defining identity `(√x)² ≃ x`.

# What this module builds

The genuine constructive square root `CReal.sqrtFrom` of `Sqrt.lean` takes a
*rational* radicand.  The Chebyshev-node half-angle recursion needs the √ of a
*CReal* radicand `√((1+x)/2)`.  This module supplies it.

## The construction (division-free diagonal)

For `x : CReal` we form the *rational* radicand approximants

    rad  x n = invSucc n + max'(x.approx n, 0)          -- clamped, strictly positive
    radLB n = invSucc n                                  -- a positive √-lower-bound witness

and the per-index genuine roots `radTerm x n = sqrtFrom (rad x n) …` (Heron).  The
limit of the moving-radicand roots is assembled by the EXISTING completeness
engine `completeLimitFromRate` (`CRealCompleteRate.lean`): its per-term regularity
modulus is `sqrtModulus`, and its outer Cauchy rate is supplied as `Type`-level
data through `CSqrtData` (see the honesty note below).

## PROVED here

  * `csqrt x d : CReal`                          — the √, as a genuine `CReal`.
  * `csqrt_converges : ConvergesTo (radTerm x) (csqrt x d)`.
  * `csqrt_nonneg    : czero ≤ csqrt x d`        — `√x ≥ 0` (not `IsPositive`;
    `x` may be `0`, so no uniform positive witness — correct).
  * `csqrt_sq        : (√x)² ≃ x`                — the defining identity, via
    `convergesTo_mul` + `Equiv_of_limit_of_equal` + `sqrtFrom_sq_equiv`, using
    `rad_to_x` (where the `czero ≤ x` hypothesis genuinely enters, bounding the
    clamp defect `max'(x_N,0) − x_N ≤ invSucc N`).

## Honesty note — the one Type-level residual `CSqrtData`

A bare `x : CReal` carries only a **Prop-level** Cauchy field (`∃ N …`).  The
completeness engine needs the outer Cauchy rate of the moving-radicand tower as
**Type-level data** `M : Q' → Nat`; extracting `M` from `x`'s Prop field would
need `Classical.choose` (forbidden by the axiom policy, README).  So `csqrt` is stated for an
`x` **together with** the outer-modulus package `CSqrtData x` (`M`, its
`LeRatBound`, antitonicity, and a uniform `|x_n| ≤ B` bound used by the product
continuity).  This is exactly the datum the downstream Chebyshev consumer *has*
(it builds its radicands and their moduli), so no generality is lost in practice.
The residual is precisely "generic CReal lacks a Type-level modulus" — a real
substrate limitation, named not hidden.

## Axiom gate (see README: axiom policy)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `sorry`, no `native_decide`; `decide` only on closed `Q'`;
`by_cases` only on the *decidable* `Q'` order.  Witnesses (`M`, `reg`) are
`Type`-level data.
-/

import ConstructiveReals.Reals
import ConstructiveReals.Sqrt
import ConstructiveReals.CRealAbs
import ConstructiveReals.CRealExp
import ConstructiveReals.CRealCompleteRate
import ConstructiveReals.RegularCRealArith
import ConstructiveReals.AbsQ

namespace ConstructiveReals

namespace CReal

open Q'

/-! ## A. Rational radicand approximants (division-free, unconditional) -/

/-- The clamped rational radicand approximant `aₙ = invSucc n + max'(xₙ, 0)`.
Always strictly positive (the `invSucc n` term). -/
def rad (x : CReal) (n : Nat) : Q' := Q'.invSucc n + Q'.max' (x.approx n) 0

/-- The rational √-lower-bound witness `Lₙ = invSucc n`. -/
def radLB (n : Nat) : Q' := Q'.invSucc n

theorem invSucc_le_one (n : Nat) : Q'.invSucc n ≤ (1 : Q') := by
  show (Q'.invSucc n).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((Q'.invSucc n).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_den]
  simp only [show ((1 : Q').den : Int) = 1 from rfl, show (1 : Q').num = 1 from rfl]
  omega

theorem rad_pos (x : CReal) (i : Nat) : (0 : Q') < rad x i :=
  Q'.pos_add_nonneg (Q'.invSucc_pos i) (le_max'_right (x.approx i) 0)

theorem radLB_pos (i : Nat) : (0 : Q') < radLB i := Q'.invSucc_pos i

theorem radLB_sq_le (x : CReal) (i : Nat) : radLB i * radLB i ≤ rad x i := by
  -- invSucc·invSucc ≤ invSucc·1 = invSucc ≤ invSucc + max' = rad
  have h1 : Q'.invSucc i * Q'.invSucc i ≤ Q'.invSucc i := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (Q'.invSucc i) 1 (Q'.invSucc i)
        (invSucc_le_one i) (Q'.invSucc_nonneg i)) ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.invSucc i))
  show radLB i * radLB i ≤ Q'.invSucc i + Q'.max' (x.approx i) 0
  refine Q'.le_trans' _ _ _ h1 ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _))) ?_
  exact Q'.add_le_add_left (Q'.invSucc i) 0 (Q'.max' (x.approx i) 0)
    (le_max'_right (x.approx i) 0)

/-- The per-index genuine root `Tₙ = √aₙ` (Heron), as a `CReal`. -/
def radTerm (x : CReal) (n : Nat) : CReal :=
  sqrtFrom (rad x n) (radLB n) (rad_pos x n) (radLB_pos n) (radLB_sq_le x n)

theorem radTerm_approx (x : CReal) (n k : Nat) :
    (radTerm x n).approx k = heronSeq (rad x n) k := rfl

/-- Termwise defining identity `(√aₙ)² ≃ ofQ' aₙ` (re-export of `sqrtFrom_sq_equiv`). -/
theorem radTerm_sq (x : CReal) (n : Nat) :
    CReal.Equiv (CReal.mul (radTerm x n) (radTerm x n)) (CReal.ofQ' (rad x n)) :=
  sqrtFrom_sq_equiv (rad x n) (radLB n) (rad_pos x n) (radLB_pos n) (radLB_sq_le x n)

/-! ## B. The per-term regularity modulus (`sqrtModulus`, positivity-guarded) -/

/-- The per-term Cauchy modulus of `radTerm x i` at tolerance `ε`.  Guarded by a
`dite` on the *decidable* `0 < ε` so the function is total; on `0 < ε` it is the
genuine `sqrtModulus`. -/
def radReg (x : CReal) (i : Nat) (ε : Q') : Nat :=
  if h : (0 : Q') < ε then
    sqrtModulus (rad x i) (radLB i) (rad_pos x i) (radLB_pos i) ε h
  else 0

/-- `radReg` is a genuine per-term regularity modulus for the `radTerm x` tower. -/
theorem radReg_reg (x : CReal) : RegPred (radTerm x) (radReg x) := by
  intro i ε hε p qq hp hqq
  simp only [radReg, dif_pos hε] at hp hqq
  show heronSeq (rad x i) p ≤ heronSeq (rad x i) qq + ε
     ∧ heronSeq (rad x i) qq ≤ heronSeq (rad x i) p + ε
  rcases Nat.le_total qq p with hle | hle
  · refine ⟨?_, ?_⟩
    · exact Q'.le_trans' _ _ _ (heronSeq_antitone (rad x i) (rad_pos x i) hle)
        (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))
    · exact sqrt_cauchy_dir (rad x i) (radLB i) (rad_pos x i) (radLB_pos i)
        (radLB_sq_le x i) ε hε hqq hle
  · refine ⟨?_, ?_⟩
    · exact sqrt_cauchy_dir (rad x i) (radLB i) (rad_pos x i) (radLB_pos i)
        (radLB_sq_le x i) ε hε hp hle
    · exact Q'.le_trans' _ _ _ (heronSeq_antitone (rad x i) (rad_pos x i) hle)
        (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

/-! ## C. The outer-modulus package (the honest Type-level residual) -/

/-- The `Type`-level data a `csqrt` needs beyond `x` itself: the outer Cauchy rate
`M` of the moving-radicand root tower (with its `leRat` bound and antitonicity),
plus a uniform `|x_n| ≤ B` bound (consumed by product continuity in `csqrt_sq`). -/
structure CSqrtData (x : CReal) : Type where
  /-- Outer Cauchy rate of `radTerm x` (Type-level data). -/
  M : Q' → Nat
  /-- The `leRat` outer Cauchy bound at rate `M`. -/
  hb : LeRatBound (radTerm x) M
  /-- `M` is antitone in the tolerance. -/
  Mmono : MmonoPred M
  /-- A uniform bound on `x`'s approximations. -/
  B : Q'
  /-- `0 ≤ B`. -/
  hB0 : (0 : Q') ≤ B
  /-- `|x_n| ≤ B` for every `n`. -/
  hxB : ∀ n, Q'.abs (x.approx n) ≤ B

/-! ## D. The construction and its limit / positivity -/

/-- **The constructive √ of a CReal radicand.**  Assembled by the completeness
engine from the moving-radicand Heron roots `radTerm x`. -/
def csqrt (x : CReal) (d : CSqrtData x) : CReal :=
  completeLimitFromRate (radTerm x) d.M (radReg x) (radReg_reg x) d.hb

theorem csqrt_approx (x : CReal) (d : CSqrtData x) (n : Nat) :
    (csqrt x d).approx n =
      (radTerm x (MhatR d.M n)).approx (RhatR d.M (radReg x) n) := rfl

/-- The moving-radicand roots converge to `csqrt x d`. -/
theorem csqrt_converges (x : CReal) (d : CSqrtData x) :
    ConvergesTo (radTerm x) (csqrt x d) :=
  convergesTo_completeLimitFromRate (radTerm x) d.M (radReg x) (radReg_reg x) d.hb d.Mmono

/-- **`√x ≥ 0`.**  Every approximation is a positive Heron iterate. -/
theorem csqrt_nonneg (x : CReal) (d : CSqrtData x) : czero ≤ csqrt x d := by
  refine ofQ'_le_of_approx_ge (fun n => ?_)
  show (0 : Q') ≤ (csqrt x d).approx n
  rw [csqrt_approx]
  exact Q'.le_of_lt (heronSeq_pos (rad_pos x _) _)

/-! ## E. Uniform bound on the Heron tower (for product continuity) -/

/-- A uniform bound `|√aₖ|_n = heronSeq(aₖ)_n ≤ B + 1 + 1` on the whole
double-indexed Heron tower, from the uniform `|x_n| ≤ B` bound. -/
theorem radTerm_abs_le (x : CReal) (d : CSqrtData x) (k n : Nat) :
    Q'.abs ((radTerm x k).approx n) ≤ d.B + 1 + 1 := by
  show Q'.abs (heronSeq (rad x k) n) ≤ d.B + 1 + 1
  have hpos : (0 : Q') < rad x k := rad_pos x k
  have h0 : (0 : Q') ≤ heronSeq (rad x k) n := Q'.le_of_lt (heronSeq_pos hpos n)
  -- rad x k ≤ B + 1
  have hmaxB : Q'.max' (x.approx k) 0 ≤ d.B :=
    (max'_le_iff' (x.approx k) 0 d.B).mpr
      ⟨Q'.le_trans' _ _ _ (Q'.le_abs_self (x.approx k)) (d.hxB k),
       Q'.le_trans' _ _ _ (Q'.abs_nonneg (x.approx k)) (d.hxB k)⟩
  have hrad : rad x k ≤ d.B + 1 := by
    show Q'.invSucc k + Q'.max' (x.approx k) 0 ≤ d.B + 1
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (invSucc_le_one k) hmaxB) ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv 1 d.B)
  -- heronSeq n ≤ heronSeq 0 = rad + 1 ≤ (B+1)+1
  have hup : heronSeq (rad x k) n ≤ d.B + 1 + 1 := by
    refine Q'.le_trans' _ _ _
      (heronSeq_antitone (rad x k) hpos (Nat.zero_le n)) ?_
    rw [heronSeq_zero]
    exact Q'.add_le_add_right (rad x k) (d.B + 1) 1 hrad
  -- lower: -(B+2) ≤ 0 ≤ heronSeq
  have hB2 : (0 : Q') ≤ d.B + 1 + 1 :=
    Q'.le_trans' 0 (d.B + 1) (d.B + 1 + 1)
      (Q'.le_trans' 0 d.B (d.B + 1) d.hB0
        (Q'.add_le_self_of_nonneg d.B 1 (by decide)))
      (Q'.add_le_self_of_nonneg (d.B + 1) 1 (by decide))
  have hneg : -(d.B + 1 + 1) ≤ (0 : Q') := Q'.neg_le_neg hB2
  exact Q'.abs_le (Q'.le_trans' _ _ _ hneg h0) hup

/-! ## F. `rad_to_x` — the moving radicands converge to `x` (uses `czero ≤ x`) -/

/-- **The clamped radicands converge to `x`.**  Here the `czero ≤ x` hypothesis
genuinely enters: it bounds the clamp defect `max'(x_N,0) − x_N ≤ invSucc N`. -/
theorem rad_to_x (x : CReal) (h : czero ≤ x) :
    ConvergesTo (fun n => CReal.ofQ' (rad x n)) x := by
  intro ε hε
  let p : Q' := HalfPow.half * (HalfPow.half * ε)
  have hp : (0 : Q') < p := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  -- p + (p + p) ≤ ε  (three quarters ≤ one)
  have h3p : p + (p + p) ≤ ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv p p p))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg ((p + p) + p) p (Q'.le_of_lt hp)) ?_
    exact fourQ_le ε hε
  have hple : p ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg p (p + p) (Q'.le_of_lt (Q'.add_pos hp hp))) h3p
  obtain ⟨Nc, hNc⟩ := x.cauchy p hp
  refine ⟨max Nc p.den, fun N hN => ⟨max Nc p.den, fun n hn => ?_⟩⟩
  have hNNc : Nc ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hNden : p.den ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hnNc : Nc ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  obtain ⟨hxc, hxc'⟩ := hNc N n hNNc hnNc   -- x_N ≤ x_n + p , x_n ≤ x_N + p
  -- invSucc N ≤ p
  have hinv : Q'.invSucc N ≤ p :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hNden) (HalfPow.invSucc_den_le p hp)
  -- clamp: 0 ≤ x_N + invSucc N  (from h at N)
  have hposN : (0 : Q') ≤ x.approx N + Q'.invSucc N := h N
  -- max'(x_N,0) ≤ x_N + p
  have hclamp : Q'.max' (x.approx N) 0 ≤ x.approx N + Q'.invSucc N :=
    (max'_le_iff' (x.approx N) 0 (x.approx N + Q'.invSucc N)).mpr
      ⟨Q'.add_le_self_of_nonneg (x.approx N) (Q'.invSucc N) (Q'.invSucc_nonneg N), hposN⟩
  have hmaxp : Q'.max' (x.approx N) 0 ≤ x.approx N + p :=
    Q'.le_trans' _ _ _ hclamp (Q'.add_le_add_left (x.approx N) (Q'.invSucc N) p hinv)
  refine ⟨?_, ?_⟩
  · -- rad x N ≤ x_n + ε
    show rad x N ≤ x.approx n + ε
    -- rad = invSucc N + max' ≃ max' + invSucc N ≤ (x_N + p) + p ≤ ((x_n + p) + p) + p ≤ x_n + ε
    have hcomm : (rad x N).eqv (Q'.max' (x.approx N) 0 + Q'.invSucc N) :=
      Q'.add_comm_eqv (Q'.invSucc N) (Q'.max' (x.approx N) 0)
    have hstep1 : Q'.max' (x.approx N) 0 + Q'.invSucc N ≤ (x.approx N + p) + p :=
      Q'.add_le_add hmaxp hinv
    have hstep2 : (x.approx N + p) + p ≤ ((x.approx n + p) + p) + p :=
      Q'.add_le_add_right _ _ p (Q'.add_le_add_right _ _ p hxc)
    have hchain : rad x N ≤ ((x.approx n + p) + p) + p :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) (Q'.le_trans' _ _ _ hstep1 hstep2)
    -- ((x_n + p)+p)+p ≤ x_n + (p + (p+p)) ≤ x_n + ε
    refine Q'.le_trans' _ _ _ hchain ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.add_le_add_left (x.approx n) (p + (p + p)) ε h3p)
    -- ((x_n + p)+p)+p ≃ x_n + (p + (p+p))
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x.approx n + p) p p) ?_
    exact Q'.add_assoc_eqv (x.approx n) p (p + p)
  · -- x_n ≤ rad x N + ε
    show x.approx n ≤ rad x N + ε
    have hxle_rad : x.approx N ≤ rad x N := by
      refine Q'.le_trans' _ _ _ (le_max'_left (x.approx N) 0) ?_
      show Q'.max' (x.approx N) 0 ≤ Q'.invSucc N + Q'.max' (x.approx N) 0
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv _))) ?_
      exact Q'.add_le_add_right 0 (Q'.invSucc N) (Q'.max' (x.approx N) 0) (Q'.invSucc_nonneg N)
    refine Q'.le_trans' _ _ _ hxc' ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ p hxle_rad) ?_
    exact Q'.add_le_add_left (rad x N) p ε hple

/-! ## G. The defining identity `(√x)² ≃ x` -/

/-- **`(√x)² ≃ x`.**  Product continuity of the moving-radicand roots
(`convergesTo_mul`), termwise `(√aₙ)² ≃ ofQ' aₙ` (`radTerm_sq`), and
`rad x n → x` (`rad_to_x`), assembled by `Equiv_of_limit_of_equal`. -/
theorem csqrt_sq (x : CReal) (d : CSqrtData x) (h : czero ≤ x) :
    CReal.Equiv (CReal.mul (csqrt x d) (csqrt x d)) x := by
  have hB2 : (0 : Q') ≤ d.B + 1 + 1 :=
    Q'.le_trans' 0 (d.B + 1) (d.B + 1 + 1)
      (Q'.le_trans' 0 d.B (d.B + 1) d.hB0
        (Q'.add_le_self_of_nonneg d.B 1 (by decide)))
      (Q'.add_le_self_of_nonneg (d.B + 1) 1 (by decide))
  have hub : ∀ k n, Q'.abs ((radTerm x k).approx n) ≤ d.B + 1 + 1 :=
    radTerm_abs_le x d
  have hVb : ∀ n, Q'.abs ((csqrt x d).approx n) ≤ d.B + 1 + 1 := by
    intro n
    rw [csqrt_approx]
    exact radTerm_abs_le x d _ _
  have hmul :
      ConvergesTo (fun k => CReal.mul (radTerm x k) (radTerm x k))
        (CReal.mul (csqrt x d) (csqrt x d)) :=
    convergesTo_mul hB2 hub hVb (csqrt_converges x d) (csqrt_converges x d)
  exact Equiv_of_limit_of_equal (fun N => radTerm_sq x N) hmul (rad_to_x x h)

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.CReal.rad_pos
#print axioms ConstructiveReals.CReal.radLB_sq_le
#print axioms ConstructiveReals.CReal.radReg_reg
#print axioms ConstructiveReals.CReal.csqrt
#print axioms ConstructiveReals.CReal.csqrt_converges
#print axioms ConstructiveReals.CReal.csqrt_nonneg
#print axioms ConstructiveReals.CReal.rad_to_x
#print axioms ConstructiveReals.CReal.csqrt_sq
