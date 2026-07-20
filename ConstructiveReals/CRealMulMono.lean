/-
`CReal.mul` monotonicity / nonnegativity — the order-compatibility of
constructive-real multiplication, intuitionistic (axiom-clean).

The one-slack `CReal.le` (`Reals.lean`) is non-transitive and does not multiply
cleanly (the slack `1/(n+1)` times an unbounded factor is not controlled), so
order facts about products are stated through the SOUND, regularity-free
predicates `CReal.leRat` (limit `≤` a rational, `CRealLe.lean`) and
`ExpPos.geRat` (limit `≥` a rational).  This module provides:

- `Q'.mul_ge_of_bounds` — a sign-cased **lower** bound on a product of bounded
  rationals (`-(Bu+Bv)·δ ≤ u·v`), the dual of `AbsQ.mul_le_of_bounds`.
- `CReal.mul_nonneg` — product of two nonnegatives is nonnegative
  (`geRat A 0 → geRat B 0 → geRat (mul A B) 0`).  This is the heart of
  "multiply an inequality by a nonnegative": `A ≥ c` becomes `A − c ≥ 0`
  (`geRat_add_neg`), and `(A−c)·B ≥ 0` is then `mul_nonneg`.
- `CReal.leRat_smul_nonneg` — scale a rational upper bound by a nonnegative
  rational (`leRat y b → leRat (c·y) (c·b)`), the eventual divide-by-`(1+x)`
  step of the U.5 soundness chain.

Together with the F.4 `mul`/`add`/`neg` substrate these discharge the algebraic
half of `(1+x) ≤ eˣ ⟹ (1+x)·e⁻ˣ ≤ eˣ·e⁻ˣ = 1 ⟹ e⁻ˣ ≤ 1/(1+x)`; the product
law `eˣ·e⁻ˣ = 1` is the remaining analytic piece.

# Axiom-gate (see README: axiom policy)

`[propext]` only (and `Quot.sound` where `Nat`/`omega` enter via reused
helpers).  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.CRealLe
import ConstructiveReals.CRealMul
import ConstructiveReals.CRealAdd
import ConstructiveReals.AbsQ
import ConstructiveReals.ExpPos

namespace ConstructiveReals

namespace Q'

/-- From `0 ≤ a + δ`, get `-δ ≤ a`. -/
theorem neg_le_of_zero_le_add {a δ : Q'} (h : (0 : Q') ≤ a + δ) : -δ ≤ a := by
  have h1 : (0 : Q') + -δ ≤ (a + δ) + -δ := Q'.add_le_add_right 0 (a + δ) (-δ) h
  have e0 : ((0 : Q') + -δ) = -δ := Q'.zero_add' (-δ)
  have e1 : ((a + δ) + -δ).eqv a := by
    have a1 := Q'.add_assoc_eqv a δ (-δ)
    have a2 : (a + (δ + -δ)).eqv (a + 0) :=
      Q'.add_eqv_congr_left a (δ + -δ) 0 (Q'.add_neg_self_eqv δ)
    rw [Q'.add_zero' a] at a2
    exact Q'.eqv_trans _ _ _ a1 a2
  rw [e0] at h1
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e1)

/-- From `c ≤ d`, get `0 ≤ d + -c`. -/
theorem sub_nonneg_of_le {c d : Q'} (h : c ≤ d) : (0 : Q') ≤ d + -c := by
  have h1 : c + -c ≤ d + -c := Q'.add_le_add_right c d (-c) h
  exact Q'.le_trans' 0 (c + -c) (d + -c) (Q'.ge_of_eqv (Q'.add_neg_self_eqv c)) h1

/-- **Sign-cased product lower bound** (dual of `mul_le_of_bounds`):
`-δ ≤ u ≤ Bu`, `-δ ≤ v ≤ Bv` (`δ, Bu, Bv ≥ 0`) ⇒ `-(Bu·δ + Bv·δ) ≤ u·v`. -/
theorem mul_ge_of_bounds {u v δ Bu Bv : Q'}
    (hδ : (0 : Q') ≤ δ) (hBu : (0 : Q') ≤ Bu) (hBv : (0 : Q') ≤ Bv)
    (hu1 : -δ ≤ u) (hu2 : u ≤ Bu) (hv1 : -δ ≤ v) (hv2 : v ≤ Bv) :
    -(Bu * δ + Bv * δ) ≤ u * v := by
  have hBuδ : (0 : Q') ≤ Bu * δ := Q'.mul_nonneg Bu δ hBu hδ
  have hBvδ : (0 : Q') ≤ Bv * δ := Q'.mul_nonneg Bv δ hBv hδ
  have hS : (0 : Q') ≤ Bu * δ + Bv * δ := Q'.zero_le_add _ _ hBuδ hBvδ
  have hnegS_le_negBuδ : -(Bu * δ + Bv * δ) ≤ -(Bu * δ) :=
    Q'.neg_le_neg (Q'.add_le_self_of_nonneg (Bu * δ) (Bv * δ) hBvδ)
  have hnegS_le_negBvδ : -(Bu * δ + Bv * δ) ≤ -(Bv * δ) :=
    Q'.neg_le_neg (Q'.le_trans' (Bv * δ) (Bv * δ + Bu * δ) (Bu * δ + Bv * δ)
      (Q'.add_le_self_of_nonneg (Bv * δ) (Bu * δ) hBuδ)
      (Q'.le_of_eqv (Q'.add_comm_eqv (Bv * δ) (Bu * δ))))
  have hnegS_le_zero : -(Bu * δ + Bv * δ) ≤ (0 : Q') := by
    have := Q'.neg_le_neg hS
    rwa [show (-(0 : Q')) = 0 from rfl] at this
  by_cases hu : (0 : Q') ≤ u
  · by_cases hv : (0 : Q') ≤ v
    · exact Q'.le_trans' _ _ _ hnegS_le_zero (Q'.mul_nonneg u v hu hv)
    · -- u ≥ 0, v < 0 : bound by -(Bu·δ)
      have hnv : (0 : Q') ≤ -v := Q'.neg_nonneg_of_not_nonneg hv
      have s1 : u * (-v) ≤ Bu * (-v) := Q'.mul_le_mul_of_nonneg_right u Bu (-v) hu2 hnv
      have e1 : (u * (-v)).eqv (-(u * v)) := Q'.mul_neg_eqv u v
      have e2 : (Bu * (-v)).eqv (-(Bu * v)) := Q'.mul_neg_eqv Bu v
      have s1' : -(u * v) ≤ -(Bu * v) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) (Q'.le_trans' _ _ _ s1 (Q'.le_of_eqv e2))
      have s1'' : Bu * v ≤ u * v :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv (Bu * v)))
          (Q'.le_trans' _ _ _ (Q'.neg_le_neg s1') (Q'.le_of_eqv (Q'.neg_neg_eqv (u * v))))
      have s2 : Bu * (-δ) ≤ Bu * v := Q'.mul_le_mul_of_nonneg_left (-δ) v Bu hv1 hBu
      have e3 : (Bu * (-δ)).eqv (-(Bu * δ)) := Q'.mul_neg_eqv Bu δ
      have s2' : -(Bu * δ) ≤ Bu * v := Q'.le_trans' _ _ _ (Q'.ge_of_eqv e3) s2
      exact Q'.le_trans' _ _ _ hnegS_le_negBuδ (Q'.le_trans' _ _ _ s2' s1'')
  · by_cases hv : (0 : Q') ≤ v
    · -- u < 0, v ≥ 0 : bound by -(Bv·δ)
      have s1 : (-δ) * v ≤ u * v := Q'.mul_le_mul_of_nonneg_right (-δ) u v hu1 hv
      have e1 : ((-δ) * v).eqv (-(δ * v)) := Q'.neg_mul_eqv δ v
      have s2 : δ * v ≤ δ * Bv := Q'.mul_le_mul_of_nonneg_left v Bv δ hv2 hδ
      have s3 : -(δ * Bv) ≤ -(δ * v) := Q'.neg_le_neg s2
      have s4 : -(δ * v) ≤ (-δ) * v := Q'.ge_of_eqv e1
      have s5 : -(δ * Bv) ≤ u * v := Q'.le_trans' _ _ _ s3 (Q'.le_trans' _ _ _ s4 s1)
      have e2 : (-(Bv * δ)).eqv (-(δ * Bv)) :=
        Q'.neg_eqv_congr (Bv * δ) (δ * Bv) (Q'.mul_comm_eqv Bv δ)
      have s6 : -(Bv * δ) ≤ u * v := Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) s5
      exact Q'.le_trans' _ _ _ hnegS_le_negBvδ s6
    · -- u < 0, v < 0 : u·v ≥ 0
      have hnu : (0 : Q') ≤ -u := Q'.neg_nonneg_of_not_nonneg hu
      have hnv : (0 : Q') ≤ -v := Q'.neg_nonneg_of_not_nonneg hv
      have hpos : (0 : Q') ≤ (-u) * (-v) := Q'.mul_nonneg (-u) (-v) hnu hnv
      have e : ((-u) * (-v)).eqv (u * v) :=
        Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-u) v)
          (Q'.eqv_trans _ _ _
            (Q'.neg_eqv_congr ((-u) * v) (-(u * v)) (Q'.neg_mul_eqv u v))
            (Q'.neg_neg_eqv (u * v)))
      exact Q'.le_trans' _ _ _ hnegS_le_zero
        (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv e))

end Q'

namespace CReal

open Q'

/-- **Product of nonnegatives is nonnegative.** If the limits of `A` and `B`
are both `≥ 0`, so is the limit of `A·B`.  Routed through `geRat` because the
one-slack `≤` does not multiply. -/
theorem mul_nonneg {A B : CReal}
    (hA : ExpPos.geRat A 0) (hB : ExpPos.geRat B 0) :
    ExpPos.geRat (CReal.mul A B) 0 := by
  intro ε hε
  obtain ⟨Na, Ba, hBa, hba⟩ := CReal.localBound A
  obtain ⟨Nb, Bb, hBb, hbb⟩ := CReal.localBound B
  have hBsum : (0 : Q') ≤ Ba + Bb := Q'.zero_le_add _ _ hBa hBb
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hBsum hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  obtain ⟨Na', ha'⟩ := hA δ hδpos
  obtain ⟨Nb', hb'⟩ := hB δ hδpos
  refine ⟨max (max Na Nb) (max Na' Nb'), fun n hn => ?_⟩
  have lna : Na ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have lnb : Nb ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have lna' : Na' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
  have lnb' : Nb' ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
  have hAub : A.approx n ≤ Ba := (hba n lna).2
  have hBub : B.approx n ≤ Bb := (hbb n lnb).2
  have hAlb : -δ ≤ A.approx n := Q'.neg_le_of_zero_le_add (ha' n lna')
  have hBlb : -δ ≤ B.approx n := Q'.neg_le_of_zero_le_add (hb' n lnb')
  have hlow : -(Ba * δ + Bb * δ) ≤ A.approx n * B.approx n :=
    Q'.mul_ge_of_bounds hδnn hBa hBb hAlb hAub hBlb hBub
  -- `Ba·δ + Bb·δ = (Ba+Bb)·δ ≤ ε`
  have hsum_le : Ba * δ + Bb * δ ≤ ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_mul_eqv Ba Bb δ))) hδ
  -- `0 ≤ A_n·B_n + (Ba·δ+Bb·δ)` from `hlow`, then weaken `(Ba·δ+Bb·δ) ≤ ε`
  have h0 : (0 : Q') ≤ A.approx n * B.approx n + (Ba * δ + Bb * δ) := by
    have hstep : -(Ba * δ + Bb * δ) + (Ba * δ + Bb * δ)
        ≤ A.approx n * B.approx n + (Ba * δ + Bb * δ) :=
      Q'.add_le_add_right _ _ (Ba * δ + Bb * δ) hlow
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv (Ba * δ + Bb * δ))) hstep
  -- goal: `0 ≤ (mul A B).approx n + ε`
  exact Q'.le_trans' _ _ _ h0
    (Q'.add_le_add_left (A.approx n * B.approx n) (Ba * δ + Bb * δ) ε hsum_le)

/-- **Scale a rational upper bound by a nonnegative rational.**
`0 ≤ c → leRat y b → leRat (c·y) (c·b)`.  The eventual divide-step:
`(1+x)·e⁻ˣ ≤ 1 ⟹ e⁻ˣ ≤ 1/(1+x)` is this with `c = 1/(1+x)`. -/
theorem leRat_smul_nonneg {c : Q'} (hc : (0 : Q') ≤ c) {y : CReal} {b : Q'}
    (h : CReal.leRat y b) : CReal.leRat (CReal.mul (CReal.ofQ' c) y) (c * b) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hc hε
  obtain ⟨N, hN⟩ := h δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  have hyb : y.approx n ≤ b + δ := hN n hn
  have s1 : c * y.approx n ≤ c * (b + δ) :=
    Q'.mul_le_mul_of_nonneg_left (y.approx n) (b + δ) c hyb hc
  have e1 : (c * (b + δ)).eqv (c * b + c * δ) := Q'.mul_add_eqv c b δ
  have s2 : c * b + c * δ ≤ c * b + ε := Q'.add_le_add_left (c * b) (c * δ) ε hδ
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) s2)

/-- **Subtract a rational from a lower bound.** `geRat A c → geRat (A − c) 0`
(where `A − c := add A (neg (ofQ' c))`).  Turns `A ≥ c` into `A − c ≥ 0`,
the input shape `mul_nonneg` consumes. -/
theorem geRat_add_neg {A : CReal} {c : Q'} (h : ExpPos.geRat A c) :
    ExpPos.geRat (CReal.add A (CReal.neg (CReal.ofQ' c))) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hAc : c ≤ A.approx n + ε := hN n hn
  -- goal: `0 ≤ (A_n + -c) + ε`
  have h0 : (0 : Q') ≤ (A.approx n + ε) + -c := Q'.sub_nonneg_of_le hAc
  have erearr : ((A.approx n + ε) + -c).eqv ((A.approx n + -c) + ε) := by
    have a1 := Q'.add_assoc_eqv (A.approx n) ε (-c)
    have a2 : (A.approx n + (ε + -c)).eqv (A.approx n + (-c + ε)) :=
      Q'.add_eqv_congr_left (A.approx n) (ε + -c) (-c + ε) (Q'.add_comm_eqv ε (-c))
    have a3 : (A.approx n + (-c + ε)).eqv ((A.approx n + -c) + ε) :=
      Q'.eqv_symm (Q'.add_assoc_eqv (A.approx n) (-c) ε)
    exact Q'.eqv_trans _ _ _ a1 (Q'.eqv_trans _ _ _ a2 a3)
  exact Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv erearr)

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.neg_le_of_zero_le_add
#print axioms ConstructiveReals.Q'.sub_nonneg_of_le
#print axioms ConstructiveReals.Q'.mul_ge_of_bounds
#print axioms ConstructiveReals.CReal.mul_nonneg
#print axioms ConstructiveReals.CReal.leRat_smul_nonneg
#print axioms ConstructiveReals.CReal.geRat_add_neg
