/-
# Constructive-real absolute value, the infinitesimal lemma, and limit-of-equal-sequences

This module supplies the small CReal-level analytic infrastructure named by the
constructive-reals route (CoRN `AbsIR` / `approach_zero_weak`) for closing the
differentiated Jacobi-triple-product residual without classical input:

* **`CReal.abs`** — absolute value, defined INDEX-WISE (`(abs x).approx n :=
  Q'.abs (x.approx n)`), reusing the `Q'.abs` of `AbsQ.lean`.  Defining it
  index-wise (NOT via sign trichotomy, which is undecidable / needs LEM) makes
  the Cauchy modulus immediate from the reverse-triangle inequality
  `||a| − |b|| ≤ |a − b|`.  It respects the `Equiv` setoid (`abs_equiv_congr`).

* **`eqv_zero_of_abs_le_all_pos`** — the infinitesimal lemma (CoRN
  `AbsIR_approach_zero`): if `|x|`'s limit is `≤ ε` for EVERY rational `ε > 0`
  (here phrased as the eventual-approximation bound `CReal.leRat (abs x) ε`),
  then `x ≃ 0` (`CReal.Equiv x czero`).  Proved through the all-rational-ε form,
  NO classical trichotomy.

* **`Equiv_of_limit_of_equal`** — the limit-of-equal-sequences lemma (uniqueness
  of limits): if two CReal sequences `aSeq, bSeq : Nat → CReal` are `Equiv`
  term-by-term (`∀ N, Equiv (aSeq N) (bSeq N)`) and each converges (with explicit
  modulus) to a limit (`aSeq N → A`, `bSeq N → B`), then `Equiv A B`.  This is the
  generic engine that lifts the FINITE Gauss q-binomial identity
  `GaussQBinom.gauss_qbinom_all` (an `aₙ ≃ bₙ` for all finite `N`) to the
  UNDIFFERENTIATED limit-level Jacobi identity `ϑ₃^{ser} = ϑ₃^{prod}` as CReals.

## Axiom gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.AbsQ
import ConstructiveReals.HalfPow
import ConstructiveReals.ExpNeg
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealLe
import ConstructiveReals.ExpAdd

namespace ConstructiveReals

open ConstructiveReals

namespace Q'

/-! ## 0. `Q'` reverse-triangle and abs helpers

Local copies (the `CRealAbs` import chain does not reach `TsumDeriv`): `abs`
respects `eqv`, `abs (x·…)` triangle, and the reverse triangle `|a| ≤ |b| + |a−b|`.
All from the `AbsQ.lean` primitives. -/

/-- An `Eq` lifts to `eqv`. -/
theorem eqv_of_eq' {a b : Q'} (h : a = b) : a.eqv b := by subst h; exact Q'.eqv_refl a

/-- Two-sided additive congruence. -/
theorem add_eqv_congr' {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-- `abs` respects `eqv`. -/
theorem abs_eqv_congr {a b : Q'} (h : a.eqv b) : (Q'.abs a).eqv (Q'.abs b) := by
  have hab : a ≤ b := Q'.le_of_eqv h
  have hba : b ≤ a := Q'.ge_of_eqv h
  have h1 : Q'.abs a ≤ Q'.abs b := by
    refine Q'.abs_le ?_ ?_
    · have hnb : -(Q'.abs b) ≤ b := by
        have := Q'.neg_le_abs b
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv b))
      exact Q'.le_trans' _ _ _ hnb hba
    · exact Q'.le_trans' _ _ _ hab (Q'.le_abs_self b)
  have h2 : Q'.abs b ≤ Q'.abs a := by
    refine Q'.abs_le ?_ ?_
    · have hna : -(Q'.abs a) ≤ a := by
        have := Q'.neg_le_abs a
        have hh := Q'.neg_le_neg this
        exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv a))
      exact Q'.le_trans' _ _ _ hna hab
    · exact Q'.le_trans' _ _ _ hba (Q'.le_abs_self a)
  show (Q'.abs a).num * ((Q'.abs b).den : Int) = (Q'.abs b).num * ((Q'.abs a).den : Int)
  exact Int.le_antisymm h1 h2

/-- `abs (u + v) ≤ abs u + abs v` (the triangle inequality on `Q'`). -/
theorem abs_add_le' (u v : Q') : Q'.abs (u + v) ≤ Q'.abs u + Q'.abs v := by
  refine Q'.abs_le ?_ ?_
  · have hu : -(Q'.abs u) ≤ u := by
      have := Q'.neg_le_abs u
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv u))
    have hv : -(Q'.abs v) ≤ v := by
      have := Q'.neg_le_abs v
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv v))
    have hneg : (-(Q'.abs u + Q'.abs v)).eqv ((-(Q'.abs u)) + (-(Q'.abs v))) :=
      Q'.neg_add_eqv (Q'.abs u) (Q'.abs v)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg) ?_
    exact Q'.add_le_add hu hv
  · exact Q'.add_le_add (Q'.le_abs_self u) (Q'.le_abs_self v)

/-- `abs (−x) ≈ abs x`. -/
theorem abs_neg' (x : Q') : (Q'.abs (-x)).eqv (Q'.abs x) := by
  have h1 : Q'.abs (-x) ≤ Q'.abs x := by
    refine Q'.abs_le ?_ ?_
    · exact Q'.neg_le_neg (Q'.le_abs_self x)
    · exact Q'.neg_le_abs x
  have h2 : Q'.abs x ≤ Q'.abs (-x) := by
    refine Q'.abs_le ?_ ?_
    · have := Q'.le_abs_self (-x)
      have hh := Q'.neg_le_neg this
      exact Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.neg_neg_eqv x))
    · have := Q'.neg_le_abs (-x)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv x)) this
  show (Q'.abs (-x)).num * ((Q'.abs x).den : Int) = (Q'.abs x).num * ((Q'.abs (-x)).den : Int)
  exact Int.le_antisymm h1 h2

/-- **The reverse triangle inequality (one-sided):** `|a| ≤ |b| + |a − b|`. -/
theorem abs_le_abs_add_abs_sub (a b : Q') :
    Q'.abs a ≤ Q'.abs b + Q'.abs (a + (-b)) := by
  -- a = b + (a − b), so |a| ≤ |b| + |a − b|.
  have he : a.eqv (b + (a + (-b))) := by
    -- b + (a + −b) ≈ a
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.add_comm_eqv a (-b))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv b (-b) a)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ 0 a (Q'.add_neg_self_eqv b)) ?_
    exact eqv_of_eq' (Q'.zero_add' a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_eqv_congr he)) ?_
  exact abs_add_le' b (a + (-b))

/-- If `−ε ≤ d` and `d ≤ ε` then `|d| ≤ ε`.  (Just `abs_le`.) -/
theorem abs_le_of_bounds {d ε : Q'} (h1 : -ε ≤ d) (h2 : d ≤ ε) : Q'.abs d ≤ ε :=
  Q'.abs_le h1 h2

end Q'

namespace CReal

open Q'

/-! ## 1. `CReal.abs` — index-wise absolute value

`(abs x).approx n := Q'.abs (x.approx n)`.  The Cauchy modulus is INHERITED from
`x`: from `x_m ≤ x_n + ε` and `x_n ≤ x_m + ε` we get `|x_m − x_n| ≤ ε`, and the
reverse triangle `|x_m| ≤ |x_n| + |x_m − x_n| ≤ |x_n| + ε` (both ways). -/

/-- **Constructive-real absolute value**, defined index-wise via `Q'.abs`. -/
def abs (x : CReal) : CReal where
  approx n := Q'.abs (x.approx n)
  cauchy := by
    intro ε hε
    obtain ⟨N, hN⟩ := x.cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN m n hm hn   -- x_m ≤ x_n+ε , x_n ≤ x_m+ε
    -- |x_m − x_n| ≤ ε and |x_n − x_m| ≤ ε
    have hd_mn : Q'.abs (x.approx m + (-(x.approx n))) ≤ ε := by
      refine Q'.abs_le_of_bounds ?_ ?_
      · -- −ε ≤ x_m − x_n  ⟸  x_n ≤ x_m + ε
        have hstep : -ε ≤ (x.approx m) + (-(x.approx n)) := by
          -- x_n ≤ x_m + ε ⟹ −ε ≤ x_m − x_n
          have hh := Q'.add_le_add_right _ _ ((-(x.approx n)) + (-ε)) h2
          -- (x_n) + ((−x_n)+(−ε)) ≤ (x_m+ε) + ((−x_n)+(−ε))
          -- LHS ≈ −ε ; RHS ≈ x_m − x_n
          refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hh ?_)
          · -- −ε ≤ x_n + ((−x_n)+(−ε))
            refine Q'.ge_of_eqv ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.add_assoc_eqv (x.approx n) (-(x.approx n)) (-ε))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0 (-ε) (Q'.add_neg_self_eqv (x.approx n))) ?_
            exact eqv_of_eq' (Q'.zero_add' (-ε))
          · -- (x_m+ε)+((−x_n)+(−ε)) ≤ x_m − x_n  (≈, so ≤)
            refine Q'.le_of_eqv ?_
            -- (x_m+ε)+((−x_n)+(−ε)) ≈ x_m + (−x_n)
            refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x.approx m) ε ((-(x.approx n)) + (-ε))) ?_
            refine Q'.add_eqv_congr_left (x.approx m) _ _ ?_
            -- ε + ((−x_n)+(−ε)) ≈ −x_n
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left ε _ _ (Q'.add_comm_eqv (-(x.approx n)) (-ε))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.add_assoc_eqv ε (-ε) (-(x.approx n)))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0 (-(x.approx n)) (Q'.add_neg_self_eqv ε)) ?_
            exact eqv_of_eq' (Q'.zero_add' (-(x.approx n)))
        exact hstep
      · -- x_m − x_n ≤ ε  ⟸  x_m ≤ x_n + ε
        have hh := Q'.add_le_add_right _ _ (-(x.approx n)) h1
        refine Q'.le_trans' _ _ _ hh ?_
        -- (x_n+ε) + (−x_n) ≤ ε  (≈)
        refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(x.approx n)) (Q'.add_comm_eqv (x.approx n) ε)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε (x.approx n) (-(x.approx n))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ε _ _ (Q'.add_neg_self_eqv (x.approx n))) ?_
        exact eqv_of_eq' (Q'.add_zero' ε)
    -- |x_n − x_m| ≤ ε  (symmetric)
    have hd_nm : Q'.abs ((x.approx n) + (-(x.approx m))) ≤ ε := by
      refine Q'.abs_le_of_bounds ?_ ?_
      · have hstep : -ε ≤ (x.approx n) + (-(x.approx m)) := by
          have hh := Q'.add_le_add_right _ _ ((-(x.approx m)) + (-ε)) h1
          refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hh ?_)
          · refine Q'.ge_of_eqv ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.add_assoc_eqv (x.approx m) (-(x.approx m)) (-ε))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0 (-ε) (Q'.add_neg_self_eqv (x.approx m))) ?_
            exact eqv_of_eq' (Q'.zero_add' (-ε))
          · refine Q'.le_of_eqv ?_
            refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x.approx n) ε ((-(x.approx m)) + (-ε))) ?_
            refine Q'.add_eqv_congr_left (x.approx n) _ _ ?_
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left ε _ _ (Q'.add_comm_eqv (-(x.approx m)) (-ε))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.add_assoc_eqv ε (-ε) (-(x.approx m)))) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0 (-(x.approx m)) (Q'.add_neg_self_eqv ε)) ?_
            exact eqv_of_eq' (Q'.zero_add' (-(x.approx m)))
        exact hstep
      · have hh := Q'.add_le_add_right _ _ (-(x.approx m)) h2
        refine Q'.le_trans' _ _ _ hh ?_
        refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(x.approx m)) (Q'.add_comm_eqv (x.approx m) ε)) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε (x.approx m) (-(x.approx m))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ε _ _ (Q'.add_neg_self_eqv (x.approx m))) ?_
        exact eqv_of_eq' (Q'.add_zero' ε)
    -- |x_m| ≤ |x_n| + ε  and  |x_n| ≤ |x_m| + ε
    refine ⟨?_, ?_⟩
    · -- |x_m| ≤ |x_n| + |x_m − x_n| ≤ |x_n| + ε
      refine Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub (x.approx m) (x.approx n)) ?_
      exact Q'.add_le_add_left _ _ ε hd_mn
    · refine Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub (x.approx n) (x.approx m)) ?_
      exact Q'.add_le_add_left _ _ ε hd_nm

@[simp] theorem abs_approx (x : CReal) (n : Nat) :
    (abs x).approx n = Q'.abs (x.approx n) := rfl

/-- `abs (ofQ' q) = ofQ' (Q'.abs q)`. -/
theorem abs_ofQ' (q : Q') : abs (ofQ' q) = ofQ' (Q'.abs q) := rfl

/-! ## 2. `abs` respects the `Equiv` setoid

If `x ≃ y` then `|x| ≃ |y|`, through the reverse-triangle bound `||x_n|−|y_n|| ≤
|x_n − y_n|` past the `Equiv` modulus. -/

/-- **`abs` is `Equiv`-congruent**: `Equiv x y → Equiv (abs x) (abs y)`. -/
theorem abs_equiv_congr {x y : CReal} (h : CReal.Equiv x y) :
    CReal.Equiv (abs x) (abs y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn   -- x_n ≤ y_n+ε , y_n ≤ x_n+ε
  -- |x_n − y_n| ≤ ε
  have hxy : Q'.abs ((x.approx n) + (-(y.approx n))) ≤ ε := by
    refine Q'.abs_le_of_bounds ?_ ?_
    · -- −ε ≤ x_n − y_n  ⟸  y_n ≤ x_n + ε
      have hh := Q'.add_le_add_right _ _ ((-(y.approx n)) + (-ε)) h2
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hh ?_)
      · refine Q'.ge_of_eqv ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (y.approx n) (-(y.approx n)) (-ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (-ε) (Q'.add_neg_self_eqv (y.approx n))) ?_
        exact eqv_of_eq' (Q'.zero_add' (-ε))
      · refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x.approx n) ε ((-(y.approx n)) + (-ε))) ?_
        refine Q'.add_eqv_congr_left (x.approx n) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left ε _ _ (Q'.add_comm_eqv (-(y.approx n)) (-ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv ε (-ε) (-(y.approx n)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (-(y.approx n)) (Q'.add_neg_self_eqv ε)) ?_
        exact eqv_of_eq' (Q'.zero_add' (-(y.approx n)))
    · have hh := Q'.add_le_add_right _ _ (-(y.approx n)) h1
      refine Q'.le_trans' _ _ _ hh ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(y.approx n)) (Q'.add_comm_eqv (y.approx n) ε)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε (y.approx n) (-(y.approx n))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ε _ _ (Q'.add_neg_self_eqv (y.approx n))) ?_
      exact eqv_of_eq' (Q'.add_zero' ε)
  have hyx : Q'.abs ((y.approx n) + (-(x.approx n))) ≤ ε := by
    refine Q'.abs_le_of_bounds ?_ ?_
    · have hh := Q'.add_le_add_right _ _ ((-(x.approx n)) + (-ε)) h1
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hh ?_)
      · refine Q'.ge_of_eqv ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (x.approx n) (-(x.approx n)) (-ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (-ε) (Q'.add_neg_self_eqv (x.approx n))) ?_
        exact eqv_of_eq' (Q'.zero_add' (-ε))
      · refine Q'.le_of_eqv ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (y.approx n) ε ((-(x.approx n)) + (-ε))) ?_
        refine Q'.add_eqv_congr_left (y.approx n) _ _ ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left ε _ _ (Q'.add_comm_eqv (-(x.approx n)) (-ε))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv ε (-ε) (-(x.approx n)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ 0 (-(x.approx n)) (Q'.add_neg_self_eqv ε)) ?_
        exact eqv_of_eq' (Q'.zero_add' (-(x.approx n)))
    · have hh := Q'.add_le_add_right _ _ (-(x.approx n)) h2
      refine Q'.le_trans' _ _ _ hh ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (-(x.approx n)) (Q'.add_comm_eqv (x.approx n) ε)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε (x.approx n) (-(x.approx n))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ε _ _ (Q'.add_neg_self_eqv (x.approx n))) ?_
      exact eqv_of_eq' (Q'.add_zero' ε)
  -- |x_n| ≤ |y_n| + ε and |y_n| ≤ |x_n| + ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub (x.approx n) (y.approx n)) ?_
    exact Q'.add_le_add_left _ _ ε hxy
  · refine Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub (y.approx n) (x.approx n)) ?_
    exact Q'.add_le_add_left _ _ ε hyx

/-! ## 3. The infinitesimal lemma (CoRN `AbsIR_approach_zero`)

If `|x|`'s limit is `≤ ε` for EVERY rational `ε > 0` — phrased as
`CReal.leRat (abs x) ε` (the regularity-free eventual bound `|x|_n ≤ ε + δ`) —
then `x ≃ 0`.  The `abs`-approx is `Q'.abs (x_n) ≥ 0`, so `−ε ≤ x_n ≤ ε`
eventually, giving the two-sided `Equiv` tolerance directly. -/

/-- **THE INFINITESIMAL LEMMA.**  If for every rational `ε > 0` the limit of `|x|`
is `≤ ε` (`CReal.leRat (abs x) ε`), then `x ≃ 0` (`CReal.Equiv x czero`).
No classical trichotomy: routes entirely through the all-rational-ε form. -/
theorem eqv_zero_of_abs_le_all_pos {x : CReal}
    (h : ∀ ε : Q', (0 : Q') < ε → CReal.leRat (abs x) ε) :
    CReal.Equiv x czero := by
  intro ε hε
  -- work at ε' = (1/2)·ε, get an eventual bound |x_n| ≤ ε' + ε' = ε.
  have hε' : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  -- leRat (abs x) ε' gives: ∀ tol>0, eventually |x_n| ≤ ε' + tol.  Use tol = ε'.
  obtain ⟨N, hN⟩ := h (HalfPow.half * ε) hε' (HalfPow.half * ε) hε'
  refine ⟨N, fun n hn => ?_⟩
  have hb : Q'.abs (x.approx n) ≤ HalfPow.half * ε + HalfPow.half * ε := hN n hn
  have hbε : Q'.abs (x.approx n) ≤ ε :=
    Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (ExpNeg.two_halves ε))
  -- czero.approx n = 0.  Need x_n ≤ 0 + ε and 0 ≤ x_n + ε.
  refine ⟨?_, ?_⟩
  · -- x_n ≤ czero_n + ε = 0 + ε
    show x.approx n ≤ (0 : Q') + ε
    refine Q'.le_trans' _ _ _ (Q'.le_abs_self (x.approx n)) ?_
    refine Q'.le_trans' _ _ _ hbε ?_
    exact Q'.ge_of_eqv (eqv_of_eq' (Q'.zero_add' ε))
  · -- czero_n ≤ x_n + ε, i.e. 0 ≤ x_n + ε  ⟸  −ε ≤ x_n  ⟸  −|x_n| ≤ x_n and −ε ≤ −|x_n|
    show (0 : Q') ≤ x.approx n + ε
    -- −ε ≤ x_n : −ε ≤ −|x_n| ≤ x_n.
    have hneg : -ε ≤ x.approx n := by
      have h1 : -ε ≤ -(Q'.abs (x.approx n)) := Q'.neg_le_neg hbε
      -- −|x_n| ≤ x_n : from neg_le_abs (−x_n): −(−x_n) ≤ |−x_n| ≈ |x_n|, then −|x_n| ≤ x_n.
      have h2 : -(Q'.abs (x.approx n)) ≤ x.approx n := by
        -- neg_le_abs (x_n) : −x_n ≤ |x_n| ; negate: −|x_n| ≤ −(−x_n) ≈ x_n.
        have := Q'.neg_le_neg (Q'.neg_le_abs (x.approx n))   -- −|x_n| ≤ −(−x_n)
        exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv (x.approx n)))
      exact Q'.le_trans' _ _ _ h1 h2
    -- 0 = −ε + ε ≤ x_n + ε
    have hh := Q'.add_le_add_right _ _ ε hneg
    refine Q'.le_trans' _ _ _ ?_ hh
    exact Q'.ge_of_eqv (Q'.neg_add_self_eqv ε)

/-! ## 4. Limit-of-equal-sequences (uniqueness of limits)

A `CReal`-sequence `s : Nat → CReal` **converges to** `L : CReal` with modulus
`M : Q' → Nat` if for every `ε > 0`, every `N ≥ M ε` and every approximation index
`n`, the `N`-th term's `n`-th approximation is within `ε` of `L`'s `n`-th
approximation.  (We phrase convergence approx-wise / two-sided, matching `Equiv`.) -/

/-- A `CReal`-valued sequence `s` **converges to** `L`: for every `ε > 0` there is
a threshold stage `Nstage` such that for EVERY term index `N ≥ Nstage` the term
`s N` is two-sided `ε`-close to `L` eventually in the approximation index.  The
stage is `∃`-quantified (a `Prop`) — matching the `CReal.cauchy` field — so that
`convergesTo_self` is derivable from a `CReal`'s own (Prop-level) Cauchy modulus
WITHOUT choice.  Making the bound hold for ALL `N` past the stage (not just the
threshold term) is the standard definition and is what makes limits unique. -/
def ConvergesTo (s : Nat → CReal) (L : CReal) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
    ∃ Napx : Nat, ∀ n : Nat, Napx ≤ n →
      (s N).approx n ≤ L.approx n + ε ∧ L.approx n ≤ (s N).approx n + ε

/-- **Every `CReal` is the limit of the constant sequence of its own
approximations.**  `ConvergesTo (fun N => ofQ' (L.approx N)) L`, with the
convergence stage = `L`'s own Cauchy modulus.  This is the canonical realisation
that turns a `Q'`-valued partial-sum sequence (lifted by `ofQ'`) into a
`ConvergesTo` witness for the `CReal` it defines — the engine input
`Equiv_of_limit_of_equal` consumes.  Proof: at any term `K ≥ N(ε)`,
`(ofQ' (L.approx K)).approx n = L.approx K`, and `L`'s Cauchy bound gives
`|L.approx K − L.approx n| ≤ ε` for all `n ≥ N(ε)`.  Derived from the Prop-level
`cauchy` field — NO `Classical.choice`. -/
theorem convergesTo_self (L : CReal) : ConvergesTo (fun N => ofQ' (L.approx N)) L := by
  intro ε hε
  obtain ⟨Nc, hNc⟩ := L.cauchy ε hε
  refine ⟨Nc, fun N hN => ⟨Nc, fun n hn => ?_⟩⟩
  -- (ofQ' (L.approx N)).approx n = L.approx N ; bound by L's Cauchy at (N, n).
  obtain ⟨h1, h2⟩ := hNc N n hN hn   -- L.approx N ≤ L.approx n + ε , L.approx n ≤ L.approx N + ε
  exact ⟨h1, h2⟩

/-- **LIMIT OF EQUAL SEQUENCES = uniqueness of limits.**  If `aSeq N ≃ bSeq N` for
every `N`, and `aSeq` converges to `A`, `bSeq` converges to `B` (with explicit
moduli, `ConvergesTo`), then `A ≃ B`.

Proof: pick `ε`; work at `q = (1/4)ε`.  Take the COMMON stage `N = max(stageA q,
stageB q)`, so BOTH convergence bounds apply to the SAME term index `N`.  At any
approximation index `n` past the three eventual stages (A's, B's, and the termwise
`Equiv (aSeq N) (bSeq N)`'s):

    A_n ≤ aSeq(N)_n + q          (A's convergence, reversed)
        ≤ (bSeq(N)_n + q) + q    (termwise equality aSeq N ≃ bSeq N)
        ≤ ((B_n + q) + q) + q    (B's convergence)
    so A_n ≤ B_n + (q+q+q+q) [pad one q] = B_n + ε, and symmetrically. -/
theorem Equiv_of_limit_of_equal {aSeq bSeq : Nat → CReal} {A B : CReal}
    (hterm : ∀ N : Nat, CReal.Equiv (aSeq N) (bSeq N))
    (hA : ConvergesTo aSeq A) (hB : ConvergesTo bSeq B) :
    CReal.Equiv A B := by
  intro ε hε
  let q : Q' := HalfPow.half * (HalfPow.half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  -- the two convergence thresholds at scale q
  obtain ⟨NstA, hstA⟩ := hA q hqpos
  obtain ⟨NstB, hstB⟩ := hB q hqpos
  -- the common term index
  let N : Nat := max NstA NstB
  have hNA : NstA ≤ N := Nat.le_max_left _ _
  have hNB : NstB ≤ N := Nat.le_max_right _ _
  -- convergence eventual-approx witnesses at the common term N
  obtain ⟨NapxA, hclA⟩ := hstA N hNA   -- aSeq N vs A
  obtain ⟨NapxB, hclB⟩ := hstB N hNB   -- bSeq N vs B
  -- termwise equality aSeq N ≃ bSeq N, at tolerance q
  obtain ⟨NeqN, heqN⟩ := hterm N q hqpos
  refine ⟨max (max NapxA NapxB) NeqN, fun n hn => ?_⟩
  have hnA : NapxA ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hn
  have hnB : NapxB ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hn
  have hnE : NeqN ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hA1, hA2⟩ := hclA n hnA   -- aSeqN_n ≤ A_n+q , A_n ≤ aSeqN_n+q
  obtain ⟨hB1, hB2⟩ := hclB n hnB   -- bSeqN_n ≤ B_n+q , B_n ≤ bSeqN_n+q
  obtain ⟨hE1, hE2⟩ := heqN n hnE   -- aSeqN_n ≤ bSeqN_n+q , bSeqN_n ≤ aSeqN_n+q
  -- Helper: chaining `u ≤ v+q`, `v ≤ w+q`, `w ≤ z+q` ⟹ `u ≤ z + ε`.
  have chain3 : ∀ u v w z : Q', u ≤ v + q → v ≤ w + q → w ≤ z + q → u ≤ z + ε := by
    intro u v w z huv hvw hwz
    -- u ≤ v+q ≤ (w+q)+q ≤ ((z+q)+q)+q ; and ((z+q)+q)+q ≤ z+ε since 3q ≤ ε.
    have s1 : u ≤ (w + q) + q := Q'.le_trans' _ _ _ huv (Q'.add_le_add_right _ _ q hvw)
    have s2 : u ≤ ((z + q) + q) + q :=
      Q'.le_trans' _ _ _ s1 (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hwz))
    refine Q'.le_trans' _ _ _ s2 ?_
    -- ((z+q)+q)+q ≤ z + ε.  z + (q+q+q) ≤ z + (q+q+q+q) = z + ε.
    -- ((z+q)+q)+q ≈ z + ((q+q)+q) ≤ z + (((q+q)+q)+q) = z + ε.
    have hreassoc : (((z + q) + q) + q).eqv (z + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (z + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z q (q + q)) ?_
      exact Q'.add_eqv_congr_left z _ _ (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    -- z + ((q+q)+q) ≤ z + (((q+q)+q)+q)  since 0 ≤ q
    have hpad : z + ((q + q) + q) ≤ z + (((q + q) + q) + q) :=
      Q'.add_le_add_left _ _ _ (Q'.add_le_self_of_nonneg ((q + q) + q) q (Q'.le_of_lt hqpos))
    refine Q'.le_trans' _ _ _ hpad ?_
    -- z + (((q+q)+q)+q) ≈ z + ε   since ((q+q)+q)+q ≈ ε  (= 4·(¼ε))
    refine Q'.le_of_eqv (Q'.add_eqv_congr_left z _ _ ?_)
    -- ((q+q)+q)+q ≈ ε with q = ½(½ε): (q+q) ≈ ½ε, +(q+q) ≈ ε.
    have hqq : (q + q).eqv (HalfPow.half * ε) :=
      ExpNeg.two_halves (HalfPow.half * ε)
    -- ((q+q)+q)+q ≈ (q+q)+(q+q) ≈ ½ε+½ε ≈ ε
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (q + q) q q) ?_
    refine Q'.eqv_trans _ _ _ (add_eqv_congr' hqq hqq) ?_
    exact ExpNeg.two_halves ε
  refine ⟨?_, ?_⟩
  · -- A_n ≤ B_n + ε : A ≤ aSeqN+q, aSeqN ≤ bSeqN+q, bSeqN ≤ B+q
    exact chain3 (A.approx n) ((aSeq N).approx n) ((bSeq N).approx n) (B.approx n) hA2 hE1 hB1
  · -- B_n ≤ A_n + ε : B ≤ bSeqN+q, bSeqN ≤ aSeqN+q, aSeqN ≤ A+q
    exact chain3 (B.approx n) ((bSeq N).approx n) ((aSeq N).approx n) (A.approx n) hB2 hE2 hA1

/-! ## 5. CReal-level uniqueness from the infinitesimal lemma (Route-B core)

The infinitesimal lemma plus the `Equiv ↔ (difference ≃ 0)` bridge give a clean
CReal-level uniqueness: two `CReal`s whose DIFFERENCE has limit `≤ ε` for every
rational `ε > 0` are `Equiv`.  This is the CReal upgrade the differentiated-JTP
route names for converting a `Q'`-rational derivative-value equality into the
genuine `CReal.Equiv` of the two derivative realisations: any two `CReal`s that are
both within every `ε` of each other coincide. -/

/-- **`Equiv` from the difference being infinitesimal.**  If `add D₁ (neg D₂)` (the
`CReal` difference) is `≃ 0` (`Equiv … czero`), then `D₁ ≃ D₂`.  The two are
inter-derivable since `(D₁ − D₂)_n = D₁_n − D₂_n` and `czero_n = 0`, so the
two-sided tolerance transfers directly. -/
theorem Equiv_of_sub_eqv_zero {D₁ D₂ : CReal}
    (h : CReal.Equiv (add D₁ (neg D₂)) czero) : CReal.Equiv D₁ D₂ := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  -- (add D₁ (neg D₂)).approx n = D₁_n + (−D₂_n) ; czero_n = 0.
  -- h1 : D₁_n + (−D₂_n) ≤ 0 + ε ;  h2 : 0 ≤ (D₁_n + (−D₂_n)) + ε.
  have h1' : (D₁.approx n) + (-(D₂.approx n)) ≤ (0 : Q') + ε := h1
  have h2' : (0 : Q') ≤ ((D₁.approx n) + (-(D₂.approx n))) + ε := h2
  refine ⟨?_, ?_⟩
  · -- D₁_n ≤ D₂_n + ε : from (D₁_n − D₂_n) ≤ ε, add D₂_n.
    have hd : (D₁.approx n) + (-(D₂.approx n)) ≤ ε :=
      Q'.le_trans' _ _ _ h1' (Q'.le_of_eqv (eqv_of_eq' (Q'.zero_add' ε)))
    have hh := Q'.add_le_add_right _ _ (D₂.approx n) hd   -- (D₁−D₂)+D₂ ≤ ε+D₂
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv (Q'.add_comm_eqv ε (D₂.approx n))))
    -- D₁_n ≤ (D₁_n + (−D₂_n)) + D₂_n
    refine Q'.ge_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (D₁.approx n) (-(D₂.approx n)) (D₂.approx n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (D₁.approx n) _ _ (Q'.neg_add_self_eqv (D₂.approx n))) ?_
    exact eqv_of_eq' (Q'.add_zero' (D₁.approx n))
  · -- D₂_n ≤ D₁_n + ε : from −ε ≤ D₁_n − D₂_n  (i.e. 0 ≤ (D₁−D₂)+ε), add D₂_n.
    -- D₂_n ≤ D₁_n + ε ⟺ 0 ≤ D₁_n + ε − D₂_n = (D₁_n − D₂_n) + ε.
    have hh := Q'.add_le_add_right _ _ (D₂.approx n) h2'   -- 0+D₂_n ≤ ((D₁−D₂)+ε)+D₂_n
    refine Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (eqv_of_eq' (Q'.zero_add' (D₂.approx n)))) hh) ?_
    -- ((D₁_n − D₂_n) + ε) + D₂_n ≈ D₁_n + ε
    refine Q'.le_of_eqv ?_
    -- ((D₁ + −D₂) + ε) + D₂ ≈ D₁ + ε
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (D₂.approx n) (Q'.add_assoc_eqv (D₁.approx n) (-(D₂.approx n)) ε)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (D₁.approx n) ((-(D₂.approx n)) + ε) (D₂.approx n)) ?_
    refine Q'.add_eqv_congr_left (D₁.approx n) _ _ ?_
    -- ((−D₂)+ε)+D₂ ≈ ε
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (D₂.approx n) (Q'.add_comm_eqv (-(D₂.approx n)) ε)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ε (-(D₂.approx n)) (D₂.approx n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left ε _ _ (Q'.neg_add_self_eqv (D₂.approx n))) ?_
    exact eqv_of_eq' (Q'.add_zero' ε)

/-- **CReal-LEVEL UNIQUENESS (the Route-B core).**  Two `CReal`s `D₁`, `D₂` whose
difference is infinitesimal — `|D₁ − D₂|`'s limit is `≤ ε` for EVERY rational
`ε > 0` (`∀ ε>0, leRat (abs (add D₁ (neg D₂))) ε`) — are `Equiv`.  This is the
CReal upgrade of the `Q'`-Archimedean uniqueness: composes the infinitesimal lemma
(`eqv_zero_of_abs_le_all_pos`) with the difference-to-`Equiv` bridge.  It is the
genuine "cancellation by all-ε" that the differentiated-JTP realisation needs to
turn a derivative-value equality into the `CReal.Equiv` of the two realisations. -/
theorem Equiv_of_abs_sub_le_all_pos {D₁ D₂ : CReal}
    (h : ∀ ε : Q', (0 : Q') < ε → CReal.leRat (abs (add D₁ (neg D₂))) ε) :
    CReal.Equiv D₁ D₂ :=
  Equiv_of_sub_eqv_zero (eqv_zero_of_abs_le_all_pos h)

/-- **Limit of equal sequences, applied to two `CReal`s via their own
approximations.**  If two `CReal`s `A`, `B` have `Equiv`-equal approximation
sequences term by term (`∀ N, Equiv (ofQ' (A.approx N)) (ofQ' (B.approx N))`),
then `Equiv A B`.  This packages `Equiv_of_limit_of_equal` with `convergesTo_self`
on both sides, so the user only supplies the termwise `Equiv` of the lifted
partials.  The genuinely useful corollary for lifting a FINITE matched-truncation
identity (e.g. the Gauss q-binomial `qProd N ≈ gaussSum N`) to the equality of the
two `CReal` limits, even when those limits converge at different RATES (the rates
never enter — only the matched-at-each-`N` equality does). -/
theorem Equiv_of_lifted_approx_equal {A B : CReal}
    (hterm : ∀ N : Nat, CReal.Equiv (ofQ' (A.approx N)) (ofQ' (B.approx N))) :
    CReal.Equiv A B :=
  Equiv_of_limit_of_equal hterm (convergesTo_self A) (convergesTo_self B)

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.Q'.abs_eqv_congr
#print axioms ConstructiveReals.Q'.abs_add_le'
#print axioms ConstructiveReals.Q'.abs_neg'
#print axioms ConstructiveReals.Q'.abs_le_abs_add_abs_sub
#print axioms ConstructiveReals.CReal.abs
#print axioms ConstructiveReals.CReal.abs_ofQ'
#print axioms ConstructiveReals.CReal.abs_equiv_congr
#print axioms ConstructiveReals.CReal.eqv_zero_of_abs_le_all_pos
#print axioms ConstructiveReals.CReal.convergesTo_self
#print axioms ConstructiveReals.CReal.Equiv_of_sub_eqv_zero
#print axioms ConstructiveReals.CReal.Equiv_of_abs_sub_le_all_pos
#print axioms ConstructiveReals.CReal.Equiv_of_limit_of_equal
#print axioms ConstructiveReals.CReal.Equiv_of_lifted_approx_equal
