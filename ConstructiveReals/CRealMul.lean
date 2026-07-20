/-
`CReal.mul` — constructive multiplication of constructive reals, intuitionistic
(axiom-clean, no `Classical.choice`).

Design that stays choice-free: the product is defined **pointwise**,
`(a*b).approx n := a.approx n * b.approx n`, which is computable from the
`approx` data alone — the (Prop-level, existential) Cauchy moduli of `a`, `b`
are used only inside the `cauchy` *proof* (itself a `Prop`, where destructing
existentials is fine).

The Cauchy estimate is the two-step bound
`a_p b_p ≤ a_q b_p + B·δ ≤ a_q b_q + 2B·δ` (vary one factor at a time), using
`AbsQ.mul_le_of_bounds` for each step and a division-free choice of `δ`.

This module first proves the `Q'` algebra helpers it needs (negation of a sum,
add–sub cancellation, right distributivity, sub-bounds, a division-free
`∃δ, B·δ+B·δ ≤ ε`), then boundedness, then `CReal.mul`.

# Axiom-gate (see README: axiom policy)

`[propext]` only (and `Quot.sound` where `omega`/`Nat` enter).  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.AbsQ
import ConstructiveReals.Reals
import ConstructiveReals.RatNat

namespace ConstructiveReals

namespace Q'

/-- `−(a + b) ≃ −a + −b`. -/
theorem neg_add_eqv (a b : Q') : (-(a + b)).eqv (-a + -b) := by
  show (-(a + b)).num * ((-a + -b).den : Int) = (-a + -b).num * ((-(a + b)).den : Int)
  have hLn : (-(a + b)).num = -(a.num * (b.den : Int) + b.num * (a.den : Int)) := rfl
  have hRn : (-a + -b).num = (-a.num) * (b.den : Int) + (-b.num) * (a.den : Int) := rfl
  rw [hLn, hRn,
      show ((-a + -b).den : Int) = ((a + b).den : Int) from rfl,
      show ((-(a + b)).den : Int) = ((a + b).den : Int) from rfl,
      add_den_cast a b]
  simp only [Int.neg_mul, Int.add_mul, Int.neg_add]

/-- `a + −a ≃ 0`. -/
theorem add_neg_self_eqv (a : Q') : (a + -a).eqv 0 :=
  eqv_trans (a + -a) (-a + a) 0 (add_comm_eqv a (-a)) (neg_add_self_eqv a)

/-- `x ≃ y + (x − y)` (add–sub cancellation; `x − y = x + −y`). -/
theorem add_sub_cancel_eqv (x y : Q') : x.eqv (y + (x + -y)) := by
  have h2 : (y + (x + -y)).eqv (y + (-y + x)) :=
    add_eqv_congr_left y (x + -y) (-y + x) (add_comm_eqv x (-y))
  have h3 : (y + (-y + x)).eqv ((y + -y) + x) := eqv_symm (add_assoc_eqv y (-y) x)
  have h4 : ((y + -y) + x).eqv ((0 : Q') + x) :=
    add_eqv_congr_right (y + -y) 0 x (add_neg_self_eqv y)
  rw [zero_add'] at h4
  exact eqv_symm
    (eqv_trans (y + (x + -y)) (y + (-y + x)) x h2
      (eqv_trans (y + (-y + x)) ((y + -y) + x) x h3 h4))

/-- Right distributivity `(a + b)·c ≃ a·c + b·c` (from `mul_add` + commutativity). -/
theorem add_mul_eqv (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) := by
  have h1 : ((a + b) * c).eqv (c * (a + b)) := mul_comm_eqv (a + b) c
  have h2 : (c * (a + b)).eqv (c * a + c * b) := mul_add_eqv c a b
  have h3 : (c * a + c * b).eqv (a * c + c * b) :=
    add_eqv_congr_right (c * a) (a * c) (c * b) (mul_comm_eqv c a)
  have h4 : (a * c + c * b).eqv (a * c + b * c) :=
    add_eqv_congr_left (a * c) (c * b) (b * c) (mul_comm_eqv c b)
  exact eqv_trans ((a + b) * c) (c * (a + b)) (a * c + b * c) h1
    (eqv_trans (c * (a + b)) (c * a + c * b) (a * c + b * c) h2
      (eqv_trans (c * a + c * b) (a * c + c * b) (a * c + b * c) h3 h4))

/-- From `a ≤ b + c`, get `a − b ≤ c`. -/
theorem sub_le_of_le_add {a b c : Q'} (h : a ≤ b + c) : a + -b ≤ c := by
  have h1 : a + -b ≤ (b + c) + -b := add_le_add_right a (b + c) (-b) h
  have h2 : ((b + c) + -b).eqv c := by
    have e1 : ((b + c) + -b).eqv ((c + b) + -b) :=
      add_eqv_congr_right (b + c) (c + b) (-b) (add_comm_eqv b c)
    have e2 : ((c + b) + -b).eqv (c + (b + -b)) := add_assoc_eqv c b (-b)
    have e3 : (c + (b + -b)).eqv (c + 0) := add_eqv_congr_left c (b + -b) 0 (add_neg_self_eqv b)
    have e4 : (c + (0 : Q')) = c := add_zero' c
    have e3' : (c + (b + -b)).eqv c := by rw [e4] at e3; exact e3
    exact eqv_trans ((b + c) + -b) ((c + b) + -b) c e1
      (eqv_trans ((c + b) + -b) (c + (b + -b)) c e2 e3')
  exact le_trans' (a + -b) ((b + c) + -b) c h1 (le_of_eqv h2)

/-- From `a ≤ b + c`, get `−c ≤ b + −a`. -/
theorem neg_le_sub_of_le_add {a b c : Q'} (h : a ≤ b + c) : -c ≤ b + -a := by
  have h1 : a + -b ≤ c := sub_le_of_le_add h
  have h2 : -c ≤ -(a + -b) := neg_le_neg h1
  have h3 : (-(a + -b)).eqv (-a + -(-b)) := neg_add_eqv a (-b)
  have h4 : (-a + -(-b)).eqv (-a + b) := add_eqv_congr_left (-a) (-(-b)) b (neg_neg_eqv b)
  have h5 : (-a + b).eqv (b + -a) := add_comm_eqv (-a) b
  exact le_trans' (-c) (-(a + -b)) (b + -a) h2
    (le_of_eqv
      (eqv_trans (-(a + -b)) (-a + -(-b)) (b + -a) h3
        (eqv_trans (-a + -(-b)) (-a + b) (b + -a) h4 h5)))

end Q'

/-! ## Boundedness of a `CReal` past its `ε=1` cutoff -/

namespace CReal

open Q'

/-- A `CReal` is bounded past the stage `N` where its terms are within `1`:
`∃ N B, 0 ≤ B ∧ ∀ n ≥ N, −B ≤ a_n ≤ B`, with `B = |a_N| + 1`.  (No global
bound — only the post-cutoff range, which is all `CReal.mul` needs.) -/
theorem localBound (a : CReal) : ∃ N : Nat, ∃ B : Q', (0 : Q') ≤ B ∧
    ∀ n, N ≤ n → -B ≤ a.approx n ∧ a.approx n ≤ B := by
  obtain ⟨N, hN⟩ := a.cauchy 1 (by decide)
  refine ⟨N, Q'.abs (a.approx N) + 1, ?_, ?_⟩
  · exact le_trans' 0 (Q'.abs (a.approx N)) (Q'.abs (a.approx N) + 1)
      (Q'.abs_nonneg _) (Q'.add_le_self_of_nonneg _ 1 (by decide))
  · intro n hn
    obtain ⟨hub, hlb⟩ := hN n N hn (Nat.le_refl N)
    refine ⟨?_, ?_⟩
    · -- −(|v|+1) ≤ a_n
      have hv : -(Q'.abs (a.approx N)) ≤ a.approx N :=
        le_trans' (-(Q'.abs (a.approx N))) (-(-(a.approx N))) (a.approx N)
          (Q'.neg_le_neg (Q'.neg_le_abs (a.approx N)))
          (Q'.le_of_eqv (Q'.neg_neg_eqv (a.approx N)))
      have h1 : -(Q'.abs (a.approx N)) ≤ a.approx n + 1 := le_trans' _ _ _ hv hlb
      have h2 : -(Q'.abs (a.approx N)) + -1 ≤ (a.approx n + 1) + -1 :=
        Q'.add_le_add_right _ _ (-1) h1
      have h3 : ((a.approx n + 1) + -1).eqv (a.approx n) := by
        have e1 := Q'.add_assoc_eqv (a.approx n) 1 (-1)
        have e2 : (a.approx n + (1 + -1)).eqv (a.approx n + 0) :=
          Q'.add_eqv_congr_left (a.approx n) (1 + -1) 0 (Q'.add_neg_self_eqv 1)
        rw [Q'.add_zero' (a.approx n)] at e2
        exact Q'.eqv_trans _ _ _ e1 e2
      have h4 : -(Q'.abs (a.approx N)) + -1 ≤ a.approx n := le_trans' _ _ _ h2 (Q'.le_of_eqv h3)
      exact le_trans' (-(Q'.abs (a.approx N) + 1)) (-(Q'.abs (a.approx N)) + -1) (a.approx n)
        (Q'.le_of_eqv (Q'.neg_add_eqv (Q'.abs (a.approx N)) 1)) h4
    · -- a_n ≤ |v| + 1
      exact le_trans' (a.approx n) (a.approx N + 1) (Q'.abs (a.approx N) + 1) hub
        (Q'.add_le_add_right (a.approx N) (Q'.abs (a.approx N)) 1 (Q'.le_abs_self _))

/-! ## A division-free product modulus -/

theorem pos_of_num_pos {q : Q'} (h : 0 < q.num) : (0 : Q') < q := by
  show (0 : Int) * (q.den : Int) < q.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]; exact h

theorem num_pos_of_pos {q : Q'} (h : (0 : Q') < q) : 0 < q.num := by
  have h' : (0 : Int) * (q.den : Int) < q.num * (1 : Int) := h
  rw [Int.zero_mul, Int.mul_one] at h'; exact h'

theorem ofNat_le_ofNat {n m : Nat} (h : n ≤ m) : (Q'.ofNat n) ≤ Q'.ofNat m := by
  show (Int.ofNat n) * (1 : Int) ≤ (Int.ofNat m) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]; exact Int.ofNat_le.mpr h

/-- `(ofNat M)·(ε.num / (ε.den·M)) ≃ ε` — the `M`-cancellation. -/
theorem ofNatMul_mkPos_eqv (M : Nat) (ε : Q') (hden : 0 < ε.den * M) :
    (Q'.ofNat M * Q'.mkPos ε.num (ε.den * M) hden).eqv ε := by
  show ((M : Int) * ε.num) * (ε.den : Int)
     = ε.num * ((Q'.ofNat M * Q'.mkPos ε.num (ε.den * M) hden).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den,
      show ((Q'.ofNat M).den : Int) = 1 from rfl, Int.one_mul, Int.natCast_mul]
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

/-- **Division-free product modulus**: `∃ δ > 0, B·δ ≤ ε` (`B ≥ 0`, `ε > 0`). -/
theorem exists_mul_le {B ε : Q'} (hB : (0 : Q') ≤ B) (hε : (0 : Q') < ε) :
    ∃ δ : Q', (0 : Q') < δ ∧ B * δ ≤ ε := by
  have hεn : 0 < ε.num := num_pos_of_pos hε
  obtain ⟨M, hMdef⟩ : ∃ M, B.num.toNat + 1 = M := ⟨_, rfl⟩
  have hMpos : 0 < M := by omega
  have hden : 0 < ε.den * M := Nat.mul_pos ε.den_pos hMpos
  have hδpos : (0 : Q') < Q'.mkPos ε.num (ε.den * M) hden :=
    pos_of_num_pos (by rw [Q'.mkPos_num]; exact hεn)
  refine ⟨Q'.mkPos ε.num (ε.den * M) hden, hδpos, ?_⟩
  have hBM : B ≤ Q'.ofNat M :=
    le_trans' B (Q'.ofNat B.num.toNat) (Q'.ofNat M)
      (RatNat.le_ofNat_toNat B hB) (ofNat_le_ofNat (by omega))
  exact le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right B (Q'.ofNat M) _ hBM (Q'.le_of_lt hδpos))
    (Q'.le_of_eqv (ofNatMul_mkPos_eqv M ε hden))

/-! ## `CReal.mul` -/

/-- Pointwise product of constructive reals; Cauchy via the two-step bound
`a_p b_p ≤ a_q b_p + δ·Bb ≤ a_q b_q + δ·Bb + δ·Ba ≤ a_q b_q + ε`. -/
def mul (a b : CReal) : CReal where
  approx n := a.approx n * b.approx n
  cauchy := by
    intro ε hε
    obtain ⟨Na, Ba, hBa, hba⟩ := localBound a
    obtain ⟨Nb, Bb, hBb, hbb⟩ := localBound b
    have hB : (0 : Q') ≤ Ba + Bb :=
      le_trans' 0 Ba (Ba + Bb) hBa (Q'.add_le_self_of_nonneg Ba Bb hBb)
    obtain ⟨δ, hδpos, hδ⟩ := exists_mul_le hB hε
    have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
    obtain ⟨Na', ha'⟩ := a.cauchy δ hδpos
    obtain ⟨Nb', hb'⟩ := b.cauchy δ hδpos
    -- the directional bound, used both ways
    have key : ∀ p q : Nat, Na ≤ p → Nb ≤ p → Na ≤ q → Na' ≤ p → Na' ≤ q →
        Nb' ≤ p → Nb' ≤ q →
        a.approx p * b.approx p ≤ a.approx q * b.approx q + ε := by
      intro p q hpa hpb hqa hpa' hqa' hpb' hqb'
      -- δ-closeness of the two factors
      have hac := ha' p q hpa' hqa'   -- a_p ≤ a_q+δ ∧ a_q ≤ a_p+δ
      have hbc := hb' p q hpb' hqb'   -- b_p ≤ b_q+δ ∧ b_q ≤ b_p+δ
      have hda1 : a.approx p + -a.approx q ≤ δ := Q'.sub_le_of_le_add hac.1
      have hda2 : -δ ≤ a.approx p + -a.approx q := Q'.neg_le_sub_of_le_add hac.2
      have hdb1 : b.approx p + -b.approx q ≤ δ := Q'.sub_le_of_le_add hbc.1
      have hdb2 : -δ ≤ b.approx p + -b.approx q := Q'.neg_le_sub_of_le_add hbc.2
      -- factor bounds
      have hbp := hbb p hpb   -- -Bb ≤ b_p ∧ b_p ≤ Bb
      have haq := hba q hqa   -- -Ba ≤ a_q ∧ a_q ≤ Ba
      -- Step A: a_p b_p ≤ a_q b_p + δ*Bb
      have termA : (a.approx p + -a.approx q) * b.approx p ≤ δ * Bb :=
        Q'.mul_le_of_bounds hδnn hBb hda2 hda1 hbp.1 hbp.2
      have idA : (a.approx p * b.approx p).eqv
          (a.approx q * b.approx p + (a.approx p + -a.approx q) * b.approx p) := by
        have e1 := Q'.add_sub_cancel_eqv (a.approx p) (a.approx q)  -- a_p ≃ a_q+(a_p+-a_q)
        have e2 : (a.approx p * b.approx p).eqv
            ((a.approx q + (a.approx p + -a.approx q)) * b.approx p) :=
          Q'.mul_eqv_congr_right (a.approx p) (a.approx q + (a.approx p + -a.approx q))
            (b.approx p) e1
        exact Q'.eqv_trans _ _ _ e2
          (Q'.add_mul_eqv (a.approx q) (a.approx p + -a.approx q) (b.approx p))
      have stepA : a.approx p * b.approx p ≤ a.approx q * b.approx p + δ * Bb :=
        le_trans' _ _ _ (Q'.le_of_eqv idA)
          (Q'.add_le_add_left (a.approx q * b.approx p)
            ((a.approx p + -a.approx q) * b.approx p) (δ * Bb) termA)
      -- Step B: a_q b_p ≤ a_q b_q + δ*Ba
      have termB : (b.approx p + -b.approx q) * a.approx q ≤ δ * Ba :=
        Q'.mul_le_of_bounds hδnn hBa hdb2 hdb1 haq.1 haq.2
      have idB : (a.approx q * b.approx p).eqv
          (a.approx q * b.approx q + (b.approx p + -b.approx q) * a.approx q) := by
        have e1 := Q'.add_sub_cancel_eqv (b.approx p) (b.approx q)  -- b_p ≃ b_q+(b_p+-b_q)
        have e2 : (a.approx q * b.approx p).eqv
            (a.approx q * (b.approx q + (b.approx p + -b.approx q))) :=
          Q'.mul_eqv_congr_left (a.approx q) (b.approx p)
            (b.approx q + (b.approx p + -b.approx q)) e1
        have e3 : (a.approx q * (b.approx q + (b.approx p + -b.approx q))).eqv
            (a.approx q * b.approx q + a.approx q * (b.approx p + -b.approx q)) :=
          Q'.mul_add_eqv (a.approx q) (b.approx q) (b.approx p + -b.approx q)
        have e4 : (a.approx q * (b.approx p + -b.approx q)).eqv
            ((b.approx p + -b.approx q) * a.approx q) :=
          Q'.mul_comm_eqv (a.approx q) (b.approx p + -b.approx q)
        exact Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3
          (Q'.add_eqv_congr_left (a.approx q * b.approx q)
            (a.approx q * (b.approx p + -b.approx q))
            ((b.approx p + -b.approx q) * a.approx q) e4))
      have stepB : a.approx q * b.approx p ≤ a.approx q * b.approx q + δ * Ba :=
        le_trans' _ _ _ (Q'.le_of_eqv idB)
          (Q'.add_le_add_left (a.approx q * b.approx q)
            ((b.approx p + -b.approx q) * a.approx q) (δ * Ba) termB)
      -- combine: a_p b_p ≤ a_q b_q + (δ*Ba + δ*Bb) ≤ a_q b_q + ε
      have hsum : δ * Bb + δ * Ba ≤ ε := by
        have e : (δ * Ba + δ * Bb).eqv ((Ba + Bb) * δ) := by
          have c1 : (δ * Ba + δ * Bb).eqv (δ * (Ba + Bb)) :=
            Q'.eqv_symm (Q'.mul_add_eqv δ Ba Bb)
          exact Q'.eqv_trans _ _ _ c1 (Q'.mul_comm_eqv δ (Ba + Bb))
        have e' : (δ * Bb + δ * Ba).eqv ((Ba + Bb) * δ) :=
          Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (δ * Bb) (δ * Ba)) e
        exact le_trans' _ _ _ (Q'.le_of_eqv e') hδ
      -- a_p b_p ≤ (a_q b_p + δ*Bb) ≤ (a_q b_q + δ*Ba) + δ*Bb = a_q b_q + (δ*Ba + δ*Bb)
      have chain : a.approx p * b.approx p ≤ (a.approx q * b.approx q + δ * Ba) + δ * Bb :=
        le_trans' _ _ _ stepA
          (Q'.add_le_add_right (a.approx q * b.approx p)
            (a.approx q * b.approx q + δ * Ba) (δ * Bb) stepB)
      have reassoc : ((a.approx q * b.approx q + δ * Ba) + δ * Bb).eqv
          (a.approx q * b.approx q + (δ * Bb + δ * Ba)) := by
        have a1 := Q'.add_assoc_eqv (a.approx q * b.approx q) (δ * Ba) (δ * Bb)
        exact Q'.eqv_trans _ _ _ a1
          (Q'.add_eqv_congr_left (a.approx q * b.approx q) (δ * Ba + δ * Bb) (δ * Bb + δ * Ba)
            (Q'.add_comm_eqv (δ * Ba) (δ * Bb)))
      exact le_trans' _ _ _ (le_trans' _ _ _ chain (Q'.le_of_eqv reassoc))
        (Q'.add_le_add_left (a.approx q * b.approx q) (δ * Bb + δ * Ba) ε hsum)
    -- assemble both directions
    refine ⟨max (max Na Nb) (max Na' Nb'), fun p q hp hq => ?_⟩
    have lpa : Na ≤ p := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hp
    have lpb : Nb ≤ p := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hp
    have lpa' : Na' ≤ p := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hp
    have lpb' : Nb' ≤ p := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hp
    have lqa : Na ≤ q := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hq
    have lqb : Nb ≤ q := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hq
    have lqa' : Na' ≤ q := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hq
    have lqb' : Nb' ≤ q := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hq
    exact ⟨key p q lpa lpb lqa lpa' lqa' lpb' lqb',
           key q p lqa lqb lpa lqa' lpa' lqb' lpb'⟩

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates -/

#print axioms ConstructiveReals.CReal.exists_mul_le
#print axioms ConstructiveReals.CReal.mul
#print axioms ConstructiveReals.CReal.localBound
#print axioms ConstructiveReals.Q'.neg_add_eqv
#print axioms ConstructiveReals.Q'.add_sub_cancel_eqv
#print axioms ConstructiveReals.Q'.add_mul_eqv
#print axioms ConstructiveReals.Q'.sub_le_of_le_add
#print axioms ConstructiveReals.Q'.neg_le_sub_of_le_add
