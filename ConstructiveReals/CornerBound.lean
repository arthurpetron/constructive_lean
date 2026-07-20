/-
Product law L3b — the corner vanishes: `corner x m → 0` (Mertens' estimate).

`cornerₘ = Σ_{i<m} aᵢ·(P⁻ₘ − P⁻_{m−i})` (L3a).  Bounding the signed block by the
magnitude block (`block_upper`/`block_lower`) gives `±cornerₘ ≤ cornerAbsₘ` with

    cornerAbsₘ := Σ_{i<m} aᵢ·blockAbs x (m−i) i .

Every product `aᵢ·blockAbs x (m−i) i` lives at total degree `≥ m`, so for `m`
large the whole sum is small.  Concretely, with a global bound `B` on `P⁺` and
`δ` chosen so `(B+B)·δ ≤ ε`, splitting at `K = max(halfRatioCutoff,
termAbsModulus(½δ))`:

  * `i < K`: the block `blockAbs x (m−i) i` starts past the cutoff, so `≤ δ`
    (uniform `expNeg_tail_bound`); the part is `≤ (Σ_{i<K} aᵢ)·δ ≤ B·δ`.
  * `K ≤ i`: the weights sum to `blockAbs x K (m−K) ≤ δ` (a-tail from `K`), the
    blocks are `≤ B`; the part is `≤ δ·B`.

So `cornerAbsₘ ≤ (B+B)·δ ≤ ε` for `m ≥ K + termAbsModulus(½δ)`.

# Axiom-gate (see README: axiom policy)

`[propext]` only, plus `Quot.sound` where `omega`/`Nat` enter.  No `Classical.*`,
no `sorryAx`.
-/

import ConstructiveReals.ProductDecomp
import ConstructiveReals.ExpPos
import ConstructiveReals.CRealMulMono

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.RationalTail
open ConstructiveReals.ExpNeg
open ConstructiveReals.HalfPow
open ConstructiveReals.RatNat

/-! ## finSum infrastructure -/

/-- Range-restricted monotonicity: agreement on `i < n` suffices. -/
theorem finSum_le_lt (f g : QSeq) :
    ∀ n, (∀ i, i < n → f i ≤ g i) → finSum f n ≤ finSum g n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h =>
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right (finSum f n) (finSum g n) (f n)
          (finSum_le_lt f g n (fun i hi => h i (Nat.lt_succ_of_lt hi))))
        (Q'.add_le_add_left (finSum g n) (f n) (g n) (h n (Nat.lt_succ_self n)))

/-- Split a `finSum` at an offset: `Σ_{i<K+d} f = Σ_{i<K} f + Σ_{j<d} f(K+j)`. -/
theorem finSum_split (f : QSeq) (K : Nat) :
    ∀ d, (finSum f (K + d)).eqv (finSum f K + finSum (fun j => f (K + j)) d)
  | 0 => by
      show (finSum f K).eqv (finSum f K + (0 : Q'))
      exact Q'.eqv_of_eq (Q'.add_zero' _).symm
  | d + 1 => by
      show (finSum f (K + d) + f (K + d)).eqv
          (finSum f K + (finSum (fun j => f (K + j)) d + f (K + d)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (K + d)) (finSum_split f K d)) ?_
      exact Q'.add_assoc_eqv (finSum f K) (finSum (fun j => f (K + j)) d) (f (K + d))

/-- Negation distributes over `finSum`. -/
theorem neg_finSum (f : QSeq) :
    ∀ n, (-(finSum f n)).eqv (finSum (fun i => -(f i)) n)
  | 0 => by show (-(0 : Q')).eqv (0 : Q'); decide
  | n + 1 => by
      show (-(finSum f n + f n)).eqv (finSum (fun i => -(f i)) n + -(f n))
      exact Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (finSum f n) (f n))
        (Q'.add_eqv_congr_right _ _ (-(f n)) (neg_finSum f n))

/-- `0 ≤ partialSumAbs x k`. -/
theorem psAbs_nonneg (x : Q') (hx : (0 : Q') ≤ x) (k : Nat) :
    (0 : Q') ≤ partialSumAbs x k := by
  have h := ExpPos.partialSumAbs_mono x hx 0 k
  rw [Nat.zero_add] at h
  exact h

/-! ## `cornerAbs` and the `±corner ≤ cornerAbs` reduction -/

/-- `cornerAbsTerm x m i = aᵢ·blockAbs x (m−i) i`. -/
def cornerAbsTerm (x : Q') (m : Nat) : Nat → Q' :=
  fun i => termAbs x i * blockAbs x (m - i) i

/-- `cornerAbsₘ = Σ_{i<m} aᵢ·blockAbs x (m−i) i`. -/
def cornerAbs (x : Q') (m : Nat) : Q' := finSum (cornerAbsTerm x m) m

/-- Termwise: `±cornerTerm ≤ cornerAbsTerm`, for `i < m`. -/
theorem cornerTerm_abs_le (x : Q') (hx : (0 : Q') ≤ x) (m i : Nat) (hi : i < m) :
    cornerTerm x m i ≤ cornerAbsTerm x m i
      ∧ -(cornerTerm x m i) ≤ cornerAbsTerm x m i := by
  have hile : i ≤ m := Nat.le_of_lt hi
  have hmi : (m - i) + i = m := by omega
  have ha : (0 : Q') ≤ termAbs x i := termAbs_nonneg x hx i
  -- P⁻ₘ − P⁻_{m−i} ≤ blockAbs ; P⁻_{m−i} − P⁻ₘ ≤ blockAbs
  have hup : partialSum x m + -(partialSum x (m - i)) ≤ blockAbs x (m - i) i := by
    have := block_upper x hx (m - i) i  -- partialSum x ((m-i)+i) ≤ partialSum x (m-i) + blockAbs
    rw [hmi] at this
    exact Q'.sub_le_of_le_add this
  have hlo : -(partialSum x m + -(partialSum x (m - i))) ≤ blockAbs x (m - i) i := by
    have hbl := block_lower x hx (m - i) i  -- partialSum x (m-i) ≤ partialSum x ((m-i)+i) + blockAbs
    rw [hmi] at hbl
    -- partialSum x (m-i) - partialSum x m ≤ blockAbs
    have h2 : partialSum x (m - i) + -(partialSum x m) ≤ blockAbs x (m - i) i :=
      Q'.sub_le_of_le_add hbl
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h2
    -- -(P_m + -P_{m-i}) ≃ -P_m + - -P_{m-i} ≃ -P_m + P_{m-i} ≃ P_{m-i} + -P_m
    exact Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (partialSum x m) (-(partialSum x (m - i))))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-(partialSum x m)) (-(-(partialSum x (m - i))))
          (partialSum x (m - i)) (Q'.neg_neg_eqv (partialSum x (m - i))))
        (Q'.add_comm_eqv (-(partialSum x m)) (partialSum x (m - i))))
  refine ⟨?_, ?_⟩
  · -- aᵢ·diff ≤ aᵢ·blockAbs
    exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs x i) hup ha
  · -- -(aᵢ·diff) = aᵢ·(-diff) ≤ aᵢ·blockAbs
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_neg_eqv (termAbs x i)
        (partialSum x m + -(partialSum x (m - i)))))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs x i) hlo ha

theorem corner_le_cornerAbs (x : Q') (hx : (0 : Q') ≤ x) (m : Nat) :
    corner x m ≤ cornerAbs x m :=
  finSum_le_lt (cornerTerm x m) (cornerAbsTerm x m) m
    (fun i hi => (cornerTerm_abs_le x hx m i hi).1)

theorem neg_corner_le_cornerAbs (x : Q') (hx : (0 : Q') ≤ x) (m : Nat) :
    -(corner x m) ≤ cornerAbs x m := by
  -- -(Σ cornerTerm) ≃ Σ (-cornerTerm) ≤ Σ cornerAbsTerm
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (neg_finSum (cornerTerm x m) m)) ?_
  exact finSum_le_lt (fun i => -(cornerTerm x m i)) (cornerAbsTerm x m) m
    (fun i hi => (cornerTerm_abs_le x hx m i hi).2)

/-! ## Global bound on `P⁺` and on every block -/

/-- A uniform bound `∀ n, partialSumAbs x n ≤ B` (`B ≥ 0`). -/
theorem exists_psAbs_bound (x : Q') (hx : (0 : Q') ≤ x) :
    ∃ B : Q', (0 : Q') ≤ B ∧ ∀ n, partialSumAbs x n ≤ B := by
  obtain ⟨N, B, hB0, hB⟩ := CReal.localBound (ExpPos.expPos x hx)
  refine ⟨B, hB0, fun n => ?_⟩
  rcases Nat.le_total N n with hNn | hnN
  · -- n ≥ N : direct
    obtain ⟨_, hub⟩ := hB n hNn
    exact hub
  · -- n ≤ N : monotone up to N, then bound
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnN
    obtain ⟨_, hub⟩ := hB (n + d) (Nat.le_refl _)
    exact Q'.le_trans' _ _ _ (ExpPos.partialSumAbs_mono x hx n d) hub

/-- `partialSumAbs x (k+d) ≃ partialSumAbs x k + blockAbs x k d`. -/
theorem psAbs_split (x : Q') (k d : Nat) :
    (partialSumAbs x (k + d)).eqv (partialSumAbs x k + blockAbs x k d) := by
  rw [partialSumAbs_eq_finSum, partialSumAbs_eq_finSum, blockAbs_eq_finSum]
  exact finSum_split (termAbs x) k d

/-- Every block is bounded by the global `P⁺` bound. -/
theorem blockAbs_le_bound (x : Q') (hx : (0 : Q') ≤ x) {B : Q'}
    (hB : ∀ n, partialSumAbs x n ≤ B) (k d : Nat) :
    blockAbs x k d ≤ B := by
  -- blockAbs x k d ≤ partialSumAbs x k + blockAbs x k d ≃ partialSumAbs x (k+d) ≤ B
  refine Q'.le_trans' _ _ _ ?_ (hB (k + d))
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.eqv_symm (psAbs_split x k d)))
  -- blockAbs ≤ partialSumAbs x k + blockAbs  (since partialSumAbs ≥ 0)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (blockAbs x k d)).symm)) ?_
  exact Q'.add_le_add_right 0 (partialSumAbs x k) (blockAbs x k d)
    (psAbs_nonneg x hx k)

/-! ## The Mertens bound -/

/-- **`cornerAbsₘ → 0`.**  For `x ≥ 0` and `ε > 0`, every `m` past an explicit
modulus has `cornerAbs x m ≤ ε`. -/
theorem cornerAbs_le (x : Q') (hx : (0 : Q') ≤ x) (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m → cornerAbs x m ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := exists_psAbs_bound x hx
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.zero_le_add _ _ hB0 hB0) hε
  have hδnn : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  have hhδ : (0 : Q') < half * δ := ExpNeg.half_mul_pos δ hδpos
  have hhδnn : (0 : Q') ≤ half * δ := Q'.le_of_lt hhδ
  -- cutoffs
  have hMcut : halfRatioCutoff x ≤ termAbsModulus x (half * δ) := by
    unfold ExpNeg.termAbsModulus; exact Nat.le_add_right _ _
  obtain ⟨K, hKdef⟩ :
      ∃ K, K = max (halfRatioCutoff x) (termAbsModulus x (half * δ)) := ⟨_, rfl⟩
  have hKcut : halfRatioCutoff x ≤ K := by rw [hKdef]; exact Nat.le_max_left _ _
  have hKM : termAbsModulus x (half * δ) ≤ K := by rw [hKdef]; exact Nat.le_max_right _ _
  refine ⟨K + termAbsModulus x (half * δ), fun m hm => ?_⟩
  have hKm : K ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKm  -- m = K + d
  -- split cornerAbs at K
  have hsplit : (cornerAbs x (K + d)).eqv
      (finSum (cornerAbsTerm x (K + d)) K
        + finSum (fun j => cornerAbsTerm x (K + d) (K + j)) d) :=
    finSum_split (cornerAbsTerm x (K + d)) K d
  -- Part 1 ≤ B·δ
  have hpart1 : finSum (cornerAbsTerm x (K + d)) K ≤ B * δ := by
    -- termwise: cornerAbsTerm i ≤ termAbs x i · δ  (block ≤ δ for i < K)
    have hterm1 : ∀ i, i < K → cornerAbsTerm x (K + d) i ≤ termAbs x i * δ := by
      intro i hiK
      have hblock : blockAbs x ((K + d) - i) i ≤ δ := by
        have hmodi : termAbsModulus x (half * δ) ≤ (K + d) - i := by omega
        refine expNeg_tail_bound x hx δ hδnn ((K + d) - i)
          (Nat.le_trans hMcut hmodi)
          (termAbs_le_of_modulus_le x (half * δ) hx hhδ ((K + d) - i) hmodi) i
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs x i) hblock (termAbs_nonneg x hx i)
    refine Q'.le_trans' _ _ _
      (finSum_le_lt (cornerAbsTerm x (K + d)) (fun i => termAbs x i * δ) K hterm1) ?_
    -- Σ (termAbs x i · δ) ≃ (Σ termAbs x i)·δ = partialSumAbs x K · δ ≤ B·δ
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (finSum_mul_const (termAbs x) δ K))) ?_
    rw [← partialSumAbs_eq_finSum]
    exact Q'.mul_le_mul_of_nonneg_right (partialSumAbs x K) B δ (hB K) hδnn
  -- Part 2 ≤ δ·B
  have hpart2 : finSum (fun j => cornerAbsTerm x (K + d) (K + j)) d ≤ δ * B := by
    have hterm2 : ∀ j, (fun j => cornerAbsTerm x (K + d) (K + j)) j ≤ termAbs x (K + j) * B := by
      intro j
      show termAbs x (K + j) * blockAbs x ((K + d) - (K + j)) (K + j) ≤ termAbs x (K + j) * B
      exact Q'.mul_le_mul_of_nonneg_left _ _ (termAbs x (K + j))
        (blockAbs_le_bound x hx hB _ _) (termAbs_nonneg x hx (K + j))
    refine Q'.le_trans' _ _ _
      (finSum_le_finSum_of_termwise (fun j => cornerAbsTerm x (K + d) (K + j))
        (fun j => termAbs x (K + j) * B) hterm2 d) ?_
    -- Σ (termAbs x (K+j)·B) ≃ (Σ termAbs x (K+j))·B = blockAbs x K d · B ≤ δ·B
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (finSum_mul_const (fun j => termAbs x (K + j)) B d))) ?_
    rw [← blockAbs_eq_finSum]
    have hblockK : blockAbs x K d ≤ δ :=
      expNeg_tail_bound x hx δ hδnn K hKcut
        (termAbs_le_of_modulus_le x (half * δ) hx hhδ K hKM) d
    exact Q'.mul_le_mul_of_nonneg_right (blockAbs x K d) δ B hblockK hB0
  -- combine
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hpart1 hpart2) ?_
  -- B·δ + δ·B ≃ (B+B)·δ ≤ ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hδ
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (B * δ) (δ * B) (B * δ) (Q'.mul_comm_eqv δ B)) ?_
  exact Q'.eqv_symm (Q'.add_mul_eqv B B δ)

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.finSum_split
#print axioms ConstructiveReals.corner_le_cornerAbs
#print axioms ConstructiveReals.neg_corner_le_cornerAbs
#print axioms ConstructiveReals.blockAbs_le_bound
#print axioms ConstructiveReals.cornerAbs_le
