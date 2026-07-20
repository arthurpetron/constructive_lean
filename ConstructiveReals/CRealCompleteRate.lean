/-
# `leRat`-outer completeness backbone for `CReal` (the Prop/Type wall resolver)

This module supplies the completeness lemma the existing `leRat` infrastructure
(the `∀ε>0 ∃N …` rational upper bound) needs in order to construct the LIMIT of a
Cauchy sequence of `CReal`s.

## The Prop/Type wall

The three existing completeness backbones — `CReal.completeLimit` (`ModCauchy`),
`CReal.completeLimitIdx` (`ModCauchyIdx`) and `CReal.completeLimitCauchy`
(`ModCauchyEv`) — all demand the OUTER two-sided bound as `Type`-level DATA:
either an all-`k` inequality (`ModCauchy`/`ModCauchyIdx`) or an eventual bound
with a `Type`-level threshold `boundK : Q' → Nat → Nat → Nat` (`ModCauchyEv`).
A `leRat` bound

    leRat (s m − s n) ε  :=  ∀ δ>0, ∃ N, ∀ j ≥ N, (s m − s n).approx j ≤ ε + δ

is a `Prop` (`∀ε ∃N`); its threshold `N` lives behind a proof-irrelevant `∃`, so
it CANNOT fill the `Type`-level `boundK`.  This is the wall: the natural outer
estimate produced by the refinement infrastructure is `leRat`, but no existing
completeness limit consumes a `leRat` outer bound.

## The resolution (the key insight)

The limit CONSTRUCTION needs only the `Type`-level data: the Cauchy RATE
`M : Q' → Nat` and the per-term regularity modulus `reg : Nat → Q' → Nat`.  The
per-pair outer bound is used ONLY inside the `cauchy`/`ConvergesTo` PROOFS — which
are `Prop`s, so eliminating the `∃N` of `leRat` there is allowed.  We therefore
keep the diagonal `(s (MhatR k)).approx (RhatR k)` EXACTLY as in
`completeLimitCauchy`, and re-prove the two directedness obligations by
`obtain`-ing the `leRat` threshold inside the proof and enlarging the common
bridging index past it.

## Error budget (four `q`-steps, `q = ¼ε`)

The outer step now costs `≤ 2q`: instantiating `hb` at level `invSucc a` and
`evTwoSided_of_leRat` at tolerance `η = invSucc a` gives the inflated outer bound
`invSucc a + invSucc a ≤ 2q`.  With the two inner-regularity steps (`≤ q` each)
the total is `4q = ε`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `completeLimitFromRate s M reg hreg hb Mmono : CReal` — the diagonal limit
    built from the `Type`-level rate `M`, the `Type`-level regularity `reg`, the
    `Prop`-level `leRat` outer bound `hb`, and antitone `Mmono`.
  * `convergesTo_completeLimitFromRate : ConvergesTo s (completeLimitFromRate …)`.
  * bound-passers `leEv_ofQ'_completeLimitFromRate`,
    `leEv_completeLimitFromRate_ofQ'`, `isPositiveEv_completeLimitFromRate`.
  * a non-vacuity demo on the constant sequence.

This is the reusable engine: any `Nat → CReal` sequence with a `Type`-level rate,
`Type`-level per-term regularity, and a `leRat` outer Cauchy bound has a limit.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Every load-bearing declaration reports `[propext]` or
`[propext, Quot.sound]` (the latter only via reused `Nat`/`omega`/`Int` helpers).
-/

import ConstructiveReals.CRealCompleteCauchy

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.HalfPow

namespace CReal

open Q'

/-! ## 0. Local rational helpers (keep the import surface minimal) -/

/-- `a + (-b) ≤ c ⟹ a ≤ b + c`.  (Same statement as `Pi.le_add_of_sub_le`,
re-proved locally to avoid the `Pi` import.) -/
theorem leAddOfSubLe {a b c : Q'} (h : a + (-b) ≤ c) : a ≤ b + c := by
  have h1 : (a + (-b)) + b ≤ c + b := Q'.add_le_add_right _ _ _ h
  have e1 : ((a + (-b)) + b).eqv a := by
    have s1 : ((a + (-b)) + b).eqv (a + ((-b) + b)) := Q'.add_assoc_eqv a (-b) b
    have s2 : (a + ((-b) + b)).eqv (a + 0) :=
      Q'.add_eqv_congr_left a ((-b) + b) 0 (Q'.neg_add_self_eqv b)
    have s3 : (a + (0 : Q')).eqv a := by rw [Q'.add_zero' a]; exact Q'.eqv_refl a
    exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 s3)
  have e2 : (c + b).eqv (b + c) := Q'.add_comm_eqv c b
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv e2))

/-- The `4q ≤ ε` collapse for `q = ¼ε`: `(((q+q)+q)+q) ≤ ε`. -/
theorem fourQ_le (ε : Q') (hε : (0 : Q') < ε) :
    (((half * (half * ε) + half * (half * ε)) + half * (half * ε)) + half * (half * ε)) ≤ ε := by
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  -- q + q ≃ ½ε
  have hqq : (q + q).eqv (half * ε) := ExpNeg.two_halves (half * ε)
  -- ((q+q)+q)+q ≃ (q+q)+(q+q) ≃ ½ε + ½ε ≃ ε
  have e1 : ((((q + q) + q) + q)).eqv ((q + q) + (q + q)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (q + q) q q) ?_
    exact Q'.eqv_refl _
  have e2 : ((q + q) + (q + q)).eqv ((half * ε) + (half * ε)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (q + q) (half * ε) (q + q) hqq) ?_
    exact Q'.add_eqv_congr_left (half * ε) (q + q) (half * ε) hqq
  have e3 : ((half * ε) + (half * ε)).eqv ε := ExpNeg.two_halves ε
  have efinal : ((((q + q) + q) + q)).eqv ε :=
    Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)
  exact Q'.le_of_eqv efinal

/-- Reassociate-and-collapse: if `((p+p)+p)+p ≤ ε` then
`(((w+p)+p)+p)+p ≤ w + ε`. -/
theorem collapse4 (w p ε : Q') (h4 : ((p + p) + p) + p ≤ ε) :
    (((w + p) + p) + p) + p ≤ w + ε := by
  -- (((w+p)+p)+p)+p ≃ w + (p+(p+(p+p)))  by repeated re-association
  have step1 : ((((w + p) + p) + p) + p).eqv ((((w + p) + p)) + (p + p)) :=
    Q'.add_assoc_eqv (((w + p) + p)) p p
  have step2 : (((w + p) + p) + (p + p)).eqv ((w + p) + (p + (p + p))) :=
    Q'.add_assoc_eqv (w + p) p (p + p)
  have step3 : ((w + p) + (p + (p + p))).eqv (w + (p + (p + (p + p)))) :=
    Q'.add_assoc_eqv w p (p + (p + p))
  have echain : ((((w + p) + p) + p) + p).eqv (w + (p + (p + (p + p)))) :=
    Q'.eqv_trans _ _ _ step1 (Q'.eqv_trans _ _ _ step2 step3)
  -- and ((p+p)+p)+p ≃ p+(p+(p+p))
  have epp1 : (((p + p) + p) + p).eqv ((p + p) + (p + p)) :=
    Q'.add_assoc_eqv (p + p) p p
  have epp2 : ((p + p) + (p + p)).eqv (p + (p + (p + p))) :=
    Q'.add_assoc_eqv p p (p + p)
  have epp : (((p + p) + p) + p).eqv (p + (p + (p + p))) :=
    Q'.eqv_trans _ _ _ epp1 epp2
  -- so (((w+p)+p)+p)+p ≃ w + (((p+p)+p)+p) ≤ w + ε
  have hle1 : ((((w + p) + p) + p) + p) ≤ (w + (p + (p + (p + p)))) := Q'.le_of_eqv echain
  have hsum_le : (p + (p + (p + p))) ≤ ε := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv epp) h4
  exact Q'.le_trans' _ _ _ hle1
    (Q'.add_le_add_left w (p + (p + (p + p))) ε hsum_le)

/-! ## 1. The `leRat` outer bound, unpacked into an eventual two-sided form -/

/-- From `leRat (add x (neg y)) ε` extract, at tolerance `δ > 0`, a threshold `N`
past which `x.approx j ≤ y.approx j + (ε + δ)`. -/
theorem evOneSided_of_leRat {x y : CReal} {ε : Q'}
    (h : leRat (add x (neg y)) ε) {δ : Q'} (hδ : (0 : Q') < δ) :
    ∃ N : Nat, ∀ j : Nat, N ≤ j → x.approx j ≤ y.approx j + (ε + δ) := by
  obtain ⟨N, hN⟩ := h δ hδ
  refine ⟨N, fun j hj => ?_⟩
  have hraw : x.approx j + (-(y.approx j)) ≤ ε + δ := by simpa using hN j hj
  exact leAddOfSubLe hraw

/-- The two-sided eventual outer bound at an enlarged tolerance.  Given the `leRat`
outer bound in BOTH directions at level `ε`, and any tolerance `η > 0`, there is a
threshold `K` past which the two approximations agree to within `ε + η`. -/
theorem evTwoSided_of_leRat {x y : CReal} {ε : Q'}
    (hxy : leRat (add x (neg y)) ε) (hyx : leRat (add y (neg x)) ε)
    {η : Q'} (hη : (0 : Q') < η) :
    ∃ K : Nat, ∀ k : Nat, K ≤ k →
      x.approx k ≤ y.approx k + (ε + η) ∧ y.approx k ≤ x.approx k + (ε + η) := by
  obtain ⟨K1, hK1⟩ := evOneSided_of_leRat hxy hη
  obtain ⟨K2, hK2⟩ := evOneSided_of_leRat hyx hη
  refine ⟨max K1 K2, fun k hk => ?_⟩
  exact ⟨hK1 k (Nat.le_trans (Nat.le_max_left _ _) hk),
         hK2 k (Nat.le_trans (Nat.le_max_right _ _) hk)⟩

/-! ## 2. The diagonal data (standalone copies of the `MhatE`/`RhatE` machinery) -/

/-- Running-max of the outer rate (same shape as `MhatE`). -/
def MhatR (M : Q' → Nat) : Nat → Nat
  | 0 => M (Q'.invSucc 0)
  | k + 1 => max (MhatR M k) (M (Q'.invSucc (k + 1)))

theorem MhatR_mono_succ (M : Q' → Nat) (k : Nat) :
    MhatR M k ≤ MhatR M (k + 1) := Nat.le_max_left _ _

theorem MhatR_mono (M : Q' → Nat) {a b : Nat} (h : a ≤ b) :
    MhatR M a ≤ MhatR M b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (MhatR_mono_succ M b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

theorem M_le_MhatR (M : Q' → Nat) (k : Nat) :
    M (Q'.invSucc k) ≤ MhatR M k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The index-absorbing approximation index (same shape as `RhatE`). -/
def RhatR (M : Q' → Nat) (reg : Nat → Q' → Nat) (k : Nat) : Nat :=
  max k (reg (MhatR M k) (Q'.invSucc k))

theorem k_le_RhatR (M : Q' → Nat) (reg : Nat → Q' → Nat) (k : Nat) :
    k ≤ RhatR M reg k := Nat.le_max_left _ _

theorem reg_le_RhatR (M : Q' → Nat) (reg : Nat → Q' → Nat) (k : Nat) :
    reg (MhatR M k) (Q'.invSucc k) ≤ RhatR M reg k := Nat.le_max_right _ _

/-- The monotone-shifted, index-absorbing diagonal. -/
def diagSeqR (s : Nat → CReal) (M : Q' → Nat) (reg : Nat → Q' → Nat) (k : Nat) : Q' :=
  (s (MhatR M k)).approx (RhatR M reg k)

/-! ## 3. The hypothesis bundle for `completeLimitFromRate` -/

/-- The per-term regularity predicate (`Type`-free; a `Prop`, but its modulus
`reg` is `Type`-level data passed alongside). -/
def RegPred (s : Nat → CReal) (reg : Nat → Q' → Nat) : Prop :=
  ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg i ε ≤ p → reg i ε ≤ qq →
    (s i).approx p ≤ (s i).approx qq + ε ∧ (s i).approx qq ≤ (s i).approx p + ε

/-- The `leRat` outer Cauchy bound predicate. -/
def LeRatBound (s : Nat → CReal) (M : Q' → Nat) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
    leRat (add (s m) (neg (s n))) ε ∧ leRat (add (s n) (neg (s m))) ε

/-- The antitone-rate predicate. -/
def MmonoPred (M : Q' → Nat) : Prop :=
  ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ

/-! ## 4. The diagonal is Cauchy (outer bound consumed from the `leRat` hypothesis) -/

/-- The directed core bound on the `leRat`-outer diagonal.  For `a ≤ b` with
`a, b ≥ q.den` (`q = ¼ε`), `|D a − D b| ≤ ε`.  The outer step uses `hb` at level
`invSucc a` and `evTwoSided_of_leRat` at tolerance `η = invSucc a` to obtain a
`Prop`-level threshold `Kab`; the bridging index `big` is enlarged past it.  Four
`q`-steps: inner-a (`≤ q`), outer (`≤ 2q`), inner-b (`≤ q`). -/
theorem diagSeqR_directed (s : Nat → CReal) (M : Q' → Nat) (reg : Nat → Q' → Nat)
    (hreg : RegPred s reg) (hb : LeRatBound s M)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∀ a b : Nat, a ≤ b → (half * (half * ε)).den ≤ a →
      diagSeqR s M reg a ≤ diagSeqR s M reg b + ε ∧
      diagSeqR s M reg b ≤ diagSeqR s M reg a + ε := by
  intro a b hab hNa
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  -- scales: invSucc a ≤ q, invSucc b ≤ invSucc a ≤ q
  have hinvapos : (0 : Q') < Q'.invSucc a := Q'.invSucc_pos a
  have hinva : Q'.invSucc a ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hNa) (HalfPow.invSucc_den_le q hqpos)
  have hinvbpos : (0 : Q') < Q'.invSucc b := Q'.invSucc_pos b
  have hinvb_a : Q'.invSucc b ≤ Q'.invSucc a := ExpNeg.invSucc_le_of_le hab
  have hinvb : Q'.invSucc b ≤ q := Q'.le_trans' _ _ _ hinvb_a hinva
  -- outer availabilities: M (invSucc a) ≤ MhatR a, ≤ MhatR b
  have hMa : M (Q'.invSucc a) ≤ MhatR M a := M_le_MhatR M a
  have hMb : M (Q'.invSucc a) ≤ MhatR M b := Nat.le_trans hMa (MhatR_mono M hab)
  -- the leRat outer bound at level invSucc a comparing s(MhatR a), s(MhatR b)
  obtain ⟨hxy, hyx⟩ := hb (Q'.invSucc a) hinvapos (MhatR M a) (MhatR M b) hMa hMb
  -- consume it (Prop): at tolerance η = invSucc a, get a threshold Kab
  obtain ⟨Kab, hKab⟩ := evTwoSided_of_leRat hxy hyx hinvapos
  -- the common large index past both RhatR and Kab
  let big : Nat := max (max (RhatR M reg a) (RhatR M reg b)) Kab
  have hRab_big : max (RhatR M reg a) (RhatR M reg b) ≤ big := Nat.le_max_left _ _
  have hRa_big : RhatR M reg a ≤ big := Nat.le_trans (Nat.le_max_left _ _) hRab_big
  have hRb_big : RhatR M reg b ≤ big := Nat.le_trans (Nat.le_max_right _ _) hRab_big
  have hK_big : Kab ≤ big := Nat.le_max_right _ _
  -- inner-modulus availabilities
  have hregA : reg (MhatR M a) (Q'.invSucc a) ≤ RhatR M reg a := reg_le_RhatR M reg a
  have hregA_big : reg (MhatR M a) (Q'.invSucc a) ≤ big := Nat.le_trans hregA hRa_big
  have hregB : reg (MhatR M b) (Q'.invSucc b) ≤ RhatR M reg b := reg_le_RhatR M reg b
  have hregB_big : reg (MhatR M b) (Q'.invSucc b) ≤ big := Nat.le_trans hregB hRb_big
  -- (I) inner reg of s(MhatR a) at scale invSucc a between RhatR a and big
  obtain ⟨hIa1, hIa2⟩ :=
    hreg (MhatR M a) (Q'.invSucc a) hinvapos (RhatR M reg a) big hregA hregA_big
  -- (O) the eventual outer (level invSucc a, tolerance invSucc a) at big ≥ Kab
  obtain ⟨hO1, hO2⟩ := hKab big hK_big
  -- (II) inner reg of s(MhatR b) at scale invSucc b between big and RhatR b
  obtain ⟨hIb1, hIb2⟩ :=
    hreg (MhatR M b) (Q'.invSucc b) hinvbpos big (RhatR M reg b) hregB_big hregB
  -- rescale each step to q (outer to 2q via invSucc a + invSucc a ≤ q + q)
  have hIa1' : (s (MhatR M a)).approx (RhatR M reg a)
      ≤ (s (MhatR M a)).approx big + q :=
    Q'.le_trans' _ _ _ hIa1 (Q'.add_le_add_left _ _ q hinva)
  have hIa2' : (s (MhatR M a)).approx big
      ≤ (s (MhatR M a)).approx (RhatR M reg a) + q :=
    Q'.le_trans' _ _ _ hIa2 (Q'.add_le_add_left _ _ q hinva)
  -- outer: invSucc a + invSucc a ≤ q + q
  have houterscale : Q'.invSucc a + Q'.invSucc a ≤ q + q :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hinva)
      (Q'.add_le_add_left q (Q'.invSucc a) q hinva)
  have hO1' : (s (MhatR M a)).approx big ≤ (s (MhatR M b)).approx big + (q + q) :=
    Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_left _ _ (q + q) houterscale)
  have hO2' : (s (MhatR M b)).approx big ≤ (s (MhatR M a)).approx big + (q + q) :=
    Q'.le_trans' _ _ _ hO2 (Q'.add_le_add_left _ _ (q + q) houterscale)
  have hIb1' : (s (MhatR M b)).approx big
      ≤ (s (MhatR M b)).approx (RhatR M reg b) + q :=
    Q'.le_trans' _ _ _ hIb1 (Q'.add_le_add_left _ _ q hinvb)
  have hIb2' : (s (MhatR M b)).approx (RhatR M reg b)
      ≤ (s (MhatR M b)).approx big + q :=
    Q'.le_trans' _ _ _ hIb2 (Q'.add_le_add_left _ _ q hinvb)
  -- `4q ≤ ε` collapse via collapse4 + fourQ_le
  have h4q : ∀ w : Q', (((w + q) + q) + q) + q ≤ w + ε :=
    fun w => collapse4 w q ε (fourQ_le ε hε)
  refine ⟨?_, ?_⟩
  · -- D a ≤ ((( (s MhatR b)_{RhatR b} + q) + (q+q)) + q) reorganized to 4 q-steps
    -- chain: D a ≤ (s a)_big + q ≤ ((s b)_big + (q+q)) + q ≤ (((s b)_{RhatR b}+q)+(q+q))+q
    have hchain : diagSeqR s M reg a
        ≤ (((((s (MhatR M b)).approx (RhatR M reg b)) + q) + q) + q) + q := by
      -- step1: D a = (s a)_{RhatR a} ≤ (s a)_big + q
      refine Q'.le_trans' _ _ _ hIa1' ?_
      -- step2: (s a)_big + q ≤ ((s b)_big + (q+q)) + q
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1') ?_
      -- now: ((s b)_big + (q+q)) + q ; rewrite (q+q) to q+q and push (s b)_big ≤ (s b)_{RhatR b}+q
      -- ((s b)_big + (q+q)) + q ≤ (((s b)_{RhatR b}+q) + (q+q)) + q
      have hpush : (s (MhatR M b)).approx big + (q + q)
          ≤ (((s (MhatR M b)).approx (RhatR M reg b)) + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hIb1'
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      -- reshape  (((X+q)+(q+q))+q) = ((((X+q)+q)+q)+q)  via associativity of the middle (q+q)
      -- LHS = (((X + q) + (q+q)) + q), target = ((((X+q)+q)+q)+q)
      have ereshape : ((((s (MhatR M b)).approx (RhatR M reg b) + q) + (q + q)) + q).eqv
          (((((s (MhatR M b)).approx (RhatR M reg b)) + q) + q) + q + q) := by
        -- ((X+q)+(q+q)) ≃ (((X+q)+q)+q) by inverse assoc; then +q on both sides
        refine Q'.add_eqv_congr_right _ _ q ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv ((s (MhatR M b)).approx (RhatR M reg b) + q) q q)
      exact Q'.le_of_eqv ereshape
    exact Q'.le_trans' _ _ _ hchain (h4q (diagSeqR s M reg b))
  · have hchain : diagSeqR s M reg b
        ≤ (((((s (MhatR M a)).approx (RhatR M reg a)) + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hIb2' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2') ?_
      have hpush : (s (MhatR M a)).approx big + (q + q)
          ≤ (((s (MhatR M a)).approx (RhatR M reg a)) + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hIa2'
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      have ereshape : ((((s (MhatR M a)).approx (RhatR M reg a) + q) + (q + q)) + q).eqv
          (((((s (MhatR M a)).approx (RhatR M reg a)) + q) + q) + q + q) := by
        refine Q'.add_eqv_congr_right _ _ q ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv ((s (MhatR M a)).approx (RhatR M reg a) + q) q q)
      exact Q'.le_of_eqv ereshape
    exact Q'.le_trans' _ _ _ hchain (h4q (diagSeqR s M reg a))

/-! ## 5. The completeness limit -/

/-- **The `leRat`-outer completeness limit.**  The index-absorbing diagonal of a
sequence with `Type`-level rate `M`, `Type`-level per-term regularity `reg`
(`hreg`), `Prop`-level `leRat` outer Cauchy bound `hb`, and antitone `Mmono` is a
`CReal`.  The construction uses only `M`/`reg`; `hb`/`Mmono` are consumed in the
`cauchy` proof (a `Prop`). -/
def completeLimitFromRate (s : Nat → CReal) (M : Q' → Nat) (reg : Nat → Q' → Nat)
    (hreg : RegPred s reg) (hb : LeRatBound s M) : CReal where
  approx k := diagSeqR s M reg k
  cauchy := by
    intro ε hε
    refine ⟨(half * (half * ε)).den, fun a b ha hb' => ?_⟩
    rcases Nat.le_total a b with hab | hba
    · exact diagSeqR_directed s M reg hreg hb ε hε a b hab ha
    · have h := diagSeqR_directed s M reg hreg hb ε hε b a hba hb'
      exact ⟨h.2, h.1⟩

@[simp] theorem completeLimitFromRate_approx (s : Nat → CReal) (M : Q' → Nat)
    (reg : Nat → Q' → Nat) (hreg : RegPred s reg) (hb : LeRatBound s M) (k : Nat) :
    (completeLimitFromRate s M reg hreg hb).approx k =
      (s (MhatR M k)).approx (RhatR M reg k) := rfl

/-! ## 6. The diagonal limit is the limit of `s` -/

/-- **`ConvergesTo s (completeLimitFromRate …)`.**  At scale `ε`, `q = ¼ε`, stage
`M q`.  For `N ≥ M q` and approx index `n ≥ max (reg N q) q.den`, bridge
`(s N)_n → (s N)_J → (s (MhatR n))_J → (s (MhatR n))_{RhatR n} = L_n` at an
enlarged index `J = max (RhatR n) Kab`, where `Kab` is the `leRat` threshold at
level `q` and tolerance `q` (outer ≤ `2q`).  Steps: inner-N (`≤ q`), outer
(`≤ 2q`), inner-(MhatR n) (`≤ q`); `4q ≤ ε`. -/
theorem convergesTo_completeLimitFromRate (s : Nat → CReal) (M : Q' → Nat)
    (reg : Nat → Q' → Nat) (hreg : RegPred s reg) (hb : LeRatBound s M)
    (Mmono : MmonoPred M) :
    ConvergesTo s (completeLimitFromRate s M reg hreg hb) := by
  intro ε hε
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  refine ⟨M q, fun N hN => ?_⟩
  refine ⟨max (reg N q) q.den, fun n hn => ?_⟩
  have hregNn : reg N q ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hqdenn : q.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hinvn : Q'.invSucc n ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn) (HalfPow.invSucc_den_le q hqpos)
  have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
  -- M q ≤ MhatR n
  have hMqn : M q ≤ MhatR M n :=
    Nat.le_trans (Mmono q (Q'.invSucc n) hinvnpos hinvn) (M_le_MhatR M n)
  -- the leRat outer bound at level q comparing s N, s (MhatR n)
  obtain ⟨hxy, hyx⟩ := hb q hqpos N (MhatR M n) hN hMqn
  -- consume it (Prop): tolerance q, threshold Kab
  obtain ⟨Kab, hKab⟩ := evTwoSided_of_leRat hxy hyx hqpos
  -- enlarged bridging index
  let J : Nat := max (RhatR M reg n) Kab
  have hRn_J : RhatR M reg n ≤ J := Nat.le_max_left _ _
  have hK_J : Kab ≤ J := Nat.le_max_right _ _
  have hn_R : n ≤ RhatR M reg n := k_le_RhatR M reg n
  have hregN_R : reg N q ≤ RhatR M reg n := Nat.le_trans hregNn hn_R
  have hregN_J : reg N q ≤ J := Nat.le_trans hregN_R hRn_J
  -- inner modulus of s (MhatR n) at scale invSucc n
  have hregMn_R : reg (MhatR M n) (Q'.invSucc n) ≤ RhatR M reg n := reg_le_RhatR M reg n
  have hregMn_J : reg (MhatR M n) (Q'.invSucc n) ≤ J := Nat.le_trans hregMn_R hRn_J
  -- (I) inner reg of s N at scale q between n and J
  obtain ⟨hI1, hI2⟩ := hreg N q hqpos n J hregNn hregN_J
  -- (O) eventual outer (level q, tolerance q) at J ≥ Kab
  obtain ⟨hO1, hO2⟩ := hKab J hK_J
  -- (II) inner reg of s (MhatR n) at scale invSucc n between J and RhatR n
  obtain ⟨hII1, hII2⟩ :=
    hreg (MhatR M n) (Q'.invSucc n) hinvnpos J (RhatR M reg n) hregMn_J hregMn_R
  -- rescale step (II) to q
  have hII1' : (s (MhatR M n)).approx J ≤ (s (MhatR M n)).approx (RhatR M reg n) + q :=
    Q'.le_trans' _ _ _ hII1 (Q'.add_le_add_left _ _ q hinvn)
  have hII2' : (s (MhatR M n)).approx (RhatR M reg n) ≤ (s (MhatR M n)).approx J + q :=
    Q'.le_trans' _ _ _ hII2 (Q'.add_le_add_left _ _ q hinvn)
  -- `4q ≤ ε` collapse
  have h4q : ∀ w : Q', (((w + q) + q) + q) + q ≤ w + ε :=
    fun w => collapse4 w q ε (fourQ_le ε hε)
  refine ⟨?_, ?_⟩
  · show (s N).approx n ≤ (completeLimitFromRate s M reg hreg hb).approx n + ε
    -- (s N)_n ≤ (s N)_J + q ≤ ((s MhatR n)_J + (q+q)) + q ≤ ((((s MhatR n)_{RhatR n}+q)+q)+q)+q
    have hchain : (s N).approx n
        ≤ ((((s (MhatR M n)).approx (RhatR M reg n) + q) + q) + q) + q := by
      -- step (I): (s N)_n ≤ (s N)_J + q
      refine Q'.le_trans' _ _ _ hI1 ?_
      -- step (O): (s N)_J + q ≤ ((s MhatR n)_J + (q+q)) + q
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1) ?_
      -- step (II): push (s MhatR n)_J ≤ (s MhatR n)_{RhatR n} + q under +(q+q), +q
      have hpush : (s (MhatR M n)).approx J + (q + q)
          ≤ ((s (MhatR M n)).approx (RhatR M reg n) + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hII1'
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      -- reshape (((X+q)+(q+q))+q) = ((((X+q)+q)+q)+q)
      have ereshape : ((((s (MhatR M n)).approx (RhatR M reg n) + q) + (q + q)) + q).eqv
          (((((s (MhatR M n)).approx (RhatR M reg n)) + q) + q) + q + q) := by
        refine Q'.add_eqv_congr_right _ _ q ?_
        exact Q'.eqv_symm
          (Q'.add_assoc_eqv ((s (MhatR M n)).approx (RhatR M reg n) + q) q q)
      exact Q'.le_of_eqv ereshape
    exact Q'.le_trans' _ _ _ hchain (h4q ((s (MhatR M n)).approx (RhatR M reg n)))
  · show (completeLimitFromRate s M reg hreg hb).approx n ≤ (s N).approx n + ε
    -- L_n = (s MhatR n)_{RhatR n} ≤ (s MhatR n)_J + q ≤ ((s N)_J + (q+q)) + q ≤ (((( s N)_n+q)+q)+q)+q
    have hchain : (s (MhatR M n)).approx (RhatR M reg n)
        ≤ (((((s N).approx n) + q) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hII2' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2) ?_
      have hpush : (s N).approx J + (q + q)
          ≤ (((s N).approx n) + q) + (q + q) :=
        Q'.add_le_add_right _ _ (q + q) hI2
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hpush) ?_
      have ereshape : ((((s N).approx n + q) + (q + q)) + q).eqv
          (((((s N).approx n) + q) + q) + q + q) := by
        refine Q'.add_eqv_congr_right _ _ q ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv ((s N).approx n + q) q q)
      exact Q'.le_of_eqv ereshape
    exact Q'.le_trans' _ _ _ hchain (h4q ((s N).approx n))

/-! ## 7. Bound-passing to the diagonal limit -/

/-- **Lower bound passes to the limit.** -/
theorem leEv_ofQ'_completeLimitFromRate (s : Nat → CReal) (M : Q' → Nat)
    (reg : Nat → Q' → Nat) (hreg : RegPred s reg) (hb : LeRatBound s M) {lb : Q'}
    (h : ∀ k j : Nat, lb ≤ (s k).approx j) :
    leEv (ofQ' lb) (completeLimitFromRate s M reg hreg hb) :=
  leEv_ofQ'_of_approx_ge (fun n => h (MhatR M n) (RhatR M reg n))

/-- **Upper bound passes to the limit.** -/
theorem leEv_completeLimitFromRate_ofQ' (s : Nat → CReal) (M : Q' → Nat)
    (reg : Nat → Q' → Nat) (hreg : RegPred s reg) (hb : LeRatBound s M) {ub : Q'}
    (h : ∀ k j : Nat, (s k).approx j ≤ ub) :
    leEv (completeLimitFromRate s M reg hreg hb) (ofQ' ub) :=
  leEv_le_ofQ'_of_approx_le (fun n => h (MhatR M n) (RhatR M reg n))

/-- **Strict positivity passes to the limit (eventual form).** -/
theorem isPositiveEv_completeLimitFromRate (s : Nat → CReal) (M : Q' → Nat)
    (reg : Nat → Q' → Nat) (hreg : RegPred s reg) (hb : LeRatBound s M) {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ k j : Nat, ε ≤ (s k).approx j) :
    (0 : Q') < ε ∧ leEv (ofQ' ε) (completeLimitFromRate s M reg hreg hb) :=
  ⟨hε, leEv_ofQ'_completeLimitFromRate s M reg hreg hb h⟩

/-! ## 8. Non-vacuity demo

The constant `CReal` sequence at `ofQ' 1`, routed through the `leRat`-outer
interface, converges to its limit.  Its rate `M ε = 0`, regularity `reg i ε = 0`,
and the `leRat` outer bound holds since the terms are identical. -/

/-- The constant-sequence regularity (every `ofQ' 1` is constant). -/
theorem constSeq_RegPred : RegPred constSeq (fun _ _ => 0) := by
  intro i ε hε p qq _ _
  refine ⟨?_, ?_⟩ <;>
    exact Q'.add_le_self_of_nonneg (1 : Q') ε (Q'.le_of_lt hε)

/-- The constant-sequence `leRat` outer bound. -/
theorem constSeq_LeRatBound : LeRatBound constSeq (fun _ => 0) := by
  intro ε hε m n _ _
  refine ⟨?_, ?_⟩ <;>
    · refine leRat_of_eventually ⟨0, fun j _ => ?_⟩
      -- (add (constSeq _) (neg (constSeq _))).approx j = 1 + (-1) = 0 ≤ ε? need ≤ 0 ; here ≤ ε
      show (constSeq _).approx j + (-((constSeq _).approx j)) ≤ ε
      have he : ((1 : Q') + (-(1 : Q'))).eqv (0 : Q') := Q'.add_neg_self_eqv (1 : Q')
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_of_lt hε)

/-- The constant-sequence rate is antitone (trivially constant). -/
theorem constSeq_MmonoPred : MmonoPred (fun _ => 0) := by
  intro _ _ _ _; exact Nat.le_refl 0

/-- The `leRat`-outer completeness limit of the constant `ofQ' 1` sequence. -/
def demoConstLimitFromRate : CReal :=
  completeLimitFromRate constSeq (fun _ => 0) (fun _ _ => 0)
    constSeq_RegPred constSeq_LeRatBound

/-- Non-vacuity: the constant sequence converges to its `leRat`-outer limit. -/
theorem demoConstLimitFromRate_converges :
    ConvergesTo constSeq demoConstLimitFromRate :=
  convergesTo_completeLimitFromRate constSeq (fun _ => 0) (fun _ _ => 0)
    constSeq_RegPred constSeq_LeRatBound constSeq_MmonoPred

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.CReal.leAddOfSubLe
#print axioms ConstructiveReals.CReal.fourQ_le
#print axioms ConstructiveReals.CReal.collapse4
#print axioms ConstructiveReals.CReal.evOneSided_of_leRat
#print axioms ConstructiveReals.CReal.evTwoSided_of_leRat
#print axioms ConstructiveReals.CReal.MhatR_mono
#print axioms ConstructiveReals.CReal.M_le_MhatR
#print axioms ConstructiveReals.CReal.diagSeqR_directed
#print axioms ConstructiveReals.CReal.completeLimitFromRate
#print axioms ConstructiveReals.CReal.completeLimitFromRate_approx
#print axioms ConstructiveReals.CReal.convergesTo_completeLimitFromRate
#print axioms ConstructiveReals.CReal.leEv_ofQ'_completeLimitFromRate
#print axioms ConstructiveReals.CReal.leEv_completeLimitFromRate_ofQ'
#print axioms ConstructiveReals.CReal.isPositiveEv_completeLimitFromRate
#print axioms ConstructiveReals.CReal.demoConstLimitFromRate_converges
