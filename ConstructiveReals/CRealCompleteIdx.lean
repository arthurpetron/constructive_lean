/-
# Index-indexed completeness backbone for `CReal`

A variant of `Constructive.CReal.completeLimit` whose INNER regularity modulus is
**index-indexed**: `reg : Nat → Q' → Nat` rather than `reg : Q' → Nat`.

## Why this exists (the convergence-interface limitation)

`CReal.ModCauchy s` carries a SINGLE index-FREE inner regularity modulus
`reg : Q' → Nat` valid for EVERY term `s i` simultaneously
(`∀ i ε, reg ε ≤ p,q ⇒ (s i).approx p ≈ε (s i).approx q`).  For sequences whose
terms are themselves finite sums of a GROWING number of regular pieces — e.g. a
Riemann sum `semiSum n` (a `csum` of `n` Heron-√ terms) — the per-term inner
modulus GROWS with the term index `n`, so no single index-free `reg ε` controls
all terms.  Closing `ModCauchy` literally for such a sequence is impossible.

The fix here keeps the OUTER datum (`M`, `bound`, `Mmono`) IDENTICAL — the outer
bound is the genuine convergence content and is unchanged — and relaxes the inner
modulus to `reg : Nat → Q' → Nat` (`reg i ε`).  In the diagonal limit the term
index at diagonal step `k` is the KNOWN value `Mhat k`, so the inner modulus
`reg (Mhat k) ε` is available pointwise.  The diagonal's approximation index is
shifted to `RhatIdx k = max k (reg (Mhat k) (invSucc k))`, which ABSORBS the
per-term inner modulus into the diagonal so that the OUTER stage `N(ε)` stays
index-free.  No antitonicity of `reg` is assumed.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `ModCauchyIdx s` — the index-indexed modulus-Cauchy datum (outer `M`/`bound`/
    `Mmono` identical to `ModCauchy`; inner `reg : Nat → Q' → Nat`, `regular`
    index-indexed).
  * `modCauchy_to_idx : ModCauchy s → ModCauchyIdx s` — the free coercion
    (index-free ⟹ index-indexed by ignoring the index); the POINT is the
    converse direction is now inhabitable for growing-modulus sequences.
  * `completeLimitIdx s c : CReal` — the diagonal limit (approx
    `RhatIdx`-shifted), with `cauchy` re-proved from the index-indexed `reg`.
  * `convergesTo_completeLimitIdx : ConvergesTo s (completeLimitIdx s c)`.
  * bound-passing: `leEv_ofQ'_completeLimitIdx`, `leEv_completeLimitIdx_ofQ'`,
    `isPositiveEv_completeLimitIdx` — `Q'` lower/upper bounds and strict
    positivity pass to the limit (mirror the `CReal.completeLimit` lemmas).

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Every load-bearing declaration reports `[propext]` or
`[propext, Quot.sound]` (the latter only via reused `Nat`/`omega` helpers).
-/

import ConstructiveReals.CRealComplete

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.HalfPow

namespace CReal

open Q'

/-! ## 1. The index-indexed modulus-Cauchy datum -/

/-- An **index-indexed** uniform-rate modulus-Cauchy datum for a `CReal` sequence
`s`.  The OUTER modulus `M`, its `bound`, and the antitone `Mmono` are IDENTICAL
to `ModCauchy` (the genuine convergence content).  The INNER regularity modulus is
relaxed to `reg : Nat → Q' → Nat` — for each term index `i` a private Cauchy
modulus `reg i` — so that sequences whose per-term inner modulus grows with `i`
(Riemann sums, …) are admissible.  All fields are `Type`-level data. -/
structure ModCauchyIdx (s : Nat → CReal) where
  /-- Outer Cauchy modulus, `Type`-level data (identical to `ModCauchy.M`). -/
  M : Q' → Nat
  /-- Index-indexed inner regularity modulus, `Type`-level data. -/
  reg : Nat → Q' → Nat
  /-- Outer uniform two-sided bound (identical to `ModCauchy.bound`). -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
    ∀ k : Nat, (s m).approx k ≤ (s n).approx k + ε ∧ (s n).approx k ≤ (s m).approx k + ε
  /-- Index-indexed inner regularity: each term `s i` is Cauchy with its OWN
  modulus `reg i`. -/
  regular : ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg i ε ≤ p → reg i ε ≤ qq →
    (s i).approx p ≤ (s i).approx qq + ε ∧ (s i).approx qq ≤ (s i).approx p + ε
  /-- The outer modulus is antitone (identical to `ModCauchy.Mmono`). -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ

/-- **Free coercion `ModCauchy → ModCauchyIdx`.**  An index-FREE inner modulus is
an index-indexed one that ignores the index.  (The converse is the point: a
growing-modulus sequence has `ModCauchyIdx` but not `ModCauchy`.) -/
def modCauchy_to_idx {s : Nat → CReal} (c : ModCauchy s) : ModCauchyIdx s where
  M := c.M
  reg := fun _ => c.reg
  bound := c.bound
  regular := fun i => c.regular i
  Mmono := c.Mmono

/-! ## 2. The diagonal data -/

/-- Running-max of `M (invSucc 0), …, M (invSucc k)` — monotone, dominating each
(identical shape to `CReal.Mhat`, for the `ModCauchyIdx` outer modulus). -/
def MhatI (s : Nat → CReal) (c : ModCauchyIdx s) : Nat → Nat
  | 0 => c.M (Q'.invSucc 0)
  | k + 1 => max (MhatI s c k) (c.M (Q'.invSucc (k + 1)))

theorem MhatI_mono_succ (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) :
    MhatI s c k ≤ MhatI s c (k + 1) := Nat.le_max_left _ _

theorem MhatI_mono (s : Nat → CReal) (c : ModCauchyIdx s) {a b : Nat} (h : a ≤ b) :
    MhatI s c a ≤ MhatI s c b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (MhatI_mono_succ s c b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

/-- `c.M (invSucc k) ≤ MhatI s c k`. -/
theorem M_le_MhatI (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) :
    c.M (Q'.invSucc k) ≤ MhatI s c k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The **index-absorbing approximation index** for diagonal step `k`:
`RhatIdx k = max k (reg (MhatI k) (invSucc k))`.  The first argument keeps the
index `≥ k` (so the diagonal resolves); the second absorbs the per-term inner
modulus of the (known) term `s (MhatI k)` at scale `invSucc k`. -/
def RhatIdx (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) : Nat :=
  max k (c.reg (MhatI s c k) (Q'.invSucc k))

theorem k_le_RhatIdx (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) :
    k ≤ RhatIdx s c k := Nat.le_max_left _ _

theorem reg_le_RhatIdx (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) :
    c.reg (MhatI s c k) (Q'.invSucc k) ≤ RhatIdx s c k := Nat.le_max_right _ _

/-- The monotone-shifted, index-absorbing diagonal
`D k = (s (MhatI k)).approx (RhatIdx k)`. -/
def diagSeqIdx (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) : Q' :=
  (s (MhatI s c k)).approx (RhatIdx s c k)

/-! ## 3. The diagonal is Cauchy -/

/-- The directed core bound on the index-indexed diagonal.  For `a ≤ b` with
`a, b ≥ q.den` (`q = ¼ε`, so `invSucc a ≤ q` and `invSucc b ≤ invSucc a ≤ q`),
`|D a − D b| ≤ ε`.  Three bridges at the common index `big = max (RhatIdx a)
(RhatIdx b)`:
  * inner regularity of `s (MhatI a)` (scale `invSucc a`) between `RhatIdx a` and
    `big` — valid since `RhatIdx a, big ≥ reg (MhatI a) (invSucc a)`;
  * the OUTER bound (scale `invSucc a`) comparing `s (MhatI a)` and `s (MhatI b)`
    at `big`;
  * inner regularity of `s (MhatI b)` (scale `invSucc b ≤ invSucc a`) between
    `big` and `RhatIdx b`.
Each `≤ invSucc a ≤ q`, and `3q ≤ ε`. -/
theorem diagSeqIdx_directed (s : Nat → CReal) (c : ModCauchyIdx s)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∀ a b : Nat, a ≤ b → (half * (half * ε)).den ≤ a →
      diagSeqIdx s c a ≤ diagSeqIdx s c b + ε ∧ diagSeqIdx s c b ≤ diagSeqIdx s c a + ε := by
  intro a b hab hNa
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  -- scales
  have hinvapos : (0 : Q') < Q'.invSucc a := Q'.invSucc_pos a
  have hinva : Q'.invSucc a ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hNa) (HalfPow.invSucc_den_le q hqpos)
  have hinvbpos : (0 : Q') < Q'.invSucc b := Q'.invSucc_pos b
  have hinvb_a : Q'.invSucc b ≤ Q'.invSucc a := ExpNeg.invSucc_le_of_le hab
  have hinvb : Q'.invSucc b ≤ q := Q'.le_trans' _ _ _ hinvb_a hinva
  -- the common large index
  let big : Nat := max (RhatIdx s c a) (RhatIdx s c b)
  have hRa_big : RhatIdx s c a ≤ big := Nat.le_max_left _ _
  have hRb_big : RhatIdx s c b ≤ big := Nat.le_max_right _ _
  -- inner-modulus availabilities
  have hregA : c.reg (MhatI s c a) (Q'.invSucc a) ≤ RhatIdx s c a := reg_le_RhatIdx s c a
  have hregA_big : c.reg (MhatI s c a) (Q'.invSucc a) ≤ big := Nat.le_trans hregA hRa_big
  have hregB : c.reg (MhatI s c b) (Q'.invSucc b) ≤ RhatIdx s c b := reg_le_RhatIdx s c b
  have hregB_big : c.reg (MhatI s c b) (Q'.invSucc b) ≤ big := Nat.le_trans hregB hRb_big
  -- outer availabilities
  have hMa : c.M (Q'.invSucc a) ≤ MhatI s c a := M_le_MhatI s c a
  have hMb : c.M (Q'.invSucc a) ≤ MhatI s c b := Nat.le_trans hMa (MhatI_mono s c hab)
  -- (I) inner reg of s(MhatI a) at scale invSucc a between RhatIdx a and big
  obtain ⟨hIa1, hIa2⟩ :=
    c.regular (MhatI s c a) (Q'.invSucc a) hinvapos (RhatIdx s c a) big hregA hregA_big
  -- (O) outer at scale invSucc a comparing s(MhatI a), s(MhatI b) at index big
  obtain ⟨hO1, hO2⟩ := c.bound (Q'.invSucc a) hinvapos (MhatI s c a) (MhatI s c b) hMa hMb big
  -- (II) inner reg of s(MhatI b) at scale invSucc b between big and RhatIdx b
  obtain ⟨hIb1, hIb2⟩ :=
    c.regular (MhatI s c b) (Q'.invSucc b) hinvbpos big (RhatIdx s c b) hregB_big hregB
  -- rescale each step to q
  have hIa1' : (s (MhatI s c a)).approx (RhatIdx s c a)
      ≤ (s (MhatI s c a)).approx big + q :=
    Q'.le_trans' _ _ _ hIa1 (Q'.add_le_add_left _ _ q hinva)
  have hIa2' : (s (MhatI s c a)).approx big
      ≤ (s (MhatI s c a)).approx (RhatIdx s c a) + q :=
    Q'.le_trans' _ _ _ hIa2 (Q'.add_le_add_left _ _ q hinva)
  have hO1' : (s (MhatI s c a)).approx big ≤ (s (MhatI s c b)).approx big + q :=
    Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_left _ _ q hinva)
  have hO2' : (s (MhatI s c b)).approx big ≤ (s (MhatI s c a)).approx big + q :=
    Q'.le_trans' _ _ _ hO2 (Q'.add_le_add_left _ _ q hinva)
  have hIb1' : (s (MhatI s c b)).approx big
      ≤ (s (MhatI s c b)).approx (RhatIdx s c b) + q :=
    Q'.le_trans' _ _ _ hIb1 (Q'.add_le_add_left _ _ q hinvb)
  have hIb2' : (s (MhatI s c b)).approx (RhatIdx s c b)
      ≤ (s (MhatI s c b)).approx big + q :=
    Q'.le_trans' _ _ _ hIb2 (Q'.add_le_add_left _ _ q hinvb)
  -- `3q ≤ ε` collapse: ((w + q) + q) + q ≤ w + ε
  have hqq_half : q + q ≤ half * ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves (half * ε))) ?_
    exact Q'.le_refl' _
  have h3q : ∀ w : Q', ((w + q) + q) + q ≤ w + ε := by
    intro w
    -- ((w+q)+q)+q ≃ w + ((q+q)+q) ≤ w + ((½ε)+q) ≤ w + ((½ε)+(½ε)) ≃ w + ε
    have hreassoc : (((w + q) + q) + q).eqv (w + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (w + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w q (q + q)) ?_
      exact Q'.add_eqv_congr_left w (q + (q + q)) ((q + q) + q)
        (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    refine Q'.add_le_add_left w ((q + q) + q) ε ?_
    -- (q+q)+q ≤ (½ε)+q ≤ (½ε)+(½ε) ≃ ε
    have hstep1 : (q + q) + q ≤ (half * ε) + q :=
      Q'.add_le_add_right (q + q) (half * ε) q hqq_half
    have hqle : q ≤ half * ε := by
      -- q = ½(½ε) ≤ ½ε since ½ε ≤ ½ε + ½ε and q+q ≤ ½ε
      refine Q'.le_trans' _ _ _ ?_ hqq_half
      exact Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hqpos)
    have hstep2 : (half * ε) + q ≤ (half * ε) + (half * ε) :=
      Q'.add_le_add_left (half * ε) q (half * ε) hqle
    refine Q'.le_trans' _ _ _ hstep1 ?_
    refine Q'.le_trans' _ _ _ hstep2 ?_
    exact Q'.le_of_eqv (ExpNeg.two_halves ε)
  refine ⟨?_, ?_⟩
  · -- D a → big(a) → big(b) → D b, three q-steps
    have hchain : diagSeqIdx s c a
        ≤ (((s (MhatI s c b)).approx (RhatIdx s c b) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hIa1' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1') ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hIb1')
    exact Q'.le_trans' _ _ _ hchain (h3q (diagSeqIdx s c b))
  · -- D b → big(b) → big(a) → D a, three q-steps
    have hchain : diagSeqIdx s c b
        ≤ (((s (MhatI s c a)).approx (RhatIdx s c a) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hIb2' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2') ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hIa2')
    exact Q'.le_trans' _ _ _ hchain (h3q (diagSeqIdx s c a))

/-- **The index-indexed completeness limit.**  The index-absorbing diagonal of an
index-indexed modulus-Cauchy `CReal` sequence is a `CReal`. -/
def completeLimitIdx (s : Nat → CReal) (c : ModCauchyIdx s) : CReal where
  approx k := diagSeqIdx s c k
  cauchy := by
    intro ε hε
    refine ⟨(half * (half * ε)).den, fun a b ha hb => ?_⟩
    rcases Nat.le_total a b with hab | hba
    · exact diagSeqIdx_directed s c ε hε a b hab ha
    · have h := diagSeqIdx_directed s c ε hε b a hba hb
      exact ⟨h.2, h.1⟩

@[simp] theorem completeLimitIdx_approx (s : Nat → CReal) (c : ModCauchyIdx s) (k : Nat) :
    (completeLimitIdx s c).approx k = (s (MhatI s c k)).approx (RhatIdx s c k) := rfl

/-! ## 4. The diagonal limit is the limit of `s` -/

/-- **`ConvergesTo s (completeLimitIdx s c)`.**  At scale `ε`, work at `q = ½ε`.
Stage `Nstage = c.M q`.  For a term `N ≥ Nstage` and approx index `n ≥ Napx :=
max (reg N q) q.den`, bridge `(s N)_n → (s N)_{RhatIdx n} → (s (MhatI n))_{RhatIdx
n} = L_n`:
  * inner regularity of the FIXED term `s N` (scale `q`) between `n` and
    `RhatIdx n ≥ n` — valid since `n ≥ reg N q`;
  * the OUTER bound (scale `q`) comparing `s N` and `s (MhatI n)` at index
    `RhatIdx n` (`M q ≤ N`, and `M q ≤ M (invSucc n) ≤ MhatI n` since
    `invSucc n ≤ q`).
Two `q`-steps, `2q ≤ ε`. -/
theorem convergesTo_completeLimitIdx (s : Nat → CReal) (c : ModCauchyIdx s) :
    ConvergesTo s (completeLimitIdx s c) := by
  intro ε hε
  let q : Q' := half * ε
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  refine ⟨c.M q, fun N hN => ⟨max (c.reg N q) q.den, fun n hn => ?_⟩⟩
  have hregNn : c.reg N q ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hqdenn : q.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hn_R : n ≤ RhatIdx s c n := k_le_RhatIdx s c n
  have hregNR : c.reg N q ≤ RhatIdx s c n := Nat.le_trans hregNn hn_R
  -- invSucc n ≤ q
  have hinvn : Q'.invSucc n ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn) (HalfPow.invSucc_den_le q hqpos)
  have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
  -- M q ≤ MhatI n
  have hMqn : c.M q ≤ MhatI s c n :=
    Nat.le_trans (c.Mmono q (Q'.invSucc n) hinvnpos hinvn) (M_le_MhatI s c n)
  -- (I) inner reg of s N at scale q between n and RhatIdx n
  obtain ⟨hI1, hI2⟩ := c.regular N q hqpos n (RhatIdx s c n) hregNn hregNR
  -- (O) outer at scale q comparing s N, s (MhatI n) at index RhatIdx n
  obtain ⟨hO1, hO2⟩ := c.bound q hqpos N (MhatI s c n) hN hMqn (RhatIdx s c n)
  -- `2q ≤ ε` collapse: (w + q) + q ≤ w + ε
  have h2q : ∀ w : Q', (w + q) + q ≤ w + ε := by
    intro w
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv w q q)) ?_
    exact Q'.add_le_add_left w (q + q) ε (Q'.le_of_eqv (ExpNeg.two_halves ε))
  refine ⟨?_, ?_⟩
  · -- (s N)_n ≤ (s N)_{RhatIdx n} + q ≤ ((s (MhatI n))_{RhatIdx n} + q) + q ≤ L_n + ε
    show (s N).approx n ≤ (completeLimitIdx s c).approx n + ε
    have hchain : (s N).approx n
        ≤ ((s (MhatI s c n)).approx (RhatIdx s c n) + q) + q :=
      Q'.le_trans' _ _ _ hI1 (Q'.add_le_add_right _ _ q hO1)
    exact Q'.le_trans' _ _ _ hchain (h2q ((s (MhatI s c n)).approx (RhatIdx s c n)))
  · -- L_n = (s (MhatI n))_{RhatIdx n} ≤ (s N)_{RhatIdx n} + q ≤ ((s N)_n + q) + q ≤ (s N)_n + ε
    show (completeLimitIdx s c).approx n ≤ (s N).approx n + ε
    have hchain : (s (MhatI s c n)).approx (RhatIdx s c n)
        ≤ ((s N).approx n + q) + q :=
      Q'.le_trans' _ _ _ hO2 (Q'.add_le_add_right _ _ q hI2)
    exact Q'.le_trans' _ _ _ hchain (h2q ((s N).approx n))

/-! ## 5. Bound-passing to the diagonal limit -/

/-- **Lower bound passes to the limit.** -/
theorem leEv_ofQ'_completeLimitIdx (s : Nat → CReal) (c : ModCauchyIdx s) {lb : Q'}
    (h : ∀ k j : Nat, lb ≤ (s k).approx j) :
    leEv (ofQ' lb) (completeLimitIdx s c) :=
  leEv_ofQ'_of_approx_ge (fun n => h (MhatI s c n) (RhatIdx s c n))

/-- **Upper bound passes to the limit.** -/
theorem leEv_completeLimitIdx_ofQ' (s : Nat → CReal) (c : ModCauchyIdx s) {ub : Q'}
    (h : ∀ k j : Nat, (s k).approx j ≤ ub) :
    leEv (completeLimitIdx s c) (ofQ' ub) :=
  leEv_le_ofQ'_of_approx_le (fun n => h (MhatI s c n) (RhatIdx s c n))

/-- **Strict positivity passes to the limit (eventual form).** -/
theorem isPositiveEv_completeLimitIdx (s : Nat → CReal) (c : ModCauchyIdx s) {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ k j : Nat, ε ≤ (s k).approx j) :
    (0 : Q') < ε ∧ leEv (ofQ' ε) (completeLimitIdx s c) :=
  ⟨hε, leEv_ofQ'_completeLimitIdx s c h⟩

end CReal

/-! ## 6. Non-vacuity demo

The constant `CReal` sequence at `ofQ' 1`, viewed through the index-indexed
interface via `modCauchy_to_idx`, converges to its limit. -/

namespace CReal

/-- The index-indexed datum for the constant sequence (via the free coercion). -/
def constSeqModCauchyIdx : ModCauchyIdx constSeq := modCauchy_to_idx constSeqModCauchy

/-- The index-indexed completeness limit of the constant `ofQ' 1` sequence. -/
def demoConstLimitIdx : CReal := completeLimitIdx constSeq constSeqModCauchyIdx

/-- The machinery is non-vacuous: the constant sequence converges to its
index-indexed limit. -/
theorem demoConstLimitIdx_converges : ConvergesTo constSeq demoConstLimitIdx :=
  convergesTo_completeLimitIdx constSeq constSeqModCauchyIdx

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.CReal.modCauchy_to_idx
#print axioms ConstructiveReals.CReal.MhatI_mono
#print axioms ConstructiveReals.CReal.M_le_MhatI
#print axioms ConstructiveReals.CReal.diagSeqIdx_directed
#print axioms ConstructiveReals.CReal.completeLimitIdx
#print axioms ConstructiveReals.CReal.completeLimitIdx_approx
#print axioms ConstructiveReals.CReal.convergesTo_completeLimitIdx
#print axioms ConstructiveReals.CReal.leEv_ofQ'_completeLimitIdx
#print axioms ConstructiveReals.CReal.leEv_completeLimitIdx_ofQ'
#print axioms ConstructiveReals.CReal.isPositiveEv_completeLimitIdx
#print axioms ConstructiveReals.CReal.demoConstLimitIdx_converges
