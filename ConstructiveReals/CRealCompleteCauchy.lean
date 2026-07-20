/-
# CReal-level (eventual-in-approx) completeness backbone for `CReal`

This module is the third completeness backbone for the Bishop-style regular
reals `CReal`, sitting alongside `CReal.completeLimit` (index-FREE inner modulus)
and `CReal.completeLimitIdx` (index-INDEXED inner modulus).  The difference is in
the OUTER datum: both prior backbones demand the outer two-sided bound to hold at
EVERY approximation index `k` simultaneously

    ∀ k, |(s m).approx k − (s n).approx k| ≤ ε              (all-`k`),

whereas this backbone relaxes the outer bound to the genuine CReal-level
(Bishop) form: for `m, n ≥ M ε` there is an approximation threshold `K` past
which the approximations agree,

    ∃ K, ∀ k ≥ K, |(s m).approx k − (s n).approx k| ≤ ε     (eventual-in-`k`).

## Why this exists (the all-`k` obstruction)

For a Riemann sequence `semiSum n` of `√(1 − x²)` the natural inter-resolution
estimate (the √-Hölder mesh error) is CReal-level: it controls the LIMITS of two
Riemann sums, i.e. it is eventual in the approximation index `k`.  The all-`k`
form is delicate near the integrand's slow points (the Heron iterate of `√` of a
near-zero radicand is a crude rational at small `k`), so the all-`k` outer bound
need NOT hold.  The eventual-in-`k` form is exactly the natural Riemann estimate
and is what Bishop completeness of a Cauchy sequence of reals consumes.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `ModCauchyEv s` — the eventual-outer modulus-Cauchy datum (inner `reg`
    index-indexed, identical to `ModCauchyIdx.reg`; the antitone outer modulus
    `M` identical; the outer `bound` relaxed to the eventual-in-`k` form).
  * `modCauchyIdx_to_ev : ModCauchyIdx s → ModCauchyEv s` — the free coercion
    (an all-`k` outer bound IS an eventual one with threshold `0`); the POINT is
    the converse direction (the eventual form is inhabitable when all-`k` is not).
  * `completeLimitCauchy s c : CReal` — the diagonal limit (same index-absorbing
    diagonal as `completeLimitIdx`), with `cauchy` re-proved from the
    eventual outer bound by enlarging the common bridging index past the
    per-pair outer threshold.
  * `convergesTo_completeLimitCauchy : ConvergesTo s (completeLimitCauchy s c)`.
  * bound-passing: `leEv_ofQ'_completeLimitCauchy`,
    `leEv_completeLimitCauchy_ofQ'`, `isPositiveEv_completeLimitCauchy`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Every load-bearing declaration reports `[propext]` or
`[propext, Quot.sound]` (the latter only via reused `Nat`/`omega` helpers).
-/

import ConstructiveReals.CRealCompleteIdx

namespace ConstructiveReals

open ConstructiveReals
open ConstructiveReals.HalfPow

namespace CReal

open Q'

/-! ## 1. The eventual-outer modulus-Cauchy datum -/

/-- An **eventual-outer** uniform-rate modulus-Cauchy datum for a `CReal`
sequence `s`.  The INNER regularity modulus `reg : Nat → Q' → Nat` and the
antitone outer modulus `M` are identical to `ModCauchyIdx`.  The OUTER two-sided
bound is relaxed to the genuine CReal-level (Bishop) form: for `m, n ≥ M ε`, the
approximations agree past some approximation threshold `K = boundK ε m n`.  All
fields are `Type`-level data. -/
structure ModCauchyEv (s : Nat → CReal) where
  /-- Outer Cauchy modulus, `Type`-level data (identical to `ModCauchyIdx.M`). -/
  M : Q' → Nat
  /-- Index-indexed inner regularity modulus (identical to `ModCauchyIdx.reg`). -/
  reg : Nat → Q' → Nat
  /-- The per-pair approximation threshold for the eventual outer bound. -/
  boundK : Q' → Nat → Nat → Nat
  /-- Eventual-in-`k` outer two-sided bound: for `m, n ≥ M ε`, the
  approximations agree to within `ε` for every approx index `k ≥ boundK ε m n`. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
    ∀ k : Nat, boundK ε m n ≤ k →
      (s m).approx k ≤ (s n).approx k + ε ∧ (s n).approx k ≤ (s m).approx k + ε
  /-- Index-indexed inner regularity (identical to `ModCauchyIdx.regular`). -/
  regular : ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg i ε ≤ p → reg i ε ≤ qq →
    (s i).approx p ≤ (s i).approx qq + ε ∧ (s i).approx qq ≤ (s i).approx p + ε
  /-- The outer modulus is antitone (identical to `ModCauchyIdx.Mmono`). -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ

/-- **Free coercion `ModCauchyIdx → ModCauchyEv`.**  An all-`k` outer bound is an
eventual one with threshold `0`.  (The converse is the point: a Riemann sequence
has `ModCauchyEv` but need not have `ModCauchyIdx`, because the all-`k` outer
bound can fail at small `k`.) -/
def modCauchyIdx_to_ev {s : Nat → CReal} (c : ModCauchyIdx s) : ModCauchyEv s where
  M := c.M
  reg := c.reg
  boundK := fun _ _ _ => 0
  bound := fun ε hε m n hm hn k _ => c.bound ε hε m n hm hn k
  regular := c.regular
  Mmono := c.Mmono

/-! ## 2. The diagonal data (identical shape to `completeLimitIdx`) -/

/-- Running-max of the outer modulus (identical to `MhatI`). -/
def MhatE (s : Nat → CReal) (c : ModCauchyEv s) : Nat → Nat
  | 0 => c.M (Q'.invSucc 0)
  | k + 1 => max (MhatE s c k) (c.M (Q'.invSucc (k + 1)))

theorem MhatE_mono_succ (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) :
    MhatE s c k ≤ MhatE s c (k + 1) := Nat.le_max_left _ _

theorem MhatE_mono (s : Nat → CReal) (c : ModCauchyEv s) {a b : Nat} (h : a ≤ b) :
    MhatE s c a ≤ MhatE s c b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (MhatE_mono_succ s c b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

theorem M_le_MhatE (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) :
    c.M (Q'.invSucc k) ≤ MhatE s c k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The index-absorbing approximation index (identical shape to `RhatIdx`). -/
def RhatE (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) : Nat :=
  max k (c.reg (MhatE s c k) (Q'.invSucc k))

theorem k_le_RhatE (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) :
    k ≤ RhatE s c k := Nat.le_max_left _ _

theorem reg_le_RhatE (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) :
    c.reg (MhatE s c k) (Q'.invSucc k) ≤ RhatE s c k := Nat.le_max_right _ _

/-- The monotone-shifted, index-absorbing diagonal. -/
def diagSeqEv (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) : Q' :=
  (s (MhatE s c k)).approx (RhatE s c k)

/-! ## 3. The diagonal is Cauchy

The proof is `diagSeqIdx_directed` with one structural change: the common
bridging index `big` is enlarged to also exceed the per-pair eventual outer
threshold `boundK (invSucc a) (MhatE a) (MhatE b)`, so the (now eventual) outer
bound is applicable at `big`.  The inner-regularity bridges still hold because
`big` only grew (each inner-regularity hypothesis `… ≤ big` is monotone in
`big`). -/

/-- The directed core bound on the eventual-outer diagonal.  For `a ≤ b` with
`a, b ≥ q.den` (`q = ¼ε`), `|D a − D b| ≤ ε`, via the three bridges of
`diagSeqIdx_directed` at the enlarged common index
`big = max (max (RhatE a) (RhatE b)) (boundK (invSucc a) (MhatE a) (MhatE b))`. -/
theorem diagSeqEv_directed (s : Nat → CReal) (c : ModCauchyEv s)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∀ a b : Nat, a ≤ b → (half * (half * ε)).den ≤ a →
      diagSeqEv s c a ≤ diagSeqEv s c b + ε ∧ diagSeqEv s c b ≤ diagSeqEv s c a + ε := by
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
  -- the common large index: max of the two RhatE plus the eventual-outer threshold
  let Kab : Nat := c.boundK (Q'.invSucc a) (MhatE s c a) (MhatE s c b)
  let big : Nat := max (max (RhatE s c a) (RhatE s c b)) Kab
  have hRab_big : max (RhatE s c a) (RhatE s c b) ≤ big := Nat.le_max_left _ _
  have hRa_big : RhatE s c a ≤ big := Nat.le_trans (Nat.le_max_left _ _) hRab_big
  have hRb_big : RhatE s c b ≤ big := Nat.le_trans (Nat.le_max_right _ _) hRab_big
  have hK_big : Kab ≤ big := Nat.le_max_right _ _
  -- inner-modulus availabilities
  have hregA : c.reg (MhatE s c a) (Q'.invSucc a) ≤ RhatE s c a := reg_le_RhatE s c a
  have hregA_big : c.reg (MhatE s c a) (Q'.invSucc a) ≤ big := Nat.le_trans hregA hRa_big
  have hregB : c.reg (MhatE s c b) (Q'.invSucc b) ≤ RhatE s c b := reg_le_RhatE s c b
  have hregB_big : c.reg (MhatE s c b) (Q'.invSucc b) ≤ big := Nat.le_trans hregB hRb_big
  -- outer availabilities
  have hMa : c.M (Q'.invSucc a) ≤ MhatE s c a := M_le_MhatE s c a
  have hMb : c.M (Q'.invSucc a) ≤ MhatE s c b := Nat.le_trans hMa (MhatE_mono s c hab)
  -- (I) inner reg of s(MhatE a) at scale invSucc a between RhatE a and big
  obtain ⟨hIa1, hIa2⟩ :=
    c.regular (MhatE s c a) (Q'.invSucc a) hinvapos (RhatE s c a) big hregA hregA_big
  -- (O) eventual outer at scale invSucc a comparing s(MhatE a), s(MhatE b) at big ≥ Kab
  obtain ⟨hO1, hO2⟩ :=
    c.bound (Q'.invSucc a) hinvapos (MhatE s c a) (MhatE s c b) hMa hMb big hK_big
  -- (II) inner reg of s(MhatE b) at scale invSucc b between big and RhatE b
  obtain ⟨hIb1, hIb2⟩ :=
    c.regular (MhatE s c b) (Q'.invSucc b) hinvbpos big (RhatE s c b) hregB_big hregB
  -- rescale each step to q
  have hIa1' : (s (MhatE s c a)).approx (RhatE s c a)
      ≤ (s (MhatE s c a)).approx big + q :=
    Q'.le_trans' _ _ _ hIa1 (Q'.add_le_add_left _ _ q hinva)
  have hIa2' : (s (MhatE s c a)).approx big
      ≤ (s (MhatE s c a)).approx (RhatE s c a) + q :=
    Q'.le_trans' _ _ _ hIa2 (Q'.add_le_add_left _ _ q hinva)
  have hO1' : (s (MhatE s c a)).approx big ≤ (s (MhatE s c b)).approx big + q :=
    Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_left _ _ q hinva)
  have hO2' : (s (MhatE s c b)).approx big ≤ (s (MhatE s c a)).approx big + q :=
    Q'.le_trans' _ _ _ hO2 (Q'.add_le_add_left _ _ q hinva)
  have hIb1' : (s (MhatE s c b)).approx big
      ≤ (s (MhatE s c b)).approx (RhatE s c b) + q :=
    Q'.le_trans' _ _ _ hIb1 (Q'.add_le_add_left _ _ q hinvb)
  have hIb2' : (s (MhatE s c b)).approx (RhatE s c b)
      ≤ (s (MhatE s c b)).approx big + q :=
    Q'.le_trans' _ _ _ hIb2 (Q'.add_le_add_left _ _ q hinvb)
  -- `3q ≤ ε` collapse: ((w + q) + q) + q ≤ w + ε
  have hqq_half : q + q ≤ half * ε := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves (half * ε))) ?_
    exact Q'.le_refl' _
  have h3q : ∀ w : Q', ((w + q) + q) + q ≤ w + ε := by
    intro w
    have hreassoc : (((w + q) + q) + q).eqv (w + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (w + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w q (q + q)) ?_
      exact Q'.add_eqv_congr_left w (q + (q + q)) ((q + q) + q)
        (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    refine Q'.add_le_add_left w ((q + q) + q) ε ?_
    have hstep1 : (q + q) + q ≤ (half * ε) + q :=
      Q'.add_le_add_right (q + q) (half * ε) q hqq_half
    have hqle : q ≤ half * ε := by
      refine Q'.le_trans' _ _ _ ?_ hqq_half
      exact Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hqpos)
    have hstep2 : (half * ε) + q ≤ (half * ε) + (half * ε) :=
      Q'.add_le_add_left (half * ε) q (half * ε) hqle
    refine Q'.le_trans' _ _ _ hstep1 ?_
    refine Q'.le_trans' _ _ _ hstep2 ?_
    exact Q'.le_of_eqv (ExpNeg.two_halves ε)
  refine ⟨?_, ?_⟩
  · have hchain : diagSeqEv s c a
        ≤ (((s (MhatE s c b)).approx (RhatE s c b) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hIa1' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1') ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hIb1')
    exact Q'.le_trans' _ _ _ hchain (h3q (diagSeqEv s c b))
  · have hchain : diagSeqEv s c b
        ≤ (((s (MhatE s c a)).approx (RhatE s c a) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hIb2' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2') ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hIa2')
    exact Q'.le_trans' _ _ _ hchain (h3q (diagSeqEv s c a))

/-- **The eventual-outer completeness limit.**  The index-absorbing diagonal of
an eventual-outer modulus-Cauchy `CReal` sequence is a `CReal`. -/
def completeLimitCauchy (s : Nat → CReal) (c : ModCauchyEv s) : CReal where
  approx k := diagSeqEv s c k
  cauchy := by
    intro ε hε
    refine ⟨(half * (half * ε)).den, fun a b ha hb => ?_⟩
    rcases Nat.le_total a b with hab | hba
    · exact diagSeqEv_directed s c ε hε a b hab ha
    · have h := diagSeqEv_directed s c ε hε b a hba hb
      exact ⟨h.2, h.1⟩

@[simp] theorem completeLimitCauchy_approx (s : Nat → CReal) (c : ModCauchyEv s) (k : Nat) :
    (completeLimitCauchy s c).approx k = (s (MhatE s c k)).approx (RhatE s c k) := rfl

/-! ## 4. The diagonal limit is the limit of `s`

Same as `convergesTo_completeLimitIdx`, except the outer bound comparing the
fixed term `s N` to `s (MhatE n)` is now eventual, so the bridging approx index
is enlarged past the per-pair threshold `boundK q N (MhatE n)`. -/

/-- **`ConvergesTo s (completeLimitCauchy s c)`.**  At scale `ε`, work at
`q = ¼ε`, stage `c.M q`.  For `N ≥ c.M q` and approx index
`n ≥ max (reg N q) q.den`, bridge `(s N)_n → (s N)_J → (s (MhatE n))_J → (s
(MhatE n))_{RhatE n} = L_n` at the enlarged index `J = max (RhatE n) (boundK q N
(MhatE n))`:
  * inner regularity of `s N` (scale `q`) between `n` and `J` (both `≥ reg N q`);
  * the EVENTUAL outer bound (scale `q`) comparing `s N`, `s (MhatE n)` at `J ≥
    boundK q N (MhatE n)`;
  * inner regularity of `s (MhatE n)` (scale `invSucc n ≤ q`) between `J` and
    `RhatE n` (both `≥ reg (MhatE n) (invSucc n)`).
Three `q`-steps, `3q ≤ ε`. -/
theorem convergesTo_completeLimitCauchy (s : Nat → CReal) (c : ModCauchyEv s) :
    ConvergesTo s (completeLimitCauchy s c) := by
  intro ε hε
  let q : Q' := half * (half * ε)
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
  refine ⟨c.M q, fun N hN => ?_⟩
  refine ⟨max (c.reg N q) q.den, fun n hn => ?_⟩
  have hregNn : c.reg N q ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hqdenn : q.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- invSucc n ≤ q
  have hinvn : Q'.invSucc n ≤ q :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hqdenn) (HalfPow.invSucc_den_le q hqpos)
  have hinvnpos : (0 : Q') < Q'.invSucc n := Q'.invSucc_pos n
  -- the enlarged bridging index
  let Kpair : Nat := c.boundK q N (MhatE s c n)
  let J : Nat := max (RhatE s c n) Kpair
  have hRn_J : RhatE s c n ≤ J := Nat.le_max_left _ _
  have hK_J : Kpair ≤ J := Nat.le_max_right _ _
  have hn_R : n ≤ RhatE s c n := k_le_RhatE s c n
  have hregN_R : c.reg N q ≤ RhatE s c n := Nat.le_trans hregNn hn_R
  have hregN_J : c.reg N q ≤ J := Nat.le_trans hregN_R hRn_J
  -- inner modulus of s (MhatE n) at scale invSucc n
  have hregMn_R : c.reg (MhatE s c n) (Q'.invSucc n) ≤ RhatE s c n := reg_le_RhatE s c n
  have hregMn_J : c.reg (MhatE s c n) (Q'.invSucc n) ≤ J := Nat.le_trans hregMn_R hRn_J
  -- M q ≤ MhatE n
  have hMqn : c.M q ≤ MhatE s c n :=
    Nat.le_trans (c.Mmono q (Q'.invSucc n) hinvnpos hinvn) (M_le_MhatE s c n)
  -- (I) inner reg of s N at scale q between n and J
  obtain ⟨hI1, hI2⟩ := c.regular N q hqpos n J hregNn hregN_J
  -- (O) eventual outer at scale q comparing s N, s (MhatE n) at J ≥ Kpair
  obtain ⟨hO1, hO2⟩ := c.bound q hqpos N (MhatE s c n) hN hMqn J hK_J
  -- (II) inner reg of s (MhatE n) at scale invSucc n between J and RhatE n
  obtain ⟨hII1, hII2⟩ :=
    c.regular (MhatE s c n) (Q'.invSucc n) hinvnpos J (RhatE s c n) hregMn_J hregMn_R
  -- rescale step (II) to q
  have hII1' : (s (MhatE s c n)).approx J ≤ (s (MhatE s c n)).approx (RhatE s c n) + q :=
    Q'.le_trans' _ _ _ hII1 (Q'.add_le_add_left _ _ q hinvn)
  have hII2' : (s (MhatE s c n)).approx (RhatE s c n) ≤ (s (MhatE s c n)).approx J + q :=
    Q'.le_trans' _ _ _ hII2 (Q'.add_le_add_left _ _ q hinvn)
  -- `3q ≤ ε` collapse
  have h3q : ∀ w : Q', ((w + q) + q) + q ≤ w + ε := by
    intro w
    have hreassoc : (((w + q) + q) + q).eqv (w + ((q + q) + q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (w + q) q q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv w q (q + q)) ?_
      exact Q'.add_eqv_congr_left w (q + (q + q)) ((q + q) + q)
        (Q'.eqv_symm (Q'.add_assoc_eqv q q q))
    have hqq_half : q + q ≤ half * ε := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.two_halves (half * ε))) ?_
      exact Q'.le_refl' _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hreassoc) ?_
    refine Q'.add_le_add_left w ((q + q) + q) ε ?_
    have hstep1 : (q + q) + q ≤ (half * ε) + q :=
      Q'.add_le_add_right (q + q) (half * ε) q hqq_half
    have hqle : q ≤ half * ε := by
      refine Q'.le_trans' _ _ _ ?_ hqq_half
      exact Q'.add_le_self_of_nonneg q q (Q'.le_of_lt hqpos)
    have hstep2 : (half * ε) + q ≤ (half * ε) + (half * ε) :=
      Q'.add_le_add_left (half * ε) q (half * ε) hqle
    refine Q'.le_trans' _ _ _ hstep1 ?_
    refine Q'.le_trans' _ _ _ hstep2 ?_
    exact Q'.le_of_eqv (ExpNeg.two_halves ε)
  refine ⟨?_, ?_⟩
  · -- (s N)_n ≤ (s N)_J + q ≤ ((s (MhatE n))_J + q) + q ≤ (((s(MhatE n))_{RhatE n}+q)+q)+q ≤ L_n + ε
    show (s N).approx n ≤ (completeLimitCauchy s c).approx n + ε
    have hchain : (s N).approx n
        ≤ (((s (MhatE s c n)).approx (RhatE s c n) + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hI1 ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO1) ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hII1')
    exact Q'.le_trans' _ _ _ hchain (h3q ((s (MhatE s c n)).approx (RhatE s c n)))
  · show (completeLimitCauchy s c).approx n ≤ (s N).approx n + ε
    have hchain : (s (MhatE s c n)).approx (RhatE s c n)
        ≤ (((s N).approx n + q) + q) + q := by
      refine Q'.le_trans' _ _ _ hII2' ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ q hO2) ?_
      exact Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hI2)
    exact Q'.le_trans' _ _ _ hchain (h3q ((s N).approx n))

/-! ## 5. Bound-passing to the diagonal limit -/

/-- **Lower bound passes to the limit.** -/
theorem leEv_ofQ'_completeLimitCauchy (s : Nat → CReal) (c : ModCauchyEv s) {lb : Q'}
    (h : ∀ k j : Nat, lb ≤ (s k).approx j) :
    leEv (ofQ' lb) (completeLimitCauchy s c) :=
  leEv_ofQ'_of_approx_ge (fun n => h (MhatE s c n) (RhatE s c n))

/-- **Upper bound passes to the limit.** -/
theorem leEv_completeLimitCauchy_ofQ' (s : Nat → CReal) (c : ModCauchyEv s) {ub : Q'}
    (h : ∀ k j : Nat, (s k).approx j ≤ ub) :
    leEv (completeLimitCauchy s c) (ofQ' ub) :=
  leEv_le_ofQ'_of_approx_le (fun n => h (MhatE s c n) (RhatE s c n))

/-- **Strict positivity passes to the limit (eventual form).** -/
theorem isPositiveEv_completeLimitCauchy (s : Nat → CReal) (c : ModCauchyEv s) {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ k j : Nat, ε ≤ (s k).approx j) :
    (0 : Q') < ε ∧ leEv (ofQ' ε) (completeLimitCauchy s c) :=
  ⟨hε, leEv_ofQ'_completeLimitCauchy s c h⟩

/-! ## 6. Non-vacuity demo

The constant `CReal` sequence at `ofQ' 1`, routed through the eventual-outer
interface via `modCauchyIdx_to_ev`, converges to its limit. -/

/-- The eventual-outer datum for the constant sequence (via the free coercions). -/
def constSeqModCauchyEv : ModCauchyEv constSeq :=
  modCauchyIdx_to_ev (modCauchy_to_idx constSeqModCauchy)

/-- The eventual-outer completeness limit of the constant `ofQ' 1` sequence. -/
def demoConstLimitCauchy : CReal := completeLimitCauchy constSeq constSeqModCauchyEv

/-- The machinery is non-vacuous: the constant sequence converges to its
eventual-outer limit. -/
theorem demoConstLimitCauchy_converges : ConvergesTo constSeq demoConstLimitCauchy :=
  convergesTo_completeLimitCauchy constSeq constSeqModCauchyEv

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy)

Every load-bearing declaration must report `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`omega` helpers).  No `Classical.*`,
no `native_decide`, no `sorry`. -/

#print axioms ConstructiveReals.CReal.modCauchyIdx_to_ev
#print axioms ConstructiveReals.CReal.MhatE_mono
#print axioms ConstructiveReals.CReal.M_le_MhatE
#print axioms ConstructiveReals.CReal.diagSeqEv_directed
#print axioms ConstructiveReals.CReal.completeLimitCauchy
#print axioms ConstructiveReals.CReal.completeLimitCauchy_approx
#print axioms ConstructiveReals.CReal.convergesTo_completeLimitCauchy
#print axioms ConstructiveReals.CReal.leEv_ofQ'_completeLimitCauchy
#print axioms ConstructiveReals.CReal.leEv_completeLimitCauchy_ofQ'
#print axioms ConstructiveReals.CReal.isPositiveEv_completeLimitCauchy
#print axioms ConstructiveReals.CReal.demoConstLimitCauchy_converges
