/-
**Geometric domination of the decaying exponential** — the constructive
exp machinery the uniform SU(N) character-tail cap needs (atom (B1) of
`docs/sun-uniform-cap-factorization.md`).

# The point

The character tail `S_i = Σ_m (m+1)^{2q} e^{−t h(m)}` is polynomial × Gaussian.
To sum it via `CharacterTail.geom_series_le` one needs the term decay bounded by
a GENUINE geometric `ρ^m` with rational `ρ < 1` — the Padé surrogate
`e^{−x} ≤ 1/(1+x)` is too weak (it makes the polynomial-weighted sum DIVERGE,
`notes/uniform-character-tail-bound.md` §6, because `(m+1)^{2q}/(1+t·m²) ~ m^{2q−2}`).

This module supplies the missing bridge from the continuous exponential to a
discrete geometric:

    e^{−a·m} ≤ ρ^m    for every m,    whenever    e^{−a} ≤ ρ   (ρ < 1).

Proof: induction on `m` via the addition law `e^{−a(m+1)} = e^{−am}·e^{−a}`
(`expNeg_add_equiv`) and `leRat_mul`.  No `CReal` power is needed — the bound is
purely `e^{−am} ≤ ρ^m` with `ρ^m` the rational `Q'.pow`.

Combined with a linear lower bound `h(m) ≥ c·m` (so `e^{−t h(m)} ≤ e^{−(tc)·m}`
by `expNeg` antitonicity) this gives `e^{−t h(m)} ≤ ρ^m`, the genuine geometric
term-decay the polynomial-geometric sum machinery consumes — beating the
`(9/4)^q` polynomial factor the rational bound cannot.

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Soundness
import ConstructiveReals.ExpAdd
import ConstructiveReals.ExpNegCongr
import ConstructiveReals.Geometric
import ConstructiveReals.CRealMulLe
import ConstructiveReals.QPoly

namespace ConstructiveReals

open ConstructiveReals

/-! ## A rational upper bound on `e^{−a}` -/

/-- **`e^{−a} ≤ ρ`** for a rational base `ρ`, given the `Q'` sufficient condition
`oneOver1p a ≤ ρ` (i.e. `1/(1+a) ≤ ρ`, equivalently `a ≥ (1−ρ)/ρ`).  Composes
`expNeg_le_oneOver1p` (`e^{−a} ≤ 1/(1+a)`) with `leRat_mono`. -/
theorem expNeg_le_rat (a ρ : Q') (ha : (0 : Q') ≤ a)
    (hρ : ExpUBInstance.oneOver1p a ≤ ρ) :
    CReal.leRat (ExpNeg.expNeg a ha) ρ :=
  CReal.leRat_mono (expNeg_le_oneOver1p a ha) hρ

/-! ## Geometric domination `e^{−a·m} ≤ ρ^m` -/

/-- `0 ≤ ofNat m`. -/
theorem ofNat_nonneg (m : Nat) : (0 : Q') ≤ Q'.ofNat m := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (Q'.ofNat m).num
  have : (Q'.ofNat m).num = (m : Int) := rfl
  rw [this]; exact Int.natCast_nonneg m

/-- `a · ofNat(m+1) ≃ a · ofNat m + a` — the successor split of the scaled
argument. -/
theorem mul_ofNat_succ_eqv (a : Q') (m : Nat) :
    (a * Q'.ofNat (m + 1)).eqv (a * Q'.ofNat m + a) := by
  -- ofNat(m+1) ≃ ofNat m + 1
  have h1 : (Q'.ofNat (m + 1)).eqv (Q'.ofNat m + 1) := by
    refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv m 1) ?_
    exact Q'.add_eqv_congr_left (Q'.ofNat m) (Q'.ofNat 1) 1 (by decide)
  -- a · ofNat(m+1) ≃ a · (ofNat m + 1) ≃ a·ofNat m + a·1 ≃ a·ofNat m + a
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a (Q'.ofNat m) 1) ?_
  exact Q'.add_eqv_congr_left (a * Q'.ofNat m) (a * 1) a (Q'.mul_one_eqv a)

/-- **Geometric domination of the heat-kernel exponential.**
`e^{−a·m} ≤ ρ^m` for every `m`, given `e^{−a} ≤ ρ` (`a ≥ 0`, `0 ≤ ρ`).

Induction on `m`: the base is `e^{0} ≤ 1`; the step is
`e^{−a(m+1)} = e^{−am}·e^{−a} ≤ ρ^m·ρ = ρ^{m+1}` via the addition law and
`leRat_mul`.  This is the genuine geometric term-decay (rational base `ρ < 1`)
that the polynomial-geometric character-tail sum needs — NOT the too-weak
`1/(1+a)` Padé surrogate. -/
theorem expNeg_mul_le_pow (a ρ : Q') (ha : (0 : Q') ≤ a) (hρ0 : (0 : Q') ≤ ρ)
    (hρ : CReal.leRat (ExpNeg.expNeg a ha) ρ) :
    ∀ m : Nat,
      CReal.leRat
        (ExpNeg.expNeg (a * Q'.ofNat m) (Q'.mul_nonneg a (Q'.ofNat m) ha (ofNat_nonneg m)))
        (ρ ^ m) := by
  intro m
  induction m with
  | zero =>
      -- e^{−(a·0)} ≤ ρ^0 = 1.  a·0 ≃ 0, so e^{−(a·0)} ≃ e^0 ≤ 1.
      have harg : (a * Q'.ofNat 0).eqv 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (by decide)) (QPoly.q_mul_zero a)
      have he : CReal.Equiv
          (ExpNeg.expNeg (a * Q'.ofNat 0)
            (Q'.mul_nonneg a (Q'.ofNat 0) ha (ofNat_nonneg 0)))
          (ExpNeg.expNeg 0 (by decide)) :=
        expNeg_eqv_congr _ (by decide) harg
      have h0 : CReal.leRat (ExpNeg.expNeg 0 (by decide)) (ρ ^ 0) := by
        rw [Q'.pow_zero]
        exact expNeg_le_rat 0 1 (by decide) (by decide)
      exact CReal.leRat_of_equiv he h0
  | succ m ih =>
      -- e^{−a(m+1)} ≃ e^{−(a·m + a)} ≃ e^{−am}·e^{−a} ≤ ρ^m·ρ = ρ^{m+1}.
      have hamnn : (0 : Q') ≤ a * Q'.ofNat m :=
        Q'.mul_nonneg a (Q'.ofNat m) ha (ofNat_nonneg m)
      have hsumnn : (0 : Q') ≤ a * Q'.ofNat m + a := Q'.zero_le_add _ _ hamnn ha
      -- e^{−a(m+1)} ≃ e^{−(a·m + a)}
      have e1 : CReal.Equiv
          (ExpNeg.expNeg (a * Q'.ofNat (m + 1))
            (Q'.mul_nonneg a (Q'.ofNat (m + 1)) ha (ofNat_nonneg (m + 1))))
          (ExpNeg.expNeg (a * Q'.ofNat m + a) hsumnn) :=
        expNeg_eqv_congr _ hsumnn (mul_ofNat_succ_eqv a m)
      -- e^{−(a·m + a)} ≃ e^{−am}·e^{−a}
      have e2 : CReal.Equiv
          (ExpNeg.expNeg (a * Q'.ofNat m + a) hsumnn)
          (CReal.mul (ExpNeg.expNeg (a * Q'.ofNat m) hamnn) (ExpNeg.expNeg a ha)) :=
        (expNeg_add_equiv (a * Q'.ofNat m) a hamnn ha).symm
      -- e^{−am}·e^{−a} ≤ ρ^m·ρ
      have hmul : CReal.leRat
          (CReal.mul (ExpNeg.expNeg (a * Q'.ofNat m) hamnn) (ExpNeg.expNeg a ha))
          (ρ ^ m * ρ) :=
        CReal.leRat_mul ih hρ
          (expNeg_geRat_zero _ hamnn) (expNeg_geRat_zero a ha)
          (Q'.pow_nonneg ρ hρ0 m) hρ0
      -- assemble: ρ^{m+1} = ρ·ρ^m, and ρ^m·ρ ≃ ρ·ρ^m (mul_comm)
      have hpow : CReal.leRat
          (CReal.mul (ExpNeg.expNeg (a * Q'.ofNat m) hamnn) (ExpNeg.expNeg a ha))
          (ρ ^ (m + 1)) := by
        rw [Q'.pow_succ]
        exact CReal.leRat_mono hmul (Q'.le_of_eqv (Q'.mul_comm_eqv (ρ ^ m) ρ))
      exact CReal.leRat_of_equiv (CReal.Equiv.trans e1 e2) hpow

/-! ## Demonstrator: `e^{−m} ≤ (1/2)^m`

A concrete non-vacuous instance: at `a = 1`, `ρ = 1/2` (since
`e^{−1} ≤ 1/(1+1) = 1/2`), the machinery gives the geometric decay
`e^{−m} ≤ (1/2)^m` for every `m` — exhibiting that the heat-kernel exponential
is dominated by a genuine geometric series with base `< 1`. -/
theorem expNeg_nat_le_half_pow (m : Nat) :
    CReal.leRat
      (ExpNeg.expNeg ((1 : Q') * Q'.ofNat m)
        (Q'.mul_nonneg 1 (Q'.ofNat m) (by decide) (ofNat_nonneg m)))
      ((Q'.mkPos 1 2 (by decide)) ^ m) :=
  expNeg_mul_le_pow 1 (Q'.mkPos 1 2 (by decide)) (by decide) (by decide)
    (expNeg_le_rat 1 (Q'.mkPos 1 2 (by decide)) (by decide) (by decide)) m

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.expNeg_le_rat
#print axioms ConstructiveReals.mul_ofNat_succ_eqv
#print axioms ConstructiveReals.expNeg_mul_le_pow
#print axioms ConstructiveReals.expNeg_nat_le_half_pow
