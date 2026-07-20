/-
`CReal.add` / `CReal.neg` — the additive substrate of constructive-real
arithmetic, intuitionistic (axiom-clean, no `Classical.choice`).

Both are defined **pointwise** (`(x+y).approx n := x.approx n + y.approx n`,
`(-x).approx n := -(x.approx n)`), computable from the `approx` data alone; the
(Prop-level) Cauchy moduli of `x`, `y` are used only inside the `cauchy`
*proofs*.  `neg` needs no `ε`-splitting (negation preserves the modulus
verbatim); `add` splits `ε` into `half·ε + half·ε` and reuses
`ExpNeg.two_halves`.

This is the "straightforward" remainder of the F.4 `CReal` arithmetic layer
that sits beside the already-landed `CReal.mul` (`CRealMul.lean`); together they
are what the U.5 soundness chain
`(1+x) ≤ eˣ ⟹ (1+x)·e⁻ˣ ≤ eˣ·e⁻ˣ = 1 ⟹ e⁻ˣ ≤ 1/(1+x)` and the product law
`eˣ·e⁻ˣ = 1` are built from.  `leRat_add` is the sound-upper-bound companion:
limit-`≤` of a sum from limit-`≤` of the summands.

# Axiom-gate (see README: axiom policy)

`[propext]` only (and `Quot.sound` where `Nat`/`omega` enter via the reused
`Q'`/`ExpNeg` helpers).  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.Reals
import ConstructiveReals.CRealLe
import ConstructiveReals.CRealMul
import ConstructiveReals.ExpNeg

namespace ConstructiveReals

open ConstructiveReals.HalfPow

namespace Q'

/-- Negation flips a one-slack bound: `a ≤ b + ε ⟹ -b ≤ -a + ε`. -/
theorem neg_le_neg_add {a b ε : Q'} (h : a ≤ b + ε) : -b ≤ -a + ε := by
  have h1 : a + -b ≤ ε := Q'.sub_le_of_le_add h
  have h2 : -b + a ≤ ε := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv (-b) a)) h1
  have h3 : (-b + a) + -a ≤ ε + -a := Q'.add_le_add_right _ _ (-a) h2
  have e1 : ((-b + a) + -a).eqv (-b) := by
    have a1 := Q'.add_assoc_eqv (-b) a (-a)
    have a2 : (-b + (a + -a)).eqv (-b + 0) :=
      Q'.add_eqv_congr_left (-b) (a + -a) 0 (Q'.add_neg_self_eqv a)
    rw [Q'.add_zero' (-b)] at a2
    exact Q'.eqv_trans _ _ _ a1 a2
  have e2 : (ε + -a).eqv (-a + ε) := Q'.add_comm_eqv ε (-a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm e1))
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv e2))

/-- Monotonicity of `+` in both arguments. -/
theorem add_le_add {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' (a + c) (b + c) (b + d)
    (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-- Regroup `(a+s)+(b+s) ≃ (a+b)+(s+s)` — the slack-collecting rearrangement. -/
theorem regroup (a b s : Q') : ((a + s) + (b + s)).eqv ((a + b) + (s + s)) := by
  have e1 : ((a + s) + (b + s)).eqv (a + (s + (b + s))) := Q'.add_assoc_eqv a s (b + s)
  have m1 : (s + (b + s)).eqv ((s + b) + s) := Q'.eqv_symm (Q'.add_assoc_eqv s b s)
  have m2 : ((s + b) + s).eqv ((b + s) + s) :=
    Q'.add_eqv_congr_right (s + b) (b + s) s (Q'.add_comm_eqv s b)
  have m3 : ((b + s) + s).eqv (b + (s + s)) := Q'.add_assoc_eqv b s s
  have minner : (s + (b + s)).eqv (b + (s + s)) :=
    Q'.eqv_trans _ _ _ m1 (Q'.eqv_trans _ _ _ m2 m3)
  have e2 : (a + (s + (b + s))).eqv (a + (b + (s + s))) :=
    Q'.add_eqv_congr_left a (s + (b + s)) (b + (s + s)) minner
  have e3 : (a + (b + (s + s))).eqv ((a + b) + (s + s)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv a b (s + s))
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)

end Q'

namespace CReal

open Q'

/-! ## `CReal.neg` -/

/-- Pointwise negation of a constructive real; the Cauchy modulus is preserved. -/
def neg (x : CReal) : CReal where
  approx n := -(x.approx n)
  cauchy := by
    intro ε hε
    obtain ⟨N, hN⟩ := x.cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN m n hm hn
    exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

@[simp] theorem neg_approx (x : CReal) (n : Nat) : (neg x).approx n = -(x.approx n) := rfl

/-- `neg` commutes with the embedding: `-(ofQ' a) = ofQ' (-a)`. -/
theorem ofQ'_neg (a : Q') : neg (ofQ' a) = ofQ' (-a) := rfl

/-! ## `CReal.add` -/

/-- Pointwise sum of constructive reals; Cauchy via `ε = half·ε + half·ε`. -/
def add (x y : CReal) : CReal where
  approx n := x.approx n + y.approx n
  cauchy := by
    intro ε hε
    have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
    obtain ⟨Nx, hNx⟩ := x.cauchy (half * ε) hhε
    obtain ⟨Ny, hNy⟩ := y.cauchy (half * ε) hhε
    refine ⟨max Nx Ny, fun m n hm hn => ?_⟩
    have hmx : Nx ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
    have hmy : Ny ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
    have hnx : Nx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hny : Ny ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    obtain ⟨hx1, hx2⟩ := hNx m n hmx hnx
    obtain ⟨hy1, hy2⟩ := hNy m n hmy hny
    have step : ∀ xm xn ym yn : Q',
        xm ≤ xn + half * ε → ym ≤ yn + half * ε →
        xm + ym ≤ (xn + yn) + ε := by
      intro xm xn ym yn hxx hyy
      have hsum : xm + ym ≤ (xn + half * ε) + (yn + half * ε) := Q'.add_le_add hxx hyy
      have ereg : ((xn + half * ε) + (yn + half * ε)).eqv ((xn + yn) + (half * ε + half * ε)) :=
        Q'.regroup xn yn (half * ε)
      have etwo : ((xn + yn) + (half * ε + half * ε)).eqv ((xn + yn) + ε) :=
        Q'.add_eqv_congr_left (xn + yn) (half * ε + half * ε) ε (ExpNeg.two_halves ε)
      exact Q'.le_trans' _ _ _ hsum
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))
    exact ⟨step (x.approx m) (x.approx n) (y.approx m) (y.approx n) hx1 hy1,
           step (x.approx n) (x.approx m) (y.approx n) (y.approx m) hx2 hy2⟩

@[simp] theorem add_approx (x y : CReal) (n : Nat) :
    (add x y).approx n = x.approx n + y.approx n := rfl

/-- `add` commutes with the embedding: `ofQ' a + ofQ' b = ofQ' (a+b)`. -/
theorem ofQ'_add (a b : Q') : add (ofQ' a) (ofQ' b) = ofQ' (a + b) := rfl

/-! ## Sound rational upper bound of a sum -/

/-- The limit-`≤` of a sum: `leRat x a → leRat y b → leRat (add x y) (a+b)`.
The sound (regularity-free) companion to `add`, splitting `ε` evenly. -/
theorem leRat_add {x y : CReal} {a b : Q'}
    (hx : CReal.leRat x a) (hy : CReal.leRat y b) :
    CReal.leRat (add x y) (a + b) := by
  intro ε hε
  have hhε : (0 : Q') < half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nx, hNx⟩ := hx (half * ε) hhε
  obtain ⟨Ny, hNy⟩ := hy (half * ε) hhε
  refine ⟨max Nx Ny, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h1 := hNx n hnx
  have h2 := hNy n hny
  have hsum : x.approx n + y.approx n ≤ (a + half * ε) + (b + half * ε) :=
    Q'.add_le_add h1 h2
  have ereg : ((a + half * ε) + (b + half * ε)).eqv ((a + b) + (half * ε + half * ε)) :=
    Q'.regroup a b (half * ε)
  have etwo : ((a + b) + (half * ε + half * ε)).eqv ((a + b) + ε) :=
    Q'.add_eqv_congr_left (a + b) (half * ε + half * ε) ε (ExpNeg.two_halves ε)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

end CReal

end ConstructiveReals

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.Q'.neg_le_neg_add
#print axioms ConstructiveReals.Q'.add_le_add
#print axioms ConstructiveReals.Q'.regroup
#print axioms ConstructiveReals.CReal.neg
#print axioms ConstructiveReals.CReal.ofQ'_neg
#print axioms ConstructiveReals.CReal.add
#print axioms ConstructiveReals.CReal.ofQ'_add
#print axioms ConstructiveReals.CReal.leRat_add
