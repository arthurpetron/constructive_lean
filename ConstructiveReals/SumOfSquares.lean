/-
Constructive sum-of-squares (SOS) positivity primitives — the reusable
backbone for every positive-semidefiniteness obligation in Track B
(OS2 reflection positivity, OS4 clustering, the GNS inner product).

A symmetric form is positive-semidefinite (PSD) when it is a
nonnegatively-weighted sum of squares of linear functionals; this file
proves the *consumer* of such a certificate:

    0 ≤ Σ_{k<m} D_k · L_k²     when every D_k ≥ 0     (`geRat_sos`)

together with the atoms it rests on: rational/`CReal` squares are
nonnegative, and a finite sum of nonnegative constructive reals is
nonnegative.  The heat-kernel Gram PSD theorem (E1's analytic completion)
then reduces to *exhibiting* the certificate `(D_k, L_k)` — a constructive
LDLᵀ / positive quadrature whose pivots `D_k ≥ 0` are the AM–GM-type
inequalities — and feeding it to `geRat_sos`.

# Axiom-gate (see README: axiom policy)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import ConstructiveReals.HalfPow
import ConstructiveReals.ExpNeg
import ConstructiveReals.ExpPos
import ConstructiveReals.CRealAdd
import ConstructiveReals.CRealSum
import ConstructiveReals.CRealMul
import ConstructiveReals.CRealMulMono
import ConstructiveReals.ExpAdd

namespace ConstructiveReals.SumOfSquares

open ConstructiveReals

/-! ## Nonnegativity atoms -/

/-- Rational squares are nonnegative: `0 ≤ a·a`. -/
theorem q_mul_self_nonneg (a : Q') : (0 : Q') ≤ a * a := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ a.num * a.num
  rcases Int.le_total 0 a.num with hz | hz
  · exact Int.mul_nonneg hz hz
  · have h2 : (0 : Int) ≤ -a.num := Int.neg_nonneg.mpr hz
    have h4 : (0 : Int) ≤ (-a.num) * (-a.num) := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h4

/-- A constant `≥ 0` embeds to a `≥ 0` constructive real. -/
theorem geRat_ofQ'_nonneg {c : Q'} (hc : (0 : Q') ≤ c) :
    ExpPos.geRat (CReal.ofQ' c) 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun _ _ => hc⟩

/-- **A constructive-real square is nonnegative:** `0 ≤ x·x`.  Immediate,
since `(x·x).approx n = (x.approx n)²` pointwise (no clamping in `CReal.mul`). -/
theorem geRat_sq_nonneg (x : CReal) : ExpPos.geRat (CReal.mul x x) 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun n _ => q_mul_self_nonneg (x.approx n)⟩

/-! ## Finite sums of nonnegatives -/

/-- Lower-bound companion of `CReal.leRat_add`: `geRat x a → geRat y b →
geRat (x+y) (a+b)` (splits `ε` evenly, mirroring `leRat_add`). -/
theorem geRat_add {x y : CReal} {a b : Q'}
    (hx : ExpPos.geRat x a) (hy : ExpPos.geRat y b) :
    ExpPos.geRat (CReal.add x y) (a + b) := by
  intro ε hε
  have hhε : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nx, hNx⟩ := hx (HalfPow.half * ε) hhε
  obtain ⟨Ny, hNy⟩ := hy (HalfPow.half * ε) hhε
  refine ⟨max Nx Ny, fun n hn => ?_⟩
  have hnx : Nx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hny : Ny ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have h1 := hNx n hnx
  have h2 := hNy n hny
  have hsum : a + b ≤ (x.approx n + HalfPow.half * ε) + (y.approx n + HalfPow.half * ε) :=
    Q'.add_le_add h1 h2
  have ereg : ((x.approx n + HalfPow.half * ε) + (y.approx n + HalfPow.half * ε)).eqv
      ((x.approx n + y.approx n) + (HalfPow.half * ε + HalfPow.half * ε)) :=
    Q'.regroup (x.approx n) (y.approx n) (HalfPow.half * ε)
  have etwo : ((x.approx n + y.approx n) + (HalfPow.half * ε + HalfPow.half * ε)).eqv
      ((x.approx n + y.approx n) + ε) :=
    Q'.add_eqv_congr_left (x.approx n + y.approx n)
      (HalfPow.half * ε + HalfPow.half * ε) ε (ExpNeg.two_halves ε)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv ereg) (Q'.le_of_eqv etwo))

/-- `czero ≥ 0`. -/
theorem geRat_czero : ExpPos.geRat CReal.czero 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun _ _ => Q'.le_refl' 0⟩

/-- A finite sum of nonnegative constructive reals is `≥ 0`. -/
theorem geRat_csum_nonneg {A : Nat → CReal} (h : ∀ i, ExpPos.geRat (A i) 0) :
    ∀ n, ExpPos.geRat (CReal.csum A n) 0
  | 0 => geRat_czero
  | (n + 1) => by
      rw [CReal.csum_succ]
      exact ExpPos.geRat_mono (geRat_add (geRat_csum_nonneg h n) (h n)) (by decide)

/-! ## The SOS ⟹ PSD primitive -/

/-- **SOS ⟹ PSD:** a nonnegatively-weighted finite sum of squares of
constructive reals is `≥ 0`:

    0 ≤ Σ_{k<m} D_k · (L_k)²     whenever every D_k ≥ 0.

This is the certificate consumer: any quadratic form presented as such a
sum is positive-semidefinite.  Each summand is `(≥0 constant)·(square)`,
nonnegative by `mul_nonneg`; the sum is nonnegative by `geRat_csum_nonneg`. -/
theorem geRat_sos (D : Nat → Q') (L : Nat → CReal)
    (hD : ∀ k, (0 : Q') ≤ D k) (m : Nat) :
    ExpPos.geRat
      (CReal.csum (fun k => CReal.mul (CReal.ofQ' (D k)) (CReal.mul (L k) (L k))) m) 0 :=
  geRat_csum_nonneg
    (fun k => CReal.mul_nonneg (geRat_ofQ'_nonneg (hD k)) (geRat_sq_nonneg (L k))) m

/-- **CReal-weighted SOS ⟹ PSD:** the same with `CReal` weights `P_k ≥ 0`
(the heat-kernel Gram pivots are `CReal`, not rational, so the LDLᵀ
certificate needs this form): `0 ≤ Σ_{k<m} P_k · (L_k)²` when each
`P_k ≥ 0`. -/
theorem geRat_sos_creal (P L : Nat → CReal)
    (hP : ∀ k, ExpPos.geRat (P k) 0) (m : Nat) :
    ExpPos.geRat
      (CReal.csum (fun k => CReal.mul (P k) (CReal.mul (L k) (L k))) m) 0 :=
  geRat_csum_nonneg
    (fun k => CReal.mul_nonneg (hP k) (geRat_sq_nonneg (L k))) m

/-! ## Lifting `CReal` identities from pointwise `Q'` equalities

`CReal.Equiv` is just "eventually `|A_n − B_n| ≤ ε`", so it follows
immediately from pointwise equality of approximations.  Since `CReal.mul`
and `CReal.add` act approx-wise, this reduces **any** `CReal` polynomial
identity to the corresponding `Q'` identity (where the ring-eqv lemmas
live) — the enabler for the LDLᵀ / SOS-factorization certificates that
route (a) needs at each order. -/

/-- If two constructive reals agree approx-wise (`A_n ≃ B_n` for all `n`),
they are `Equiv`. -/
theorem Equiv_of_approx_eqv {A B : CReal}
    (h : ∀ n, (A.approx n).eqv (B.approx n)) : CReal.Equiv A B := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n))
      (Q'.add_le_self_of_nonneg (B.approx n) ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (h n)))
      (Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε))

end ConstructiveReals.SumOfSquares

/-! ## Axiom-dependency gates (see README: axiom policy) -/

#print axioms ConstructiveReals.SumOfSquares.q_mul_self_nonneg
#print axioms ConstructiveReals.SumOfSquares.geRat_sq_nonneg
#print axioms ConstructiveReals.SumOfSquares.geRat_csum_nonneg
#print axioms ConstructiveReals.SumOfSquares.geRat_sos
#print axioms ConstructiveReals.SumOfSquares.geRat_sos_creal
#print axioms ConstructiveReals.SumOfSquares.Equiv_of_approx_eqv
