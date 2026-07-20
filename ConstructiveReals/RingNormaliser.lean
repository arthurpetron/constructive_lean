/-
**Constructive reflective ring normaliser over `Q'` (Lean-core; no Mathlib
`ring`).**

This module builds a *sound* decision procedure for multivariate polynomial
identities over the constructive rationals `Q'` (equivalently: polynomial
identities with integer coefficients, evaluated at arbitrary `Q'` points).  It
is designed for certificate steps that reduce, after cross-multiplication,
to multivariate polynomial identities that `ac_rfl`/`omega` cannot discharge
(`omega` is linear only; `ac_rfl` cannot distribute).

# The reflection pipeline

  * `PolyExpr` — a reflective syntax of multivariate polynomial expressions
    (`const : Int`, `var : Nat`, `add`, `mul`, `neg`, `pow`) as DATA.
  * `eval ρ : PolyExpr → Q'` — the evaluation homomorphism into `Q'` at an
    environment `ρ : Nat → Q'` (variable `i` ↦ `ρ i`; integer constants via
    `Q'.ofInt`; `pow` via the internal fold `qpow`).
  * `NormalPoly` (= `List (List Nat × Int)`) — canonical form: a sorted,
    like-terms-combined, zero-free list of `(exponent-vector, coefficient)`
    pairs.  Monomials are trailing-zero-trimmed exponent vectors, ordered by a
    strict lex order (`monoCmp`); `DecidableEq` is structural list equality.
  * `normalize : PolyExpr → NormalPoly` and the SOUNDNESS THEOREM
    `normalize_eval : (eval ρ e).eqv (evalRaw ρ (normalize e))` — proved by
    structural induction on `PolyExpr` using ONLY the `Q'` ring axioms
    (`mul_comm_eqv`, `mul_assoc_eqv`, `mul_add_eqv`, `add_assoc_eqv`, … from
    `RationalsMul.lean`).  This is the load-bearing core: it is genuinely
    proved, never assumed.
  * `poly_identity_of_normal_eq` — the DECISION PROCEDURE: if
    `normalize e₁ = normalize e₂` (a closed `decide`/`rfl` on the canonical
    form), then `∀ ρ, (eval ρ e₁).eqv (eval ρ e₂)`.  SOUND (proves true
    identities; completeness is not claimed — see residual note).

# Demonstration (Vandermonde convolutions)

`vandermonde_deg2` proves the degree-2 Chu–Vandermonde convolution identity,
cleared of denominators,

  `n(n-1) + 2·m·n + m(m-1)  =  (m+n)(m+n-1)`      (∀ m,n ∈ Q')

— a genuine member of the Vandermonde/Saalschütz convolution family.  It is
beyond `omega` (nonlinear:
`m²`, `n²`, `mn`) and beyond `ac_rfl` (requires distribution and cancellation
of the cross term).  It is proved purely by reflection:
`normalize LHS = normalize RHS` by kernel computation, then
`poly_identity_of_normal_eq`.

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Int` core only.  No `Real`, `Classical.*`,
`native_decide`, `ring`/`nlinarith`.  `decide`/`rfl` are genuine kernel
decisions on the small concrete canonical forms.  No `sorry`/`admit`/new
`axiom`; witnesses (`normalize`, `eval`) are Type-level `def`s (Rule 8).
`#print axioms` gated (`propext`/`Quot.sound`).

# Residual (honest scope)

Coefficients are `Int`: this decides polynomial identities with integer
coefficients (equivalently rational identities after clearing denominators —
which a cross-multiplication step always achieves).  Genuine rational-function
coefficients requiring `gcd`-normalisation of `Q'` numerators/denominators, and
true rational-FUNCTION (division) identities, are NOT handled here and are the
named residual.  Completeness (equal polynomials ⇒ equal normal forms) is not
proved — only soundness is — though canonicalisation makes it hold in practice
(the demonstration relies on it computationally, verified by the kernel).
-/
import ConstructiveReals.RationalsMul

/-! ## Small `Q'` helper used below (`-(a+b) ≃ -a + -b`). -/

namespace ConstructiveReals.Q'

/-- `-(a + b) ≃ -a + -b`. -/
theorem neg_add_eqv_split (a b : Q') : (-(a + b)).eqv ((-a) + (-b)) := by
  show (-(a + b)).num * (((-a) + (-b)).den : Int)
      = ((-a) + (-b)).num * ((-(a + b)).den : Int)
  have hL : (-(a + b)).num = -(a.num * (b.den : Int) + b.num * (a.den : Int)) := rfl
  have hR : ((-a) + (-b)).num
      = (-a.num) * (b.den : Int) + (-b.num) * (a.den : Int) := rfl
  have hnum : -(a.num * (b.den : Int) + b.num * (a.den : Int))
      = (-a.num) * (b.den : Int) + (-b.num) * (a.den : Int) := by
    rw [Int.neg_mul, Int.neg_mul, Int.neg_add]
  rw [hL, hR, add_den_cast (-a) (-b), neg_den a, neg_den b,
      show (-(a + b)).den = (a + b).den from rfl, add_den_cast a b, hnum]

end ConstructiveReals.Q'

namespace ConstructiveReals.RingNormaliser

open ConstructiveReals
open ConstructiveReals.Q'

/-! ## 0. Small `Q'` helpers not already in `RationalsMul`. -/

/-- Structural equality implies `eqv`. -/
theorem eqv_of_eq {a b : Q'} (h : a = b) : a.eqv b := by
  cases h; exact Q'.eqv_refl a

/-- `(0 : Q') * a ≃ 0`. -/
theorem q_zero_mul (a : Q') : ((0 : Q') * a).eqv 0 := by
  show ((0 : Q') * a).num * ((0 : Q').den : Int)
      = (0 : Q').num * (((0 : Q') * a).den : Int)
  show ((0 : Int) * a.num) * (1 : Int) = (0 : Int) * (((0 : Q') * a).den : Int)
  rw [Int.zero_mul, Int.zero_mul, Int.zero_mul]

/-- Right-distributivity `(a + b) * c ≃ a*c + b*c` (from `mul_add` + `mul_comm`). -/
theorem q_add_mul (a b c : Q') : ((a + b) * c).eqv (a * c + b * c) := by
  refine Q'.eqv_trans _ (c * (a + b)) _ (Q'.mul_comm_eqv (a + b) c) ?_
  refine Q'.eqv_trans _ (c * a + c * b) _ (Q'.mul_add_eqv c a b) ?_
  exact Q'.eqv_trans _ (a * c + c * b) _
    (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c a))
    (Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv c b))

/-- `Q'.ofInt` is additive: `ofInt (a+b) ≃ ofInt a + ofInt b`. -/
theorem ofInt_add (a b : Int) :
    (Q'.ofInt (a + b)).eqv (Q'.ofInt a + Q'.ofInt b) := by
  show (Q'.ofInt (a + b)).num * ((Q'.ofInt a + Q'.ofInt b).den : Int)
      = (Q'.ofInt a + Q'.ofInt b).num * ((Q'.ofInt (a + b)).den : Int)
  -- ofInt x = ⟨x, 0⟩, den 1; sum has num a*1 + b*1, den 1*1.
  show (a + b) * (((1 * 1 - 1) + 1 : Nat) : Int)
      = (a * ((1 : Nat) : Int) + b * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
  simp

/-- `Q'.ofInt` is multiplicative: `ofInt (a*b) ≃ ofInt a * ofInt b`. -/
theorem ofInt_mul (a b : Int) :
    (Q'.ofInt (a * b)).eqv (Q'.ofInt a * Q'.ofInt b) := by
  show (Q'.ofInt (a * b)).num * ((Q'.ofInt a * Q'.ofInt b).den : Int)
      = (Q'.ofInt a * Q'.ofInt b).num * ((Q'.ofInt (a * b)).den : Int)
  show (a * b) * (((1 * 1 - 1) + 1 : Nat) : Int)
      = (a * b) * ((1 : Nat) : Int)
  simp

/-- `ofInt 0 = 0` (structural). -/
theorem ofInt_zero : Q'.ofInt 0 = 0 := rfl

/-- `ofInt 1 = 1` (structural). -/
theorem ofInt_one : Q'.ofInt 1 = 1 := rfl

/-! ## 1. `qpow` — the evaluation of a `Nat` power (internal fold). -/

/-- `x` raised to a `Nat` power, as a right-nested product. -/
def qpow (x : Q') : Nat → Q'
  | 0     => 1
  | n + 1 => qpow x n * x

@[simp] theorem qpow_zero (x : Q') : qpow x 0 = 1 := rfl
@[simp] theorem qpow_succ (x : Q') (n : Nat) : qpow x (n + 1) = qpow x n * x := rfl

/-- Power respects `eqv` in the base: `a ≃ b → qpow a n ≃ qpow b n`. -/
theorem qpow_eqv_congr {a b : Q'} (h : a.eqv b) : ∀ n, (qpow a n).eqv (qpow b n)
  | 0     => Q'.eqv_refl 1
  | n + 1 => by
      have ih := qpow_eqv_congr h n
      exact Q'.eqv_trans _ (qpow b n * a) _
        (Q'.mul_eqv_congr_right _ _ _ ih)
        (Q'.mul_eqv_congr_left _ _ _ h)

/-- Exponent-additivity: `qpow x (a+b) ≃ qpow x a * qpow x b`. -/
theorem qpow_add (x : Q') (a : Nat) : ∀ b, (qpow x (a + b)).eqv (qpow x a * qpow x b)
  | 0     => by
      -- qpow x (a+0) = qpow x a ; RHS = qpow x a * 1 ≃ qpow x a.
      exact Q'.eqv_symm (Q'.mul_one_eqv (qpow x a))
  | b + 1 => by
      -- qpow x (a+(b+1)) = qpow x (a+b) * x
      have ih := qpow_add x a b
      -- ≃ (qpow x a * qpow x b) * x ≃ qpow x a * (qpow x b * x) = qpow x a * qpow x (b+1)
      have h1 : (qpow x (a + (b + 1))).eqv ((qpow x a * qpow x b) * x) := by
        have : (qpow x (a + (b + 1))) = qpow x (a + b) * x := by
          have : a + (b + 1) = (a + b) + 1 := by omega
          rw [this]; rfl
        rw [this]
        exact Q'.mul_eqv_congr_right _ _ _ ih
      exact Q'.eqv_trans _ ((qpow x a * qpow x b) * x) _ h1
        (Q'.mul_assoc_eqv (qpow x a) (qpow x b) x)

/-! ## 2. Monomials — trailing-zero-trimmed exponent vectors.

A monomial is a `List Nat`: position `i` is the exponent of variable `i`
(`ρ i`).  The empty list is the constant monomial `1`.  All monomials produced
by the normaliser are *trailing-zero-trimmed*, so structural list equality is
monomial equality. -/

/-- Evaluate a monomial from variable index `i`: `∏_j (ρ (i+j))^{es_j}`. -/
def evalMonoFrom (ρ : Nat → Q') (i : Nat) : List Nat → Q'
  | []      => 1
  | e :: es => qpow (ρ i) e * evalMonoFrom ρ (i + 1) es

/-- Evaluate a monomial (from variable index `0`). -/
def evalMono (ρ : Nat → Q') (m : List Nat) : Q' := evalMonoFrom ρ 0 m

/-- Multiply two monomials: component-wise addition of exponent vectors (with
`0`-padding for the shorter one). -/
def monoMul : List Nat → List Nat → List Nat
  | [],      b       => b
  | a,       []      => a
  | x :: xs, y :: ys => (x + y) :: monoMul xs ys

/-- Four-factor rearrangement `(a*b)*(c*d) ≃ (a*c)*(b*d)` at `eqv`. -/
theorem q_mul4_swap (a b c d : Q') :
    ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  -- (a*b)*(c*d) ≃ a*(b*(c*d)) ≃ a*((b*c)*d) ≃ a*((c*b)*d) ≃ a*(c*(b*d)) ≃ (a*c)*(b*d)
  refine Q'.eqv_trans _ (a * (b * (c * d))) _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ (a * ((c * b) * d)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- **Monomial multiplication is a homomorphism** (from any base index `i`):
`evalMonoFrom ρ i (monoMul a b) ≃ evalMonoFrom ρ i a * evalMonoFrom ρ i b`. -/
theorem evalMonoFrom_monoMul (ρ : Nat → Q') :
    ∀ (i : Nat) (a b : List Nat),
      (evalMonoFrom ρ i (monoMul a b)).eqv
        (evalMonoFrom ρ i a * evalMonoFrom ρ i b)
  | _, [],      b       => by
      -- monoMul [] b = b ; RHS = 1 * evalMonoFrom b ≃ evalMonoFrom b.
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | _, x :: xs, []      => by
      -- monoMul (x::xs) [] = x::xs ; RHS = evalMonoFrom (x::xs) * 1 ≃ evalMonoFrom (x::xs).
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
  | i, x :: xs, y :: ys => by
      -- monoMul = (x+y) :: monoMul xs ys
      have ih := evalMonoFrom_monoMul ρ (i + 1) xs ys
      -- LHS = qpow (ρ i) (x+y) * evalMonoFrom ρ (i+1) (monoMul xs ys)
      -- ≃ (qpow (ρi) x * qpow (ρi) y) * (evalMonoFrom xs * evalMonoFrom ys)
      have step1 :
          (evalMonoFrom ρ i (monoMul (x :: xs) (y :: ys))).eqv
            ((qpow (ρ i) x * qpow (ρ i) y)
              * (evalMonoFrom ρ (i + 1) xs * evalMonoFrom ρ (i + 1) ys)) := by
        show (qpow (ρ i) (x + y)
              * evalMonoFrom ρ (i + 1) (monoMul xs ys)).eqv _
        exact Q'.eqv_trans _
          ((qpow (ρ i) x * qpow (ρ i) y)
              * evalMonoFrom ρ (i + 1) (monoMul xs ys)) _
          (Q'.mul_eqv_congr_right _ _ _ (qpow_add (ρ i) x y))
          (Q'.mul_eqv_congr_left _ _ _ ih)
      -- rearrange (AB)(CD) → (AC)(BD)
      exact Q'.eqv_trans _
        ((qpow (ρ i) x * qpow (ρ i) y)
            * (evalMonoFrom ρ (i + 1) xs * evalMonoFrom ρ (i + 1) ys)) _
        step1
        (q_mul4_swap (qpow (ρ i) x) (qpow (ρ i) y)
          (evalMonoFrom ρ (i + 1) xs) (evalMonoFrom ρ (i + 1) ys))

/-- The homomorphism at index `0`. -/
theorem evalMono_monoMul (ρ : Nat → Q') (a b : List Nat) :
    (evalMono ρ (monoMul a b)).eqv (evalMono ρ a * evalMono ρ b) :=
  evalMonoFrom_monoMul ρ 0 a b

/-- The variable-`i` monomial `x_i = [0,…,0,1]` (length `i+1`). -/
def varMono (i : Nat) : List Nat := List.replicate i 0 ++ [1]

/-- Evaluating the variable monomial from base index `j` gives `ρ (j + i)`. -/
theorem evalMonoFrom_varMono (ρ : Nat → Q') :
    ∀ (i j : Nat), (evalMonoFrom ρ j (varMono i)).eqv (ρ (j + i))
  | 0, j => by
      -- varMono 0 = [1] ; evalMonoFrom ρ j [1] = qpow (ρ j) 1 * 1
      show (qpow (ρ j) 1 * evalMonoFrom ρ (j + 1) []).eqv (ρ (j + 0))
      -- qpow (ρj) 1 = qpow (ρj) 0 * ρj = 1 * ρj ; * evalMonoFrom [] = *1
      have h1 : (qpow (ρ j) 1 * evalMonoFrom ρ (j + 1) []).eqv (qpow (ρ j) 1) :=
        Q'.mul_one_eqv _
      have h2 : (qpow (ρ j) 1).eqv (ρ j) := by
        show (qpow (ρ j) 0 * ρ j).eqv (ρ j)
        exact Q'.eqv_trans _ (1 * ρ j) _ (Q'.eqv_refl _) (Q'.one_mul_eqv (ρ j))
      have : (j + 0) = j := by omega
      rw [this]
      exact Q'.eqv_trans _ (qpow (ρ j) 1) _ h1 h2
  | i + 1, j => by
      -- varMono (i+1) = 0 :: varMono i
      show (qpow (ρ j) 0 * evalMonoFrom ρ (j + 1) (varMono i)).eqv (ρ (j + (i + 1)))
      have ih := evalMonoFrom_varMono ρ i (j + 1)
      -- qpow (ρj) 0 = 1 ; 1 * evalMonoFrom (varMono i) ≃ evalMonoFrom (varMono i) ≃ ρ ((j+1)+i)
      have h1 : (qpow (ρ j) 0 * evalMonoFrom ρ (j + 1) (varMono i)).eqv
                  (evalMonoFrom ρ (j + 1) (varMono i)) := Q'.one_mul_eqv _
      have hidx : ((j + 1) + i) = (j + (i + 1)) := by omega
      rw [hidx] at ih
      exact Q'.eqv_trans _ (evalMonoFrom ρ (j + 1) (varMono i)) _ h1 ih

/-! ## 3. Raw polynomials and their evaluation. -/

/-- A raw polynomial: an (unsorted, possibly-uncombined) list of
`(monomial, integer-coefficient)` terms. -/
abbrev RawPoly := List (List Nat × Int)

/-- Naive evaluation of a raw polynomial: `Σ (ofInt c) * evalMono m`.
This is also the evaluation used for `NormalPoly` (a canonical `RawPoly`). -/
def evalRaw (ρ : Nat → Q') : RawPoly → Q'
  | []            => 0
  | (m, c) :: rest => Q'.ofInt c * evalMono ρ m + evalRaw ρ rest

@[simp] theorem evalRaw_nil (ρ : Nat → Q') : evalRaw ρ [] = 0 := rfl
@[simp] theorem evalRaw_cons (ρ : Nat → Q') (m : List Nat) (c : Int) (rest : RawPoly) :
    evalRaw ρ ((m, c) :: rest) = Q'.ofInt c * evalMono ρ m + evalRaw ρ rest := rfl

/-- Append of raw polynomials evaluates to the sum. -/
theorem evalRaw_append (ρ : Nat → Q') :
    ∀ (p q : RawPoly), (evalRaw ρ (p ++ q)).eqv (evalRaw ρ p + evalRaw ρ q)
  | [],            q => by
      -- evalRaw ([] ++ q) = evalRaw q ; RHS = 0 + evalRaw q = evalRaw q (structural)
      exact eqv_of_eq (Q'.zero_add' (evalRaw ρ q)).symm
  | (m, c) :: p,   q => by
      -- evalRaw (((m,c)::p) ++ q) = t + evalRaw (p ++ q)
      -- ≃ t + (evalRaw p + evalRaw q) ≃ (t + evalRaw p) + evalRaw q
      have ih := evalRaw_append ρ p q
      let t := Q'.ofInt c * evalMono ρ m
      show (t + evalRaw ρ (p ++ q)).eqv ((t + evalRaw ρ p) + evalRaw ρ q)
      refine Q'.eqv_trans _ (t + (evalRaw ρ p + evalRaw ρ q)) _
        (Q'.add_eqv_congr_left _ _ _ ih) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv t (evalRaw ρ p) (evalRaw ρ q))

/-- Negate a raw polynomial: negate every coefficient. -/
def rawNeg (p : RawPoly) : RawPoly := p.map (fun mc => (mc.1, -mc.2))

/-- `rawNeg` evaluates to the negation. -/
theorem evalRaw_rawNeg (ρ : Nat → Q') :
    ∀ (p : RawPoly), (evalRaw ρ (rawNeg p)).eqv (-(evalRaw ρ p))
  | []            => by
      -- evalRaw (rawNeg []) = 0 ; -(0) ≃ 0
      show (0 : Q').eqv (-(0 : Q'))
      exact Q'.eqv_symm (by
        show (-(0 : Q')).eqv 0
        show (-(0:Q')).num * ((0:Q').den : Int) = (0:Q').num * ((-(0:Q')).den : Int)
        show (-(0:Int)) * (1:Int) = (0:Int) * (1:Int)
        simp)
  | (m, c) :: p   => by
      have ih := evalRaw_rawNeg ρ p
      let M := evalMono ρ m
      -- evalRaw (rawNeg ((m,c)::p)) = ofInt(-c)*M + evalRaw (rawNeg p)
      show (Q'.ofInt (-c) * M + evalRaw ρ (rawNeg p)).eqv
            (-(Q'.ofInt c * M + evalRaw ρ p))
      -- ofInt(-c)*M ≃ -(ofInt c * M) ; then -(A) + -(B) ≃ -(A+B)
      have hc : (Q'.ofInt (-c) * M).eqv (-(Q'.ofInt c * M)) := by
        have h1 : (Q'.ofInt (-c)).eqv (-(Q'.ofInt c)) := by
          show (Q'.ofInt (-c)).num * ((-(Q'.ofInt c)).den : Int)
              = (-(Q'.ofInt c)).num * ((Q'.ofInt (-c)).den : Int)
          show (-c) * (1 : Int) = (-c) * (1 : Int)
          rfl
        exact Q'.eqv_trans _ ((-(Q'.ofInt c)) * M) _
          (Q'.mul_eqv_congr_right _ _ _ h1)
          (Q'.neg_mul_eqv (Q'.ofInt c) M)
      refine Q'.eqv_trans _ ((-(Q'.ofInt c * M)) + (-(evalRaw ρ p))) _
        (Q'.eqv_trans _ ((-(Q'.ofInt c * M)) + evalRaw ρ (rawNeg p)) _
          (Q'.add_eqv_congr_right _ _ _ hc)
          (Q'.add_eqv_congr_left _ _ _ ih)) ?_
      -- -(A) + -(B) ≃ -(A + B)
      exact Q'.eqv_symm (neg_add_eqv_split (Q'.ofInt c * M) (evalRaw ρ p))

/-- Scale a raw polynomial by a single term `(m, c)`: multiply every monomial by
`m` and every coefficient by `c`. -/
def scaleTerm (m : List Nat) (c : Int) (p : RawPoly) : RawPoly :=
  p.map (fun mc => (monoMul m mc.1, c * mc.2))

/-- `scaleTerm` evaluates to `(ofInt c * evalMono m) * evalRaw p`. -/
theorem evalRaw_scaleTerm (ρ : Nat → Q') (m : List Nat) (c : Int) :
    ∀ (p : RawPoly),
      (evalRaw ρ (scaleTerm m c p)).eqv
        ((Q'.ofInt c * evalMono ρ m) * evalRaw ρ p)
  | []          => by
      -- evalRaw (scaleTerm m c []) = 0 ; RHS = (…)*0 ≃ 0
      show (0 : Q').eqv ((Q'.ofInt c * evalMono ρ m) * 0)
      refine Q'.eqv_symm ?_
      exact Q'.eqv_trans _ (0 * (Q'.ofInt c * evalMono ρ m)) _
        (Q'.mul_comm_eqv _ 0) (q_zero_mul _)
  | (m', c') :: p => by
      have ih := evalRaw_scaleTerm ρ m c p
      let K := Q'.ofInt c * evalMono ρ m
      -- evalRaw (scaleTerm m c ((m',c')::p))
      --   = ofInt (c*c') * evalMono (monoMul m m') + evalRaw (scaleTerm m c p)
      show (Q'.ofInt (c * c') * evalMono ρ (monoMul m m') + evalRaw ρ (scaleTerm m c p)).eqv
            (K * (Q'.ofInt c' * evalMono ρ m' + evalRaw ρ p))
      -- head term ≃ K * (ofInt c' * evalMono m')
      have hhead : (Q'.ofInt (c * c') * evalMono ρ (monoMul m m')).eqv
                    (K * (Q'.ofInt c' * evalMono ρ m')) := by
        -- ofInt (c*c') ≃ ofInt c * ofInt c' ; evalMono (monoMul m m') ≃ evalMono m * evalMono m'
        have e1 : (Q'.ofInt (c * c') * evalMono ρ (monoMul m m')).eqv
                    ((Q'.ofInt c * Q'.ofInt c') * (evalMono ρ m * evalMono ρ m')) :=
          Q'.eqv_trans _ ((Q'.ofInt c * Q'.ofInt c') * evalMono ρ (monoMul m m')) _
            (Q'.mul_eqv_congr_right _ _ _ (ofInt_mul c c'))
            (Q'.mul_eqv_congr_left _ _ _ (evalMono_monoMul ρ m m'))
        -- (ofInt c * ofInt c') * (evalMono m * evalMono m')
        --   ≃ (ofInt c * evalMono m) * (ofInt c' * evalMono m') = K * (...)
        exact Q'.eqv_trans _ ((Q'.ofInt c * Q'.ofInt c') * (evalMono ρ m * evalMono ρ m')) _
          e1 (q_mul4_swap (Q'.ofInt c) (Q'.ofInt c') (evalMono ρ m) (evalMono ρ m'))
      -- tail via ih ; then distribute K over the sum on the RHS
      refine Q'.eqv_trans _
        (K * (Q'.ofInt c' * evalMono ρ m') + K * evalRaw ρ p) _
        (Q'.eqv_trans _
          (K * (Q'.ofInt c' * evalMono ρ m') + evalRaw ρ (scaleTerm m c p)) _
          (Q'.add_eqv_congr_right _ _ _ hhead)
          (Q'.add_eqv_congr_left _ _ _ ih)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv K (Q'.ofInt c' * evalMono ρ m') (evalRaw ρ p))

/-- Multiply two raw polynomials: distribute (`p`'s terms scale `q`). -/
def rawMul : RawPoly → RawPoly → RawPoly
  | [],            _ => []
  | (m, c) :: p,   q => scaleTerm m c q ++ rawMul p q

/-- `rawMul` evaluates to the product. -/
theorem evalRaw_rawMul (ρ : Nat → Q') :
    ∀ (p q : RawPoly), (evalRaw ρ (rawMul p q)).eqv (evalRaw ρ p * evalRaw ρ q)
  | [],          q => by
      -- evalRaw (rawMul [] q) = 0 ; RHS = 0 * evalRaw q ≃ 0
      show (0 : Q').eqv (0 * evalRaw ρ q)
      exact Q'.eqv_symm (q_zero_mul (evalRaw ρ q))
  | (m, c) :: p, q => by
      have ih := evalRaw_rawMul ρ p q
      let Q := evalRaw ρ q
      -- rawMul ((m,c)::p) q = scaleTerm m c q ++ rawMul p q
      -- evalRaw ≃ evalRaw (scaleTerm m c q) + evalRaw (rawMul p q)
      have happ := evalRaw_append ρ (scaleTerm m c q) (rawMul p q)
      -- ≃ ((ofInt c * evalMono m) * Q) + (evalRaw p * Q)
      have hsc := evalRaw_scaleTerm ρ m c q
      -- RHS goal: (ofInt c * evalMono m + evalRaw p) * Q
      show (evalRaw ρ (scaleTerm m c q ++ rawMul p q)).eqv
            ((Q'.ofInt c * evalMono ρ m + evalRaw ρ p) * Q)
      refine Q'.eqv_trans _ (evalRaw ρ (scaleTerm m c q) + evalRaw ρ (rawMul p q)) _
        happ ?_
      refine Q'.eqv_trans _
        (((Q'.ofInt c * evalMono ρ m) * Q) + (evalRaw ρ p * Q)) _
        (Q'.eqv_trans _
          (((Q'.ofInt c * evalMono ρ m) * Q) + evalRaw ρ (rawMul p q)) _
          (Q'.add_eqv_congr_right _ _ _ hsc)
          (Q'.add_eqv_congr_left _ _ _ ih)) ?_
      -- (A*Q)+(B*Q) ≃ (A+B)*Q  (right-distributivity, reversed)
      exact Q'.eqv_symm (q_add_mul (Q'.ofInt c * evalMono ρ m) (evalRaw ρ p) Q)

/-- Raise a raw polynomial to a `Nat` power (right-nested `rawMul`). -/
def rawPow (p : RawPoly) : Nat → RawPoly
  | 0     => [([], 1)]
  | n + 1 => rawMul (rawPow p n) p

/-- `rawPow` evaluates to `qpow (evalRaw p) n`. -/
theorem evalRaw_rawPow (ρ : Nat → Q') (p : RawPoly) :
    ∀ n, (evalRaw ρ (rawPow p n)).eqv (qpow (evalRaw ρ p) n)
  | 0     => by
      -- evalRaw [([],1)] = ofInt 1 * evalMono [] + 0 = 1 * 1 + 0 ≃ 1 = qpow _ 0
      show (Q'.ofInt 1 * evalMono ρ [] + 0).eqv (1 : Q')
      -- ofInt 1 = 1 ; evalMono [] = 1
      have h1 : (Q'.ofInt 1 * evalMono ρ [] + 0).eqv (Q'.ofInt 1 * evalMono ρ []) :=
        eqv_of_eq (Q'.add_zero' (Q'.ofInt 1 * evalMono ρ []))
      have h2 : (Q'.ofInt 1 * evalMono ρ []).eqv (1 : Q') := by
        show ((1 : Q') * (1 : Q')).eqv (1 : Q')
        exact Q'.mul_one_eqv 1
      exact Q'.eqv_trans _ (Q'.ofInt 1 * evalMono ρ []) _ h1 h2
  | n + 1 => by
      have ih := evalRaw_rawPow ρ p n
      -- rawPow p (n+1) = rawMul (rawPow p n) p
      show (evalRaw ρ (rawMul (rawPow p n) p)).eqv (qpow (evalRaw ρ p) n * evalRaw ρ p)
      refine Q'.eqv_trans _ (evalRaw ρ (rawPow p n) * evalRaw ρ p) _
        (evalRaw_rawMul ρ (rawPow p n) p) ?_
      exact Q'.mul_eqv_congr_right _ _ _ ih

/-! ## 4. The reflective syntax `PolyExpr` and `eval`. -/

/-- Multivariate polynomial expressions with integer constants and
`Nat`-indexed variables. -/
inductive PolyExpr where
  | const : Int → PolyExpr
  | var   : Nat → PolyExpr
  | add   : PolyExpr → PolyExpr → PolyExpr
  | mul   : PolyExpr → PolyExpr → PolyExpr
  | neg   : PolyExpr → PolyExpr
  | pow   : PolyExpr → Nat → PolyExpr
  deriving Repr

/-- The evaluation homomorphism `PolyExpr → Q'` at environment `ρ`. -/
def eval (ρ : Nat → Q') : PolyExpr → Q'
  | .const c => Q'.ofInt c
  | .var i   => ρ i
  | .add a b => eval ρ a + eval ρ b
  | .mul a b => eval ρ a * eval ρ b
  | .neg a   => -(eval ρ a)
  | .pow a n => qpow (eval ρ a) n

/-- Reflect a `PolyExpr` into a raw (uncanonicalised) polynomial. -/
def rawNormalize : PolyExpr → RawPoly
  | .const c => [([], c)]
  | .var i   => [(varMono i, 1)]
  | .add a b => rawNormalize a ++ rawNormalize b
  | .mul a b => rawMul (rawNormalize a) (rawNormalize b)
  | .neg a   => rawNeg (rawNormalize a)
  | .pow a n => rawPow (rawNormalize a) n

/-- **`rawNormalize` preserves value** (structural induction; `Q'` ring axioms). -/
theorem eval_rawNormalize (ρ : Nat → Q') :
    ∀ (e : PolyExpr), (eval ρ e).eqv (evalRaw ρ (rawNormalize e))
  | .const c => by
      -- evalRaw [([],c)] = ofInt c * evalMono [] + 0 = ofInt c * 1 + 0 ≃ ofInt c
      show (Q'.ofInt c).eqv (Q'.ofInt c * evalMono ρ [] + 0)
      refine Q'.eqv_symm ?_
      have h1 : (Q'.ofInt c * evalMono ρ [] + 0).eqv (Q'.ofInt c * evalMono ρ []) :=
        eqv_of_eq (Q'.add_zero' (Q'.ofInt c * evalMono ρ []))
      have h2 : (Q'.ofInt c * evalMono ρ []).eqv (Q'.ofInt c) := by
        show (Q'.ofInt c * (1 : Q')).eqv (Q'.ofInt c)
        exact Q'.mul_one_eqv (Q'.ofInt c)
      exact Q'.eqv_trans _ (Q'.ofInt c * evalMono ρ []) _ h1 h2
  | .var i => by
      -- evalRaw [(varMono i, 1)] = ofInt 1 * evalMono (varMono i) + 0
      show (ρ i).eqv (Q'.ofInt 1 * evalMono ρ (varMono i) + 0)
      refine Q'.eqv_symm ?_
      have h1 : (Q'.ofInt 1 * evalMono ρ (varMono i) + 0).eqv
                  (Q'.ofInt 1 * evalMono ρ (varMono i)) :=
        eqv_of_eq (Q'.add_zero' (Q'.ofInt 1 * evalMono ρ (varMono i)))
      have h2 : (Q'.ofInt 1 * evalMono ρ (varMono i)).eqv (evalMono ρ (varMono i)) := by
        show ((1 : Q') * evalMono ρ (varMono i)).eqv (evalMono ρ (varMono i))
        exact Q'.one_mul_eqv _
      have h3 : (evalMono ρ (varMono i)).eqv (ρ i) := by
        show (evalMonoFrom ρ 0 (varMono i)).eqv (ρ i)
        have := evalMonoFrom_varMono ρ i 0
        have h0 : (0 + i) = i := by omega
        rw [h0] at this
        exact this
      exact Q'.eqv_trans _ (Q'.ofInt 1 * evalMono ρ (varMono i)) _ h1
        (Q'.eqv_trans _ (evalMono ρ (varMono i)) _ h2 h3)
  | .add a b => by
      have iha := eval_rawNormalize ρ a
      have ihb := eval_rawNormalize ρ b
      -- eval (add a b) = eval a + eval b ≃ evalRaw (rawNorm a) + evalRaw (rawNorm b)
      -- ≃ evalRaw (rawNorm a ++ rawNorm b)
      show (eval ρ a + eval ρ b).eqv (evalRaw ρ (rawNormalize a ++ rawNormalize b))
      refine Q'.eqv_trans _ (evalRaw ρ (rawNormalize a) + evalRaw ρ (rawNormalize b)) _
        (Q'.eqv_trans _ (evalRaw ρ (rawNormalize a) + eval ρ b) _
          (Q'.add_eqv_congr_right _ _ _ iha)
          (Q'.add_eqv_congr_left _ _ _ ihb)) ?_
      exact Q'.eqv_symm (evalRaw_append ρ (rawNormalize a) (rawNormalize b))
  | .mul a b => by
      have iha := eval_rawNormalize ρ a
      have ihb := eval_rawNormalize ρ b
      show (eval ρ a * eval ρ b).eqv (evalRaw ρ (rawMul (rawNormalize a) (rawNormalize b)))
      refine Q'.eqv_trans _ (evalRaw ρ (rawNormalize a) * evalRaw ρ (rawNormalize b)) _
        (Q'.eqv_trans _ (evalRaw ρ (rawNormalize a) * eval ρ b) _
          (Q'.mul_eqv_congr_right _ _ _ iha)
          (Q'.mul_eqv_congr_left _ _ _ ihb)) ?_
      exact Q'.eqv_symm (evalRaw_rawMul ρ (rawNormalize a) (rawNormalize b))
  | .neg a => by
      have iha := eval_rawNormalize ρ a
      show (-(eval ρ a)).eqv (evalRaw ρ (rawNeg (rawNormalize a)))
      refine Q'.eqv_trans _ (-(evalRaw ρ (rawNormalize a))) _
        (Q'.neg_eqv_congr _ _ iha) ?_
      exact Q'.eqv_symm (evalRaw_rawNeg ρ (rawNormalize a))
  | .pow a n => by
      have iha := eval_rawNormalize ρ a
      show (qpow (eval ρ a) n).eqv (evalRaw ρ (rawPow (rawNormalize a) n))
      refine Q'.eqv_trans _ (qpow (evalRaw ρ (rawNormalize a)) n) _
        (qpow_eqv_congr iha n) ?_
      exact Q'.eqv_symm (evalRaw_rawPow ρ (rawNormalize a) n)

/-! ## 5. Canonicalisation — sorted, like-terms-combined, zero-free. -/

/-- Strict lex comparison of trailing-zero-trimmed monomials (low-index variable
first).  Returns `.eq` iff the (trimmed) lists are structurally equal. -/
def monoCmp : List Nat → List Nat → Ordering
  | [],      []      => Ordering.eq
  | [],      _ :: _  => Ordering.lt
  | _ :: _,  []      => Ordering.gt
  | x :: xs, y :: ys =>
      if x < y then Ordering.lt
      else if y < x then Ordering.gt
      else monoCmp xs ys

/-- `monoCmp m m' = .eq → m = m'` (structural equality). -/
theorem monoCmp_eq {m m' : List Nat} : monoCmp m m' = Ordering.eq → m = m' := by
  induction m generalizing m' with
  | nil =>
      cases m' with
      | nil => intro _; rfl
      | cons y ys => intro h; simp [monoCmp] at h
  | cons x xs ih =>
      cases m' with
      | nil => intro h; simp [monoCmp] at h
      | cons y ys =>
          intro h
          unfold monoCmp at h
          by_cases hxy : x < y
          · simp [hxy] at h
          · by_cases hyx : y < x
            · simp [hxy, hyx] at h
            · simp [hxy, hyx] at h
              have hxeq : x = y := by omega
              have := ih h
              rw [hxeq, this]

/-- Insert a single term `(m, c)` into a canonical polynomial, preserving the
sorted/combined/zero-free invariant. -/
def insertTerm (m : List Nat) (c : Int) : RawPoly → RawPoly
  | [] => if c = 0 then [] else [(m, c)]
  | (m', c') :: rest =>
      if c = 0 then (m', c') :: rest
      else match monoCmp m m' with
        | Ordering.lt => (m, c) :: (m', c') :: rest
        | Ordering.eq => if c + c' = 0 then rest else (m, c + c') :: rest
        | Ordering.gt => (m', c') :: insertTerm m c rest

/-- **`insertTerm` preserves value.** -/
theorem evalRaw_insertTerm (ρ : Nat → Q') (m : List Nat) (c : Int) :
    ∀ (p : RawPoly),
      (evalRaw ρ (insertTerm m c p)).eqv (Q'.ofInt c * evalMono ρ m + evalRaw ρ p)
  | [] => by
      by_cases hc : c = 0
      · -- insertTerm m 0 [] = [] ; RHS = ofInt 0 * M + 0
        subst hc
        show (evalRaw ρ (insertTerm m 0 [])).eqv (Q'.ofInt 0 * evalMono ρ m + 0)
        have : insertTerm m (0 : Int) [] = [] := by simp [insertTerm]
        rw [this]
        show (0 : Q').eqv (Q'.ofInt 0 * evalMono ρ m + 0)
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ (Q'.ofInt 0 * evalMono ρ m) _ ?_ ?_
        · exact eqv_of_eq (Q'.add_zero' (Q'.ofInt 0 * evalMono ρ m))
        · show ((0 : Q') * evalMono ρ m).eqv 0
          exact q_zero_mul (evalMono ρ m)
      · -- insertTerm m c [] = [(m,c)] ; RHS = ofInt c * M + 0
        show (evalRaw ρ (insertTerm m c [])).eqv (Q'.ofInt c * evalMono ρ m + 0)
        have : insertTerm m c [] = [(m, c)] := by simp [insertTerm, hc]
        rw [this]
        show (Q'.ofInt c * evalMono ρ m + 0).eqv (Q'.ofInt c * evalMono ρ m + 0)
        exact Q'.eqv_refl _
  | (m', c') :: rest => by
      let M := evalMono ρ m
      let M' := evalMono ρ m'
      let R := evalRaw ρ rest
      by_cases hc : c = 0
      · -- drop: insertTerm m 0 (…) = (…) ; RHS = ofInt 0 * M + (ofInt c' M' + R) ≃ that
        subst hc
        have : insertTerm m (0 : Int) ((m', c') :: rest) = (m', c') :: rest := by
          simp [insertTerm]
        rw [this]
        show (evalRaw ρ ((m', c') :: rest)).eqv
              (Q'.ofInt 0 * M + (Q'.ofInt c' * M' + R))
        refine Q'.eqv_symm ?_
        -- ofInt 0 * M ≃ 0 ; 0 + X ≃ X
        refine Q'.eqv_trans _ ((0 : Q') + (Q'.ofInt c' * M' + R)) _
          (Q'.add_eqv_congr_right _ _ _ (q_zero_mul M)) ?_
        exact eqv_of_eq (Q'.zero_add' (Q'.ofInt c' * M' + R))
      · -- c ≠ 0: case on monoCmp m m'
        have hins :
            insertTerm m c ((m', c') :: rest)
              = (match monoCmp m m' with
                  | Ordering.lt => (m, c) :: (m', c') :: rest
                  | Ordering.eq => if c + c' = 0 then rest else (m, c + c') :: rest
                  | Ordering.gt => (m', c') :: insertTerm m c rest) := by
          simp [insertTerm, hc]
        rw [hins]
        cases hcmp : monoCmp m m' with
        | lt =>
            show (evalRaw ρ ((m, c) :: (m', c') :: rest)).eqv
                  (Q'.ofInt c * M + evalRaw ρ ((m', c') :: rest))
            exact Q'.eqv_refl _
        | eq =>
            have hmm : m = m' := monoCmp_eq hcmp
            subst hmm
            -- M' is defeq M (same m); goal after subst
            by_cases hz : c + c' = 0
            · -- combine to zero, drop
              simp only [hz, if_true]
              show R.eqv (Q'.ofInt c * M + (Q'.ofInt c' * M + R))
              refine Q'.eqv_symm ?_
              -- ofInt c * M + ofInt c' * M ≃ ofInt (c+c') * M ≃ ofInt 0 * M ≃ 0
              refine Q'.eqv_trans _ ((Q'.ofInt c * M + Q'.ofInt c' * M) + R) _
                (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofInt c * M) (Q'.ofInt c' * M) R)) ?_
              have hcomb : (Q'.ofInt c * M + Q'.ofInt c' * M).eqv (0 : Q') := by
                refine Q'.eqv_trans _ (Q'.ofInt (c + c') * M) _ ?_ ?_
                · exact Q'.eqv_symm
                    (Q'.eqv_trans _ ((Q'.ofInt c + Q'.ofInt c') * M) _
                      (Q'.mul_eqv_congr_right _ _ _ (ofInt_add c c'))
                      (q_add_mul (Q'.ofInt c) (Q'.ofInt c') M))
                · rw [hz]
                  exact q_zero_mul M
              refine Q'.eqv_trans _ ((0 : Q') + R) _
                (Q'.add_eqv_congr_right _ _ _ hcomb) ?_
              exact eqv_of_eq (Q'.zero_add' R)
            · -- combine, keep
              simp only [hz, if_false]
              show (Q'.ofInt (c + c') * M + R).eqv
                    (Q'.ofInt c * M + (Q'.ofInt c' * M + R))
              -- ofInt (c+c') * M ≃ ofInt c * M + ofInt c' * M ; then reassociate
              refine Q'.eqv_trans _ ((Q'.ofInt c * M + Q'.ofInt c' * M) + R) _
                (Q'.add_eqv_congr_right _ _ _
                  (Q'.eqv_trans _ ((Q'.ofInt c + Q'.ofInt c') * M) _
                    (Q'.mul_eqv_congr_right _ _ _ (ofInt_add c c'))
                    (q_add_mul (Q'.ofInt c) (Q'.ofInt c') M))) ?_
              exact Q'.add_assoc_eqv (Q'.ofInt c * M) (Q'.ofInt c' * M) R
        | gt =>
            have ih := evalRaw_insertTerm ρ m c rest
            show (evalRaw ρ ((m', c') :: insertTerm m c rest)).eqv
                  (Q'.ofInt c * M + (Q'.ofInt c' * M' + R))
            -- evalRaw = ofInt c' * M' + evalRaw (insertTerm m c rest)
            -- ≃ ofInt c' * M' + (ofInt c * M + R) ≃ ofInt c * M + (ofInt c' * M' + R)
            refine Q'.eqv_trans _ (Q'.ofInt c' * M' + (Q'.ofInt c * M + R)) _
              (Q'.add_eqv_congr_left _ _ _ ih) ?_
            -- swap the two summands' grouping: b + (a + r) ≃ a + (b + r)
            refine Q'.eqv_trans _ ((Q'.ofInt c' * M' + Q'.ofInt c * M) + R) _
              (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofInt c' * M') (Q'.ofInt c * M) R)) ?_
            refine Q'.eqv_trans _ ((Q'.ofInt c * M + Q'.ofInt c' * M') + R) _
              (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (Q'.ofInt c' * M') (Q'.ofInt c * M))) ?_
            exact Q'.add_assoc_eqv (Q'.ofInt c * M) (Q'.ofInt c' * M') R

/-- Canonicalise a raw polynomial: insert every term into an empty canonical
polynomial. -/
def canon (p : RawPoly) : RawPoly :=
  p.foldr (fun mc acc => insertTerm mc.1 mc.2 acc) []

/-- **`canon` preserves value.** -/
theorem evalRaw_canon (ρ : Nat → Q') :
    ∀ (p : RawPoly), (evalRaw ρ (canon p)).eqv (evalRaw ρ p)
  | [] => Q'.eqv_refl _
  | (m, c) :: rest => by
      have ih := evalRaw_canon ρ rest
      -- canon ((m,c)::rest) = insertTerm m c (canon rest)
      show (evalRaw ρ (insertTerm m c (canon rest))).eqv
            (Q'.ofInt c * evalMono ρ m + evalRaw ρ rest)
      refine Q'.eqv_trans _ (Q'.ofInt c * evalMono ρ m + evalRaw ρ (canon rest)) _
        (evalRaw_insertTerm ρ m c (canon rest)) ?_
      exact Q'.add_eqv_congr_left _ _ _ ih

/-! ## 6. `normalize` and the soundness theorem + decision procedure. -/

/-- A canonical (normal-form) polynomial. -/
abbrev NormalPoly := RawPoly

/-- Reflect and canonicalise. -/
def normalize (e : PolyExpr) : NormalPoly := canon (rawNormalize e)

/-- **THE SOUNDNESS THEOREM.**  `normalize` preserves the value of the
expression: `eval ρ e ≃ evalRaw ρ (normalize e)`.  Composed from the two
genuinely-proved halves (`eval_rawNormalize`, `evalRaw_canon`); no step is
assumed. -/
theorem normalize_eval (ρ : Nat → Q') (e : PolyExpr) :
    (eval ρ e).eqv (evalRaw ρ (normalize e)) := by
  refine Q'.eqv_trans _ (evalRaw ρ (rawNormalize e)) _ (eval_rawNormalize ρ e) ?_
  exact Q'.eqv_symm (evalRaw_canon ρ (rawNormalize e))

/-- **THE DECISION PROCEDURE.**  If two expressions have structurally-equal
normal forms, they are equal as functions on every `Q'` environment.  SOUND. -/
theorem poly_identity_of_normal_eq (e₁ e₂ : PolyExpr)
    (h : normalize e₁ = normalize e₂) (ρ : Nat → Q') :
    (eval ρ e₁).eqv (eval ρ e₂) := by
  have h1 := normalize_eval ρ e₁
  have h2 := normalize_eval ρ e₂
  rw [h] at h1
  exact Q'.eqv_trans _ (evalRaw ρ (normalize e₂)) _ h1 (Q'.eqv_symm h2)

/-! ## 7. Demonstration — the degree-2 Chu–Vandermonde convolution identity.

`n(n-1) + 2·m·n + m(m-1) = (m+n)(m+n-1)` for all `m,n : Q'`.  This is the
`k=2` member of the Vandermonde/Saalschütz convolution family noted above;
it is nonlinear (so beyond `omega`) and needs
distribution + cross-term cancellation (so beyond `ac_rfl`).  Proved by pure
reflection. -/

/-- LHS syntax: `x₁·(x₁ - 1) + 2·x₀·x₁ + x₀·(x₀ - 1)`  (`x₀ = m`, `x₁ = n`). -/
def vdmLHS : PolyExpr :=
  .add
    (.add
      (.mul (.var 1) (.add (.var 1) (.const (-1))))
      (.mul (.mul (.const 2) (.var 0)) (.var 1)))
    (.mul (.var 0) (.add (.var 0) (.const (-1))))

/-- RHS syntax: `(x₀ + x₁)·(x₀ + x₁ - 1)`. -/
def vdmRHS : PolyExpr :=
  .mul
    (.add (.var 0) (.var 1))
    (.add (.add (.var 0) (.var 1)) (.const (-1)))

/-- The two sides share the SAME canonical normal form (kernel computation). -/
theorem vdm_normal_eq : normalize vdmLHS = normalize vdmRHS := by decide

/-- **The demonstrated multivariate identity** (∀ `m,n : Q'`), proved via the
reflective normaliser — beyond `omega` (nonlinear) and `ac_rfl` (needs
distribution + cross-term cancellation). -/
theorem vandermonde_deg2 (m n : Q') :
    (eval (fun i => if i = 0 then m else n) vdmLHS).eqv
      (eval (fun i => if i = 0 then m else n) vdmRHS) :=
  poly_identity_of_normal_eq vdmLHS vdmRHS vdm_normal_eq _

/-- A concrete readable corollary: the identity written out in `Q'` arithmetic,
`n·(n + (-1)) + (2·m)·n + m·(m + (-1)) ≃ (m + n)·((m + n) + (-1))`. -/
theorem vandermonde_deg2_explicit (m n : Q') :
    ((n * (n + (-1 : Q'))) + ((2 : Q') * m) * n + (m * (m + (-1 : Q')))).eqv
      ((m + n) * ((m + n) + (-1 : Q'))) := by
  have h := vandermonde_deg2 m n
  -- `eval` on both sides unfolds definitionally to the displayed `Q'` terms.
  simpa [eval, vdmLHS, vdmRHS, qpow] using h

/-! ## 8. A DEGREE-3 Vandermonde/Saalschütz member — a genuine hypergeometric
building block that external CAS tools COMPUTE and the normaliser VERIFIES.

The Chu–Vandermonde convolution, cleared to falling-factorial (integer-coefficient
polynomial) form, is

  `Σ_{k=0}^{p} C(p,k)·(m)_k·(n)_{p-k}  =  (m+n)_p`      (`(m)_k` the falling factorial)

— the classical "Vandermonde/Saalschütz convolution layer".  The `p = 3`
member is a genuine multivariate
polynomial identity of degree 3 (beyond the degree-2 demo above): with binomials
`C(3,·) = 1,3,3,1`,

  `(n)_3 + 3·(m)_1(n)_2 + 3·(m)_2(n)_1 + (m)_3  =  (m+n)(m+n-1)(m+n-2)`.

A computer-algebra system computed the identity (residual
`0`); the proof here is by the reflective normaliser — the certificate is trusted
for NOTHING, the kernel decides `normalize LHS = normalize RHS`. -/

/-- Falling factorial `(x_i)_k` as a `PolyExpr` (right-nested product
`x·(x−1)·…·(x−k+1)`). -/
def fallingExpr (i : Nat) : Nat → PolyExpr
  | 0     => .const 1
  | k + 1 => .mul (fallingExpr i k) (.add (.var i) (.const (-(k : Int))))

/-- LHS syntax of the degree-3 Chu–Vandermonde (falling-factorial) convolution:
`(n)_3 + 3·(m)_1(n)_2 + 3·(m)_2(n)_1 + (m)_3`  (`x₀ = m`, `x₁ = n`). -/
def vdm3LHS : PolyExpr :=
  .add
    (.add
      (.add
        (fallingExpr 1 3)
        (.mul (.const 3) (.mul (fallingExpr 0 1) (fallingExpr 1 2))))
      (.mul (.const 3) (.mul (fallingExpr 0 2) (fallingExpr 1 1))))
    (fallingExpr 0 3)

/-- RHS syntax `(m+n)_3 = (m+n)(m+n-1)(m+n-2)`. -/
def vdm3RHS : PolyExpr :=
  .mul
    (.mul (.add (.var 0) (.var 1))
      (.add (.add (.var 0) (.var 1)) (.const (-1))))
    (.add (.add (.var 0) (.var 1)) (.const (-2)))

/-- The two sides share the SAME canonical normal form (kernel computation). -/
theorem vdm3_normal_eq : normalize vdm3LHS = normalize vdm3RHS := by decide

/-- **The degree-3 Chu–Vandermonde convolution identity** (∀ `m,n : Q'`), a
genuine member of the Vandermonde/Saalschütz layer, proved by the reflective
normaliser (the CAS only computed it). -/
theorem vandermonde_deg3 (m n : Q') :
    (eval (fun i => if i = 0 then m else n) vdm3LHS).eqv
      (eval (fun i => if i = 0 then m else n) vdm3RHS) :=
  poly_identity_of_normal_eq vdm3LHS vdm3RHS vdm3_normal_eq _

/-! ## 9. The DEGREE-4 Chu–Vandermonde member — the layer scales another degree.

The `p = 4` member of the same falling-factorial convolution family
(`C(4,·) = 1,4,6,4,1`):

  `(n)_4 + 4·(m)_1(n)_3 + 6·(m)_2(n)_2 + 4·(m)_3(n)_1 + (m)_4
      = (m+n)(m+n-1)(m+n-2)(m+n-3)`.

A computer-algebra system computed it (residual `0`, spot-checked on
`m,n ∈ [-3,6]²`); the proof here is by the reflective normaliser —
the certificate is trusted for NOTHING, the kernel decides
`normalize LHS = normalize RHS`.  This certifies the normaliser scales one degree
past `vandermonde_deg3`, a concrete new element of the very
"Vandermonde/Saalschütz convolution layer" consumed by outer
creative-telescoping steps. -/

/-- LHS syntax of the degree-4 Chu–Vandermonde (falling-factorial) convolution:
`(n)_4 + 4·(m)_1(n)_3 + 6·(m)_2(n)_2 + 4·(m)_3(n)_1 + (m)_4`  (`x₀ = m`, `x₁ = n`). -/
def vdm4LHS : PolyExpr :=
  .add
    (.add
      (.add
        (.add
          (fallingExpr 1 4)
          (.mul (.const 4) (.mul (fallingExpr 0 1) (fallingExpr 1 3))))
        (.mul (.const 6) (.mul (fallingExpr 0 2) (fallingExpr 1 2))))
      (.mul (.const 4) (.mul (fallingExpr 0 3) (fallingExpr 1 1))))
    (fallingExpr 0 4)

/-- RHS syntax `(m+n)_4 = (m+n)(m+n-1)(m+n-2)(m+n-3)`. -/
def vdm4RHS : PolyExpr :=
  .mul
    (.mul
      (.mul (.add (.var 0) (.var 1))
        (.add (.add (.var 0) (.var 1)) (.const (-1))))
      (.add (.add (.var 0) (.var 1)) (.const (-2))))
    (.add (.add (.var 0) (.var 1)) (.const (-3)))

/-- The two sides share the SAME canonical normal form (kernel computation). -/
theorem vdm4_normal_eq : normalize vdm4LHS = normalize vdm4RHS := by decide

/-- **The degree-4 Chu–Vandermonde convolution identity** (∀ `m,n : Q'`), a
genuine member of the Vandermonde/Saalschütz layer one degree past
`vandermonde_deg3`, proved by the reflective normaliser (the CAS only computed it). -/
theorem vandermonde_deg4 (m n : Q') :
    (eval (fun i => if i = 0 then m else n) vdm4LHS).eqv
      (eval (fun i => if i = 0 then m else n) vdm4RHS) :=
  poly_identity_of_normal_eq vdm4LHS vdm4RHS vdm4_normal_eq _

end ConstructiveReals.RingNormaliser

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms ConstructiveReals.RingNormaliser.evalMono_monoMul
#print axioms ConstructiveReals.RingNormaliser.evalRaw_rawMul
#print axioms ConstructiveReals.RingNormaliser.eval_rawNormalize
#print axioms ConstructiveReals.RingNormaliser.evalRaw_canon
#print axioms ConstructiveReals.RingNormaliser.normalize_eval
#print axioms ConstructiveReals.RingNormaliser.poly_identity_of_normal_eq
#print axioms ConstructiveReals.RingNormaliser.vdm_normal_eq
#print axioms ConstructiveReals.RingNormaliser.vandermonde_deg2
#print axioms ConstructiveReals.RingNormaliser.vdm3_normal_eq
#print axioms ConstructiveReals.RingNormaliser.vandermonde_deg3
#print axioms ConstructiveReals.RingNormaliser.vdm4_normal_eq
#print axioms ConstructiveReals.RingNormaliser.vandermonde_deg4
